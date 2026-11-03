import GoFV.SSA.Func

/-!
# Allocation and value/block mutation primitives

Verbatim ports of the `ssa.Func`/`Value`/`Block` primitives every pass uses
(`docs/PASSES.md` §1.1, §1.2): ID allocation with Go's LIFO free lists (`func.go:280-453`),
`Uses` maintenance (`value.go` `SetArg*`/`AddArg*`/`resetArgs`/`reset`/`copyOf`, `block.go`
control setters), `truncateValues`, `invalidateCFG`, and the constant cache removal
(`unCache`, `func.go:356-395`; `constVal` is in `GoFV.SSA.ConstCache`).

All functions are pure `Func → … → Func` (or `Func × ID` when they allocate) over IDs. Go
`Fatalf` sanity checks are not replicated: on a function the stock compiler accepted they never
fire, and parity checks the result. `v.InCache` is membership in `f.consts` (the export's
definition), so `unCache` of a value that is in no cache line is a no-op, exactly like Go's
`if v.InCache { … }` guard.
-/

namespace GoFV.SSA

/-- `notStmtBoundary` (`numberlines.go:63`): values with these ops never carry a statement
mark; `newValue` gives them `WithNotStmt` positions. -/
def Op.notStmtBoundary : Op → Bool
  | .Copy | .Phi | .VarDef | .VarLive | .Unknown | .FwdRef | .Arg | .ArgIntReg
  | .ArgFloatReg => true
  | _ => false

/-- `BranchPrediction` times −1 (`b.Likely *= -1`). -/
def BranchPrediction.neg : BranchPrediction → BranchPrediction
  | .unlikely => .likely | .unknown => .unknown | .likely => .unlikely

/-- Magic `f.constants` keys of zero-valued non-numeric constants (`func.go:684-689`). -/
def constSliceMagic : Int64 := 1122334455
def constInterfaceMagic : Int64 := 2233445566
def constNilMagic : Int64 := 3344556677
def constEmptyStringMagic : Int64 := 4455667788

namespace Func

/-! ## Table access -/

/-- The value `id` (Go's `*Value`); `default` if it is not in the function. -/
@[inline] def getV (f : Func) (id : ID) : Value := (f.value? id).getD default

/-- The block `id`; `default` if it is not in the function. -/
@[inline] def getB (f : Func) (id : ID) : Block := (f.block? id).getD default

/-- Update value `id` in place (no-op if absent). -/
@[inline] def modV (f : Func) (id : ID) (g : Value → Value) : Func :=
  { f with valueTab := f.valueTab.modify id (Option.map g) }

/-- Update block `id` in place (no-op if absent). -/
@[inline] def modB (f : Func) (id : ID) (g : Block → Block) : Func :=
  { f with blockTab := f.blockTab.modify id (Option.map g) }

/-- Store `x` at index `i`, growing the table with `none` as needed. -/
@[inline] def tabPut {α} (a : Array (Option α)) (i : Nat) (x : α) : Array (Option α) :=
  if i < a.size then a.set! i (some x)
  else (a ++ Array.replicate (i - a.size) none).push (some x)

@[inline] def incUses (f : Func) (id : ID) : Func := f.modV id fun v => { v with uses := v.uses + 1 }
@[inline] def decUses (f : Func) (id : ID) : Func := f.modV id fun v => { v with uses := v.uses - 1 }

/-- `f.invalidateCFG()` (`func.go:803`): drops the cached postorder, idom, sdom and loop nest
(`auxmap` and `cachedLineStarts` survive). -/
def invalidateCFG (f : Func) : Func :=
  { f with cache := { f.cache with postorder := none, idom := none, sdom := none,
                                   loopnest := none } }

/-! ## Constant cache removal (`func.go:356-395`) -/

/-- Index of the cache line with key `k` in `f.consts`. -/
def constLine? (f : Func) (k : Int64) : Option Nat := f.consts.findIdx? (·.1 == k)

/-- `f.unCacheLine(v, aux)`: swap-remove `v` from line `aux` (an emptied line is dropped: the
export lists only non-empty lines). `none` if `v` is not in that line. -/
def unCacheLine (f : Func) (v : ID) (aux : Int64) : Option Func := do
  let li ← f.constLine? aux
  let vv := f.consts[li]!.2
  let i ← vv.idxOf? v
  let last := vv.size - 1
  let vv := (vv.set! i vv[last]!).pop
  if vv.isEmpty then return { f with consts := f.consts.eraseIdx! li }
  return { f with consts := f.consts.set! li (aux, vv) }

/-- `f.unCache(v)`: remove `v` from the constant cache if it is there (its own `AuxInt` line,
or for a zero `AuxInt` the magic line of its op). -/
def unCache (f : Func) (v : ID) : Func :=
  let x := f.getV v
  match f.unCacheLine v x.auxInt with
  | some f => f
  | none =>
    if x.auxInt != 0 then f else
    let magic : Int64 := match x.op with
      | .ConstNil => constNilMagic
      | .ConstSlice => constSliceMagic
      | .ConstString => constEmptyStringMagic
      | .ConstInterface => constInterfaceMagic
      | _ => 0
    if magic == 0 then f else (f.unCacheLine v magic).getD f

/-! ## Allocation (`func.go:280-453`) -/

/-- Pop `f.freeValues`, else take `f.vid.get()`. -/
@[inline] def allocVid (f : Func) : ID × Func :=
  match f.freeValues with
  | id :: rest => (id, { f with freeValues := rest })
  | [] => (f.vidLast + 1, { f with vidLast := f.vidLast + 1 })

/-- `f.newValueNoBlock(op, t, pos)`: a fresh value in no block (`block = 0`, Go's nil); the
caller sets its block and appends it to that block's values. -/
def newValueNoBlock (f : Func) (op : Op) (t : TypeRef) (pos : Pos) : Func × ID :=
  let (id, f) := f.allocVid
  let pos := if op.notStmtBoundary then pos.withNotStmt else pos
  let v : Value := { id, op, type := t, auxInt := 0, aux := none, pos, uses := 0, args := #[],
                     block := 0 }
  ({ f with valueTab := tabPut f.valueTab id v }, id)

/-- `f.newValue(op, t, b, pos)`: a fresh value appended to `b.Values`. -/
def newValue (f : Func) (op : Op) (t : TypeRef) (b : ID) (pos : Pos) : Func × ID :=
  let (f, id) := f.newValueNoBlock op t pos
  let f := f.modV id fun v => { v with block := b }
  (f.modB b fun blk => { blk with values := blk.values.push id }, id)

/-- `b.NewValue{0,1,2,3,4}{,I,A,IA}(pos, op, t, auxint, aux, args...)`: `newValue`, then
`AuxInt`, `Aux` and the arguments (each argument's `Uses` incremented, in order). -/
def newValueArgs (f : Func) (b : ID) (pos : Pos) (op : Op) (t : TypeRef) (auxInt : Int64 := 0)
    (aux : Option AuxRef := none) (args : Array ID := #[]) : Func × ID :=
  let (f, id) := f.newValue op t b pos
  let f := f.modV id fun v => { v with auxInt, aux, args }
  (args.foldl incUses f, id)

/-- `b.NewValue0(pos, op, t)`. -/
@[inline] def newValue0 (f : Func) (b : ID) (pos : Pos) (op : Op) (t : TypeRef) : Func × ID :=
  f.newValueArgs b pos op t

/-- `f.freeValue(v)`: uncache, drop from the value table, push on `f.freeValues`. The value
must have no uses and no args, and the caller removes it from its block's values. -/
def freeValue (f : Func) (v : ID) : Func :=
  let f := f.unCache v
  { f with valueTab := f.valueTab.set! v none, freeValues := v :: f.freeValues }

/-- `f.NewBlock(kind)`: pop `f.freeBlocks`, else `f.bid.get()`; append to `f.Blocks`;
invalidate the CFG caches. -/
def newBlock (f : Func) (kind : BlockKind) : Func × ID :=
  let (id, f) : ID × Func := match f.freeBlocks with
    | id :: rest => (id, { f with freeBlocks := rest })
    | [] => (f.bidLast + 1, { f with bidLast := f.bidLast + 1 })
  let b : Block := { id, kind, pos := Pos.none, likely := .unknown, auxInt := 0, aux := none,
                     controls := #[], succs := #[], preds := #[], values := #[] }
  let f := { f with blockTab := tabPut f.blockTab id b, blocks := f.blocks.push id }
  (f.invalidateCFG, id)

/-- `f.freeBlock(b)`: drop from the block table, push on `f.freeBlocks` (the caller removes it
from `f.Blocks`). -/
def freeBlock (f : Func) (b : ID) : Func :=
  { f with blockTab := f.blockTab.set! b none, freeBlocks := b :: f.freeBlocks }

/-! ## Arguments (`value.go`) -/

/-- `v.AddArg(w)`. -/
def addArg (f : Func) (v w : ID) : Func :=
  (f.modV v fun x => { x with args := x.args.push w }).incUses w

/-- `v.AddArgs(ws...)` (also `AddArg2..6`). -/
def addArgs (f : Func) (v : ID) (ws : Array ID) : Func :=
  ws.foldl incUses (f.modV v fun x => { x with args := x.args ++ ws })

/-- `v.SetArg(i, w)`. -/
def setArg (f : Func) (v : ID) (i : Nat) (w : ID) : Func :=
  let old := (f.getV v).args[i]!
  let f := (f.decUses old).modV v fun x => { x with args := x.args.set! i w }
  f.incUses w

/-- `v.resetArgs()`. -/
def resetArgs (f : Func) (v : ID) : Func :=
  let f := (f.getV v).args.foldl decUses f
  f.modV v fun x => { x with args := #[] }

/-- `v.SetArgs1..4(ws...)`: `resetArgs`, then `AddArg` each. -/
def setArgs (f : Func) (v : ID) (ws : Array ID) : Func := (f.resetArgs v).addArgs v ws

/-- `v.SetArgs1(w)`. -/
@[inline] def setArgs1 (f : Func) (v w : ID) : Func := f.setArgs v #[w]

/-- `v.reset(op)`: uncache, set the op, drop the args, zero `AuxInt` and `Aux` (type and
position are kept). -/
def resetValue (f : Func) (v : ID) (op : Op) : Func :=
  let f := (f.unCache v).modV v fun x => { x with op }
  (f.resetArgs v).modV v fun x => { x with auxInt := 0, aux := none }

/-- `v.copyOf(a)`: make `v` a `Copy` of `a` (with `a`'s type); no-op if `v == a`. -/
def copyOf (f : Func) (v a : ID) : Func :=
  if v == a then f else
  let t := (f.getV a).type
  let f := (f.unCache v).modV v fun x => { x with op := .Copy }
  let f := (f.resetArgs v).addArg v a
  f.modV v fun x => { x with auxInt := 0, aux := none, type := t }

/-! ## Block controls (`block.go:180-275`) -/

/-- `b.ResetControls()`. -/
def resetControls (f : Func) (b : ID) : Func :=
  let f := (f.getB b).controls.foldl decUses f
  f.modB b fun x => { x with controls := #[] }

/-- `b.SetControl(v)`. -/
def setControl (f : Func) (b v : ID) : Func :=
  ((f.resetControls b).modB b fun x => { x with controls := #[v] }).incUses v

/-- `b.AddControl(v)`. -/
def addControl (f : Func) (b v : ID) : Func :=
  (f.modB b fun x => { x with controls := x.controls.push v }).incUses v

/-- `b.ReplaceControl(i, v)`. -/
def replaceControl (f : Func) (b : ID) (i : Nat) (v : ID) : Func :=
  let old := (f.getB b).controls[i]!
  let f := (f.decUses old).modB b fun x => { x with controls := x.controls.set! i v }
  f.incUses v

/-- `b.CopyControls(from)`. -/
def copyControls (f : Func) (b src : ID) : Func :=
  if b == src then f else
  (f.getB src).controls.foldl (fun f c => f.addControl b c) (f.resetControls b)

/-- `b.Reset(kind)`: kind, no controls, nil `Aux`, zero `AuxInt`. -/
def resetBlock (f : Func) (b : ID) (kind : BlockKind) : Func :=
  let f := f.modB b fun x => { x with kind }
  (f.resetControls b).modB b fun x => { x with aux := none, auxInt := 0 }

/-- `b.resetWithControl(kind, v)`. -/
def resetWithControl (f : Func) (b : ID) (kind : BlockKind) (v : ID) : Func :=
  ((f.resetBlock b kind).modB b fun x => { x with controls := #[v] }).incUses v

/-- `b.resetWithControl2(kind, v, w)`. -/
def resetWithControl2 (f : Func) (b : ID) (kind : BlockKind) (v w : ID) : Func :=
  (((f.resetBlock b kind).modB b fun x => { x with controls := #[v, w] }).incUses v).incUses w

/-- `b.truncateValues(i)`: keep the first `i` values (the rest must already have had their
args reset). -/
def truncateValues (f : Func) (b : ID) (i : Nat) : Func :=
  f.modB b fun x => { x with values := x.values.extract 0 i }

end Func

end GoFV.SSA
