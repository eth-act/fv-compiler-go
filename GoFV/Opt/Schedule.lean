import GoFV.Opt.LowTy
import GoFV.SSA.Alloc
import GoFV.Util.PdqSort

/-!
# schedule (`schedule.go:16-373`)

Port of `schedule` (go1.27.3; docs/PASSES2.md, schedule, #407). Every value gets a score
(`ScorePhi` … `ScoreControl`); with `Config.optimize`, values used by a value of their own block
are marked `inBlockUses`. Each block is then scheduled by Kahn's algorithm over the edges
argument → user (no edges into phis) and load → next store of the block (`nextMem`, shared
between blocks and only used for a store of the same block), with the edge list sorted by
source ID (Go's unstable `slices.SortFunc`: `GoFV.Util.PdqSort`) and the ready values in a
`container/heap` ordered by `ValHeap.Less`. That comparator uses wrapping `AuxInt` subtraction
and `Type.Compare`, so it need not be a strict order; the heap operations (`up`/`down`) and the
push order are ported exactly. Afterwards `SPanchored` and nil-check results are bypassed in
every argument and control, `SPanchored` values are freed (scheduled order) and nil checks get
`types.TypeVoid`; `f.scheduled` is set. `schedule` does not call `storeOrder`.
-/

namespace GoFV.Opt

open GoFV.SSA

namespace Schedule

/-- The score constants (`schedule.go:16-28`). -/
abbrev scorePhi : Nat := 0
abbrev scoreArg : Nat := 1
abbrev scoreInitMem : Nat := 2
abbrev scoreReadTuple : Nat := 3
abbrev scoreNilCheck : Nat := 4
abbrev scoreMemory : Nat := 5
abbrev scoreReadFlags : Nat := 6
abbrev scoreDefault : Nat := 7
abbrev scoreFlags : Nat := 8
abbrev scoreInductionInc : Nat := 9
abbrev scoreControl : Nat := 10

/-- `v.isFlagOp()`: flags type, or a tuple whose second field is flags (the PPC64 carry ops do
not exist on arm64). -/
def isFlagOp (ty : LowTy) (v : Value) : Bool :=
  ty.isFlags v.type || (ty.tuple? v.type).any (fun (_, s) => ty.isFlags s)

/-- `v.hasFlagInput()`. -/
def hasFlagInput (ty : LowTy) (f : Func) (v : Value) : Bool :=
  v.args.any fun a => isFlagOp ty (f.getV a)

/-- `ValHeap.Less` on the values `x` and `y`. -/
def less (f : Func) (ord : TypeOrder) (score : Array Nat) (ibu : Array Bool) (x y : ID) :
    Bool :=
  let vx := f.getV x
  let vy := f.getV y
  let sx := score.getD x 0
  let sy := score.getD y 0
  if sx != sy then sx < sy else
  let ix := ibu.getD x false
  let iy := ibu.getD y false
  if ix != iy then ix else
  if vx.pos != vy.pos then vx.pos.before vy.pos else
  if vx.op != .Phi && vx.args.size != vy.args.size then vx.args.size > vy.args.size else
  if vx.uses != vy.uses then vx.uses > vy.uses else
  let c := vx.auxInt - vy.auxInt
  if c != 0 then c < 0 else
  match ord.compare vx.type vy.type with
  | .eq => x < y
  | o => o == .lt

/-- Swap two heap slots. -/
@[inline] def swapAt (a : Array ID) (i j : Nat) : Array ID :=
  let x := a[i]!
  (a.set! i a[j]!).set! j x

/-- `container/heap.up(h, j)`. -/
def up (lt : ID → ID → Bool) (a : Array ID) (j : Nat) : Array ID := Id.run do
  let mut a := a
  let mut j := j
  for _ in [0:a.size] do
    if j == 0 then break
    let i := (j - 1) / 2
    if !lt a[j]! a[i]! then break
    a := swapAt a i j
    j := i
  return a

/-- `container/heap.down(h, 0, n)`. -/
def down (lt : ID → ID → Bool) (a : Array ID) (n : Nat) : Array ID := Id.run do
  let mut a := a
  let mut i := 0
  for _ in [0:n + 1] do
    let j1 := 2 * i + 1
    if j1 >= n then break
    let mut j := j1
    if j1 + 1 < n && lt a[j1 + 1]! a[j1]! then j := j1 + 1
    if !lt a[j]! a[i]! then break
    a := swapAt a i j
    i := j
  return a

/-- `heap.Push(h, v)`. -/
@[inline] def push (lt : ID → ID → Bool) (a : Array ID) (v : ID) : Array ID :=
  let a := a.push v
  up lt a (a.size - 1)

/-- `heap.Pop(h)`: the popped value and the heap (non-empty heap). -/
@[inline] def pop (lt : ID → ID → Bool) (a : Array ID) : ID × Array ID :=
  let n := a.size - 1
  let a := down lt (swapAt a 0 n) n
  (a.back!, a.pop)

/-- `sort.Search(len(edges), p)` for a predicate `p` on the edge source that is monotone over
the sorted edges. -/
def search (edges : Array (ID × ID)) (p : ID → Bool) : Nat := Id.run do
  let mut lo := 0
  let mut hi := edges.size
  for _ in [0:edges.size + 1] do
    if lo >= hi then break
    let h := (lo + hi) / 2
    if !p edges[h]!.1 then lo := h + 1 else hi := h
  return lo

/-- The scores of all values (`schedule.go:138-228`). -/
def scores (ty : LowTy) (f : Func) (nv : Nat) : Except String (Array Nat) := do
  let mut score : Array Nat := Array.replicate nv 0
  for b in f.blocks do
    let blk := f.getB b
    for v in blk.values do
      let x := f.getV v
      let s ←
        if x.op == .ARM64LoweredGetClosurePtr then
          if b != f.entry then
            throw s!"LoweredGetClosurePtr appeared outside of entry block, b=b{b}"
          pure scorePhi
        else if x.op.nilCheck then pure scoreNilCheck
        else if x.op == .Phi then pure scorePhi
        else if x.op == .ArgIntReg || x.op == .ArgFloatReg then
          if b != f.entry then
            throw s!"{x.op.exportName} appeared outside of entry block, b=b{b}"
          pure scorePhi
        else if x.op == .Arg || x.op == .SP || x.op == .SB then pure scoreArg
        else if x.op == .InitMem then pure scoreInitMem
        else if ty.isMemory x.type then pure scoreMemory
        else if x.op == .Select0 || x.op == .Select1 || x.op == .SelectN then pure scoreReadTuple
        else if hasFlagInput ty f x then pure scoreReadFlags
        else if isFlagOp ty x then pure scoreFlags
        else
          let induction : Bool :=
            x.args.size == 1 &&
              (let p := f.getV x.args[0]!
               p.op == .Phi && p.uses > 1 && blk.succs.size == 1 &&
                 blk.succs[0]!.b == p.block && p.args[blk.succs[0]!.i]? == some v)
          pure (if induction then scoreInductionInc else scoreDefault)
      score := score.set! v s
    for c in blk.controls do
      let cv := f.getV c
      if cv.block != b || score.getD c 0 < scoreReadTuple then continue
      if score.getD c 0 == scoreReadTuple then
        let some a := cv.args[0]? | throw s!"schedule: tuple selector v{c} has no argument"
        score := score.set! a scoreControl
        continue
      score := score.set! c scoreControl
  return score

/-- Schedule one block (`schedule.go:244-325`). `nextMem` and `inEdges` persist across blocks
(Go's `f.Cache` slices). -/
def block (ty : LowTy) (f : Func) (lt : ID → ID → Bool) (b : ID) (nextMem : Array (Option ID))
    (inEdges : Array Nat) : Except String (Array ID × Array (Option ID) × Array Nat) := do
  let vals := (f.getB b).values
  let mut edges : Array (ID × ID) := #[]
  for v in vals do
    let x := f.getV v
    if x.op == .Phi then continue
    for a in x.args do
      if (f.getV a).block == b then edges := edges.push (a, v)
  let mut nextMem := nextMem
  for v in vals do
    let x := f.getV v
    if x.op != .Phi && x.op != .InitMem && ty.isMemory x.type then
      let some m := ty.memoryArg f x | throw s!"schedule: v{v} has no memory argument"
      nextMem := nextMem.set! m (some v)
  for v in vals do
    let x := f.getV v
    if x.op == .Phi || ty.isMemory x.type then continue
    let some w := ty.memoryArg f x | continue
    if let some s := nextMem.getD w none then
      if (f.getV s).block == b then edges := edges.push (v, s)
  edges := GoFV.Util.PdqSort.sortFunc
    (fun (e₁ e₂ : ID × ID) => if e₁.1 < e₂.1 then -1 else if e₁.1 > e₂.1 then 1 else 0) edges
  let mut inEdges := inEdges
  for e in edges do
    inEdges := inEdges.modify e.2 (· + 1)
  let mut heap : Array ID := #[]
  for v in vals do
    if inEdges.getD v 0 == 0 then heap := push lt heap v
  let mut order : Array ID := #[]
  -- every value is pushed at most once (when its in-edge count reaches zero)
  for _ in [0:vals.size + 1] do
    if heap.isEmpty then break
    let (v, h) := pop lt heap
    heap := h
    order := order.push v
    let i := search edges (· >= v)
    let j := search edges (· > v)
    for k in [i:j] do
      let y := edges[k]!.2
      inEdges := inEdges.modify y (· - 1)
      if inEdges.getD y 0 == 0 then heap := push lt heap y
  if order.size != vals.size then
    throw s!"schedule does not include all values in block b{b}"
  return (order, nextMem, inEdges)

/-- `a.Op == OpSPanchored || opcodeTable[a.Op].nilCheck`. -/
@[inline] def bypassed (x : Value) : Bool := x.op == .SPanchored || x.op.nilCheck

/-- The bypassed value chain from `a` (`for a.Op == … { a = a.Args[0] }`), each step
recorded. -/
def chain (f : Func) (a : ID) : Except String (Array ID) := do
  let mut out : Array ID := #[]
  let mut a := a
  for _ in [0:f.valueTab.size + 1] do
    let x := f.getV a
    if !bypassed x then return out
    let some a' := x.args[0]? | throw s!"schedule: v{a} has no argument"
    a := a'
    out := out.push a
  throw "schedule: cyclic SPanchored/nil check chain"

end Schedule

open Schedule in
/-- `schedule(f)`. -/
def schedule (env : PassEnv) (f : Func) : Except String Func := do
  let ty ← LowTy.ofEnv env
  let optimize ← env.flag "optimize"
  let nv := max f.valueTab.size (f.vidLast + 1)
  let mut ibu : Array Bool := Array.replicate nv false
  if optimize then
    for b in f.blocks do
      for v in (f.getB b).values do
        for a in (f.getV v).args do
          if (f.getV a).block == b then ibu := ibu.set! a true
  let score ← scores ty f nv
  let lt := less f env.typeOrder score ibu
  let mut f := f
  let mut nextMem : Array (Option ID) := Array.replicate nv none
  let mut inEdges : Array Nat := Array.replicate nv 0
  for b in f.blocks do
    let (order, nm, ie) ← block ty f lt b nextMem inEdges
    nextMem := nm
    inEdges := ie
    f := f.modB b fun x => { x with values := order }
  -- bypass SPanchored and nil checks
  for b in f.blocks do
    for v in (f.getB b).values do
      for i in [0:(f.getV v).args.size] do
        for a in ← chain f (f.getV v).args[i]! do
          f := f.setArg v i a
    for i in [0:(f.getB b).controls.size] do
      for c in ← chain f (f.getB b).controls[i]! do
        f := f.replaceControl b i c
  for b in f.blocks do
    let mut keep : Array ID := #[]
    for v in (f.getB b).values do
      let x := f.getV v
      if x.op == .SPanchored then
        if x.uses != 0 then throw s!"SPAnchored still has {x.uses} uses"
        f := (f.resetArgs v).freeValue v
      else
        if x.op.nilCheck then
          if x.uses != 0 then throw s!"nilcheck still has {x.uses} uses"
          f := f.modV v fun y => { y with type := ty.void }
        keep := keep.push v
    f := f.modB b fun x => { x with values := keep }
  return { f with low := { f.low with scheduled := true } }

/-- The `schedule` pass. -/
def schedulePass : Pass := Pass.ofFunc schedule

end GoFV.Opt
