import GoFV.Opt.Pass
import GoFV.Opt.NumberLines
import GoFV.SSA.Alloc
import GoFV.SSA.Analysis.CfgCache
import GoFV.SSA.StoreOrder
import GoFV.SSA.TypePred
import GoFV.SSA.XPosMap

/-!
# nilcheckelim (`nilcheck.go:15-187`)

Port of `nilcheckelim` (go1.27.3; docs/PASSES.md, nilcheckelim). `nonNilValues` is seeded with
the values whose op makes them non-nil (`Addr`, `LocalAddr`, `AddPtr`, `OffPtr`, `Add32/64`,
`Sub32/64`, `SlicePtr`) and closed over phis whose arguments are all non-nil. Then an
explicit-stack walk of the dominator tree (`f.Sdom()`, children pushed in child/sibling order,
`ClearPtr` items undoing path facts) visits each block: an `If (IsNonNil p)` predecessor makes
`p` non-nil in its true successor; the block's values are put in store order (`storeOrder`
under the pass name `nilcheckelim`, which leaves blocks without nil checks alone); a redundant
`IsNonNil` becomes `ConstBool [1]` and a redundant `NilCheck` a `Copy` of the dominating check
(or of the pointer itself), their statement marks moved through `f.cachedLineStarts` to the
next eligible value of the same line, else to the block. Nothing is allocated or freed.
`Debug_checknil` only logs.
-/

namespace GoFV.Opt

open GoFV.SSA GoFV.SSA.Analysis

namespace NilCheck

/-- The ops whose result `nilcheckelim` assumes non-nil (`nilcheck.go:57`). -/
def nonNilOp : Op → Bool
  | .Addr | .LocalAddr | .AddPtr | .OffPtr | .Add32 | .Add64 | .Sub32 | .Sub64 | .SlicePtr => true
  | _ => false

/-- A dominator-walk stack item (`bp`). -/
inductive Item where
  /-- `Work`: process block `b` and push its dominees. -/
  | work (b : ID)
  /-- `ClearPtr`: forget that `ptr` is non-nil. -/
  | clearPtr (ptr : ID)

/-- The initial `nonNilValues` (`nilcheck.go:52-85`), indexed by value ID. -/
def initialNonNil (f : Func) : Array (Option ID) := Id.run do
  let mut nn : Array (Option ID) := Array.replicate (f.vidLast + 1) none
  for b in f.blocks do
    for v in (f.getB b).values do
      if nonNilOp (f.getV v).op then nn := nn.set! v (some v)
  -- phis whose arguments are all non-nil; each round that changes marks a new phi
  for _ in [0:f.vidLast + 2] do
    let mut changed := false
    for b in f.blocks do
      for v in (f.getB b).values do
        let x := f.getV v
        if x.op == .Phi && x.args.all (fun a => (nn[a]?).join.isSome) then
          if (nn[v]?).join.isNone then changed := true
          nn := nn.set! v (some v)
    if !changed then break
  return nn

/-- Move a pending statement mark to `v` (`nilcheck.go:155-158,163-166`). -/
@[inline] def takeStmt (f : Func) (pending : XPosMap) (v : ID) : Func × XPosMap :=
  let x := f.getV v
  if x.pos.isStmt != Pos.notStmt && !NumberLines.isPoorStatementOp x.op && pending.contains x.pos
  then
    let p := x.pos.withIsStmt
    (f.modV v fun y => { y with pos := p }, pending.remove p)
  else (f, pending)

/-- State of the dominator walk. -/
structure St where
  f : Func
  nonNil : Array (Option ID)
  work : Array Item
  pending : XPosMap
  storeNumber : Array Int

/-- Process the values of block `b` in their (store-ordered) order (`nilcheck.go:122-160`). -/
def processValues (s : St) (b : ID) : Except String St := do
  let mut s := s
  for v in (s.f.getB b).values do
    let x := s.f.getV v
    match x.op with
    | .IsNonNil =>
      let ptr := x.args[0]!
      if (s.nonNil[ptr]?).join.isSome then
        let mut f := s.f
        let mut pending := s.pending
        if x.pos.isStmt == Pos.isStmtMark then
          pending ← pending.add x.pos
          f := f.modV v fun y => { y with pos := x.pos.withNotStmt }
        f := f.resetValue v .ConstBool
        f := f.modV v fun y => { y with auxInt := 1 }
        s := { s with f, pending }
    | .NilCheck =>
      let ptr := x.args[0]!
      match (s.nonNil[ptr]?).join with
      | some nc =>
        let mut pending := s.pending
        if x.pos.isStmt == Pos.isStmtMark then pending ← pending.add x.pos
        let f := s.f.modV v fun y => { y with op := .Copy }
        s := { s with f := f.setArgs1 v nc, pending }
      | none =>
        s := { s with nonNil := s.nonNil.set! ptr (some v), work := s.work.push (.clearPtr ptr) }
        let (f, pending) := takeStmt s.f s.pending v
        s := { s with f, pending }
    | _ =>
      let (f, pending) := takeStmt s.f s.pending v
      s := { s with f, pending }
  return s

/-- One `Work` item (`nilcheck.go:103-178`). -/
def workBlock (passName : String) (isMem : TypeRef → Bool) (sdom : SparseTree) (s : St) (b : ID) :
    Except String St := do
  let mut s := s
  let blk := s.f.getB b
  -- dominated by an explicit nil check?
  if blk.preds.size == 1 then
    let p := s.f.getB blk.preds[0]!.b
    if p.kind == .If && (s.f.getV p.controls[0]!).op == .IsNonNil &&
        (p.succs[0]?.map (·.b)) == some b then
      let ptr := (s.f.getV p.controls[0]!).args[0]!
      if (s.nonNil[ptr]?).join.isNone then
        s := { s with nonNil := s.nonNil.set! ptr (some ptr), work := s.work.push (.clearPtr ptr) }
  -- order values w.r.t. stores
  let (vals, sn) ← storeOrder s.f isMem passName blk.values s.storeNumber
  s := { s with f := s.f.modB b fun x => { x with values := vals }, storeNumber := sn,
                pending := s.pending.clear }
  s ← processValues s b
  -- any later value of the block may take a pending mark
  for v in (s.f.getB b).values do
    let (f, pending) := takeStmt s.f s.pending v
    s := { s with f, pending }
  let bpos := (s.f.getB b).pos
  if s.pending.contains bpos then
    let p := bpos.withIsStmt
    s := { s with f := s.f.modB b fun x => { x with pos := p }, pending := s.pending.remove p }
  -- dominees
  let mut w := sdom.child b
  for _ in [0:s.f.blockTab.size] do
    let some c := w | break
    s := { s with work := s.work.push (.work c) }
    w := sdom.sibling c
  return s

end NilCheck

open NilCheck in
/-- `nilcheckelim(f)`. -/
def nilcheckelim (env : PassEnv) (f : Func) : Except String Func := do
  let some mem := env.typ? "Mem" | throw "typs: no Mem"
  let isMem := env.tables.isMemory mem
  let (sdom, f) := f.sdom
  let some pending := XPosMap.ofCache f.cache.lineStarts | throw "nil f.cachedLineStarts"
  let mut s : St := { f, nonNil := initialNonNil f, work := #[.work f.entry], pending,
                      storeNumber := Array.replicate (f.vidLast + 1) 0 }
  -- each block is pushed once (dominator tree) and each push of a ClearPtr follows a fact
  let fuel := 2 * (f.blockTab.size + f.valueTab.size) + 2
  for _ in [0:fuel] do
    let some it := s.work.back? | break
    s := { s with work := s.work.pop }
    match it with
    | .work b => s ← workBlock env.passName isMem sdom s b
    | .clearPtr p => s := { s with nonNil := s.nonNil.set! p none }
  if !s.work.isEmpty then throw "nilcheckelim: walk did not terminate"
  return { s.f with cache := { s.f.cache with lineStarts := some s.pending.toCache } }

def nilcheckelimPass : Pass := Pass.ofFunc nilcheckelim

end GoFV.Opt
