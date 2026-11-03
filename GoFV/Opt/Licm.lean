import GoFV.Opt.Pass
import GoFV.SSA.Alloc
import GoFV.SSA.Analysis.CfgCache
import GoFV.SSA.TypePred

/-!
# loop invariant (`licm.go:36-159`)

`licm` (docs/PASSES2.md, loop invariant, issue #398):

1. A fresh `loopnestfor(f)` (caching the postorder and dominator tree, not the nest); return if
   there are no loops or an irreducible one was seen.
2. Seed the loop-dependent set with every value of a leaf-loop block (`b2l` set and `isInner`)
   except `earlyOk` non-pointer values (whose bad marks are fatal) and `Select0`/`Select1`;
   close it under argument uses (`uses.go`; block controls are not uses) restricted to
   leaf-loop blocks. The closure is order independent.
3. For each block of the original `f.Blocks` in a leaf loop whose header has two predecessors,
   move every value not in the set, in `b.Values` order, to the header predecessor outside the
   loop (predecessor 0 if its ID is past the nest's `b2l` or its loop is not this one, else 1),
   first splicing in a `Plain` preheader (`NewBlock`, predecessor's `Pos`) if that predecessor
   is not `Plain`; append there, then compact the source block stably. No value is allocated
   and no `Uses` change.
-/

namespace GoFV.Opt

open GoFV.SSA

namespace Licm

/-- The loop-dependent values (`loopDependent`, `licm.go:43-98`), by value ID. -/
def dependent (tabs : Tables) (mem : TypeRef) (nest : Analysis.LoopNest) (f : Func) :
    Except String (Array Bool) := do
  let inLeaf (b : ID) : Bool :=
    match nest.loopOf b with
    | some l => nest.loops[l]!.isInner
    | none => false
  let n := f.vidLast + 1
  let mut users : Array (Array ID) := Array.replicate n #[]
  for b in f.blocks do
    for v in (f.getB b).values do
      for a in (f.getV v).args do
        users := users.modify a (·.push v)
  let mut dep : Array Bool := Array.replicate n false
  let mut queue : Array ID := #[]
  for b in f.blocks do
    if !inLeaf b then continue
    for v in (f.getB b).values do
      let x := f.getV v
      if x.op.earlyOk then
        let memArg := match x.args.back? with
          | some a => tabs.isMemory mem (f.getV a).type
          | none => false
        if tabs.isMemory mem x.type || x.op.nilCheck || x.op.hasSideEffects || memArg then
          throw s!"op {x.op.exportName} has bad earlyOk mark"
        if (tabs.type? x.type).map (·.kind) != some .PTR then continue
      if x.op == .Select0 || x.op == .Select1 then continue
      dep := dep.set! v true
      queue := queue.push v
  for _ in [0:n + 1] do
    let some v := queue.back? | break
    queue := queue.pop
    for u in users[v]! do
      if !inLeaf (f.getV u).block then continue
      if dep[u]! then continue
      dep := dep.set! u true
      queue := queue.push u
  return dep

end Licm

open Licm in
/-- `licm(f)`. -/
def licm (env : PassEnv) (f : Func) : Except String Func := do
  let some mem := env.typ? "Mem" | throw "licm: no typ.Mem"
  let (nest, f) ← f.loopnestfor
  if nest.loops.isEmpty || nest.hasIrreducible then return f
  let dep ← dependent env.tables mem nest f
  let mut f := f
  for b in f.blocks do
    let some l := nest.loopOf b | continue
    let loop := nest.loops[l]!
    if !loop.isInner then continue
    let h := loop.header
    if (f.getB h).preds.size != 2 then continue
    let vals := (f.getB b).values
    let mut moved : Array Bool := Array.replicate vals.size false
    for hi : i in [0:vals.size] do
      let v := vals[i]
      if dep[v]! then continue
      let p0 := (f.getB h).preds[0]!.b
      let inIdx := if p0 ≥ nest.b2l.size || nest.loopOf p0 != some l then 0 else 1
      let e := (f.getB h).preds[inIdx]!
      let mut dest := e.b
      if (f.getB dest).kind != .Plain then
        let outIdx := e.i
        let (f', mid) := f.newBlock .Plain
        let pos := (f'.getB dest).pos
        f := f'.modB mid fun x => { x with pos, preds := #[⟨dest, outIdx⟩], succs := #[⟨h, inIdx⟩] }
        f := f.modB h fun x => { x with preds := x.preds.set! inIdx ⟨mid, 0⟩ }
        f := f.modB dest fun x => { x with succs := x.succs.set! outIdx ⟨mid, 0⟩ }
        dest := mid
      moved := moved.set! i true
      f := f.modV v fun x => { x with block := dest }
      f := f.modB dest fun x => { x with values := x.values.push v }
    if moved.any id then
      let mut kept := #[]
      for hi : i in [0:vals.size] do
        if !moved[i]! then kept := kept.push vals[i]
      f := f.modB b fun x => { x with values := kept }
  return f

/-- The `loop invariant` pass. -/
def licmPass : Pass := Pass.ofFunc licm

end GoFV.Opt
