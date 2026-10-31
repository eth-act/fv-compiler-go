import GoFV.SSA.Export
import Std.Data.HashSet.Basic

/-!
# Reachable blocks and live values

Ports of `ReachableBlocks` and the `live` result of `liveValues` (`ssa/deadcode.go`), as
used by `findlive` (and so by `f.String()`, which marks the rest `DEAD`). Both results are
indexed by ID (`f.NumBlocks()` = `bidLast + 1`, `f.NumValues()` = `vidLast + 1`).
The worklist loops run on fuel: every iteration pops an entry and every ID is pushed at most
once.
-/

namespace GoFV.SSA

/-- `ReachableBlocks(f)`: blocks reachable from the entry (`BlockFirst` only via its first
successor). -/
def Func.reachableBlocks (f : Func) : Array Bool := Id.run do
  let n := f.bidLast + 1
  let mut r := (Array.replicate n false).set! f.entry true
  let mut stack := #[f.entry]
  for _ in [0:n+1] do
    let some b := stack.back? | break
    stack := stack.pop
    let some blk := f.block? b | continue
    let succs := if blk.kind == .First then blk.succs.extract 0 1 else blk.succs
    for e in succs do
      if !r.getD e.b true then
        r := r.set! e.b true
        stack := stack.push e.b
  return r

/-- `pt.Pos(p).Base().InliningIndex()` (−1 without a position base). -/
def Tables.inliningIndex (t : Tables) (p : Pos) : Int :=
  (t.posBase? p.index).map (·.inl) |>.getD (-1)

/-- `liveValues(f, reachable)` (before register allocation): the `live` set and
`liveOrderStmts`, the newly live values whose position is not `PosNotStmt`, in discovery order
(roots in `f.Blocks` order, controls before values, then the LIFO closure; an `InlMark` root is
recorded even when already live, as in Go). -/
def Func.liveValuesOrder (f : Func) (t : Tables) (reachable : Array Bool) :
    Array Bool × Array ID := Id.run do
  let n := f.vidLast + 1
  let mut inl : Std.HashSet Int := {}
  for bid in f.blocks do
    let some b := f.block? bid | continue
    for vid in b.values do
      let some v := f.value? vid | continue
      let i := t.inliningIndex v.pos
      if i ≥ 0 then inl := inl.insert i
    let i := t.inliningIndex b.pos
    if i ≥ 0 then inl := inl.insert i
  let mut live := Array.replicate n false
  let mut q : Array ID := #[]
  let mut order : Array ID := #[]
  let stmt (vid : ID) : Bool := ((f.value? vid).map (·.pos.isStmt != Pos.notStmt)).getD false
  for bid in f.blocks do
    if !reachable.getD bid false then continue
    let some b := f.block? bid | continue
    for c in b.controls do
      if !live.getD c true then
        live := live.set! c true
        q := q.push c
        if stmt c then order := order.push c
    for vid in b.values do
      let some v := f.value? vid | continue
      if (v.op.call || v.op.hasSideEffects || v.op.nilCheck) && !live.getD vid true then
        live := live.set! vid true
        q := q.push vid
        if stmt vid then order := order.push vid
      if v.op == .InlMark then
        if !inl.contains v.auxInt.toInt then continue
        live := live.set! vid true
        q := q.push vid
        if stmt vid then order := order.push vid
  -- an `InlMark` may be pushed twice, every other value at most once
  for _ in [0:2*n+1] do
    let some vid := q.back? | break
    q := q.pop
    let some v := f.value? vid | continue
    let preds := ((f.block? v.block).map (·.preds)).getD #[]
    for h : i in [0:v.args.size] do
      let x := v.args[i]
      if v.op == .Phi && !(preds[i]?.map (reachable.getD ·.b false)).getD false then continue
      if !live.getD x true then
        live := live.set! x true
        q := q.push x
        if stmt x then order := order.push x
  return (live, order)

/-- The `live` result of `liveValues(f, reachable)`. -/
def Func.liveValues (f : Func) (t : Tables) (reachable : Array Bool) : Array Bool :=
  (f.liveValuesOrder t reachable).1

end GoFV.SSA
