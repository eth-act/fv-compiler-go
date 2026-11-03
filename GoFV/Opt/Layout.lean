import GoFV.Opt.Pass
import GoFV.SSA.Alloc
import GoFV.Util.SparseSet

/-!
# layout (`layout.go:10-188`)

`layout` (docs/PASSES2.md, layout, issue #406): `f.Blocks = layoutOrder(f)`, `f.laidout = true`.
The exit set (insertion-ordered sparse set) starts with the `Exit` blocks and grows by
predecessors all of whose successors are in it; the other blocks get their predecessor count
as indegree (zero: LIFO stack `zerodegree`, else sparse set `posdegree`). From the entry, each
scheduled block decrements its successors' indegrees in reverse successor order (newly zero:
moved to `zerodegree`, else pushed on the `succs` stack); the next block is the predicted
successor if unscheduled, else the first unscheduled entry popped from `zerodegree`, `succs`,
`posdegree`, `exit`, in that order.
-/

namespace GoFV.Opt

open GoFV.SSA

/-- `layoutOrder(f)`. -/
def layoutOrder (f : Func) : Except String (Array ID) := do
  let nb := f.bidLast + 1
  let mut order : Array ID := Array.mkEmpty f.blocks.size
  let mut scheduled : Array Bool := Array.replicate nb false
  let mut indegree : Array Int := Array.replicate nb 0
  let mut posdegree := Util.SparseSet.new nb
  let mut zerodegree : Array ID := #[]
  let mut succs : Array ID := #[]
  let mut exit := Util.SparseSet.new nb
  for b in f.blocks do
    if (f.getB b).kind == .Exit then exit := exit.add b
  for _ in [0:nb + 1] do
    let mut changed := false
    for id in exit.contents do
      for pe in (f.getB id).preds do
        let p := pe.b
        if exit.contains p then continue
        if (f.getB p).succs.all fun s => exit.contains s.b then
          exit := exit.add p
          changed := true
    if !changed then break
  for b in f.blocks do
    if exit.contains b then continue
    let n := (f.getB b).preds.size
    indegree := indegree.set! b n
    if n == 0 then zerodegree := zerodegree.push b
    else posdegree := posdegree.add b
  let mut bid := f.entry
  for _ in [0:f.blocks.size + 1] do
    let blk := f.getB bid
    order := order.push bid
    scheduled := scheduled.set! bid true
    if order.size == f.blocks.size then return order
    for k in [0:blk.succs.size] do
      let c := blk.succs[blk.succs.size - 1 - k]!.b
      indegree := indegree.modify c (· - 1)
      if indegree[c]! == 0 then
        posdegree := posdegree.remove c
        zerodegree := zerodegree.push c
      else
        succs := succs.push c
    let likely : Option ID := match blk.likely with
      | .likely => some blk.succs[0]!.b
      | .unlikely => some blk.succs[1]!.b
      | .unknown => none
    if let some l := likely then
      if !scheduled[l]! then
        bid := l
        continue
    let mut next : Option ID := none
    for _ in [0:zerodegree.size] do
      let some cid := zerodegree.back? | break
      zerodegree := zerodegree.pop
      if !scheduled[cid]! then
        next := some cid
        break
    if next.isNone then
      for _ in [0:succs.size] do
        let some cid := succs.back? | break
        succs := succs.pop
        if !scheduled[cid]! then
          next := some cid
          break
    if next.isNone then
      for _ in [0:posdegree.size] do
        let (cid, s) := posdegree.pop
        posdegree := s
        if !scheduled[cid]! then
          next := some cid
          break
    if next.isNone then
      for _ in [0:exit.size] do
        let (cid, s) := exit.pop
        exit := s
        if !scheduled[cid]! then
          next := some cid
          break
    let some n := next | throw "layout: no unscheduled block left"
    bid := n
  throw "layout: block order does not cover f.Blocks"

/-- `layout(f)`. -/
def layout (f : Func) : Except String Func := do
  let order ← layoutOrder f
  return { f with blocks := order, low := { f.low with laidout := true } }

/-- The `layout` pass. -/
def layoutPass : Pass := Pass.ofFunc fun _ f => layout f

end GoFV.Opt
