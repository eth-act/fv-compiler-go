import GoFV.Opt.Pass
import GoFV.SSA.Alloc
import GoFV.Util.PdqSort

/-!
# loop rotate (`looprotate.go`)

Port of `loopRotate` (go1.27.3; docs/PASSES2.md, loop rotate, #411). On the cached loop nest
(`f.loopnest()`; regalloc has computed it), unless it has an irreducible loop or no loop: the
loops, sorted by depth descending with Go's unstable `slices.SortFunc` (equal depths tie), each
pick the last `Plain` predecessor of their header that belongs to the loop itself as the new top
block `p` (hotness `HotInitial`, plus `HotPgo` in a PGO-hot function). If `p` is not the header
(`HotNotFlowIn`), the blocks from the header up to `p` in the current order that belong to the
loop, or are the top of a direct child loop, are placed after `p` (`after[p]`), and `p` and the
header swap places. Finally the blocks are emitted in that order, each followed (recursively) by
its `after` list. Only `f.Blocks` and `Hotness` change.
-/

namespace GoFV.Opt

open GoFV.SSA

namespace LoopRotate

/-- `HotNotFlowIn`, `HotInitial`, `HotPgo` (`block.go`). -/
abbrev hotNotFlowIn : Nat := 1
abbrev hotInitial : Nat := 2
abbrev hotPgo : Nat := 4

/-- `moveBlocks(blocks)`: append each block and, recursively, its `after` list. -/
def moveBlocks (after : Array (Option (Array ID))) : Nat → Array ID → Array ID → Except String (Array ID)
  | 0, _, _ => throw "looprotate: after lists too deep"
  | fuel + 1, out, bs => do
    let mut out := out
    for a in bs do
      out := out.push a
      if let some next := after.getD a none then out ← moveBlocks after fuel out next
    return out

end LoopRotate

open LoopRotate in
/-- `loopRotate(f)`. -/
def loopRotate (env : PassEnv) (f : Func) : Except String Func := do
  let some nest := f.cache.loopnest | throw "loopRotate: no cached loop nest"
  if nest.irreducible || nest.loops.isEmpty then return f
  let nb := max f.blockTab.size (f.bidLast + 1)
  let mut b2l : Array (Option Nat) := Array.replicate nest.b2lSize none
  for (b, l) in nest.b2l do
    b2l := b2l.set! b (some l)
  let loopOf (b : ID) : Except String (Option Nat) :=
    if h : b < b2l.size then pure b2l[b] else throw s!"loopRotate: b{b} outside b2l"
  let mut blocks := f.blocks
  let mut idToIdx : Array Nat := Array.replicate nb 0
  for h : i in [0:blocks.size] do
    idToIdx := idToIdx.set! blocks[i] i
  let mut hot : Array Nat := Array.replicate nb 0
  for (b, h) in f.low.hotness do
    hot := hot.set! b h
  let mut move : Array Bool := Array.replicate nb false
  let mut after : Array (Option (Array ID)) := Array.replicate nb none
  let mut tops : Array (Option ID) := Array.replicate nb none
  let order := GoFV.Util.PdqSort.sortFunc
    (fun (i j : Nat) =>
      let di := nest.loops[i]!.depth
      let dj := nest.loops[j]!.depth
      if di > dj then -1 else if di < dj then 1 else 0)
    (Array.range nest.loops.size)
  for li in order do
    let loop := nest.loops[li]!
    let mut top : Option ID := none
    for e in (f.getB loop.header).preds do
      if (f.getB e.b).kind != .Plain then continue
      if (← loopOf e.b) != some li then continue
      top := some e.b
    let some p := top | continue
    tops := tops.set! loop.header (some p)
    hot := hot.modify p (· ||| hotInitial)
    if env.pgohot then hot := hot.modify p (· ||| hotPgo)
    if p == loop.header then continue
    hot := hot.modify p (· ||| hotNotFlowIn)
    let mut list : Array ID := #[loop.header]
    let mut b := loop.header
    for _ in [0:blocks.size] do
      let nextIdx := idToIdx[b]! + 1
      if nextIdx >= blocks.size then break
      let nextb := blocks[nextIdx]!
      if nextb == p then break
      if let some bl := ← loopOf nextb then
        if bl == li ||
            (nest.loops[bl]!.outer == some li && tops[nest.loops[bl]!.header]! == some nextb) then
          list := list.push nextb
      b := nextb
    after := after.set! p (some list)
    let hi := idToIdx[loop.header]!
    let pi := idToIdx[p]!
    blocks := (blocks.set! hi p).set! pi loop.header
    idToIdx := (idToIdx.set! loop.header pi).set! p hi
    for x in list do
      move := move.set! x true
  -- move blocks to their destinations
  let mut out : Array ID := #[]
  for b in blocks do
    if move[b]! then continue
    out := out.push b
    if let some next := after[b]! then out ← moveBlocks after (blocks.size + 1) out next
  if out.size != blocks.size then throw "bad reordering in looprotate"
  let mut hotness : Array (ID × Nat) := #[]
  for h : b in [0:hot.size] do
    if hot[b] != 0 then hotness := hotness.push (b, hot[b])
  return { f with blocks := out, low := { f.low with hotness } }

/-- The `loop rotate` pass. -/
def loopRotatePass : Pass := Pass.ofFunc loopRotate

end GoFV.Opt
