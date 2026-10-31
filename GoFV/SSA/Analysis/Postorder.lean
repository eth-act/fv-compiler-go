import GoFV.SSA.Func

/-!
# DFS postorder

Port of `postorderWithNumbering` (`ssa/dom.go:23`, go1.27.3): an iterative DFS from `f.Entry`
over each block's `Succs` in order; a block is emitted when all its successors are explored.
Order-sensitive (successor order), so ported verbatim. Unreachable blocks do not appear.
`f.NumBlocks()` is `bidLast + 1`.
-/

namespace GoFV.SSA.Analysis

/-- `postorderWithNumbering(f, ponums)`: the postorder and, by block ID, each block's index in
it (`ponums`; 0 for blocks not in the postorder, as Go leaves them). -/
def postorderWithNumbering (f : Func) : Array ID × Array Nat := Id.run do
  let nb := f.bidLast + 1
  let mut seen := (Array.replicate nb false).set! f.entry true
  let mut order : Array ID := #[]
  let mut ponums := Array.replicate nb 0
  -- stack of (block, number of successor edges already explored)
  let mut s : Array (ID × Nat) := #[(f.entry, 0)]
  -- every iteration explores one edge or pops one of at most `nb` pushed blocks
  let edges := f.blocks.foldl (fun n b => n + ((f.block? b).map (·.succs.size)).getD 0) 0
  for _ in [0:2 * nb + edges + 1] do
    let some (b, i) := s.back? | break
    let succs := ((f.block? b).map (·.succs)).getD #[]
    if h : i < succs.size then
      s := s.set! (s.size - 1) (b, i + 1)
      let bb := succs[i].b
      if !seen.getD bb true then
        seen := seen.set! bb true
        s := s.push (bb, 0)
      continue
    s := s.pop
    ponums := ponums.set! b order.size
    order := order.push b
  return (order, ponums)

/-- `postorder(f)`: the reachable blocks in DFS postorder (not cached; see `CfgCache`). -/
def postorder (f : Func) : Array ID := (postorderWithNumbering f).1

end GoFV.SSA.Analysis
