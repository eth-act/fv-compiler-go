import GoFV.SSA.Func

/-!
# Dominators

Port of `dominators` → `dominatorsLTOrig` (`ssa/dom.go:58-185`, go1.27.3): Lengauer–Tarjan,
"simple" version, verbatim (including Go's never-emptied buckets and the depth-first search
`dfsOrig` that may push a block several times). Works on the current CFG, never on a cached
postorder. The result is indexed by block ID (size `f.NumBlocks()`): the immediate dominator,
`none` for the entry and for unreachable blocks.

Every reachable block's immediate dominator is unique, so any correct algorithm yields the same
array; the verbatim port keeps the parity argument trivial.
-/

namespace GoFV.SSA.Analysis

/-- `dfsOrig(entry, semi, vertex, label, parent)`: numbers the reachable blocks 1..n in DFS
preorder (`semi`, `vertex`), sets `label[v] = v` and the DFS-tree `parent`. Returns
`(n, semi, vertex, label, parent)`. -/
def dfsOrig (f : Func) (entry : ID) (semi vertex label parent : Array Nat) :
    Nat × Array Nat × Array Nat × Array Nat × Array Nat := Id.run do
  let mut semi := semi
  let mut vertex := vertex
  let mut label := label
  let mut parent := parent
  let mut n := 0
  let mut s : Array ID := #[entry]
  -- a block is pushed once per incoming edge from a newly numbered block, plus the entry
  let edges := f.blocks.foldl (fun n b => n + ((f.block? b).map (·.succs.size)).getD 0) 0
  for _ in [0:edges + 2] do
    let some v := s.back? | break
    s := s.pop
    if semi.getD v 1 != 0 then continue
    n := n + 1
    semi := semi.set! v n
    vertex := vertex.set! n v
    label := label.set! v v
    for e in ((f.block? v).map (·.succs)).getD #[] do
      let w := e.b
      if semi.getD w 1 == 0 then
        s := s.push w
        parent := parent.set! w v
  return (n, semi, vertex, label, parent)

/-- `compressOrig(v, ancestor, semi, label)` (recursive in Go; `fuel` bounds the ancestor
chain). Returns `(ancestor, label)`. -/
def compressOrig (semi : Array Nat) : Nat → Nat → Array Nat → Array Nat → Array Nat × Array Nat
  | 0, _, ancestor, label => (ancestor, label)
  | fuel + 1, v, ancestor, label =>
    let av := ancestor[v]!
    if ancestor[av]! != 0 then
      let (ancestor, label) := compressOrig semi fuel av ancestor label
      let label := if semi[label[av]!]! < semi[label[v]!]! then label.set! v label[av]! else label
      (ancestor.set! v ancestor[av]!, label)
    else (ancestor, label)

/-- `evalOrig(v, ancestor, semi, label)`. Returns `(u, ancestor, label)`. -/
def evalOrig (fuel : Nat) (semi : Array Nat) (v : Nat) (ancestor label : Array Nat) :
    Nat × Array Nat × Array Nat :=
  if ancestor[v]! == 0 then (v, ancestor, label) else
  let (ancestor, label) := compressOrig semi fuel v ancestor label
  (label[v]!, ancestor, label)

/-- `f.dominatorsLTOrig(entry)`: immediate dominators by block ID. -/
def dominatorsLTOrig (f : Func) (entry : ID) : Array (Option ID) := Id.run do
  let nb := f.bidLast + 1
  let z := Array.replicate nb 0
  let (n, semi, vertex, label, parent) := dfsOrig f entry z z z z
  let mut semi := semi
  let mut label := label
  let mut ancestor := z
  let mut bucketHead := z
  let mut bucketLink := z
  let mut idom : Array (Option ID) := Array.replicate nb none
  for k in [0:n - 1] do
    let i := n - k
    let w := vertex[i]!
    -- step 2
    for e in ((f.block? w).map (·.preds)).getD #[] do
      let v := e.b
      if semi[v]! == 0 then continue
      let (u, a, l) := evalOrig nb semi v ancestor label
      ancestor := a
      label := l
      if semi[u]! < semi[w]! then semi := semi.set! w semi[u]!
    -- add w to bucket[vertex[semi[w]]]
    let vsw := vertex[semi[w]!]!
    bucketLink := bucketLink.set! w bucketHead[vsw]!
    bucketHead := bucketHead.set! vsw w
    -- linkOrig(parent[w], w)
    let pw := parent[w]!
    ancestor := ancestor.set! w pw
    -- step 3 (the bucket of parent[w] is never emptied, as in Go); the bucket lists are
    -- acyclic, each block being added once, so `nb` steps suffice
    let mut v := bucketHead[pw]!
    for _ in [0:nb] do
      if v == 0 then break
      let (u, a, l) := evalOrig nb semi v ancestor label
      ancestor := a
      label := l
      idom := idom.set! v (some (if semi[u]! < semi[v]! then u else pw))
      v := bucketLink[v]!
  -- step 4
  for i in [2:n + 1] do
    let w := vertex[i]!
    let d := (idom[w]!).getD 0
    if d != vertex[semi[w]!]! then idom := idom.set! w idom[d]!
  return idom

/-- `dominators(f)`: `f.dominatorsLTOrig(f.Entry)`. -/
def dominators (f : Func) : Array (Option ID) := dominatorsLTOrig f f.entry

end GoFV.SSA.Analysis
