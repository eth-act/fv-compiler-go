import GoFV.SSA.Func

/-!
# CFG analyses for the checker (`GoFV.SSA.check`, issue #8)

What `check.go` reads through `f.Sdom()`, `f.postorder()` and `f.loopnest()`, recomputed
from the CFG (never from the possibly stale `f.cache`):

- `postorder`: Go's `postorderWithNumbering` (iterative DFS from the entry, successors in
  order).
- `DomTree`: immediate dominators of the reachable blocks (Cooper–Harvey–Kennedy over the
  postorder; the dominator tree is unique, so this equals Go's Lengauer–Tarjan result) with
  DFS entry/exit numbers for O(1) ancestor queries, as Go's `SparseTree`.
- `LoopNest`: a port of `loopnestfor` (`likelyadjust.go`), including its depth self-check.

Executable checker code (`Id.run` loops over arrays); the facts a proof needs from a passing
check are stated separately (`docs/contracts/check.md`).
-/

namespace GoFV.SSA

namespace CheckCfg

/-- Successor block IDs of `b` in `f` (missing blocks are skipped). -/
@[inline] def succIDs (f : Func) (b : ID) : Array ID :=
  match f.block? b with
  | some blk => blk.succs.map (·.b)
  | none => #[]

/-- Go's `postorderWithNumbering(f, nil)`: the blocks reachable from the entry, in postorder
of an iterative DFS that visits successors in order. -/
def postorder (f : Func) : Array ID := Id.run do
  let n := f.blockTab.size
  let mut seen : Array Bool := Array.replicate n false
  let mut order : Array ID := #[]
  if f.entry < n then
    seen := seen.set! f.entry true
  let mut stack : Array (ID × Nat) := #[(f.entry, 0)]
  -- each iteration either pushes a block (at most n) or advances an edge index or pops
  let fuel := 4 * n + 4 * f.blocks.foldl (fun s b => s + (succIDs f b).size) 0 + 4
  for _ in [0:fuel] do
    if stack.isEmpty then break
    let (b, i) := stack.back!
    let ss := succIDs f b
    if h : i < ss.size then
      stack := stack.set! (stack.size - 1) (b, i + 1)
      let bb := ss[i]
      if bb < n && !seen[bb]! then
        seen := seen.set! bb true
        stack := stack.push (bb, 0)
    else
      stack := stack.pop
      order := order.push b
  return order

/-- The dominator tree of the reachable blocks, by block ID. -/
structure DomTree where
  /-- Immediate dominator (`none` for the entry and unreachable blocks). -/
  idom : Array (Option ID)
  /-- DFS numbers of the dominator tree (0 for unreachable blocks). -/
  entry : Array Nat
  exit : Array Nat

namespace DomTree

/-- `SparseTree.IsAncestorEq`: `x` dominates `y` (every block dominates itself; an
unreachable `y` is dominated by no other block). -/
def isAncestorEq (t : DomTree) (x y : ID) : Bool :=
  x == y ||
    (let xe := t.entry[x]?.getD 0
     let ye := t.entry[y]?.getD 0
     xe != 0 && ye != 0 && xe ≤ ye && t.exit[y]?.getD 0 ≤ t.exit[x]?.getD 0)

/-- `SparseTree.isAncestor`: strict dominance. -/
def isAncestor (t : DomTree) (x y : ID) : Bool :=
  x != y &&
    (let xe := t.entry[x]?.getD 0
     let ye := t.entry[y]?.getD 0
     xe != 0 && ye != 0 && xe < ye && t.exit[y]?.getD 0 < t.exit[x]?.getD 0)

/-- Block `b` is reachable from the entry. -/
def reachable (t : DomTree) (b : ID) : Bool := t.entry[b]?.getD 0 != 0

end DomTree

/-- Predecessor block IDs of `b`. -/
@[inline] def predIDs (f : Func) (b : ID) : Array ID :=
  match f.block? b with
  | some blk => blk.preds.map (·.b)
  | none => #[]

/-- Dominators by Cooper, Harvey, Kennedy ("A Simple, Fast Dominance Algorithm") over Go's
postorder `po`. -/
def dominators (f : Func) (po : Array ID) : DomTree := Id.run do
  let n := f.blockTab.size
  let none' : Nat := po.size
  -- postorder number by block ID (`none'` for unreachable)
  let mut ponum : Array Nat := Array.replicate n none'
  for h : i in [0:po.size] do
    ponum := ponum.set! po[i] i
  -- idom as postorder numbers (`none'` = undefined)
  let mut idom : Array Nat := Array.replicate po.size none'
  if po.size > 0 then
    idom := idom.set! (po.size - 1) (po.size - 1)
  let mut changed := true
  for _ in [0:po.size + 2] do
    if !changed then break
    changed := false
    -- reverse postorder, skipping the entry (the last block of po)
    for k in [0:po.size - 1] do
      let i := po.size - 2 - k
      let b := po[i]!
      let mut newIdom := none'
      for p in predIDs f b do
        let pi := ponum[p]?.getD none'
        if pi == none' || idom[pi]! == none' then continue
        if newIdom == none' then
          newIdom := pi
        else
          -- intersect
          let mut a := pi
          let mut c := newIdom
          for _ in [0:2 * po.size + 2] do
            if a == c then break
            while a < c do a := idom[a]!
            while c < a do c := idom[c]!
          newIdom := a
      if newIdom != none' && idom[i]! != newIdom then
        idom := idom.set! i newIdom
        changed := true
  -- by block ID
  let mut idomB : Array (Option ID) := Array.replicate n none
  let mut children : Array (Array ID) := Array.replicate n #[]
  for h : i in [0:po.size] do
    let b := po[i]
    let d := idom[i]!
    if d != none' && d != i then
      idomB := idomB.set! b (some po[d]!)
      children := children.modify po[d]! (·.push b)
  -- DFS numbering of the dominator tree from the entry (children in postorder-of-po order,
  -- any order gives correct ancestor queries)
  let mut entry : Array Nat := Array.replicate n 0
  let mut exit : Array Nat := Array.replicate n 0
  if po.size > 0 then
    let root := po[po.size - 1]!
    let mut clock := 1
    let mut stack : Array (ID × Nat) := #[(root, 0)]
    entry := entry.set! root clock
    for _ in [0:2 * po.size + 2] do
      if stack.isEmpty then break
      let (b, i) := stack.back!
      let cs := children[b]!
      if h : i < cs.size then
        stack := stack.set! (stack.size - 1) (b, i + 1)
        clock := clock + 1
        entry := entry.set! cs[i] clock
        stack := stack.push (cs[i], 0)
      else
        clock := clock + 1
        exit := exit.set! b clock
        stack := stack.pop
  return { idom := idomB, entry, exit }

/-- A loop of `loopnestfor`. -/
structure Loop where
  header : ID
  outer : Option Nat := none
  nBlocks : Nat := 0
  depth : Nat := 0
  isInner : Bool := true
  deriving Inhabited

/-- `loopnest`: the loop of each block (index into `loops`), by block ID. -/
structure LoopNest where
  b2l : Array (Option Nat)
  loops : Array Loop
  hasIrreducible : Bool

namespace LoopNest

/-- `outerinner(outer, inner)`: record that `outer` contains `inner`. -/
def outerinner (t : DomTree) : Nat → Array Loop → Nat → Nat → Array Loop
  | 0, ls, _, _ => ls
  | fuel + 1, ls, outer, inner => Id.run do
    let mut inner := inner
    let mut oldouter := ls[inner]!.outer
    for _ in [0:ls.size + 1] do
      match oldouter with
      | some o =>
        if t.isAncestor ls[outer]!.header ls[o]!.header then
          inner := o
          oldouter := ls[o]!.outer
        else break
      | none => break
    if oldouter == some outer then return ls
    let mut ls := ls
    if let some o := oldouter then
      ls := outerinner t fuel ls o outer
    ls := ls.modify inner fun l => { l with outer := some outer }
    ls := ls.modify outer fun l => { l with isInner := false }
    return ls

/-- `loop.nearestOuterLoop(sdom, b)`. -/
def nearestOuterLoop (t : DomTree) (ls : Array Loop) (l : Nat) (b : ID) : Option Nat := Id.run do
  let mut o := ls[l]!.outer
  for _ in [0:ls.size + 1] do
    match o with
    | some x => if t.isAncestorEq ls[x]!.header b then return some x else o := ls[x]!.outer
    | none => return none
  return o

/-- `loop.isWithinOrEq(ll)` (`ll = none`: the whole function). -/
def isWithinOrEq (ls : Array Loop) (l : Option Nat) (ll : Option Nat) : Bool := Id.run do
  match ll with
  | none => return true
  | some ll =>
    let mut l := l
    for _ in [0:ls.size + 1] do
      match l with
      | some x => if x == ll then return true else l := ls[x]!.outer
      | none => return false
    return false

end LoopNest

/-- `loopnestfor(f)` with postorder `po` and dominator tree `t`; `error` for its depth
self-check ("bad depth calculation"). -/
def loopnest (f : Func) (po : Array ID) (t : DomTree) : Except String LoopNest := do
  let n := f.blockTab.size
  let mut b2l : Array (Option Nat) := Array.replicate n none
  let mut loops : Array Loop := #[]
  let mut visited : Array Bool := Array.replicate n false
  let mut sawIrred := false
  for b in po do
    let mut innermost : Option Nat := none
    for bb in succIDs f b do
      let mut l := b2l[bb]?.join
      if t.isAncestorEq bb b then
        if l.isNone then
          loops := loops.push { header := bb }
          l := some (loops.size - 1)
          b2l := b2l.set! bb l
      else if !(visited[bb]?.getD false) then
        sawIrred := true
      else if let some x := l then
        if !t.isAncestorEq loops[x]!.header b then
          l := LoopNest.nearestOuterLoop t loops x b
      match l with
      | none => continue
      | some x =>
        if innermost == some x then continue
        match innermost with
        | none => innermost := some x
        | some i =>
          if t.isAncestor loops[i]!.header loops[x]!.header then
            loops := LoopNest.outerinner t (loops.size + 1) loops i x
            innermost := some x
          else if t.isAncestor loops[x]!.header loops[i]!.header then
            loops := LoopNest.outerinner t (loops.size + 1) loops x i
    if let some i := innermost then
      b2l := b2l.set! b (some i)
      loops := loops.modify i fun l => { l with nBlocks := l.nBlocks + 1 }
    visited := visited.set! b true
  -- depths
  for h : k in [0:loops.size] do
    if loops[k]!.depth != 0 then continue
    let mut d := 0
    let mut x := some k
    for _ in [0:loops.size + 1] do
      match x with
      | some y =>
        if loops[y]!.depth != 0 then
          d := d + loops[y]!.depth
          break
        d := d + 1
        x := loops[y]!.outer
      | none => break
    x := some k
    for _ in [0:loops.size + 1] do
      match x with
      | some y =>
        if loops[y]!.depth != 0 then break
        loops := loops.modify y fun l => { l with depth := d }
        d := d - 1
        x := loops[y]!.outer
      | none => break
  for l in loops do
    let want := match l.outer with
      | some o => loops[o]!.depth + 1
      | none => 1
    if l.depth != want then
      throw s!"bad depth calculation for loop b{l.header}: got {l.depth} want {want}"
  return { b2l, loops, hasIrreducible := sawIrred }

end CheckCfg

end GoFV.SSA
