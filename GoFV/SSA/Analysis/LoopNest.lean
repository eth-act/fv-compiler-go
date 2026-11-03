import GoFV.SSA.Analysis.SparseTree

/-!
# Loop nest (`loopnestfor`, `likelyadjust.go`)

A port of Go's `loopnestfor`: loops found from the postorder and the dominator tree, each
block's innermost loop (`b2l`), loop nesting (`outer`), depths with Go's own self-check, and
whether an irreducible loop was seen. Used by the checker's loop-construction check
(`check.go`) and, through `Func.loopnestfor`/`Func.loopnest` (`CfgCache`, which pass the
cached postorder and dominator tree), by the lowered passes; `po` and `t` are passed
explicitly (Go reads `f.postorder()` and `f.Sdom()`).
-/

namespace GoFV.SSA.Analysis

/-- Successor block IDs of `b` in `f` (missing blocks are skipped). -/
@[inline] def succIDs (f : Func) (b : ID) : Array ID :=
  match f.block? b with
  | some blk => blk.succs.map (·.b)
  | none => #[]

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
def outerinner (t : SparseTree) : Nat → Array Loop → Nat → Nat → Array Loop
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
def nearestOuterLoop (t : SparseTree) (ls : Array Loop) (l : Nat) (b : ID) : Option Nat := Id.run do
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
def loopnest (f : Func) (po : Array ID) (t : SparseTree) : Except String LoopNest := do
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

end GoFV.SSA.Analysis
