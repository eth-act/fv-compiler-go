import GoFV.SSA.Analysis.Postorder
import GoFV.SSA.Analysis.Dom
import GoFV.SSA.Analysis.SparseTree
import GoFV.SSA.Analysis.LoopNest

/-!
# Cached CFG analyses

`f.postorder()`, `f.Idom()`, `f.Sdom()`, `f.loopnest()` (`ssa/func.go:766-801`, go1.27.3): each
returns the cached result if there is one, else computes it and caches it in `f.cache`. The
caches are dropped only by `invalidateCFG` (`GoFV.SSA.Alloc`), which Go calls from `AddEdgeTo`,
`removePred`, `removeSucc`, `NewBlock` and a few passes, **not** from `swapSuccessors`; so a
cached postorder (and the sparse tree and loop nest built from it) can be stale, and that is
observable (docs/PASSES.md §1.3, docs/PASSES2.md §1.3). Each accessor returns the result and the
function with the updated cache.
-/

namespace GoFV.SSA.Func

open GoFV.SSA.Analysis

/-- `f.postorder()` / `f.Postorder()`. -/
def postorder (f : Func) : Array ID × Func :=
  match f.cache.postorder with
  | some po => (po, f)
  | none =>
    let po := Analysis.postorder f
    (po, { f with cache := { f.cache with postorder := some po } })

/-- `f.Idom()`: immediate dominators by block ID. -/
def idom (f : Func) : Array (Option ID) × Func :=
  match f.cache.idom with
  | some d => (d, f)
  | none =>
    let d := dominators f
    (d, { f with cache := { f.cache with idom := some d } })

/-- `f.Sdom()`: `newSparseTree(f, f.Idom())` over `f.postorder()`. -/
def sdom (f : Func) : SparseTree × Func :=
  match f.cache.sdom with
  | some t => (t, f)
  | none =>
    let (d, f) := f.idom
    let (po, f) := f.postorder
    let t := newSparseTree (f.bidLast + 1) f.entry po d
    (t, { f with cache := { f.cache with sdom := some t } })

/-- `loopnestfor(f)`: the loop nest over `f.postorder()` and `f.Sdom()` (both cached as a side
effect); the result is not cached (LICM builds its own nest this way). -/
def loopnestfor (f : Func) : Except String (Analysis.LoopNest × Func) := do
  let (po, f) := f.postorder
  let (t, f) := f.sdom
  return (← Analysis.loopnest f po t, f)

end GoFV.SSA.Func

namespace GoFV.SSA.Analysis.LoopNest

/-- The cached form (`f.cachedLoopnest`, format 5) of a loop nest. -/
def toCache (n : Analysis.LoopNest) : SSA.LoopNest where
  b2lSize := n.b2l.size
  irreducible := n.hasIrreducible
  loops := n.loops.map fun l =>
    { header := l.header, outer := l.outer, nBlocks := l.nBlocks, depth := l.depth,
      isInner := l.isInner, unavoidableCall := false }
  b2l := Id.run do
    let mut r := #[]
    for h : i in [0:n.b2l.size] do
      if let some l := n.b2l[i] then r := r.push (i, l)
    return r

/-- A cached loop nest as an `Analysis.LoopNest` (`b2l` dense, of the size it was built with). -/
def ofCache (c : SSA.LoopNest) : Analysis.LoopNest where
  b2l := c.b2l.foldl (init := Array.replicate c.b2lSize none) fun a (b, l) => a.set! b (some l)
  loops := c.loops.map fun l =>
    { header := l.header, outer := l.outer, nBlocks := l.nBlocks.toNat, depth := l.depth.toNat,
      isInner := l.isInner }
  hasIrreducible := c.irreducible

/-- `ln.b2l[b]`: the innermost loop of block `b` (`none` past the end, where Go would panic). -/
@[inline] def loopOf (n : Analysis.LoopNest) (b : ID) : Option Nat := n.b2l[b]?.join

end GoFV.SSA.Analysis.LoopNest

namespace GoFV.SSA.Func

/-- `f.loopnest()`: the cached loop nest (possibly stale), else `loopnestfor(f)`, which is then
cached. -/
def loopnest (f : Func) : Except String (Analysis.LoopNest × Func) := do
  match f.cache.loopnest with
  | some c => return (Analysis.LoopNest.ofCache c, f)
  | none =>
    let (n, f) ← f.loopnestfor
    return (n, { f with cache := { f.cache with loopnest := some n.toCache } })

end GoFV.SSA.Func
