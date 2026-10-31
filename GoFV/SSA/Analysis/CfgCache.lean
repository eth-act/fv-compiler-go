import GoFV.SSA.Analysis.Postorder
import GoFV.SSA.Analysis.Dom
import GoFV.SSA.Analysis.SparseTree

/-!
# Cached CFG analyses

`f.postorder()`, `f.Idom()`, `f.Sdom()` (`ssa/func.go:766-800`, go1.27.3): each returns the
cached result if there is one, else computes it and caches it in `f.cache`. The caches are
dropped only by `invalidateCFG` (`GoFV.SSA.Alloc`), which Go calls from `AddEdgeTo`,
`removePred`, `removeSucc`, `NewBlock` and a few passes, **not** from `swapSuccessors`; so a
cached postorder (and the sparse tree built from it) can be stale, and that is observable
(docs/PASSES.md §1.3). Each accessor returns the result and the function with the updated
cache.
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

end GoFV.SSA.Func
