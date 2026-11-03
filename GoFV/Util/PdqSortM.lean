import GoFV.Util.PdqSort

/-!
# Go's unstable sort with an effectful comparator

`GoFV.Util.PdqSort` (`slices.SortFunc` / `sort.Sort`, go1.27.3) with the comparator in a monad:
for comparators that change state while the sort runs, e.g. `pair`'s load sort, which numbers
aux values on their first comparison (`pair.go:125-180`; docs/PASSES2.md §1.7). Definition by
definition the same algorithm as `PdqSort` (same comparisons, in the same order, with the same
short-circuits, and the same swaps), with each `lt` call a monadic action; the fuel arguments
and their bounds are `PdqSort`'s. `scripts/util-difftest.sh` checks it against Go together with
the pure port.
-/

namespace GoFV.Util.PdqSortM

open GoFV.Util.PdqSort (bitLen breakPatterns Hint)

section
variable {m : Type → Type} [Monad m] {α : Type} [Inhabited α] (lt : α → α → m Bool)

/-- `for c(i) { i++ }`, at most `fuel` iterations; returns the final `i`. -/
def scanUp (c : Nat → m Bool) : (fuel i : Nat) → m Nat
  | 0, i => pure i
  | fuel + 1, i => do if ← c i then scanUp c fuel (i + 1) else pure i

/-- `for c(j) { j-- }`, at most `fuel` iterations; returns the final `j`. -/
def scanDown (c : Nat → m Bool) : (fuel j : Nat) → m Nat
  | 0, j => pure j
  | fuel + 1, j => do if ← c j then scanDown c fuel (j - 1) else pure j

/-- `cond && lt x y`, `lt` called only if `cond`. -/
@[inline] def andLt (cond : Bool) (x y : α) : m Bool := if cond then lt x y else pure false

/-- `cond && !lt x y`, `lt` called only if `cond`. -/
@[inline] def andNotLt (cond : Bool) (x y : α) : m Bool :=
  if cond then do return !(← lt x y) else pure false

/-- `PdqSort.insertionShift`. -/
def insertionShift (a : Nat) : Nat → Array α → m (Array α)
  | 0, d => pure d
  | k + 1, d => do
    let j := a + k + 1
    if ← lt d[j]! d[j - 1]! then insertionShift a k (d.swapIfInBounds j (j - 1)) else pure d

/-- `PdqSort.insertionLoop`. -/
def insertionLoop (a : Nat) : Nat → Nat → Array α → m (Array α)
  | _, 0, d => pure d
  | i, n + 1, d => do insertionLoop a (i + 1) n (← insertionShift lt a (i - a) d)

/-- `insertionSortCmpFunc(data, a, b)`. -/
def insertionSort (d : Array α) (a b : Nat) : m (Array α) :=
  insertionLoop lt a (a + 1) (b - (a + 1)) d

/-- `siftDownCmpFunc(data, root, hi, first)` (`PdqSort.siftDown`). -/
def siftDown (hi first : Nat) : (fuel root : Nat) → Array α → m (Array α)
  | 0, _, d => pure d
  | fuel + 1, root, d => do
    let child := 2 * root + 1
    if child ≥ hi then return d
    let child := if ← andLt lt (child + 1 < hi) d[first + child]! d[first + child + 1]! then
      child + 1 else child
    if !(← lt d[first + root]! d[first + child]!) then return d
    siftDown hi first fuel child (d.swapIfInBounds (first + root) (first + child))

/-- `PdqSort.heapBuild`. -/
def heapBuild (hi first : Nat) : Nat → Array α → m (Array α)
  | 0, d => siftDown lt hi first (hi + 1) 0 d
  | i + 1, d => do heapBuild hi first i (← siftDown lt hi first (hi + 1) (i + 1) d)

/-- `PdqSort.heapPop`. -/
def heapPop (first : Nat) : Nat → Array α → m (Array α)
  | 0, d => pure d
  | i + 1, d => do
    heapPop first i (← siftDown lt i first (i + 1) 0 (d.swapIfInBounds first (first + i)))

/-- `heapSortCmpFunc(data, a, b)`. -/
def heapSort (d : Array α) (a b : Nat) : m (Array α) := do
  let hi := b - a
  heapPop lt a hi (← heapBuild lt hi a ((hi - 1) / 2) d)

/-- `order2CmpFunc`: returns `(x, y, swaps)`. -/
def order2 (d : Array α) (a b swaps : Nat) : m (Nat × Nat × Nat) := do
  if ← lt d[b]! d[a]! then pure (b, a, swaps + 1) else pure (a, b, swaps)

/-- `medianCmpFunc`: returns `(median index, swaps)`. -/
def median (d : Array α) (a b c swaps : Nat) : m (Nat × Nat) := do
  let (a, b, swaps) ← order2 lt d a b swaps
  let (b, _, swaps) ← order2 lt d b c swaps
  let (_, b, swaps) ← order2 lt d a b swaps
  pure (b, swaps)

/-- `medianAdjacentCmpFunc` (only called with `a ≥ 1`). -/
def medianAdjacent (d : Array α) (a swaps : Nat) : m (Nat × Nat) :=
  median lt d (a - 1) a (a + 1) swaps

/-- `choosePivotCmpFunc`. -/
def choosePivot (d : Array α) (a b : Nat) : m (Nat × Hint) := do
  let l := b - a
  let i := a + l / 4 * 1
  let j := a + l / 4 * 2
  let k := a + l / 4 * 3
  let (j, swaps) ←
    if l ≥ 8 then do
      let (i, j, k, swaps) ←
        if l ≥ 50 then do
          let (i, swaps) ← medianAdjacent lt d i 0
          let (j, swaps) ← medianAdjacent lt d j swaps
          let (k, swaps) ← medianAdjacent lt d k swaps
          pure (i, j, k, swaps)
        else pure (i, j, k, 0)
      median lt d i j k swaps
    else pure (j, 0)
  if swaps = 0 then pure (j, .increasing)
  else if swaps = 12 then pure (j, .decreasing)
  else pure (j, .unknown)

/-- Main loop of `partitionCmpFunc` (`PdqSort.partitionLoop`). -/
def partitionLoop (a : Nat) : (fuel i j : Nat) → Array α → m (Nat × Array α)
  | 0, _, j, d => pure (j, d)
  | fuel + 1, i, j, d => do
    let i ← scanUp (fun i => andLt lt (i ≤ j) d[i]! d[a]!) (j + 1 - i) i
    let j ← scanDown (fun j => andNotLt lt (i ≤ j) d[j]! d[a]!) (j + 1 - i) j
    if i > j then pure (j, d)
    else partitionLoop a fuel (i + 1) (j - 1) (d.swapIfInBounds i j)

/-- `partitionCmpFunc(data, a, b, pivot)`: `(newpivot, alreadyPartitioned, data)`. -/
def partition (d : Array α) (a b pivot : Nat) : m (Nat × Bool × Array α) := do
  let d := d.swapIfInBounds a pivot
  let i := a + 1
  let j := b - 1
  let i ← scanUp (fun i => andLt lt (i ≤ j) d[i]! d[a]!) (j + 1 - i) i
  let j ← scanDown (fun j => andNotLt lt (i ≤ j) d[j]! d[a]!) (j + 1 - i) j
  if i > j then pure (j, true, d.swapIfInBounds j a)
  else
    let d := d.swapIfInBounds i j
    let (j, d) ← partitionLoop lt a (b - a) (i + 1) (j - 1) d
    pure (j, false, d.swapIfInBounds j a)

/-- Loop of `partitionEqualCmpFunc` (`PdqSort.partitionEqualLoop`). -/
def partitionEqualLoop (a : Nat) : (fuel i j : Nat) → Array α → m (Nat × Array α)
  | 0, i, _, d => pure (i, d)
  | fuel + 1, i, j, d => do
    let i ← scanUp (fun i => andNotLt lt (i ≤ j) d[a]! d[i]!) (j + 1 - i) i
    let j ← scanDown (fun j => andLt lt (i ≤ j) d[a]! d[j]!) (j + 1 - i) j
    if i > j then pure (i, d)
    else partitionEqualLoop a fuel (i + 1) (j - 1) (d.swapIfInBounds i j)

/-- `partitionEqualCmpFunc(data, a, b, pivot)`: `(newpivot, data)`. -/
def partitionEqual (d : Array α) (a b pivot : Nat) : m (Nat × Array α) :=
  partitionEqualLoop lt a (b - a) (a + 1) (b - 1) (d.swapIfInBounds a pivot)

/-- `PdqSort.shiftLeft`. -/
def shiftLeft : Nat → Array α → m (Array α)
  | 0, d => pure d
  | j + 1, d => do
    if !(← lt d[j + 1]! d[j]!) then pure d else shiftLeft j (d.swapIfInBounds (j + 1) j)

/-- `PdqSort.shiftRight`. -/
def shiftRight (b : Nat) : (fuel j : Nat) → Array α → m (Array α)
  | 0, _, d => pure d
  | fuel + 1, j, d => do
    if j < b then
      if !(← lt d[j]! d[j - 1]!) then pure d
      else shiftRight b fuel (j + 1) (d.swapIfInBounds j (j - 1))
    else pure d

/-- Step loop of `partialInsertionSortCmpFunc` (`PdqSort.partialInsertionLoop`). -/
def partialInsertionLoop (a b : Nat) : (steps i : Nat) → Array α → m (Bool × Array α)
  | 0, _, d => pure (false, d)
  | steps + 1, i, d => do
    let i ← scanUp (fun i => andNotLt lt (i < b) d[i]! d[i - 1]!) (b - i) i
    if i = b then return (true, d)
    if b - a < 50 then return (false, d)
    let d := d.swapIfInBounds i (i - 1)
    let d ← if i - a ≥ 2 then shiftLeft lt (i - 1) d else pure d
    let d ← if b - i ≥ 2 then shiftRight lt b (b - i) (i + 1) d else pure d
    partialInsertionLoop a b steps i d

/-- `partialInsertionSortCmpFunc(data, a, b)`: `(sorted, data)`. -/
def partialInsertionSort (d : Array α) (a b : Nat) : m (Bool × Array α) :=
  partialInsertionLoop lt a b 5 (a + 1) d

/-- `PdqSort.pdqPivot`: `(data, limit, pivot, sorted)`. -/
@[inline] def pdqPivot (d : Array α) (a b limit : Nat) (wasBalanced wasPartitioned : Bool) :
    m (Array α × Nat × Nat × Bool) := do
  let (d, limit) := if !wasBalanced then (breakPatterns d a b, limit - 1) else (d, limit)
  let (pivot, hint) ← choosePivot lt d a b
  let (d, pivot, hint) :=
    if hint = .decreasing then
      (PdqSort.reverseRange d a b, (b - 1) - (pivot - a), Hint.increasing)
    else (d, pivot, hint)
  let (sorted, d) ←
    if wasBalanced && wasPartitioned && hint = .increasing then partialInsertionSort lt d a b
    else pure (false, d)
  pure (d, limit, pivot, sorted)

/-- `PdqSort.pdqPartition`. -/
@[inline] def pdqPartition
    (rec : Array α → (a b limit : Nat) → (wasBalanced wasPartitioned : Bool) → m (Array α))
    (d : Array α) (a b limit pivot : Nat) (wasBalanced wasPartitioned : Bool) :
    m (Array α) := do
  if ← andNotLt lt (a > 0) d[a - 1]! d[pivot]! then
    let (mid, d) ← partitionEqual lt d a b pivot
    rec d mid b limit wasBalanced wasPartitioned
  else
    let (mid, alreadyPartitioned, d) ← partition lt d a b pivot
    let leftLen := mid - a
    let rightLen := b - mid
    let balanceThreshold := (b - a) / 8
    if leftLen < rightLen then
      let d ← rec d a mid limit true true
      rec d (mid + 1) b limit (leftLen ≥ balanceThreshold) alreadyPartitioned
    else
      let d ← rec d (mid + 1) b limit true true
      rec d a mid limit (rightLen ≥ balanceThreshold) alreadyPartitioned

/-- `PdqSort.pdqStep`. -/
@[inline] def pdqStep
    (rec : Array α → (a b limit : Nat) → (wasBalanced wasPartitioned : Bool) → m (Array α))
    (d : Array α) (a b limit : Nat) (wasBalanced wasPartitioned : Bool) : m (Array α) := do
  if b - a ≤ 12 then insertionSort lt d a b
  else if limit = 0 then heapSort lt d a b
  else
    let (d, limit, pivot, sorted) ← pdqPivot lt d a b limit wasBalanced wasPartitioned
    if sorted then pure d
    else pdqPartition lt rec d a b limit pivot wasBalanced wasPartitioned

/-- `pdqsortCmpFunc(data, a, b, limit)` (`PdqSort.pdqsort`). -/
def pdqsort : (fuel : Nat) → Array α → (a b limit : Nat) → (wasBalanced wasPartitioned : Bool) →
    m (Array α)
  | 0, d, _, _, _, _, _ => pure d
  | fuel + 1, d, a, b, limit, wasBalanced, wasPartitioned =>
    pdqStep lt (pdqsort fuel) d a b limit wasBalanced wasPartitioned

/-- Go's unstable sort with a `less` action. -/
def sortBy (d : Array α) : m (Array α) :=
  pdqsort lt d.size d 0 d.size (bitLen d.size) true true

end

/-- `slices.SortFunc(x, cmp)` with an effectful `cmp`. -/
def sortFunc {m : Type → Type} [Monad m] {α : Type} [Inhabited α] (cmp : α → α → m Int)
    (d : Array α) : m (Array α) :=
  sortBy (fun x y => do return decide ((← cmp x y) < 0)) d

end GoFV.Util.PdqSortM
