/-
Exact port of Go's unstable sort: `slices.SortFunc` (`src/slices/zsortanyfunc.go`,
`pdqsortCmpFunc` and helpers; `src/slices/sort.go` for `xorshift`, `nextPowerOfTwo`) and
`sort.Sort` (`src/sort/zsortinterface.go`), go1.27.3. Both files are generated from one
template; apart from `cmp(x, y) < 0` vs `data.Less(i, j)` they are identical, and `sort.Sort`'s
early return for `n <= 1` is a no-op of `pdqsort`. So one algorithm, parameterised by a `less`
function, serves both.

The port performs the same comparisons and swaps in the same order as Go, so the result equals
Go's for every comparator, including ones that are not strict weak orders (ties, non-transitive
comparators: `generic cse`, `storeOrder`; docs/PASSES.md §1.5).

Every Go loop is a structurally recursive function with an explicit iteration bound (fuel)
that is never exhausted: the comment at each call states why the bound suffices. Indices are
`Nat`; every Go index expression in this algorithm is non-negative and every Go subtraction
used here stays non-negative (checked at each site).
-/

namespace GoFV.Util.PdqSort

/-- `bits.Len(uint(n))`: number of bits needed to represent `n` (0 for 0). -/
def bitLen (n : Nat) : Nat := go n n
where
  /-- `fuel ≥ n` suffices: `n` halves at each step. -/
  go : Nat → Nat → Nat
    | 0, _ => 0
    | fuel + 1, n => if n = 0 then 0 else go fuel (n / 2) + 1

/-- `(*xorshift).Next` (`slices/sort.go`): returns the new state, which is also the output. -/
def xorshiftNext (r : UInt64) : UInt64 :=
  let r := r ^^^ (r <<< 13)
  let r := r ^^^ (r >>> 7)
  r ^^^ (r <<< 17)

/-- `sortedHint`. -/
inductive Hint where
  | unknown
  | increasing
  | decreasing
  deriving DecidableEq, Repr

section
variable {α : Type u} [Inhabited α] (lt : α → α → Bool)

/-- `for c(i) { i++ }`, at most `fuel` iterations; returns the final `i`. -/
def scanUp (c : Nat → Bool) : (fuel i : Nat) → Nat
  | 0, i => i
  | fuel + 1, i => if c i then scanUp c fuel (i + 1) else i

/-- `for c(j) { j-- }`, at most `fuel` iterations; returns the final `j`. -/
def scanDown (c : Nat → Bool) : (fuel j : Nat) → Nat
  | 0, j => j
  | fuel + 1, j => if c j then scanDown c fuel (j - 1) else j

/-- Inner loop of `insertionSortCmpFunc`: `for j := a+k; j > a && less(data[j], data[j-1]); j--`. -/
def insertionShift (a : Nat) : Nat → Array α → Array α
  | 0, d => d
  | k + 1, d =>
    let j := a + k + 1
    if lt d[j]! d[j - 1]! then insertionShift a k (d.swapIfInBounds j (j - 1)) else d

/-- Outer loop of `insertionSortCmpFunc`: `n` iterations starting at `i`. -/
def insertionLoop (a : Nat) : Nat → Nat → Array α → Array α
  | _, 0, d => d
  | i, n + 1, d => insertionLoop a (i + 1) n (insertionShift lt a (i - a) d)

/-- `insertionSortCmpFunc(data, a, b)`: `for i := a + 1; i < b; i++`. -/
def insertionSort (d : Array α) (a b : Nat) : Array α :=
  insertionLoop lt a (a + 1) (b - (a + 1)) d

/-- `siftDownCmpFunc(data, root, hi, first)`. `root` grows strictly while `2*root+1 < hi`,
so `fuel = hi + 1` iterations suffice. -/
def siftDown (hi first : Nat) : (fuel root : Nat) → Array α → Array α
  | 0, _, d => d
  | fuel + 1, root, d =>
    let child := 2 * root + 1
    if child ≥ hi then d
    else
      let child :=
        if child + 1 < hi && lt d[first + child]! d[first + child + 1]! then child + 1 else child
      if !lt d[first + root]! d[first + child]! then d
      else siftDown hi first fuel child (d.swapIfInBounds (first + root) (first + child))

/-- Heap construction loop: `for i := top; i >= 0; i--`. -/
def heapBuild (hi first : Nat) : Nat → Array α → Array α
  | 0, d => siftDown lt hi first (hi + 1) 0 d
  | i + 1, d => heapBuild hi first i (siftDown lt hi first (hi + 1) (i + 1) d)

/-- Pop loop: `for i := n - 1; i >= 0; i--` (called with `n = hi`). -/
def heapPop (first : Nat) : Nat → Array α → Array α
  | 0, d => d
  | i + 1, d =>
    heapPop first i (siftDown lt i first (i + 1) 0 (d.swapIfInBounds first (first + i)))

/-- `heapSortCmpFunc(data, a, b)`. Go's `(hi-1)/2` with `hi = 0` is `0`, as in `Nat`. -/
def heapSort (d : Array α) (a b : Nat) : Array α :=
  let hi := b - a
  heapPop lt a hi (heapBuild lt hi a ((hi - 1) / 2) d)

/-- `order2CmpFunc`: returns `(x, y, swaps)`. -/
def order2 (d : Array α) (a b swaps : Nat) : Nat × Nat × Nat :=
  if lt d[b]! d[a]! then (b, a, swaps + 1) else (a, b, swaps)

/-- `medianCmpFunc`: returns `(median index, swaps)`. -/
def median (d : Array α) (a b c swaps : Nat) : Nat × Nat :=
  let (a, b, swaps) := order2 lt d a b swaps
  let (b, _, swaps) := order2 lt d b c swaps
  let (_, b, swaps) := order2 lt d a b swaps
  (b, swaps)

/-- `medianAdjacentCmpFunc` (only called with `a ≥ 1`). -/
def medianAdjacent (d : Array α) (a swaps : Nat) : Nat × Nat :=
  median lt d (a - 1) a (a + 1) swaps

/-- `choosePivotCmpFunc`. -/
def choosePivot (d : Array α) (a b : Nat) : Nat × Hint :=
  let l := b - a
  let i := a + l / 4 * 1
  let j := a + l / 4 * 2
  let k := a + l / 4 * 3
  let (j, swaps) :=
    if l ≥ 8 then
      let (i, j, k, swaps) :=
        if l ≥ 50 then
          let (i, swaps) := medianAdjacent lt d i 0
          let (j, swaps) := medianAdjacent lt d j swaps
          let (k, swaps) := medianAdjacent lt d k swaps
          (i, j, k, swaps)
        else (i, j, k, 0)
      median lt d i j k swaps
    else (j, 0)
  if swaps = 0 then (j, .increasing)
  else if swaps = 12 then (j, .decreasing)
  else (j, .unknown)

/-- `reverseRangeCmpFunc` loop: `for i < j { swap(i, j); i++; j-- }`. -/
def reverseLoop : (fuel i j : Nat) → Array α → Array α
  | 0, _, _, d => d
  | fuel + 1, i, j, d =>
    if i < j then reverseLoop fuel (i + 1) (j - 1) (d.swapIfInBounds i j) else d

/-- `reverseRangeCmpFunc(data, a, b)` (only called with `b > a`). -/
def reverseRange (d : Array α) (a b : Nat) : Array α :=
  reverseLoop (b - a) a (b - 1) d

/-- Main loop of `partitionCmpFunc`; the pivot is at `a`. Returns the final `j`. Each
iteration increases `i`, so `fuel = b - a` suffices. `j ≥ i ≥ 1` before every `j-1`. -/
def partitionLoop (a : Nat) : (fuel i j : Nat) → Array α → Nat × Array α
  | 0, _, j, d => (j, d)
  | fuel + 1, i, j, d =>
    let i := scanUp (fun i => i ≤ j && lt d[i]! d[a]!) (j + 1 - i) i
    let j := scanDown (fun j => i ≤ j && !lt d[j]! d[a]!) (j + 1 - i) j
    if i > j then (j, d)
    else partitionLoop a fuel (i + 1) (j - 1) (d.swapIfInBounds i j)

/-- `partitionCmpFunc(data, a, b, pivot)`: `(newpivot, alreadyPartitioned, data)`. -/
def partition (d : Array α) (a b pivot : Nat) : Nat × Bool × Array α :=
  let d := d.swapIfInBounds a pivot
  let i := a + 1
  let j := b - 1
  let i := scanUp (fun i => i ≤ j && lt d[i]! d[a]!) (j + 1 - i) i
  let j := scanDown (fun j => i ≤ j && !lt d[j]! d[a]!) (j + 1 - i) j
  if i > j then (j, true, d.swapIfInBounds j a)
  else
    let d := d.swapIfInBounds i j
    let (j, d) := partitionLoop lt a (b - a) (i + 1) (j - 1) d
    (j, false, d.swapIfInBounds j a)

/-- Loop of `partitionEqualCmpFunc`; the pivot is at `a`. Returns the final `i`. -/
def partitionEqualLoop (a : Nat) : (fuel i j : Nat) → Array α → Nat × Array α
  | 0, i, _, d => (i, d)
  | fuel + 1, i, j, d =>
    let i := scanUp (fun i => i ≤ j && !lt d[a]! d[i]!) (j + 1 - i) i
    let j := scanDown (fun j => i ≤ j && lt d[a]! d[j]!) (j + 1 - i) j
    if i > j then (i, d)
    else partitionEqualLoop a fuel (i + 1) (j - 1) (d.swapIfInBounds i j)

/-- `partitionEqualCmpFunc(data, a, b, pivot)`: `(newpivot, data)`. -/
def partitionEqual (d : Array α) (a b pivot : Nat) : Nat × Array α :=
  partitionEqualLoop lt a (b - a) (a + 1) (b - 1) (d.swapIfInBounds a pivot)

/-- "Shift the smaller one to the left": `for j := J; j >= 1; j--` (note: bounded by 1, not
by `a + 1`, as in Go). -/
def shiftLeft : Nat → Array α → Array α
  | 0, d => d
  | j + 1, d => if !lt d[j + 1]! d[j]! then d else shiftLeft j (d.swapIfInBounds (j + 1) j)

/-- "Shift the greater one to the right": `for j := J; j < b; j++`. -/
def shiftRight (b : Nat) : (fuel j : Nat) → Array α → Array α
  | 0, _, d => d
  | fuel + 1, j, d =>
    if j < b then
      if !lt d[j]! d[j - 1]! then d else shiftRight b fuel (j + 1) (d.swapIfInBounds j (j - 1))
    else d

/-- Step loop of `partialInsertionSortCmpFunc` (`maxSteps = 5`, `shortestShifting = 50`). -/
def partialInsertionLoop (a b : Nat) : (steps i : Nat) → Array α → Bool × Array α
  | 0, _, d => (false, d)
  | steps + 1, i, d =>
    let i := scanUp (fun i => i < b && !lt d[i]! d[i - 1]!) (b - i) i
    if i = b then (true, d)
    else if b - a < 50 then (false, d)
    else
      let d := d.swapIfInBounds i (i - 1)
      let d := if i - a ≥ 2 then shiftLeft lt (i - 1) d else d
      let d := if b - i ≥ 2 then shiftRight lt b (b - i) (i + 1) d else d
      partialInsertionLoop a b steps i d

/-- `partialInsertionSortCmpFunc(data, a, b)`: `(sorted, data)`. -/
def partialInsertionSort (d : Array α) (a b : Nat) : Bool × Array α :=
  partialInsertionLoop lt a b 5 (a + 1) d

end

/-- One iteration of `breakPatternsCmpFunc`'s loop: draw from the xorshift and swap. -/
def breakPatternsStep {α : Type u} (a length modulus : Nat) (st : UInt64 × Array α) (idx : Nat) :
    UInt64 × Array α :=
  let r := xorshiftNext st.1
  let other := r.toNat % modulus
  let other := if other ≥ length then other - length else other
  (r, st.2.swapIfInBounds idx (a + other))

/-- `breakPatternsCmpFunc(data, a, b)`: three swaps driven by an xorshift seeded by the length.
`uint(r) & (modulus-1)` is `r % modulus` since `modulus = nextPowerOfTwo(length)`. -/
def breakPatterns {α : Type u} (d : Array α) (a b : Nat) : Array α :=
  let length := b - a
  if length ≥ 8 then
    let modulus := 2 ^ bitLen length
    let idx := a + length / 4 * 2 - 1
    let st := breakPatternsStep a length modulus (UInt64.ofNat length, d) idx
    let st := breakPatternsStep a length modulus st (idx + 1)
    (breakPatternsStep a length modulus st (idx + 2)).2
  else d

section
variable {α : Type u} [Inhabited α] (lt : α → α → Bool)

/-- `pdqsortCmpFunc(data, a, b, limit)`. Each loop iteration and each recursive call works on
a strictly shorter range, so `fuel ≥ b - a` suffices (with fuel `0` the range is empty). -/
def pdqsort : (fuel : Nat) → Array α → (a b limit : Nat) → (wasBalanced wasPartitioned : Bool) →
    Array α
  | 0, d, _, _, _, _, _ => d
  | fuel + 1, d, a, b, limit, wasBalanced, wasPartitioned =>
    let length := b - a
    if length ≤ 12 then insertionSort lt d a b
    else if limit = 0 then heapSort lt d a b
    else
      let (d, limit) := if !wasBalanced then (breakPatterns d a b, limit - 1) else (d, limit)
      let (pivot, hint) := choosePivot lt d a b
      let (d, pivot, hint) :=
        if hint = .decreasing then (reverseRange d a b, (b - 1) - (pivot - a), Hint.increasing)
        else (d, pivot, hint)
      let (sorted, d) :=
        if wasBalanced && wasPartitioned && hint = .increasing then
          partialInsertionSort lt d a b
        else (false, d)
      if sorted then d
      else if a > 0 && !lt d[a - 1]! d[pivot]! then
        let (mid, d) := partitionEqual lt d a b pivot
        pdqsort fuel d mid b limit wasBalanced wasPartitioned
      else
        let (mid, alreadyPartitioned, d) := partition lt d a b pivot
        let leftLen := mid - a
        let rightLen := b - mid
        let balanceThreshold := length / 8
        if leftLen < rightLen then
          let d := pdqsort fuel d a mid limit true true
          pdqsort fuel d (mid + 1) b limit (leftLen ≥ balanceThreshold) alreadyPartitioned
        else
          let d := pdqsort fuel d (mid + 1) b limit true true
          pdqsort fuel d a mid limit (rightLen ≥ balanceThreshold) alreadyPartitioned

/-- Go's unstable sort with a `less` function: `sort.Sort` and `slices.SortFunc` with
`less x y := cmp(x, y) < 0`. -/
def sortBy (d : Array α) : Array α :=
  pdqsort lt d.size d 0 d.size (bitLen d.size) true true

end

/-- `slices.SortFunc(x, cmp)`. -/
def sortFunc {α : Type u} [Inhabited α] (cmp : α → α → Int) (d : Array α) : Array α :=
  sortBy (fun x y => decide (cmp x y < 0)) d

/-! ## The result is a permutation of the input -/

open Array (Perm)

section
variable {α : Type u} [Inhabited α] (lt : α → α → Bool)

omit [Inhabited α] in
theorem swapIfInBounds_perm (d : Array α) (i j : Nat) : (d.swapIfInBounds i j).Perm d := by
  rw [Array.swapIfInBounds_def]
  split
  · split
    · exact Array.swap_perm ..
    · exact .rfl
  · exact .rfl

theorem insertionShift_perm (a k : Nat) (d : Array α) : (insertionShift lt a k d).Perm d := by
  induction k generalizing d with
  | zero => exact .rfl
  | succ k ih =>
    simp only [insertionShift]
    split
    · exact (ih _).trans (swapIfInBounds_perm ..)
    · exact .rfl

theorem insertionSort_perm (d : Array α) (a b : Nat) : (insertionSort lt d a b).Perm d := by
  suffices ∀ i n d, (insertionLoop lt a i n d).Perm d from this ..
  intro i n
  induction n generalizing i with
  | zero => intro d; exact .rfl
  | succ n ih => intro d; exact (ih _ _).trans (insertionShift_perm ..)

theorem siftDown_perm (hi first fuel root : Nat) (d : Array α) :
    (siftDown lt hi first fuel root d).Perm d := by
  induction fuel generalizing root d with
  | zero => exact .rfl
  | succ fuel ih =>
    simp only [siftDown]
    split
    · exact .rfl
    · split <;> split <;> first | exact .rfl | exact (ih ..).trans (swapIfInBounds_perm ..)

theorem heapSort_perm (d : Array α) (a b : Nat) : (heapSort lt d a b).Perm d := by
  have hb : ∀ hi i d, (heapBuild lt hi a i d).Perm d := by
    intro hi i
    induction i with
    | zero => intro d; exact siftDown_perm ..
    | succ i ih => intro d; exact (ih _).trans (siftDown_perm ..)
  have hp : ∀ i d, (heapPop lt a i d).Perm d := by
    intro i
    induction i with
    | zero => intro d; exact .rfl
    | succ i ih =>
      intro d; exact (ih _).trans ((siftDown_perm ..).trans (swapIfInBounds_perm ..))
  exact (hp ..).trans (hb ..)

omit [Inhabited α] in
theorem reverseRange_perm (d : Array α) (a b : Nat) : (reverseRange d a b).Perm d := by
  suffices ∀ fuel i j d, (reverseLoop fuel i j d : Array α).Perm d from this ..
  intro fuel
  induction fuel with
  | zero => intro _ _ d; exact .rfl
  | succ fuel ih =>
    intro i j d
    simp only [reverseLoop]
    split
    · exact (ih ..).trans (swapIfInBounds_perm ..)
    · exact .rfl

theorem partition_perm (d : Array α) (a b pivot : Nat) :
    (partition lt d a b pivot).2.2.Perm d := by
  have hl : ∀ fuel i j d, (partitionLoop lt a fuel i j d).2.Perm d := by
    intro fuel
    induction fuel with
    | zero => intro _ _ d; exact .rfl
    | succ fuel ih =>
      intro i j d
      simp only [partitionLoop]
      split
      · exact .rfl
      · exact (ih ..).trans (swapIfInBounds_perm ..)
  simp only [partition]
  split
  · exact (swapIfInBounds_perm ..).trans (swapIfInBounds_perm ..)
  · exact (swapIfInBounds_perm ..).trans <|
      (hl ..).trans <| (swapIfInBounds_perm ..).trans (swapIfInBounds_perm ..)

theorem partitionEqual_perm (d : Array α) (a b pivot : Nat) :
    (partitionEqual lt d a b pivot).2.Perm d := by
  have hl : ∀ fuel i j d, (partitionEqualLoop lt a fuel i j d).2.Perm d := by
    intro fuel
    induction fuel with
    | zero => intro _ _ d; exact .rfl
    | succ fuel ih =>
      intro i j d
      simp only [partitionEqualLoop]
      split
      · exact .rfl
      · exact (ih ..).trans (swapIfInBounds_perm ..)
  exact (hl ..).trans (swapIfInBounds_perm ..)

theorem partialInsertionSort_perm (d : Array α) (a b : Nat) :
    (partialInsertionSort lt d a b).2.Perm d := by
  have hsl : ∀ j d, (shiftLeft lt j d).Perm d := by
    intro j
    induction j with
    | zero => intro d; exact .rfl
    | succ j ih =>
      intro d
      simp only [shiftLeft]
      split
      · exact .rfl
      · exact (ih _).trans (swapIfInBounds_perm ..)
  have hsr : ∀ fuel j d, (shiftRight lt b fuel j d).Perm d := by
    intro fuel
    induction fuel with
    | zero => intro _ d; exact .rfl
    | succ fuel ih =>
      intro j d
      simp only [shiftRight]
      split
      · split
        · exact .rfl
        · exact (ih ..).trans (swapIfInBounds_perm ..)
      · exact .rfl
  have hl : ∀ steps i d, (partialInsertionLoop lt a b steps i d).2.Perm d := by
    intro steps
    induction steps with
    | zero => intro _ d; exact .rfl
    | succ steps ih =>
      intro i d
      simp only [partialInsertionLoop]
      generalize scanUp _ _ _ = i'
      split
      · exact .rfl
      · split
        · exact .rfl
        · refine (ih ..).trans ?_
          have h0 := swapIfInBounds_perm d i' (i' - 1)
          generalize d.swapIfInBounds i' (i' - 1) = d₁ at h0 ⊢
          have h1 : (if i' - a ≥ 2 then shiftLeft lt (i' - 1) d₁ else d₁).Perm d₁ := by
            split
            · exact hsl ..
            · exact .rfl
          generalize (if i' - a ≥ 2 then shiftLeft lt (i' - 1) d₁ else d₁) = d₂ at h1 ⊢
          split
          · exact (hsr ..).trans (h1.trans h0)
          · exact h1.trans h0
  exact hl ..

omit [Inhabited α] in
theorem breakPatterns_perm (d : Array α) (a b : Nat) : (breakPatterns d a b).Perm d := by
  have hs : ∀ a length modulus (st : UInt64 × Array α) idx,
      (breakPatternsStep a length modulus st idx).2.Perm st.2 :=
    fun _ _ _ _ _ => swapIfInBounds_perm ..
  simp only [breakPatterns]
  split
  · exact (hs ..).trans <| (hs ..).trans (hs ..)
  · exact .rfl

theorem pdqsort_perm (fuel : Nat) (d : Array α) (a b limit : Nat) (wb wp : Bool) :
    (pdqsort lt fuel d a b limit wb wp).Perm d := by
  induction fuel generalizing d a b limit wb wp with
  | zero => exact .rfl
  | succ fuel ih =>
    simp only [pdqsort]
    split
    · exact insertionSort_perm ..
    split
    · exact heapSort_perm ..
    -- `d₁`: after breakPatterns, `d₂`: after the optional reverse, `d₃`: after the optional
    -- partial insertion sort.
    have h₁ : (if !wb then (breakPatterns d a b, limit - 1) else (d, limit)).1.Perm d := by
      split
      · exact breakPatterns_perm ..
      · exact .rfl
    generalize (if !wb then (breakPatterns d a b, limit - 1) else (d, limit)) = s₁ at h₁ ⊢
    obtain ⟨d₁, limit₁⟩ := s₁
    generalize choosePivot lt d₁ a b = cp
    obtain ⟨pivot, hint⟩ := cp
    have h₂ : (if hint = .decreasing then (reverseRange d₁ a b, (b - 1) - (pivot - a),
        Hint.increasing) else (d₁, pivot, hint)).1.Perm d₁ := by
      split
      · exact reverseRange_perm ..
      · exact .rfl
    generalize (if hint = .decreasing then (reverseRange d₁ a b, (b - 1) - (pivot - a),
        Hint.increasing) else (d₁, pivot, hint)) = s₂ at h₂ ⊢
    obtain ⟨d₂, pivot₂, hint₂⟩ := s₂
    have h₃ : (if wb && wp && hint₂ = .increasing then partialInsertionSort lt d₂ a b
        else (false, d₂)).2.Perm d₂ := by
      split
      · exact partialInsertionSort_perm ..
      · exact .rfl
    generalize (if wb && wp && hint₂ = .increasing then partialInsertionSort lt d₂ a b
        else (false, d₂)) = s₃ at h₃ ⊢
    obtain ⟨sorted, d₃⟩ := s₃
    have h₃' : d₃.Perm d := h₃.trans (h₂.trans h₁)
    simp only
    split
    · exact h₃'
    split
    · have hp := partitionEqual_perm lt d₃ a b pivot₂
      generalize partitionEqual lt d₃ a b pivot₂ = pe at hp ⊢
      obtain ⟨mid, d₄⟩ := pe
      exact (ih ..).trans (hp.trans h₃')
    · have hp := partition_perm lt d₃ a b pivot₂
      generalize partition lt d₃ a b pivot₂ = pe at hp ⊢
      obtain ⟨mid, ap, d₄⟩ := pe
      simp only
      split
      · exact (ih ..).trans <| (ih ..).trans (hp.trans h₃')
      · exact (ih ..).trans <| (ih ..).trans (hp.trans h₃')

/-- Go's sort returns a permutation of its input, for every `less` function. -/
theorem sortBy_perm (d : Array α) : (sortBy lt d).Perm d :=
  pdqsort_perm ..

theorem sortFunc_perm (cmp : α → α → Int) (d : Array α) : (sortFunc cmp d).Perm d :=
  sortBy_perm ..

end

end GoFV.Util.PdqSort
