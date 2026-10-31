/-
Port of `cmd/compile/internal/ssa/sparseset.go` (go1.27.3).

`dense` holds the elements in insertion order; `remove` moves the last element into the hole;
`pop` takes the last element. Passes that iterate `contents` or pop depend on exactly this order
(docs/PASSES.md §1.4). The `sparse` index is kept as in Go, so `contains`/`add`/`remove` are
O(1); `WF` is the invariant under which it agrees with `dense`, and the lemmas below let proofs
reason about `dense` alone.

Keys are `Nat` (`GoFV.SSA.ID`). Go panics on a key `≥ cap` and on `pop` of an empty set; the
port panics there as well (`[x]!`, `back!`), and the lemmas assume neither happens.
-/

namespace GoFV.Util

/-- `sparseSet`. -/
structure SparseSet where
  dense : Array Nat
  sparse : Array Nat
  deriving Inhabited, Repr

namespace SparseSet

/-- `newSparseSet(n)`. -/
def new (n : Nat) : SparseSet := ⟨#[], Array.replicate n 0⟩

/-- `cap()`. -/
def cap (s : SparseSet) : Nat := s.sparse.size

/-- `size()`. -/
def size (s : SparseSet) : Nat := s.dense.size

/-- `contains(x)`. -/
def contains (s : SparseSet) (x : Nat) : Bool :=
  match s.dense[s.sparse[x]!]? with
  | some y => y == x
  | none => false

/-- `add(x)`. -/
def add (s : SparseSet) (x : Nat) : SparseSet :=
  if s.contains x then s else ⟨s.dense.push x, s.sparse.set! x s.dense.size⟩

/-- `addAll(a)` (also `addAllValues` on the values' IDs). -/
def addAll (s : SparseSet) (a : List Nat) : SparseSet := a.foldl add s

/-- `remove(x)`. -/
def remove (s : SparseSet) (x : Nat) : SparseSet :=
  let i := s.sparse[x]!
  match s.dense[i]? with
  | some z =>
    if z == x then
      let y := s.dense[s.dense.size - 1]!
      ⟨(s.dense.set! i y).pop, s.sparse.set! y i⟩
    else s
  | none => s

/-- `pop()`: the last element and the set without it. -/
def pop (s : SparseSet) : Nat × SparseSet := (s.dense.back!, { s with dense := s.dense.pop })

/-- `clear()`. -/
def clear (s : SparseSet) : SparseSet := { s with dense := #[] }

/-- `contents()`. -/
def contents (s : SparseSet) : Array Nat := s.dense

/-! ## Invariant and lemmas -/

/-- The `sparse` index of every element points back at its position in `dense`. -/
def WF (s : SparseSet) : Prop := ∀ i (h : i < s.dense.size), s.sparse[s.dense[i]]? = some i

theorem wf_new (n : Nat) : (new n).WF := by
  intro i h; simp [new] at h

/-- Elements of a well-formed set are distinct. -/
theorem nodup {s : SparseSet} (hs : s.WF) {i j : Nat} (hi : i < s.dense.size)
    (hj : j < s.dense.size) (h : s.dense[i] = s.dense[j]) : i = j := by
  have h1 := hs i hi
  have h2 := hs j hj
  rw [h] at h1
  grind

theorem sparse_dense {s : SparseSet} (hs : s.WF) {i : Nat} (hi : i < s.dense.size) :
    s.sparse[s.dense[i]]! = i := by
  have := hs i hi
  grind

theorem contains_eq {s : SparseSet} (hs : s.WF) (x : Nat) :
    s.contains x = decide (x ∈ s.dense) := by
  unfold contains
  by_cases hm : x ∈ s.dense
  · obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 hm
    rw [sparse_dense hs hj]
    simp [hj]
  · rw [decide_eq_false hm]
    split
    · next y hy =>
      rw [Array.getElem?_eq_some_iff] at hy
      obtain ⟨hi, rfl⟩ := hy
      simp only [beq_eq_false_iff_ne]
      intro he
      exact hm (he ▸ Array.getElem_mem hi)
    · rfl

theorem dense_add {s : SparseSet} (hs : s.WF) (x : Nat) :
    (s.add x).dense = if x ∈ s.dense then s.dense else s.dense.push x := by
  unfold add; rw [contains_eq hs]; by_cases h : x ∈ s.dense <;> simp [h]

theorem cap_add (s : SparseSet) (x : Nat) : (s.add x).cap = s.cap := by
  unfold add cap; split <;> simp

theorem wf_add {s : SparseSet} (hs : s.WF) {x : Nat} (hx : x < s.cap) : (s.add x).WF := by
  unfold add
  rw [contains_eq hs]
  by_cases hm : x ∈ s.dense
  · simpa [hm] using hs
  · simp only [hm, decide_false, Bool.false_eq_true, ite_false]
    intro i hi
    simp only [Array.size_push] at hi
    simp only [Array.set!_eq_setIfInBounds]
    by_cases hin : i < s.dense.size
    · have hne : s.dense[i] ≠ x := fun he => hm (Array.mem_iff_getElem.2 ⟨i, hin, he⟩)
      rw [Array.getElem_push_lt hin, Array.getElem?_setIfInBounds_ne (Ne.symm hne)]
      exact hs i hin
    · have : i = s.dense.size := by omega
      subst this
      simp only [Array.getElem_push_eq]
      exact Array.getElem?_setIfInBounds_self_of_lt hx

/-- `remove` of an element: the last element moves into its slot. -/
theorem remove_mem {s : SparseSet} (hs : s.WF) {i : Nat} (hi : i < s.dense.size) :
    s.remove s.dense[i] =
      ⟨(s.dense.setIfInBounds i s.dense[s.dense.size - 1]).pop,
        s.sparse.setIfInBounds s.dense[s.dense.size - 1] i⟩ := by
  unfold remove
  rw [sparse_dense hs hi]
  simp [hi, getElem!_pos s.dense (s.dense.size - 1) (by omega)]

theorem remove_not_mem {s : SparseSet} (hs : s.WF) {x : Nat} (h : x ∉ s.dense) :
    s.remove x = s := by
  have hc := contains_eq hs x
  rw [decide_eq_false h] at hc
  unfold contains at hc
  unfold remove
  dsimp only
  split
  · next z hz =>
    rw [hz] at hc
    simp only [beq_eq_false_iff_ne] at hc
    simp [hc]
  · rfl

theorem cap_remove {s : SparseSet} (hs : s.WF) (x : Nat) : (s.remove x).cap = s.cap := by
  by_cases h : x ∈ s.dense
  · obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 h
    rw [remove_mem hs hi]
    simp [cap]
  · rw [remove_not_mem hs h]

theorem wf_remove {s : SparseSet} (hs : s.WF) (x : Nat) : (s.remove x).WF := by
  by_cases h : x ∈ s.dense
  · obtain ⟨I, hI, rfl⟩ := Array.mem_iff_getElem.1 h
    rw [remove_mem hs hI]
    intro k hk
    simp only [Array.size_pop, Array.size_setIfInBounds] at hk
    simp only [Array.getElem_pop]
    rw [Array.getElem_setIfInBounds (by omega)]
    split
    · next hkI =>
      subst hkI
      have := hs (s.dense.size - 1) (by omega)
      exact Array.getElem?_setIfInBounds_self_of_lt (by grind)
    · next hkI =>
      have hne : s.dense[s.dense.size - 1] ≠ s.dense[k] := fun he =>
        absurd (nodup hs (by omega) (by omega) he) (by omega)
      rw [Array.getElem?_setIfInBounds_ne hne]
      exact hs k (by omega)
  · rw [remove_not_mem hs h]; exact hs

theorem mem_remove {s : SparseSet} (hs : s.WF) (x y : Nat) :
    y ∈ (s.remove x).dense ↔ y ∈ s.dense ∧ y ≠ x := by
  by_cases h : x ∈ s.dense
  · obtain ⟨I, hI, rfl⟩ := Array.mem_iff_getElem.1 h
    rw [remove_mem hs hI]
    simp only [Array.mem_iff_getElem, Array.size_pop, Array.size_setIfInBounds,
      Array.getElem_pop]
    constructor
    · rintro ⟨k, hk, rfl⟩
      rw [Array.getElem_setIfInBounds (by omega)]
      split
      · next hkI =>
        refine ⟨⟨_, by omega, rfl⟩, fun he => ?_⟩
        exact absurd (nodup hs (by omega) hI he) (by omega)
      · next hkI =>
        exact ⟨⟨_, by omega, rfl⟩, fun he => hkI (nodup hs (by omega) hI he).symm⟩
    · rintro ⟨⟨k, hk, rfl⟩, hne⟩
      have hkI : k ≠ I := fun h => hne (by subst h; rfl)
      by_cases hkl : k = s.dense.size - 1
      · subst hkl
        refine ⟨I, by omega, ?_⟩
        rw [Array.getElem_setIfInBounds (by omega)]
        simp
      · refine ⟨k, by omega, ?_⟩
        rw [Array.getElem_setIfInBounds (by omega)]
        simp [Ne.symm hkI]
  · rw [remove_not_mem hs h]
    exact ⟨fun hy => ⟨hy, fun he => h (he ▸ hy)⟩, fun hy => hy.1⟩

theorem pop_dense (s : SparseSet) : s.pop.2.dense = s.dense.pop := rfl

theorem pop_fst (s : SparseSet) : s.pop.1 = s.dense.back! := rfl

theorem wf_pop {s : SparseSet} (hs : s.WF) : s.pop.2.WF := by
  intro i hi
  simp only [pop, Array.size_pop] at hi ⊢
  simp only [Array.getElem_pop]
  exact hs i (by omega)

theorem wf_clear (s : SparseSet) : s.clear.WF := by
  intro i h; simp [clear] at h

theorem cap_clear (s : SparseSet) : s.clear.cap = s.cap := rfl

theorem cap_pop (s : SparseSet) : s.pop.2.cap = s.cap := rfl

end SparseSet

end GoFV.Util
