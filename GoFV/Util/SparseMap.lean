/-
Port of `cmd/compile/internal/ssa/sparsemap.go` (go1.27.3): `genericSparseMap[K, V]` with
`K = ID` (`Nat`); Go's `sparseMap` is `SparseMap Int` (values are `int32`).

`dense` holds the entries in insertion order; `set` of a present key updates its entry in
place; `remove` moves the last entry into the hole (docs/PASSES.md §1.4). `get` returns `none`
where Go returns `(zero, false)`. As in `SparseSet`, `WF` is the invariant under which the
`sparse` index agrees with `dense`; Go panics on a key `≥ cap`, and so does the port.
-/

namespace GoFV.Util

/-- `sparseEntry[K, V]`. -/
structure SparseEntry (V : Type u) where
  key : Nat
  val : V
  deriving Inhabited, Repr, DecidableEq

/-- `genericSparseMap[ID, V]`. -/
structure SparseMap (V : Type u) where
  dense : Array (SparseEntry V)
  sparse : Array Nat
  deriving Inhabited, Repr

namespace SparseMap

variable {V : Type u}

/-- `newGenericSparseMap(n)`. -/
def new (n : Nat) : SparseMap V := ⟨#[], Array.replicate n 0⟩

/-- `cap()`. -/
def cap (s : SparseMap V) : Nat := s.sparse.size

/-- `size()`. -/
def size (s : SparseMap V) : Nat := s.dense.size

/-- `contains(k)`. -/
def contains (s : SparseMap V) (k : Nat) : Bool :=
  match s.dense[s.sparse[k]!]? with
  | some e => e.key == k
  | none => false

/-- `get(k)`. -/
def get (s : SparseMap V) (k : Nat) : Option V :=
  match s.dense[s.sparse[k]!]? with
  | some e => if e.key == k then some e.val else none
  | none => none

/-- `set(k, v)`. -/
def set (s : SparseMap V) (k : Nat) (v : V) : SparseMap V :=
  let i := s.sparse[k]!
  match s.dense[i]? with
  | some e =>
    if e.key == k then { s with dense := s.dense.set! i ⟨k, v⟩ }
    else ⟨s.dense.push ⟨k, v⟩, s.sparse.set! k s.dense.size⟩
  | none => ⟨s.dense.push ⟨k, v⟩, s.sparse.set! k s.dense.size⟩

/-- `remove(k)`. -/
def remove (s : SparseMap V) (k : Nat) : SparseMap V :=
  let i := s.sparse[k]!
  match s.dense[i]? with
  | some e =>
    if e.key == k then
      -- `dense` is non-empty here; `e` is only the (unused) fallback of the lookup.
      let y := s.dense[s.dense.size - 1]?.getD e
      ⟨(s.dense.set! i y).pop, s.sparse.set! y.key i⟩
    else s
  | none => s

/-- `clear()`. -/
def clear (s : SparseMap V) : SparseMap V := { s with dense := #[] }

/-- `contents()`. -/
def contents (s : SparseMap V) : Array (SparseEntry V) := s.dense

/-! ## Invariant and lemmas -/

/-- The keys in `dense` order. -/
def keys (s : SparseMap V) : Array Nat := s.dense.map (·.key)

/-- The `sparse` index of every entry's key points back at its position in `dense`. -/
def WF (s : SparseMap V) : Prop :=
  ∀ i (h : i < s.dense.size), s.sparse[s.dense[i].key]? = some i

theorem mem_keys {s : SparseMap V} {k : Nat} :
    k ∈ s.keys ↔ ∃ i, ∃ h : i < s.dense.size, s.dense[i].key = k := by
  simp only [keys, Array.mem_iff_getElem, Array.size_map, Array.getElem_map]

theorem wf_new (n : Nat) : (new n : SparseMap V).WF := by
  intro i h; simp [new] at h

/-- Keys of a well-formed map are distinct. -/
theorem nodup {s : SparseMap V} (hs : s.WF) {i j : Nat} (hi : i < s.dense.size)
    (hj : j < s.dense.size) (h : s.dense[i].key = s.dense[j].key) : i = j := by
  have h1 := hs i hi
  have h2 := hs j hj
  rw [h] at h1
  grind

theorem sparse_dense {s : SparseMap V} (hs : s.WF) {i : Nat} (hi : i < s.dense.size) :
    s.sparse[s.dense[i].key]! = i := by
  have := hs i hi
  grind

/-- The slot `sparse[k]` names an entry with key `k` only if `k` is a key. -/
theorem key_ne_of_not_mem {s : SparseMap V} {k : Nat} (h : k ∉ s.keys) {e : SparseEntry V}
    (he : s.dense[s.sparse[k]!]? = some e) : e.key ≠ k := by
  rw [Array.getElem?_eq_some_iff] at he
  obtain ⟨hi, rfl⟩ := he
  exact fun hk => h (mem_keys.2 ⟨_, hi, hk⟩)

theorem contains_eq {s : SparseMap V} (hs : s.WF) (k : Nat) :
    s.contains k = decide (k ∈ s.keys) := by
  unfold contains
  by_cases hm : k ∈ s.keys
  · obtain ⟨j, hj, rfl⟩ := mem_keys.1 hm
    rw [sparse_dense hs hj]
    simp [hj, hm]
  · rw [decide_eq_false hm]
    split
    · next e he => simpa using key_ne_of_not_mem hm he
    · rfl

theorem get_mem {s : SparseMap V} (hs : s.WF) {i : Nat} (hi : i < s.dense.size) :
    s.get s.dense[i].key = some s.dense[i].val := by
  unfold get
  rw [sparse_dense hs hi]
  simp [hi]

theorem get_not_mem {s : SparseMap V} {k : Nat} (h : k ∉ s.keys) : s.get k = none := by
  unfold get
  split
  · next e he => simp [key_ne_of_not_mem h he]
  · rfl

theorem set_mem {s : SparseMap V} (hs : s.WF) {i : Nat} (hi : i < s.dense.size) (v : V) :
    s.set s.dense[i].key v = { s with dense := s.dense.setIfInBounds i ⟨s.dense[i].key, v⟩ } := by
  unfold set
  rw [sparse_dense hs hi]
  simp [hi]

theorem set_not_mem {s : SparseMap V} {k : Nat} (h : k ∉ s.keys) (v : V) :
    s.set k v = ⟨s.dense.push ⟨k, v⟩, s.sparse.setIfInBounds k s.dense.size⟩ := by
  unfold set
  dsimp only
  split
  · next e he => simp [key_ne_of_not_mem h he]
  · rfl

theorem wf_set {s : SparseMap V} (hs : s.WF) {k : Nat} (hk : k < s.cap) (v : V) :
    (s.set k v).WF := by
  by_cases hm : k ∈ s.keys
  · obtain ⟨I, hI, rfl⟩ := mem_keys.1 hm
    rw [set_mem hs hI]
    intro j hj
    simp only [Array.size_setIfInBounds] at hj
    simp only
    rw [Array.getElem_setIfInBounds hj]
    split
    · next h => subst h; exact hs _ hI
    · exact hs j hj
  · rw [set_not_mem hm]
    intro i hi
    simp only [Array.size_push] at hi
    by_cases hin : i < s.dense.size
    · have hne : s.dense[i].key ≠ k := fun he => hm (mem_keys.2 ⟨i, hin, he⟩)
      simp only
      rw [Array.getElem_push_lt hin, Array.getElem?_setIfInBounds_ne (Ne.symm hne)]
      exact hs i hin
    · have : i = s.dense.size := by omega
      subst this
      simp only [Array.getElem_push_eq]
      exact Array.getElem?_setIfInBounds_self_of_lt hk

theorem cap_set {s : SparseMap V} (hs : s.WF) (k : Nat) (v : V) : (s.set k v).cap = s.cap := by
  by_cases hm : k ∈ s.keys
  · obtain ⟨I, hI, rfl⟩ := mem_keys.1 hm
    rw [set_mem hs hI]; rfl
  · rw [set_not_mem hm]; simp [cap]

/-- `remove` of a present key: the last entry moves into its slot. -/
theorem remove_mem {s : SparseMap V} (hs : s.WF) {i : Nat} (hi : i < s.dense.size) :
    s.remove s.dense[i].key =
      ⟨(s.dense.setIfInBounds i s.dense[s.dense.size - 1]).pop,
        s.sparse.setIfInBounds s.dense[s.dense.size - 1].key i⟩ := by
  unfold remove
  rw [sparse_dense hs hi]
  simp [hi, getElem?_pos s.dense (s.dense.size - 1) (by omega)]

theorem remove_not_mem {s : SparseMap V} {k : Nat} (h : k ∉ s.keys) : s.remove k = s := by
  unfold remove
  dsimp only
  split
  · next e he => simp [key_ne_of_not_mem h he]
  · rfl

theorem cap_remove {s : SparseMap V} (hs : s.WF) (k : Nat) : (s.remove k).cap = s.cap := by
  by_cases h : k ∈ s.keys
  · obtain ⟨i, hi, rfl⟩ := mem_keys.1 h
    rw [remove_mem hs hi]
    simp [cap]
  · rw [remove_not_mem h]

theorem wf_remove {s : SparseMap V} (hs : s.WF) (k : Nat) : (s.remove k).WF := by
  by_cases h : k ∈ s.keys
  · obtain ⟨I, hI, rfl⟩ := mem_keys.1 h
    rw [remove_mem hs hI]
    intro j hj
    simp only [Array.size_pop, Array.size_setIfInBounds] at hj
    simp only [Array.getElem_pop]
    rw [Array.getElem_setIfInBounds (by omega)]
    split
    · next hjI =>
      subst hjI
      have := hs (s.dense.size - 1) (by omega)
      exact Array.getElem?_setIfInBounds_self_of_lt (by grind)
    · next hjI =>
      have hne : s.dense[s.dense.size - 1].key ≠ s.dense[j].key := fun he =>
        absurd (nodup hs (by omega) (by omega) he) (by omega)
      rw [Array.getElem?_setIfInBounds_ne hne]
      exact hs j (by omega)
  · rw [remove_not_mem h]; exact hs

theorem wf_clear (s : SparseMap V) : s.clear.WF := by
  intro i h; simp [clear] at h

theorem cap_clear (s : SparseMap V) : s.clear.cap = s.cap := rfl

end SparseMap

end GoFV.Util
