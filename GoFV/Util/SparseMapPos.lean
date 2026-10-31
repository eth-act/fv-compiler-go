import GoFV.Util.SparseMap

/-
Port of `cmd/compile/internal/ssa/sparsemappos.go` (go1.27.3): a sparse map from `ID` to an
`int32` value and a position. Go's `sparseMapPos` is `sparsemap.go` with the entry extended by
`pos` and `get` returning `-1` for a missing key; its operations do exactly what
`genericSparseMap[ID, (int32, XPos)]`'s do, so it is `SparseMap (Int × P)` here and shares its
lemmas. `P` is the position type (`src.XPos`).
-/

namespace GoFV.Util

/-- `sparseMapPos`: entries carry `(val, pos)`. -/
abbrev SparseMapPos (P : Type u) := SparseMap (Int × P)

namespace SparseMapPos

variable {P : Type u}

/-- `newSparseMapPos(n)`. -/
def new (n : Nat) : SparseMapPos P := SparseMap.new n

/-- `get(k)`: the value, `-1` if `k` is absent. -/
def get (s : SparseMapPos P) (k : Nat) : Int :=
  match SparseMap.get s k with
  | some (v, _) => v
  | none => -1

/-- `set(k, v, a)`: sets both the value and the position. -/
def set (s : SparseMapPos P) (k : Nat) (v : Int) (a : P) : SparseMapPos P :=
  SparseMap.set s k (v, a)

theorem get_mem {s : SparseMapPos P} (hs : s.WF) {i : Nat} (hi : i < s.dense.size) :
    get s s.dense[i].key = s.dense[i].val.1 := by
  simp [get, SparseMap.get_mem hs hi]

theorem get_not_mem {s : SparseMapPos P} {k : Nat} (h : k ∉ s.keys) : get s k = -1 := by
  simp [get, SparseMap.get_not_mem h]

theorem wf_set {s : SparseMapPos P} (hs : s.WF) {k : Nat} (hk : k < s.cap) (v : Int) (a : P) :
    (set s k v a).WF :=
  SparseMap.wf_set hs hk _

end SparseMapPos

end GoFV.Util
