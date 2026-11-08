import GoFV.Proof.Rules.Dec
import GoFV.Proof.Rules.NonVacuous
import GoFV.Rules.Generated.Generic.Values01
import GoFV.Rules.Generated.Generic.Values12

/-!
# Rule lemmas: generic selections of a `Make`

`Rule.Sound` of the generic rules that select a component of a `Make`, as the dec rules in
`Dec.lean` (`dec_unfold` keeps the `Make`'s argument shapes `makeArgOk`; `sel_make2`,
`sel_make3`, `select_retype_make`): `(ArraySelect (ArrayMake1 x)) => x` (`:992`, the same rule
as `dec.rules:126`) and the constant lengths `(StringLen (StringMake _ (Const64 <t> [c])))`,
`(SliceLen (SliceMake _ (Const64 <t> [c]) _))`, `(SliceCap (SliceMake _ _ (Const64 <t> [c])))`
`=> (Const64 <t> [c])` (`:1012`, `:1031`, `:1032`): the selected argument is the result
(`Int64.ofInt c.toInt = c`). The 32-bit forms `:1033`/`:1034` are not proved.

The selections of selections `:1035–1038` (`(SliceLen (SliceMake _ (SliceLen x) _)) =>
(SliceLen x)`, …) retype the inner selection at the inner type and the result at the outer one.
`argShapeOk` makes the `Make` and `x` slices, so the inner selection is `int64` (a pointer for
`SlicePtr`) of `x`'s components, the outer selection is `poison` or that value
(`sel_make3`), and the top type gives the outer type a shape at which `retype` keeps it
(`refines_retype_len`, `refines_retype_ptr`).
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

/-- `generic.rules:992`: `(ArraySelect (ArrayMake1 x)) => x` -/
theorem r_generic_992_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_992 := by
  dec_unfold GoFV.Rules.Generated.Generic.r_generic_992
  unfold Comp.selectAux
  split
  · exact .poison _
  · have h := select_retype_make (e.ty [0]) (e.auxInt []).toInt.toNat [e.leaf [0, 0]] [e.ty [0, 0]]
      (fun i v t h1 h2 => by
        match i with
        | 0 => simp at h1 h2; subst h1 h2; exact ⟨hlt, hat⟩
        | _ + 1 => simp at h1) rfl
    generalize (e.auxInt []).toInt.toNat = k at h ⊢
    cases k with
    | zero => exact h
    | succ k =>
      have h' : Refines (Comp.select (k + 1) [Val.retype (e.ty [0]) (Comp.make [e.leaf [0, 0]])])
          .poison := by simpa using h
      rw [eq_poison_of_refines h']
      exact .poison _

/-- `generic.rules:1012`: `(StringLen (StringMake _ (Const64 <t> [c]))) => (Const64 <t> [c])` -/
theorem r_generic_1012_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1012 := by
  dec_unfold GoFV.Rules.Generated.Generic.r_generic_1012
  rw [Int64.ofInt_toInt]
  exact sel_make2 hlt (Val.retype_hasTy _ _) hat.1 hat.2 1

/-- `generic.rules:1031`: `(SliceLen (SliceMake _ (Const64 <t> [c]) _)) => (Const64 <t> [c])` -/
theorem r_generic_1031_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1031 := by
  dec_unfold GoFV.Rules.Generated.Generic.r_generic_1031
  rw [Int64.ofInt_toInt]
  exact sel_make3 hlt.1 (Val.retype_hasTy _ _) hlt.2 hat.2.1.2 hat.2.2.1.2 hat.2.2.2.2 1

/-- `generic.rules:1032`: `(SliceCap (SliceMake _ _ (Const64 <t> [c]))) => (Const64 <t> [c])` -/
theorem r_generic_1032_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1032 := by
  dec_unfold GoFV.Rules.Generated.Generic.r_generic_1032
  rw [Int64.ofInt_toInt]
  exact sel_make3 hlt.1 hlt.2 (Val.retype_hasTy _ _) hat.2.1.2 hat.2.2.1.2 hat.2.2.2.2 2

/-- Argument 1 or 2 of a `SliceMake` of a slice shape is an `int64`. -/
theorem int64_of_makeArgOk {el : Option Nat} {k : Nat} {t : Ty}
    (h : makeArgOk (.slice el) k t = true) (hk : k = 1 ∨ k = 2) : t = .int .w64 := by
  rcases hk with rfl | rfl <;>
    simp [makeArgOk, fieldShape?, Ty.asAgg, Ty.sliceAgg, shapeSub, isPtrTy] at h <;>
    exact Ty.eq_of_beq h

/-- Argument 0 of a `SliceMake` of a slice shape is a pointer. -/
theorem ptr_of_makeArgOk {el : Option Nat} {t : Ty} (h : makeArgOk (.slice el) 0 t = true) :
    isPtrTy t = true := by
  simp [makeArgOk, fieldShape?, Ty.asAgg, Ty.sliceAgg, shapeSub, isPtrTy] at h
  rcases h with h | h
  · rw [Ty.eq_of_beq h]; rfl
  · exact h

/-- A length or capacity (component 1 or 2) of a value of a slice shape: `poison` or an
`int64`. -/
theorem select_slice_len {x : Val} {el : Option Nat} (h : x.hasTy (.slice el) = true) (k : Nat)
    (hk : k = 1 ∨ k = 2) :
    Comp.select k [x] = .poison ∨ ∃ n : BitVec Width.w64.bits, Comp.select k [x] = .int .w64 n := by
  rcases Val.hasTy_slice h with rfl | ⟨p, l, c, rfl, -⟩
  · exact .inl rfl
  · rcases hk with rfl | rfl
    · exact .inr ⟨l, rfl⟩
    · exact .inr ⟨c, rfl⟩

/-- The data pointer (component 0) of a value of a slice shape: a pointer word (a pointer, a
64-bit integer, or `poison`). -/
theorem select_slice_ptr {x : Val} {el : Option Nat} (h : x.hasTy (.slice el) = true) :
    (Comp.select 0 [x]).isPtrWord = true := by
  cases x with
  | poison => rfl
  | agg vs =>
    obtain ⟨p, l, c, rfl, hp, -⟩ := Val.hasTy_agg_slice.1 h
    exact hp
  | _ => simp [Val.hasTy] at h

/-- A value `L` of shape `T` refining an `int64` (or `poison`) `s` at `int64` refines `s` at `T`. -/
theorem refines_retype_len {L s : Val} {T : Ty}
    (hs : s = .poison ∨ ∃ n : BitVec Width.w64.bits, s = .int .w64 n)
    (h : Refines L (s.retype (.int .w64))) (hty : L.hasTy T = true) : Refines L (s.retype T) := by
  rcases hs with rfl | ⟨n, rfl⟩
  · rw [eq_poison_of_refines h]; exact .poison _
  · have h' : Refines L (.int .w64 n) := by simpa [Val.retype] using h
    cases h' with
    | poison => exact .poison _
    | int => exact refines_retype_of_hasTy hty

/-- A value `L` of shape `T` refining a pointer word `s` at a pointer shape refines `s` at `T`. -/
theorem refines_retype_ptr {L s : Val} {T : Ty} {e : Option Nat} (hs : s.isPtrWord = true)
    (h : Refines L (s.retype (.ptr e))) (hty : L.hasTy T = true) : Refines L (s.retype T) := by
  cases s with
  | poison => rw [eq_poison_of_refines h]; exact .poison _
  | ptr P =>
    have hc : P.held = true := by simpa [Val.isPtrWord] using hs
    have h' : Refines L (.ptr P) := by
      simpa [Val.retype, Ptr.word_of_held hc] using h
    cases h' with
    | poison => exact .poison _
    | ptr => exact refines_retype_of_hasTy hty
  | int w x =>
    cases w <;> simp only [Val.isPtrWord, Bool.false_eq_true] at hs
    have h' : Refines L (.int .w64 x) := by simpa [Val.retype] using h
    cases h' with
    | poison => exact .poison _
    | int => exact refines_retype_of_hasTy hty
  | _ => simp [Val.isPtrWord] at hs

/-- `generic.rules:1035`: `(SlicePtr (SliceMake (SlicePtr x) _ _)) => (SlicePtr x)` -/
theorem r_generic_1035_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1035 := by
  dec_unfold GoFV.Rules.Generated.Generic.r_generic_1035
  obtain ⟨hT, ⟨⟨-, h0⟩, hx⟩, ⟨-, h1⟩, -, h2⟩ := hat
  obtain ⟨el, hT⟩ := isSliceTy_iff.1 hT
  obtain ⟨el', hx⟩ := isSliceTy_iff.1 hx
  rw [hT] at h0 h1 h2 hty ⊢
  have hk := sel_make3 (Val.retype_hasTy _ (Comp.select 0 [e.leaf [0, 0, 0]])) hlt.2.1 hlt.2.2
    h0 h1 h2 0
  obtain ⟨ep, hp⟩ := isPtrTy_iff.1 (ptr_of_makeArgOk h0)
  rw [hp] at hk hty ⊢
  rw [hx] at hlt
  exact refines_retype_ptr (select_slice_ptr hlt.1) hk hty

/-- `generic.rules:1036`: `(SliceLen (SliceMake _ (SliceLen x) _)) => (SliceLen x)` -/
theorem r_generic_1036_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1036 := by
  dec_unfold GoFV.Rules.Generated.Generic.r_generic_1036
  obtain ⟨hT, ⟨-, h0⟩, ⟨⟨-, h1⟩, hx⟩, -, h2⟩ := hat
  obtain ⟨el, hT⟩ := isSliceTy_iff.1 hT
  obtain ⟨el', hx⟩ := isSliceTy_iff.1 hx
  rw [hT] at h0 h1 h2 hty ⊢
  have hk := sel_make3 hlt.1 (Val.retype_hasTy _ (Comp.select 1 [e.leaf [0, 1, 0]])) hlt.2.2
    h0 h1 h2 1
  rw [int64_of_makeArgOk h1 (.inl rfl)] at hk hty ⊢
  rw [hx] at hlt
  exact refines_retype_len (select_slice_len hlt.2.1 1 (.inl rfl)) hk hty

/-- `generic.rules:1037`: `(SliceCap (SliceMake _ _ (SliceCap x))) => (SliceCap x)` -/
theorem r_generic_1037_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1037 := by
  dec_unfold GoFV.Rules.Generated.Generic.r_generic_1037
  obtain ⟨hT, ⟨-, h0⟩, ⟨-, h1⟩, ⟨-, h2⟩, hx⟩ := hat
  obtain ⟨el, hT⟩ := isSliceTy_iff.1 hT
  obtain ⟨el', hx⟩ := isSliceTy_iff.1 hx
  rw [hT] at h0 h1 h2 hty ⊢
  have hk := sel_make3 hlt.1 hlt.2.1 (Val.retype_hasTy _ (Comp.select 2 [e.leaf [0, 2, 0]]))
    h0 h1 h2 2
  rw [int64_of_makeArgOk h2 (.inr rfl)] at hk hty ⊢
  rw [hx] at hlt
  exact refines_retype_len (select_slice_len hlt.2.2 2 (.inr rfl)) hk hty

/-- `generic.rules:1038`: `(SliceCap (SliceMake _ _ (SliceLen x))) => (SliceLen x)` -/
theorem r_generic_1038_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1038 := by
  dec_unfold GoFV.Rules.Generated.Generic.r_generic_1038
  obtain ⟨hT, ⟨-, h0⟩, ⟨-, h1⟩, ⟨-, h2⟩, hx⟩ := hat
  obtain ⟨el, hT⟩ := isSliceTy_iff.1 hT
  obtain ⟨el', hx⟩ := isSliceTy_iff.1 hx
  rw [hT] at h0 h1 h2 hty ⊢
  have hk := sel_make3 hlt.1 hlt.2.1 (Val.retype_hasTy _ (Comp.select 1 [e.leaf [0, 2, 0]]))
    h0 h1 h2 2
  rw [int64_of_makeArgOk h2 (.inr rfl)] at hk hty ⊢
  rw [hx] at hlt
  exact refines_retype_len (select_slice_len hlt.2.2 1 (.inl rfl)) hk hty

/-! ## Non-vacuity -/

/-- A slice with `len 2 ≤ cap 5`. -/
private def slice25 : Val := .agg [.int .w64 0, .int .w64 2, .int .w64 5]

theorem inst_r_generic_1035 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_1035
    (PEnv.ofLists [([0, 0, 0], slice25), ([1, 0], .int .w64 2), ([2, 0], .int .w64 5)]
      [([], .ptr (some 8)), ([0], .slice (some 8)), ([0, 0], .ptr (some 8)),
        ([0, 0, 0], .slice (some 8))] (.int .w64) [])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_1035]
  rule_eval
  simp +decide [slice25, Comp.select, Comp.make, Val.retype, Val.ofSlice, Val.retypePtr,
    Val.retypeI64]

theorem inst_r_generic_1036 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_1036
    (PEnv.ofLists [([0, 0], .int .w64 0), ([0, 1, 0], slice25), ([2, 0], .int .w64 7)]
      [([0], .slice (some 8)), ([0, 0], .ptr (some 8)), ([0, 1, 0], .slice (some 8))] (.int .w64) [])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_1036]
  rule_eval
  simp +decide [slice25, Comp.select, Comp.make, Val.retype, Val.ofSlice, Val.retypePtr,
    Val.retypeI64]

theorem inst_r_generic_1037 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_1037
    (PEnv.ofLists [([0, 0], .int .w64 0), ([1, 0], .int .w64 2), ([0, 2, 0], slice25)]
      [([0], .slice (some 8)), ([0, 0], .ptr (some 8)), ([0, 2, 0], .slice (some 8))] (.int .w64) [])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_1037]
  rule_eval
  simp +decide [slice25, Comp.select, Comp.make, Val.retype, Val.ofSlice, Val.retypePtr,
    Val.retypeI64]

theorem inst_r_generic_1038 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_1038
    (PEnv.ofLists [([0, 0], .int .w64 0), ([1, 0], .int .w64 1), ([0, 2, 0], slice25)]
      [([0], .slice (some 8)), ([0, 0], .ptr (some 8)), ([0, 2, 0], .slice (some 8))] (.int .w64) [])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_1038]
  rule_eval
  simp +decide [slice25, Comp.select, Comp.make, Val.retype, Val.ofSlice, Val.retypePtr,
    Val.retypeI64]

end GoFV.Proof.Rules
