import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values02

/-!
# Rule lemmas: constant composites (`ConstInterface`, `ConstSlice`)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the P2 rules that expand a constant composite into
its fields (`docs/proofs/rules.md`). The top value having its type's shape (`hty`) fixes the
type to two pointer fields (interface) or a pointer and two 64-bit integers (slice); the nil
`uintptr` of `:1057` becomes the nil pointer again under the field's pointer shape
(`Ptr.ofAddr 0 = Ptr.null`). The slice's pointer type is `v.Type.Elem().PtrTo()`, the slice
shape's data pointer (`methodE`).

False under the semantics (`docs/proofs/rules.md` "Findings"): `:1039` (`rule-sat`
counterexample; `config.PtrSize == 4`: 32-bit lengths in a 64-bit slice shape) and `:1053`
(`SliceMake (AddPtr x (And64 y (Slicemask _))) (Const64 [c]) _ && c > 0`: correct in Go only
because the `Slicemask` argument is the slice's capacity, which the pattern does not check; at
`Slicemask 0` the pointer is `x`, the result's `x + y`).
-/

-- FALSE r_generic_1039 #69
-- FALSE r_generic_1053 #69

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

/-- `generic.rules:1057`: `(ConstInterface) => (IMake (ConstNil <typ.Uintptr>) (ConstNil <typ.BytePtr>))` -/
theorem r_generic_1057_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1057 := by
  rule_unfold
  generalize e.ty [] = t at hty ⊢
  obtain ⟨fs, n, rfl, h⟩ := ty_of_hasTy_agg hty
  rcases fs with _ | ⟨⟨o0, t0⟩, _ | ⟨⟨o1, t1⟩, _ | _⟩⟩ <;>
    simp only [List.map, Val.hasTyList, Bool.and_eq_true, Bool.false_eq_true, and_false] at h
  obtain ⟨rfl, ⟨el1, rfl⟩⟩ := And.intro (ty_of_hasTy_int64 h.1) (ty_of_hasTy_null h.2.1)
  exact Refines.refl _

/-- `generic.rules:1044`: `(ConstSlice) && config.PtrSize == 8 => (SliceMake (ConstNil <v.Type.Elem().PtrTo()>) (Const64 <typ.Int> [0]) (Const64 <typ.Int> [0]))` -/
theorem r_generic_1044_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1044 := by
  rule_unfold
  generalize e.ty [] = t at hty ⊢
  obtain ⟨fs, n, rfl, h⟩ := ty_of_hasTy_agg hty
  rcases fs with _ | ⟨⟨o0, t0⟩, _ | ⟨⟨o1, t1⟩, _ | ⟨⟨o2, t2⟩, _ | _⟩⟩⟩ <;>
    simp only [List.map, Val.hasTyList, Bool.and_eq_true, Bool.false_eq_true, and_false] at h
  obtain ⟨⟨el0, rfl⟩, rfl, rfl⟩ := And.intro (ty_of_hasTy_null h.1)
    (And.intro (ty_of_hasTy_int64 h.2.1) (ty_of_hasTy_int64 h.2.2.1))
  exact Refines.refl _

end GoFV.Proof.Rules
