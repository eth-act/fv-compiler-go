import GoFV.Proof.Rules.IsInBounds
import GoFV.Rules.Generated.Generic.Values04

/-!
# Rule lemmas: `IsSliceInBounds` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the P1/P2 rules whose top op is in the
`IsSliceInBounds` family (`docs/proofs/rules.md`); the comparisons as in `IsInBounds.lean`
(`ule_ofInt64`, `inBounds_self`). The 32-bit forms (`:272`, `:274`, `:276`) are not proved
(see there). `:278` (`(IsSliceInBounds (SliceLen x) (SliceCap x))`) needs `0 ≤ len ≤ cap` of
every slice value, which the semantics does not have yet (#10).
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

/-- `generic.rules:271`: `(IsSliceInBounds x x) => (ConstBool [true])` -/
theorem r_generic_271_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_271 := by
  rule_unfold
  rw [hc] at hty ⊢
  rcases inBounds_self true (e.leaf [0]) with h | h <;> rw [h] at hty ⊢
  · exact Refines.poison _
  · exact refines_retype_of_hasTy hty

/-- `generic.rules:273`: `(IsSliceInBounds (And64 (Const64 [c]) _) (Const64 [d])) && 0 <= c && c <= d => (ConstBool [true])` -/
theorem r_generic_273_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_273 := by rule_auto

/-- `generic.rules:275`: `(IsSliceInBounds (Const64 [0]) _) => (ConstBool [true])` -/
theorem r_generic_275_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_275 := by rule_auto

/-- `generic.rules:277`: `(IsSliceInBounds (Const64 [c]) (Const64 [d])) => (ConstBool [0 <= c && c <= d])` -/
theorem r_generic_277_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_277 := by
  bounds_auto

end GoFV.Proof.Rules
