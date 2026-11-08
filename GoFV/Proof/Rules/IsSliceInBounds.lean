import GoFV.Proof.Rules.IsInBounds
import GoFV.Proof.Rules.NonVacuous
import GoFV.Rules.Generated.Generic.Values04

/-!
# Rule lemmas: `IsSliceInBounds` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the P1/P2 rules whose top op is in the
`IsSliceInBounds` family (`docs/proofs/rules.md`); the comparisons as in `IsInBounds.lean`
(`ule_ofInt64`, `inBounds_self`). The 32-bit forms (`:272`, `:274`, `:276`) are not proved
(see there). `:278` (`(IsSliceInBounds (SliceLen x) (SliceCap x))`) holds since `argShapeOk`
makes `x` a slice, so it is `poison` or has `0 ≤ len ≤ cap` (`Val.hasTy_slice`, #270).
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

section

variable [GoFV.SSA.Sem.Addrs]

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

/-- `generic.rules:278`: `(IsSliceInBounds (SliceLen x) (SliceCap x)) => (ConstBool [true])` -/
theorem r_generic_278_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_278 := by
  rule_unfold
  simp only [Nat.zero_add] at hat
  obtain ⟨⟨h0, el, hs⟩, h1, -⟩ := hat
  rw [hc, h0, h1] at hty ⊢
  rw [hs] at hlt
  rcases Val.hasTy_slice hlt.1 with hp | ⟨p, l, c, hv, hl, hcm, -, hlc⟩
  · rw [hp]; exact .poison _
  · rw [hv] at hty ⊢
    have hle : l.ule c = true := by
      rw [BitVec.toInt_eq_toNat_of_msb hl, BitVec.toInt_eq_toNat_of_msb hcm] at hlc
      simp only [BitVec.ule, decide_eq_true_eq]; omega
    simp [Comp.select, Val.retype, Cmp.inBounds, hcm, hle, Conv.constBool] at hty ⊢
    exact refines_retype_of_hasTy hty

end

open scoped GoFV.SSA.Sem.Fixed

theorem inst_r_generic_278 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_278
    (PEnv.ofLists [([0, 0], .agg [.int .w64 0, .int .w64 2, .int .w64 5]),
      ([0, 1], .agg [.int .w64 0, .int .w64 2, .int .w64 5])]
      [([], .bool), ([0, 0], .slice (some 8)), ([0, 1], .slice (some 8))] (.int .w64) [])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_278]
  rule_eval
  simp [Comp.select, Val.retype, Val.asInt]
  decide

end GoFV.Proof.Rules
