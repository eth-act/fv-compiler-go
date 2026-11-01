import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values05
import GoFV.Rules.Generated.Generic.Values06

/-!
# Rule lemmas: `Lsh` rules (part 3)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Lsh` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:431`: `(Lsh64x32 x (Const32 [c])) => (Lsh64x64 x (Const64 <types.Types[types.TUINT64]> [int64(uint32(c))]))` -/
theorem r_generic_431_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_431 := by rule_auto


/-- `generic.rules:225`: `(Lsh64x64 (Const64 [c]) (Const64 [d])) => (Const64 [c << uint64(d)])` -/
theorem r_generic_225_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_225 := by rule_auto


/-- `generic.rules:497`: `(Lsh64x64 _ (Const64 [c])) && uint64(c) >= 64 => (Const64 [0])` -/
theorem r_generic_497_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_497 := by rule_auto


/-- `generic.rules:503`: `(Lsh64x64 <t> (Lsh64x64 x (Const64 [c])) (Const64 [d])) && !uaddOvf(c,d) => (Lsh64x64 x (Const64 <t> [c+d]))` -/
theorem r_generic_503_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_503 := by rule_auto


/-- `generic.rules:525`: `(Lsh64x64 i:(Rsh64x64 x (Const64 [c])) (Const64 [c])) && c >= 0 && c < 64 && i.Uses == 1 => (And64 x (Const64 <v.Type> [int64(-1) << c]))` -/
theorem r_generic_525_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_525 := by rule_auto


/-- `generic.rules:525`: `(Lsh64x64 i:(Rsh64Ux64 x (Const64 [c])) (Const64 [c])) && c >= 0 && c < 64 && i.Uses == 1 => (And64 x (Const64 <v.Type> [int64(-1) << c]))` -/
theorem r_generic_525_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_525_2 := by rule_auto


/-- `generic.rules:433`: `(Lsh64x8 x (Const8 [c])) => (Lsh64x64 x (Const64 <types.Types[types.TUINT64]> [int64(uint8(c))]))` -/
theorem r_generic_433_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_433 := by rule_auto


end GoFV.Proof.Rules
