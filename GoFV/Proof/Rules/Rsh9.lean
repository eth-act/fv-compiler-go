import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values10
import GoFV.Rules.Generated.Generic.Values11

/-!
# Rule lemmas: `Rsh` rules (part 9)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Rsh` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:530`: `(Rsh64Ux64 i:(Lsh64x64 x (Const64 [c])) (Const64 [c])) && c >= 0 && c < 64 && i.Uses == 1 => (And64 x (Const64 <v.Type> [int64(^uint64(0)>>c)]))` -/
theorem r_generic_530_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_530 := by rule_auto

/-- `generic.rules:531`: `(Rsh32Ux64 i:(Lsh32x64 x (Const64 [c])) (Const64 [c])) && c >= 0 && c < 32 && i.Uses == 1 => (And32 x (Const32 <v.Type> [int32(^uint32(0)>>c)]))` -/
theorem r_generic_531_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_531 := by rule_auto

/-- `generic.rules:532`: `(Rsh16Ux64 i:(Lsh16x64 x (Const64 [c])) (Const64 [c])) && c >= 0 && c < 16 && i.Uses == 1 => (And16 x (Const16 <v.Type> [int16(^uint16(0)>>c)]))` -/
theorem r_generic_532_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_532 := by rule_auto

/-- `generic.rules:533`: `(Rsh8Ux64 i:(Lsh8x64 x (Const64 [c])) (Const64 [c])) && c >= 0 && c < 8 && i.Uses == 1 => (And8 x (Const8 <v.Type> [int8 (^uint8 (0)>>c)]))` -/
theorem r_generic_533_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_533 := by rule_auto

end GoFV.Proof.Rules
