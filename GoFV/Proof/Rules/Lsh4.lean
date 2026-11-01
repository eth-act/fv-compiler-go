import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values05

/-!
# Rule lemmas: `Lsh` rules (part 4)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Lsh` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:1191`: `(Lsh32x16 [false] x con:(Const16 [c])) && 0 < c && c < 32 => (Lsh32x16 [true] x con)` -/
theorem r_generic_1191_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1191 := by rule_auto


/-- `generic.rules:441`: `(Lsh32x32 x (Const32 [c])) => (Lsh32x64 x (Const64 <types.Types[types.TUINT64]> [int64(uint32(c))]))` -/
theorem r_generic_441_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_441 := by rule_auto


/-- `generic.rules:1191`: `(Lsh32x32 [false] x con:(Const32 [c])) && 0 < c && c < 32 => (Lsh32x32 [true] x con)` -/
theorem r_generic_1191_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1191_2 := by rule_auto


/-- `generic.rules:228`: `(Lsh32x64 (Const32 [c]) (Const64 [d])) => (Const32 [c << uint64(d)])` -/
theorem r_generic_228_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_228 := by rule_auto


/-- `generic.rules:498`: `(Lsh32x64 _ (Const64 [c])) && uint64(c) >= 32 => (Const32 [0])` -/
theorem r_generic_498_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_498 := by rule_auto


/-- `generic.rules:526`: `(Lsh32x64 i:(Rsh32x64 x (Const64 [c])) (Const64 [c])) && c >= 0 && c < 32 && i.Uses == 1 => (And32 x (Const32 <v.Type> [int32(-1) << c]))` -/
theorem r_generic_526_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_526 := by rule_auto


/-- `generic.rules:526`: `(Lsh32x64 i:(Rsh32Ux64 x (Const64 [c])) (Const64 [c])) && c >= 0 && c < 32 && i.Uses == 1 => (And32 x (Const32 <v.Type> [int32(-1) << c]))` -/
theorem r_generic_526_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_526_2 := by rule_auto


/-- `generic.rules:1191`: `(Lsh32x64 [false] x con:(Const64 [c])) && 0 < c && c < 32 => (Lsh32x64 [true] x con)` -/
theorem r_generic_1191_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1191_3 := by rule_auto


/-- `generic.rules:443`: `(Lsh32x8 x (Const8 [c])) => (Lsh32x64 x (Const64 <types.Types[types.TUINT64]> [int64(uint8(c))]))` -/
theorem r_generic_443_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_443 := by rule_auto


/-- `generic.rules:1191`: `(Lsh32x8 [false] x con:(Const8 [c])) && 0 < c && c < 32 => (Lsh32x8 [true] x con)` -/
theorem r_generic_1191_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1191_4 := by rule_auto


/-- `generic.rules:432`: `(Lsh64x16 x (Const16 [c])) => (Lsh64x64 x (Const64 <types.Types[types.TUINT64]> [int64(uint16(c))]))` -/
theorem r_generic_432_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_432 := by rule_auto

end GoFV.Proof.Rules
