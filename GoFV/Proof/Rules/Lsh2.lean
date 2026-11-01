import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values05

/-!
# Rule lemmas: `Lsh` rules (part 2)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Lsh` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:452`: `(Lsh16x16 x (Const16 [c])) => (Lsh16x64 x (Const64 <types.Types[types.TUINT64]> [int64(uint16(c))]))` -/
theorem r_generic_452_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_452 := by rule_auto


/-- `generic.rules:1194`: `(Lsh16x16 [false] x con:(Const16 [c])) && 0 < c && c < 16 => (Lsh16x16 [true] x con)` -/
theorem r_generic_1194_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1194 := by rule_auto


/-- `generic.rules:451`: `(Lsh16x32 x (Const32 [c])) => (Lsh16x64 x (Const64 <types.Types[types.TUINT64]> [int64(uint32(c))]))` -/
theorem r_generic_451_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_451 := by rule_auto


/-- `generic.rules:1194`: `(Lsh16x32 [false] x con:(Const32 [c])) && 0 < c && c < 16 => (Lsh16x32 [true] x con)` -/
theorem r_generic_1194_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1194_2 := by rule_auto


/-- `generic.rules:231`: `(Lsh16x64 (Const16 [c]) (Const64 [d])) => (Const16 [c << uint64(d)])` -/
theorem r_generic_231_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_231 := by rule_auto


/-- `generic.rules:499`: `(Lsh16x64 _ (Const64 [c])) && uint64(c) >= 16 => (Const16 [0])` -/
theorem r_generic_499_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_499 := by rule_auto


/-- `generic.rules:527`: `(Lsh16x64 i:(Rsh16x64 x (Const64 [c])) (Const64 [c])) && c >= 0 && c < 16 && i.Uses == 1 => (And16 x (Const16 <v.Type> [int16(-1) << c]))` -/
theorem r_generic_527_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_527 := by rule_auto


/-- `generic.rules:527`: `(Lsh16x64 i:(Rsh16Ux64 x (Const64 [c])) (Const64 [c])) && c >= 0 && c < 16 && i.Uses == 1 => (And16 x (Const16 <v.Type> [int16(-1) << c]))` -/
theorem r_generic_527_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_527_2 := by rule_auto


/-- `generic.rules:1194`: `(Lsh16x64 [false] x con:(Const64 [c])) && 0 < c && c < 16 => (Lsh16x64 [true] x con)` -/
theorem r_generic_1194_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1194_3 := by rule_auto


/-- `generic.rules:453`: `(Lsh16x8 x (Const8 [c])) => (Lsh16x64 x (Const64 <types.Types[types.TUINT64]> [int64(uint8(c))]))` -/
theorem r_generic_453_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_453 := by rule_auto


/-- `generic.rules:1194`: `(Lsh16x8 [false] x con:(Const8 [c])) && 0 < c && c < 16 => (Lsh16x8 [true] x con)` -/
theorem r_generic_1194_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1194_4 := by rule_auto


/-- `generic.rules:442`: `(Lsh32x16 x (Const16 [c])) => (Lsh32x64 x (Const64 <types.Types[types.TUINT64]> [int64(uint16(c))]))` -/
theorem r_generic_442_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_442 := by rule_auto


end GoFV.Proof.Rules
