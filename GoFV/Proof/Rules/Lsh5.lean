import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values05
import GoFV.Rules.Generated.Generic.Values06

/-!
# Rule lemmas: `Lsh` rules (part 5)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Lsh` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:462`: `(Lsh8x16 x (Const16 [c])) => (Lsh8x64 x (Const64 <types.Types[types.TUINT64]> [int64(uint16(c))]))` -/
theorem r_generic_462_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_462 := by rule_auto


/-- `generic.rules:1197`: `(Lsh8x16 [false] x con:(Const16 [c])) && 0 < c && c < 8 => (Lsh8x16 [true] x con)` -/
theorem r_generic_1197_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1197 := by rule_auto


/-- `generic.rules:461`: `(Lsh8x32 x (Const32 [c])) => (Lsh8x64 x (Const64 <types.Types[types.TUINT64]> [int64(uint32(c))]))` -/
theorem r_generic_461_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_461 := by rule_auto


/-- `generic.rules:1197`: `(Lsh8x32 [false] x con:(Const32 [c])) && 0 < c && c < 8 => (Lsh8x32 [true] x con)` -/
theorem r_generic_1197_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1197_2 := by rule_auto


/-- `generic.rules:234`: `(Lsh8x64 (Const8 [c]) (Const64 [d])) => (Const8 [c << uint64(d)])` -/
theorem r_generic_234_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_234 := by rule_auto


/-- `generic.rules:500`: `(Lsh8x64 _ (Const64 [c])) && uint64(c) >= 8 => (Const8 [0])` -/
theorem r_generic_500_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_500 := by rule_auto


/-- `generic.rules:528`: `(Lsh8x64 i:(Rsh8x64 x (Const64 [c])) (Const64 [c])) && c >= 0 && c < 8 && i.Uses == 1 => (And8 x (Const8 <v.Type> [int8(-1) << c]))` -/
theorem r_generic_528_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_528 := by rule_auto


/-- `generic.rules:528`: `(Lsh8x64 i:(Rsh8Ux64 x (Const64 [c])) (Const64 [c])) && c >= 0 && c < 8 && i.Uses == 1 => (And8 x (Const8 <v.Type> [int8(-1) << c]))` -/
theorem r_generic_528_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_528_2 := by rule_auto


/-- `generic.rules:1197`: `(Lsh8x64 [false] x con:(Const64 [c])) && 0 < c && c < 8 => (Lsh8x64 [true] x con)` -/
theorem r_generic_1197_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1197_3 := by rule_auto


/-- `generic.rules:463`: `(Lsh8x8 x (Const8 [c])) => (Lsh8x64 x (Const64 <types.Types[types.TUINT64]> [int64(uint8(c))]))` -/
theorem r_generic_463_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_463 := by rule_auto


/-- `generic.rules:1197`: `(Lsh8x8 [false] x con:(Const8 [c])) && 0 < c && c < 8 => (Lsh8x8 [true] x con)` -/
theorem r_generic_1197_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1197_4 := by rule_auto

end GoFV.Proof.Rules
