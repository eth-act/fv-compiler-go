import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values11

/-!
# Rule lemmas: `Rsh` rules (part 5)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Rsh` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:226`: `(Rsh64x64 (Const64 [c]) (Const64 [d])) => (Const64 [c >> uint64(d)])` -/
theorem r_generic_226_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_226 := by rule_auto


/-- `generic.rules:508`: `(Rsh64x64 <t> (Rsh64x64 x (Const64 [c])) (Const64 [d])) && !uaddOvf(c,d) => (Rsh64x64 x (Const64 <t> [c+d]))` -/
theorem r_generic_508_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_508 := by rule_auto


/-- `generic.rules:1189`: `(Rsh64x64 [false] x con:(Const64 [c])) && 0 < c && c < 64 => (Rsh64x64 [true] x con)` -/
theorem r_generic_1189_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1189_3 := by rule_auto


/-- `generic.rules:436`: `(Rsh64x8 x (Const8 [c])) => (Rsh64x64 x (Const64 <types.Types[types.TUINT64]> [int64(uint8(c))]))` -/
theorem r_generic_436_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_436 := by rule_auto


/-- `generic.rules:1189`: `(Rsh64x8 [false] x con:(Const8 [c])) && 0 < c && c < 64 => (Rsh64x8 [true] x con)` -/
theorem r_generic_1189_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1189_4 := by rule_auto


/-- `generic.rules:468`: `(Rsh8Ux16 x (Const16 [c])) => (Rsh8Ux64 x (Const64 <types.Types[types.TUINT64]> [int64(uint16(c))]))` -/
theorem r_generic_468_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_468 := by rule_auto


/-- `generic.rules:1199`: `(Rsh8Ux16 [false] x con:(Const16 [c])) && 0 < c && c < 8 => (Rsh8Ux16 [true] x con)` -/
theorem r_generic_1199_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1199 := by rule_auto


/-- `generic.rules:467`: `(Rsh8Ux32 x (Const32 [c])) => (Rsh8Ux64 x (Const64 <types.Types[types.TUINT64]> [int64(uint32(c))]))` -/
theorem r_generic_467_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_467 := by rule_auto


/-- `generic.rules:1199`: `(Rsh8Ux32 [false] x con:(Const32 [c])) && 0 < c && c < 8 => (Rsh8Ux32 [true] x con)` -/
theorem r_generic_1199_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1199_2 := by rule_auto


/-- `generic.rules:236`: `(Rsh8Ux64 (Const8 [c]) (Const64 [d])) => (Const8 [int8(uint8(c) >> uint64(d))])` -/
theorem r_generic_236_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_236 := by rule_auto


/-- `generic.rules:500`: `(Rsh8Ux64 _ (Const64 [c])) && uint64(c) >= 8 => (Const8 [0])` -/
theorem r_generic_500_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_500_2 := by rule_auto


end GoFV.Proof.Rules
