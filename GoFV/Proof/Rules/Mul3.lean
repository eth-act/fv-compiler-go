import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values06
import GoFV.Rules.Generated.Generic.Values07

/-!
# Rule lemmas: `Mul` rules (part 3)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the P1/P2 rules whose top op is in the
`Mul` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:1108`: `(Mul16 <t> x (Const16 [c])) && isPowerOfTwo(uint16(c)) && v.Block.Func.pass.name != "opt" => (Lsh16x64 <t> x (Const64 <typ.UInt64> [log16u(uint16(c))]))` -/
theorem r_generic_1108_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1108 := by rule_auto

/-- `generic.rules:1116`: `(Mul16 <t> x (Const16 [c])) && isPowerOfTwo(uint16(-c)) && v.Block.Func.pass.name != "opt" => (Neg16 (Lsh16x64 <t> x (Const64 <typ.UInt64> [log16u(uint16(-c))])))` -/
theorem r_generic_1116_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1116 := by rule_auto

/-- `generic.rules:1110`: `(Mul32 <t> x (Const32 [c])) && isPowerOfTwo(uint32(c)) && v.Block.Func.pass.name != "opt" => (Lsh32x64 <t> x (Const64 <typ.UInt64> [log32u(uint32(c))]))` -/
theorem r_generic_1110_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1110 := by rule_auto

/-- `generic.rules:1118`: `(Mul32 <t> x (Const32 [c])) && isPowerOfTwo(uint32(-c)) && v.Block.Func.pass.name != "opt" => (Neg32 (Lsh32x64 <t> x (Const64 <typ.UInt64> [log32u(uint32(-c))])))` -/
theorem r_generic_1118_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1118 := by rule_auto

/-- `generic.rules:1112`: `(Mul64 <t> x (Const64 [c])) && isPowerOfTwo(uint64(c)) && v.Block.Func.pass.name != "opt" => (Lsh64x64 <t> x (Const64 <typ.UInt64> [log64u(uint64(c))]))` -/
theorem r_generic_1112_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1112 := by rule_auto

/-- `generic.rules:1120`: `(Mul64 <t> x (Const64 [c])) && isPowerOfTwo(uint64(-c)) && v.Block.Func.pass.name != "opt" => (Neg64 (Lsh64x64 <t> x (Const64 <typ.UInt64> [log64u(uint64(-c))])))` -/
theorem r_generic_1120_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1120 := by rule_auto

/-- `generic.rules:1106`: `(Mul8 <t> x (Const8 [c])) && isPowerOfTwo(uint8(c)) && v.Block.Func.pass.name != "opt" => (Lsh8x64 <t> x (Const64 <typ.UInt64> [log8u(uint8(c))]))` -/
theorem r_generic_1106_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1106 := by rule_auto

/-- `generic.rules:1114`: `(Mul8 <t> x (Const8 [c])) && isPowerOfTwo(uint8(-c)) && v.Block.Func.pass.name != "opt" => (Neg8 (Lsh8x64 <t> x (Const64 <typ.UInt64> [log8u(uint8(-c))])))` -/
theorem r_generic_1114_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1114 := by rule_auto

end GoFV.Proof.Rules
