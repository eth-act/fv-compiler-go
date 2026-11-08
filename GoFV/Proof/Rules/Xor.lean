import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values13
import GoFV.Rules.Generated.Generic.Values14

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `Xor` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Xor` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:642`: `(Xor16 x x) => (Const16 [0])` -/
theorem r_generic_642_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_642 := by rule_auto

/-- `generic.rules:643`: `(Xor16 (Const16 [0]) x) => x` -/
theorem r_generic_643_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_643 := by rule_auto

/-- `generic.rules:689`: `(Xor16 x (Xor16 x y)) => y` -/
theorem r_generic_689_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_689 := by rule_auto

/-- `generic.rules:1266`: `(Xor16 (Xor16 i:(Const16 <t>) z) x) && (z.Op != OpConst16 && x.Op != OpConst16) => (Xor16 i (Xor16 <t> z x))` -/
theorem r_generic_1266_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1266 := by rule_auto

/-- `generic.rules:2195`: `(Xor16 left:(Lsh16x64 x y) right:(Rsh16Ux64 x (Sub64 (Const64 [16]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 16) => (RotateLeft16 x y)` -/
theorem r_generic_2195_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2195_3 := by rule_auto

/-- `generic.rules:2196`: `(Xor16 left:(Lsh16x32 x y) right:(Rsh16Ux32 x (Sub32 (Const32 [16]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 16) => (RotateLeft16 x y)` -/
theorem r_generic_2196_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2196_3 := by rule_auto

/-- `generic.rules:2197`: `(Xor16 left:(Lsh16x16 x y) right:(Rsh16Ux16 x (Sub16 (Const16 [16]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 16) => (RotateLeft16 x y)` -/
theorem r_generic_2197_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2197_3 := by rule_auto

/-- `generic.rules:2198`: `(Xor16 left:(Lsh16x8 x y) right:(Rsh16Ux8 x (Sub8 (Const8 [16]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 16) => (RotateLeft16 x y)` -/
theorem r_generic_2198_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2198_3 := by rule_auto

/-- `generic.rules:2200`: `(Xor16 right:(Rsh16Ux64 x y) left:(Lsh16x64 x z:(Sub64 (Const64 [16]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 16) => (RotateLeft16 x z)` -/
theorem r_generic_2200_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2200_3 := by rule_auto

/-- `generic.rules:2201`: `(Xor16 right:(Rsh16Ux32 x y) left:(Lsh16x32 x z:(Sub32 (Const32 [16]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 16) => (RotateLeft16 x z)` -/
theorem r_generic_2201_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2201_3 := by rule_auto

/-- `generic.rules:2202`: `(Xor16 right:(Rsh16Ux16 x y) left:(Lsh16x16 x z:(Sub16 (Const16 [16]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 16) => (RotateLeft16 x z)` -/
theorem r_generic_2202_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2202_3 := by rule_auto

/-- `generic.rules:2203`: `(Xor16 right:(Rsh16Ux8 x y) left:(Lsh16x8 x z:(Sub8 (Const8 [16]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 16) => (RotateLeft16 x z)` -/
theorem r_generic_2203_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2203_3 := by rule_auto

end GoFV.Proof.Rules
