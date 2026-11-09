import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values14

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `Xor` rules (part 2)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Xor` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:2177`: `(Xor64 left:(Lsh64x16 x y) right:(Rsh64Ux16 x (Sub16 (Const16 [64]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 64) => (RotateLeft64 x y)` -/
theorem r_generic_2177_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2177_3 := by rule_auto

/-- `generic.rules:2178`: `(Xor64 left:(Lsh64x8 x y) right:(Rsh64Ux8 x (Sub8 (Const8 [64]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 64) => (RotateLeft64 x y)` -/
theorem r_generic_2178_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2178_3 := by rule_auto

/-- `generic.rules:2180`: `(Xor64 right:(Rsh64Ux64 x y) left:(Lsh64x64 x z:(Sub64 (Const64 [64]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 64) => (RotateLeft64 x z)` -/
theorem r_generic_2180_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2180_3 := by rule_auto

/-- `generic.rules:2181`: `(Xor64 right:(Rsh64Ux32 x y) left:(Lsh64x32 x z:(Sub32 (Const32 [64]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 64) => (RotateLeft64 x z)` -/
theorem r_generic_2181_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2181_3 := by rule_auto

/-- `generic.rules:2182`: `(Xor64 right:(Rsh64Ux16 x y) left:(Lsh64x16 x z:(Sub16 (Const16 [64]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 64) => (RotateLeft64 x z)` -/
theorem r_generic_2182_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2182_3 := by rule_auto

/-- `generic.rules:2183`: `(Xor64 right:(Rsh64Ux8 x y) left:(Lsh64x8 x z:(Sub8 (Const8 [64]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 64) => (RotateLeft64 x z)` -/
theorem r_generic_2183_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2183_3 := by rule_auto

/-- `generic.rules:642`: `(Xor8 x x) => (Const8 [0])` -/
theorem r_generic_642_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_642_4 := by rule_auto

/-- `generic.rules:643`: `(Xor8 (Const8 [0]) x) => x` -/
theorem r_generic_643_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_643_4 := by rule_auto

/-- `generic.rules:689`: `(Xor8 x (Xor8 x y)) => y` -/
theorem r_generic_689_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_689_4 := by rule_auto

/-- `generic.rules:1267`: `(Xor8 (Xor8 i:(Const8 <t>) z) x) && (z.Op != OpConst8 && x.Op != OpConst8) => (Xor8 i (Xor8 <t> z x))` -/
theorem r_generic_1267_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1267 := by rule_auto

/-- `generic.rules:2205`: `(Xor8 left:(Lsh8x64 x y) right:(Rsh8Ux64 x (Sub64 (Const64 [8]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 8) => (RotateLeft8 x y)` -/
theorem r_generic_2205_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2205_3 := by rule_auto

/-- `generic.rules:2206`: `(Xor8 left:(Lsh8x32 x y) right:(Rsh8Ux32 x (Sub32 (Const32 [8]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 8) => (RotateLeft8 x y)` -/
theorem r_generic_2206_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2206_3 := by rule_auto

/-- `generic.rules:2207`: `(Xor8 left:(Lsh8x16 x y) right:(Rsh8Ux16 x (Sub16 (Const16 [8]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 8) => (RotateLeft8 x y)` -/
theorem r_generic_2207_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2207_3 := by rule_auto

/-- `generic.rules:2208`: `(Xor8 left:(Lsh8x8 x y) right:(Rsh8Ux8 x (Sub8 (Const8 [8]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 8) => (RotateLeft8 x y)` -/
theorem r_generic_2208_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2208_3 := by rule_auto

/-- `generic.rules:2210`: `(Xor8 right:(Rsh8Ux64 x y) left:(Lsh8x64 x z:(Sub64 (Const64 [8]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 8) => (RotateLeft8 x z)` -/
theorem r_generic_2210_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2210_3 := by rule_auto

/-- `generic.rules:2211`: `(Xor8 right:(Rsh8Ux32 x y) left:(Lsh8x32 x z:(Sub32 (Const32 [8]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 8) => (RotateLeft8 x z)` -/
theorem r_generic_2211_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2211_3 := by rule_auto

/-- `generic.rules:2212`: `(Xor8 right:(Rsh8Ux16 x y) left:(Lsh8x16 x z:(Sub16 (Const16 [8]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 8) => (RotateLeft8 x z)` -/
theorem r_generic_2212_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2212_3 := by rule_auto

/-- `generic.rules:2213`: `(Xor8 right:(Rsh8Ux8 x y) left:(Lsh8x8 x z:(Sub8 (Const8 [8]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 8) => (RotateLeft8 x z)` -/
theorem r_generic_2213_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2213_3 := by rule_auto

end GoFV.Proof.Rules
