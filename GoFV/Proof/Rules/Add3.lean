import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values00

/-!
# Rule lemmas: `Add` rules (part 3)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Add` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:2177`: `(Add64 left:(Lsh64x16 x y) right:(Rsh64Ux16 x (Sub16 (Const16 [64]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 64) => (RotateLeft64 x y)` -/
theorem r_generic_2177_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2177 := by rule_auto

/-- `generic.rules:2178`: `(Add64 left:(Lsh64x8 x y) right:(Rsh64Ux8 x (Sub8 (Const8 [64]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 64) => (RotateLeft64 x y)` -/
theorem r_generic_2178_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2178 := by rule_auto

/-- `generic.rules:2180`: `(Add64 right:(Rsh64Ux64 x y) left:(Lsh64x64 x z:(Sub64 (Const64 [64]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 64) => (RotateLeft64 x z)` -/
theorem r_generic_2180_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2180 := by rule_auto

/-- `generic.rules:2181`: `(Add64 right:(Rsh64Ux32 x y) left:(Lsh64x32 x z:(Sub32 (Const32 [64]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 64) => (RotateLeft64 x z)` -/
theorem r_generic_2181_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2181 := by rule_auto

/-- `generic.rules:2182`: `(Add64 right:(Rsh64Ux16 x y) left:(Lsh64x16 x z:(Sub16 (Const16 [64]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 64) => (RotateLeft64 x z)` -/
theorem r_generic_2182_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2182 := by rule_auto

/-- `generic.rules:2183`: `(Add64 right:(Rsh64Ux8 x y) left:(Lsh64x8 x z:(Sub8 (Const8 [64]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 64) => (RotateLeft64 x z)` -/
theorem r_generic_2183_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2183 := by rule_auto

/-- `generic.rules:120`: `(Add8 (Const8 [c]) (Const8 [d])) => (Const8 [c+d])` -/
theorem r_generic_120_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_120 := by rule_auto

/-- `generic.rules:420`: `(Add8 <t> (Mul8 x y) (Mul8 x z)) => (Mul8 x (Add8 <t> y z))` -/
theorem r_generic_420_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_420_4 := by rule_auto

/-- `generic.rules:427`: `(Add8 x x) => (Lsh8x64 x (Const64 <types.Types[types.TUINT64]> [1]))` -/
theorem r_generic_427_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_427_4 := by rule_auto

/-- `generic.rules:646`: `(Add8 (Const8 [0]) x) => x` -/
theorem r_generic_646_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_646_4 := by rule_auto

/-- `generic.rules:655`: `(Add8 x (Neg8 y)) => (Sub8 x y)` -/
theorem r_generic_655_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_655_4 := by rule_auto

/-- `generic.rules:661`: `(Add8 (Com8 x) x) => (Const8 [-1])` -/
theorem r_generic_661_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_661_4 := by rule_auto

/-- `generic.rules:675`: `(Add8 (Sub8 x t) (Add8 t y)) => (Add8 x y)` -/
theorem r_generic_675_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_675_4 := by rule_auto

/-- `generic.rules:678`: `(Add8 (Const8 [1]) (Com8 x)) => (Neg8 x)` -/
theorem r_generic_678_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_678_4 := by rule_auto

/-- `generic.rules:778`: `(Add8 x (Sub8 y x)) => y` -/
theorem r_generic_778_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_778_4 := by rule_auto

/-- `generic.rules:779`: `(Add8 x (Add8 y (Sub8 z x))) => (Add8 y z)` -/
theorem r_generic_779_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_779_4 := by rule_auto

/-- `generic.rules:1219`: `(Add8 (Add8 i:(Const8 <t>) z) x) && (z.Op != OpConst8 && x.Op != OpConst8) => (Add8 i (Add8 <t> z x))` -/
theorem r_generic_1219_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1219 := by rule_auto

/-- `generic.rules:1225`: `(Add8 (Sub8 i:(Const8 <t>) z) x) && (z.Op != OpConst8 && x.Op != OpConst8) => (Add8 i (Sub8 <t> x z))` -/
theorem r_generic_1225_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1225 := by rule_auto

/-- `generic.rules:1279`: `(Add8 (Const8 <t> [c]) (Add8 (Const8 <t> [d]) x)) => (Add8 (Const8 <t> [c+d]) x)` -/
theorem r_generic_1279_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1279 := by rule_auto

/-- `generic.rules:1285`: `(Add8 (Const8 <t> [c]) (Sub8 (Const8 <t> [d]) x)) => (Sub8 (Const8 <t> [c+d]) x)` -/
theorem r_generic_1285_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1285 := by rule_auto

/-- `generic.rules:2205`: `(Add8 left:(Lsh8x64 x y) right:(Rsh8Ux64 x (Sub64 (Const64 [8]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 8) => (RotateLeft8 x y)` -/
theorem r_generic_2205_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2205 := by rule_auto

/-- `generic.rules:2206`: `(Add8 left:(Lsh8x32 x y) right:(Rsh8Ux32 x (Sub32 (Const32 [8]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 8) => (RotateLeft8 x y)` -/
theorem r_generic_2206_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2206 := by rule_auto

/-- `generic.rules:2207`: `(Add8 left:(Lsh8x16 x y) right:(Rsh8Ux16 x (Sub16 (Const16 [8]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 8) => (RotateLeft8 x y)` -/
theorem r_generic_2207_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2207 := by rule_auto

/-- `generic.rules:2208`: `(Add8 left:(Lsh8x8 x y) right:(Rsh8Ux8 x (Sub8 (Const8 [8]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 8) => (RotateLeft8 x y)` -/
theorem r_generic_2208_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2208 := by rule_auto

/-- `generic.rules:2210`: `(Add8 right:(Rsh8Ux64 x y) left:(Lsh8x64 x z:(Sub64 (Const64 [8]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 8) => (RotateLeft8 x z)` -/
theorem r_generic_2210_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2210 := by rule_auto

/-- `generic.rules:2212`: `(Add8 right:(Rsh8Ux16 x y) left:(Lsh8x16 x z:(Sub16 (Const16 [8]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 8) => (RotateLeft8 x z)` -/
theorem r_generic_2212_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2212 := by rule_auto

/-- `generic.rules:2213`: `(Add8 right:(Rsh8Ux8 x y) left:(Lsh8x8 x z:(Sub8 (Const8 [8]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 8) => (RotateLeft8 x z)` -/
theorem r_generic_2213_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2213 := by rule_auto

end GoFV.Proof.Rules
