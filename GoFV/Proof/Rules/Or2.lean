import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values09

/-!
# Rule lemmas: `Or` rules (part 2)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Or` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:213`: `(Or64 x (And64 x y)) => x` -/
theorem r_generic_213_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_213_3 := by rule_auto

/-- `generic.rules:632`: `(Or64 x x) => x` -/
theorem r_generic_632_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_632_3 := by rule_auto

/-- `generic.rules:633`: `(Or64 (Const64 [0]) x) => x` -/
theorem r_generic_633_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_633_3 := by rule_auto

/-- `generic.rules:634`: `(Or64 (Const64 [-1]) _) => (Const64 [-1])` -/
theorem r_generic_634_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_634_3 := by rule_auto

/-- `generic.rules:635`: `(Or64 (Com64 x) x) => (Const64 [-1])` -/
theorem r_generic_635_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_635_3 := by rule_auto

/-- `generic.rules:688`: `(Or64 x (Or64 x y)) => (Or64 x y)` -/
theorem r_generic_688_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_688_3 := by rule_auto

/-- `generic.rules:1258`: `(Or64 (Or64 i:(Const64 <t>) z) x) && (z.Op != OpConst64 && x.Op != OpConst64) => (Or64 i (Or64 <t> z x))` -/
theorem r_generic_1258_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1258 := by rule_auto

/-- `generic.rules:2175`: `(Or64 left:(Lsh64x64 x y) right:(Rsh64Ux64 x (Sub64 (Const64 [64]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 64) => (RotateLeft64 x y)` -/
theorem r_generic_2175_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2175_2 := by rule_auto

/-- `generic.rules:2176`: `(Or64 left:(Lsh64x32 x y) right:(Rsh64Ux32 x (Sub32 (Const32 [64]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 64) => (RotateLeft64 x y)` -/
theorem r_generic_2176_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2176_2 := by rule_auto

/-- `generic.rules:2177`: `(Or64 left:(Lsh64x16 x y) right:(Rsh64Ux16 x (Sub16 (Const16 [64]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 64) => (RotateLeft64 x y)` -/
theorem r_generic_2177_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2177_2 := by rule_auto

/-- `generic.rules:2178`: `(Or64 left:(Lsh64x8 x y) right:(Rsh64Ux8 x (Sub8 (Const8 [64]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 64) => (RotateLeft64 x y)` -/
theorem r_generic_2178_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2178_2 := by rule_auto

/-- `generic.rules:2180`: `(Or64 right:(Rsh64Ux64 x y) left:(Lsh64x64 x z:(Sub64 (Const64 [64]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 64) => (RotateLeft64 x z)` -/
theorem r_generic_2180_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2180_2 := by rule_auto

/-- `generic.rules:2181`: `(Or64 right:(Rsh64Ux32 x y) left:(Lsh64x32 x z:(Sub32 (Const32 [64]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 64) => (RotateLeft64 x z)` -/
theorem r_generic_2181_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2181_2 := by rule_auto

/-- `generic.rules:2182`: `(Or64 right:(Rsh64Ux16 x y) left:(Lsh64x16 x z:(Sub16 (Const16 [64]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 64) => (RotateLeft64 x z)` -/
theorem r_generic_2182_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2182_2 := by rule_auto

/-- `generic.rules:2183`: `(Or64 right:(Rsh64Ux8 x y) left:(Lsh64x8 x z:(Sub8 (Const8 [64]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 64) => (RotateLeft64 x z)` -/
theorem r_generic_2183_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2183_2 := by rule_auto

/-- `generic.rules:213`: `(Or8 x (And8 x y)) => x` -/
theorem r_generic_213_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_213_4 := by rule_auto

/-- `generic.rules:632`: `(Or8 x x) => x` -/
theorem r_generic_632_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_632_4 := by rule_auto

/-- `generic.rules:633`: `(Or8 (Const8 [0]) x) => x` -/
theorem r_generic_633_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_633_4 := by rule_auto

/-- `generic.rules:634`: `(Or8 (Const8 [-1]) _) => (Const8 [-1])` -/
theorem r_generic_634_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_634_4 := by rule_auto

/-- `generic.rules:635`: `(Or8 (Com8 x) x) => (Const8 [-1])` -/
theorem r_generic_635_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_635_4 := by rule_auto

/-- `generic.rules:688`: `(Or8 x (Or8 x y)) => (Or8 x y)` -/
theorem r_generic_688_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_688_4 := by rule_auto

/-- `generic.rules:1261`: `(Or8 (Or8 i:(Const8 <t>) z) x) && (z.Op != OpConst8 && x.Op != OpConst8) => (Or8 i (Or8 <t> z x))` -/
theorem r_generic_1261_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1261 := by rule_auto

/-- `generic.rules:2205`: `(Or8 left:(Lsh8x64 x y) right:(Rsh8Ux64 x (Sub64 (Const64 [8]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 8) => (RotateLeft8 x y)` -/
theorem r_generic_2205_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2205_2 := by rule_auto

/-- `generic.rules:2206`: `(Or8 left:(Lsh8x32 x y) right:(Rsh8Ux32 x (Sub32 (Const32 [8]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 8) => (RotateLeft8 x y)` -/
theorem r_generic_2206_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2206_2 := by rule_auto

/-- `generic.rules:2207`: `(Or8 left:(Lsh8x16 x y) right:(Rsh8Ux16 x (Sub16 (Const16 [8]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 8) => (RotateLeft8 x y)` -/
theorem r_generic_2207_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2207_2 := by rule_auto

/-- `generic.rules:2208`: `(Or8 left:(Lsh8x8 x y) right:(Rsh8Ux8 x (Sub8 (Const8 [8]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 8) => (RotateLeft8 x y)` -/
theorem r_generic_2208_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2208_2 := by rule_auto

/-- `generic.rules:2210`: `(Or8 right:(Rsh8Ux64 x y) left:(Lsh8x64 x z:(Sub64 (Const64 [8]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 8) => (RotateLeft8 x z)` -/
theorem r_generic_2210_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2210_2 := by rule_auto

/-- `generic.rules:2211`: `(Or8 right:(Rsh8Ux32 x y) left:(Lsh8x32 x z:(Sub32 (Const32 [8]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 8) => (RotateLeft8 x z)` -/
theorem r_generic_2211_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2211_2 := by rule_auto

/-- `generic.rules:2212`: `(Or8 right:(Rsh8Ux16 x y) left:(Lsh8x16 x z:(Sub16 (Const16 [8]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 8) => (RotateLeft8 x z)` -/
theorem r_generic_2212_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2212_2 := by rule_auto

/-- `generic.rules:2213`: `(Or8 right:(Rsh8Ux8 x y) left:(Lsh8x8 x z:(Sub8 (Const8 [8]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 8) => (RotateLeft8 x z)` -/
theorem r_generic_2213_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2213_2 := by rule_auto

end GoFV.Proof.Rules
