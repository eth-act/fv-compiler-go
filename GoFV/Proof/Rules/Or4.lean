import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values08

/-!
# Rule lemmas: `Or` rules (part 4)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Or` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:213`: `(Or32 x (And32 x y)) => x` -/
theorem r_generic_213_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_213_2 := by rule_auto


/-- `generic.rules:632`: `(Or32 x x) => x` -/
theorem r_generic_632_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_632_2 := by rule_auto


/-- `generic.rules:633`: `(Or32 (Const32 [0]) x) => x` -/
theorem r_generic_633_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_633_2 := by rule_auto


/-- `generic.rules:634`: `(Or32 (Const32 [-1]) _) => (Const32 [-1])` -/
theorem r_generic_634_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_634_2 := by rule_auto


/-- `generic.rules:635`: `(Or32 (Com32 x) x) => (Const32 [-1])` -/
theorem r_generic_635_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_635_2 := by rule_auto


/-- `generic.rules:688`: `(Or32 x (Or32 x y)) => (Or32 x y)` -/
theorem r_generic_688_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_688_2 := by rule_auto


/-- `generic.rules:1259`: `(Or32 (Or32 i:(Const32 <t>) z) x) && (z.Op != OpConst32 && x.Op != OpConst32) => (Or32 i (Or32 <t> z x))` -/
theorem r_generic_1259_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1259 := by rule_auto


/-- `generic.rules:2185`: `(Or32 left:(Lsh32x64 x y) right:(Rsh32Ux64 x (Sub64 (Const64 [32]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 32) => (RotateLeft32 x y)` -/
theorem r_generic_2185_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2185_2 := by rule_auto


/-- `generic.rules:2186`: `(Or32 left:(Lsh32x32 x y) right:(Rsh32Ux32 x (Sub32 (Const32 [32]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 32) => (RotateLeft32 x y)` -/
theorem r_generic_2186_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2186_2 := by rule_auto


/-- `generic.rules:2187`: `(Or32 left:(Lsh32x16 x y) right:(Rsh32Ux16 x (Sub16 (Const16 [32]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 32) => (RotateLeft32 x y)` -/
theorem r_generic_2187_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2187_2 := by rule_auto


/-- `generic.rules:2188`: `(Or32 left:(Lsh32x8 x y) right:(Rsh32Ux8 x (Sub8 (Const8 [32]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 32) => (RotateLeft32 x y)` -/
theorem r_generic_2188_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2188_2 := by rule_auto


/-- `generic.rules:2190`: `(Or32 right:(Rsh32Ux64 x y) left:(Lsh32x64 x z:(Sub64 (Const64 [32]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 32) => (RotateLeft32 x z)` -/
theorem r_generic_2190_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2190_2 := by rule_auto


/-- `generic.rules:2191`: `(Or32 right:(Rsh32Ux32 x y) left:(Lsh32x32 x z:(Sub32 (Const32 [32]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 32) => (RotateLeft32 x z)` -/
theorem r_generic_2191_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2191_2 := by rule_auto


/-- `generic.rules:2192`: `(Or32 right:(Rsh32Ux16 x y) left:(Lsh32x16 x z:(Sub16 (Const16 [32]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 32) => (RotateLeft32 x z)` -/
theorem r_generic_2192_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2192_2 := by rule_auto


/-- `generic.rules:2193`: `(Or32 right:(Rsh32Ux8 x y) left:(Lsh32x8 x z:(Sub8 (Const8 [32]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 32) => (RotateLeft32 x z)` -/
theorem r_generic_2193_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2193_2 := by rule_auto

end GoFV.Proof.Rules
