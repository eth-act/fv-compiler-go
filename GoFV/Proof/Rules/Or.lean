import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values08

/-!
# Rule lemmas: `Or` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Or` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:213`: `(Or16 x (And16 x y)) => x` -/
theorem r_generic_213_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_213 := by rule_auto


/-- `generic.rules:632`: `(Or16 x x) => x` -/
theorem r_generic_632_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_632 := by rule_auto


/-- `generic.rules:633`: `(Or16 (Const16 [0]) x) => x` -/
theorem r_generic_633_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_633 := by rule_auto


/-- `generic.rules:634`: `(Or16 (Const16 [-1]) _) => (Const16 [-1])` -/
theorem r_generic_634_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_634 := by rule_auto


/-- `generic.rules:635`: `(Or16 (Com16 x) x) => (Const16 [-1])` -/
theorem r_generic_635_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_635 := by rule_auto


/-- `generic.rules:688`: `(Or16 x (Or16 x y)) => (Or16 x y)` -/
theorem r_generic_688_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_688 := by rule_auto


/-- `generic.rules:1260`: `(Or16 (Or16 i:(Const16 <t>) z) x) && (z.Op != OpConst16 && x.Op != OpConst16) => (Or16 i (Or16 <t> z x))` -/
theorem r_generic_1260_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1260 := by rule_auto


/-- `generic.rules:2195`: `(Or16 left:(Lsh16x64 x y) right:(Rsh16Ux64 x (Sub64 (Const64 [16]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 16) => (RotateLeft16 x y)` -/
theorem r_generic_2195_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2195_2 := by rule_auto


/-- `generic.rules:2196`: `(Or16 left:(Lsh16x32 x y) right:(Rsh16Ux32 x (Sub32 (Const32 [16]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 16) => (RotateLeft16 x y)` -/
theorem r_generic_2196_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2196_2 := by rule_auto


/-- `generic.rules:2197`: `(Or16 left:(Lsh16x16 x y) right:(Rsh16Ux16 x (Sub16 (Const16 [16]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 16) => (RotateLeft16 x y)` -/
theorem r_generic_2197_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2197_2 := by rule_auto


/-- `generic.rules:2198`: `(Or16 left:(Lsh16x8 x y) right:(Rsh16Ux8 x (Sub8 (Const8 [16]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 16) => (RotateLeft16 x y)` -/
theorem r_generic_2198_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2198_2 := by rule_auto


/-- `generic.rules:2200`: `(Or16 right:(Rsh16Ux64 x y) left:(Lsh16x64 x z:(Sub64 (Const64 [16]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 16) => (RotateLeft16 x z)` -/
theorem r_generic_2200_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2200_2 := by rule_auto


/-- `generic.rules:2201`: `(Or16 right:(Rsh16Ux32 x y) left:(Lsh16x32 x z:(Sub32 (Const32 [16]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 16) => (RotateLeft16 x z)` -/
theorem r_generic_2201_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2201_2 := by rule_auto


/-- `generic.rules:2202`: `(Or16 right:(Rsh16Ux16 x y) left:(Lsh16x16 x z:(Sub16 (Const16 [16]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 16) => (RotateLeft16 x z)` -/
theorem r_generic_2202_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2202_2 := by rule_auto


/-- `generic.rules:2203`: `(Or16 right:(Rsh16Ux8 x y) left:(Lsh16x8 x z:(Sub8 (Const8 [16]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 16) => (RotateLeft16 x z)` -/
theorem r_generic_2203_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2203_2 := by rule_auto


end GoFV.Proof.Rules
