import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values00

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `Add` rules (part 7)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Add` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

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
