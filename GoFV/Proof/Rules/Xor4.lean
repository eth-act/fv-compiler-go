import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values13
import GoFV.Rules.Generated.Generic.Values14

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `Xor` rules (part 4)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Xor` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:642`: `(Xor32 x x) => (Const32 [0])` -/
theorem r_generic_642_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_642_2 := by rule_auto

/-- `generic.rules:643`: `(Xor32 (Const32 [0]) x) => x` -/
theorem r_generic_643_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_643_2 := by rule_auto

/-- `generic.rules:689`: `(Xor32 x (Xor32 x y)) => y` -/
theorem r_generic_689_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_689_2 := by rule_auto

/-- `generic.rules:1265`: `(Xor32 (Xor32 i:(Const32 <t>) z) x) && (z.Op != OpConst32 && x.Op != OpConst32) => (Xor32 i (Xor32 <t> z x))` -/
theorem r_generic_1265_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1265 := by rule_auto

/-- `generic.rules:2185`: `(Xor32 left:(Lsh32x64 x y) right:(Rsh32Ux64 x (Sub64 (Const64 [32]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 32) => (RotateLeft32 x y)` -/
theorem r_generic_2185_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2185_3 := by rule_auto

/-- `generic.rules:2186`: `(Xor32 left:(Lsh32x32 x y) right:(Rsh32Ux32 x (Sub32 (Const32 [32]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 32) => (RotateLeft32 x y)` -/
theorem r_generic_2186_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2186_3 := by rule_auto

/-- `generic.rules:2187`: `(Xor32 left:(Lsh32x16 x y) right:(Rsh32Ux16 x (Sub16 (Const16 [32]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 32) => (RotateLeft32 x y)` -/
theorem r_generic_2187_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2187_3 := by rule_auto

/-- `generic.rules:2188`: `(Xor32 left:(Lsh32x8 x y) right:(Rsh32Ux8 x (Sub8 (Const8 [32]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 32) => (RotateLeft32 x y)` -/
theorem r_generic_2188_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2188_3 := by rule_auto

/-- `generic.rules:2190`: `(Xor32 right:(Rsh32Ux64 x y) left:(Lsh32x64 x z:(Sub64 (Const64 [32]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 32) => (RotateLeft32 x z)` -/
theorem r_generic_2190_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2190_3 := by rule_auto

/-- `generic.rules:2191`: `(Xor32 right:(Rsh32Ux32 x y) left:(Lsh32x32 x z:(Sub32 (Const32 [32]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 32) => (RotateLeft32 x z)` -/
theorem r_generic_2191_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2191_3 := by rule_auto

/-- `generic.rules:2192`: `(Xor32 right:(Rsh32Ux16 x y) left:(Lsh32x16 x z:(Sub16 (Const16 [32]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 32) => (RotateLeft32 x z)` -/
theorem r_generic_2192_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2192_3 := by rule_auto

/-- `generic.rules:2193`: `(Xor32 right:(Rsh32Ux8 x y) left:(Lsh32x8 x z:(Sub8 (Const8 [32]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 32) => (RotateLeft32 x z)` -/
theorem r_generic_2193_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2193_3 := by rule_auto

/-- `generic.rules:642`: `(Xor64 x x) => (Const64 [0])` -/
theorem r_generic_642_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_642_3 := by rule_auto

/-- `generic.rules:643`: `(Xor64 (Const64 [0]) x) => x` -/
theorem r_generic_643_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_643_3 := by rule_auto

/-- `generic.rules:689`: `(Xor64 x (Xor64 x y)) => y` -/
theorem r_generic_689_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_689_3 := by rule_auto

/-- `generic.rules:1264`: `(Xor64 (Xor64 i:(Const64 <t>) z) x) && (z.Op != OpConst64 && x.Op != OpConst64) => (Xor64 i (Xor64 <t> z x))` -/
theorem r_generic_1264_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1264 := by rule_auto

/-- `generic.rules:2175`: `(Xor64 left:(Lsh64x64 x y) right:(Rsh64Ux64 x (Sub64 (Const64 [64]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 64) => (RotateLeft64 x y)` -/
theorem r_generic_2175_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2175_3 := by rule_auto

/-- `generic.rules:2176`: `(Xor64 left:(Lsh64x32 x y) right:(Rsh64Ux32 x (Sub32 (Const32 [64]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 64) => (RotateLeft64 x y)` -/
theorem r_generic_2176_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2176_3 := by rule_auto

end GoFV.Proof.Rules
