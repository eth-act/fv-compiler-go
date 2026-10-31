import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values00

/-!
# Rule lemmas: `Add` rules (part 2)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Add` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

-- `bv_decide` proofs fail nondeterministically under parallel elaboration here (`grind failed`
-- after a `bv_decide` that succeeds sequentially); the probe runs sequentially too.
set_option Elab.async false

/-- `generic.rules:778`: `(Add32 x (Sub32 y x)) => y` -/
theorem r_generic_778_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_778_2 := by rule_auto

/-- `generic.rules:779`: `(Add32 x (Add32 y (Sub32 z x))) => (Add32 y z)` -/
theorem r_generic_779_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_779_2 := by rule_auto

/-- `generic.rules:1217`: `(Add32 (Add32 i:(Const32 <t>) z) x) && (z.Op != OpConst32 && x.Op != OpConst32) => (Add32 i (Add32 <t> z x))` -/
theorem r_generic_1217_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1217 := by rule_auto

/-- `generic.rules:1223`: `(Add32 (Sub32 i:(Const32 <t>) z) x) && (z.Op != OpConst32 && x.Op != OpConst32) => (Add32 i (Sub32 <t> x z))` -/
theorem r_generic_1223_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1223 := by rule_auto

/-- `generic.rules:1277`: `(Add32 (Const32 <t> [c]) (Add32 (Const32 <t> [d]) x)) => (Add32 (Const32 <t> [c+d]) x)` -/
theorem r_generic_1277_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1277 := by rule_auto

/-- `generic.rules:1283`: `(Add32 (Const32 <t> [c]) (Sub32 (Const32 <t> [d]) x)) => (Sub32 (Const32 <t> [c+d]) x)` -/
theorem r_generic_1283_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1283 := by rule_auto

/-- `generic.rules:2185`: `(Add32 left:(Lsh32x64 x y) right:(Rsh32Ux64 x (Sub64 (Const64 [32]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 32) => (RotateLeft32 x y)` -/
theorem r_generic_2185_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2185 := by rule_auto

/-- `generic.rules:2186`: `(Add32 left:(Lsh32x32 x y) right:(Rsh32Ux32 x (Sub32 (Const32 [32]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 32) => (RotateLeft32 x y)` -/
theorem r_generic_2186_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2186 := by rule_auto

/-- `generic.rules:2187`: `(Add32 left:(Lsh32x16 x y) right:(Rsh32Ux16 x (Sub16 (Const16 [32]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 32) => (RotateLeft32 x y)` -/
theorem r_generic_2187_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2187 := by rule_auto

/-- `generic.rules:2188`: `(Add32 left:(Lsh32x8 x y) right:(Rsh32Ux8 x (Sub8 (Const8 [32]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 32) => (RotateLeft32 x y)` -/
theorem r_generic_2188_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2188 := by rule_auto

/-- `generic.rules:2190`: `(Add32 right:(Rsh32Ux64 x y) left:(Lsh32x64 x z:(Sub64 (Const64 [32]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 32) => (RotateLeft32 x z)` -/
theorem r_generic_2190_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2190 := by rule_auto

/-- `generic.rules:2191`: `(Add32 right:(Rsh32Ux32 x y) left:(Lsh32x32 x z:(Sub32 (Const32 [32]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 32) => (RotateLeft32 x z)` -/
theorem r_generic_2191_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2191 := by rule_auto

/-- `generic.rules:2192`: `(Add32 right:(Rsh32Ux16 x y) left:(Lsh32x16 x z:(Sub16 (Const16 [32]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 32) => (RotateLeft32 x z)` -/
theorem r_generic_2192_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2192 := by rule_auto

/-- `generic.rules:2193`: `(Add32 right:(Rsh32Ux8 x y) left:(Lsh32x8 x z:(Sub8 (Const8 [32]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 32) => (RotateLeft32 x z)` -/
theorem r_generic_2193_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2193 := by rule_auto

/-- `generic.rules:123`: `(Add64 (Const64 [c]) (Const64 [d])) => (Const64 [c+d])` -/
theorem r_generic_123_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_123 := by rule_auto

/-- `generic.rules:420`: `(Add64 <t> (Mul64 x y) (Mul64 x z)) => (Mul64 x (Add64 <t> y z))` -/
theorem r_generic_420_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_420_3 := by rule_auto

/-- `generic.rules:427`: `(Add64 x x) => (Lsh64x64 x (Const64 <types.Types[types.TUINT64]> [1]))` -/
theorem r_generic_427_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_427_3 := by rule_auto

/-- `generic.rules:646`: `(Add64 (Const64 [0]) x) => x` -/
theorem r_generic_646_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_646_3 := by rule_auto

/-- `generic.rules:655`: `(Add64 x (Neg64 y)) => (Sub64 x y)` -/
theorem r_generic_655_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_655_3 := by rule_auto

/-- `generic.rules:661`: `(Add64 (Com64 x) x) => (Const64 [-1])` -/
theorem r_generic_661_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_661_3 := by rule_auto

/-- `generic.rules:675`: `(Add64 (Sub64 x t) (Add64 t y)) => (Add64 x y)` -/
theorem r_generic_675_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_675_3 := by rule_auto

/-- `generic.rules:678`: `(Add64 (Const64 [1]) (Com64 x)) => (Neg64 x)` -/
theorem r_generic_678_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_678_3 := by rule_auto

/-- `generic.rules:778`: `(Add64 x (Sub64 y x)) => y` -/
theorem r_generic_778_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_778_3 := by rule_auto

/-- `generic.rules:779`: `(Add64 x (Add64 y (Sub64 z x))) => (Add64 y z)` -/
theorem r_generic_779_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_779_3 := by rule_auto

/-- `generic.rules:1216`: `(Add64 (Add64 i:(Const64 <t>) z) x) && (z.Op != OpConst64 && x.Op != OpConst64) => (Add64 i (Add64 <t> z x))` -/
theorem r_generic_1216_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1216 := by rule_auto

/-- `generic.rules:1222`: `(Add64 (Sub64 i:(Const64 <t>) z) x) && (z.Op != OpConst64 && x.Op != OpConst64) => (Add64 i (Sub64 <t> x z))` -/
theorem r_generic_1222_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1222 := by rule_auto

/-- `generic.rules:1276`: `(Add64 (Const64 <t> [c]) (Add64 (Const64 <t> [d]) x)) => (Add64 (Const64 <t> [c+d]) x)` -/
theorem r_generic_1276_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1276 := by rule_auto

/-- `generic.rules:1282`: `(Add64 (Const64 <t> [c]) (Sub64 (Const64 <t> [d]) x)) => (Sub64 (Const64 <t> [c+d]) x)` -/
theorem r_generic_1282_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1282 := by rule_auto

/-- `generic.rules:2175`: `(Add64 left:(Lsh64x64 x y) right:(Rsh64Ux64 x (Sub64 (Const64 [64]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 64) => (RotateLeft64 x y)` -/
theorem r_generic_2175_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2175 := by rule_auto

/-- `generic.rules:2176`: `(Add64 left:(Lsh64x32 x y) right:(Rsh64Ux32 x (Sub32 (Const32 [64]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 64) => (RotateLeft64 x y)` -/
theorem r_generic_2176_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2176 := by rule_auto

end GoFV.Proof.Rules
