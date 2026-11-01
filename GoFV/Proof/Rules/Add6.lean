import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values00

/-!
# Rule lemmas: `Add` rules (part 6)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Add` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

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
