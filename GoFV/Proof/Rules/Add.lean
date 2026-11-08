import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values00

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `Add` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Add` family (`docs/proofs/rules.md`).
-/

/-! False rules (`docs/proofs/rules.md`, "Findings"); `scripts/rule-proofs.py table` reads these lines.
-- FALSE r_generic_2168 #90
-- FALSE r_generic_2167 #90
-- FALSE r_generic_2166 #90
-- FALSE r_generic_2169 #90
-- FALSE r_generic_2168_2 #90
-- FALSE r_generic_2167_2 #90
-- FALSE r_generic_2166_2 #90
-- FALSE r_generic_2169_2 #90
-- FALSE r_generic_2168_3 #90
-- FALSE r_generic_2167_3 #90
-- FALSE r_generic_2166_3 #90
-- FALSE r_generic_2169_3 #90
-/

/-! False rules (`docs/proofs/rules.md`, "Findings"); `scripts/rule-proofs.py table` reads these lines.
`CondSelect` into `Sub` (`generic.rules:2342`): at `bool = false` the matched value is `x`, the
result `x - 0`, `poison` when `x` is an address-less pointer in a 64-bit integer register
(#69, RuleProofs10).
-- FALSE r_generic_2342 #69
-- FALSE r_generic_2342_2 #69
-- FALSE r_generic_2342_3 #69
`generic.rules:2325` (`CondSelect` into `Add` and `Mul` by the condition): the same at
`bool = false` (`x + c*0`), and the leaf `x` of the narrower forms is not constrained to the
`Add`'s width (RuleProofs17).
-- FALSE r_generic_2325 #69
-- FALSE r_generic_2325_2 #69
-- FALSE r_generic_2325_3 #69
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:121`: `(Add16 (Const16 [c]) (Const16 [d])) => (Const16 [c+d])` -/
theorem r_generic_121_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_121 := by rule_auto


/-- `generic.rules:420`: `(Add16 <t> (Mul16 x y) (Mul16 x z)) => (Mul16 x (Add16 <t> y z))` -/
theorem r_generic_420_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_420 := by rule_auto


/-- `generic.rules:427`: `(Add16 x x) => (Lsh16x64 x (Const64 <types.Types[types.TUINT64]> [1]))` -/
theorem r_generic_427_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_427 := by rule_auto


/-- `generic.rules:646`: `(Add16 (Const16 [0]) x) => x` -/
theorem r_generic_646_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_646 := by rule_auto


/-- `generic.rules:655`: `(Add16 x (Neg16 y)) => (Sub16 x y)` -/
theorem r_generic_655_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_655 := by rule_auto


/-- `generic.rules:661`: `(Add16 (Com16 x) x) => (Const16 [-1])` -/
theorem r_generic_661_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_661 := by rule_auto


/-- `generic.rules:675`: `(Add16 (Sub16 x t) (Add16 t y)) => (Add16 x y)` -/
theorem r_generic_675_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_675 := by rule_auto


/-- `generic.rules:678`: `(Add16 (Const16 [1]) (Com16 x)) => (Neg16 x)` -/
theorem r_generic_678_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_678 := by rule_auto


/-- `generic.rules:778`: `(Add16 x (Sub16 y x)) => y` -/
theorem r_generic_778_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_778 := by rule_auto


/-- `generic.rules:779`: `(Add16 x (Add16 y (Sub16 z x))) => (Add16 y z)` -/
theorem r_generic_779_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_779 := by rule_auto


/-- `generic.rules:1218`: `(Add16 (Add16 i:(Const16 <t>) z) x) && (z.Op != OpConst16 && x.Op != OpConst16) => (Add16 i (Add16 <t> z x))` -/
theorem r_generic_1218_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1218 := by rule_auto


/-- `generic.rules:1224`: `(Add16 (Sub16 i:(Const16 <t>) z) x) && (z.Op != OpConst16 && x.Op != OpConst16) => (Add16 i (Sub16 <t> x z))` -/
theorem r_generic_1224_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1224 := by rule_auto


/-- `generic.rules:1278`: `(Add16 (Const16 <t> [c]) (Add16 (Const16 <t> [d]) x)) => (Add16 (Const16 <t> [c+d]) x)` -/
theorem r_generic_1278_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1278 := by rule_auto


/-- `generic.rules:1284`: `(Add16 (Const16 <t> [c]) (Sub16 (Const16 <t> [d]) x)) => (Sub16 (Const16 <t> [c+d]) x)` -/
theorem r_generic_1284_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1284 := by rule_auto


/-- `generic.rules:2195`: `(Add16 left:(Lsh16x64 x y) right:(Rsh16Ux64 x (Sub64 (Const64 [16]) y))) && (shiftIsBounded(left) || shiftIsBounded(right)) && canRotate(config, 16) => (RotateLeft16 x y)` -/
theorem r_generic_2195_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2195 := by rule_auto


end GoFV.Proof.Rules
