import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values10

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `RotateLeft` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`RotateLeft` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:479`: `(RotateLeft16 x (Const16 [c])) && c%16 == 0 => x` -/
theorem r_generic_479_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_479 := by rule_auto


/-- `generic.rules:2218`: `(RotateLeft16 x (And64 y (Const64 [c]))) && c&15 == 15 => (RotateLeft16 x y)` -/
theorem r_generic_2218_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2218 := by rule_auto


/-- `generic.rules:2218`: `(RotateLeft16 x (And32 y (Const32 [c]))) && c&15 == 15 => (RotateLeft16 x y)` -/
theorem r_generic_2218_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2218_2 := by rule_auto


/-- `generic.rules:2218`: `(RotateLeft16 x (And16 y (Const16 [c]))) && c&15 == 15 => (RotateLeft16 x y)` -/
theorem r_generic_2218_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2218_3 := by rule_auto


/-- `generic.rules:2218`: `(RotateLeft16 x (And8 y (Const8 [c]))) && c&15 == 15 => (RotateLeft16 x y)` -/
theorem r_generic_2218_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2218_4 := by rule_auto


/-- `generic.rules:2224`: `(RotateLeft16 x (Neg64 (And64 y (Const64 [c])))) && c&15 == 15 => (RotateLeft16 x (Neg64 <y.Type> y))` -/
theorem r_generic_2224_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2224 := by rule_auto


/-- `generic.rules:2224`: `(RotateLeft16 x (Neg32 (And32 y (Const32 [c])))) && c&15 == 15 => (RotateLeft16 x (Neg32 <y.Type> y))` -/
theorem r_generic_2224_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2224_2 := by rule_auto


/-- `generic.rules:2224`: `(RotateLeft16 x (Neg16 (And16 y (Const16 [c])))) && c&15 == 15 => (RotateLeft16 x (Neg16 <y.Type> y))` -/
theorem r_generic_2224_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2224_3 := by rule_auto


end GoFV.Proof.Rules
