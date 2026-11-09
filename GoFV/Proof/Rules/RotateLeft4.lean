import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values10

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `RotateLeft` rules (part 4)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`RotateLeft` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:480`: `(RotateLeft8 x (Const8 [c])) && c%8 == 0 => x` -/
theorem r_generic_480_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_480 := by rule_auto


/-- `generic.rules:2219`: `(RotateLeft8 x (And64 y (Const64 [c]))) && c&7 == 7 => (RotateLeft8 x y)` -/
theorem r_generic_2219_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2219 := by rule_auto


/-- `generic.rules:2219`: `(RotateLeft8 x (And32 y (Const32 [c]))) && c&7 == 7 => (RotateLeft8 x y)` -/
theorem r_generic_2219_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2219_2 := by rule_auto


/-- `generic.rules:2219`: `(RotateLeft8 x (And16 y (Const16 [c]))) && c&7 == 7 => (RotateLeft8 x y)` -/
theorem r_generic_2219_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2219_3 := by rule_auto


/-- `generic.rules:2219`: `(RotateLeft8 x (And8 y (Const8 [c]))) && c&7 == 7 => (RotateLeft8 x y)` -/
theorem r_generic_2219_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2219_4 := by rule_auto


/-- `generic.rules:2225`: `(RotateLeft8 x (Neg64 (And64 y (Const64 [c])))) && c&7 == 7 => (RotateLeft8 x (Neg64 <y.Type> y))` -/
theorem r_generic_2225_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2225 := by rule_auto


/-- `generic.rules:2225`: `(RotateLeft8 x (Neg32 (And32 y (Const32 [c])))) && c&7 == 7 => (RotateLeft8 x (Neg32 <y.Type> y))` -/
theorem r_generic_2225_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2225_2 := by rule_auto


/-- `generic.rules:2225`: `(RotateLeft8 x (Neg16 (And16 y (Const16 [c])))) && c&7 == 7 => (RotateLeft8 x (Neg16 <y.Type> y))` -/
theorem r_generic_2225_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2225_3 := by rule_auto


end GoFV.Proof.Rules
