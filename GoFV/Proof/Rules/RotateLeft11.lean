import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values10

/-!
# Rule lemmas: `RotateLeft` rules (part 11)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`RotateLeft` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:2225`: `(RotateLeft8 x (Neg8 (And8 y (Const8 [c])))) && c&7 == 7 => (RotateLeft8 x (Neg8 <y.Type> y))` -/
theorem r_generic_2225_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2225_4 := by rule_auto


/-- `generic.rules:2231`: `(RotateLeft8 x (Add64 y (Const64 [c]))) && c&7 == 0 => (RotateLeft8 x y)` -/
theorem r_generic_2231_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2231 := by rule_auto


/-- `generic.rules:2231`: `(RotateLeft8 x (Add32 y (Const32 [c]))) && c&7 == 0 => (RotateLeft8 x y)` -/
theorem r_generic_2231_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2231_2 := by rule_auto


/-- `generic.rules:2231`: `(RotateLeft8 x (Add16 y (Const16 [c]))) && c&7 == 0 => (RotateLeft8 x y)` -/
theorem r_generic_2231_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2231_3 := by rule_auto


/-- `generic.rules:2231`: `(RotateLeft8 x (Add8 y (Const8 [c]))) && c&7 == 0 => (RotateLeft8 x y)` -/
theorem r_generic_2231_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2231_4 := by rule_auto


/-- `generic.rules:2237`: `(RotateLeft8 x (Sub64 (Const64 [c]) y)) && c&7 == 0 => (RotateLeft8 x (Neg64 <y.Type> y))` -/
theorem r_generic_2237_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2237 := by rule_auto


/-- `generic.rules:2237`: `(RotateLeft8 x (Sub32 (Const32 [c]) y)) && c&7 == 0 => (RotateLeft8 x (Neg32 <y.Type> y))` -/
theorem r_generic_2237_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2237_2 := by rule_auto


/-- `generic.rules:2237`: `(RotateLeft8 x (Sub16 (Const16 [c]) y)) && c&7 == 0 => (RotateLeft8 x (Neg16 <y.Type> y))` -/
theorem r_generic_2237_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2237_3 := by rule_auto


end GoFV.Proof.Rules
