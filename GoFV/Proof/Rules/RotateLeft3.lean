import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values10

/-!
# Rule lemmas: `RotateLeft` rules (part 3)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`RotateLeft` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:477`: `(RotateLeft64 x (Const64 [c])) && c%64 == 0 => x` -/
theorem r_generic_477_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_477 := by rule_auto


/-- `generic.rules:2216`: `(RotateLeft64 x (And64 y (Const64 [c]))) && c&63 == 63 => (RotateLeft64 x y)` -/
theorem r_generic_2216_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2216 := by rule_auto


/-- `generic.rules:2216`: `(RotateLeft64 x (And32 y (Const32 [c]))) && c&63 == 63 => (RotateLeft64 x y)` -/
theorem r_generic_2216_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2216_2 := by rule_auto


/-- `generic.rules:2216`: `(RotateLeft64 x (And16 y (Const16 [c]))) && c&63 == 63 => (RotateLeft64 x y)` -/
theorem r_generic_2216_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2216_3 := by rule_auto


/-- `generic.rules:2216`: `(RotateLeft64 x (And8 y (Const8 [c]))) && c&63 == 63 => (RotateLeft64 x y)` -/
theorem r_generic_2216_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2216_4 := by rule_auto


/-- `generic.rules:2222`: `(RotateLeft64 x (Neg64 (And64 y (Const64 [c])))) && c&63 == 63 => (RotateLeft64 x (Neg64 <y.Type> y))` -/
theorem r_generic_2222_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2222 := by rule_auto


/-- `generic.rules:2222`: `(RotateLeft64 x (Neg32 (And32 y (Const32 [c])))) && c&63 == 63 => (RotateLeft64 x (Neg32 <y.Type> y))` -/
theorem r_generic_2222_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2222_2 := by rule_auto


/-- `generic.rules:2222`: `(RotateLeft64 x (Neg16 (And16 y (Const16 [c])))) && c&63 == 63 => (RotateLeft64 x (Neg16 <y.Type> y))` -/
theorem r_generic_2222_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2222_3 := by rule_auto


end GoFV.Proof.Rules
