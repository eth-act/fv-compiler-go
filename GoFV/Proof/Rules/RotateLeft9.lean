import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values10

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `RotateLeft` rules (part 9)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`RotateLeft` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:2222`: `(RotateLeft64 x (Neg8 (And8 y (Const8 [c])))) && c&63 == 63 => (RotateLeft64 x (Neg8 <y.Type> y))` -/
theorem r_generic_2222_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2222_4 := by rule_auto


/-- `generic.rules:2228`: `(RotateLeft64 x (Add64 y (Const64 [c]))) && c&63 == 0 => (RotateLeft64 x y)` -/
theorem r_generic_2228_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2228 := by rule_auto


/-- `generic.rules:2228`: `(RotateLeft64 x (Add32 y (Const32 [c]))) && c&63 == 0 => (RotateLeft64 x y)` -/
theorem r_generic_2228_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2228_2 := by rule_auto


/-- `generic.rules:2228`: `(RotateLeft64 x (Add16 y (Const16 [c]))) && c&63 == 0 => (RotateLeft64 x y)` -/
theorem r_generic_2228_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2228_3 := by rule_auto


/-- `generic.rules:2228`: `(RotateLeft64 x (Add8 y (Const8 [c]))) && c&63 == 0 => (RotateLeft64 x y)` -/
theorem r_generic_2228_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2228_4 := by rule_auto


/-- `generic.rules:2234`: `(RotateLeft64 x (Sub64 (Const64 [c]) y)) && c&63 == 0 => (RotateLeft64 x (Neg64 <y.Type> y))` -/
theorem r_generic_2234_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2234 := by rule_auto


/-- `generic.rules:2234`: `(RotateLeft64 x (Sub32 (Const32 [c]) y)) && c&63 == 0 => (RotateLeft64 x (Neg32 <y.Type> y))` -/
theorem r_generic_2234_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2234_2 := by rule_auto


/-- `generic.rules:2234`: `(RotateLeft64 x (Sub16 (Const16 [c]) y)) && c&63 == 0 => (RotateLeft64 x (Neg16 <y.Type> y))` -/
theorem r_generic_2234_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2234_3 := by rule_auto


end GoFV.Proof.Rules
