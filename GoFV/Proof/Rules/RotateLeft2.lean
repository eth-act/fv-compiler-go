import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values10

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `RotateLeft` rules (part 2)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`RotateLeft` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:478`: `(RotateLeft32 x (Const32 [c])) && c%32 == 0 => x` -/
theorem r_generic_478_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_478 := by rule_auto


/-- `generic.rules:2217`: `(RotateLeft32 x (And64 y (Const64 [c]))) && c&31 == 31 => (RotateLeft32 x y)` -/
theorem r_generic_2217_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2217 := by rule_auto


/-- `generic.rules:2217`: `(RotateLeft32 x (And32 y (Const32 [c]))) && c&31 == 31 => (RotateLeft32 x y)` -/
theorem r_generic_2217_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2217_2 := by rule_auto


/-- `generic.rules:2217`: `(RotateLeft32 x (And16 y (Const16 [c]))) && c&31 == 31 => (RotateLeft32 x y)` -/
theorem r_generic_2217_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2217_3 := by rule_auto


/-- `generic.rules:2217`: `(RotateLeft32 x (And8 y (Const8 [c]))) && c&31 == 31 => (RotateLeft32 x y)` -/
theorem r_generic_2217_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2217_4 := by rule_auto


/-- `generic.rules:2223`: `(RotateLeft32 x (Neg64 (And64 y (Const64 [c])))) && c&31 == 31 => (RotateLeft32 x (Neg64 <y.Type> y))` -/
theorem r_generic_2223_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2223 := by rule_auto


/-- `generic.rules:2223`: `(RotateLeft32 x (Neg32 (And32 y (Const32 [c])))) && c&31 == 31 => (RotateLeft32 x (Neg32 <y.Type> y))` -/
theorem r_generic_2223_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2223_2 := by rule_auto


/-- `generic.rules:2223`: `(RotateLeft32 x (Neg16 (And16 y (Const16 [c])))) && c&31 == 31 => (RotateLeft32 x (Neg16 <y.Type> y))` -/
theorem r_generic_2223_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2223_3 := by rule_auto


end GoFV.Proof.Rules
