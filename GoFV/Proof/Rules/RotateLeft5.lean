import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values10

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `RotateLeft` rules (part 5)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`RotateLeft` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:2224`: `(RotateLeft16 x (Neg8 (And8 y (Const8 [c])))) && c&15 == 15 => (RotateLeft16 x (Neg8 <y.Type> y))` -/
theorem r_generic_2224_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2224_4 := by rule_auto


/-- `generic.rules:2230`: `(RotateLeft16 x (Add64 y (Const64 [c]))) && c&15 == 0 => (RotateLeft16 x y)` -/
theorem r_generic_2230_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2230 := by rule_auto


/-- `generic.rules:2230`: `(RotateLeft16 x (Add32 y (Const32 [c]))) && c&15 == 0 => (RotateLeft16 x y)` -/
theorem r_generic_2230_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2230_2 := by rule_auto


/-- `generic.rules:2230`: `(RotateLeft16 x (Add16 y (Const16 [c]))) && c&15 == 0 => (RotateLeft16 x y)` -/
theorem r_generic_2230_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2230_3 := by rule_auto


/-- `generic.rules:2230`: `(RotateLeft16 x (Add8 y (Const8 [c]))) && c&15 == 0 => (RotateLeft16 x y)` -/
theorem r_generic_2230_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2230_4 := by rule_auto


/-- `generic.rules:2236`: `(RotateLeft16 x (Sub64 (Const64 [c]) y)) && c&15 == 0 => (RotateLeft16 x (Neg64 <y.Type> y))` -/
theorem r_generic_2236_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2236 := by rule_auto


/-- `generic.rules:2236`: `(RotateLeft16 x (Sub32 (Const32 [c]) y)) && c&15 == 0 => (RotateLeft16 x (Neg32 <y.Type> y))` -/
theorem r_generic_2236_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2236_2 := by rule_auto


/-- `generic.rules:2236`: `(RotateLeft16 x (Sub16 (Const16 [c]) y)) && c&15 == 0 => (RotateLeft16 x (Neg16 <y.Type> y))` -/
theorem r_generic_2236_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2236_3 := by rule_auto


end GoFV.Proof.Rules
