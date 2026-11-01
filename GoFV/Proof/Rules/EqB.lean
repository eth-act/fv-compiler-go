import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values03

/-!
# Rule lemmas: `EqB` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`EqB` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:280`: `(EqB x x) => (ConstBool [true])` -/
theorem r_generic_280_5_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_280_5 := by rule_auto

/-- `generic.rules:281`: `(EqB (ConstBool [c]) (ConstBool [d])) => (ConstBool [c == d])` -/
theorem r_generic_281_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_281 := by rule_auto

/-- `generic.rules:282`: `(EqB (ConstBool [false]) x) => (Not x)` -/
theorem r_generic_282_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_282 := by rule_auto

/-- `generic.rules:283`: `(EqB (ConstBool [true]) x) => x` -/
theorem r_generic_283_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_283 := by rule_auto

/-- `generic.rules:284`: `(EqB (Not x) y) => (NeqB x y)` -/
theorem r_generic_284_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_284 := by rule_auto

end GoFV.Proof.Rules
