import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values07

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `NeqB` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`NeqB` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:286`: `(NeqB x x) => (ConstBool [false])` -/
theorem r_generic_286_5_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_286_5 := by rule_auto

/-- `generic.rules:287`: `(NeqB (ConstBool [c]) (ConstBool [d])) => (ConstBool [c != d])` -/
theorem r_generic_287_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_287 := by rule_auto

/-- `generic.rules:288`: `(NeqB (ConstBool [false]) x) => x` -/
theorem r_generic_288_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_288 := by rule_auto

/-- `generic.rules:289`: `(NeqB (ConstBool [true]) x) => (Not x)` -/
theorem r_generic_289_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_289 := by rule_auto

/-- `generic.rules:290`: `(NeqB (Not x) y) => (EqB x y)` -/
theorem r_generic_290_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_290 := by rule_auto

end GoFV.Proof.Rules
