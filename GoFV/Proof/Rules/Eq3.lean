import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values03

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `Eq` rules (part 3)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Eq` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:584`: `(Eq16 (Const16 [c]) (Const16 [d])) => (ConstBool [c == d])` -/
theorem r_generic_584_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_584 := by rule_auto

/-- `generic.rules:584`: `(Eq32 (Const32 [c]) (Const32 [d])) => (ConstBool [c == d])` -/
theorem r_generic_584_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_584_2 := by rule_auto

/-- `generic.rules:584`: `(Eq64 (Const64 [c]) (Const64 [d])) => (ConstBool [c == d])` -/
theorem r_generic_584_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_584_3 := by rule_auto

/-- `generic.rules:584`: `(Eq8 (Const8 [c]) (Const8 [d])) => (ConstBool [c == d])` -/
theorem r_generic_584_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_584_4 := by rule_auto

end GoFV.Proof.Rules
