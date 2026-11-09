import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values02

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `CvtBoolToUint` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the P1/P2 rules whose top op is in the
`CvtBoolToUint` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:59`: `(CvtBoolToUint8 (ConstBool [false])) => (Const8 [0])` -/
theorem r_generic_59_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_59 := by rule_auto

/-- `generic.rules:60`: `(CvtBoolToUint8 (ConstBool [true])) => (Const8 [1])` -/
theorem r_generic_60_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_60 := by rule_auto

end GoFV.Proof.Rules
