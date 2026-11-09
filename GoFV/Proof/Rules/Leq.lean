import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values04

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `Leq` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Leq` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:617`: `(Leq16 x (Const16 <t> [-1])) => (Less16 x (Const16 <t> [0]))` -/
theorem r_generic_617_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_617 := by rule_auto

/-- `generic.rules:693`: `(Leq16U (Const16 [0]) _) => (ConstBool [true])` -/
theorem r_generic_693_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_693 := by rule_auto

/-- `generic.rules:695`: `(Leq16U _ (Const16 [-1])) => (ConstBool [true])` -/
theorem r_generic_695_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_695 := by rule_auto

/-- `generic.rules:617`: `(Leq32 x (Const32 <t> [-1])) => (Less32 x (Const32 <t> [0]))` -/
theorem r_generic_617_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_617_2 := by rule_auto

/-- `generic.rules:693`: `(Leq32U (Const32 [0]) _) => (ConstBool [true])` -/
theorem r_generic_693_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_693_2 := by rule_auto

/-- `generic.rules:695`: `(Leq32U _ (Const32 [-1])) => (ConstBool [true])` -/
theorem r_generic_695_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_695_2 := by rule_auto

/-- `generic.rules:617`: `(Leq64 x (Const64 <t> [-1])) => (Less64 x (Const64 <t> [0]))` -/
theorem r_generic_617_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_617_3 := by rule_auto

/-- `generic.rules:693`: `(Leq64U (Const64 [0]) _) => (ConstBool [true])` -/
theorem r_generic_693_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_693_3 := by rule_auto

/-- `generic.rules:695`: `(Leq64U _ (Const64 [-1])) => (ConstBool [true])` -/
theorem r_generic_695_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_695_3 := by rule_auto

/-- `generic.rules:617`: `(Leq8 x (Const8 <t> [-1])) => (Less8 x (Const8 <t> [0]))` -/
theorem r_generic_617_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_617_4 := by rule_auto

/-- `generic.rules:693`: `(Leq8U (Const8 [0]) _) => (ConstBool [true])` -/
theorem r_generic_693_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_693_4 := by rule_auto

/-- `generic.rules:695`: `(Leq8U _ (Const8 [-1])) => (ConstBool [true])` -/
theorem r_generic_695_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_695_4 := by rule_auto

end GoFV.Proof.Rules
