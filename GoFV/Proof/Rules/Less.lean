import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values04
import GoFV.Rules.Generated.Generic.Values05

/-!
# Rule lemmas: `Less` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Less` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:619`: `(Less16 (Const16 <t> [-1]) x) => (Leq16 (Const16 <t> [0]) x)` -/
theorem r_generic_619_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_619 := by rule_auto

/-- `generic.rules:692`: `(Less16U _ (Const16 [0])) => (ConstBool [false])` -/
theorem r_generic_692_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_692 := by rule_auto

/-- `generic.rules:694`: `(Less16U (Const16 [-1]) _) => (ConstBool [false])` -/
theorem r_generic_694_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_694 := by rule_auto

/-- `generic.rules:619`: `(Less32 (Const32 <t> [-1]) x) => (Leq32 (Const32 <t> [0]) x)` -/
theorem r_generic_619_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_619_2 := by rule_auto

/-- `generic.rules:692`: `(Less32U _ (Const32 [0])) => (ConstBool [false])` -/
theorem r_generic_692_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_692_2 := by rule_auto

/-- `generic.rules:694`: `(Less32U (Const32 [-1]) _) => (ConstBool [false])` -/
theorem r_generic_694_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_694_2 := by rule_auto

/-- `generic.rules:619`: `(Less64 (Const64 <t> [-1]) x) => (Leq64 (Const64 <t> [0]) x)` -/
theorem r_generic_619_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_619_3 := by rule_auto

/-- `generic.rules:692`: `(Less64U _ (Const64 [0])) => (ConstBool [false])` -/
theorem r_generic_692_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_692_3 := by rule_auto

/-- `generic.rules:694`: `(Less64U (Const64 [-1]) _) => (ConstBool [false])` -/
theorem r_generic_694_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_694_3 := by rule_auto

/-- `generic.rules:619`: `(Less8 (Const8 <t> [-1]) x) => (Leq8 (Const8 <t> [0]) x)` -/
theorem r_generic_619_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_619_4 := by rule_auto

/-- `generic.rules:692`: `(Less8U _ (Const8 [0])) => (ConstBool [false])` -/
theorem r_generic_692_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_692_4 := by rule_auto

/-- `generic.rules:694`: `(Less8U (Const8 [-1]) _) => (ConstBool [false])` -/
theorem r_generic_694_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_694_4 := by rule_auto

/-- `generic.rules:610`: `(Less16 (Const16 <t> [0]) x) && isNonNegative(x) => (Neq16 (Const16 <t> [0]) x)` -/
theorem r_generic_610_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_610 := by rule_auto

/-- `generic.rules:611`: `(Less16 x (Const16 <t> [1])) && isNonNegative(x) => (Eq16 (Const16 <t> [0]) x)` -/
theorem r_generic_611_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_611 := by rule_auto

/-- `generic.rules:610`: `(Less32 (Const32 <t> [0]) x) && isNonNegative(x) => (Neq32 (Const32 <t> [0]) x)` -/
theorem r_generic_610_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_610_2 := by rule_auto

/-- `generic.rules:611`: `(Less32 x (Const32 <t> [1])) && isNonNegative(x) => (Eq32 (Const32 <t> [0]) x)` -/
theorem r_generic_611_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_611_2 := by rule_auto

/-- `generic.rules:610`: `(Less64 (Const64 <t> [0]) x) && isNonNegative(x) => (Neq64 (Const64 <t> [0]) x)` -/
theorem r_generic_610_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_610_3 := by rule_auto

/-- `generic.rules:611`: `(Less64 x (Const64 <t> [1])) && isNonNegative(x) => (Eq64 (Const64 <t> [0]) x)` -/
theorem r_generic_611_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_611_3 := by rule_auto

/-- `generic.rules:610`: `(Less8 (Const8 <t> [0]) x) && isNonNegative(x) => (Neq8 (Const8 <t> [0]) x)` -/
theorem r_generic_610_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_610_4 := by rule_auto

/-- `generic.rules:611`: `(Less8 x (Const8 <t> [1])) && isNonNegative(x) => (Eq8 (Const8 <t> [0]) x)` -/
theorem r_generic_611_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_611_4 := by rule_auto

end GoFV.Proof.Rules
