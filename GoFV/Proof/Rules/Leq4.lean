import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values04

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `Leq` rules (part 4)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Leq` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:618`: `(Leq32 (Const32 <t> [1]) x) => (Less32 (Const32 <t> [0]) x)` -/
theorem r_generic_618_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_618_2 := by rule_auto


/-- `generic.rules:701`: `(Leq32 (Const32 [math.MinInt32]) _) => (ConstBool [true])` -/
theorem r_generic_701_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_701 := by rule_auto


/-- `generic.rules:709`: `(Leq32 _ (Const32 [math.MaxInt32])) => (ConstBool [true])` -/
theorem r_generic_709_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_709 := by rule_auto


/-- `generic.rules:719`: `(Leq32 x c:(Const32 [math.MinInt32])) => (Eq32 x c)` -/
theorem r_generic_719_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_719 := by rule_auto


/-- `generic.rules:723`: `(Leq32 c:(Const32 [math.MaxInt32]) x) => (Eq32 x c)` -/
theorem r_generic_723_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_723 := by rule_auto


/-- `generic.rules:595`: `(Leq32U (Const32 [c]) (Const32 [d])) => (ConstBool [uint32(c) <= uint32(d)])` -/
theorem r_generic_595_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_595 := by rule_auto


/-- `generic.rules:613`: `(Leq32U (Const32 <t> [1]) x) => (Neq32 (Const32 <t> [0]) x)` -/
theorem r_generic_613_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_613_2 := by rule_auto


/-- `generic.rules:714`: `(Leq32U x c:(Const32 [0])) => (Eq32 x c)` -/
theorem r_generic_714_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_714_2 := by rule_auto


/-- `generic.rules:715`: `(Leq32U c:(Const32 [-1]) x) => (Eq32 x c)` -/
theorem r_generic_715_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_715_2 := by rule_auto


/-- `generic.rules:587`: `(Leq64 (Const64 [c]) (Const64 [d])) => (ConstBool [c <= d])` -/
theorem r_generic_587_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_587_3 := by rule_auto


/-- `generic.rules:602`: `(Leq64 (Const64 [0]) (And64 _ (Const64 [c]))) && c >= 0 => (ConstBool [true])` -/
theorem r_generic_602_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_602 := by rule_auto


/-- `generic.rules:607`: `(Leq64 (Const64 [0]) (Rsh64Ux64 _ (Const64 [c]))) && c > 0 => (ConstBool [true])` -/
theorem r_generic_607_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_607 := by rule_auto


/-- `generic.rules:618`: `(Leq64 (Const64 <t> [1]) x) => (Less64 (Const64 <t> [0]) x)` -/
theorem r_generic_618_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_618_3 := by rule_auto


/-- `generic.rules:700`: `(Leq64 (Const64 [math.MinInt64]) _) => (ConstBool [true])` -/
theorem r_generic_700_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_700 := by rule_auto


/-- `generic.rules:708`: `(Leq64 _ (Const64 [math.MaxInt64])) => (ConstBool [true])` -/
theorem r_generic_708_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_708 := by rule_auto

end GoFV.Proof.Rules
