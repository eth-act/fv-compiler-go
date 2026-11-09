import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values04

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `Leq` rules (part 2)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Leq` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:587`: `(Leq16 (Const16 [c]) (Const16 [d])) => (ConstBool [c <= d])` -/
theorem r_generic_587_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_587 := by rule_auto


/-- `generic.rules:600`: `(Leq16 (Const16 [0]) (And16 _ (Const16 [c]))) && c >= 0 => (ConstBool [true])` -/
theorem r_generic_600_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_600 := by rule_auto


/-- `generic.rules:605`: `(Leq16 (Const16 [0]) (Rsh16Ux64 _ (Const64 [c]))) && c > 0 => (ConstBool [true])` -/
theorem r_generic_605_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_605 := by rule_auto


/-- `generic.rules:618`: `(Leq16 (Const16 <t> [1]) x) => (Less16 (Const16 <t> [0]) x)` -/
theorem r_generic_618_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_618 := by rule_auto


/-- `generic.rules:702`: `(Leq16 (Const16 [math.MinInt16]) _) => (ConstBool [true])` -/
theorem r_generic_702_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_702 := by rule_auto


/-- `generic.rules:710`: `(Leq16 _ (Const16 [math.MaxInt16])) => (ConstBool [true])` -/
theorem r_generic_710_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_710 := by rule_auto


/-- `generic.rules:720`: `(Leq16 x c:(Const16 [math.MinInt16])) => (Eq16 x c)` -/
theorem r_generic_720_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_720 := by rule_auto


/-- `generic.rules:724`: `(Leq16 c:(Const16 [math.MaxInt16]) x) => (Eq16 x c)` -/
theorem r_generic_724_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_724 := by rule_auto


/-- `generic.rules:596`: `(Leq16U (Const16 [c]) (Const16 [d])) => (ConstBool [uint16(c) <= uint16(d)])` -/
theorem r_generic_596_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_596 := by rule_auto


/-- `generic.rules:613`: `(Leq16U (Const16 <t> [1]) x) => (Neq16 (Const16 <t> [0]) x)` -/
theorem r_generic_613_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_613 := by rule_auto


/-- `generic.rules:714`: `(Leq16U x c:(Const16 [0])) => (Eq16 x c)` -/
theorem r_generic_714_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_714 := by rule_auto


/-- `generic.rules:715`: `(Leq16U c:(Const16 [-1]) x) => (Eq16 x c)` -/
theorem r_generic_715_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_715 := by rule_auto


/-- `generic.rules:587`: `(Leq32 (Const32 [c]) (Const32 [d])) => (ConstBool [c <= d])` -/
theorem r_generic_587_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_587_2 := by rule_auto


/-- `generic.rules:601`: `(Leq32 (Const32 [0]) (And32 _ (Const32 [c]))) && c >= 0 => (ConstBool [true])` -/
theorem r_generic_601_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_601 := by rule_auto


/-- `generic.rules:606`: `(Leq32 (Const32 [0]) (Rsh32Ux64 _ (Const64 [c]))) && c > 0 => (ConstBool [true])` -/
theorem r_generic_606_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_606 := by rule_auto


end GoFV.Proof.Rules
