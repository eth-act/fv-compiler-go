import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values04
import GoFV.Rules.Generated.Generic.Values05

/-!
# Rule lemmas: `Less` rules (part 2)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Less` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:586`: `(Less16 (Const16 [c]) (Const16 [d])) => (ConstBool [c < d])` -/
theorem r_generic_586_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_586 := by rule_auto


/-- `generic.rules:616`: `(Less16 x (Const16 <t> [1])) => (Leq16 x (Const16 <t> [0]))` -/
theorem r_generic_616_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_616 := by rule_auto


/-- `generic.rules:698`: `(Less16 _ (Const16 [math.MinInt16])) => (ConstBool [false])` -/
theorem r_generic_698_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_698 := by rule_auto


/-- `generic.rules:706`: `(Less16 (Const16 [math.MaxInt16]) _) => (ConstBool [false])` -/
theorem r_generic_706_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_706 := by rule_auto


/-- `generic.rules:728`: `(Less16 x (Const16 <t> [math.MinInt16+1])) => (Eq16 x (Const16 <t> [math.MinInt16]))` -/
theorem r_generic_728_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_728 := by rule_auto


/-- `generic.rules:732`: `(Less16 (Const16 <t> [math.MaxInt16-1]) x) => (Eq16 x (Const16 <t> [math.MaxInt16]))` -/
theorem r_generic_732_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_732 := by rule_auto


/-- `generic.rules:591`: `(Less16U (Const16 [c]) (Const16 [d])) => (ConstBool [uint16(c) < uint16(d)])` -/
theorem r_generic_591_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_591 := by rule_auto


/-- `generic.rules:612`: `(Less16U x (Const16 <t> [1])) => (Eq16 (Const16 <t> [0]) x)` -/
theorem r_generic_612_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_612 := by rule_auto


/-- `generic.rules:716`: `(Less16U x (Const16 <t> [1])) => (Eq16 x (Const16 <t> [0]))` -/
theorem r_generic_716_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_716 := by rule_auto


/-- `generic.rules:717`: `(Less16U (Const16 <t> [-2]) x) => (Eq16 x (Const16 <t> [-1]))` -/
theorem r_generic_717_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_717 := by rule_auto


/-- `generic.rules:586`: `(Less32 (Const32 [c]) (Const32 [d])) => (ConstBool [c < d])` -/
theorem r_generic_586_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_586_2 := by rule_auto


/-- `generic.rules:616`: `(Less32 x (Const32 <t> [1])) => (Leq32 x (Const32 <t> [0]))` -/
theorem r_generic_616_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_616_2 := by rule_auto


/-- `generic.rules:697`: `(Less32 _ (Const32 [math.MinInt32])) => (ConstBool [false])` -/
theorem r_generic_697_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_697 := by rule_auto


/-- `generic.rules:705`: `(Less32 (Const32 [math.MaxInt32]) _) => (ConstBool [false])` -/
theorem r_generic_705_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_705 := by rule_auto


/-- `generic.rules:727`: `(Less32 x (Const32 <t> [math.MinInt32+1])) => (Eq32 x (Const32 <t> [math.MinInt32]))` -/
theorem r_generic_727_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_727 := by rule_auto


end GoFV.Proof.Rules
