import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values04
import GoFV.Rules.Generated.Generic.Values05

/-!
# Rule lemmas: `Less` rules (part 4)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Less` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:731`: `(Less32 (Const32 <t> [math.MaxInt32-1]) x) => (Eq32 x (Const32 <t> [math.MaxInt32]))` -/
theorem r_generic_731_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_731 := by rule_auto


/-- `generic.rules:590`: `(Less32U (Const32 [c]) (Const32 [d])) => (ConstBool [uint32(c) < uint32(d)])` -/
theorem r_generic_590_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_590 := by rule_auto


/-- `generic.rules:612`: `(Less32U x (Const32 <t> [1])) => (Eq32 (Const32 <t> [0]) x)` -/
theorem r_generic_612_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_612_2 := by rule_auto


/-- `generic.rules:716`: `(Less32U x (Const32 <t> [1])) => (Eq32 x (Const32 <t> [0]))` -/
theorem r_generic_716_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_716_2 := by rule_auto


/-- `generic.rules:717`: `(Less32U (Const32 <t> [-2]) x) => (Eq32 x (Const32 <t> [-1]))` -/
theorem r_generic_717_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_717_2 := by rule_auto


/-- `generic.rules:586`: `(Less64 (Const64 [c]) (Const64 [d])) => (ConstBool [c < d])` -/
theorem r_generic_586_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_586_3 := by rule_auto


/-- `generic.rules:616`: `(Less64 x (Const64 <t> [1])) => (Leq64 x (Const64 <t> [0]))` -/
theorem r_generic_616_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_616_3 := by rule_auto


/-- `generic.rules:696`: `(Less64 _ (Const64 [math.MinInt64])) => (ConstBool [false])` -/
theorem r_generic_696_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_696 := by rule_auto


/-- `generic.rules:704`: `(Less64 (Const64 [math.MaxInt64]) _) => (ConstBool [false])` -/
theorem r_generic_704_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_704 := by rule_auto


/-- `generic.rules:726`: `(Less64 x (Const64 <t> [math.MinInt64+1])) => (Eq64 x (Const64 <t> [math.MinInt64]))` -/
theorem r_generic_726_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_726 := by rule_auto


/-- `generic.rules:730`: `(Less64 (Const64 <t> [math.MaxInt64-1]) x) => (Eq64 x (Const64 <t> [math.MaxInt64]))` -/
theorem r_generic_730_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_730 := by rule_auto


/-- `generic.rules:589`: `(Less64U (Const64 [c]) (Const64 [d])) => (ConstBool [uint64(c) < uint64(d)])` -/
theorem r_generic_589_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_589 := by rule_auto


/-- `generic.rules:612`: `(Less64U x (Const64 <t> [1])) => (Eq64 (Const64 <t> [0]) x)` -/
theorem r_generic_612_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_612_3 := by rule_auto


/-- `generic.rules:716`: `(Less64U x (Const64 <t> [1])) => (Eq64 x (Const64 <t> [0]))` -/
theorem r_generic_716_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_716_3 := by rule_auto


/-- `generic.rules:717`: `(Less64U (Const64 <t> [-2]) x) => (Eq64 x (Const64 <t> [-1]))` -/
theorem r_generic_717_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_717_3 := by rule_auto

end GoFV.Proof.Rules
