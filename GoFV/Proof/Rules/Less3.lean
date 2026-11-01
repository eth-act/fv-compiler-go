import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values05

/-!
# Rule lemmas: `Less` rules (part 3)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Less` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:586`: `(Less8 (Const8 [c]) (Const8 [d])) => (ConstBool [c < d])` -/
theorem r_generic_586_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_586_4 := by rule_auto

/-- `generic.rules:616`: `(Less8 x (Const8 <t> [1])) => (Leq8 x (Const8 <t> [0]))` -/
theorem r_generic_616_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_616_4 := by rule_auto

/-- `generic.rules:699`: `(Less8 _ (Const8 [math.MinInt8 ])) => (ConstBool [false])` -/
theorem r_generic_699_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_699 := by rule_auto

/-- `generic.rules:707`: `(Less8 (Const8 [math.MaxInt8 ]) _) => (ConstBool [false])` -/
theorem r_generic_707_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_707 := by rule_auto

/-- `generic.rules:729`: `(Less8 x (Const8 <t> [math.MinInt8 +1])) => (Eq8 x (Const8 <t> [math.MinInt8 ]))` -/
theorem r_generic_729_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_729 := by rule_auto

/-- `generic.rules:733`: `(Less8 (Const8 <t> [math.MaxInt8 -1]) x) => (Eq8 x (Const8 <t> [math.MaxInt8 ]))` -/
theorem r_generic_733_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_733 := by rule_auto

/-- `generic.rules:592`: `(Less8U (Const8 [c]) (Const8 [d])) => (ConstBool [ uint8(c) < uint8(d)])` -/
theorem r_generic_592_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_592 := by rule_auto

/-- `generic.rules:612`: `(Less8U x (Const8 <t> [1])) => (Eq8 (Const8 <t> [0]) x)` -/
theorem r_generic_612_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_612_4 := by rule_auto

/-- `generic.rules:716`: `(Less8U x (Const8 <t> [1])) => (Eq8 x (Const8 <t> [0]))` -/
theorem r_generic_716_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_716_4 := by rule_auto

/-- `generic.rules:717`: `(Less8U (Const8 <t> [-2]) x) => (Eq8 x (Const8 <t> [-1]))` -/
theorem r_generic_717_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_717_4 := by rule_auto

end GoFV.Proof.Rules
