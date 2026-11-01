import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values04

/-!
# Rule lemmas: `Leq` rules (part 3)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Leq` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:718`: `(Leq64 x c:(Const64 [math.MinInt64])) => (Eq64 x c)` -/
theorem r_generic_718_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_718 := by rule_auto

/-- `generic.rules:722`: `(Leq64 c:(Const64 [math.MaxInt64]) x) => (Eq64 x c)` -/
theorem r_generic_722_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_722 := by rule_auto

/-- `generic.rules:594`: `(Leq64U (Const64 [c]) (Const64 [d])) => (ConstBool [uint64(c) <= uint64(d)])` -/
theorem r_generic_594_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_594 := by rule_auto

/-- `generic.rules:613`: `(Leq64U (Const64 <t> [1]) x) => (Neq64 (Const64 <t> [0]) x)` -/
theorem r_generic_613_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_613_3 := by rule_auto

/-- `generic.rules:714`: `(Leq64U x c:(Const64 [0])) => (Eq64 x c)` -/
theorem r_generic_714_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_714_3 := by rule_auto

/-- `generic.rules:715`: `(Leq64U c:(Const64 [-1]) x) => (Eq64 x c)` -/
theorem r_generic_715_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_715_3 := by rule_auto

/-- `generic.rules:587`: `(Leq8 (Const8 [c]) (Const8 [d])) => (ConstBool [c <= d])` -/
theorem r_generic_587_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_587_4 := by rule_auto

/-- `generic.rules:599`: `(Leq8 (Const8 [0]) (And8 _ (Const8 [c]))) && c >= 0 => (ConstBool [true])` -/
theorem r_generic_599_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_599 := by rule_auto

/-- `generic.rules:604`: `(Leq8 (Const8 [0]) (Rsh8Ux64 _ (Const64 [c]))) && c > 0 => (ConstBool [true])` -/
theorem r_generic_604_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_604 := by rule_auto

/-- `generic.rules:618`: `(Leq8 (Const8 <t> [1]) x) => (Less8 (Const8 <t> [0]) x)` -/
theorem r_generic_618_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_618_4 := by rule_auto

/-- `generic.rules:703`: `(Leq8 (Const8 [math.MinInt8 ]) _) => (ConstBool [true])` -/
theorem r_generic_703_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_703 := by rule_auto

/-- `generic.rules:711`: `(Leq8 _ (Const8 [math.MaxInt8 ])) => (ConstBool [true])` -/
theorem r_generic_711_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_711 := by rule_auto

/-- `generic.rules:721`: `(Leq8 x c:(Const8 [math.MinInt8 ])) => (Eq8 x c)` -/
theorem r_generic_721_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_721 := by rule_auto

/-- `generic.rules:725`: `(Leq8 c:(Const8 [math.MaxInt8 ]) x) => (Eq8 x c)` -/
theorem r_generic_725_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_725 := by rule_auto

/-- `generic.rules:597`: `(Leq8U (Const8 [c]) (Const8 [d])) => (ConstBool [ uint8(c) <= uint8(d)])` -/
theorem r_generic_597_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_597 := by rule_auto

/-- `generic.rules:613`: `(Leq8U (Const8 <t> [1]) x) => (Neq8 (Const8 <t> [0]) x)` -/
theorem r_generic_613_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_613_4 := by rule_auto

/-- `generic.rules:714`: `(Leq8U x c:(Const8 [0])) => (Eq8 x c)` -/
theorem r_generic_714_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_714_4 := by rule_auto

/-- `generic.rules:715`: `(Leq8U c:(Const8 [-1]) x) => (Eq8 x c)` -/
theorem r_generic_715_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_715_4 := by rule_auto

end GoFV.Proof.Rules
