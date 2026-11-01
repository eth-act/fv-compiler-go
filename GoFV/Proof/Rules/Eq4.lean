import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values03

/-!
# Rule lemmas: `Eq` rules (part 4)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Eq` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:280`: `(Eq32 x x) => (ConstBool [true])` -/
theorem r_generic_280_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_280_2 := by rule_auto


/-- `generic.rules:297`: `(Eq32 (Const32 <t> [c]) o:(Add32 (Const32 [d]) x)) && o.Uses == 1 => (Eq32 (Const32 <t> [c-d]) x)` -/
theorem r_generic_297_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_297_2 := by rule_auto


/-- `generic.rules:300`: `(Eq32 (Const32 <t> [c]) o:(Sub32 x (Const32 [d]))) && o.Uses == 1 => (Eq32 (Const32 <t> [c+d]) x)` -/
theorem r_generic_300_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_300_2 := by rule_auto


/-- `generic.rules:303`: `(Eq32 (Const32 <t> [c]) o:(Sub32 (Const32 [d]) x)) && o.Uses == 1 => (Eq32 (Const32 <t> [d-c]) x)` -/
theorem r_generic_303_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_303_2 := by rule_auto


/-- `generic.rules:306`: `(Eq32 (Const32 <t> [c]) o:(Xor32 (Const32 [d]) x)) && o.Uses == 1 => (Eq32 (Const32 <t> [d^c]) x)` -/
theorem r_generic_306_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_306_2 := by rule_auto


/-- `generic.rules:309`: `(Eq32 (Const32 <t> [c]) o:(Com32 x)) && o.Uses == 1 => (Eq32 (Const32 <t> [^c]) x)` -/
theorem r_generic_309_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_309_2 := by rule_auto


/-- `generic.rules:312`: `(Eq32 (Const32 <t> [c]) o:(Neg32 x)) && o.Uses == 1 => (Eq32 (Const32 <t> [-c]) x)` -/
theorem r_generic_312_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_312_2 := by rule_auto


/-- `generic.rules:1178`: `(Eq32 s:(Sub32 x y) (Const32 [0])) && s.Uses == 1 => (Eq32 x y)` -/
theorem r_generic_1178_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1178_2 := by rule_auto


/-- `generic.rules:2403`: `(Eq32 (ZeroExt8to32 (CvtBoolToUint8 x)) (Const32 [1])) => x` -/
theorem r_generic_2403_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2403_2 := by rule_auto


/-- `generic.rules:2404`: `(Eq32 (ZeroExt8to32 (CvtBoolToUint8 x)) (Const32 [0])) => (Not x)` -/
theorem r_generic_2404_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2404_2 := by rule_auto


end GoFV.Proof.Rules
