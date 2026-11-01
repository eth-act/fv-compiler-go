import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values03

/-!
# Rule lemmas: `Eq` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Eq` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:280`: `(Eq16 x x) => (ConstBool [true])` -/
theorem r_generic_280_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_280 := by rule_auto


/-- `generic.rules:297`: `(Eq16 (Const16 <t> [c]) o:(Add16 (Const16 [d]) x)) && o.Uses == 1 => (Eq16 (Const16 <t> [c-d]) x)` -/
theorem r_generic_297_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_297 := by rule_auto


/-- `generic.rules:300`: `(Eq16 (Const16 <t> [c]) o:(Sub16 x (Const16 [d]))) && o.Uses == 1 => (Eq16 (Const16 <t> [c+d]) x)` -/
theorem r_generic_300_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_300 := by rule_auto


/-- `generic.rules:303`: `(Eq16 (Const16 <t> [c]) o:(Sub16 (Const16 [d]) x)) && o.Uses == 1 => (Eq16 (Const16 <t> [d-c]) x)` -/
theorem r_generic_303_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_303 := by rule_auto


/-- `generic.rules:306`: `(Eq16 (Const16 <t> [c]) o:(Xor16 (Const16 [d]) x)) && o.Uses == 1 => (Eq16 (Const16 <t> [d^c]) x)` -/
theorem r_generic_306_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_306 := by rule_auto


/-- `generic.rules:309`: `(Eq16 (Const16 <t> [c]) o:(Com16 x)) && o.Uses == 1 => (Eq16 (Const16 <t> [^c]) x)` -/
theorem r_generic_309_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_309 := by rule_auto


/-- `generic.rules:312`: `(Eq16 (Const16 <t> [c]) o:(Neg16 x)) && o.Uses == 1 => (Eq16 (Const16 <t> [-c]) x)` -/
theorem r_generic_312_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_312 := by rule_auto


/-- `generic.rules:1178`: `(Eq16 s:(Sub16 x y) (Const16 [0])) && s.Uses == 1 => (Eq16 x y)` -/
theorem r_generic_1178_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1178 := by rule_auto


/-- `generic.rules:2403`: `(Eq16 (ZeroExt8to16 (CvtBoolToUint8 x)) (Const16 [1])) => x` -/
theorem r_generic_2403_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2403 := by rule_auto


/-- `generic.rules:2404`: `(Eq16 (ZeroExt8to16 (CvtBoolToUint8 x)) (Const16 [0])) => (Not x)` -/
theorem r_generic_2404_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2404 := by rule_auto


end GoFV.Proof.Rules
