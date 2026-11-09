import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values03

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `Eq` rules (part 5)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Eq` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:280`: `(Eq64 x x) => (ConstBool [true])` -/
theorem r_generic_280_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_280_3 := by rule_auto


/-- `generic.rules:297`: `(Eq64 (Const64 <t> [c]) o:(Add64 (Const64 [d]) x)) && o.Uses == 1 => (Eq64 (Const64 <t> [c-d]) x)` -/
theorem r_generic_297_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_297_3 := by rule_auto


/-- `generic.rules:300`: `(Eq64 (Const64 <t> [c]) o:(Sub64 x (Const64 [d]))) && o.Uses == 1 => (Eq64 (Const64 <t> [c+d]) x)` -/
theorem r_generic_300_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_300_3 := by rule_auto


/-- `generic.rules:303`: `(Eq64 (Const64 <t> [c]) o:(Sub64 (Const64 [d]) x)) && o.Uses == 1 => (Eq64 (Const64 <t> [d-c]) x)` -/
theorem r_generic_303_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_303_3 := by rule_auto


/-- `generic.rules:306`: `(Eq64 (Const64 <t> [c]) o:(Xor64 (Const64 [d]) x)) && o.Uses == 1 => (Eq64 (Const64 <t> [d^c]) x)` -/
theorem r_generic_306_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_306_3 := by rule_auto


/-- `generic.rules:309`: `(Eq64 (Const64 <t> [c]) o:(Com64 x)) && o.Uses == 1 => (Eq64 (Const64 <t> [^c]) x)` -/
theorem r_generic_309_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_309_3 := by rule_auto


/-- `generic.rules:312`: `(Eq64 (Const64 <t> [c]) o:(Neg64 x)) && o.Uses == 1 => (Eq64 (Const64 <t> [-c]) x)` -/
theorem r_generic_312_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_312_3 := by rule_auto


/-- `generic.rules:1178`: `(Eq64 s:(Sub64 x y) (Const64 [0])) && s.Uses == 1 => (Eq64 x y)` -/
theorem r_generic_1178_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1178_3 := by rule_auto


/-- `generic.rules:2403`: `(Eq64 (ZeroExt8to64 (CvtBoolToUint8 x)) (Const64 [1])) => x` -/
theorem r_generic_2403_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2403_3 := by rule_auto


/-- `generic.rules:2404`: `(Eq64 (ZeroExt8to64 (CvtBoolToUint8 x)) (Const64 [0])) => (Not x)` -/
theorem r_generic_2404_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2404_3 := by rule_auto

end GoFV.Proof.Rules
