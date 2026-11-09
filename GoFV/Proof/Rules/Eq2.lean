import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values03

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `Eq` rules (part 2)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Eq` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:280`: `(Eq8 x x) => (ConstBool [true])` -/
theorem r_generic_280_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_280_4 := by rule_auto

/-- `generic.rules:297`: `(Eq8 (Const8 <t> [c]) o:(Add8 (Const8 [d]) x)) && o.Uses == 1 => (Eq8 (Const8 <t> [c-d]) x)` -/
theorem r_generic_297_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_297_4 := by rule_auto

/-- `generic.rules:300`: `(Eq8 (Const8 <t> [c]) o:(Sub8 x (Const8 [d]))) && o.Uses == 1 => (Eq8 (Const8 <t> [c+d]) x)` -/
theorem r_generic_300_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_300_4 := by rule_auto

/-- `generic.rules:303`: `(Eq8 (Const8 <t> [c]) o:(Sub8 (Const8 [d]) x)) && o.Uses == 1 => (Eq8 (Const8 <t> [d-c]) x)` -/
theorem r_generic_303_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_303_4 := by rule_auto

/-- `generic.rules:306`: `(Eq8 (Const8 <t> [c]) o:(Xor8 (Const8 [d]) x)) && o.Uses == 1 => (Eq8 (Const8 <t> [d^c]) x)` -/
theorem r_generic_306_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_306_4 := by rule_auto

/-- `generic.rules:309`: `(Eq8 (Const8 <t> [c]) o:(Com8 x)) && o.Uses == 1 => (Eq8 (Const8 <t> [^c]) x)` -/
theorem r_generic_309_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_309_4 := by rule_auto

/-- `generic.rules:312`: `(Eq8 (Const8 <t> [c]) o:(Neg8 x)) && o.Uses == 1 => (Eq8 (Const8 <t> [-c]) x)` -/
theorem r_generic_312_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_312_4 := by rule_auto

/-- `generic.rules:1178`: `(Eq8 s:(Sub8 x y) (Const8 [0])) && s.Uses == 1 => (Eq8 x y)` -/
theorem r_generic_1178_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1178_4 := by rule_auto

/-- `generic.rules:2399`: `(Eq8 (CvtBoolToUint8 x) (Const8 [1])) => x` -/
theorem r_generic_2399_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2399 := by rule_auto

/-- `generic.rules:2400`: `(Eq8 (CvtBoolToUint8 x) (Const8 [0])) => (Not x)` -/
theorem r_generic_2400_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2400 := by rule_auto

end GoFV.Proof.Rules
