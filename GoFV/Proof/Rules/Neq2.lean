import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values07

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `Neq` rules (part 2)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Neq` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:286`: `(Neq8 x x) => (ConstBool [false])` -/
theorem r_generic_286_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_286_4 := by rule_auto

/-- `generic.rules:298`: `(Neq8 (Const8 <t> [c]) o:(Add8 (Const8 [d]) x)) && o.Uses == 1 => (Neq8 (Const8 <t> [c-d]) x)` -/
theorem r_generic_298_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_298_4 := by rule_auto

/-- `generic.rules:301`: `(Neq8 (Const8 <t> [c]) o:(Sub8 x (Const8 [d]))) && o.Uses == 1 => (Neq8 (Const8 <t> [c+d]) x)` -/
theorem r_generic_301_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_301_4 := by rule_auto

/-- `generic.rules:304`: `(Neq8 (Const8 <t> [c]) o:(Sub8 (Const8 [d]) x)) && o.Uses == 1 => (Neq8 (Const8 <t> [d-c]) x)` -/
theorem r_generic_304_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_304_4 := by rule_auto

/-- `generic.rules:307`: `(Neq8 (Const8 <t> [c]) o:(Xor8 (Const8 [d]) x)) && o.Uses == 1 => (Neq8 (Const8 <t> [d^c]) x)` -/
theorem r_generic_307_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_307_4 := by rule_auto

/-- `generic.rules:310`: `(Neq8 (Const8 <t> [c]) o:(Com8 x)) && o.Uses == 1 => (Neq8 (Const8 <t> [^c]) x)` -/
theorem r_generic_310_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_310_4 := by rule_auto

/-- `generic.rules:313`: `(Neq8 (Const8 <t> [c]) o:(Neg8 x)) && o.Uses == 1 => (Neq8 (Const8 <t> [-c]) x)` -/
theorem r_generic_313_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_313_4 := by rule_auto

/-- `generic.rules:1179`: `(Neq8 s:(Sub8 x y) (Const8 [0])) && s.Uses == 1 => (Neq8 x y)` -/
theorem r_generic_1179_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1179_4 := by rule_auto

/-- `generic.rules:2397`: `(Neq8 (CvtBoolToUint8 x) (Const8 [0])) => x` -/
theorem r_generic_2397_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2397 := by rule_auto

/-- `generic.rules:2398`: `(Neq8 (CvtBoolToUint8 x) (Const8 [1])) => (Not x)` -/
theorem r_generic_2398_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2398 := by rule_auto

end GoFV.Proof.Rules
