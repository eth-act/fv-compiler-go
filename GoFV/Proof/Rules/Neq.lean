import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values07

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `Neq` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Neq` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:286`: `(Neq16 x x) => (ConstBool [false])` -/
theorem r_generic_286_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_286 := by rule_auto


/-- `generic.rules:298`: `(Neq16 (Const16 <t> [c]) o:(Add16 (Const16 [d]) x)) && o.Uses == 1 => (Neq16 (Const16 <t> [c-d]) x)` -/
theorem r_generic_298_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_298 := by rule_auto


/-- `generic.rules:301`: `(Neq16 (Const16 <t> [c]) o:(Sub16 x (Const16 [d]))) && o.Uses == 1 => (Neq16 (Const16 <t> [c+d]) x)` -/
theorem r_generic_301_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_301 := by rule_auto


/-- `generic.rules:304`: `(Neq16 (Const16 <t> [c]) o:(Sub16 (Const16 [d]) x)) && o.Uses == 1 => (Neq16 (Const16 <t> [d-c]) x)` -/
theorem r_generic_304_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_304 := by rule_auto


/-- `generic.rules:307`: `(Neq16 (Const16 <t> [c]) o:(Xor16 (Const16 [d]) x)) && o.Uses == 1 => (Neq16 (Const16 <t> [d^c]) x)` -/
theorem r_generic_307_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_307 := by rule_auto


/-- `generic.rules:310`: `(Neq16 (Const16 <t> [c]) o:(Com16 x)) && o.Uses == 1 => (Neq16 (Const16 <t> [^c]) x)` -/
theorem r_generic_310_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_310 := by rule_auto


/-- `generic.rules:313`: `(Neq16 (Const16 <t> [c]) o:(Neg16 x)) && o.Uses == 1 => (Neq16 (Const16 <t> [-c]) x)` -/
theorem r_generic_313_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_313 := by rule_auto


/-- `generic.rules:1179`: `(Neq16 s:(Sub16 x y) (Const16 [0])) && s.Uses == 1 => (Neq16 x y)` -/
theorem r_generic_1179_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1179 := by rule_auto


/-- `generic.rules:2401`: `(Neq16 (ZeroExt8to16 (CvtBoolToUint8 x)) (Const16 [0])) => x` -/
theorem r_generic_2401_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2401 := by rule_auto


/-- `generic.rules:2402`: `(Neq16 (ZeroExt8to16 (CvtBoolToUint8 x)) (Const16 [1])) => (Not x)` -/
theorem r_generic_2402_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2402 := by rule_auto


end GoFV.Proof.Rules
