import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values07

/-!
# Rule lemmas: `Neq` rules (part 4)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Neq` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:286`: `(Neq64 x x) => (ConstBool [false])` -/
theorem r_generic_286_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_286_3 := by rule_auto


/-- `generic.rules:298`: `(Neq64 (Const64 <t> [c]) o:(Add64 (Const64 [d]) x)) && o.Uses == 1 => (Neq64 (Const64 <t> [c-d]) x)` -/
theorem r_generic_298_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_298_3 := by rule_auto


/-- `generic.rules:301`: `(Neq64 (Const64 <t> [c]) o:(Sub64 x (Const64 [d]))) && o.Uses == 1 => (Neq64 (Const64 <t> [c+d]) x)` -/
theorem r_generic_301_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_301_3 := by rule_auto


/-- `generic.rules:304`: `(Neq64 (Const64 <t> [c]) o:(Sub64 (Const64 [d]) x)) && o.Uses == 1 => (Neq64 (Const64 <t> [d-c]) x)` -/
theorem r_generic_304_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_304_3 := by rule_auto


/-- `generic.rules:307`: `(Neq64 (Const64 <t> [c]) o:(Xor64 (Const64 [d]) x)) && o.Uses == 1 => (Neq64 (Const64 <t> [d^c]) x)` -/
theorem r_generic_307_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_307_3 := by rule_auto


/-- `generic.rules:310`: `(Neq64 (Const64 <t> [c]) o:(Com64 x)) && o.Uses == 1 => (Neq64 (Const64 <t> [^c]) x)` -/
theorem r_generic_310_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_310_3 := by rule_auto


/-- `generic.rules:313`: `(Neq64 (Const64 <t> [c]) o:(Neg64 x)) && o.Uses == 1 => (Neq64 (Const64 <t> [-c]) x)` -/
theorem r_generic_313_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_313_3 := by rule_auto


/-- `generic.rules:1179`: `(Neq64 s:(Sub64 x y) (Const64 [0])) && s.Uses == 1 => (Neq64 x y)` -/
theorem r_generic_1179_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1179_3 := by rule_auto


/-- `generic.rules:2401`: `(Neq64 (ZeroExt8to64 (CvtBoolToUint8 x)) (Const64 [0])) => x` -/
theorem r_generic_2401_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2401_3 := by rule_auto


/-- `generic.rules:2402`: `(Neq64 (ZeroExt8to64 (CvtBoolToUint8 x)) (Const64 [1])) => (Not x)` -/
theorem r_generic_2402_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2402_3 := by rule_auto

end GoFV.Proof.Rules
