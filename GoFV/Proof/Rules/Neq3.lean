import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values07

/-!
# Rule lemmas: `Neq` rules (part 3)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Neq` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:286`: `(Neq32 x x) => (ConstBool [false])` -/
theorem r_generic_286_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_286_2 := by rule_auto


/-- `generic.rules:298`: `(Neq32 (Const32 <t> [c]) o:(Add32 (Const32 [d]) x)) && o.Uses == 1 => (Neq32 (Const32 <t> [c-d]) x)` -/
theorem r_generic_298_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_298_2 := by rule_auto


/-- `generic.rules:301`: `(Neq32 (Const32 <t> [c]) o:(Sub32 x (Const32 [d]))) && o.Uses == 1 => (Neq32 (Const32 <t> [c+d]) x)` -/
theorem r_generic_301_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_301_2 := by rule_auto


/-- `generic.rules:304`: `(Neq32 (Const32 <t> [c]) o:(Sub32 (Const32 [d]) x)) && o.Uses == 1 => (Neq32 (Const32 <t> [d-c]) x)` -/
theorem r_generic_304_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_304_2 := by rule_auto


/-- `generic.rules:307`: `(Neq32 (Const32 <t> [c]) o:(Xor32 (Const32 [d]) x)) && o.Uses == 1 => (Neq32 (Const32 <t> [d^c]) x)` -/
theorem r_generic_307_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_307_2 := by rule_auto


/-- `generic.rules:310`: `(Neq32 (Const32 <t> [c]) o:(Com32 x)) && o.Uses == 1 => (Neq32 (Const32 <t> [^c]) x)` -/
theorem r_generic_310_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_310_2 := by rule_auto


/-- `generic.rules:313`: `(Neq32 (Const32 <t> [c]) o:(Neg32 x)) && o.Uses == 1 => (Neq32 (Const32 <t> [-c]) x)` -/
theorem r_generic_313_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_313_2 := by rule_auto


/-- `generic.rules:1179`: `(Neq32 s:(Sub32 x y) (Const32 [0])) && s.Uses == 1 => (Neq32 x y)` -/
theorem r_generic_1179_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1179_2 := by rule_auto


/-- `generic.rules:2401`: `(Neq32 (ZeroExt8to32 (CvtBoolToUint8 x)) (Const32 [0])) => x` -/
theorem r_generic_2401_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2401_2 := by rule_auto


/-- `generic.rules:2402`: `(Neq32 (ZeroExt8to32 (CvtBoolToUint8 x)) (Const32 [1])) => (Not x)` -/
theorem r_generic_2402_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2402_2 := by rule_auto


end GoFV.Proof.Rules
