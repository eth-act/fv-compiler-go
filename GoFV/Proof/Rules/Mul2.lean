import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values07

/-!
# Rule lemmas: `Mul` rules (part 2)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Mul` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:199`: `(Mul8 (Const8 <t> [c]) (Neg8 x)) => (Mul8 x (Const8 <t> [-c]))` -/
theorem r_generic_199_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_199_4 := by rule_auto

/-- `generic.rules:201`: `(Mul8 (Neg8 x) (Neg8 y)) => (Mul8 x y)` -/
theorem r_generic_201_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_201_4 := by rule_auto

/-- `generic.rules:415`: `(Mul8 (Const8 <t> [c]) (Add8 <t> (Const8 <t> [d]) x)) && !isPowerOfTwo(c) => (Add8 (Const8 <t> [c*d]) (Mul8 <t> (Const8 <t> [c]) x))` -/
theorem r_generic_415_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_415 := by rule_auto

/-- `generic.rules:648`: `(Mul8 (Const8 [0]) _) => (Const8 [0])` -/
theorem r_generic_648_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_648_4 := by rule_auto

/-- `generic.rules:1273`: `(Mul8 (Mul8 i:(Const8 <t>) z) x) && (z.Op != OpConst8 && x.Op != OpConst8) => (Mul8 i (Mul8 <t> x z))` -/
theorem r_generic_1273_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1273 := by rule_auto

/-- `generic.rules:1321`: `(Mul8 (Const8 <t> [c]) (Mul8 (Const8 <t> [d]) x)) => (Mul8 (Const8 <t> [c*d]) x)` -/
theorem r_generic_1321_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1321 := by rule_auto

end GoFV.Proof.Rules
