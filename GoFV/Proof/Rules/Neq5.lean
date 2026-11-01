import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Divisible.Values00

/-!
# Rule lemmas: `Neq` rules (part 5)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Neq` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `divisible.rules:23`: `(Neq16 x (Mul16 <t> (Div16u x (Const16 [c])) (Const16 [c]))) && x.Op != OpConst64 && isPowerOfTwo(c) => (Neq16 (And16 <t> x (Const16 <t> [c-1])) (Const16 <t> [0]))` -/
theorem r_divisible_23_sound : Rule.Sound GoFV.Rules.Generated.Divisible.r_divisible_23 := by rule_auto

/-- `divisible.rules:26`: `(Neq16 x (Mul16 <t> (Div16 x (Const16 [c])) (Const16 [c]))) && x.Op != OpConst64 && isPowerOfTwo(c) => (Neq16 (And16 <t> x (Const16 <t> [c-1])) (Const16 <t> [0]))` -/
theorem r_divisible_26_sound : Rule.Sound GoFV.Rules.Generated.Divisible.r_divisible_26 := by rule_auto

/-- `divisible.rules:23`: `(Neq32 x (Mul32 <t> (Div32u x (Const32 [c])) (Const32 [c]))) && x.Op != OpConst64 && isPowerOfTwo(c) => (Neq32 (And32 <t> x (Const32 <t> [c-1])) (Const32 <t> [0]))` -/
theorem r_divisible_23_2_sound : Rule.Sound GoFV.Rules.Generated.Divisible.r_divisible_23_2 := by rule_auto

/-- `divisible.rules:26`: `(Neq32 x (Mul32 <t> (Div32 x (Const32 [c])) (Const32 [c]))) && x.Op != OpConst64 && isPowerOfTwo(c) => (Neq32 (And32 <t> x (Const32 <t> [c-1])) (Const32 <t> [0]))` -/
theorem r_divisible_26_2_sound : Rule.Sound GoFV.Rules.Generated.Divisible.r_divisible_26_2 := by rule_auto

/-- `divisible.rules:23`: `(Neq64 x (Mul64 <t> (Div64u x (Const64 [c])) (Const64 [c]))) && x.Op != OpConst64 && isPowerOfTwo(c) => (Neq64 (And64 <t> x (Const64 <t> [c-1])) (Const64 <t> [0]))` -/
theorem r_divisible_23_3_sound : Rule.Sound GoFV.Rules.Generated.Divisible.r_divisible_23_3 := by rule_auto

/-- `divisible.rules:26`: `(Neq64 x (Mul64 <t> (Div64 x (Const64 [c])) (Const64 [c]))) && x.Op != OpConst64 && isPowerOfTwo(c) => (Neq64 (And64 <t> x (Const64 <t> [c-1])) (Const64 <t> [0]))` -/
theorem r_divisible_26_3_sound : Rule.Sound GoFV.Rules.Generated.Divisible.r_divisible_26_3 := by rule_auto

/-- `divisible.rules:23`: `(Neq8 x (Mul8 <t> (Div8u x (Const8 [c])) (Const8 [c]))) && x.Op != OpConst64 && isPowerOfTwo(c) => (Neq8 (And8 <t> x (Const8 <t> [c-1])) (Const8 <t> [0]))` -/
theorem r_divisible_23_4_sound : Rule.Sound GoFV.Rules.Generated.Divisible.r_divisible_23_4 := by rule_auto

/-- `divisible.rules:26`: `(Neq8 x (Mul8 <t> (Div8 x (Const8 [c])) (Const8 [c]))) && x.Op != OpConst64 && isPowerOfTwo(c) => (Neq8 (And8 <t> x (Const8 <t> [c-1])) (Const8 <t> [0]))` -/
theorem r_divisible_26_4_sound : Rule.Sound GoFV.Rules.Generated.Divisible.r_divisible_26_4 := by rule_auto

end GoFV.Proof.Rules
