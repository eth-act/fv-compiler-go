import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Divisible.Values00

/-!
# Rule lemmas: `Eq` rules (part 6)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Eq` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `divisible.rules:17`: `(Eq16 x (Mul16 <t> (Div16u x (Const16 [c])) (Const16 [c]))) && x.Op != OpConst64 && isPowerOfTwo(c) => (Eq16 (And16 <t> x (Const16 <t> [c-1])) (Const16 <t> [0]))` -/
theorem r_divisible_17_sound : Rule.Sound GoFV.Rules.Generated.Divisible.r_divisible_17 := by rule_auto

/-- `divisible.rules:20`: `(Eq16 x (Mul16 <t> (Div16 x (Const16 [c])) (Const16 [c]))) && x.Op != OpConst64 && isPowerOfTwo(c) => (Eq16 (And16 <t> x (Const16 <t> [c-1])) (Const16 <t> [0]))` -/
theorem r_divisible_20_sound : Rule.Sound GoFV.Rules.Generated.Divisible.r_divisible_20 := by rule_auto

/-- `divisible.rules:17`: `(Eq32 x (Mul32 <t> (Div32u x (Const32 [c])) (Const32 [c]))) && x.Op != OpConst64 && isPowerOfTwo(c) => (Eq32 (And32 <t> x (Const32 <t> [c-1])) (Const32 <t> [0]))` -/
theorem r_divisible_17_2_sound : Rule.Sound GoFV.Rules.Generated.Divisible.r_divisible_17_2 := by rule_auto

/-- `divisible.rules:20`: `(Eq32 x (Mul32 <t> (Div32 x (Const32 [c])) (Const32 [c]))) && x.Op != OpConst64 && isPowerOfTwo(c) => (Eq32 (And32 <t> x (Const32 <t> [c-1])) (Const32 <t> [0]))` -/
theorem r_divisible_20_2_sound : Rule.Sound GoFV.Rules.Generated.Divisible.r_divisible_20_2 := by rule_auto

/-- `divisible.rules:17`: `(Eq64 x (Mul64 <t> (Div64u x (Const64 [c])) (Const64 [c]))) && x.Op != OpConst64 && isPowerOfTwo(c) => (Eq64 (And64 <t> x (Const64 <t> [c-1])) (Const64 <t> [0]))` -/
theorem r_divisible_17_3_sound : Rule.Sound GoFV.Rules.Generated.Divisible.r_divisible_17_3 := by rule_auto

/-- `divisible.rules:20`: `(Eq64 x (Mul64 <t> (Div64 x (Const64 [c])) (Const64 [c]))) && x.Op != OpConst64 && isPowerOfTwo(c) => (Eq64 (And64 <t> x (Const64 <t> [c-1])) (Const64 <t> [0]))` -/
theorem r_divisible_20_3_sound : Rule.Sound GoFV.Rules.Generated.Divisible.r_divisible_20_3 := by rule_auto

/-- `divisible.rules:17`: `(Eq8 x (Mul8 <t> (Div8u x (Const8 [c])) (Const8 [c]))) && x.Op != OpConst64 && isPowerOfTwo(c) => (Eq8 (And8 <t> x (Const8 <t> [c-1])) (Const8 <t> [0]))` -/
theorem r_divisible_17_4_sound : Rule.Sound GoFV.Rules.Generated.Divisible.r_divisible_17_4 := by rule_auto

/-- `divisible.rules:20`: `(Eq8 x (Mul8 <t> (Div8 x (Const8 [c])) (Const8 [c]))) && x.Op != OpConst64 && isPowerOfTwo(c) => (Eq8 (And8 <t> x (Const8 <t> [c-1])) (Const8 <t> [0]))` -/
theorem r_divisible_20_4_sound : Rule.Sound GoFV.Rules.Generated.Divisible.r_divisible_20_4 := by rule_auto

end GoFV.Proof.Rules
