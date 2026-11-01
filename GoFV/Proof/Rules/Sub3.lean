import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values13

/-!
# Rule lemmas: `Sub` rules (part 3)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Sub` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:776`: `(Sub8 (Sub8 x y) x) => (Neg8 y)` -/
theorem r_generic_776_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_776_4 := by rule_auto

/-- `generic.rules:777`: `(Sub8 x (Add8 x y)) => (Neg8 y)` -/
theorem r_generic_777_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_777_4 := by rule_auto

/-- `generic.rules:1231`: `(Sub8 x (Sub8 i:(Const8 <t>) z)) && (z.Op != OpConst8 && x.Op != OpConst8) => (Sub8 (Add8 <t> x z) i)` -/
theorem r_generic_1231_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1231 := by rule_auto

/-- `generic.rules:1237`: `(Sub8 x (Add8 z i:(Const8 <t>))) && (z.Op != OpConst8 && x.Op != OpConst8) => (Sub8 (Sub8 <t> x z) i)` -/
theorem r_generic_1237_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1237 := by rule_auto

/-- `generic.rules:1243`: `(Sub8 (Sub8 i:(Const8 <t>) z) x) && (z.Op != OpConst8 && x.Op != OpConst8) => (Sub8 i (Add8 <t> z x))` -/
theorem r_generic_1243_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1243 := by rule_auto

/-- `generic.rules:1249`: `(Sub8 (Add8 z i:(Const8 <t>)) x) && (z.Op != OpConst8 && x.Op != OpConst8) => (Add8 i (Sub8 <t> z x))` -/
theorem r_generic_1249_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1249 := by rule_auto

/-- `generic.rules:1291`: `(Sub8 (Const8 <t> [c]) (Sub8 (Const8 <t> [d]) x)) => (Add8 (Const8 <t> [c-d]) x)` -/
theorem r_generic_1291_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1291 := by rule_auto

/-- `generic.rules:1297`: `(Sub8 (Const8 <t> [c]) (Add8 (Const8 <t> [d]) x)) => (Sub8 (Const8 <t> [c-d]) x)` -/
theorem r_generic_1297_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1297 := by rule_auto

end GoFV.Proof.Rules
