import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values00
import GoFV.Rules.Generated.Generic.Values01

/-!
# Rule lemmas: `And` rules (part 2)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`And` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:148`: `(And16 (Const16 [c]) (Const16 [d])) => (Const16 [c&d])` -/
theorem r_generic_148_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_148 := by rule_auto

/-- `generic.rules:208`: `(And16 <t> (Com16 x) (Com16 y)) => (Com16 (Or16 <t> x y))` -/
theorem r_generic_208_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_208 := by rule_auto

/-- `generic.rules:1302`: `(And16 (Const16 <t> [c]) (And16 (Const16 <t> [d]) x)) => (And16 (Const16 <t> [c&d]) x)` -/
theorem r_generic_1302_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1302 := by rule_auto

/-- `generic.rules:149`: `(And32 (Const32 [c]) (Const32 [d])) => (Const32 [c&d])` -/
theorem r_generic_149_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_149 := by rule_auto

/-- `generic.rules:208`: `(And32 <t> (Com32 x) (Com32 y)) => (Com32 (Or32 <t> x y))` -/
theorem r_generic_208_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_208_2 := by rule_auto

/-- `generic.rules:1301`: `(And32 (Const32 <t> [c]) (And32 (Const32 <t> [d]) x)) => (And32 (Const32 <t> [c&d]) x)` -/
theorem r_generic_1301_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1301 := by rule_auto

/-- `generic.rules:150`: `(And64 (Const64 [c]) (Const64 [d])) => (Const64 [c&d])` -/
theorem r_generic_150_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_150 := by rule_auto

/-- `generic.rules:208`: `(And64 <t> (Com64 x) (Com64 y)) => (Com64 (Or64 <t> x y))` -/
theorem r_generic_208_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_208_3 := by rule_auto

/-- `generic.rules:1300`: `(And64 (Const64 <t> [c]) (And64 (Const64 <t> [d]) x)) => (And64 (Const64 <t> [c&d]) x)` -/
theorem r_generic_1300_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1300 := by rule_auto

/-- `generic.rules:147`: `(And8 (Const8 [c]) (Const8 [d])) => (Const8 [c&d])` -/
theorem r_generic_147_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_147 := by rule_auto

/-- `generic.rules:208`: `(And8 <t> (Com8 x) (Com8 y)) => (Com8 (Or8 <t> x y))` -/
theorem r_generic_208_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_208_4 := by rule_auto

/-- `generic.rules:1303`: `(And8 (Const8 <t> [c]) (And8 (Const8 <t> [d]) x)) => (And8 (Const8 <t> [c&d]) x)` -/
theorem r_generic_1303_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1303 := by rule_auto

end GoFV.Proof.Rules
