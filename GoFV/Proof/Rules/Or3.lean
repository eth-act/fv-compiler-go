import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values08
import GoFV.Rules.Generated.Generic.Values09

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `Or` rules (part 3)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Or` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:153`: `(Or16 (Const16 [c]) (Const16 [d])) => (Const16 [c|d])` -/
theorem r_generic_153_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_153 := by rule_auto

/-- `generic.rules:209`: `(Or16 <t> (Com16 x) (Com16 y)) => (Com16 (And16 <t> x y))` -/
theorem r_generic_209_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_209 := by rule_auto

/-- `generic.rules:1308`: `(Or16 (Const16 <t> [c]) (Or16 (Const16 <t> [d]) x)) => (Or16 (Const16 <t> [c|d]) x)` -/
theorem r_generic_1308_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1308 := by rule_auto

/-- `generic.rules:154`: `(Or32 (Const32 [c]) (Const32 [d])) => (Const32 [c|d])` -/
theorem r_generic_154_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_154 := by rule_auto

/-- `generic.rules:209`: `(Or32 <t> (Com32 x) (Com32 y)) => (Com32 (And32 <t> x y))` -/
theorem r_generic_209_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_209_2 := by rule_auto

/-- `generic.rules:1307`: `(Or32 (Const32 <t> [c]) (Or32 (Const32 <t> [d]) x)) => (Or32 (Const32 <t> [c|d]) x)` -/
theorem r_generic_1307_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1307 := by rule_auto

/-- `generic.rules:155`: `(Or64 (Const64 [c]) (Const64 [d])) => (Const64 [c|d])` -/
theorem r_generic_155_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_155 := by rule_auto

/-- `generic.rules:209`: `(Or64 <t> (Com64 x) (Com64 y)) => (Com64 (And64 <t> x y))` -/
theorem r_generic_209_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_209_3 := by rule_auto

/-- `generic.rules:1306`: `(Or64 (Const64 <t> [c]) (Or64 (Const64 <t> [d]) x)) => (Or64 (Const64 <t> [c|d]) x)` -/
theorem r_generic_1306_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1306 := by rule_auto

/-- `generic.rules:152`: `(Or8 (Const8 [c]) (Const8 [d])) => (Const8 [c|d])` -/
theorem r_generic_152_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_152 := by rule_auto

/-- `generic.rules:209`: `(Or8 <t> (Com8 x) (Com8 y)) => (Com8 (And8 <t> x y))` -/
theorem r_generic_209_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_209_4 := by rule_auto

/-- `generic.rules:1309`: `(Or8 (Const8 <t> [c]) (Or8 (Const8 <t> [d]) x)) => (Or8 (Const8 <t> [c|d]) x)` -/
theorem r_generic_1309_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1309 := by rule_auto

end GoFV.Proof.Rules
