import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values07

/-!
# Rule lemmas: `Neg` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Neg` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:114`: `(Neg16 (Const16 [c])) => (Const16 [-c])` -/
theorem r_generic_114_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_114 := by rule_auto

/-- `generic.rules:204`: `(Neg16 (Mul16 x (Const16 <t> [c]))) => (Mul16 x (Const16 <t> [-c]))` -/
theorem r_generic_204_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_204 := by rule_auto

/-- `generic.rules:205`: `(Neg16 (Mul16 x (Neg16 y))) => (Mul16 x y)` -/
theorem r_generic_205_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_205 := by rule_auto

/-- `generic.rules:654`: `(Neg16 (Sub16 x y)) => (Sub16 y x)` -/
theorem r_generic_654_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_654 := by rule_auto

/-- `generic.rules:682`: `(Neg16 (Neg16 x)) => x` -/
theorem r_generic_682_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_682 := by rule_auto

/-- `generic.rules:685`: `(Neg16 <t> (Com16 x)) => (Add16 (Const16 <t> [1]) x)` -/
theorem r_generic_685_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_685 := by rule_auto

/-- `generic.rules:115`: `(Neg32 (Const32 [c])) => (Const32 [-c])` -/
theorem r_generic_115_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_115 := by rule_auto

/-- `generic.rules:204`: `(Neg32 (Mul32 x (Const32 <t> [c]))) => (Mul32 x (Const32 <t> [-c]))` -/
theorem r_generic_204_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_204_2 := by rule_auto

/-- `generic.rules:205`: `(Neg32 (Mul32 x (Neg32 y))) => (Mul32 x y)` -/
theorem r_generic_205_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_205_2 := by rule_auto

/-- `generic.rules:654`: `(Neg32 (Sub32 x y)) => (Sub32 y x)` -/
theorem r_generic_654_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_654_2 := by rule_auto

/-- `generic.rules:682`: `(Neg32 (Neg32 x)) => x` -/
theorem r_generic_682_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_682_2 := by rule_auto

/-- `generic.rules:685`: `(Neg32 <t> (Com32 x)) => (Add32 (Const32 <t> [1]) x)` -/
theorem r_generic_685_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_685_2 := by rule_auto

/-- `generic.rules:116`: `(Neg64 (Const64 [c])) => (Const64 [-c])` -/
theorem r_generic_116_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_116 := by rule_auto

/-- `generic.rules:204`: `(Neg64 (Mul64 x (Const64 <t> [c]))) => (Mul64 x (Const64 <t> [-c]))` -/
theorem r_generic_204_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_204_3 := by rule_auto

/-- `generic.rules:205`: `(Neg64 (Mul64 x (Neg64 y))) => (Mul64 x y)` -/
theorem r_generic_205_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_205_3 := by rule_auto

/-- `generic.rules:654`: `(Neg64 (Sub64 x y)) => (Sub64 y x)` -/
theorem r_generic_654_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_654_3 := by rule_auto

/-- `generic.rules:682`: `(Neg64 (Neg64 x)) => x` -/
theorem r_generic_682_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_682_3 := by rule_auto

/-- `generic.rules:685`: `(Neg64 <t> (Com64 x)) => (Add64 (Const64 <t> [1]) x)` -/
theorem r_generic_685_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_685_3 := by rule_auto

/-- `generic.rules:113`: `(Neg8 (Const8 [c])) => (Const8 [-c])` -/
theorem r_generic_113_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_113 := by rule_auto

/-- `generic.rules:204`: `(Neg8 (Mul8 x (Const8 <t> [c]))) => (Mul8 x (Const8 <t> [-c]))` -/
theorem r_generic_204_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_204_4 := by rule_auto

/-- `generic.rules:205`: `(Neg8 (Mul8 x (Neg8 y))) => (Mul8 x y)` -/
theorem r_generic_205_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_205_4 := by rule_auto

/-- `generic.rules:654`: `(Neg8 (Sub8 x y)) => (Sub8 y x)` -/
theorem r_generic_654_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_654_4 := by rule_auto

/-- `generic.rules:682`: `(Neg8 (Neg8 x)) => x` -/
theorem r_generic_682_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_682_4 := by rule_auto

/-- `generic.rules:685`: `(Neg8 <t> (Com8 x)) => (Add8 (Const8 <t> [1]) x)` -/
theorem r_generic_685_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_685_4 := by rule_auto

end GoFV.Proof.Rules
