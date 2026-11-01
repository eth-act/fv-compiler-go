import GoFV.Proof.Rules.TacticRange
import GoFV.Rules.Generated.Generic.Values01

/-!
# Rule lemmas: `AndB` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the P1/P2 rules whose top op is in the
`AndB` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:321`: `(AndB (Leq64 (Const64 [c]) x) (Less64 x (Const64 [d]))) && d >= c => (Less64U (Sub64 <x.Type> x (Const64 <x.Type> [c])) (Const64 <x.Type> [d-c]))` -/
theorem r_generic_321_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_321 := by rule_range

/-- `generic.rules:321`: `(AndB (Leq64 (Const64 [c]) x) (Leq64 x (Const64 [d]))) && d >= c => (Leq64U (Sub64 <x.Type> x (Const64 <x.Type> [c])) (Const64 <x.Type> [d-c]))` -/
theorem r_generic_321_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_321_2 := by rule_range

/-- `generic.rules:322`: `(AndB (Leq32 (Const32 [c]) x) (Less32 x (Const32 [d]))) && d >= c => (Less32U (Sub32 <x.Type> x (Const32 <x.Type> [c])) (Const32 <x.Type> [d-c]))` -/
theorem r_generic_322_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_322 := by rule_range

/-- `generic.rules:322`: `(AndB (Leq32 (Const32 [c]) x) (Leq32 x (Const32 [d]))) && d >= c => (Leq32U (Sub32 <x.Type> x (Const32 <x.Type> [c])) (Const32 <x.Type> [d-c]))` -/
theorem r_generic_322_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_322_2 := by rule_range

/-- `generic.rules:323`: `(AndB (Leq16 (Const16 [c]) x) (Less16 x (Const16 [d]))) && d >= c => (Less16U (Sub16 <x.Type> x (Const16 <x.Type> [c])) (Const16 <x.Type> [d-c]))` -/
theorem r_generic_323_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_323 := by rule_range

/-- `generic.rules:323`: `(AndB (Leq16 (Const16 [c]) x) (Leq16 x (Const16 [d]))) && d >= c => (Leq16U (Sub16 <x.Type> x (Const16 <x.Type> [c])) (Const16 <x.Type> [d-c]))` -/
theorem r_generic_323_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_323_2 := by rule_range

/-- `generic.rules:324`: `(AndB (Leq8 (Const8 [c]) x) (Less8 x (Const8 [d]))) && d >= c => (Less8U (Sub8 <x.Type> x (Const8 <x.Type> [c])) (Const8 <x.Type> [d-c]))` -/
theorem r_generic_324_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_324 := by rule_range

/-- `generic.rules:324`: `(AndB (Leq8 (Const8 [c]) x) (Leq8 x (Const8 [d]))) && d >= c => (Leq8U (Sub8 <x.Type> x (Const8 <x.Type> [c])) (Const8 <x.Type> [d-c]))` -/
theorem r_generic_324_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_324_2 := by rule_range

end GoFV.Proof.Rules
