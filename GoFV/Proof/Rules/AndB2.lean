import GoFV.Proof.Rules.TacticRange
import GoFV.Rules.Generated.Generic.Values01

/-!
# Rule lemmas: `AndB` rules (part 2)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the P1/P2 rules whose top op is in the
`AndB` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:327`: `(AndB (Less64 (Const64 [c]) x) (Less64 x (Const64 [d]))) && d >= c+1 && c+1 > c => (Less64U (Sub64 <x.Type> x (Const64 <x.Type> [c+1])) (Const64 <x.Type> [d-c-1]))` -/
theorem r_generic_327_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_327 := by rule_range

/-- `generic.rules:327`: `(AndB (Less64 (Const64 [c]) x) (Leq64 x (Const64 [d]))) && d >= c+1 && c+1 > c => (Leq64U (Sub64 <x.Type> x (Const64 <x.Type> [c+1])) (Const64 <x.Type> [d-c-1]))` -/
theorem r_generic_327_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_327_2 := by rule_range

/-- `generic.rules:328`: `(AndB (Less32 (Const32 [c]) x) (Less32 x (Const32 [d]))) && d >= c+1 && c+1 > c => (Less32U (Sub32 <x.Type> x (Const32 <x.Type> [c+1])) (Const32 <x.Type> [d-c-1]))` -/
theorem r_generic_328_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_328 := by rule_range

/-- `generic.rules:328`: `(AndB (Less32 (Const32 [c]) x) (Leq32 x (Const32 [d]))) && d >= c+1 && c+1 > c => (Leq32U (Sub32 <x.Type> x (Const32 <x.Type> [c+1])) (Const32 <x.Type> [d-c-1]))` -/
theorem r_generic_328_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_328_2 := by rule_range

/-- `generic.rules:329`: `(AndB (Less16 (Const16 [c]) x) (Less16 x (Const16 [d]))) && d >= c+1 && c+1 > c => (Less16U (Sub16 <x.Type> x (Const16 <x.Type> [c+1])) (Const16 <x.Type> [d-c-1]))` -/
theorem r_generic_329_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_329 := by rule_range

/-- `generic.rules:329`: `(AndB (Less16 (Const16 [c]) x) (Leq16 x (Const16 [d]))) && d >= c+1 && c+1 > c => (Leq16U (Sub16 <x.Type> x (Const16 <x.Type> [c+1])) (Const16 <x.Type> [d-c-1]))` -/
theorem r_generic_329_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_329_2 := by rule_range

/-- `generic.rules:330`: `(AndB (Less8 (Const8 [c]) x) (Less8 x (Const8 [d]))) && d >= c+1 && c+1 > c => (Less8U (Sub8 <x.Type> x (Const8 <x.Type> [c+1])) (Const8 <x.Type> [d-c-1]))` -/
theorem r_generic_330_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_330 := by rule_range

/-- `generic.rules:330`: `(AndB (Less8 (Const8 [c]) x) (Leq8 x (Const8 [d]))) && d >= c+1 && c+1 > c => (Leq8U (Sub8 <x.Type> x (Const8 <x.Type> [c+1])) (Const8 <x.Type> [d-c-1]))` -/
theorem r_generic_330_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_330_2 := by rule_range

end GoFV.Proof.Rules
