import GoFV.Proof.Rules.TacticRange
import GoFV.Rules.Generated.Generic.Values09

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `OrB` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the P1/P2 rules whose top op is in the
`OrB` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:345`: `(OrB (Less64 (Const64 [c]) x) (Less64 x (Const64 [d]))) && c >= d => (Less64U (Const64 <x.Type> [c-d]) (Sub64 <x.Type> x (Const64 <x.Type> [d])))` -/
theorem r_generic_345_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_345 := by rule_range

/-- `generic.rules:345`: `(OrB (Leq64 (Const64 [c]) x) (Less64 x (Const64 [d]))) && c >= d => (Leq64U (Const64 <x.Type> [c-d]) (Sub64 <x.Type> x (Const64 <x.Type> [d])))` -/
theorem r_generic_345_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_345_2 := by rule_range

/-- `generic.rules:346`: `(OrB (Less32 (Const32 [c]) x) (Less32 x (Const32 [d]))) && c >= d => (Less32U (Const32 <x.Type> [c-d]) (Sub32 <x.Type> x (Const32 <x.Type> [d])))` -/
theorem r_generic_346_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_346 := by rule_range

/-- `generic.rules:346`: `(OrB (Leq32 (Const32 [c]) x) (Less32 x (Const32 [d]))) && c >= d => (Leq32U (Const32 <x.Type> [c-d]) (Sub32 <x.Type> x (Const32 <x.Type> [d])))` -/
theorem r_generic_346_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_346_2 := by rule_range

/-- `generic.rules:347`: `(OrB (Less16 (Const16 [c]) x) (Less16 x (Const16 [d]))) && c >= d => (Less16U (Const16 <x.Type> [c-d]) (Sub16 <x.Type> x (Const16 <x.Type> [d])))` -/
theorem r_generic_347_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_347 := by rule_range

/-- `generic.rules:347`: `(OrB (Leq16 (Const16 [c]) x) (Less16 x (Const16 [d]))) && c >= d => (Leq16U (Const16 <x.Type> [c-d]) (Sub16 <x.Type> x (Const16 <x.Type> [d])))` -/
theorem r_generic_347_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_347_2 := by rule_range

/-- `generic.rules:348`: `(OrB (Less8 (Const8 [c]) x) (Less8 x (Const8 [d]))) && c >= d => (Less8U (Const8 <x.Type> [c-d]) (Sub8 <x.Type> x (Const8 <x.Type> [d])))` -/
theorem r_generic_348_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_348 := by rule_range

/-- `generic.rules:348`: `(OrB (Leq8 (Const8 [c]) x) (Less8 x (Const8 [d]))) && c >= d => (Leq8U (Const8 <x.Type> [c-d]) (Sub8 <x.Type> x (Const8 <x.Type> [d])))` -/
theorem r_generic_348_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_348_2 := by rule_range

end GoFV.Proof.Rules
