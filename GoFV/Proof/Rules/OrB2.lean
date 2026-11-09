import GoFV.Proof.Rules.TacticRange
import GoFV.Rules.Generated.Generic.Values09

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `OrB` rules (part 2)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the P1/P2 rules whose top op is in the
`OrB` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:351`: `(OrB (Less64 (Const64 [c]) x) (Leq64 x (Const64 [d]))) && c >= d+1 && d+1 > d => (Less64U (Const64 <x.Type> [c-d-1]) (Sub64 <x.Type> x (Const64 <x.Type> [d+1])))` -/
theorem r_generic_351_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_351 := by rule_range

/-- `generic.rules:351`: `(OrB (Leq64 (Const64 [c]) x) (Leq64 x (Const64 [d]))) && c >= d+1 && d+1 > d => (Leq64U (Const64 <x.Type> [c-d-1]) (Sub64 <x.Type> x (Const64 <x.Type> [d+1])))` -/
theorem r_generic_351_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_351_2 := by rule_range

/-- `generic.rules:352`: `(OrB (Less32 (Const32 [c]) x) (Leq32 x (Const32 [d]))) && c >= d+1 && d+1 > d => (Less32U (Const32 <x.Type> [c-d-1]) (Sub32 <x.Type> x (Const32 <x.Type> [d+1])))` -/
theorem r_generic_352_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_352 := by rule_range

/-- `generic.rules:352`: `(OrB (Leq32 (Const32 [c]) x) (Leq32 x (Const32 [d]))) && c >= d+1 && d+1 > d => (Leq32U (Const32 <x.Type> [c-d-1]) (Sub32 <x.Type> x (Const32 <x.Type> [d+1])))` -/
theorem r_generic_352_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_352_2 := by rule_range

/-- `generic.rules:353`: `(OrB (Less16 (Const16 [c]) x) (Leq16 x (Const16 [d]))) && c >= d+1 && d+1 > d => (Less16U (Const16 <x.Type> [c-d-1]) (Sub16 <x.Type> x (Const16 <x.Type> [d+1])))` -/
theorem r_generic_353_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_353 := by rule_range

/-- `generic.rules:353`: `(OrB (Leq16 (Const16 [c]) x) (Leq16 x (Const16 [d]))) && c >= d+1 && d+1 > d => (Leq16U (Const16 <x.Type> [c-d-1]) (Sub16 <x.Type> x (Const16 <x.Type> [d+1])))` -/
theorem r_generic_353_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_353_2 := by rule_range

/-- `generic.rules:354`: `(OrB (Less8 (Const8 [c]) x) (Leq8 x (Const8 [d]))) && c >= d+1 && d+1 > d => (Less8U (Const8 <x.Type> [c-d-1]) (Sub8 <x.Type> x (Const8 <x.Type> [d+1])))` -/
theorem r_generic_354_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_354 := by rule_range

/-- `generic.rules:354`: `(OrB (Leq8 (Const8 [c]) x) (Leq8 x (Const8 [d]))) && c >= d+1 && d+1 > d => (Leq8U (Const8 <x.Type> [c-d-1]) (Sub8 <x.Type> x (Const8 <x.Type> [d+1])))` -/
theorem r_generic_354_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_354_2 := by rule_range

end GoFV.Proof.Rules
