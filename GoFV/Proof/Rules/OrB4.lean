import GoFV.Proof.Rules.TacticRange
import GoFV.Rules.Generated.Generic.Values09

/-!
# Rule lemmas: `OrB` rules (part 4)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the P1/P2 rules whose top op is in the
`OrB` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:363`: `(OrB (Less64U (Const64 [c]) x) (Leq64U x (Const64 [d]))) && uint64(c) >= uint64(d+1) && uint64(d+1) > uint64(d) => (Less64U (Const64 <x.Type> [c-d-1]) (Sub64 <x.Type> x (Const64 <x.Type> [d+1])))` -/
theorem r_generic_363_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_363 := by rule_range

/-- `generic.rules:363`: `(OrB (Leq64U (Const64 [c]) x) (Leq64U x (Const64 [d]))) && uint64(c) >= uint64(d+1) && uint64(d+1) > uint64(d) => (Leq64U (Const64 <x.Type> [c-d-1]) (Sub64 <x.Type> x (Const64 <x.Type> [d+1])))` -/
theorem r_generic_363_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_363_2 := by rule_range

/-- `generic.rules:364`: `(OrB (Less32U (Const32 [c]) x) (Leq32U x (Const32 [d]))) && uint32(c) >= uint32(d+1) && uint32(d+1) > uint32(d) => (Less32U (Const32 <x.Type> [c-d-1]) (Sub32 <x.Type> x (Const32 <x.Type> [d+1])))` -/
theorem r_generic_364_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_364 := by rule_range

/-- `generic.rules:364`: `(OrB (Leq32U (Const32 [c]) x) (Leq32U x (Const32 [d]))) && uint32(c) >= uint32(d+1) && uint32(d+1) > uint32(d) => (Leq32U (Const32 <x.Type> [c-d-1]) (Sub32 <x.Type> x (Const32 <x.Type> [d+1])))` -/
theorem r_generic_364_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_364_2 := by rule_range

/-- `generic.rules:365`: `(OrB (Less16U (Const16 [c]) x) (Leq16U x (Const16 [d]))) && uint16(c) >= uint16(d+1) && uint16(d+1) > uint16(d) => (Less16U (Const16 <x.Type> [c-d-1]) (Sub16 <x.Type> x (Const16 <x.Type> [d+1])))` -/
theorem r_generic_365_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_365 := by rule_range

/-- `generic.rules:365`: `(OrB (Leq16U (Const16 [c]) x) (Leq16U x (Const16 [d]))) && uint16(c) >= uint16(d+1) && uint16(d+1) > uint16(d) => (Leq16U (Const16 <x.Type> [c-d-1]) (Sub16 <x.Type> x (Const16 <x.Type> [d+1])))` -/
theorem r_generic_365_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_365_2 := by rule_range

/-- `generic.rules:366`: `(OrB (Less8U (Const8 [c]) x) (Leq8U x (Const8 [d]))) && uint8(c) >= uint8(d+1) && uint8(d+1) > uint8(d) => (Less8U (Const8 <x.Type> [c-d-1]) (Sub8 <x.Type> x (Const8 <x.Type> [d+1])))` -/
theorem r_generic_366_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_366 := by rule_range

/-- `generic.rules:366`: `(OrB (Leq8U (Const8 [c]) x) (Leq8U x (Const8 [d]))) && uint8(c) >= uint8(d+1) && uint8(d+1) > uint8(d) => (Leq8U (Const8 <x.Type> [c-d-1]) (Sub8 <x.Type> x (Const8 <x.Type> [d+1])))` -/
theorem r_generic_366_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_366_2 := by rule_range

end GoFV.Proof.Rules
