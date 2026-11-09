import GoFV.Proof.Rules.TacticRange
import GoFV.Rules.Generated.Generic.Values09

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `OrB` rules (part 3)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the P1/P2 rules whose top op is in the
`OrB` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:357`: `(OrB (Less64U (Const64 [c]) x) (Less64U x (Const64 [d]))) && uint64(c) >= uint64(d) => (Less64U (Const64 <x.Type> [c-d]) (Sub64 <x.Type> x (Const64 <x.Type> [d])))` -/
theorem r_generic_357_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_357 := by rule_range

/-- `generic.rules:357`: `(OrB (Leq64U (Const64 [c]) x) (Less64U x (Const64 [d]))) && uint64(c) >= uint64(d) => (Leq64U (Const64 <x.Type> [c-d]) (Sub64 <x.Type> x (Const64 <x.Type> [d])))` -/
theorem r_generic_357_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_357_2 := by rule_range

/-- `generic.rules:358`: `(OrB (Less32U (Const32 [c]) x) (Less32U x (Const32 [d]))) && uint32(c) >= uint32(d) => (Less32U (Const32 <x.Type> [c-d]) (Sub32 <x.Type> x (Const32 <x.Type> [d])))` -/
theorem r_generic_358_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_358 := by rule_range

/-- `generic.rules:358`: `(OrB (Leq32U (Const32 [c]) x) (Less32U x (Const32 [d]))) && uint32(c) >= uint32(d) => (Leq32U (Const32 <x.Type> [c-d]) (Sub32 <x.Type> x (Const32 <x.Type> [d])))` -/
theorem r_generic_358_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_358_2 := by rule_range

/-- `generic.rules:359`: `(OrB (Less16U (Const16 [c]) x) (Less16U x (Const16 [d]))) && uint16(c) >= uint16(d) => (Less16U (Const16 <x.Type> [c-d]) (Sub16 <x.Type> x (Const16 <x.Type> [d])))` -/
theorem r_generic_359_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_359 := by rule_range

/-- `generic.rules:359`: `(OrB (Leq16U (Const16 [c]) x) (Less16U x (Const16 [d]))) && uint16(c) >= uint16(d) => (Leq16U (Const16 <x.Type> [c-d]) (Sub16 <x.Type> x (Const16 <x.Type> [d])))` -/
theorem r_generic_359_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_359_2 := by rule_range

/-- `generic.rules:360`: `(OrB (Less8U (Const8 [c]) x) (Less8U x (Const8 [d]))) && uint8(c) >= uint8(d) => (Less8U (Const8 <x.Type> [c-d]) (Sub8 <x.Type> x (Const8 <x.Type> [d])))` -/
theorem r_generic_360_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_360 := by rule_range

/-- `generic.rules:360`: `(OrB (Leq8U (Const8 [c]) x) (Less8U x (Const8 [d]))) && uint8(c) >= uint8(d) => (Leq8U (Const8 <x.Type> [c-d]) (Sub8 <x.Type> x (Const8 <x.Type> [d])))` -/
theorem r_generic_360_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_360_2 := by rule_range

end GoFV.Proof.Rules
