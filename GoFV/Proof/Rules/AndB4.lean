import GoFV.Proof.Rules.TacticRange
import GoFV.Rules.Generated.Generic.Values01

/-!
# Rule lemmas: `AndB` rules (part 4)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the P1/P2 rules whose top op is in the
`AndB` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:339`: `(AndB (Less64U (Const64 [c]) x) (Less64U x (Const64 [d]))) && uint64(d) >= uint64(c+1) && uint64(c+1) > uint64(c) => (Less64U (Sub64 <x.Type> x (Const64 <x.Type> [c+1])) (Const64 <x.Type> [d-c-1]))` -/
theorem r_generic_339_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_339 := by rule_range

/-- `generic.rules:339`: `(AndB (Less64U (Const64 [c]) x) (Leq64U x (Const64 [d]))) && uint64(d) >= uint64(c+1) && uint64(c+1) > uint64(c) => (Leq64U (Sub64 <x.Type> x (Const64 <x.Type> [c+1])) (Const64 <x.Type> [d-c-1]))` -/
theorem r_generic_339_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_339_2 := by rule_range

/-- `generic.rules:340`: `(AndB (Less32U (Const32 [c]) x) (Less32U x (Const32 [d]))) && uint32(d) >= uint32(c+1) && uint32(c+1) > uint32(c) => (Less32U (Sub32 <x.Type> x (Const32 <x.Type> [c+1])) (Const32 <x.Type> [d-c-1]))` -/
theorem r_generic_340_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_340 := by rule_range

/-- `generic.rules:340`: `(AndB (Less32U (Const32 [c]) x) (Leq32U x (Const32 [d]))) && uint32(d) >= uint32(c+1) && uint32(c+1) > uint32(c) => (Leq32U (Sub32 <x.Type> x (Const32 <x.Type> [c+1])) (Const32 <x.Type> [d-c-1]))` -/
theorem r_generic_340_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_340_2 := by rule_range

/-- `generic.rules:341`: `(AndB (Less16U (Const16 [c]) x) (Less16U x (Const16 [d]))) && uint16(d) >= uint16(c+1) && uint16(c+1) > uint16(c) => (Less16U (Sub16 <x.Type> x (Const16 <x.Type> [c+1])) (Const16 <x.Type> [d-c-1]))` -/
theorem r_generic_341_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_341 := by rule_range

/-- `generic.rules:341`: `(AndB (Less16U (Const16 [c]) x) (Leq16U x (Const16 [d]))) && uint16(d) >= uint16(c+1) && uint16(c+1) > uint16(c) => (Leq16U (Sub16 <x.Type> x (Const16 <x.Type> [c+1])) (Const16 <x.Type> [d-c-1]))` -/
theorem r_generic_341_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_341_2 := by rule_range

/-- `generic.rules:342`: `(AndB (Less8U (Const8 [c]) x) (Less8U x (Const8 [d]))) && uint8(d) >= uint8(c+1) && uint8(c+1) > uint8(c) => (Less8U (Sub8 <x.Type> x (Const8 <x.Type> [c+1])) (Const8 <x.Type> [d-c-1]))` -/
theorem r_generic_342_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_342 := by rule_range

/-- `generic.rules:342`: `(AndB (Less8U (Const8 [c]) x) (Leq8U x (Const8 [d]))) && uint8(d) >= uint8(c+1) && uint8(c+1) > uint8(c) => (Leq8U (Sub8 <x.Type> x (Const8 <x.Type> [c+1])) (Const8 <x.Type> [d-c-1]))` -/
theorem r_generic_342_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_342_2 := by rule_range

end GoFV.Proof.Rules
