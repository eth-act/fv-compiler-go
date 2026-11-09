import GoFV.Proof.Rules.TacticRange
import GoFV.Rules.Generated.Generic.Values01

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `AndB` rules (part 3)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the P1/P2 rules whose top op is in the
`AndB` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:333`: `(AndB (Leq64U (Const64 [c]) x) (Less64U x (Const64 [d]))) && uint64(d) >= uint64(c) => (Less64U (Sub64 <x.Type> x (Const64 <x.Type> [c])) (Const64 <x.Type> [d-c]))` -/
theorem r_generic_333_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_333 := by rule_range

/-- `generic.rules:333`: `(AndB (Leq64U (Const64 [c]) x) (Leq64U x (Const64 [d]))) && uint64(d) >= uint64(c) => (Leq64U (Sub64 <x.Type> x (Const64 <x.Type> [c])) (Const64 <x.Type> [d-c]))` -/
theorem r_generic_333_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_333_2 := by rule_range

/-- `generic.rules:334`: `(AndB (Leq32U (Const32 [c]) x) (Less32U x (Const32 [d]))) && uint32(d) >= uint32(c) => (Less32U (Sub32 <x.Type> x (Const32 <x.Type> [c])) (Const32 <x.Type> [d-c]))` -/
theorem r_generic_334_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_334 := by rule_range

/-- `generic.rules:334`: `(AndB (Leq32U (Const32 [c]) x) (Leq32U x (Const32 [d]))) && uint32(d) >= uint32(c) => (Leq32U (Sub32 <x.Type> x (Const32 <x.Type> [c])) (Const32 <x.Type> [d-c]))` -/
theorem r_generic_334_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_334_2 := by rule_range

/-- `generic.rules:335`: `(AndB (Leq16U (Const16 [c]) x) (Less16U x (Const16 [d]))) && uint16(d) >= uint16(c) => (Less16U (Sub16 <x.Type> x (Const16 <x.Type> [c])) (Const16 <x.Type> [d-c]))` -/
theorem r_generic_335_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_335 := by rule_range

/-- `generic.rules:335`: `(AndB (Leq16U (Const16 [c]) x) (Leq16U x (Const16 [d]))) && uint16(d) >= uint16(c) => (Leq16U (Sub16 <x.Type> x (Const16 <x.Type> [c])) (Const16 <x.Type> [d-c]))` -/
theorem r_generic_335_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_335_2 := by rule_range

/-- `generic.rules:336`: `(AndB (Leq8U (Const8 [c]) x) (Less8U x (Const8 [d]))) && uint8(d) >= uint8(c) => (Less8U (Sub8 <x.Type> x (Const8 <x.Type> [c])) (Const8 <x.Type> [d-c]))` -/
theorem r_generic_336_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_336 := by rule_range

/-- `generic.rules:336`: `(AndB (Leq8U (Const8 [c]) x) (Leq8U x (Const8 [d]))) && uint8(d) >= uint8(c) => (Leq8U (Sub8 <x.Type> x (Const8 <x.Type> [c])) (Const8 <x.Type> [d-c]))` -/
theorem r_generic_336_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_336_2 := by rule_range

end GoFV.Proof.Rules
