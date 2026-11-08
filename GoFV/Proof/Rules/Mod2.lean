import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values06

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `Mod` rules (part 2)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Mod` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:218`: `(Mod64 (Const64 [c]) (Const64 [d])) && d != 0 => (Const64 [c % d])` -/
theorem r_generic_218_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_218 := by rule_auto

/-- `generic.rules:1144`: `(Mod64 <t> n (Const64 [c])) && c < 0 && c != -1<<63 => (Mod64 <t> n (Const64 <t> [-c]))` -/
theorem r_generic_1144_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1144 := by rule_auto

/-- `generic.rules:1156`: `(Mod64 <t> x (Const64 [c])) && x.Op != OpConst64 && (c > 0 || c == -1<<63) => (Sub64 x (Mul64 <t> (Div64 <t> x (Const64 <t> [c])) (Const64 <t> [c])))` -/
theorem r_generic_1156_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1156 := by rule_auto

/-- `generic.rules:223`: `(Mod64u (Const64 [c]) (Const64 [d])) && d != 0 => (Const64 [int64(uint64(c) % uint64(d))])` -/
theorem r_generic_223_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_223 := by rule_auto

/-- `generic.rules:1164`: `(Mod64u <t> x (Const64 [c])) && x.Op != OpConst64 && c != 0 => (Sub64 x (Mul64 <t> (Div64u <t> x (Const64 <t> [c])) (Const64 <t> [c])))` -/
theorem r_generic_1164_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1164 := by rule_auto

/-- `generic.rules:215`: `(Mod8 (Const8 [c]) (Const8 [d])) && d != 0 => (Const8 [c % d])` -/
theorem r_generic_215_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_215 := by rule_auto

/-- `generic.rules:1141`: `(Mod8 <t> n (Const8 [c])) && c < 0 && c != -1<<7 => (Mod8 <t> n (Const8 <t> [-c]))` -/
theorem r_generic_1141_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1141 := by rule_auto

/-- `generic.rules:1150`: `(Mod8 <t> x (Const8 [c])) && x.Op != OpConst8 && (c > 0 || c == -1<<7) => (Sub8 x (Mul8 <t> (Div8 <t> x (Const8 <t> [c])) (Const8 <t> [c])))` -/
theorem r_generic_1150_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1150 := by rule_auto

/-- `generic.rules:220`: `(Mod8u (Const8 [c]) (Const8 [d])) && d != 0 => (Const8 [int8(uint8(c) % uint8(d))])` -/
theorem r_generic_220_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_220 := by rule_auto

/-- `generic.rules:1158`: `(Mod8u <t> x (Const8 [c])) && x.Op != OpConst8 && c != 0 => (Sub8 x (Mul8 <t> (Div8u <t> x (Const8 <t> [c])) (Const8 <t> [c])))` -/
theorem r_generic_1158_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1158 := by rule_auto

end GoFV.Proof.Rules
