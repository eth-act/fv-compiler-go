import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values02

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `Div` rules (part 2)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Div` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:175`: `(Div64 (Const64 [c]) (Const64 [d])) && d != 0 => (Const64 [c/d])` -/
theorem r_generic_175_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_175 := by rule_auto

/-- `generic.rules:1085`: `(Div64 <t> n (Const64 [c])) && c < 0 && c != -1<<63 => (Neg64 (Div64 <t> n (Const64 <t> [-c])))` -/
theorem r_generic_1085_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1085 := by rule_auto

/-- `generic.rules:1094`: `(Div64 <t> x (Const64 [-1<<63])) => (Rsh64Ux64 (And64 <t> x (Neg64 <t> x)) (Const64 <typ.UInt64> [63]))` -/
theorem r_generic_1094_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1094 := by rule_auto

/-- `generic.rules:179`: `(Div64u (Const64 [c]) (Const64 [d])) && d != 0 => (Const64 [int64(uint64(c)/uint64(d))])` -/
theorem r_generic_179_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_179 := by rule_auto

/-- `generic.rules:172`: `(Div8 (Const8 [c]) (Const8 [d])) && d != 0 => (Const8 [c/d])` -/
theorem r_generic_172_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_172 := by rule_auto

/-- `generic.rules:1082`: `(Div8 <t> n (Const8 [c])) && c < 0 && c != -1<<7 => (Neg8 (Div8 <t> n (Const8 <t> [-c])))` -/
theorem r_generic_1082_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1082 := by rule_auto

/-- `generic.rules:1091`: `(Div8 <t> x (Const8 [-1<<7 ])) => (Rsh8Ux64 (And8 <t> x (Neg8 <t> x)) (Const64 <typ.UInt64> [7 ]))` -/
theorem r_generic_1091_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1091 := by rule_auto

/-- `generic.rules:176`: `(Div8u (Const8 [c]) (Const8 [d])) && d != 0 => (Const8 [int8(uint8(c)/uint8(d))])` -/
theorem r_generic_176_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_176 := by rule_auto

end GoFV.Proof.Rules
