import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values02

/-!
# Rule lemmas: `Div` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Div` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

-- `divmod.rules:136–148` (`(Div16u/32u/64u <t> x (Const [c])) && t.IsSigned() && smagicOK(c)`)
-- are false under the semantics: `t.IsSigned()` is an oracle atom, nothing makes `x`
-- non-negative (Go applies them after the prove pass showed it), e.g. 136 at c = 3,
-- x = 0xFFFF: 21845 vs 32767 (agent DivmodU, docs/proofs/rules.md "Findings").
-- FALSE r_divmod_136 #69
-- FALSE r_divmod_140 #69
-- FALSE r_divmod_144 #69
-- FALSE r_divmod_148 #69

/-- `generic.rules:173`: `(Div16 (Const16 [c]) (Const16 [d])) && d != 0 => (Const16 [c/d])` -/
theorem r_generic_173_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_173 := by rule_auto

/-- `generic.rules:1083`: `(Div16 <t> n (Const16 [c])) && c < 0 && c != -1<<15 => (Neg16 (Div16 <t> n (Const16 <t> [-c])))` -/
theorem r_generic_1083_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1083 := by rule_auto

/-- `generic.rules:1092`: `(Div16 <t> x (Const16 [-1<<15])) => (Rsh16Ux64 (And16 <t> x (Neg16 <t> x)) (Const64 <typ.UInt64> [15]))` -/
theorem r_generic_1092_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1092 := by rule_auto

/-- `generic.rules:177`: `(Div16u (Const16 [c]) (Const16 [d])) && d != 0 => (Const16 [int16(uint16(c)/uint16(d))])` -/
theorem r_generic_177_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_177 := by rule_auto

/-- `generic.rules:174`: `(Div32 (Const32 [c]) (Const32 [d])) && d != 0 => (Const32 [c/d])` -/
theorem r_generic_174_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_174 := by rule_auto

/-- `generic.rules:1084`: `(Div32 <t> n (Const32 [c])) && c < 0 && c != -1<<31 => (Neg32 (Div32 <t> n (Const32 <t> [-c])))` -/
theorem r_generic_1084_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1084 := by rule_auto

/-- `generic.rules:1093`: `(Div32 <t> x (Const32 [-1<<31])) => (Rsh32Ux64 (And32 <t> x (Neg32 <t> x)) (Const64 <typ.UInt64> [31]))` -/
theorem r_generic_1093_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1093 := by rule_auto

/-- `generic.rules:178`: `(Div32u (Const32 [c]) (Const32 [d])) && d != 0 => (Const32 [int32(uint32(c)/uint32(d))])` -/
theorem r_generic_178_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_178 := by rule_auto

end GoFV.Proof.Rules
