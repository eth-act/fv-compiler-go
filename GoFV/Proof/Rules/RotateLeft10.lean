import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values10

/-!
# Rule lemmas: `RotateLeft` rules (part 10)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`RotateLeft` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:2234`: `(RotateLeft64 x (Sub8 (Const8 [c]) y)) && c&63 == 0 => (RotateLeft64 x (Neg8 <y.Type> y))` -/
theorem r_generic_2234_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2234_4 := by rule_auto


/-- `generic.rules:2240`: `(RotateLeft64 x (Const64 [c])) && config.PtrSize == 4 => (RotateLeft64 x (Const32 <typ.UInt32> [int32(c)]))` -/
theorem r_generic_2240_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2240_3 := by rule_auto


/-- `generic.rules:2245`: `(RotateLeft64 (RotateLeft64 x c) d) && c.Type.Size() == 8 && d.Type.Size() == 8 => (RotateLeft64 x (Add64 <c.Type> c d))` -/
theorem r_generic_2245_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2245_3 := by rule_auto


/-- `generic.rules:2246`: `(RotateLeft64 (RotateLeft64 x c) d) && c.Type.Size() == 4 && d.Type.Size() == 4 => (RotateLeft64 x (Add32 <c.Type> c d))` -/
theorem r_generic_2246_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2246_3 := by rule_auto


/-- `generic.rules:2247`: `(RotateLeft64 (RotateLeft64 x c) d) && c.Type.Size() == 2 && d.Type.Size() == 2 => (RotateLeft64 x (Add16 <c.Type> c d))` -/
theorem r_generic_2247_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2247_3 := by rule_auto


/-- `generic.rules:2248`: `(RotateLeft64 (RotateLeft64 x c) d) && c.Type.Size() == 1 && d.Type.Size() == 1 => (RotateLeft64 x (Add8 <c.Type> c d))` -/
theorem r_generic_2248_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2248_3 := by rule_auto

end GoFV.Proof.Rules
