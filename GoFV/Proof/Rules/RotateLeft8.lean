import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values10

/-!
# Rule lemmas: `RotateLeft` rules (part 8)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`RotateLeft` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:2235`: `(RotateLeft32 x (Sub8 (Const8 [c]) y)) && c&31 == 0 => (RotateLeft32 x (Neg8 <y.Type> y))` -/
theorem r_generic_2235_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2235_4 := by rule_auto


/-- `generic.rules:2240`: `(RotateLeft32 x (Const64 [c])) && config.PtrSize == 4 => (RotateLeft32 x (Const32 <typ.UInt32> [int32(c)]))` -/
theorem r_generic_2240_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2240_2 := by rule_auto


/-- `generic.rules:2245`: `(RotateLeft32 (RotateLeft32 x c) d) && c.Type.Size() == 8 && d.Type.Size() == 8 => (RotateLeft32 x (Add64 <c.Type> c d))` -/
theorem r_generic_2245_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2245_2 := by rule_auto


/-- `generic.rules:2246`: `(RotateLeft32 (RotateLeft32 x c) d) && c.Type.Size() == 4 && d.Type.Size() == 4 => (RotateLeft32 x (Add32 <c.Type> c d))` -/
theorem r_generic_2246_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2246_2 := by rule_auto_dec


/-- `generic.rules:2247`: `(RotateLeft32 (RotateLeft32 x c) d) && c.Type.Size() == 2 && d.Type.Size() == 2 => (RotateLeft32 x (Add16 <c.Type> c d))` -/
theorem r_generic_2247_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2247_2 := by rule_auto_dec


/-- `generic.rules:2248`: `(RotateLeft32 (RotateLeft32 x c) d) && c.Type.Size() == 1 && d.Type.Size() == 1 => (RotateLeft32 x (Add8 <c.Type> c d))` -/
theorem r_generic_2248_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2248_2 := by rule_auto

end GoFV.Proof.Rules
