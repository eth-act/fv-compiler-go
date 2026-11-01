import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values10

/-!
# Rule lemmas: `RotateLeft` rules (part 6)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`RotateLeft` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:2236`: `(RotateLeft16 x (Sub8 (Const8 [c]) y)) && c&15 == 0 => (RotateLeft16 x (Neg8 <y.Type> y))` -/
theorem r_generic_2236_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2236_4 := by rule_auto


/-- `generic.rules:2240`: `(RotateLeft16 x (Const64 [c])) && config.PtrSize == 4 => (RotateLeft16 x (Const32 <typ.UInt32> [int32(c)]))` -/
theorem r_generic_2240_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2240 := by rule_auto


/-- `generic.rules:2245`: `(RotateLeft16 (RotateLeft16 x c) d) && c.Type.Size() == 8 && d.Type.Size() == 8 => (RotateLeft16 x (Add64 <c.Type> c d))` -/
theorem r_generic_2245_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2245 := by rule_auto


/-- `generic.rules:2246`: `(RotateLeft16 (RotateLeft16 x c) d) && c.Type.Size() == 4 && d.Type.Size() == 4 => (RotateLeft16 x (Add32 <c.Type> c d))` -/
theorem r_generic_2246_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2246 := by rule_auto


/-- `generic.rules:2247`: `(RotateLeft16 (RotateLeft16 x c) d) && c.Type.Size() == 2 && d.Type.Size() == 2 => (RotateLeft16 x (Add16 <c.Type> c d))` -/
theorem r_generic_2247_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2247 := by rule_auto


/-- `generic.rules:2248`: `(RotateLeft16 (RotateLeft16 x c) d) && c.Type.Size() == 1 && d.Type.Size() == 1 => (RotateLeft16 x (Add8 <c.Type> c d))` -/
theorem r_generic_2248_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2248 := by rule_auto

end GoFV.Proof.Rules
