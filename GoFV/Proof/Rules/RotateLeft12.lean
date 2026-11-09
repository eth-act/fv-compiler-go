import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values10

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `RotateLeft` rules (part 12)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`RotateLeft` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:2237`: `(RotateLeft8 x (Sub8 (Const8 [c]) y)) && c&7 == 0 => (RotateLeft8 x (Neg8 <y.Type> y))` -/
theorem r_generic_2237_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2237_4 := by rule_auto


/-- `generic.rules:2240`: `(RotateLeft8 x (Const64 [c])) && config.PtrSize == 4 => (RotateLeft8 x (Const32 <typ.UInt32> [int32(c)]))` -/
theorem r_generic_2240_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2240_4 := by rule_auto


/-- `generic.rules:2245`: `(RotateLeft8 (RotateLeft8 x c) d) && c.Type.Size() == 8 && d.Type.Size() == 8 => (RotateLeft8 x (Add64 <c.Type> c d))` -/
theorem r_generic_2245_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2245_4 := by rule_auto


/-- `generic.rules:2246`: `(RotateLeft8 (RotateLeft8 x c) d) && c.Type.Size() == 4 && d.Type.Size() == 4 => (RotateLeft8 x (Add32 <c.Type> c d))` -/
theorem r_generic_2246_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2246_4 := by rule_auto_dec


/-- `generic.rules:2247`: `(RotateLeft8 (RotateLeft8 x c) d) && c.Type.Size() == 2 && d.Type.Size() == 2 => (RotateLeft8 x (Add16 <c.Type> c d))` -/
theorem r_generic_2247_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2247_4 := by rule_auto_dec


/-- `generic.rules:2248`: `(RotateLeft8 (RotateLeft8 x c) d) && c.Type.Size() == 1 && d.Type.Size() == 1 => (RotateLeft8 x (Add8 <c.Type> c d))` -/
theorem r_generic_2248_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_2248_4 := by rule_auto

end GoFV.Proof.Rules
