import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values11

/-!
# Rule lemmas: `Rsh` rules (part 4)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Rsh` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:449`: `(Rsh32Ux8 x (Const8 [c])) => (Rsh32Ux64 x (Const64 <types.Types[types.TUINT64]> [int64(uint8(c))]))` -/
theorem r_generic_449_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_449 := by rule_auto


/-- `generic.rules:1193`: `(Rsh32Ux8 [false] x con:(Const8 [c])) && 0 < c && c < 32 => (Rsh32Ux8 [true] x con)` -/
theorem r_generic_1193_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1193_4 := by rule_auto


/-- `generic.rules:445`: `(Rsh32x16 x (Const16 [c])) => (Rsh32x64 x (Const64 <types.Types[types.TUINT64]> [int64(uint16(c))]))` -/
theorem r_generic_445_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_445 := by rule_auto


/-- `generic.rules:1192`: `(Rsh32x16 [false] x con:(Const16 [c])) && 0 < c && c < 32 => (Rsh32x16 [true] x con)` -/
theorem r_generic_1192_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1192 := by rule_auto


/-- `generic.rules:444`: `(Rsh32x32 x (Const32 [c])) => (Rsh32x64 x (Const64 <types.Types[types.TUINT64]> [int64(uint32(c))]))` -/
theorem r_generic_444_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_444 := by rule_auto


/-- `generic.rules:1192`: `(Rsh32x32 [false] x con:(Const32 [c])) && 0 < c && c < 32 => (Rsh32x32 [true] x con)` -/
theorem r_generic_1192_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1192_2 := by rule_auto


/-- `generic.rules:229`: `(Rsh32x64 (Const32 [c]) (Const64 [d])) => (Const32 [c >> uint64(d)])` -/
theorem r_generic_229_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_229 := by rule_auto


/-- `generic.rules:1192`: `(Rsh32x64 [false] x con:(Const64 [c])) && 0 < c && c < 32 => (Rsh32x64 [true] x con)` -/
theorem r_generic_1192_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1192_3 := by rule_auto


/-- `generic.rules:446`: `(Rsh32x8 x (Const8 [c])) => (Rsh32x64 x (Const64 <types.Types[types.TUINT64]> [int64(uint8(c))]))` -/
theorem r_generic_446_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_446 := by rule_auto


/-- `generic.rules:1192`: `(Rsh32x8 [false] x con:(Const8 [c])) && 0 < c && c < 32 => (Rsh32x8 [true] x con)` -/
theorem r_generic_1192_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1192_4 := by rule_auto


/-- `generic.rules:438`: `(Rsh64Ux16 x (Const16 [c])) => (Rsh64Ux64 x (Const64 <types.Types[types.TUINT64]> [int64(uint16(c))]))` -/
theorem r_generic_438_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_438 := by rule_auto


/-- `generic.rules:1190`: `(Rsh64Ux16 [false] x con:(Const16 [c])) && 0 < c && c < 64 => (Rsh64Ux16 [true] x con)` -/
theorem r_generic_1190_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1190 := by rule_auto


end GoFV.Proof.Rules
