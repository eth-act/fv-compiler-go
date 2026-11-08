import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values11

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `Rsh` rules (part 8)

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the phase-P1 rules whose top op is in the
`Rsh` family (`docs/proofs/rules.md`).
-/

namespace GoFV.Proof.Rules

/-- `generic.rules:1199`: `(Rsh8Ux64 [false] x con:(Const64 [c])) && 0 < c && c < 8 => (Rsh8Ux64 [true] x con)` -/
theorem r_generic_1199_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1199_3 := by rule_auto


/-- `generic.rules:469`: `(Rsh8Ux8 x (Const8 [c])) => (Rsh8Ux64 x (Const64 <types.Types[types.TUINT64]> [int64(uint8(c))]))` -/
theorem r_generic_469_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_469 := by rule_auto


/-- `generic.rules:1199`: `(Rsh8Ux8 [false] x con:(Const8 [c])) && 0 < c && c < 8 => (Rsh8Ux8 [true] x con)` -/
theorem r_generic_1199_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1199_4 := by rule_auto


/-- `generic.rules:465`: `(Rsh8x16 x (Const16 [c])) => (Rsh8x64 x (Const64 <types.Types[types.TUINT64]> [int64(uint16(c))]))` -/
theorem r_generic_465_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_465 := by rule_auto


/-- `generic.rules:464`: `(Rsh8x32 x (Const32 [c])) => (Rsh8x64 x (Const64 <types.Types[types.TUINT64]> [int64(uint32(c))]))` -/
theorem r_generic_464_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_464 := by rule_auto


/-- `generic.rules:235`: `(Rsh8x64 (Const8 [c]) (Const64 [d])) => (Const8 [c >> uint64(d)])` -/
theorem r_generic_235_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_235 := by rule_auto


/-- `generic.rules:466`: `(Rsh8x8 x (Const8 [c])) => (Rsh8x64 x (Const64 <types.Types[types.TUINT64]> [int64(uint8(c))]))` -/
theorem r_generic_466_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_466 := by rule_auto


end GoFV.Proof.Rules
