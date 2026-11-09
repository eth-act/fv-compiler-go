import GoFV.Proof.Rules.DivmodSPow2
import GoFV.Proof.Rules.DivmodSBV
import GoFV.Proof.Rules.NonVacuous
import GoFV.Rules.Generated.Divmod.Values00

variable [GoFV.SSA.Sem.Addrs]

/-!
# Signed division by a constant (`divmod.rules`, #69)

`Div8..64 x (Const c)`: by a power of two (biased arithmetic shift, `divs_pow2`) and by the
`smagic` magic number (`divs_smagic` replaces the helper call by its result and
`DivmodS.SSpec`, `divs_close` applies the width-generic lemma of the rule's shape;
`GoFV/Proof/Rules/DivmodSMagic.lean`).
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Rules.Generated.Divmod

/-- `divmod.rules:21`: `(Div8 <t> n (Const8 [c])) && isPowerOfTwo(c) => (Rsh8x64 (Add8 <t> n (Rsh8Ux64 <t> (Rsh8x64 <t> n (Const64 <typ.UInt64> [ 7])) (Const64 <typ.UInt64> [int64( 8-log8(c))]))) (Const64 <typ.UInt64> [int64(log8(c))]))` -/
theorem r_divmod_21_sound : Rule.Sound r_divmod_21 := by
  rule_unfold
  divs_prefix
  all_goals divs_pow2

/-- `divmod.rules:25`: `(Div16 <t> n (Const16 [c])) && isPowerOfTwo(c) => (Rsh16x64 (Add16 <t> n (Rsh16Ux64 <t> (Rsh16x64 <t> n (Const64 <typ.UInt64> [15])) (Const64 <typ.UInt64> [int64(16-log16(c))]))) (Const64 <typ.UInt64> [int64(log16(c))]))` -/
theorem r_divmod_25_sound : Rule.Sound r_divmod_25 := by
  rule_unfold
  divs_prefix
  all_goals divs_pow2

/-- `divmod.rules:29`: `(Div32 <t> n (Const32 [c])) && isPowerOfTwo(c) => (Rsh32x64 (Add32 <t> n (Rsh32Ux64 <t> (Rsh32x64 <t> n (Const64 <typ.UInt64> [31])) (Const64 <typ.UInt64> [int64(32-log32(c))]))) (Const64 <typ.UInt64> [int64(log32(c))]))` -/
theorem r_divmod_29_sound : Rule.Sound r_divmod_29 := by
  rule_unfold
  divs_prefix
  all_goals divs_pow2

/-- `divmod.rules:33`: `(Div64 <t> n (Const64 [c])) && isPowerOfTwo(c) => (Rsh64x64 (Add64 <t> n (Rsh64Ux64 <t> (Rsh64x64 <t> n (Const64 <typ.UInt64> [63])) (Const64 <typ.UInt64> [int64(64-log64(c))]))) (Const64 <typ.UInt64> [int64(log64(c))]))` -/
theorem r_divmod_33_sound : Rule.Sound r_divmod_33 := by
  rule_unfold
  divs_prefix
  all_goals divs_pow2

/-- `r_divmod_87` fires on `x / 7` (8-bit): the `smagic` path. -/
theorem inst_r_divmod_87 : Rule.Inst r_divmod_87
    (PEnv.ofLists [([0], .i8 100)] [([1], .int .w8)] (.int .w8) [([1], 7)]) (Oracle.const true) := by
  simp [r_divmod_87]
  rule_eval
  all_goals rfl

end GoFV.Proof.Rules
