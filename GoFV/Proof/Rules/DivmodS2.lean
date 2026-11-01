import GoFV.Proof.Rules.DivmodSBV
import GoFV.Rules.Generated.Divmod.Values00

/-!
# Signed division by a constant, `smagic` rules (`divmod.rules`, #69)

`Div8..64 x (Const c)`: by a power of two (biased arithmetic shift, `divs_pow2`) and by the
`smagic` magic number (`divs_smagic` replaces the helper call by its result and
`DivmodS.SSpec`, `divs_close` applies the width-generic lemma of the rule's shape;
`GoFV/Proof/Rules/DivmodSMagic.lean`).
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Rules.Generated.Divmod

/-- `divmod.rules:87`: `(Div8 <t> x (Const8 [c])) && smagicOK8(c) => (Sub8 <t> (Rsh32x64 <t> (Mul32 <typ.UInt32> (SignExt8to32 x) (Const32 <typ.UInt32> [int32(smagic8(c).m)])) (Const64 <typ.UInt64> [8 + smagic8(c).s])) (Rsh32x64 <t> (SignExt8to32 x) (Const64 <typ.UInt64> [31])))` -/
theorem r_divmod_87_sound : Rule.Sound r_divmod_87 := by
  rule_unfold
  (try rule_ands)
  divs_smagic
  divs_prefix
  all_goals divs_wide

/-- `divmod.rules:93`: `(Div16 <t> x (Const16 [c])) && smagicOK16(c) => (Sub16 <t> (Rsh32x64 <t> (Mul32 <typ.UInt32> (SignExt16to32 x) (Const32 <typ.UInt32> [int32(smagic16(c).m)])) (Const64 <typ.UInt64> [16 + smagic16(c).s])) (Rsh32x64 <t> (SignExt16to32 x) (Const64 <typ.UInt64> [31])))` -/
theorem r_divmod_93_sound : Rule.Sound r_divmod_93 := by
  rule_unfold
  (try rule_ands)
  divs_smagic
  divs_prefix
  all_goals divs_wide

/-- `divmod.rules:99`: `(Div32 <t> x (Const32 [c])) && smagicOK32(c) && config.RegSize == 8 => (Sub32 <t> (Rsh64x64 <t> (Mul64 <typ.UInt64> (SignExt32to64 x) (Const64 <typ.UInt64> [int64(smagic32(c).m)])) (Const64 <typ.UInt64> [32 + smagic32(c).s])) (Rsh64x64 <t> (SignExt32to64 x) (Const64 <typ.UInt64> [63])))` -/
theorem r_divmod_99_sound : Rule.Sound r_divmod_99 := by
  rule_unfold
  (try rule_ands)
  divs_smagic
  divs_prefix
  all_goals divs_wide

/-- `divmod.rules:113`: `(Div64 <t> x (Const64 [c])) && smagicOK64(c) && smagic64(c).m&1 == 0 => (Sub64 <t> (Rsh64x64 <t> (Hmul64 <t> x (Const64 <typ.UInt64> [int64(smagic64(c).m/2)])) (Const64 <typ.UInt64> [smagic64(c).s - 1])) (Rsh64x64 <t> x (Const64 <typ.UInt64> [63])))` -/
theorem r_divmod_113_sound : Rule.Sound r_divmod_113 := by
  rule_unfold
  (try rule_ands)
  divs_smagic
  divs_prefix
  all_goals divs_even

/-- `divmod.rules:121`: `(Div32 <t> x (Const32 [c])) && smagicOK32(c) && config.RegSize == 4 && smagic32(c).m&1 != 0 => (Sub32 <t> (Rsh32x64 <t> (Add32 <t> x (Hmul32 <t> x (Const32 <typ.UInt32> [int32(smagic32(c).m)]))) (Const64 <typ.UInt64> [smagic32(c).s])) (Rsh32x64 <t> x (Const64 <typ.UInt64> [31])))` -/
theorem r_divmod_121_sound : Rule.Sound r_divmod_121 := by
  rule_unfold
  cases hok : Magic.smagicOK (wrapInt 32 true (e.auxInt [1]).toInt)
  · simp only [hok, cond_false, binE, DV.bool.injEq, Bool.false_eq_true, false_and] at hcond
  (try rule_ands)
  divs_smagic
  divs_prefix
  all_goals divs_add

/-- `divmod.rules:127`: `(Div64 <t> x (Const64 [c])) && smagicOK64(c) && smagic64(c).m&1 != 0 => (Sub64 <t> (Rsh64x64 <t> (Add64 <t> x (Hmul64 <t> x (Const64 <typ.UInt64> [int64(smagic64(c).m)]))) (Const64 <typ.UInt64> [smagic64(c).s])) (Rsh64x64 <t> x (Const64 <typ.UInt64> [63])))` -/
theorem r_divmod_127_sound : Rule.Sound r_divmod_127 := by
  rule_unfold
  (try rule_ands)
  divs_smagic
  divs_prefix
  all_goals divs_add

end GoFV.Proof.Rules
