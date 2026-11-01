import GoFV.Proof.Rules.DivmodUMagic2

/-!
# Unsigned magic division, `Mul` by `2^16 + m` and `Avg64u` (`divmod.rules:159`, `:232`)

`rule_unfold_getd` and `KernelSafe` (`TacticCond.lean`), `divu_auto`, the closers of
`DivmodUMagic.lean`/`DivmodUMagic2.lean` (`docs/proofs/rules.md`, "Kernel deep recursion").
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules.DivmodU
open GoFV.Proof.Rules.KernelSafe

/-- `divmod.rules:159`: `(Div16u <t> x (Const16 [c])) && umagicOK16(c) && config.RegSize == 8 => (Trunc64to16 <t> (Rsh64Ux64 <typ.UInt64> (Mul64 <typ.UInt64> (ZeroExt16to64 x) (Const64 <typ.UInt64> [int64(1<<16 + umagic16(c).m)])) (Const64 <typ.UInt64> [16 + umagic16(c).s])))` -/
theorem r_divmod_159_sound : Rule.Sound GoFV.Rules.Generated.Divmod.r_divmod_159 := by
  rule_unfold_getd
  divu_auto
  all_goals
    divu_facts
    exact close_mul_full _ _ _ _ hspec (by decide) (toNat_ofNat_add_ofNat _ _ (by omega))
      (by divu_amt)

/-- `divmod.rules:159` at `x = 100`, `c = 7`. -/
theorem inst_r_divmod_159 : Rule.Inst GoFV.Rules.Generated.Divmod.r_divmod_159
    (PEnv.ofLists [([0], .i16 100)] [] (.int .w16) [([1], 7)]) (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Divmod.r_divmod_159]
  rule_eval
  rfl

/-- `divmod.rules:232`: `(Div64u <t> x (Const64 [c])) && umagicOK64(c) => (Rsh64Ux64 <t> (Avg64u x (Hmul64u <typ.UInt64> x (Const64 <typ.UInt64> [int64(umagic64(c).m)]))) (Const64 <typ.UInt64> [umagic64(c).s - 1]))` -/
theorem r_divmod_232_sound : Rule.Sound GoFV.Rules.Generated.Divmod.r_divmod_232 := by
  rule_unfold_getd
  divu_auto
  all_goals divu_facts
  · have := hmul_le (n := 64) ‹BitVec 64› (BitVec.ofNat 64 ‹Nat›)
    omega
  · exact close_avg_hmul _ _ _ hspec (by divu_amt)

/-- `divmod.rules:232` at `x = 100`, `c = 7`. -/
theorem inst_r_divmod_232 : Rule.Inst GoFV.Rules.Generated.Divmod.r_divmod_232
    (PEnv.ofLists [([0], .i64 100)] [] (.int .w64) [([1], 7)]) (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Divmod.r_divmod_232]
  rule_eval
  rfl

end GoFV.Proof.Rules
