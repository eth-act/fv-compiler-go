import GoFV.Proof.Rules.DivmodUMagic2

/-!
# Unsigned magic division with `umagic(c).m` in the condition (`divmod.rules:171`, `:180`, `:206`)

`rule_unfold_getd` and `KernelSafe` (`TacticCond.lean`), `divu_auto`, the closers of
`DivmodUMagic.lean`/`DivmodUMagic2.lean` (`docs/proofs/rules.md`, "Kernel deep recursion").
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules.DivmodU
open GoFV.Proof.Rules.KernelSafe

/-- `divmod.rules:180`: `(Div64u <t> x (Const64 [c])) && umagicOK64(c) && umagic64(c).m&1 == 0 => (Rsh64Ux64 <t> (Hmul64u <typ.UInt64> x (Const64 <typ.UInt64> [int64(1<<63 + umagic64(c).m/2)])) (Const64 <typ.UInt64> [umagic64(c).s - 1]))` -/
theorem r_divmod_180_sound : Rule.Sound GoFV.Rules.Generated.Divmod.r_divmod_180 := by
  rule_unfold_getd
  divu_auto
  all_goals
    divu_facts
    exact close_hmul_half _ _ _ _ hspec (m_even_of_and_one (by omega) ‹_›)
      (by rw [goQuo_nat_two]; exact toNat_ofNat_add_ofInt _ _ (by omega)) (by divu_amt)

/-- `divmod.rules:180` at `x = 100`, `c = 3` (`umagic64(3).m` even). -/
theorem inst_r_divmod_180 : Rule.Inst GoFV.Rules.Generated.Divmod.r_divmod_180
    (PEnv.ofLists [([0], .i64 100)] [] (.int .w64) [([1], 3)]) (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Divmod.r_divmod_180]
  rule_eval
  rfl

/-- `divmod.rules:171`: `(Div32u <t> x (Const32 [c])) && umagicOK32(c) && umagic32(c).m&1 == 0 && config.RegSize == 8 => (Trunc64to32 <t> (Rsh64Ux64 <typ.UInt64> (Mul64 <typ.UInt64> (ZeroExt32to64 x) (Const64 <typ.UInt64> [int64(1<<31 + umagic32(c).m/2)])) (Const64 <typ.UInt64> [32 + umagic32(c).s - 1])))` -/
theorem r_divmod_171_sound : Rule.Sound GoFV.Rules.Generated.Divmod.r_divmod_171 := by
  rule_unfold_getd
  divu_auto
  all_goals
    divu_facts
    exact close_mul_half _ _ _ _ hspec (m_even_of_and_one (by omega) hcond.1) (by decide)
      (by rw [goQuo_nat_two]; exact toNat_ofNat_add_ofInt _ _ (by omega)) (by divu_amt)

/-- `divmod.rules:171` at `x = 100`, `c = 3`. -/
theorem inst_r_divmod_171 : Rule.Inst GoFV.Rules.Generated.Divmod.r_divmod_171
    (PEnv.ofLists [([0], .i32 100)] [] (.int .w32) [([1], 3)]) (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Divmod.r_divmod_171]
  rule_eval
  rfl

/-- `divmod.rules:206`: `(Div64u <t> x (Const64 [c])) && umagicOK64(c) && c&1 == 0 => (Rsh64Ux64 <t> (Hmul64u <typ.UInt64> (Rsh64Ux64 <typ.UInt64> x (Const64 <typ.UInt64> [1])) (Const64 <typ.UInt64> [int64(1<<63 + (umagic64(c).m+1)/2)])) (Const64 <typ.UInt64> [umagic64(c).s - 2]))` -/
theorem r_divmod_206_sound : Rule.Sound GoFV.Rules.Generated.Divmod.r_divmod_206 := by
  rule_unfold_getd
  divu_auto
  all_goals
    divu_facts
    have hd := lowBits_even_of_and_one ‹_›
    have hm1 := m_succ_lt hspec hd
    exact close_hmul_even _ _ _ _ hspec hd
      (by rw [wrapInt_succ _ (by omega), goQuo_nat_two]
          exact toNat_ofNat_add_ofInt _ _ (by omega))
      (by divu_amt)

/-- `divmod.rules:206` at `x = 100`, `c = 6`. -/
theorem inst_r_divmod_206 : Rule.Inst GoFV.Rules.Generated.Divmod.r_divmod_206
    (PEnv.ofLists [([0], .i64 100)] [] (.int .w64) [([1], 6)]) (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Divmod.r_divmod_206]
  rule_eval
  rfl

end GoFV.Proof.Rules
