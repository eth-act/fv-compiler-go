import GoFV.Proof.Rules.DivmodUMagic2

variable [GoFV.SSA.Sem.Addrs]

/-!
# Unsigned magic division, `Mul` by `2^16 + m` and `Avg64u` (`divmod.rules:159`, `:221`, `:232`)

`rule_unfold_getd` and `KernelSafe` (`TacticCond.lean`), `divu_auto`, the closers of
`DivmodUMagic.lean`/`DivmodUMagic2.lean` (`docs/proofs/rules.md`, "Kernel deep recursion").
-/

namespace GoFV.Proof.Rules.DivmodU

theorem toNat_zext_shl32 (x : BitVec 32) {a : Nat} (ha : a = 32) :
    (BitVec.setWidth 64 x <<< a).toNat = x.toNat * 2 ^ 32 := by
  have hx := x.isLt
  rw [ha, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_trans hx (by decide)), Nat.shiftLeft_eq]
  exact Nat.mod_eq_of_lt (mul_lt_two_pow hx (Nat.le_refl _) (by decide))

theorem toNat_zext_mul32 (x : BitVec 32) {m : Nat} (hm : m < 2 ^ 32) :
    (BitVec.setWidth 64 x * BitVec.ofNat 64 m).toNat = x.toNat * m := by
  have hx := x.isLt
  rw [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (Nat.lt_trans hx (by decide)), Nat.mod_eq_of_lt (Nat.lt_trans hm (by decide))]
  exact Nat.mod_eq_of_lt (mul_lt_two_pow hx (Nat.le_of_lt hm) (by decide))

/-- `Avg64u (x << 32) (x * m)` (zero-extended 32-bit `x`, `divmod.rules:221`) meets its
`x ≥ y` premise: `x * 2^32 ≥ x * m`. -/
theorem avg_shl_ge (x : BitVec 32) {a m : Nat} (hm : m < 2 ^ 32) (ha : a = 32) :
    ¬(BitVec.setWidth 64 x <<< a).toNat < (BitVec.setWidth 64 x * BitVec.ofNat 64 m).toNat := by
  rw [toNat_zext_shl32 x ha, toNat_zext_mul32 x hm]
  exact Nat.not_lt.mpr (Nat.mul_le_mul_left _ (Nat.le_of_lt hm))

/-- `divmod.rules:221`: `Avg64u (x << 32) (x * m) >> (32 + S - 1)`, truncated, is `x / d`. -/
theorem close_avg_shl {S m : Nat} (x : BitVec 32) (c : Int) (a k : Nat) (h : USpec 32 c S m)
    (ha : a = 32) (hk : k = 32 + S - 1) :
    x / BitVec.ofInt 32 c =
      BitVec.setWidth 32
        (BitVec.ofNat 64 (((BitVec.setWidth 64 x <<< a).toNat +
          (BitVec.setWidth 64 x * BitVec.ofNat 64 m).toNat) / 2) >>> k) := by
  have hx := x.isLt
  have hm := h.m_lt
  have hS := h.S_le
  have hS2 := h.S_ge
  have hlt : x.toNat * (2 ^ 32 + m) < 2 ^ 65 :=
    mul_lt_two_pow (p := 32) (q := 33) hx (by omega) (by omega)
  have hlt2 : x.toNat * (2 ^ 32 + m) / 2 < 2 ^ 64 := by omega
  apply BitVec.eq_of_toNat_eq
  rw [toNat_zext_shl32 x ha, toNat_zext_mul32 x hm, hk, ← Nat.mul_add, BitVec.toNat_udiv,
    toNat_ofInt_lowBits, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hlt2, Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_succ',
    show (32 + S - 1).succ = 32 + S by omega, udiv_mul h hx]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx)).symm

end GoFV.Proof.Rules.DivmodU

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

/-- `divmod.rules:221`: `(Div32u <t> x (Const32 [c])) && umagicOK32(c) && config.RegSize == 8 => (Trunc64to32 <t> (Rsh64Ux64 <typ.UInt64> (Avg64u (Lsh64x64 <typ.UInt64> (ZeroExt32to64 x) (Const64 <typ.UInt64> [32])) (Mul64 <typ.UInt64> (ZeroExt32to64 x) (Const64 <typ.UInt64> [int64(umagic32(c).m)]))) (Const64 <typ.UInt64> [32 + umagic32(c).s - 1])))` -/
theorem r_divmod_221_sound : Rule.Sound GoFV.Rules.Generated.Divmod.r_divmod_221 := by
  rule_unfold_getd
  divu_auto
  all_goals divu_facts
  · refine avg_shl_ge _ hspec.m_lt ?_ ‹_›
    decide
  · refine close_avg_shl _ _ _ _ hspec ?_ ?_
    · decide
    · simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at *
      omega

/-- `divmod.rules:221` at `x = 100`, `c = 7`. -/
theorem inst_r_divmod_221 : Rule.Inst GoFV.Rules.Generated.Divmod.r_divmod_221
    (PEnv.ofLists [([0], .i32 100)] [] (.int .w32) [([1], 7)]) (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Divmod.r_divmod_221]
  rule_eval
  rfl

end GoFV.Proof.Rules
