import GoFV.Proof.Low.Rules.Kit

/-!
# Flags of `CMP`/`CMPW` and the comparison rules (issue #385)

`SUBS x y` (`Arm64.subFlags`, `AddWithCarry(x, ¬y, 1)`) sets `Z` iff `x = y`, `C` iff `x ≥ y`
unsigned, and `N ≠ V` iff `x < y` signed (`sub_z`, `sub_lo`, `sub_lt64`, `sub_lt32`); the
conditions `Equal` … `LessEqualU` read them as Phase 1's comparisons (`cond_sub`). A generic
comparison of two `w`-bit integers is the `CSET` of the condition on their `CMP`/`CMPW` flags
(`refines_cmp`).
-/

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules GoFV.Proof.Low

/-! ## `SUBS` flags -/

theorem sub_res (n : Nat) (x y : BitVec n) :
    BitVec.ofNat n (x.toNat + (~~~y).toNat + 1) = x - y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_not]
  have := y.isLt
  congr 1; omega

theorem sub_z (n : Nat) (x y : BitVec n) : (Arm64.subFlags x y).2.z = (x == y) := by
  simp only [Arm64.subFlags, addWithCarry, ite_true, sub_res]
  by_cases h : x = y
  · subst h; simp
  · have : x - y ≠ 0#n := by
      intro h'; apply h
      exact (BitVec.sub_eq_iff_eq_add.mp h').trans (by simp)
    show (x - y == 0#n) = (x == y)
    rw [beq_false_of_ne this, beq_false_of_ne h]

theorem sub_lo (n : Nat) (x y : BitVec n) : (!(Arm64.subFlags x y).2.c) = x.ult y := by
  simp only [Arm64.subFlags, addWithCarry, ite_true, BitVec.toNat_ofNat, BitVec.toNat_not,
    BitVec.ult]
  have := y.isLt
  have := x.isLt
  by_cases h : x.toNat < y.toNat
  · have : (x.toNat + (2 ^ n - 1 - y.toNat) + 1) % 2 ^ n = x.toNat + (2 ^ n - 1 - y.toNat) + 1 :=
      Nat.mod_eq_of_lt (by omega)
    simp [this, h]
  · have : (x.toNat + (2 ^ n - 1 - y.toNat) + 1) % 2 ^ n ≠
        x.toNat + (2 ^ n - 1 - y.toNat) + 1 := by
      intro h'
      have := Nat.mod_lt (x.toNat + (2 ^ n - 1 - y.toNat) + 1) (Nat.two_pow_pos n)
      omega
    simp [this, h]

private theorem toInt_not64 (y : BitVec 64) : (~~~y).toInt = -y.toInt - 1 := by
  rw [BitVec.toInt_not, BitVec.toInt_eq_toNat_cond]
  have := y.isLt
  rw [Int.bmod_def]
  simp only [Nat.reducePow]
  split <;> split <;> omega

private theorem toInt_not32 (y : BitVec 32) : (~~~y).toInt = -y.toInt - 1 := by
  rw [BitVec.toInt_not, BitVec.toInt_eq_toNat_cond]
  have := y.isLt
  rw [Int.bmod_def]
  simp only [Nat.reducePow]
  split <;> split <;> omega

theorem sub_lt64 (x y : BitVec 64) :
    ((Arm64.subFlags x y).2.n != (Arm64.subFlags x y).2.v) = x.slt y := by
  simp only [Arm64.subFlags, addWithCarry, ite_true, sub_res, BitVec.slt, BitVec.msb_eq_toInt,
    toInt_not64, BitVec.toInt_sub]
  have h1 := BitVec.le_toInt x
  have h2 := BitVec.toInt_lt (x := x)
  have h3 := BitVec.le_toInt y
  have h4 := BitVec.toInt_lt (x := y)
  simp only [Nat.reducePow, Nat.reduceSub] at h1 h2 h3 h4 ⊢
  rw [Int.bmod_def]
  rw [Bool.eq_iff_iff]
  split <;> simp only [bne_iff_ne, ne_eq, decide_eq_true_eq] <;> rw [Bool.eq_iff_iff] <;>
    simp only [bne_iff_ne, ne_eq, decide_eq_true_eq] <;> omega

theorem sub_lt32 (x y : BitVec 32) :
    ((Arm64.subFlags x y).2.n != (Arm64.subFlags x y).2.v) = x.slt y := by
  simp only [Arm64.subFlags, addWithCarry, ite_true, sub_res, BitVec.slt, BitVec.msb_eq_toInt,
    toInt_not32, BitVec.toInt_sub]
  have h1 := BitVec.le_toInt x
  have h2 := BitVec.toInt_lt (x := x)
  have h3 := BitVec.le_toInt y
  have h4 := BitVec.toInt_lt (x := y)
  simp only [Nat.reducePow, Nat.reduceSub] at h1 h2 h3 h4 ⊢
  rw [Int.bmod_def]
  rw [Bool.eq_iff_iff]
  split <;> simp only [bne_iff_ne, ne_eq, decide_eq_true_eq] <;> rw [Bool.eq_iff_iff] <;>
    simp only [bne_iff_ne, ne_eq, decide_eq_true_eq] <;> omega

/-! ## Conditions on `SUBS` flags -/

/-- The conditions of `Equal` … `LessEqualU` on the flags of `SUBS x y`, as Phase 1's
comparisons, given the signed `N ≠ V` (`hlt`). -/
theorem cond_sub {n : Nat} (x y : BitVec n)
    (hlt : ((Arm64.subFlags x y).2.n != (Arm64.subFlags x y).2.v) = x.slt y) :
    Cond.eq.onVal (Arm64.subFlags x y).2.toVal = some (x == y) ∧
    Cond.ne.onVal (Arm64.subFlags x y).2.toVal = some (x != y) ∧
    Cond.lt.onVal (Arm64.subFlags x y).2.toVal = some (x.slt y) ∧
    Cond.le.onVal (Arm64.subFlags x y).2.toVal = some (x.sle y) ∧
    Cond.lo.onVal (Arm64.subFlags x y).2.toVal = some (x.ult y) ∧
    Cond.ls.onVal (Arm64.subFlags x y).2.toVal = some (x.ule y) := by
  have hz := sub_z n x y
  have hc := sub_lo n x y
  simp only [Cond.onVal, Flags.toVal, Val.flagBit, Cond.eval, Option.map_some, bind,
    Option.bind_some, pure]
  refine ⟨hz ▸ rfl, by rw [hz]; rfl, by rw [← hlt], ?_, by rw [← hc], ?_⟩
  · have hle : x.sle y = (x.slt y || x == y) := by
      rw [Bool.eq_iff_iff]
      simp only [BitVec.sle, BitVec.slt, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq,
        ← BitVec.toInt_inj]
      omega
    rw [hle, ← hlt, ← hz]
    cases (Arm64.subFlags x y).2.n <;> cases (Arm64.subFlags x y).2.v <;>
      cases (Arm64.subFlags x y).2.z <;> rfl
  · have hle : x.ule y = (x.ult y || x == y) := by
      rw [Bool.eq_iff_iff]
      simp only [BitVec.ule, BitVec.ult, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq,
        ← BitVec.toNat_inj]
      omega
    rw [hle, ← hc, ← hz]
    cases (Arm64.subFlags x y).2.c <;> cases (Arm64.subFlags x y).2.z <;> rfl

end GoFV.Proof.Low.Rules
