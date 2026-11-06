import GoFV.Proof.Low.Rules.Peep

/-!
# Lowering rule lemmas: compares with a negated immediate (`ARM64.rules:597`, `598`)

`(CMPWconst [c] y) && c < 0 && c != -1<<31 => (CMNWconst [-c] y)`, its converse on `CMNWconst`
(`598`), and `(CMNconst [c] y) && c < 0 && c != -1<<63 => (CMPconst [-c] y)` (`597`): `SUBS x, k`
and `ADDS x, -k` give the same result and `NZCV` when `k` is neither 0 nor `intMin`
(`subFlags_eq_cmn`: the carry of `x + ~k + 1` is that of `x + (2^n - k)`, the signed sum alike),
and so the same ghost sign `g` (`Arm64.cmpRes`).

False under the semantics, so not proven: `(CMPconst [c] y) && c < 0 && c != -1<<63 =>
(CMNconst [-c] y)` (`597`, the `CMPconst` form) and the shifted-operand compares
`(CMP x0 x1:(SLLconst [c] y)) => (CMPshiftLL x0 y [c])`, `(CMP x0:(SLLconst [c] y) x1) =>
(InvertFlags (CMPshiftLL x1 y [c]))` and their `SRL`/`SRA` forms (`1463-1468`): `CMP` compares a
pointer without a concrete address with an integer as unequal (`Arm64.cmp`, `Z` clear), which
`CMN`/`CMPshift*` (registers only, `Arm64.cmp1`/`cmp2`) leave `poison`; a 64-bit word may hold such
a pointer (`Val.hasTy`).
-/

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules GoFV.Proof.Low
open GoFV.Rules.Generated.ARM64

/-- `SUBS x, k` is `ADDS x, -k` when `k` is neither 0 nor `intMin`. -/
theorem subFlags_eq_cmn {n : Nat} (x y : BitVec n) (h0 : y ≠ 0) (hm : y ≠ BitVec.intMin n) :
    Arm64.subFlags x y = addWithCarry x (-y) false := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact absurd (BitVec.eq_of_toNat_eq (by have := y.isLt; simp at this; simp [this])) h0
  have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← Nat.pow_succ']; congr 1; omega
  have hlt := y.isLt
  have hy : 0 < y.toNat := by
    rcases Nat.eq_zero_or_pos y.toNat with h | h
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h)) h0
    · exact h
  have hmn : y.toNat ≠ 2 ^ (n - 1) := fun h =>
    hm (BitVec.eq_of_toNat_eq (by rw [h, BitVec.toNat_intMin_of_pos hn]))
  have hnot : (~~~y).toNat = 2 ^ n - 1 - y.toNat := BitVec.toNat_not
  have hneg : (-y).toNat = 2 ^ n - y.toNat := by
    rw [BitVec.toNat_neg, Nat.mod_eq_of_lt (by omega)]
  have hu : (~~~y).toNat + 1 = (-y).toNat := by omega
  have hs : (~~~y).toInt + 1 = (-y).toInt := by
    rw [BitVec.toInt_eq_toNat_cond (~~~y), BitVec.toInt_eq_toNat_cond (-y), hnot, hneg]
    split <;> split <;> omega
  have hv : x.toInt + (~~~y).toInt + ((1 : Nat) : Int) = x.toInt + (-y).toInt + ((0 : Nat) : Int) := by
    push_cast; omega
  simp only [Arm64.subFlags, addWithCarry, ite_true, Bool.false_eq_true, ite_false]
  rw [show x.toNat + (~~~y).toNat + 1 = x.toNat + (-y).toNat + 0 by omega, hv]

/-- A negative 32-bit immediate other than the minimum: neither 0 nor `intMin`. -/
theorem ofInt32_neg_ok {c : Int} (h1 : c < 0) (h2 : c ≠ -2147483648) (h3 : -2147483648 ≤ c) :
    BitVec.ofInt 32 c ≠ 0 ∧ BitVec.ofInt 32 c ≠ BitVec.intMin 32 := by
  have ht : (BitVec.ofInt 32 c).toInt = c := by
    rw [BitVec.toInt_ofInt]; exact Int.bmod_eq_of_le (by omega) (by omega)
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [h] at ht; simp at ht; omega
  · rw [h] at ht; simp [BitVec.toInt_intMin] at ht; omega

/-- A 32-bit immediate is the `int32` value of its auxint. -/
theorem imm32_wrapInt (k : Int64) : Arm64.imm32 k = BitVec.ofInt 32 (wrapInt 32 true k.toInt) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Arm64.imm32, BitVec.toNat_ofInt, wrapInt, ite_true]
  rw [Int.bmod_emod]

/-- `ARM64.rules:598`: `(CMPWconst [c] y) && c < 0 && c != -1<<31 => (CMNWconst [-c] y)` -/
theorem r_ARM64_598_2_sound : ArmRule.Checked r_ARM64_598_2 := by
  left; arm_unfold; arm_norm
  obtain ⟨h1, h2⟩ := hcond
  simp only [decide_eq_true_eq] at h1
  have hr := (wrapInt_true_range 32 (e.auxInt []).toInt).1
  obtain ⟨n0, nm⟩ := ofInt32_neg_ok h1 h2 (by simpa using hr)
  rw [imm32_wrap, imm32_wrapInt, BitVec.ofInt_neg]
  have : (fun x => Arm64.subFlags x (BitVec.ofInt 32 (wrapInt 32 true (e.auxInt []).toInt))) =
      fun x => addWithCarry x (-BitVec.ofInt 32 (wrapInt 32 true (e.auxInt []).toInt)) false :=
    funext fun x => subFlags_eq_cmn _ _ n0 nm
  rw [this]; exact Refines.refl _

/-- `CMN` with a register is `CMP` with its negation, when the register is neither 0 nor `intMin`. -/
theorem cmn_eq_subFlags_neg {n : Nat} (x k : BitVec n) (h0 : k ≠ 0) (hm : k ≠ BitVec.intMin n) :
    addWithCarry x k false = Arm64.subFlags x (-k) := by
  have n0 : -k ≠ 0 := fun h => h0 (by simpa using congrArg (- ·) h)
  have nm : -k ≠ BitVec.intMin n := fun h => hm (by simpa [BitVec.neg_intMin] using congrArg (- ·) h)
  rw [subFlags_eq_cmn x (-k) n0 nm, BitVec.neg_neg]

/-- `ARM64.rules:598`: `(CMNWconst [c] y) && c < 0 && c != -1<<31 => (CMPWconst [-c] y)` -/
theorem r_ARM64_598_sound : ArmRule.Checked r_ARM64_598 := by
  left; arm_unfold; arm_norm
  obtain ⟨h1, h2⟩ := hcond
  simp only [decide_eq_true_eq] at h1
  have hr := (wrapInt_true_range 32 (e.auxInt []).toInt).1
  obtain ⟨n0, nm⟩ := ofInt32_neg_ok h1 h2 (by simpa using hr)
  rw [imm32_wrap, imm32_wrapInt, BitVec.ofInt_neg]
  have : (fun x => addWithCarry x (BitVec.ofInt 32 (wrapInt 32 true (e.auxInt []).toInt)) false) =
      fun x => Arm64.subFlags x (-BitVec.ofInt 32 (wrapInt 32 true (e.auxInt []).toInt)) :=
    funext fun x => cmn_eq_subFlags_neg _ _ n0 nm
  rw [this]; exact Refines.refl _

/-- `ARM64.rules:597`: `(CMNconst [c] y) && c < 0 && c != -1<<63 => (CMPconst [-c] y)` -/
theorem r_ARM64_597_sound : ArmRule.Checked r_ARM64_597 := by
  left; arm_unfold; arm_norm
  obtain ⟨h1, h2⟩ := hcond
  simp only [decide_eq_true_eq] at h1
  have hk := (e.auxInt []).le_toInt
  have hk2 := (e.auxInt []).toInt_lt
  have hK : (BitVec.ofInt 64 (e.auxInt []).toInt).toInt = (e.auxInt []).toInt := by
    rw [BitVec.toInt_ofInt]; exact Int.bmod_eq_of_le (by omega) (by omega)
  have n0 : BitVec.ofInt 64 (e.auxInt []).toInt ≠ 0 := fun h => by rw [h] at hK; simp at hK; omega
  have nm : BitVec.ofInt 64 (e.auxInt []).toInt ≠ BitVec.intMin 64 := fun h => by
    rw [h] at hK; simp [BitVec.toInt_intMin] at hK; omega
  rw [BitVec.ofInt_neg]
  simp only [Arm64.cmp1, Arm64.cmp]
  cases hy : Arm64.reg (e.leaf [0]) with
  | none => rw [retypeL_poison]; exact .poison _
  | some x =>
    simp only [Arm64.reg, BitVec.setWidth_eq]
    rw [cmn_eq_subFlags_neg x _ n0 nm]; exact Refines.refl _

end GoFV.Proof.Low.Rules
