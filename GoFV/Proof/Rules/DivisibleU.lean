import GoFV.Proof.Rules.DivisibleInv
import GoFV.Proof.Rules.NonVacuous
import GoFV.Rules.Generated.Divisible.Values00

/-!
# `divisible.rules`: unsigned divisibility by a rotated product (#69)

`x == (x / c) * c` (`Div*u`) becomes `rotateRight(x * m, k) ≤ max` (`RotateLeft` by `w - k`)
with `udivisible(c) = (k, m, max)`: `c = d0 * 2^k`, `d0` odd, `m * d0 ≡ 1 (mod 2^w)`,
`max = ⌊(2^w - 1) / c⌋` (`udiv_rot`, any width `w`). The rules hold for every nonzero `c`
(`udivisibleOK` only selects the profitable ones); for `c = 0` the source divides by zero.
-/

namespace GoFV.Proof.Rules.Divisible

open GoFV.Rules

theorem mul_inv_one {w : Nat} (hw : 0 < w) (d0 m : Nat) (hmd : m * d0 % 2 ^ w = 1) :
    BitVec.ofNat w m * BitVec.ofNat w d0 = 1#w := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, ← Nat.mul_mod, hmd]
  exact (Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))).symm

/-- Rotating `q * 2^k` right by `k` (left by `w - k`) gives `q`. -/
theorem rot_shl {w k q : Nat} (hk : k < w) (hq : q * 2 ^ k < 2 ^ w) :
    (BitVec.ofNat w (q * 2 ^ k)).rotateLeft (w - k) = BitVec.ofNat w q := by
  have hq' : q < 2 ^ w := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right q (Nat.two_pow_pos k)) hq
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_rotateLeft, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq,
    Nat.mod_eq_of_lt hq']
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · simp only [Nat.sub_zero, Nat.mod_self, Nat.shiftLeft_zero, Nat.pow_zero, Nat.mul_one,
      Nat.mod_eq_of_lt hq', Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hq', Nat.or_zero]
  · have hr : (w - k) % w = w - k := Nat.mod_eq_of_lt (by omega)
    rw [hr, show w - (w - k) = k by omega, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
      Nat.mul_assoc, ← Nat.pow_add, show k + (w - k) = w by omega, Nat.mul_mod_left,
      Nat.mul_div_cancel _ (Nat.two_pow_pos k), Nat.zero_or]

/-- Divisibility by `d = d0 * 2^k` (`d0` odd, `m` its inverse mod `2^w`) as a rotated product. -/
theorem udiv_rot {w : Nat} (x C : BitVec w) (d0 kk m : Nat) (hd : C.toNat = d0 * 2 ^ kk)
    (hd0 : d0 % 2 = 1) (hmd : m * d0 % 2 ^ w = 1) :
    (x == x / C * C) = ((x * BitVec.ofNat w m).rotateLeft
      (BitVec.ofNat w w - BitVec.ofNat w kk).toNat).ule (BitVec.ofNat w ((2 ^ w - 1) / (d0 * 2 ^ kk))) := by
  have hC := C.isLt
  have hpk := Nat.two_pow_pos kk
  have hdpos : 0 < d0 * 2 ^ kk := Nat.mul_pos (by omega) hpk
  have hkd : 2 ^ kk ≤ d0 * 2 ^ kk := Nat.le_mul_of_pos_left _ (by omega)
  have hkw : 2 ^ kk < 2 ^ w := by omega
  have hk : kk < w := (Nat.pow_lt_pow_iff_right (a := 2) (by decide)).mp hkw
  have hw : w < 2 ^ w := Nat.lt_two_pow_self
  have hamt : (BitVec.ofNat w w - BitVec.ofNat w kk).toNat = w - kk := by
    have := GoFV.Proof.Rules.toNat_ofNat_sub (BitVec.ofNat w kk) hw
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
    rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hamt]
  generalize hdd : d0 * 2 ^ kk = d at *
  have hMD := mul_inv_one (w := w) (by omega) d0 m hmd
  -- forward: a multiple of `d` maps to its quotient
  have fwd : ∀ q, q * d < 2 ^ w →
      (BitVec.ofNat w (q * d) * BitVec.ofNat w m).rotateLeft (w - kk) = BitVec.ofNat w q := by
    intro q hq
    have hq2 : q * 2 ^ kk < 2 ^ w := Nat.lt_of_le_of_lt (by rw [← hdd, Nat.mul_left_comm]; exact Nat.le_mul_of_pos_left _ (by omega)) hq
    have : BitVec.ofNat w (q * d) * BitVec.ofNat w m = BitVec.ofNat w (q * 2 ^ kk) := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, ← Nat.mul_mod]
      rw [← hdd, show q * (d0 * 2 ^ kk) * m = q * 2 ^ kk * (m * d0) by
        rw [Nat.mul_comm m d0, Nat.mul_comm d0 (2 ^ kk)]; simp only [Nat.mul_assoc, Nat.mul_left_comm],
        Nat.mul_mod, hmd, Nat.mul_one, Nat.mod_mod]
    rw [this, rot_shl hk hq2]
  -- the rotated product is injective in `x`
  have inj : ∀ y z : BitVec w, (y * BitVec.ofNat w m).rotateLeft (w - kk) =
      (z * BitVec.ofNat w m).rotateLeft (w - kk) → y = z := by
    intro y z h
    have h2 := congrArg (fun v => (v.rotateLeft kk) * BitVec.ofNat w d0) h
    simp only [GoFV.Proof.Rules.rotateLeft_rotateLeft] at h2
    rw [GoFV.Proof.Rules.rotateLeft_eq_self _ (by rw [show w - kk + kk = w by omega]; exact Nat.mod_self w),
      GoFV.Proof.Rules.rotateLeft_eq_self _ (by rw [show w - kk + kk = w by omega]; exact Nat.mod_self w),
      BitVec.mul_assoc, BitVec.mul_assoc, hMD, BitVec.mul_one, BitVec.mul_one] at h2
    exact h2
  have hx := x.isLt
  rw [Bool.eq_iff_iff, beq_iff_eq, BitVec.ule, decide_eq_true_iff]
  have hxd : (x / C * C).toNat = x.toNat / d * d := by
    rw [BitVec.toNat_mul, BitVec.toNat_udiv, hd]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) hx)
  constructor
  · intro h
    have hx' : x = BitVec.ofNat w (x.toNat / d * d) := by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, ← hxd, ← h, Nat.mod_eq_of_lt hx]
    rw [hx', fwd _ (Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) hx), BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    have h1 : x.toNat / d * d ≤ 2 ^ w - 1 := by omega
    have h2 : x.toNat / d ≤ (2 ^ w - 1) / d := (Nat.le_div_iff_mul_le hdpos).mpr h1
    have h3 : (2 ^ w - 1) / d < 2 ^ w := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    rw [Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt (by omega)]
    exact h2
  · intro h
    generalize hR : (x * BitVec.ofNat w m).rotateLeft (w - kk) = R at h
    have h3 : (2 ^ w - 1) / d < 2 ^ w := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h3] at h
    have h1 : R.toNat * d ≤ 2 ^ w - 1 := (Nat.le_div_iff_mul_le hdpos).mp h
    have h4 := fwd R.toNat (by omega)
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at h4
    have h5 := inj _ _ (h4.trans hR.symm)
    have h6 : x.toNat = R.toNat * d := by
      have h7 : R.toNat * d < 2 ^ w := by omega
      rw [← h5, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h7]
    apply BitVec.eq_of_toNat_eq
    rw [hxd, h6, Nat.mul_div_cancel _ hdpos]

theorem udiv_rot_ne {w : Nat} (x C : BitVec w) (d0 kk m : Nat) (hd : C.toNat = d0 * 2 ^ kk)
    (hd0 : d0 % 2 = 1) (hmd : m * d0 % 2 ^ w = 1) :
    (x != x / C * C) = (BitVec.ofNat w ((2 ^ w - 1) / (d0 * 2 ^ kk))).ult ((x * BitVec.ofNat w m).rotateLeft
      (BitVec.ofNat w w - BitVec.ofNat w kk).toNat) := by
  rw [bne, udiv_rot x C d0 kk m hd hd0 hmd, BitVec.ule, BitVec.ult, Bool.eq_iff_iff]
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le, decide_eq_true_eq]
end GoFV.Proof.Rules.Divisible

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

set_option hygiene false in
/-- `rule_unfold`, the `udivisible` call split into failure (the divisor is `0`: the source is
`poison`) and success (`udivisible_ok`), then `udiv_rot`. -/
macro "divisible_u" : tactic => `(tactic| (
  rule_unfold
  (try rule_ands)
  (try rule_clear_oracle)
  (try clear hcond)
  divisible_gen
  rcases U with s | ⟨k, m, mx⟩
  · have hz := GoFV.Proof.Rules.Divisible.udivisible_err hU
    clear hU
    divisible_gen_rhs
    divisible_rest
  · obtain ⟨kk, d0, rfl, hd, hd0, hmd, rfl⟩ :=
      GoFV.Proof.Rules.Divisible.udivisible_ok (by decide) (by decide) hU
    clear hU
    divisible_rest
    all_goals first
      | exact GoFV.Proof.Rules.Divisible.udiv_rot _ _ d0 kk m hd hd0 hmd
      | exact GoFV.Proof.Rules.Divisible.udiv_rot_ne _ _ d0 kk m hd hd0 hmd))

theorem r_divisible_32_sound : Rule.Sound GoFV.Rules.Generated.Divisible.r_divisible_32 := by
  divisible_u

theorem r_divisible_48_sound : Rule.Sound GoFV.Rules.Generated.Divisible.r_divisible_48 := by
  divisible_u

theorem r_divisible_64_sound : Rule.Sound GoFV.Rules.Generated.Divisible.r_divisible_64 := by
  divisible_u

theorem r_divisible_80_sound : Rule.Sound GoFV.Rules.Generated.Divisible.r_divisible_80 := by
  divisible_u

/-- `divisible.rules:48`: `(Eq16 x (Mul16 (Div16u x (Const16 [c])) (Const16 [c])))` at `x = 14`,
`c = 7`. -/
theorem inst_r_divisible_48 : Rule.Inst GoFV.Rules.Generated.Divisible.r_divisible_48
    (PEnv.ofLists [([0], .i16 14), ([0, 0, 1], .i16 14)] [([], .bool)] (.int .w16)
      [([1, 0, 1], 7), ([1, 1], 7)])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Divisible.r_divisible_48]
  rule_eval
  -- the `x.Op`/`div.Uses` field reads (string-literal matches) by evaluation
  rfl

end GoFV.Proof.Rules
