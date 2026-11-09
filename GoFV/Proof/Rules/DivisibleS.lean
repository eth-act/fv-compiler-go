import GoFV.Proof.Rules.DivisibleU
import GoFV.Proof.Rules.DivmodSMagic
import GoFV.Rules.Generated.Divisible.Values00

variable [GoFV.SSA.Sem.Addrs]

/-!
# `divisible.rules`: signed divisibility by a rotated product (#69)

`x == (x / c) * c` (`Div*`, signed) becomes `rotateRight(x * m + a, k) ≤ max` (`RotateLeft` by
`w - k`) with `sdivisible(c) = (k, m, a, max)`: `c = d0 * 2^k`, `d0` odd, `m * d0 ≡ 1 (mod 2^w)`,
`a = A * 2^k` and `max = 2 * A` for `A = ⌊(2^(w-1) - 1) / c⌋` (`sdivisible_ok`). `sdiv_rot`: a
multiple `c * r` of `c` (`|r| ≤ A`) maps to `A + r`, and the map is injective. The rules need
`sdivisibleOK(c)`: `c` positive and not a power of two (so `d0 > 1` and `-2^(w-1)` is not a
multiple of `c`). For `c = 0` (the helper fails) the source divides by zero.
-/

namespace GoFV.Proof.Rules.Divisible

open GoFV.Rules

/-- Clearing the low `t` bits of a 64-bit number (`x & -(1 << t)` in `uint64`). -/
theorem and_negPow {X t : Nat} (hX : X < 2 ^ 64) (ht : t < 64) :
    X &&& (2 ^ 64 - 2 ^ t) % 2 ^ 64 = X / 2 ^ t * 2 ^ t := by
  have hpt := Nat.two_pow_pos t
  rw [Nat.mod_eq_of_lt (by omega), ← Nat.shiftRight_eq_div_pow, ← Nat.shiftLeft_eq,
    show 2 ^ 64 - 2 ^ t = (2 ^ (64 - t) - 1) <<< t by
      rw [Nat.shiftLeft_eq, Nat.sub_mul, Nat.one_mul, ← Nat.pow_add, Nat.sub_add_cancel (by omega)]]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_shiftRight,
    Nat.testBit_two_pow_sub_one]
  by_cases hi : t ≤ i
  · rw [show t + (i - t) = i by omega]
    by_cases h64 : i < 64
    · simp [hi, show i - t < 64 - t by omega]
    · have : X.testBit i = false :=
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hX (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [this]
  · simp [show ¬ i ≥ t by omega]

/-- A failing `sdivisible n c`: the divisor's low bits are zero. -/
theorem sdivisible_err {n : Nat} {c : Int} {s : String} (hn : n ≤ 64)
    (h : Magic.sdivisible n c = .error s) : BitVec.ofInt n c = 0 := by
  unfold Magic.sdivisible at h
  generalize hdd : (c.emod (2 ^ 64)).toNat = d at h
  have hd : d = 0 := by
    by_cases hd : d = 0
    · exact hd
    · simp [hd, pure, Except.pure] at h
  subst hd
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofInt, show (0 : BitVec n).toNat = 0 by simp]
  have h0 : c % ((2 ^ 64 : Nat) : Int) = 0 := by
    have := Int.emod_nonneg c (show ((2 ^ 64 : Nat) : Int) ≠ 0 by decide)
    rw [show c.emod (2 ^ 64) = c % ((2 ^ 64 : Nat) : Int) from rfl] at hdd
    omega
  have hdvd : ((2 ^ n : Nat) : Int) ∣ ((2 ^ 64 : Nat) : Int) :=
    Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow 2 hn)
  rw [← Int.emod_emod_of_dvd c hdvd, h0, Int.zero_emod]
  rfl

/-- What `sdivisible n c = .ok (k, m, a, max)` gives on a constant accepted by `sdivisibleOK`
in the signed range: `c = d0 * 2^k` (`d0 > 1` odd), `m` the inverse of `d0` modulo `2^n`,
`a = A * 2^k`, `max = 2 * A` for `A = ⌊(2^(n-1) - 1) / c⌋`. -/
theorem sdivisible_ok {n : Nat} {c k : Int} {m a mx : Nat} (hn1 : 1 ≤ n) (hn : n ≤ 64)
    (hok : Magic.smagicOK c = true) (hc : c < 2 ^ (n - 1))
    (h : Magic.sdivisible n c = .ok (k, m, a, mx)) :
    ∃ kk d0 : Nat, k = kk ∧ c = ((d0 * 2 ^ kk : Nat) : Int) ∧ d0 % 2 = 1 ∧ 1 < d0 ∧
      m * d0 % 2 ^ n = 1 ∧ a = (2 ^ (n - 1) - 1) / (d0 * 2 ^ kk) * 2 ^ kk ∧
      mx = 2 * ((2 ^ (n - 1) - 1) / (d0 * 2 ^ kk)) := by
  simp only [Magic.smagicOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨h0, hnp⟩ := hok
  have hp63 : (2 : Int) ^ (n - 1) ≤ 2 ^ 63 := by
    have : 2 ^ (n - 1) ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
    exact_mod_cast this
  obtain ⟨hC0, hCp⟩ := GoFV.Proof.Rules.DivmodS.notPow2_spec h0 (by omega) hnp
  obtain ⟨C, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  simp only [Int.toNat_natCast] at hC0 hCp
  have hCn : C < 2 ^ (n - 1) := by exact_mod_cast hc
  have h63' : 2 ^ (n - 1) ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
  unfold Magic.sdivisible at h
  have hd : ((C : Int).emod (2 ^ 64)).toNat = C := by
    rw [show (C : Int).emod (2 ^ 64) = (C : Int) % 2 ^ 64 from rfl,
      Int.emod_eq_of_lt (by omega) (by omega)]
    rfl
  rw [hd] at h
  simp only [Nat.ne_of_gt hC0, ite_false, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  obtain ⟨he, hodd⟩ := trailingZeros_spec C hC0 (by omega)
  generalize trailingZeros C 64 = t at *
  generalize hD : C / 2 ^ t = d0 at he hodd
  have hpt := Nat.two_pow_pos t
  have ht : t < 64 := by
    have : 2 ^ t ≤ C := by rw [he]; exact Nat.le_mul_of_pos_left _ (by omega)
    exact (Nat.pow_lt_pow_iff_right (a := 2) (by decide)).mp (by omega)
  have hd1 : 1 < d0 := by
    rcases Nat.lt_or_ge 1 d0 with h1 | h1
    · exact h1
    · exact absurd (by rw [he, show d0 = 1 by omega, Nat.one_mul]) (hCp t)
  subst he
  have hsh : (d0 * 2 ^ t) >>> t = d0 := by
    rw [Nat.shiftRight_eq_div_pow, hD]
  have hmask : (2 ^ n - 1) >>> 1 = 2 ^ (n - 1) - 1 := by
    have : 2 ^ n = 2 * 2 ^ (n - 1) := by
      rw [← Nat.pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel hn1]
    rw [Nat.shiftRight_eq_div_pow, this]
    have := Nat.two_pow_pos (n - 1)
    omega
  have hQ : (2 ^ (n - 1) - 1) / d0 < 2 ^ 64 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
  rw [hsh, hmask, and_negPow hQ ht, Nat.div_div_eq_div_mul]
  refine ⟨t, d0, rfl, rfl, hodd, hd1, inv64_mask hn1 hn hodd, rfl, ?_⟩
  have hA : (2 ^ (n - 1) - 1) / (d0 * 2 ^ t) * 2 ^ t ≤ 2 ^ (n - 1) - 1 := by
    rw [Nat.mul_comm d0]
    calc (2 ^ (n - 1) - 1) / (2 ^ t * d0) * 2 ^ t
        ≤ (2 ^ (n - 1) - 1) / (2 ^ t * d0) * (2 ^ t * d0) :=
          Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (by omega))
      _ ≤ 2 ^ (n - 1) - 1 := Nat.div_mul_le_self _ _
  rw [Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow, ← Nat.mul_assoc,
    Nat.mul_div_cancel _ hpt]

/-- Truncated division by a positive `c` multiplies back to the dividend iff `c` divides it. -/
theorem sdiv_mul_eq {w : Nat} (hw : 1 ≤ w) (x C : BitVec w) (c : Int) (hc : 0 < c)
    (hC : C.toInt = c) : (x == x.sdiv C * C) = decide (x.toInt.tmod c = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← BitVec.toInt_inj, BitVec.toInt_mul,
    BitVec.toInt_sdiv, hC, Int.bmod_mul_bmod]
  have hlo := BitVec.le_toInt x
  have hhi := BitVec.toInt_lt (x := x)
  have hN : ((2 ^ w : Nat) : Int) = 2 * (2 : Int) ^ (w - 1) := by
    rw [Int.natCast_pow, ← Int.pow_succ', Nat.sub_add_cancel hw]; rfl
  generalize (2 : Int) ^ (w - 1) = N at *
  generalize x.toInt = T at *
  have h1 := Int.tdiv_mul_add_tmod T c
  have h2 := Int.tmod_lt_of_pos T hc
  have h3 := Int.lt_tmod_of_pos T hc
  have h4 : 0 ≤ T → 0 ≤ T.tmod c ∧ 0 ≤ T.tdiv c * c := fun hT =>
    ⟨Int.tmod_nonneg c hT, Int.mul_nonneg (Int.tdiv_nonneg hT (by omega)) (by omega)⟩
  have h5 : T < 0 → T.tmod c ≤ 0 ∧ T.tdiv c * c ≤ 0 := by
    intro hT
    have m1 := Int.tmod_nonneg c (show 0 ≤ -T by omega)
    have m2 := Int.mul_nonneg (Int.tdiv_nonneg (show 0 ≤ -T by omega) (show 0 ≤ c by omega))
      (show 0 ≤ c by omega)
    rw [Int.neg_tmod] at m1
    rw [Int.neg_tdiv, Int.neg_mul] at m2
    omega
  generalize T.tdiv c * c = P at *
  generalize T.tmod c = r at *
  rw [Int.bmod_eq_of_le (by rw [hN]; omega) (by rw [hN]; omega)]
  omega

/-- Signed divisibility by `c = d0 * 2^k` (`d0 > 1` odd, `m` its inverse mod `2^w`) as a rotated
product, for `0 < c < 2^(w-1)`. -/
theorem sdiv_rot_core {w : Nat} (hw : 1 ≤ w) (x : BitVec w) (d0 kk m : Nat)
    (hc : d0 * 2 ^ kk < 2 ^ (w - 1)) (hd0 : d0 % 2 = 1) (hd1 : 1 < d0)
    (hmd : m * d0 % 2 ^ w = 1) :
    (x == x.sdiv (BitVec.ofNat w (d0 * 2 ^ kk)) * BitVec.ofNat w (d0 * 2 ^ kk)) =
      ((x * BitVec.ofNat w m + BitVec.ofNat w ((2 ^ (w - 1) - 1) / (d0 * 2 ^ kk) * 2 ^ kk)).rotateLeft
        (w - kk)).ule (BitVec.ofNat w (2 * ((2 ^ (w - 1) - 1) / (d0 * 2 ^ kk)))) := by
  have hpk := Nat.two_pow_pos kk
  have hW : 2 ^ w = 2 * 2 ^ (w - 1) := by
    rw [← Nat.pow_succ', Nat.succ_eq_add_one, Nat.sub_add_cancel hw]
  have hkd : 2 ^ kk ≤ d0 * 2 ^ kk := Nat.le_mul_of_pos_left _ (by omega)
  have hk : kk < w := by
    have : 2 ^ kk < 2 ^ w := by omega
    exact (Nat.pow_lt_pow_iff_right (a := 2) (by decide)).mp this
  have hMD := mul_inv_one (w := w) (by omega) d0 m hmd
  have hmd' : ((2 ^ w : Nat) : Int) ∣ (m : Int) * d0 - 1 := by
    have h := Nat.div_add_mod (m * d0) (2 ^ w)
    rw [hmd] at h
    refine ⟨((m * d0 / 2 ^ w : Nat) : Int), ?_⟩
    have h' : ((2 ^ w * (m * d0 / 2 ^ w) + 1 : Nat) : Int) = ((m * d0 : Nat) : Int) := by rw [h]
    push_cast at h' ⊢
    omega
  obtain ⟨t, ht⟩ := hmd'
  have hlo := BitVec.le_toInt x
  have hhi := BitVec.toInt_lt (x := x)
  have hNi : (2 : Int) ^ (w - 1) = ((2 ^ (w - 1) : Nat) : Int) := by simp
  rw [hNi] at hlo hhi
  generalize hA : (2 ^ (w - 1) - 1) / (d0 * 2 ^ kk) = A
  generalize hcd : d0 * 2 ^ kk = c at *
  generalize hN : 2 ^ (w - 1) = N at *
  have hcpos : 0 < c := by omega
  -- `c * A ≤ N - 1 < c * (A + 1)`
  have hA1 : A * c ≤ N - 1 := by rw [← hA]; exact Nat.div_mul_le_self _ _
  have hA2 : N - 1 < A * c + c := by
    rw [← hA]
    have := Nat.div_add_mod' (N - 1) c
    have := Nat.mod_lt (N - 1) hcpos
    omega
  have hAk : A * 2 ^ kk ≤ A * c := Nat.mul_le_mul_left _ (by omega)
  have hA0 : A ≤ A * c := Nat.le_mul_of_pos_right _ hcpos
  have h2A : 2 * A < 2 ^ w := by omega
  have hC : (BitVec.ofNat w c).toInt = c := by
    rw [BitVec.toInt_ofNat']
    have e : ((2 ^ w : Nat) : Int) = 2 * (N : Int) := by rw [hW]; push_cast; rfl
    apply Int.bmod_eq_of_le <;> rw [e] <;> omega
  rw [sdiv_mul_eq hw x _ c (by omega) hC]
  -- forward: `c * r` maps to `A + r`
  have fwd : ∀ r : Int, -(A : Int) ≤ r → r ≤ A →
      (BitVec.ofInt w (c * r) * BitVec.ofNat w m + BitVec.ofNat w (A * 2 ^ kk)).rotateLeft
        (w - kk) = BitVec.ofNat w (A + r).toNat := by
    intro r hr1 hr2
    have e : BitVec.ofInt w (c * r) * BitVec.ofNat w m + BitVec.ofNat w (A * 2 ^ kk) =
        BitVec.ofNat w ((A + r).toNat * 2 ^ kk) := by
      rw [← BitVec.ofInt_natCast w m, ← BitVec.ofInt_natCast w (A * 2 ^ kk),
        ← BitVec.ofInt_natCast w ((A + r).toNat * 2 ^ kk), ← BitVec.ofInt_mul, ← BitVec.ofInt_add]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofInt, BitVec.toNat_ofInt]
      congr 1
      apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
      apply Int.emod_eq_zero_of_dvd
      refine ⟨2 ^ kk * r * t, ?_⟩
      have hr : (((A + r).toNat : Nat) : Int) = A + r := Int.toNat_of_nonneg (by omega)
      rw [← hcd]
      push_cast at hr ht ⊢
      rw [hr]
      have hm : (m : Int) * d0 = 1 + 2 ^ w * t := by omega
      grind
    rw [e, rot_shl hk]
    have : (A + r).toNat ≤ 2 * A := by omega
    calc (A + r).toNat * 2 ^ kk ≤ 2 * A * 2 ^ kk := Nat.mul_le_mul_right _ this
      _ < 2 ^ w := by rw [Nat.mul_assoc]; omega
  -- the rotated product is injective
  have inj : ∀ y z : BitVec w,
      (y * BitVec.ofNat w m + BitVec.ofNat w (A * 2 ^ kk)).rotateLeft (w - kk) =
        (z * BitVec.ofNat w m + BitVec.ofNat w (A * 2 ^ kk)).rotateLeft (w - kk) → y = z := by
    intro y z h
    have h2 := congrArg (fun v => (v.rotateLeft kk - BitVec.ofNat w (A * 2 ^ kk)) *
      BitVec.ofNat w d0) h
    simp only [GoFV.Proof.Rules.rotateLeft_rotateLeft] at h2
    rw [GoFV.Proof.Rules.rotateLeft_eq_self _ (by rw [show w - kk + kk = w by omega]; exact Nat.mod_self w),
      GoFV.Proof.Rules.rotateLeft_eq_self _ (by rw [show w - kk + kk = w by omega]; exact Nat.mod_self w),
      BitVec.add_sub_cancel, BitVec.add_sub_cancel, BitVec.mul_assoc, BitVec.mul_assoc, hMD,
      BitVec.mul_one, BitVec.mul_one] at h2
    exact h2
  have hA2' : (N : Int) - 1 < A * c + c := by omega
  have hA1' : (A : Int) * c ≤ N - 1 := by
    have : ((A * c : Nat) : Int) ≤ ((N - 1 : Nat) : Int) := by exact_mod_cast hA1
    push_cast at this
    omega
  rw [Bool.eq_iff_iff, decide_eq_true_iff, BitVec.ule, decide_eq_true_iff]
  constructor
  · intro h
    obtain ⟨r, hr⟩ := Int.dvd_iff_tmod_eq_zero.mpr h
    -- `-2^(w-1)` is no multiple of `c`
    have hne : (c : Int) * r ≠ -(N : Int) := by
      intro he
      have hdv : d0 ∣ 2 ^ (w - 1) := by
        refine ⟨2 ^ kk * r.natAbs, ?_⟩
        have := congrArg Int.natAbs he
        rw [Int.natAbs_mul, Int.natAbs_neg, Int.natAbs_natCast, Int.natAbs_natCast] at this
        rw [hN, ← this, ← hcd, Nat.mul_assoc]
      obtain ⟨t, ht⟩ := GoFV.Proof.Rules.DivmodS.dvd_two_pow hdv
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · rw [h0] at ht; omega
      · rw [ht, show t = (t - 1) + 1 by omega, Nat.pow_succ] at hd0; omega
    have hr1 : -(A : Int) ≤ r := by
      refine Int.not_lt.mp fun hlt => ?_
      have : (c : Int) * r ≤ c * (-((A : Int) + 1)) :=
        Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      rw [Int.mul_neg, Int.mul_add, Int.mul_one, Int.mul_comm (c : Int) A] at this
      omega
    have hr2 : r ≤ A := by
      refine Int.not_lt.mp fun hlt => ?_
      have : (c : Int) * ((A : Int) + 1) ≤ c * r :=
        Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      rw [Int.mul_add, Int.mul_one, Int.mul_comm (c : Int) A] at this
      omega
    have hx : x = BitVec.ofInt w (c * r) := by rw [← hr, BitVec.ofInt_toInt]
    rw [hx, fwd r hr1 hr2, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt h2A]
    omega
  · intro h
    generalize hR : (x * BitVec.ofNat w m + BitVec.ofNat w (A * 2 ^ kk)).rotateLeft (w - kk) = R at h
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h2A] at h
    have h4 := fwd ((R.toNat : Int) - A) (by omega) (by omega)
    rw [show ((A : Int) + ((R.toNat : Int) - A)).toNat = R.toNat by omega, BitVec.ofNat_toNat,
      BitVec.setWidth_eq] at h4
    have h5 := inj _ _ (h4.trans hR.symm)
    have hb : ((c : Int) * ((R.toNat : Int) - A)).bmod (2 ^ w) =
        (c : Int) * ((R.toNat : Int) - A) := by
      have e : ((2 ^ w : Nat) : Int) = 2 * (N : Int) := by rw [hW]; push_cast; rfl
      have b1 : (c : Int) * ((R.toNat : Int) - A) ≤ c * A :=
        Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      have b2 : (c : Int) * (-(A : Int)) ≤ c * ((R.toNat : Int) - A) :=
        Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
      rw [Int.mul_neg, Int.mul_comm (c : Int) A] at b2
      rw [Int.mul_comm (c : Int) A] at b1
      apply Int.bmod_eq_of_le <;> rw [e] <;> omega
    rw [← h5, BitVec.toInt_ofInt, hb]
    exact Int.dvd_iff_tmod_eq_zero.mp (Int.dvd_mul_right _ _)

/-- `sdiv_rot_core` in the shape of the rule goal: the `sdivisible w c` results `(k, m, a, max)`
for a constant `c` accepted by `sdivisibleOK` in the signed range. -/
theorem sdiv_rot {w : Nat} (hw : 1 ≤ w) (hw64 : w ≤ 64) (x : BitVec w) {c k : Int} {m a mx : Nat}
    (hok : Magic.smagicOK c = true) (hc : c < 2 ^ (w - 1))
    (hU : Magic.sdivisible w c = .ok (k, m, a, mx)) :
    (x == x.sdiv (BitVec.ofInt w c) * BitVec.ofInt w c) =
      ((x * BitVec.ofNat w m + BitVec.ofNat w a).rotateLeft
        (BitVec.ofNat w w - BitVec.ofInt w k).toNat).ule (BitVec.ofNat w mx) := by
  obtain ⟨kk, d0, rfl, rfl, hd0, hd1, hmd, rfl, rfl⟩ := sdivisible_ok hw hw64 hok hc hU
  have hc' : d0 * 2 ^ kk < 2 ^ (w - 1) := by exact_mod_cast hc
  have hkd : 2 ^ kk ≤ d0 * 2 ^ kk := Nat.le_mul_of_pos_left _ (by omega)
  have hk : kk < w := by
    have : 2 ^ kk < 2 ^ (w - 1) := by omega
    have := (Nat.pow_lt_pow_iff_right (a := 2) (by decide)).mp this
    omega
  have hwl : w < 2 ^ w := Nat.lt_two_pow_self
  have hamt : (BitVec.ofNat w w - BitVec.ofInt w kk).toNat = w - kk := by
    rw [BitVec.ofInt_natCast]
    have := GoFV.Proof.Rules.toNat_ofNat_sub (BitVec.ofNat w kk) hwl
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega)
    rw [this, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  rw [hamt, BitVec.ofInt_natCast]
  exact sdiv_rot_core hw x d0 kk m hc' hd0 hd1 hmd

theorem sdiv_rot_ne {w : Nat} (hw : 1 ≤ w) (hw64 : w ≤ 64) (x : BitVec w) {c k : Int}
    {m a mx : Nat} (hok : Magic.smagicOK c = true) (hc : c < 2 ^ (w - 1))
    (hU : Magic.sdivisible w c = .ok (k, m, a, mx)) :
    (x != x.sdiv (BitVec.ofInt w c) * BitVec.ofInt w c) =
      (BitVec.ofNat w mx).ult ((x * BitVec.ofNat w m + BitVec.ofNat w a).rotateLeft
        (BitVec.ofNat w w - BitVec.ofInt w k).toNat) := by
  rw [bne, sdiv_rot hw hw64 x hok hc hU, BitVec.ule, BitVec.ult, Bool.eq_iff_iff]
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le, decide_eq_true_eq]

end GoFV.Proof.Rules.Divisible

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

set_option hygiene false in
/-- `rule_unfold`, the `sdivisible` call split into failure (the divisor is `0`: the source is
`poison`) and success (`sdiv_rot`, with `sdivisibleOK` and the signed range of the constant). -/
macro "divisible_s" : tactic => `(tactic| (
  rule_unfold
  (try rule_ands)
  (try rule_clear_oracle)
  (try clear hcond)
  divisible_gen
  rcases U with s | ⟨k, m, a, mx⟩
  · have hz := GoFV.Proof.Rules.Divisible.sdivisible_err (by decide) hU
    clear hU
    divisible_gen_rhs
    divisible_rest
  · divisible_rest
    all_goals first
      | exact GoFV.Proof.Rules.Divisible.sdiv_rot (by decide) (by decide) _ (by assumption)
          (by simp only [Nat.reduceSub, Int.reducePow]; omega) hU
      | exact GoFV.Proof.Rules.Divisible.sdiv_rot_ne (by decide) (by decide) _ (by assumption)
          (by simp only [Nat.reduceSub, Int.reducePow]; omega) hU))

theorem r_divisible_98_sound : Rule.Sound GoFV.Rules.Generated.Divisible.r_divisible_98 := by
  divisible_s

theorem r_divisible_107_sound : Rule.Sound GoFV.Rules.Generated.Divisible.r_divisible_107 := by
  divisible_s

theorem r_divisible_116_sound : Rule.Sound GoFV.Rules.Generated.Divisible.r_divisible_116 := by
  divisible_s

theorem r_divisible_125_sound : Rule.Sound GoFV.Rules.Generated.Divisible.r_divisible_125 := by
  divisible_s

theorem r_divisible_134_sound : Rule.Sound GoFV.Rules.Generated.Divisible.r_divisible_134 := by
  divisible_s

theorem r_divisible_143_sound : Rule.Sound GoFV.Rules.Generated.Divisible.r_divisible_143 := by
  divisible_s

theorem r_divisible_152_sound : Rule.Sound GoFV.Rules.Generated.Divisible.r_divisible_152 := by
  divisible_s

theorem r_divisible_161_sound : Rule.Sound GoFV.Rules.Generated.Divisible.r_divisible_161 := by
  divisible_s

/-- `divisible.rules:98`: `(Eq8 x (Mul8 (Div8 x (Const8 [c])) (Const8 [c])))` at `x = -12`,
`c = 6`. -/
theorem inst_r_divisible_98 : Rule.Inst GoFV.Rules.Generated.Divisible.r_divisible_98
    (PEnv.ofLists [([0], .i8 (-12)), ([0, 0, 1], .i8 (-12))] [([], .bool)] (.int .w8)
      [([1, 0, 1], 6), ([1, 1], 6)])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Divisible.r_divisible_98]
  rule_eval
  rfl

/-- `divisible.rules:107`: `(Neq8 x (Mul8 (Div8 x (Const8 [c])) (Const8 [c])))` at `x = 13`,
`c = 6`. -/
theorem inst_r_divisible_107 : Rule.Inst GoFV.Rules.Generated.Divisible.r_divisible_107
    (PEnv.ofLists [([0], .i8 13), ([0, 0, 1], .i8 13)] [([], .bool)] (.int .w8)
      [([1, 0, 1], 6), ([1, 1], 6)])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Divisible.r_divisible_107]
  rule_eval
  rfl

/-- `divisible.rules:116`: `(Eq16 x (Mul16 (Div16 x (Const16 [c])) (Const16 [c])))` at `x = -12`,
`c = 6`. -/
theorem inst_r_divisible_116 : Rule.Inst GoFV.Rules.Generated.Divisible.r_divisible_116
    (PEnv.ofLists [([0], .i16 (-12)), ([0, 0, 1], .i16 (-12))] [([], .bool)] (.int .w16)
      [([1, 0, 1], 6), ([1, 1], 6)])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Divisible.r_divisible_116]
  rule_eval
  rfl

/-- `divisible.rules:125`: `(Neq16 x (Mul16 (Div16 x (Const16 [c])) (Const16 [c])))` at `x = 13`,
`c = 6`. -/
theorem inst_r_divisible_125 : Rule.Inst GoFV.Rules.Generated.Divisible.r_divisible_125
    (PEnv.ofLists [([0], .i16 13), ([0, 0, 1], .i16 13)] [([], .bool)] (.int .w16)
      [([1, 0, 1], 6), ([1, 1], 6)])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Divisible.r_divisible_125]
  rule_eval
  rfl

/-- `divisible.rules:134`: `(Eq32 x (Mul32 (Div32 x (Const32 [c])) (Const32 [c])))` at `x = -12`,
`c = 6`. -/
theorem inst_r_divisible_134 : Rule.Inst GoFV.Rules.Generated.Divisible.r_divisible_134
    (PEnv.ofLists [([0], .i32 (-12)), ([0, 0, 1], .i32 (-12))] [([], .bool)] (.int .w32)
      [([1, 0, 1], 6), ([1, 1], 6)])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Divisible.r_divisible_134]
  rule_eval
  rfl

/-- `divisible.rules:143`: `(Neq32 x (Mul32 (Div32 x (Const32 [c])) (Const32 [c])))` at `x = 13`,
`c = 6`. -/
theorem inst_r_divisible_143 : Rule.Inst GoFV.Rules.Generated.Divisible.r_divisible_143
    (PEnv.ofLists [([0], .i32 13), ([0, 0, 1], .i32 13)] [([], .bool)] (.int .w32)
      [([1, 0, 1], 6), ([1, 1], 6)])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Divisible.r_divisible_143]
  rule_eval
  rfl

/-- `divisible.rules:152`: `(Eq64 x (Mul64 (Div64 x (Const64 [c])) (Const64 [c])))` at `x = -12`,
`c = 6`. -/
theorem inst_r_divisible_152 : Rule.Inst GoFV.Rules.Generated.Divisible.r_divisible_152
    (PEnv.ofLists [([0], .i64 (-12)), ([0, 0, 1], .i64 (-12))] [([], .bool)] (.int .w64)
      [([1, 0, 1], 6), ([1, 1], 6)])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Divisible.r_divisible_152]
  rule_eval
  rfl

/-- `divisible.rules:161`: `(Neq64 x (Mul64 (Div64 x (Const64 [c])) (Const64 [c])))` at `x = 13`,
`c = 6`. -/
theorem inst_r_divisible_161 : Rule.Inst GoFV.Rules.Generated.Divisible.r_divisible_161
    (PEnv.ofLists [([0], .i64 13), ([0, 0, 1], .i64 13)] [([], .bool)] (.int .w64)
      [([1, 0, 1], 6), ([1, 1], 6)])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Divisible.r_divisible_161]
  rule_eval
  rfl

end GoFV.Proof.Rules
