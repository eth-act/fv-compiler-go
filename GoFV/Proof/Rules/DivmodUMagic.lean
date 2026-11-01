import Lean
import GoFV.Rules.Helpers.Magic

/-!
# Unsigned magic numbers (`umagic`) for the `divmod.rules` division rules (#69)

`umagic_ok`: `umagicOK w c` (the low `w` bits `d` of `c` are neither zero nor a power of two)
makes `umagic w c` succeed with `(s, m)`, `s = bitsLen d`, and `M = 2^w + m` satisfying the
Granlund–Montgomery bound `2^(w+s) ≤ M*d < 2^(w+s) + 2^s` (`USpec`). The `Nat` lemmas
`udiv_magic`, `udiv_magic_half`, `udiv_magic_even` and `udiv_magic_avg` are the quotients the
rules compute (`DivmodU.lean`).
-/


namespace GoFV.Proof.Rules.DivmodU

open GoFV.Rules GoFV.Rules.Magic

/-- Granlund–Montgomery: if `2^(n+s) ≤ M*d ≤ 2^(n+s) + 2^s` then `x*M / 2^(n+s) = x / d` for
`x < 2^n`. -/
theorem udiv_magic {n s d M x : Nat} (hd : 0 < d) (hlo : 2 ^ (n + s) ≤ M * d)
    (hhi : M * d ≤ 2 ^ (n + s) + 2 ^ s) (hx : x < 2 ^ n) : x * M / 2 ^ (n + s) = x / d := by
  have hA : 2 ^ (n + s) = 2 ^ n * 2 ^ s := Nat.pow_add 2 n s
  apply Nat.div_eq_of_lt_le
  · calc x / d * 2 ^ (n + s) ≤ x / d * (M * d) := Nat.mul_le_mul_left _ hlo
      _ = (x / d * d) * M := by rw [Nat.mul_comm M d, ← Nat.mul_assoc]
      _ ≤ x * M := Nat.mul_le_mul_right _ (Nat.div_mul_le_self x d)
  · apply Nat.lt_of_mul_lt_mul_right (a := d)
    have h1 : x * M * d ≤ x * 2 ^ (n + s) + x * 2 ^ s := by
      rw [Nat.mul_assoc, ← Nat.mul_add]; exact Nat.mul_le_mul_left _ hhi
    have h2 : x * 2 ^ s < 2 ^ (n + s) := by
      rw [hA]; exact Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos s)
    have h3 : (x + 1) * 2 ^ (n + s) ≤ (x / d + 1) * 2 ^ (n + s) * d := by
      rw [Nat.mul_right_comm]
      apply Nat.mul_le_mul_right
      have := Nat.lt_div_mul_add (a := x) hd
      rw [Nat.add_mul, Nat.one_mul]; omega
    rw [Nat.add_mul, Nat.one_mul] at h3
    omega

theorem bitsLen_spec {d : Nat} (hd : 0 < d) : d < 2 ^ bitsLen d ∧ 2 ^ (bitsLen d - 1) ≤ d := by
  unfold bitsLen
  simp only [Nat.ne_of_gt hd, ite_false, Nat.add_sub_cancel]
  exact ⟨Nat.lt_log2_self, Nat.log2_self_le (Nat.ne_of_gt hd)⟩

/-- `⌈a/d⌉ * d` lies in `[a, a + d)`. -/
theorem ceil_div_mul {a d : Nat} (hd : 0 < d) :
    a ≤ (a + d - 1) / d * d ∧ (a + d - 1) / d * d ≤ a + d - 1 := by
  have h1 := Nat.div_add_mod (a + d - 1) d
  have h2 := Nat.mod_lt (a + d - 1) hd
  rw [Nat.mul_comm] at h1
  omega

theorem two_pow_pos_int (n : Nat) : (0 : Int) < 2 ^ n := Int.pow_pos (by decide)

theorem lowBits_lt (n : Nat) (c : Int) : lowBits n c < 2 ^ n := by
  unfold lowBits
  rw [show c.emod (2 ^ n) = c % 2 ^ n from rfl]
  have hp := two_pow_pos_int n
  have h0 := Int.emod_nonneg c (Int.ne_of_gt hp)
  have h1 := Int.emod_lt_of_pos c hp
  have : ((c % 2 ^ n).toNat : Int) < ((2 ^ n : Nat) : Int) := by
    rw [Int.toNat_of_nonneg h0]; simpa using h1
  exact_mod_cast this

theorem pat64_mod {n : Nat} (hn : n ≤ 64) (c : Int) : pat64 c % 2 ^ n = lowBits n c := by
  unfold pat64 lowBits
  rw [show c.emod (2 ^ n) = c % 2 ^ n from rfl, show c.emod (2 ^ 64) = c % 2 ^ 64 from rfl]
  have hp := two_pow_pos_int 64
  have hq := two_pow_pos_int n
  apply Int.ofNat_inj.mp
  rw [Int.natCast_emod, Int.toNat_of_nonneg (Int.emod_nonneg c (Int.ne_of_gt hp)),
    Int.toNat_of_nonneg (Int.emod_nonneg c (Int.ne_of_gt hq))]
  have hd : ((2 ^ n : Nat) : Int) ∣ ((2 ^ 64 : Nat) : Int) :=
    Int.natCast_dvd_natCast.mpr (Nat.pow_dvd_pow 2 hn)
  simp only [Int.natCast_pow, Int.cast_ofNat_Int] at hd ⊢
  exact Int.emod_emod_of_dvd c hd

/-- The low bits of `c - 1` are those of `c` minus one when the latter are not zero. -/
theorem lowBits_sub_one {n : Nat} {c : Int} (h : lowBits n c ≠ 0) :
    lowBits n (c - 1) = lowBits n c - 1 := by
  unfold lowBits at *
  rw [show (c - 1).emod (2 ^ n) = (c - 1) % 2 ^ n from rfl] at *
  rw [show c.emod (2 ^ n) = c % 2 ^ n from rfl] at *
  have hp := two_pow_pos_int n
  have h0 := Int.emod_nonneg c (Int.ne_of_gt hp)
  have h1 := Int.emod_lt_of_pos c hp
  have h2 := Int.mul_ediv_add_emod c (2 ^ n)
  have hr : 0 < c % 2 ^ n := by
    rcases Int.lt_or_eq_of_le h0 with h3 | h3
    · exact h3
    · rw [← h3] at h; simp at h
  have : (c - 1) % 2 ^ n = c % 2 ^ n - 1 := by
    rw [show c - 1 = (c % 2 ^ n - 1) + 2 ^ n * (c / 2 ^ n) by omega,
      Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  rw [this]
  omega

/-- A `w`-bit `bmod` is zero when the `w`-bit pattern is. -/
theorem bmod_ne_zero {X : Nat} {w : Nat} (h : (X : Int).bmod (2 ^ w) ≠ 0) : X % 2 ^ w ≠ 0 := by
  intro h0
  apply h
  have h1 : (X : Int) % ((2 ^ w : Nat) : Int) = 0 := by
    rw [← Int.natCast_emod, h0]; rfl
  rw [Int.bmod_def, h1]
  have hp := two_pow_pos_int w
  simp only [Int.natCast_pow, Int.cast_ofNat_Int] at hp ⊢
  split <;> omega

/-- What `umagic n c = .ok (s, m)` gives about `d = lowBits n c`, `s = bitsLen d` and
`M = 2^n + m`, plus `d` not a power of two (`umagicOK`). -/
structure USpec (n : Nat) (c : Int) (S m : Nat) : Prop where
  d_pos : 0 < lowBits n c
  d_lt : lowBits n c < 2 ^ n
  d_lo : 2 ^ (S - 1) < lowBits n c
  d_hi : lowBits n c < 2 ^ S
  S_ge : 2 ≤ S
  S_le : S ≤ n
  m_lt : m < 2 ^ n
  lo : 2 ^ (n + S) ≤ (2 ^ n + m) * lowBits n c
  hi : (2 ^ n + m) * lowBits n c < 2 ^ (n + S) + 2 ^ S

/-- The bit test of `umagic`: `M = ⌈2^(n+S)/d⌉` lies in `[2^n, 2^(n+1))` when `d` is not a
power of two. -/
theorem umagic_bit {n S d : Nat} (hd : 0 < d) (hdn : d < 2 ^ n) (hlo : 2 ^ (S - 1) < d)
    (hhi : d < 2 ^ S) : (((2 ^ (n + S) + d - 1) / d) >>> n) % 2 = 1 := by
  generalize hM : (2 ^ (n + S) + d - 1) / d = M
  obtain ⟨h1, h2⟩ := ceil_div_mul (a := 2 ^ (n + S)) hd
  rw [hM] at h1 h2
  have hA : 2 ^ (n + S) = 2 ^ n * 2 ^ S := Nat.pow_add 2 n S
  have hpn := Nat.two_pow_pos n
  have hS1 : 1 ≤ S := by
    rcases Nat.eq_zero_or_pos S with h0 | h0
    · subst h0; simp at hlo hhi; omega
    · exact h0
  have hpS : 2 ^ S = 2 * 2 ^ (S - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have hMlo : 2 ^ n ≤ M := by
    false_or_by_contra
    rename_i hlt
    have : M * d < 2 ^ n * d := Nat.mul_lt_mul_of_pos_right (by omega) hd
    have : 2 ^ n * d ≤ 2 ^ n * 2 ^ S := Nat.mul_le_mul_left _ (Nat.le_of_lt hhi)
    omega
  have hMhi : M < 2 * 2 ^ n := by
    false_or_by_contra
    rename_i hge
    have h3 : 2 * 2 ^ n * (2 ^ (S - 1) + 1) ≤ M * d :=
      Nat.mul_le_mul (by omega) hlo
    have h4 : 2 * 2 ^ n * (2 ^ (S - 1) + 1) = 2 ^ n * 2 ^ S + 2 * 2 ^ n := by
      rw [hpS, Nat.mul_add, Nat.mul_one, Nat.mul_comm 2 (2 ^ n), Nat.mul_assoc]
    omega
  rw [Nat.shiftRight_eq_div_pow]
  have h5 : M / 2 ^ n = 1 := by
    apply Nat.div_eq_of_lt_le <;> omega
  rw [h5]

/-- `umagicOK w c` (`w ∈ {8, 16, 32, 64}`): the low `w` bits `d` of `c` are neither zero nor a
power of two. -/
theorem umagicOK_spec {w : Nat} {c : Int} (h : umagicOK w c = true)
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64) :
    lowBits w c ≠ 0 ∧ lowBits w c &&& (lowBits w c - 1) ≠ 0 := by
  have hw64 : w ≤ 64 := by omega
  have hX : (pat64 c &&& pat64 (c - 1)) % 2 ^ w ≠ 0 := by
    apply bmod_ne_zero
    unfold umagicOK notPow2 andPred bitwise at h
    rcases hw with rfl | rfl | rfl | rfl <;>
      simpa [GoTy.intInfo?, wrapInt] using h
  rw [Nat.and_mod_two_pow, pat64_mod hw64, pat64_mod hw64] at hX
  have hd : lowBits w c ≠ 0 := by
    intro h0; rw [h0, Nat.zero_and] at hX; exact hX rfl
  rw [lowBits_sub_one hd] at hX
  exact ⟨hd, hX⟩

/-- `umagicOK w c` makes `umagic w c` succeed, with `USpec`. -/
theorem umagic_ok {w : Nat} {c : Int} (h : umagicOK w c = true)
    (hw : w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64 := by decide) :
    ∃ S m : Nat, umagic w c = .ok ((S : Int), m) ∧ USpec w c S m := by
  obtain ⟨hd0, hand⟩ := umagicOK_spec h hw
  have hw1 : 1 ≤ w := by omega
  have hw64 : w ≤ 64 := by omega
  have hdn := lowBits_lt w c
  generalize hd : lowBits w c = d at *
  have hdp : 0 < d := Nat.pos_of_ne_zero hd0
  obtain ⟨hdS, hSd⟩ := bitsLen_spec hdp
  have hlo : 2 ^ (bitsLen d - 1) < d := by
    rcases Nat.lt_or_eq_of_le hSd with h1 | h1
    · exact h1
    · rw [← h1, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_self] at hand
      exact absurd rfl hand
  have hbit := umagic_bit hdp hdn hlo hdS
  have hok : umagic w c = .ok ((bitsLen d : Int),
      ((2 ^ (w + bitsLen d) + d - 1) / d - 2 ^ w) % 2 ^ 64) := by
    unfold umagic
    rw [hd]
    simp only [hd0, hbit, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rfl
  refine ⟨_, _, hok, ?_⟩
  -- the spec of the result
  generalize bitsLen d = S at *
  generalize hM : (2 ^ (w + S) + d - 1) / d = M at hok hbit
  obtain ⟨h1, h2⟩ := ceil_div_mul (a := 2 ^ (w + S)) hdp
  rw [hM] at h1 h2
  rw [Nat.shiftRight_eq_div_pow] at hbit
  have hpn := Nat.two_pow_pos w
  have hS1 : 1 ≤ S := by
    rcases Nat.eq_zero_or_pos S with h0 | h0
    · subst h0; simp at hlo hdS; omega
    · exact h0
  have hpS : 2 ^ S = 2 * 2 ^ (S - 1) := by
    rw [← Nat.pow_succ']; congr 1; omega
  have hMlo : 2 ^ w ≤ M := by
    false_or_by_contra
    rename_i hlt
    have : M / 2 ^ w = 0 := Nat.div_eq_of_lt (by omega)
    rw [this] at hbit; exact absurd hbit (by decide)
  have hMhi : M < 2 * 2 ^ w := by
    false_or_by_contra
    rename_i hge
    have h3 : 2 * 2 ^ w * (2 ^ (S - 1) + 1) ≤ M * d := Nat.mul_le_mul (by omega) hlo
    have h4 : 2 * 2 ^ w * (2 ^ (S - 1) + 1) = 2 ^ w * 2 ^ S + 2 * 2 ^ w := by
      rw [hpS, Nat.mul_add, Nat.mul_one, Nat.mul_comm 2 (2 ^ w), Nat.mul_assoc]
    have hA : 2 ^ (w + S) = 2 ^ w * 2 ^ S := Nat.pow_add 2 w S
    omega
  have h64 : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hw64
  have hm : (M - 2 ^ w) % 2 ^ 64 = M - 2 ^ w := Nat.mod_eq_of_lt (by omega)
  have hSw : S ≤ w := by
    false_or_by_contra
    rename_i hgt
    have : 2 ^ w ≤ 2 ^ (S - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  have hS2 : 2 ≤ S := by
    false_or_by_contra
    rename_i hlt
    have : S = 1 := by omega
    subst this; simp at hlo hdS; omega
  rw [hm]
  have hMe : 2 ^ w + (M - 2 ^ w) = M := by omega
  have hA : 2 ^ (w + S) = 2 ^ w * 2 ^ S := Nat.pow_add 2 w S
  subst hd
  refine ⟨hdp, hdn, hlo, hdS, hS2, hSw, by omega, ?_, ?_⟩ <;> rw [hMe] <;> omega

theorem pow_split {a b : Nat} (h : b ≤ a) : 2 ^ a = 2 ^ b * 2 ^ (a - b) := by
  rw [← Nat.pow_add]; congr 1; omega

/-- `Mul` shape: `x * (2^n + m) >> (n + S) = x / d`. -/
theorem udiv_mul {n S m x : Nat} {c : Int} (h : USpec n c S m) (hx : x < 2 ^ n) :
    x * (2 ^ n + m) / 2 ^ (n + S) = x / lowBits n c :=
  udiv_magic h.d_pos h.lo (Nat.le_of_lt h.hi) hx

/-- Even `m`: `x * (2^(n-1) + m/2) >> (n + S - 1) = x / d`. -/
theorem udiv_half {n S m x : Nat} {c : Int} (h : USpec n c S m) (hm : m % 2 = 0)
    (hx : x < 2 ^ n) : x * (2 ^ (n - 1) + m / 2) / 2 ^ (n + S - 1) = x / lowBits n c := by
  have hn : 1 ≤ n := Nat.le_trans (by decide) (Nat.le_trans h.S_ge h.S_le)
  have h1 : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [pow_split (b := 1) hn]
  have h2 : 2 ^ (n + S) = 2 * 2 ^ (n + S - 1) := by rw [pow_split (b := 1) (by omega)]
  have h3 : 2 ^ n + m = 2 * (2 ^ (n - 1) + m / 2) := by omega
  rw [← udiv_mul h hx, h3, h2, Nat.mul_left_comm, Nat.mul_div_mul_left _ _ (by decide)]

/-- Even `d`: `(x >> 1) * (2^(n-1) + (m+1)/2) >> (n + S - 2) = x / d`. -/
theorem udiv_even {n S m x : Nat} {c : Int} (h : USpec n c S m) (hd : lowBits n c % 2 = 0)
    (hx : x < 2 ^ n) :
    x / 2 * (2 ^ (n - 1) + (m + 1) / 2) / 2 ^ (n + S - 2) = x / lowBits n c := by
  have hn : 2 ≤ n := Nat.le_trans h.S_ge h.S_le
  have hS := h.S_ge
  have hlo := h.lo
  have hhi := h.hi
  have hdp := h.d_pos
  have hdS := h.d_hi
  generalize lowBits n c = d at *
  have e1 : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [pow_split (b := 1) (by omega)]
  have e2 : 2 ^ (n + S) = 4 * 2 ^ (n - 1 + (S - 1)) := by
    rw [pow_split (b := 2) (by omega)]; congr 2; omega
  have e3 : 2 ^ S = 2 * 2 ^ (S - 1) := by rw [pow_split (b := 1) (by omega)]
  have e4 : n + S - 2 = n - 1 + (S - 1) := by omega
  generalize hM' : 2 ^ (n - 1) + (m + 1) / 2 = M' at *
  have hM1 : 2 ^ n + m ≤ 2 * M' := by omega
  have hM2 : 2 * M' ≤ 2 ^ n + m + 1 := by omega
  have hdd : d = 2 * (d / 2) := by omega
  have hA : 2 * M' * d = 4 * (M' * (d / 2)) := by
    conv => lhs; rw [hdd]
    rw [Nat.mul_mul_mul_comm]
  have hl : (2 ^ n + m) * d ≤ 2 * M' * d := Nat.mul_le_mul_right _ hM1
  have hu : 2 * M' * d ≤ (2 ^ n + m + 1) * d := Nat.mul_le_mul_right _ hM2
  rw [Nat.add_mul, Nat.one_mul] at hu
  rw [e4, udiv_magic (n := n - 1) (s := S - 1) (d := d / 2) (x := x / 2) (M := M') (by omega)
    (by omega) (by omega) (by omega), Nat.div_div_eq_div_mul, ← hdd]

/-- `Avg` of `x * 2^n` and `x * m`: `((x * 2^n + x * m) / 2) >> (n + S - 1) = x / d`. -/
theorem udiv_avg_wide {n S m x : Nat} {c : Int} (h : USpec n c S m) (hx : x < 2 ^ n) :
    (x * 2 ^ n + x * m) / 2 / 2 ^ (n + S - 1) = x / lowBits n c := by
  have hn : 1 ≤ n := Nat.le_trans (by decide) (Nat.le_trans h.S_ge h.S_le)
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ', show (n + S - 1).succ = n + S by
    have := h.S_ge; omega, ← Nat.mul_add]
  exact udiv_mul h hx

/-- `Avg` of `x` and `Hmul x m`: `((x + x * m / 2^n) / 2) >> (S - 1) = x / d`. -/
theorem udiv_avg_hmul {n S m x : Nat} {c : Int} (h : USpec n c S m) (hx : x < 2 ^ n) :
    (x + x * m / 2 ^ n) / 2 / 2 ^ (S - 1) = x / lowBits n c := by
  have hS := h.S_ge
  have e : x + x * m / 2 ^ n = (x * m + 2 ^ n * x) / 2 ^ n := by
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos n)]; omega
  have e2 : 2 ^ n * (2 * 2 ^ (S - 1)) = 2 ^ (n + S) := by
    rw [Nat.pow_add, pow_split (a := S) (b := 1) (by omega), Nat.pow_one]
  rw [e, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, e2]
  rw [show x * m + 2 ^ n * x = x * (2 ^ n + m) by
    rw [Nat.mul_add, Nat.mul_comm (2 ^ n) x, Nat.add_comm]]
  exact udiv_mul h hx

/-! ## The rules' `BitVec` results -/

theorem toNat_ofInt_lowBits (n : Nat) (c : Int) : (BitVec.ofInt n c).toNat = lowBits n c := by
  rw [BitVec.toNat_ofInt]; rfl

theorem mul_lt_two_pow {a b p q W : Nat} (ha : a < 2 ^ p) (hb : b ≤ 2 ^ q) (h : p + q ≤ W) :
    a * b < 2 ^ W := by
  calc a * b ≤ a * 2 ^ q := Nat.mul_le_mul_left _ hb
    _ < 2 ^ p * 2 ^ q := Nat.mul_lt_mul_of_pos_right ha (Nat.two_pow_pos q)
    _ = 2 ^ (p + q) := (Nat.pow_add 2 p q).symm
    _ ≤ 2 ^ W := Nat.pow_le_pow_right (by decide) h

/-- A product in a wider register, shifted right and truncated, computes `x / d` when it does
not overflow and its quotient is `x / d`. -/
theorem close_mul {n W : Nat} (x : BitVec n) (c : Int) (C : BitVec W) (k : Nat) (hnW : n ≤ W)
    (hb : x.toNat * C.toNat < 2 ^ W) (hq : x.toNat * C.toNat / 2 ^ k = x.toNat / lowBits n c) :
    x / BitVec.ofInt n c = BitVec.setWidth n ((BitVec.setWidth W x * C) >>> k) := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have hxW : x.toNat < 2 ^ W := Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hnW)
  rw [BitVec.toNat_udiv, toNat_ofInt_lowBits, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.toNat_mul, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hxW, Nat.mod_eq_of_lt hb,
    Nat.shiftRight_eq_div_pow, hq]
  exact (Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx)).symm

/-- The high half of the double-width product, shifted right, computes `x / d` when its
quotient is `x / d`. -/
theorem close_hmul {n : Nat} (x : BitVec n) (c : Int) (C : BitVec n) (k : Nat)
    (hq : x.toNat * C.toNat / 2 ^ n / 2 ^ k = x.toNat / lowBits n c) :
    x / BitVec.ofInt n c =
      BitVec.extractLsb' n n (BitVec.setWidth (2 * n) x * BitVec.setWidth (2 * n) C) >>> k := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have hC := C.isLt
  have hn2 : n ≤ 2 * n := by omega
  have hb : x.toNat * C.toNat < 2 ^ (2 * n) := mul_lt_two_pow hx (Nat.le_of_lt hC) (by omega)
  rw [BitVec.toNat_udiv, toNat_ofInt_lowBits, BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat,
    BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hn2)),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hC (Nat.pow_le_pow_right (by decide) hn2)),
    Nat.mod_eq_of_lt hb, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have hlt : x.toNat * C.toNat / 2 ^ n < 2 ^ n := by
    apply Nat.div_lt_of_lt_mul; rw [← Nat.pow_add, show n + n = 2 * n by omega]; exact hb
  rw [Nat.mod_eq_of_lt hlt, hq]

/-- `Mul` by `2^n + m`, shifted by `n + s` (`divmod.rules:154`, `:159`). -/
theorem close_mul_full {n W S m : Nat} (x : BitVec n) (c : Int) (C : BitVec W) (k : Nat)
    (h : USpec n c S m) (hW : 2 * n + 1 ≤ W) (hC : C.toNat = 2 ^ n + m) (hk : k = n + S) :
    x / BitVec.ofInt n c = BitVec.setWidth n ((BitVec.setWidth W x * C) >>> k) := by
  have hm := h.m_lt
  apply close_mul x c C k (by omega) _ (by rw [hC, hk]; exact udiv_mul h x.isLt)
  rw [hC]
  refine mul_lt_two_pow (q := n + 1) x.isLt ?_ (by omega)
  rw [Nat.pow_succ]; omega

/-- `Mul` by `2^(n-1) + m/2`, shifted by `n + s - 1` (even `m`, `divmod.rules:166`, `:171`). -/
theorem close_mul_half {n W S m : Nat} (x : BitVec n) (c : Int) (C : BitVec W) (k : Nat)
    (h : USpec n c S m) (hm2 : m % 2 = 0) (hW : 2 * n ≤ W) (hC : C.toNat = 2 ^ (n - 1) + m / 2)
    (hk : k = n + S - 1) :
    x / BitVec.ofInt n c = BitVec.setWidth n ((BitVec.setWidth W x * C) >>> k) := by
  have hm := h.m_lt
  have hn : 1 ≤ n := Nat.le_trans (by decide) (Nat.le_trans h.S_ge h.S_le)
  have e1 : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [pow_split (b := 1) hn]
  apply close_mul x c C k (by omega) _ (by rw [hC, hk]; exact udiv_half h hm2 x.isLt)
  rw [hC]
  exact mul_lt_two_pow (q := n) x.isLt (by omega) (by omega)

/-- `Hmul` by `2^(n-1) + m/2`, shifted by `s - 1` (even `m`, `divmod.rules:176`, `:180`). -/
theorem close_hmul_half {n S m : Nat} (x : BitVec n) (c : Int) (C : BitVec n) (k : Nat)
    (h : USpec n c S m) (hm2 : m % 2 = 0) (hC : C.toNat = 2 ^ (n - 1) + m / 2)
    (hk : k = S - 1) :
    x / BitVec.ofInt n c =
      BitVec.extractLsb' n n (BitVec.setWidth (2 * n) x * BitVec.setWidth (2 * n) C) >>> k := by
  apply close_hmul
  have hS := h.S_ge
  rw [hC, hk, Nat.div_div_eq_div_mul, ← Nat.pow_add, show n + (S - 1) = n + S - 1 by omega]
  exact udiv_half h hm2 x.isLt

end GoFV.Proof.Rules.DivmodU
