import GoFV.Proof.Rules.DivmodU
import GoFV.Proof.Rules.TacticCond

/-!
# Lemmas for the unsigned magic-number division rules of `DivmodU2.lean`, `DivmodU3.lean` (#69)

`divmod.rules:159`, `:171`, `:180`, `:206`, `:232`: the proofs use `rule_unfold_getd` and
`KernelSafe` (`TacticCond.lean`: the kernel rejects `rule_unfold`'s proof with "deep
recursion"), `divu_auto` as for `:154`, the condition's `m&1 == 0` / `c&1 == 0` as
`m % 2 = 0` / `lowBits 64 c % 2 = 0` (below), and the closing lemmas of `DivmodUMagic.lean`
and below (`close_hmul_even` for `:206`, `close_avg_hmul` for `:232`).
-/

namespace GoFV.Proof.Rules.DivmodU

open GoFV.Rules GoFV.Rules.Magic

/-- `x & 1 == 0` on a `uint64` pattern of `m < 2^64`, as the condition evaluates it. -/
theorem m_even_of_and_one {m : Nat} (hm : m < 2 ^ 64)
    (h : wrapInt 64 false ((((m : Int) % 2 ^ 64).toNat &&& ((1 : Int) % 2 ^ 64).toNat : Nat) : Int)
      = 0) : m % 2 = 0 := by
  have h1 : ((m : Int) % 2 ^ 64).toNat = m := by omega
  have h2 : ((1 : Int) % 2 ^ 64).toNat = 1 := by decide
  simp only [h1, h2, Nat.and_one_is_mod] at h
  unfold wrapInt at h
  simp only [Bool.false_eq_true, ↓reduceIte] at h
  change ((m % 2 : Nat) : Int) % 2 ^ 64 = 0 at h
  omega

/-- `c & 1 == 0` on an `int64` constant `c`: the divisor's low bits are even. -/
theorem lowBits_even_of_and_one {c : Int}
    (h : wrapInt 64 true (((c % 2 ^ 64).toNat &&& ((1 : Int) % 2 ^ 64).toNat : Nat) : Int) = 0) :
    lowBits 64 c % 2 = 0 := by
  have hl : lowBits 64 c = (c % 2 ^ 64).toNat := rfl
  have h2 : ((1 : Int) % 2 ^ 64).toNat = 1 := by decide
  simp only [h2, Nat.and_one_is_mod, ← hl] at h
  have hlt := lowBits_lt 64 c
  unfold wrapInt at h
  simp only [↓reduceIte] at h
  have hb : ((lowBits 64 c % 2 : Nat) : Int).bmod (2 ^ 64) = ((lowBits 64 c % 2 : Nat) : Int) :=
    Int.bmod_eq_of_le (by omega) (by omega)
  omega

/-- The constants `1<<k + q` of the rules (no wrap). -/
theorem toNat_ofNat_add_ofInt {W : Nat} (A q : Nat) (h : A + q < 2 ^ W) :
    (BitVec.ofNat W A + BitVec.ofInt W (q : Int)).toNat = A + q := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofInt]
  have h2 : ((q : Int) % ((2 ^ W : Nat) : Int)).toNat = q := by
    rw [Int.emod_eq_of_lt (Int.natCast_nonneg q) (by omega)]; rfl
  rw [h2, Nat.mod_eq_of_lt (a := A) (by omega)]
  exact Nat.mod_eq_of_lt h

/-- `1<<k + m` with `m` a natural (`divmod.rules:159`). -/
theorem toNat_ofNat_add_ofNat {W : Nat} (A q : Nat) (h : A + q < 2 ^ W) :
    (BitVec.ofNat W A + BitVec.ofNat W q).toNat = A + q := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := A) (by omega), Nat.mod_eq_of_lt (a := q) (by omega)]
  exact Nat.mod_eq_of_lt h

/-- An even divisor's magic number has `m + 1 < 2^n` (no wrap of `umagic(c).m+1`). -/
theorem m_succ_lt {n S m : Nat} {c : Int} (h : USpec n c S m) (hd : lowBits n c % 2 = 0) :
    m + 1 < 2 ^ n := by
  have hS := h.S_ge
  have hSn := h.S_le
  have hhi := h.hi
  have hlo := h.d_lo
  generalize lowBits n c = d at *
  have e1 : 2 ^ S = 2 * 2 ^ (S - 1) := by rw [pow_split (b := 1) (by omega)]
  have e2 : 2 ^ (n + S) = 2 ^ n * 2 ^ S := Nat.pow_add 2 n S
  have e3 : 2 ^ n = 2 ^ (S - 1) * 2 ^ (n - (S - 1)) := pow_split (by omega)
  have e4 : 2 ≤ 2 ^ (n - (S - 1)) := by
    have : 2 ^ 1 ≤ 2 ^ (n - (S - 1)) := Nat.pow_le_pow_right (by decide) (by omega)
    simpa using this
  have e5 : 2 ≤ 2 ^ (S - 1) := by
    have : 2 ^ 1 ≤ 2 ^ (S - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    simpa using this
  have hd2 : 2 ^ (S - 1) + 2 ≤ d := by
    have : 2 ^ (S - 1) % 2 = 0 := by
      rw [pow_split (a := S - 1) (b := 1) (by omega)]; simp
    omega
  false_or_by_contra
  rename_i hm
  rw [e2, e1, e3] at hhi
  rw [e3] at hm
  generalize 2 ^ (S - 1) = P at *
  generalize 2 ^ (n - (S - 1)) = R at *
  have h1 : (2 * (P * R) - 1) * (P + 2) ≤ (P * R + m) * d :=
    Nat.mul_le_mul (by omega) hd2
  have h2 : P * 2 ≤ P * R := Nat.mul_le_mul_left P e4
  rw [Nat.sub_mul, Nat.mul_add, Nat.mul_add] at h1
  generalize P * R = Y at *
  rw [Nat.mul_left_comm Y 2 P] at hhi
  rw [Nat.mul_assoc 2 Y P] at h1
  omega

/-- `goQuo` of a natural by 2. -/
theorem goQuo_nat_two (a : Nat) : goQuo (a : Int) 2 = ((a / 2 : Nat) : Int) :=
  (Int.ofNat_tdiv a 2).symm

/-- `umagic(c).m+1` in `uint64` without wrap. -/
theorem wrapInt_succ (m : Nat) (h : m + 1 < 2 ^ 64) :
    wrapInt 64 false ((m : Int) + 1) = ((m + 1 : Nat) : Int) := by
  unfold wrapInt
  simp only [Bool.false_eq_true, ↓reduceIte]
  change ((m + 1 : Nat) : Int) % 2 ^ 64 = _
  omega

/-- `close_hmul` for a product of `y` (a function of `x`) by `C`. -/
theorem close_hmul_of {n : Nat} (x y : BitVec n) (c : Int) (C : BitVec n) (k : Nat)
    (hq : y.toNat * C.toNat / 2 ^ n / 2 ^ k = x.toNat / lowBits n c) :
    x / BitVec.ofInt n c =
      BitVec.extractLsb' n n (BitVec.setWidth (2 * n) y * BitVec.setWidth (2 * n) C) >>> k := by
  apply BitVec.eq_of_toNat_eq
  have hy := y.isLt
  have hC := C.isLt
  have hn2 : n ≤ 2 * n := by omega
  have hb : y.toNat * C.toNat < 2 ^ (2 * n) := mul_lt_two_pow hy (Nat.le_of_lt hC) (by omega)
  rw [BitVec.toNat_udiv, toNat_ofInt_lowBits, BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat,
    BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) hn2)),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hC (Nat.pow_le_pow_right (by decide) hn2)),
    Nat.mod_eq_of_lt hb, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow]
  have hlt : y.toNat * C.toNat / 2 ^ n < 2 ^ n := by
    apply Nat.div_lt_of_lt_mul; rw [← Nat.pow_add, show n + n = 2 * n by omega]; exact hb
  rw [Nat.mod_eq_of_lt hlt, hq]

/-- `Hmul` of `x >> 1` by `2^(n-1) + (m+1)/2`, shifted by `s - 2` (even divisor,
`divmod.rules:206`). -/
theorem close_hmul_even {n S m : Nat} (x : BitVec n) (c : Int) (C : BitVec n) (k : Nat)
    (h : USpec n c S m) (hd : lowBits n c % 2 = 0) (hC : C.toNat = 2 ^ (n - 1) + (m + 1) / 2)
    (hk : k = S - 2) :
    x / BitVec.ofInt n c =
      BitVec.extractLsb' n n (BitVec.setWidth (2 * n) (x >>> 1) * BitVec.setWidth (2 * n) C)
        >>> k := by
  apply close_hmul_of
  have hS := h.S_ge
  rw [hC, hk, Nat.div_div_eq_div_mul, ← Nat.pow_add, show n + (S - 2) = n + S - 2 by omega,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.pow_one]
  exact udiv_even h hd x.isLt

/-- The high half of the double-width product. -/
theorem toNat_hmul {n : Nat} (x C : BitVec n) :
    (BitVec.extractLsb' n n (BitVec.setWidth (2 * n) x * BitVec.setWidth (2 * n) C)).toNat =
      x.toNat * C.toNat / 2 ^ n := by
  have hx := x.isLt
  have hC := C.isLt
  have hn2 : n ≤ 2 * n := by omega
  have hb : x.toNat * C.toNat < 2 ^ (2 * n) := mul_lt_two_pow hx (Nat.le_of_lt hC) (by omega)
  rw [BitVec.extractLsb'_toNat, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hn2)),
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hC (Nat.pow_le_pow_right (by decide) hn2)),
    Nat.mod_eq_of_lt hb, Nat.shiftRight_eq_div_pow]
  apply Nat.mod_eq_of_lt
  apply Nat.div_lt_of_lt_mul; rw [← Nat.pow_add, show n + n = 2 * n by omega]; exact hb

/-- `Hmul x C ≤ x`: the `Avg` of `divmod.rules:232` does not see `x < y`. -/
theorem hmul_le (x C : BitVec n) :
    (BitVec.extractLsb' n n (BitVec.setWidth (2 * n) x * BitVec.setWidth (2 * n) C)).toNat ≤
      x.toNat := by
  rw [toNat_hmul]
  apply Nat.div_le_of_le_mul
  rw [Nat.mul_comm (2 ^ n)]
  exact Nat.mul_le_mul_left _ (Nat.le_of_lt C.isLt)

/-- `Avg x (Hmul x m)`, shifted by `s - 1` (`divmod.rules:232`). -/
theorem close_avg_hmul {n S m : Nat} (x : BitVec n) (c : Int) (k : Nat) (h : USpec n c S m)
    (hk : k = S - 1) :
    x / BitVec.ofInt n c =
      BitVec.ofNat n ((x.toNat + (BitVec.extractLsb' n n
        (BitVec.setWidth (2 * n) x * BitVec.setWidth (2 * n) (BitVec.ofNat n m))).toNat) / 2)
        >>> k := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have hle := hmul_le x (BitVec.ofNat n m)
  rw [toNat_hmul, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h.m_lt] at hle ⊢
  rw [BitVec.toNat_udiv, toNat_ofInt_lowBits, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega), Nat.shiftRight_eq_div_pow, hk]
  exact (udiv_avg_hmul h hx).symm

end GoFV.Proof.Rules.DivmodU

namespace GoFV.Proof.Rules

/-- The bounds of `USpec` and the condition's leftovers (`umagic(c).m` read from the struct). -/
macro "divu_facts" : tactic => `(tactic| (
  try simp only [List.find?_cons, String.reduceBEq, Option.map_some, rule_cond_s,
    GoFV.Proof.Rules.pat64_omega] at *
  have := (‹GoFV.Proof.Rules.DivmodU.USpec _ _ _ _›).m_lt
  have := (‹GoFV.Proof.Rules.DivmodU.USpec _ _ _ _›).S_le
  have := (‹GoFV.Proof.Rules.DivmodU.USpec _ _ _ _›).S_ge))

/-- A shift amount `w + S - j` computed in 64 bits. -/
macro "divu_amt" : tactic => `(tactic| (
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow] at *
  omega))

end GoFV.Proof.Rules
