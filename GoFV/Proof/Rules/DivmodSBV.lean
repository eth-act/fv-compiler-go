import GoFV.Proof.Rules.DivmodSMagic

/-!
# Signed division by a constant: the `BitVec` forms (`divmod.rules`, #69)

Width-generic lemmas for the result shapes of the signed `Div` rules (`smagic`: wide multiply,
`Hmul` by `m/2`, `x + Hmul x m`) and the tactics that
apply them (`divs_wide`, `divs_even`, `divs_add`, `divs_prefix`).
-/

namespace GoFV.Proof.Rules.DivmodS

open GoFV.Rules GoFV.Rules.Magic

theorem two_pow_int_succ (k : Nat) : (2 : Int) ^ (k + 1) = 2 * 2 ^ k := by
  rw [Int.pow_succ, Int.mul_comm]

theorem two_pow_int_pos (k : Nat) : (0 : Int) < 2 ^ k := Int.pow_pos (by decide)

theorem two_pow_int_le {a b : Nat} (h : a ≤ b) : (2 : Int) ^ a ≤ 2 ^ b := by
  have : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) h
  exact_mod_cast this

/-- `bmod 2^w` is the identity on the signed range of `w` bits. -/
theorem bmod_of_range {x : Int} {w : Nat} (hw : 1 ≤ w) (h1 : -(2 ^ (w - 1) : Int) ≤ x)
    (h2 : x < 2 ^ (w - 1)) : x.bmod (2 ^ w) = x := by
  have e : ((2 ^ w : Nat) : Int) = 2 * 2 ^ (w - 1) := by
    rw [Int.natCast_pow, Int.cast_ofNat_Int, ← two_pow_int_succ]
    exact congrArg (2 ^ ·) (by omega)
  apply Int.bmod_eq_of_le <;> rw [e] <;> omega

/-- The sign of `x` in the signed range of `k + 1` bits, by an arithmetic shift by `k`. -/
theorem div_pow_sgn {x : Int} {k : Nat} (h1 : -(2 ^ k : Int) ≤ x) (h2 : x < 2 ^ k) :
    x / 2 ^ k = if x < 0 then -1 else 0 := by
  rw [Int.ediv_eq_iff_of_pos (two_pow_int_pos k)]
  split <;> omega

theorem mul_range {X A B : Int} {M : Nat} (hA1 : -A ≤ X) (hA2 : X < A) (hM : (M : Int) < B) :
    -(A * B) ≤ X * M ∧ X * M < A * B := by
  have hM0 : (0 : Int) ≤ M := Int.natCast_nonneg M
  have hA0 : 0 ≤ A := by omega
  have h1 : -A * M ≤ X * M := Int.mul_le_mul_of_nonneg_right hA1 hM0
  have h2 : A * M ≤ A * B := Int.mul_le_mul_of_nonneg_left (by omega) hA0
  rw [Int.neg_mul] at h1
  refine ⟨by omega, ?_⟩
  rcases Int.lt_or_le 0 X with hX | hX
  · have h3 : X * M ≤ X * B := Int.mul_le_mul_of_nonneg_left (by omega) (by omega)
    have h4 : X * B < A * B := Int.mul_lt_mul_of_pos_right hA2 (by omega)
    omega
  · have h3 : X * M ≤ 0 * M := Int.mul_le_mul_of_nonneg_right hX hM0
    have h4 : 0 < A * B := Int.mul_pos (by omega) (by omega)
    rw [Int.zero_mul] at h3
    omega

theorem toInt_setWidth_of_le {n W : Nat} (P : BitVec W) (h : n ≤ W) :
    (P.setWidth n).toInt = P.toInt.bmod (2 ^ n) := by
  rw [BitVec.toInt_setWidth, BitVec.toInt_eq_toNat_bmod P,
    Int.bmod_bmod_of_dvd (Nat.pow_dvd_pow 2 h)]

/-- `Div8/16/32` by `smagic` in a wider register (`divmod.rules:87/93/99`):
`(SignExt x * M) >> (n + s) - (SignExt x >> (W - 1))`, truncated to `n` bits. -/
theorem sdiv_magic_wide {n W S M : Nat} {c : Int} (hn : 2 ≤ n) (hW : 2 * n ≤ W)
    (h : SSpec n c S M) (x : BitVec n) {a b : Nat} (ha : a = n + S) (hb : b = W - 1) :
    x.sdiv (BitVec.ofInt n c) =
      BitVec.setWidth n (BitVec.setWidth n ((BitVec.signExtend W x * BitVec.ofNat W M).sshiftRight a) -
        BitVec.setWidth n ((BitVec.signExtend W x).sshiftRight b)) := by
  obtain ⟨-, hS2, hS3, hS4, -, hM2, hMC1, hMC2⟩ := h
  subst ha hb
  have hc0 : 0 < c := by omega
  obtain ⟨C, rfl⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt hc0)
  simp only [Int.toNat_natCast] at hS3 hS4 hMC1 hMC2
  have hC0 : 0 < C := by omega
  have hpS : 2 ^ (S + 1) ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hnW : n ≤ W := by omega
  have hCi : (C : Int) < 2 ^ (n - 1) := by
    have : C < 2 ^ (n - 1) := by omega
    exact_mod_cast this
  have hMi : (M : Int) < 2 ^ n := by exact_mod_cast hM2
  have hn1 : (2 : Int) ^ n = 2 * 2 ^ (n - 1) := by
    rw [← two_pow_int_succ]; exact congrArg (2 ^ ·) (by omega)
  have hnn : (2 : Int) ^ (n - 1) * 2 ^ n ≤ 2 ^ (W - 1) := by
    rw [← Int.pow_add]; exact two_pow_int_le (by omega)
  have hnW1 : (2 : Int) ^ (n - 1) ≤ 2 ^ (W - 1) := two_pow_int_le (by omega)
  have hnW2 : (2 : Int) ^ n ≤ 2 ^ (W - 1) := two_pow_int_le (by omega)
  have hX1 := BitVec.le_toInt x
  have hX2 := BitVec.toInt_lt (x := x)
  have hXM := mul_range (M := M) hX1 hX2 hMi
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.setWidth_eq, BitVec.toInt_sdiv, BitVec.toInt_sub, toInt_setWidth_of_le _ hnW,
    toInt_setWidth_of_le _ hnW, Int.bmod_sub_bmod, Int.sub_bmod_bmod,
    BitVec.toInt_sshiftRight, BitVec.toInt_sshiftRight, BitVec.toInt_mul,
    BitVec.toInt_signExtend_of_le hnW, BitVec.toInt_ofNat', BitVec.toInt_ofInt,
    bmod_of_range (w := n) (by omega) (by omega) hCi,
    bmod_of_range (x := (M : Int)) (w := W) (by omega) (by omega) (by omega),
    bmod_of_range (x := x.toInt * M) (w := W) (by omega) (by omega) (by omega),
    Int.shiftRight_eq_div_pow, Int.shiftRight_eq_div_pow, Int.natCast_pow, Int.natCast_pow,
    Int.cast_ofNat_Int, div_pow_sgn (x := x.toInt) (k := W - 1) (by omega) (by omega),
    sdiv_magic_int (by omega) hC0 hMC1 hMC2 (by omega) hX1 hX2]

theorem mul_le_of_abs {X Y A B : Int} (hX1 : -A ≤ X) (hX2 : X ≤ A) (hY1 : -B ≤ Y) (hY2 : Y ≤ B) :
    -(A * B) ≤ X * Y ∧ X * Y ≤ A * B := by
  have hA : 0 ≤ A := by omega
  have hB : 0 ≤ B := by omega
  have key : ∀ {U V : Int}, 0 ≤ U → U ≤ A → 0 ≤ V → V ≤ B → 0 ≤ U * V ∧ U * V ≤ A * B :=
    fun h1 h2 h3 h4 => ⟨Int.mul_nonneg h1 h3, Int.mul_le_mul h2 h4 h3 hA⟩
  rcases Int.lt_or_le X 0 with hX | hX <;> rcases Int.lt_or_le Y 0 with hY | hY
  · have := key (U := -X) (V := -Y) (by omega) (by omega) (by omega) (by omega)
    rw [Int.neg_mul_neg] at this; omega
  · have := key (U := -X) (V := Y) (by omega) (by omega) hY hY2
    rw [Int.neg_mul] at this; omega
  · have := key (U := X) (V := -Y) hX hX2 (by omega) (by omega)
    rw [Int.mul_neg] at this; omega
  · have := key (U := X) (V := Y) hX hX2 hY hY2
    omega

/-- `Hmul` (signed): the high half of the double-width product is `⌊x*y / 2^n⌋`. -/
theorem toInt_hmul {n : Nat} (hn : 1 ≤ n) (x y : BitVec n) :
    (BitVec.extractLsb' n n (BitVec.signExtend (2 * n) x * BitVec.signExtend (2 * n) y)).toInt =
      x.toInt * y.toInt / 2 ^ n := by
  have hX1 := BitVec.le_toInt x
  have hX2 := BitVec.toInt_lt (x := x)
  have hY1 := BitVec.le_toInt y
  have hY2 := BitVec.toInt_lt (x := y)
  generalize hK : (2 : Int) ^ (n - 1) = K at hX1 hX2 hY1 hY2
  have hK0 : 0 < K := by rw [← hK]; exact two_pow_int_pos _
  have hKK : 0 < K * K := Int.mul_pos hK0 hK0
  have hn2 : (2 : Int) ^ n = 2 * K := by
    rw [← hK, ← two_pow_int_succ]; exact congrArg (2 ^ ·) (by omega)
  have h2n1 : (2 : Int) ^ (2 * n - 1) = 2 * (K * K) := by
    rw [← hK, ← Int.pow_add, ← two_pow_int_succ]; exact congrArg (2 ^ ·) (by omega)
  have h2n : (2 : Int) ^ (2 * n) = 2 ^ n * 2 ^ n := by
    rw [← Int.pow_add]; exact congrArg (2 ^ ·) (by omega)
  obtain ⟨hP1, hP2⟩ := mul_le_of_abs (A := K) (B := K) hX1 (by omega) hY1 (by omega)
  have hp : (BitVec.signExtend (2 * n) x * BitVec.signExtend (2 * n) y).toInt =
      x.toInt * y.toInt := by
    rw [BitVec.toInt_mul, BitVec.toInt_signExtend_of_le (by omega),
      BitVec.toInt_signExtend_of_le (by omega)]
    exact bmod_of_range (by omega) (by omega) (by omega)
  generalize BitVec.signExtend (2 * n) x * BitVec.signExtend (2 * n) y = p at hp
  generalize x.toInt * y.toInt = P at hp hP1 hP2
  have hpos : (0 : Int) < 2 ^ n := two_pow_int_pos n
  have hq1 : -(2 ^ (n - 1) : Int) ≤ P / 2 ^ n := by
    rw [Int.le_ediv_iff_mul_le hpos, hK, hn2, Int.neg_mul, Int.mul_left_comm]; omega
  have hq2 : P / 2 ^ n < 2 ^ (n - 1) := by
    rw [Int.ediv_lt_iff_lt_mul hpos, hK, hn2, Int.mul_left_comm]; omega
  have hc : (p.toNat : Int) = P ∨ (p.toNat : Int) = P + 2 ^ n * 2 ^ n := by
    rw [← hp, BitVec.toInt_eq_toNat_cond]
    split
    · exact Or.inl rfl
    · right; rw [← h2n]; push_cast; omega
  rw [BitVec.toInt_extractLsb', Nat.shiftRight_eq_div_pow, Int.natCast_ediv, Int.natCast_pow,
    Int.cast_ofNat_Int]
  rcases hc with hc | hc <;> rw [hc]
  · exact bmod_of_range hn hq1 hq2
  · rw [Int.add_mul_ediv_right _ _ (Int.ne_of_gt hpos),
      show P / 2 ^ n + 2 ^ n = P / 2 ^ n + 1 * ((2 ^ n : Nat) : Int) by push_cast; omega,
      Int.add_mul_bmod_self_right]
    exact bmod_of_range hn hq1 hq2

theorem ediv_range {P K D : Int} (hK : 0 < K) (hD : 2 * K ≤ D) (h1 : -(K * K) ≤ P)
    (h2 : P ≤ K * K) : -K ≤ P / D ∧ P / D < K := by
  have hD0 : 0 < D := by omega
  have h3 : K * (2 * K) ≤ K * D := Int.mul_le_mul_of_nonneg_left hD (Int.le_of_lt hK)
  have hKK : 0 < K * K := Int.mul_pos hK hK
  rw [Int.mul_left_comm] at h3
  constructor
  · rw [Int.le_ediv_iff_mul_le hD0, Int.neg_mul]; omega
  · rw [Int.ediv_lt_iff_lt_mul hD0]; omega

/-- The common tail of the `Hmul` forms: `C = c.toNat` and the facts on `x*M`. -/
theorem sdiv_magic_tail {n S M : Nat} {c : Int} (hn : 2 ≤ n) (hS2 : S + 2 ≤ n)
    (hS3 : 2 ^ S < c.toNat) (hS4 : c.toNat < 2 ^ (S + 1))
    (hMC1 : 2 ^ (n + S) < M * c.toNat) (hMC2 : M * c.toNat < 2 ^ (n + S) + c.toNat)
    (x : BitVec n) (q : Int) (hq : q = x.toInt * M / 2 ^ (n + S)) :
    x.sdiv (BitVec.ofInt n c) = BitVec.ofInt n q - x.sshiftRight (n - 1) := by
  have hc0 : 0 < c := by omega
  obtain ⟨C, rfl⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt hc0)
  simp only [Int.toNat_natCast] at hS3 hS4 hMC1 hMC2
  have hC0 : 0 < C := by omega
  have hpS : 2 ^ (S + 1) ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hCi : (C : Int) < 2 ^ (n - 1) := by
    have : C < 2 ^ (n - 1) := by omega
    exact_mod_cast this
  have hX1 := BitVec.le_toInt x
  have hX2 := BitVec.toInt_lt (x := x)
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sdiv, BitVec.toInt_sub, BitVec.toInt_ofInt q, Int.bmod_sub_bmod,
    BitVec.toInt_ofInt (C : Int), bmod_of_range (x := (C : Int)) (w := n) (by omega) (by omega) hCi,
    BitVec.toInt_sshiftRight, Int.shiftRight_eq_div_pow, Int.natCast_pow, Int.cast_ofNat_Int,
    div_pow_sgn (x := x.toInt) (k := n - 1) hX1 hX2, hq,
    sdiv_magic_int (by omega) hC0 hMC1 hMC2 (by omega) hX1 hX2]

/-- `m & 1 == 0` on the `uint64` pattern of `m < 2^n`: `m` is even. -/
theorem even_of_and_one {n M : Nat} (hn : n ≤ 64) (hM : M < 2 ^ n)
    (h : wrapInt 64 false ((pat64 (M : Int) &&& pat64 1 : Nat) : Int) = 0) : M % 2 = 0 := by
  have h64 : M < 2 ^ 64 := Nat.lt_of_lt_of_le hM (Nat.pow_le_pow_right (by decide) hn)
  rw [pat64_nat h64, show pat64 1 = 1 from rfl, Nat.and_one_is_mod] at h
  simp only [wrapInt, Bool.false_eq_true, ite_false] at h
  rw [show ((M % 2 : Nat) : Int).emod (2 ^ 64) = ((M % 2 : Nat) : Int) % 2 ^ 64 from rfl,
    Int.emod_eq_of_lt (by omega) (by omega)] at h
  omega

/-- `Div32/64` by `smagic` with an even `m` (`divmod.rules:107/113`):
`Hmul x (m/2) >> (s - 1) - (x >> (n - 1))`. -/
theorem sdiv_magic_hmul_even {n S M : Nat} {c : Int} (hn : 2 ≤ n) (hn64 : n ≤ 64)
    (h : SSpec n c S M) (hand : wrapInt 64 false ((pat64 (M : Int) &&& pat64 1 : Nat) : Int) = 0)
    (x : BitVec n) {a b : Nat} (ha : a = S - 1) (hb : b = n - 1) :
    x.sdiv (BitVec.ofInt n c) =
      (BitVec.extractLsb' n n (BitVec.signExtend (2 * n) x *
          BitVec.signExtend (2 * n) (BitVec.ofInt n (goQuo (M : Int) 2)))).sshiftRight a -
        x.sshiftRight b := by
  obtain ⟨hS1, hS2, hS3, hS4, -, hM2, hMC1, hMC2⟩ := h
  have hMe := even_of_and_one hn64 hM2 hand
  subst ha hb
  have hy : (BitVec.ofInt n (goQuo (M : Int) 2)).toInt = ((M / 2 : Nat) : Int) := by
    have hM2' : M / 2 < 2 ^ (n - 1) := by
      have : 2 ^ n = 2 * 2 ^ (n - 1) := by
        rw [← Nat.pow_succ']; exact congrArg (2 ^ ·) (by omega)
      omega
    have hM2i : ((M / 2 : Nat) : Int) < 2 ^ (n - 1) := by exact_mod_cast hM2'
    rw [BitVec.toInt_ofInt, show goQuo (M : Int) 2 = ((M / 2 : Nat) : Int) from rfl]
    exact bmod_of_range (by omega) (by omega) hM2i
  rw [sdiv_magic_tail hn hS2 hS3 hS4 hMC1 hMC2 x _ rfl]
  congr 1
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sshiftRight, toInt_hmul (by omega), hy, Int.shiftRight_eq_div_pow,
    Int.natCast_pow, Int.cast_ofNat_Int, Int.ediv_ediv_of_nonneg (Int.le_of_lt (two_pow_int_pos _)),
    ← Int.pow_add, BitVec.toInt_ofInt]
  have hM : (M : Int) = 2 * ((M / 2 : Nat) : Int) := by omega
  have hD : (2 : Int) ^ (n + S) = 2 * 2 ^ (n + (S - 1)) := by
    rw [← two_pow_int_succ]; exact congrArg (2 ^ ·) (by omega)
  rw [hM, hD, Int.mul_left_comm, Int.mul_ediv_mul_of_pos _ _ (by decide)]
  -- the quotient is in the signed range of `n` bits
  have hM2' : ((M / 2 : Nat) : Int) < 2 ^ (n - 1) := by rw [← hy]; exact BitVec.toInt_lt
  have hX1 := BitVec.le_toInt x
  have hX2 := BitVec.toInt_lt (x := x)
  obtain ⟨hP1, hP2⟩ := mul_le_of_abs (Y := ((M / 2 : Nat) : Int)) hX1 (Int.le_of_lt hX2)
    (by omega) (Int.le_of_lt hM2')
  have hKD : 2 * 2 ^ (n - 1) ≤ (2 : Int) ^ (n + (S - 1)) := by
    rw [← two_pow_int_succ]; exact two_pow_int_le (by omega)
  obtain ⟨hq1, hq2⟩ := ediv_range (two_pow_int_pos _) hKD hP1 hP2
  exact bmod_of_range (by omega) hq1 hq2

/-- `Div32/64` by `smagic` with an odd `m ≥ 2^(n-1)` (`divmod.rules:121/127`), `m` read as the
signed `m - 2^n`: `(x + Hmul x m) >> s - (x >> (n - 1))`. -/
theorem sdiv_magic_hmul_add {n S M : Nat} {c : Int} (hn : 2 ≤ n) (h : SSpec n c S M)
    (x : BitVec n) {a b : Nat} (ha : a = S) (hb : b = n - 1) :
    x.sdiv (BitVec.ofInt n c) =
      (x + BitVec.extractLsb' n n (BitVec.signExtend (2 * n) x *
          BitVec.signExtend (2 * n) (BitVec.ofNat n M))).sshiftRight a -
        x.sshiftRight b := by
  obtain ⟨-, hS2, hS3, hS4, hM1, hM2, hMC1, hMC2⟩ := h
  subst a b
  generalize hK : (2 : Int) ^ (n - 1) = K
  have hK0 : 0 < K := by rw [← hK]; exact two_pow_int_pos _
  have hn2 : (2 : Int) ^ n = 2 * K := by
    rw [← hK, ← two_pow_int_succ]; exact congrArg (2 ^ ·) (by omega)
  have hM1i : K ≤ (M : Int) := by rw [← hK]; exact_mod_cast hM1
  have hM2i : (M : Int) < 2 ^ n := by exact_mod_cast hM2
  have hy : (BitVec.ofNat n M).toInt = (M : Int) - 2 ^ n := by
    have h := Int.add_mul_bmod_self_right ((M : Int) - 2 ^ n) 1 (2 ^ n)
    rw [show (M : Int) - 2 ^ n + 1 * ((2 ^ n : Nat) : Int) = M by push_cast; omega] at h
    rw [BitVec.toInt_ofNat', h]
    exact bmod_of_range (w := n) (by omega) (by omega) (by omega)
  have hX1 := BitVec.le_toInt x
  have hX2 := BitVec.toInt_lt (x := x)
  rw [hK] at hX1 hX2
  rw [sdiv_magic_tail hn hS2 hS3 hS4 hMC1 hMC2 x _ rfl]
  congr 1
  apply BitVec.eq_of_toInt_eq
  have hpos : (0 : Int) < 2 ^ n := two_pow_int_pos n
  have e : x.toInt * ((M : Int) - 2 ^ n) / 2 ^ n = x.toInt * M / 2 ^ n - x.toInt := by
    rw [Int.mul_sub, show x.toInt * M - x.toInt * 2 ^ n = x.toInt * M + (-x.toInt) * 2 ^ n by
      rw [Int.neg_mul]; omega, Int.add_mul_ediv_right _ _ (Int.ne_of_gt hpos)]
    omega
  rw [BitVec.toInt_sshiftRight, BitVec.toInt_add, toInt_hmul (by omega), hy, e,
    show x.toInt + (x.toInt * M / 2 ^ n - x.toInt) = x.toInt * M / 2 ^ n by omega]
  obtain ⟨hP1, hP2⟩ := mul_range (M := M) hX1 hX2 (by omega : (M : Int) < 2 * K)
  have hq1 : -K ≤ x.toInt * M / 2 ^ n := by
    rw [Int.le_ediv_iff_mul_le hpos, hn2, Int.neg_mul]; omega
  have hq2 : x.toInt * M / 2 ^ n < K := by
    rw [Int.ediv_lt_iff_lt_mul hpos, hn2]; omega
  rw [bmod_of_range (w := n) (by omega) (by omega) (by omega), Int.shiftRight_eq_div_pow, Int.natCast_pow,
    Int.cast_ofNat_Int, Int.ediv_ediv_of_nonneg (Int.le_of_lt hpos), ← Int.pow_add,
    BitVec.toInt_ofInt]
  have hS : K ≤ K * 2 ^ S := by
    have := Int.mul_le_mul_of_nonneg_left (two_pow_int_le (Nat.zero_le S)) (Int.le_of_lt hK0)
    simpa using this
  have hD : (0 : Int) < 2 ^ S := two_pow_int_pos S
  rw [Int.pow_add, ← Int.ediv_ediv_of_nonneg (Int.le_of_lt hpos)]
  generalize x.toInt * M / 2 ^ n = q at hq1 hq2
  have h1 : -K ≤ q / 2 ^ S := by
    rw [Int.le_ediv_iff_mul_le hD, Int.neg_mul]; omega
  have h2 : q / 2 ^ S < K := by
    rw [Int.ediv_lt_iff_lt_mul hD]; omega
  exact bmod_of_range (x := q / 2 ^ S) (w := n) (by omega) (by omega) (by omega)

/-- `rule_auto`'s normalisation and case splits (after `divs_smagic`). -/
macro "divs_prefix" : tactic => `(tactic| (
  (try rule_ands)
  (try rule_clear_oracle)
  (try rule_norm)
  (try rule_ands)
  all_goals (repeat rule_split1)
  all_goals (try rule_widths)
  all_goals (repeat rule_gen1)
  all_goals (try simp only [GoFV.Proof.Rules.DV.int.injEq, GoFV.Proof.Rules.DV.bool.injEq] at *)
  all_goals (try rule_ands)
  all_goals (try rule_subst)
  all_goals (try rule_norm)
  all_goals (try simp_all only [rule_arith, rule_close_s])))

/-- Close a `smagic` goal of the wide form (`divmod.rules:87/93/99`). -/
macro "divs_wide" : tactic => `(tactic| (
  (try (simp only [GoFV.SSA.Sem.Val.retype] at *; rule_norm))
  exact GoFV.Proof.Rules.DivmodS.sdiv_magic_wide (by decide) (by decide)
    ‹GoFV.Proof.Rules.DivmodS.SSpec _ _ _ _› _
    (by have := (‹GoFV.Proof.Rules.DivmodS.SSpec _ _ _ _›).hS2; bv_omega) (by bv_omega)))

/-- Close a `smagic` goal of the form `x + Hmul x m` (`divmod.rules:121/127`). -/
macro "divs_add" : tactic => `(tactic| (
  exact GoFV.Proof.Rules.DivmodS.sdiv_magic_hmul_add (by decide)
    ‹GoFV.Proof.Rules.DivmodS.SSpec _ _ _ _› _
    (by have := (‹GoFV.Proof.Rules.DivmodS.SSpec _ _ _ _›).hS2; bv_omega) (by bv_omega)))

/-- Close a `smagic` goal of the form `Hmul x (m/2)`, `m` even (`divmod.rules:107/113`). -/
macro "divs_even" : tactic => `(tactic| (
  exact GoFV.Proof.Rules.DivmodS.sdiv_magic_hmul_even (by decide) (by decide)
    ‹GoFV.Proof.Rules.DivmodS.SSpec _ _ _ _› ‹GoFV.Rules.wrapInt 64 false _ = 0› _
    (by have := (‹GoFV.Proof.Rules.DivmodS.SSpec _ _ _ _›).hS2
        have := (‹GoFV.Proof.Rules.DivmodS.SSpec _ _ _ _›).hS1; bv_omega) (by bv_omega)))

end GoFV.Proof.Rules.DivmodS
