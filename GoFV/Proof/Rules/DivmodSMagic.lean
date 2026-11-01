import GoFV.Rules.Helpers.Magic
import GoFV.Proof.Rules.Tactic

namespace GoFV.Proof.Rules.DivmodS

open GoFV.Rules GoFV.Rules.Magic

/-- `⌈a/d⌉ * d` lies in `[a, a + d)`. -/
theorem ceil_div_mul {a d : Nat} (hd : 0 < d) :
    a ≤ (a + d - 1) / d * d ∧ (a + d - 1) / d * d ≤ a + d - 1 := by
  have h1 := Nat.div_add_mod (a + d - 1) d
  have h2 := Nat.mod_lt (a + d - 1) hd
  rw [Nat.mul_comm] at h1
  omega

theorem bitsLen_spec {d : Nat} (hd : 0 < d) : d < 2 ^ bitsLen d ∧ 2 ^ (bitsLen d - 1) ≤ d := by
  unfold bitsLen
  simp only [Nat.ne_of_gt hd, ite_false, Nat.add_sub_cancel]
  exact ⟨Nat.lt_log2_self, Nat.log2_self_le (Nat.ne_of_gt hd)⟩

/-- A divisor of a power of two is a power of two. -/
theorem dvd_two_pow {c : Nat} : ∀ {a : Nat}, c ∣ 2 ^ a → ∃ t, c = 2 ^ t
  | 0, h => ⟨0, Nat.eq_one_of_dvd_one h⟩
  | a + 1, h => by
    obtain ⟨q, hq⟩ := h
    rcases Nat.mod_two_eq_zero_or_one c with hc | hc
    · obtain ⟨t, ht⟩ := dvd_two_pow (a := a) (c := c / 2) ⟨q, by
        have : c = 2 * (c / 2) := by omega
        rw [this, Nat.pow_succ, Nat.mul_assoc] at hq; omega⟩
      exact ⟨t + 1, by rw [Nat.pow_succ]; omega⟩
    · have hq2 : q % 2 = 0 := by
        have h1 : (c * q) % 2 = 0 := by rw [← hq, Nat.pow_succ, Nat.mul_mod_left]
        rw [Nat.mul_mod, hc] at h1
        rcases Nat.mod_two_eq_zero_or_one q with h | h
        · exact h
        · rw [h] at h1; exact absurd h1 (by decide)
      have h2 : c * q = 2 * (c * (q / 2)) := by
        rw [← Nat.mul_assoc, Nat.mul_comm 2 c, Nat.mul_assoc,
          Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hq2)]
      exact dvd_two_pow (a := a) ⟨q / 2, by rw [Nat.pow_succ] at hq; omega⟩

theorem pat64_nat {C : Nat} (h : C < 2 ^ 64) : pat64 (C : Int) = C := by
  unfold pat64
  rw [show (C : Int).emod (2 ^ 64) = (C : Int) % 2 ^ 64 from rfl,
    Int.emod_eq_of_lt (by omega) (by omega)]
  rfl

theorem pat64_nat_sub_one {C : Nat} (h1 : 1 ≤ C) (h : C ≤ 2 ^ 64) :
    pat64 ((C : Int) - 1) = C - 1 := by
  unfold pat64
  rw [show ((C : Int) - 1).emod (2 ^ 64) = ((C : Int) - 1) % 2 ^ 64 from rfl,
    Int.emod_eq_of_lt (by omega) (by omega)]
  omega

/-- `notPow2 64 c` on a positive `c < 2^63`: `c` is not zero and not a power of two. -/
theorem notPow2_spec {c : Int} (h0 : 0 ≤ c) (h63 : c < 2 ^ 63) (h : notPow2 64 c = true) :
    0 < c.toNat ∧ ∀ k, c.toNat ≠ 2 ^ k := by
  obtain ⟨C, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  simp only [Int.toNat_natCast]
  have hC : C < 2 ^ 63 := by omega
  simp only [notPow2, ite_true, andPred, bitwise, GoTy.intInfo?, Option.getD_some,
    pat64_nat (show C < 2 ^ 64 by omega)] at h
  rcases Nat.eq_zero_or_pos C with hz | hz
  · subst hz
    simp [pat64, wrapInt] at h
  refine ⟨hz, fun k hk => ?_⟩
  subst hk
  rw [pat64_nat_sub_one hz (by omega), Nat.and_two_pow_sub_one_eq_mod, Nat.mod_self] at h
  simp [wrapInt] at h

/-- What `smagic n c = .ok (S, M)` gives (a structure: `simp_all` leaves it alone). -/
structure SSpec (n : Nat) (c : Int) (S M : Nat) : Prop where
  hS1 : 1 ≤ S
  hS2 : S + 2 ≤ n
  hS3 : 2 ^ S < c.toNat
  hS4 : c.toNat < 2 ^ (S + 1)
  hM1 : 2 ^ (n - 1) ≤ M
  hM2 : M < 2 ^ n
  hMC1 : 2 ^ (n + S) < M * c.toNat
  hMC2 : M * c.toNat < 2 ^ (n + S) + c.toNat

/-- `smagic n c` succeeds on a constant accepted by `smagicOK` in the signed range of `n` bits:
`s = ⌈log2 c⌉ - 1`, `m = ⌈2^(n+s)/c⌉` with `2^(n-1) ≤ m < 2^n` and `2^(n+s) < m*c < 2^(n+s) + c`. -/
theorem smagic_ok {n : Nat} {c : Int} (hn : 2 ≤ n) (hn64 : n ≤ 64) (hok : smagicOK c = true)
    (hc : c < 2 ^ (n - 1)) :
    ∃ S M : Nat, smagic n c = .ok ((S : Int), M) ∧ SSpec n c S M := by
  simp only [smagicOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨h0, hnp⟩ := hok
  have hp63 : (2 : Int) ^ (n - 1) ≤ 2 ^ 63 := by
    have : 2 ^ (n - 1) ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
    exact_mod_cast this
  obtain ⟨hC0, hCp⟩ := notPow2_spec h0 (by omega) hnp
  obtain ⟨C, rfl⟩ := Int.eq_ofNat_of_zero_le h0
  simp only [Int.toNat_natCast] at hC0 hCp ⊢
  have hCn : C < 2 ^ (n - 1) := by exact_mod_cast hc
  obtain ⟨hB1, hB2⟩ := bitsLen_spec hC0
  have hB : bitsLen C = (bitsLen C - 1) + 1 := by
    rcases Nat.eq_zero_or_pos (bitsLen C) with h | h
    · rw [h] at hB1; omega
    · omega
  generalize hS : bitsLen C - 1 = S at hB hB2
  rw [hB] at hB1
  have hSC : 2 ^ S < C := Nat.lt_of_le_of_ne hB2 (fun h => hCp S h.symm)
  have hS1 : 1 ≤ S := by
    rcases Nat.eq_zero_or_pos S with h | h
    · subst h; simp at hB1 hSC; omega
    · exact h
  have hSn : S + 2 ≤ n := by
    have : 2 ^ S < 2 ^ (n - 1) := by omega
    have := (Nat.pow_lt_pow_iff_right (by decide)).mp this
    omega
  have hpos : 0 < C := hC0
  obtain ⟨hlo, hhi⟩ := ceil_div_mul (a := 2 ^ (n + S)) hpos
  generalize hM : (2 ^ (n + S) + C - 1) / C = M at hlo hhi
  have hne : M * C ≠ 2 ^ (n + S) := by
    intro h
    obtain ⟨t, ht⟩ := dvd_two_pow (c := C) (a := n + S) ⟨M, by rw [← h, Nat.mul_comm]⟩
    exact hCp t ht
  have hlt : 2 ^ (n + S) < M * C := Nat.lt_of_le_of_ne hlo (Ne.symm hne)
  have hpn : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← Nat.pow_succ']; exact congrArg (2 ^ ·) (by omega)
  have hnS : 2 ^ (n + S) = 2 ^ (n - 1) * 2 ^ (S + 1) := by
    rw [← Nat.pow_add]; exact congrArg (2 ^ ·) (by omega)
  have hnS' : 2 ^ (n + S) = 2 ^ n * 2 ^ S := Nat.pow_add 2 n S
  have hMlo : 2 ^ (n - 1) ≤ M := by
    have : 2 ^ (n - 1) * C < M * C :=
      Nat.lt_of_le_of_lt (by rw [hnS]; exact Nat.mul_le_mul_left _ (Nat.le_of_lt hB1)) hlt
    exact Nat.le_of_lt (Nat.lt_of_mul_lt_mul_right this)
  have hMhi : M < 2 ^ n := by
    have h1 : 2 ^ n * (2 ^ S + 1) ≤ 2 ^ n * C := Nat.mul_le_mul_left _ hSC
    rw [Nat.mul_add, Nat.mul_one, ← hnS'] at h1
    exact Nat.lt_of_mul_lt_mul_right (a := C) (by omega)
  refine ⟨S, M, ?_, ⟨hS1, hSn, by simpa using hSC, by simpa using hB1, hMlo, hMhi,
    by simpa using hlt, by simp only [Int.toNat_natCast]; omega⟩⟩
  have hc0 : ¬ ((C : Int) ≤ 0) := by omega
  have hb1 : M >>> n = 0 := by
    rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_of_lt hMhi
  have hb2 : M >>> (n - 1) = 1 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  have hm : M % 2 ^ 64 = M :=
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hMhi (Nat.pow_le_pow_right (by decide) hn64))
  simp only [smagic, hc0, ite_false, Int.toNat_natCast, hS, hM, hb1, hb2, hm]
  rfl

theorem magicDV_ok (s : Int) (m : Nat) :
    magicDV (.ok (s, m)) = some (.strct [("s", .int s), ("m", .int m)]) := rfl

theorem strctField_s (s : Int) (m : Nat) :
    strctField [("s", DV.int s), ("m", DV.int (m : Int))] "s" = some (DV.int s) := by
  simp [strctField]

theorem strctField_m (s : Int) (m : Nat) :
    strctField [("s", DV.int s), ("m", DV.int (m : Int))] "m" = some (DV.int m) := by
  simp [strctField]

open Lean Meta Elab Tactic in
/-- Replace the `smagic n c` call (`c` accepted by `smagicOK`, in the signed range) by its
result `(S, M)` and the facts of `smagic_ok` (`hS1 … hMC2`). -/
elab "divs_smagic" : tactic => withMainContext do
  let find (e : Lean.Expr) := e.find? fun t => t.isAppOfArity ``GoFV.Rules.Magic.smagic 2
  let mut cand := find (← instantiateMVars (← getMainTarget))
  for h in ← getLCtx do
    if cand.isNone && !h.isImplementationDetail then
      cand := find (← instantiateMVars h.type)
  let some c := cand | throwError "divs_smagic: no smagic call"
  let n ← Term.exprToSyntax (c.getArg! 0)
  let x ← Term.exprToSyntax (c.getArg! 1)
  if c.getArg! 1 |>.isAppOfArity ``GoFV.Rules.wrapInt 3 then
    let w ← Term.exprToSyntax ((c.getArg! 1).getArg! 0)
    let a ← Term.exprToSyntax ((c.getArg! 1).getArg! 2)
    evalTactic (← `(tactic| have := GoFV.Proof.Rules.wrapInt_true_range $w $a))
  else if c.getArg! 1 |>.isAppOfArity ``Int64.toInt 1 then
    let a ← Term.exprToSyntax ((c.getArg! 1).getArg! 0)
    evalTactic (← `(tactic| have := GoFV.Proof.Rules.int64_toInt_range $a))
  let S := mkIdent `S
  let M := mkIdent `M
  let hsm := mkIdent `hsm
  let hspec := mkIdent `hspec
  evalTactic (← `(tactic| (
    obtain ⟨$S, $M, $hsm, $hspec⟩ :=
      GoFV.Proof.Rules.DivmodS.smagic_ok (n := $n) (c := $x) (by decide) (by decide)
        (by assumption) (by omega)
    simp only [$hsm:ident, GoFV.Proof.Rules.DivmodS.magicDV_ok,
      GoFV.Proof.Rules.DivmodS.strctField_s, GoFV.Proof.Rules.DivmodS.strctField_m] at *)))

theorem pow_split {n S : Nat} (hn : 1 ≤ n) : 2 ^ (n + S) = 2 ^ (n - 1) * 2 ^ (S + 1) := by
  rw [← Nat.pow_add]; exact congrArg (2 ^ ·) (by omega)

/-- Upper bound of the signed magic quotient: `y*M < (⌊y/C⌋ + 1) * 2^(n+S)` for `y ≤ 2^(n-1)`. -/
theorem magic_hi {n S M C y : Nat} (hn : 1 ≤ n) (hC0 : 0 < C)
    (hhi : M * C < 2 ^ (n + S) + C) (hC : C ≤ 2 ^ (S + 1)) (hy : y ≤ 2 ^ (n - 1)) :
    y * M < (y / C + 1) * 2 ^ (n + S) := by
  generalize hD : 2 ^ (n + S) = D at hhi
  have hD0 : 0 < D := by rw [← hD]; exact Nat.two_pow_pos _
  rcases Nat.eq_zero_or_pos y with h0 | hy1
  · subst h0; simp; omega
  apply Nat.lt_of_mul_lt_mul_right (a := C)
  have h1 : y * M * C < y * D + y * C := by
    rw [Nat.mul_assoc, ← Nat.mul_add]; exact (Nat.mul_lt_mul_left hy1).mpr hhi
  have h2 : y * C ≤ D := by
    rw [← hD, pow_split (S := S) hn]; exact Nat.mul_le_mul hy hC
  have h3 : y + 1 ≤ (y / C + 1) * C := by
    have := Nat.div_add_mod' y C
    have := Nat.mod_lt y hC0
    rw [Nat.add_mul, Nat.one_mul]; omega
  have h4 : (y + 1) * D ≤ (y / C + 1) * C * D := Nat.mul_le_mul_right D h3
  rw [Nat.add_mul, Nat.one_mul] at h4
  rw [Nat.mul_right_comm (y / C + 1)]
  omega

/-- Lower bound: `⌊y/C⌋ * 2^(n+S) ≤ y*M`, strict for `y > 0` when `2^(n+S) < M*C`. -/
theorem magic_lo {n S M C y : Nat} (hlo : 2 ^ (n + S) ≤ M * C) :
    y / C * 2 ^ (n + S) ≤ y * M := by
  calc y / C * 2 ^ (n + S) ≤ y / C * (M * C) := Nat.mul_le_mul_left _ hlo
    _ = (y / C * C) * M := by rw [Nat.mul_comm M C, ← Nat.mul_assoc]
    _ ≤ y * M := Nat.mul_le_mul_right _ (Nat.div_mul_le_self y C)

theorem magic_lo' {n S M C y : Nat} (hlo : 2 ^ (n + S) < M * C) (hy1 : 1 ≤ y) :
    y / C * 2 ^ (n + S) < y * M := by
  apply Nat.lt_of_mul_lt_mul_right (a := C)
  calc y / C * 2 ^ (n + S) * C = (y / C * C) * 2 ^ (n + S) := Nat.mul_right_comm _ _ _
    _ ≤ y * 2 ^ (n + S) := Nat.mul_le_mul_right _ (Nat.div_mul_le_self y C)
    _ < y * (M * C) := (Nat.mul_lt_mul_left hy1).mpr hlo
    _ = y * M * C := (Nat.mul_assoc _ _ _).symm

/-- Signed division by the magic number: for `-2^(n-1) ≤ x < 2^(n-1)`,
`⌊x*M / 2^(n+S)⌋ + [x < 0] = x.tdiv C` when `2^(n+S) < M*C < 2^(n+S) + C ≤ 2^(n+S) + 2^(S+1)`. -/
theorem sdiv_magic_int {n S M C : Nat} {x : Int} (hn : 1 ≤ n) (hC0 : 0 < C)
    (hlo : 2 ^ (n + S) < M * C) (hhi : M * C < 2 ^ (n + S) + C) (hC : C ≤ 2 ^ (S + 1))
    (hx1 : -(2 ^ (n - 1) : Int) ≤ x) (hx2 : x < 2 ^ (n - 1)) :
    x * M / 2 ^ (n + S) - (if x < 0 then -1 else 0) = x.tdiv C := by
  have hP : ((2 : Int) ^ (n - 1)) = ((2 ^ (n - 1) : Nat) : Int) := by simp
  have hDn : ((2 : Int) ^ (n + S)) = ((2 ^ (n + S) : Nat) : Int) := by simp
  rw [hP] at hx1 hx2
  rw [hDn]
  rcases Int.lt_or_le x 0 with hneg | hpos
  · obtain ⟨y, hy⟩ := Int.eq_ofNat_of_zero_le (a := -x) (by omega)
    have hx : x = -(y : Int) := by omega
    subst hx
    have hy1 : 1 ≤ y := by omega
    have hy2 : y ≤ 2 ^ (n - 1) := by omega
    have h1 := magic_hi hn hC0 hhi hC hy2
    have h2 := magic_lo' (n := n) (S := S) hlo hy1
    rw [if_pos hneg, Int.neg_tdiv, ← Int.ofNat_tdiv]
    generalize y / C = q at *
    have hD0 := Nat.two_pow_pos (n + S)
    generalize 2 ^ (n + S) = D at *
    have hD : (0 : Int) < D := by omega
    have h1' := Int.ofNat_lt.mpr h1
    have h2' := Int.ofNat_lt.mpr h2
    push_cast at h1' h2'
    have e : -(y : Int) * M / D = -(q : Int) - 1 := by
      rw [Int.ediv_eq_iff_of_pos hD]
      simp only [Int.sub_mul, Int.add_mul, Int.neg_mul, Int.one_mul] at h1' h2' ⊢
      omega
    rw [e]; omega
  · obtain ⟨y, rfl⟩ := Int.eq_ofNat_of_zero_le hpos
    have hy2 : y ≤ 2 ^ (n - 1) := by omega
    have h1 := magic_hi hn hC0 hhi hC hy2
    have h2 := magic_lo (y := y) (Nat.le_of_lt hlo)
    rw [if_neg (by omega), Int.sub_zero, ← Int.ofNat_tdiv]
    generalize y / C = q at *
    have hD0 := Nat.two_pow_pos (n + S)
    generalize 2 ^ (n + S) = D at *
    have hD : (0 : Int) < D := by omega
    have h1' := Int.ofNat_lt.mpr h1
    have h2' := Int.ofNat_le.mpr h2
    push_cast at h1' h2'
    rw [Int.ediv_eq_iff_of_pos hD]
    simp only [Int.add_mul, Int.one_mul] at h1' h2' ⊢
    omega

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

/-- `Div32/64` by `smagic` with an even `m` (`divmod.rules:107/113`):
`Hmul x (m/2) >> (s - 1) - (x >> (n - 1))`. -/
theorem sdiv_magic_hmul_even {n S M : Nat} {c : Int} (hn : 2 ≤ n) (h : SSpec n c S M)
    (hMe : M % 2 = 0) (x : BitVec n) {a b : Nat} (ha : a = S - 1) (hb : b = n - 1) :
    x.sdiv (BitVec.ofInt n c) =
      (BitVec.extractLsb' n n (BitVec.signExtend (2 * n) x *
          BitVec.signExtend (2 * n) (BitVec.ofInt n (goQuo (M : Int) 2)))).sshiftRight a -
        x.sshiftRight b := by
  obtain ⟨hS1, hS2, hS3, hS4, -, hM2, hMC1, hMC2⟩ := h
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

/-- `(x >>s (n-1)) >>> (n-k)` as a number: `2^k - 1` for a negative `x`, else `0`. -/
theorem bias_toNat {n k : Nat} (hk : k + 2 ≤ n) (x : BitVec n) :
    ((x.sshiftRight (n - 1)).toNat >>> (n - k) : Nat) = if x.toInt < 0 then 2 ^ k - 1 else 0 := by
  have hX1 := BitVec.le_toInt x
  have hX2 := BitVec.toInt_lt (x := x)
  have h1 := BitVec.toInt_sshiftRight (x := x) (n := n - 1)
  rw [Int.shiftRight_eq_div_pow, Int.natCast_pow, Int.cast_ofNat_Int,
    div_pow_sgn (x := x.toInt) (k := n - 1) hX1 hX2] at h1
  have h2 := BitVec.toInt_eq_toNat_cond (x.sshiftRight (n - 1))
  have h3 := (x.sshiftRight (n - 1)).isLt
  have hpn : 2 ^ n = 2 ^ k * 2 ^ (n - k) := by
    rw [← Nat.pow_add]; exact congrArg (2 ^ ·) (by omega)
  have hpk : 0 < 2 ^ k := Nat.two_pow_pos k
  have hpd : 0 < 2 ^ (n - k) := Nat.two_pow_pos (n - k)
  rw [Nat.shiftRight_eq_div_pow]
  generalize 2 ^ n = N at *
  generalize (x.sshiftRight (n - 1)).toNat = t at *
  split at h1
  · rw [if_pos (by assumption)]
    have hs : t = N - 1 := by
      split at h2 <;> omega
    rw [hs]
    apply Nat.div_eq_of_lt_le
    · rw [Nat.sub_mul, Nat.one_mul, ← hpn]; omega
    · rw [Nat.sub_add_cancel hpk, ← hpn]; omega
  · rw [if_neg (by assumption)]
    have hs : t = 0 := by
      split at h2 <;> omega
    rw [hs, Nat.zero_div]

/-- Signed division by `2^k` (`divmod.rules:21-33`): add the bias `2^k - 1` to a negative `x`
(`(x >>s (n-1)) >>> (n-k)`), then shift arithmetically by `k`. -/
theorem sdiv_pow2 {n k : Nat} (hk : k + 2 ≤ n) (x : BitVec n) {c : Int}
    (hc : c = ((2 ^ k : Nat) : Int)) {a b d : Nat} (ha : a = n - 1) (hb : b = n - k)
    (hd : d = k) :
    x.sdiv (BitVec.ofInt n c) = (x + x.sshiftRight a >>> b).sshiftRight d := by
  subst c a b d
  have hX1 := BitVec.le_toInt x
  have hX2 := BitVec.toInt_lt (x := x)
  have hkn : 2 ^ k < 2 ^ (n - 1) := Nat.pow_lt_pow_right (by decide) (by omega)
  have hkn' : ((2 ^ k : Nat) : Int) < 2 ^ (n - 1) := by
    have := Int.ofNat_lt.mpr hkn; push_cast at this ⊢; exact this
  have hD : (0 : Int) < ((2 ^ k : Nat) : Int) := by
    have := Nat.two_pow_pos k; omega
  have hb := bias_toNat hk x
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_sdiv, BitVec.toInt_ofInt,
    bmod_of_range (x := ((2 ^ k : Nat) : Int)) (w := n) (by omega) (by omega) hkn',
    BitVec.toInt_sshiftRight, BitVec.toInt_add, BitVec.toInt_ushiftRight, if_neg (by omega),
    hb, Int.shiftRight_eq_div_pow]
  generalize hK : ((2 ^ k : Nat) : Int) = D at *
  split
  · rename_i hneg
    obtain ⟨y, hy⟩ := Int.eq_ofNat_of_zero_le (a := -x.toInt) (by omega)
    have hT : (((2 ^ k - 1 : Nat) : Nat) : Int) = D - 1 := by
      rw [← hK]; have := Nat.two_pow_pos k; omega
    rw [hT, bmod_of_range (x := x.toInt + (D - 1)) (w := n) (by omega) (by omega) (by omega)]
    have ht : x.toInt.tdiv D = -((y / 2 ^ k : Nat) : Int) := by
      rw [show x.toInt = -(y : Int) by omega, Int.neg_tdiv, ← hK, ← Int.ofNat_tdiv]
    have hq := Nat.div_add_mod y (2 ^ k)
    have hr := Nat.mod_lt y (Nat.two_pow_pos k)
    have hq' : (y : Int) = D * ((y / 2 ^ k : Nat) : Int) + ((y % 2 ^ k : Nat) : Int) := by
      rw [← hK]; exact_mod_cast hq.symm
    have hr' : ((y % 2 ^ k : Nat) : Int) < D := by rw [← hK]; exact_mod_cast hr
    have e : (x.toInt + (D - 1)) / D = -((y / 2 ^ k : Nat) : Int) := by
      rw [Int.ediv_eq_iff_of_pos hD, Int.neg_mul, Int.mul_comm]
      omega
    rw [ht, e]
    apply bmod_of_range (w := n) (by omega)
    · have h1 : (0 : Int) ≤ ((y / 2 ^ k : Nat) : Int) := Int.natCast_nonneg _
      have h2 : D * ((y / 2 ^ k : Nat) : Int) ≤ y := by omega
      have h3 : 1 * ((y / 2 ^ k : Nat) : Int) ≤ D * ((y / 2 ^ k : Nat) : Int) :=
        Int.mul_le_mul_of_nonneg_right (by omega) h1
      omega
    · have : (0 : Int) ≤ ((y / 2 ^ k : Nat) : Int) := Int.natCast_nonneg _
      omega
  · rename_i hpos
    rw [show (((0 : Nat) : Int)) = 0 from rfl, Int.add_zero, BitVec.toInt_bmod_cancel,
      Int.tdiv_eq_ediv_of_nonneg (by omega)]
    apply bmod_of_range (w := n) (by omega)
    · exact Int.le_trans (by omega) (Int.ediv_nonneg (by omega) (by omega))
    · exact Int.lt_of_le_of_lt (Int.ediv_le_self _ (by omega)) hX2

/-- A positive `C` with `C &&& (C - 1) = 0` is a power of two. -/
theorem eq_two_pow_of_and_pred {C : Nat} (h0 : 0 < C) (h : C &&& (C - 1) = 0) :
    C = 2 ^ Nat.log2 C := by
  have h1 := Nat.log2_self_le (Nat.ne_of_gt h0)
  have h2 := Nat.lt_log2_self (n := C)
  generalize Nat.log2 C = k at *
  false_or_by_contra
  rename_i hne
  have hk := congrArg (Nat.testBit · k) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at hk
  have hp : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; omega
  rw [show C = 2 ^ k + (C - 2 ^ k) by omega, show 2 ^ k + (C - 2 ^ k) - 1 = 2 ^ k + (C - 2 ^ k - 1)
    by omega, Nat.testBit_two_pow_add_eq, Nat.testBit_two_pow_add_eq,
    Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)] at hk
  simp at hk

/-- `isPowerOfTwo(c)` on a `w`-bit constant `0 < c < 2^(w-1)`: `c = 2^k`, `bitsLen c = k + 1`
(`log(c) = k`). -/
theorem pow2_of_andPred {w : Nat} {c : Int} (hw : 2 ≤ w) (hw64 : w ≤ 64) (h0 : 0 < c)
    (hc : c < 2 ^ (w - 1))
    (h : wrapInt w true (wrapInt w true ((pat64 c &&& pat64 (c - 1) : Nat) : Int)) = 0) :
    ∃ k, c = ((2 ^ k : Nat) : Int) ∧ k + 2 ≤ w ∧ bitsLen (c.emod (2 ^ w)).toNat = k + 1 := by
  obtain ⟨C, rfl⟩ := Int.eq_ofNat_of_zero_le (Int.le_of_lt h0)
  have hp : (2 : Int) ^ (w - 1) ≤ 2 ^ 63 := two_pow_int_le (by omega)
  have hCw : C < 2 ^ (w - 1) := by exact_mod_cast hc
  have h63 : C < 2 ^ 64 := Nat.lt_of_lt_of_le hCw (Nat.pow_le_pow_right (by decide) (by omega))
  rw [pat64_nat h63, pat64_nat_sub_one (by omega) (by omega)] at h
  have hand : C &&& (C - 1) ≤ C := Nat.and_le_left
  have hr : ((C &&& (C - 1) : Nat) : Int) < 2 ^ (w - 1) := by
    have : C &&& (C - 1) < 2 ^ (w - 1) := by omega
    exact_mod_cast this
  simp only [wrapInt, ite_true] at h
  rw [bmod_of_range (x := ((C &&& (C - 1) : Nat) : Int)) (w := w) (by omega) (by omega) hr,
    bmod_of_range (x := ((C &&& (C - 1) : Nat) : Int)) (w := w) (by omega) (by omega) hr] at h
  have hC := eq_two_pow_of_and_pred (C := C) (by omega) (by exact_mod_cast h)
  refine ⟨Nat.log2 C, by rw [← hC], ?_, ?_⟩
  · have : 2 ^ Nat.log2 C < 2 ^ (w - 1) := by omega
    have := (Nat.pow_lt_pow_iff_right (by decide)).mp this
    omega
  · have hCw' : (C : Int) < 2 ^ w := by
      have : C < 2 ^ w := Nat.lt_of_lt_of_le hCw (Nat.pow_le_pow_right (by decide) (by omega))
      exact_mod_cast this
    rw [show (C : Int).emod (2 ^ w) = (C : Int) % 2 ^ w from rfl,
      Int.emod_eq_of_lt (by omega) hCw', Int.toNat_natCast]
    unfold bitsLen
    rw [if_neg (by omega)]

/-- `m & 1 == 0` on the `uint64` pattern of `m < 2^n`: `m` is even. -/
theorem even_of_and_one {n M : Nat} (hn : n ≤ 64) (hM : M < 2 ^ n)
    (h : wrapInt 64 false ((pat64 (M : Int) &&& pat64 1 : Nat) : Int) = 0) : M % 2 = 0 := by
  have h64 : M < 2 ^ 64 := Nat.lt_of_lt_of_le hM (Nat.pow_le_pow_right (by decide) hn)
  rw [pat64_nat h64, show pat64 1 = 1 from rfl, Nat.and_one_is_mod] at h
  simp only [wrapInt, Bool.false_eq_true, ite_false] at h
  rw [show ((M % 2 : Nat) : Int).emod (2 ^ 64) = ((M % 2 : Nat) : Int) % 2 ^ 64 from rfl,
    Int.emod_eq_of_lt (by omega) (by omega)] at h
  omega

open Lean Meta Elab Tactic in
/-- Close `x.sdiv (BitVec.ofInt w c) = (x + (x >>s (w-1)) >>> (w - log c)) >>s log c` from
`isPowerOfTwo(c)` (`c > 0`, `wrapInt w true (andPred _ c) = 0`) and the range of `c`. -/
elab "divs_pow2" : tactic => withMainContext do
  let some t := (← instantiateMVars (← getMainTarget)).find? fun t =>
      t.isAppOfArity ``BitVec.sdiv 3 && (t.getArg! 2).isAppOfArity ``BitVec.ofInt 2
    | throwError "divs_pow2: no sdiv by a constant"
  let w ← Term.exprToSyntax ((t.getArg! 2).getArg! 0)
  let c ← Term.exprToSyntax ((t.getArg! 2).getArg! 1)
  let x ← Term.exprToSyntax (t.getArg! 1)
  let mut hand : Option Lean.Expr := none
  for h in ← getLCtx do
    if h.isImplementationDetail then continue
    let ty ← instantiateMVars h.type
    if let some (_, l, _) := ty.eq? then
      if l.isAppOfArity ``GoFV.Rules.wrapInt 3 && (l.getArg! 2).isAppOfArity ``GoFV.Rules.andPred 2 then
        hand := some h.toExpr
  let some handE := hand | throwError "divs_pow2: no `isPowerOfTwo` fact"
  let hs ← Term.exprToSyntax handE
  let hp := mkIdent `hpow
  evalTactic (← `(tactic| (
    have $hp:ident := $hs
    simp only [GoFV.Rules.andPred, GoFV.Rules.bitwise, GoFV.Rules.GoTy.intInfo?,
      Option.getD_some] at $hp:ident
    obtain ⟨k, hk, hkw, hlog⟩ := GoFV.Proof.Rules.DivmodS.pow2_of_andPred (w := $w) (c := $c)
      (by decide) (by decide) (by omega) (by omega) $hp
    rw [hlog]
    exact GoFV.Proof.Rules.DivmodS.sdiv_pow2 hkw $x hk (by bv_omega) (by bv_omega) (by bv_omega))))

end GoFV.Proof.Rules.DivmodS
