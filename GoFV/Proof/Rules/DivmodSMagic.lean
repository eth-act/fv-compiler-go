import GoFV.Rules.Helpers.Magic
import GoFV.Proof.Rules.Tactic

/-!
# Signed division by a constant: `smagic` (`divmod.rules`, #69)

`smagic_ok`: `smagicOK c` and `c` in the signed range of `n` bits make `smagic n c` succeed, with
`2^(n+s) < m*c < 2^(n+s) + c` (`SSpec`); `sdiv_magic_int`: then `⌊x*m / 2^(n+s)⌋ + [x < 0]` is
`x.tdiv c` on the signed range. `divs_smagic` replaces the helper call in a rule goal.
-/

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

end GoFV.Proof.Rules.DivmodS
