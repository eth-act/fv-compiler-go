import GoFV.Proof.Rules.DivmodSBV

/-!
# Signed division by a power of two (`divmod.rules:21-33`, #69)

`sdiv_pow2`: `x.sdiv (2^k)` is `(x + (x >>s (n-1)) >>> (n-k)) >>s k`; `pow2_of_andPred`:
`isPowerOfTwo(c)` on an `n`-bit constant gives `c = 2^k` with `log(c) = k`; `divs_pow2` closes a
rule goal with both.
-/

namespace GoFV.Proof.Rules.DivmodS

open GoFV.Rules GoFV.Rules.Magic

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
