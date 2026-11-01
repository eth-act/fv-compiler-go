import GoFV.Proof.Rules.Tactic

/-!
# Non-negative operands (`isNonNegative`, `generic.rules:610`, `:611`, `:1138`; #69)

Closers for the goals of the `isNonNegative` rules that `rule_close` would otherwise leave to
`bv_decide` (whose `_native` axioms the axioms audit rejects): a signed comparison with `0`/`1`
of a value with a clear sign bit is an unsigned one, and `x srem -2^63 = x`.
-/

namespace GoFV.Proof.Rules.NonNegCmp

theorem slt_zero_left_of_msb {n : Nat} (x : BitVec n) (hx : (!x.msb) = true) (c : BitVec n)
    (hc : c = 0#n) : (0#n).slt x = (c != x) := by
  subst hc
  simp only [Bool.not_eq_true'] at hx
  rw [BitVec.slt_eq_ult, hx, BitVec.msb_zero, bne_self_eq_false, Bool.false_xor, Bool.eq_iff_iff,
    BitVec.ult_iff_lt, bne_iff_ne, ne_eq, BitVec.lt_def, BitVec.toNat_eq, BitVec.toNat_zero]
  omega

theorem slt_one_right_of_msb {n : Nat} (hn : 2 ≤ n) (x : BitVec n) (hx : (!x.msb) = true)
    (c : BitVec n) (hc : c = 0#n) : x.slt 1#n = (c == x) := by
  subst hc
  simp only [Bool.not_eq_true'] at hx
  have h2 : 1 < 2 ^ (n - 1) := Nat.one_lt_two_pow (by omega)
  have hpn : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← Nat.pow_succ']; congr 1; omega
  have h1 : (1#n).toNat = 1 := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hm : (1#n).msb = false := by
    rw [BitVec.msb_eq_decide, h1]; simp only [decide_eq_false_iff_not, Nat.not_le]; omega
  rw [BitVec.slt_eq_ult, hx, hm, bne_self_eq_false, Bool.false_xor, Bool.eq_iff_iff,
    BitVec.ult_iff_lt, beq_iff_eq, BitVec.lt_def, h1, BitVec.toNat_eq, BitVec.toNat_zero]
  omega

theorem srem_intMin64_of_msb (x : BitVec 64) (hx : (!x.msb) = true) :
    x.srem (BitVec.ofInt 64 (-9223372036854775808)) = x := by
  simp only [Bool.not_eq_true'] at hx
  have hl : x.toNat < 2 ^ 63 := by
    rw [BitVec.msb_eq_decide] at hx; simpa using hx
  rw [BitVec.srem, hx, show (BitVec.ofInt 64 (-9223372036854775808)).msb = true by decide]
  simp only [BitVec.neg_eq, BitVec.umod_eq]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_umod, show (-(BitVec.ofInt 64 (-9223372036854775808))).toNat = 2 ^ 63 by decide,
    Nat.mod_eq_of_lt hl]

end GoFV.Proof.Rules.NonNegCmp
