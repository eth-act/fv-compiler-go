import GoFV.Proof.Rules.DivisibleInv
import GoFV.Proof.Rules.NonVacuous
import GoFV.Rules.Generated.Generic.Values03
import GoFV.Rules.Generated.Generic.Values07

variable [GoFV.SSA.Sem.Addrs]

/-!
# `generic.rules`: comparisons with a product by an odd constant, `Mod` widened (#69)

* `(Eq (Const c) (Mul (Const d) x))` with `d` odd ⇒ `(Eq (Const c * inverse(d)) x)`
  (`generic.rules:315–318`, `Eq`/`Neq`): `modularMultiplicativeInverse(d)` is `inv64 d`
  (`modInverse_ok`), an inverse of `d` modulo `2^w` (`inv_bv`), so `c = d * x ⇔ c * inv = x`
  (`eq_mul_inv`).
* `(Eq8/16 (Mod x (Const c)) (Const 0))` ⇒ the same test on 32 bits (`generic.rules:1169–1175`):
  the zero-extended (sign-extended) operands have the same remainder (`umod_widen`,
  `srem_widen`); the rules hold for every `c`.
-/

namespace GoFV.Proof.Rules.Divisible

open GoFV.Rules

theorem eq_mul_inv {w : Nat} (C D x Y : BitVec w) (h : Y * D = 1#w) :
    (C == D * x) = (C * Y == x) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor
  · intro hc
    rw [hc, BitVec.mul_comm D x, BitVec.mul_assoc, BitVec.mul_comm D Y, h, BitVec.mul_one]
  · intro hc
    rw [← hc, BitVec.mul_comm C Y, ← BitVec.mul_assoc, BitVec.mul_comm D Y, h, BitVec.one_mul]

theorem ne_mul_inv {w : Nat} (C D x Y : BitVec w) (h : Y * D = 1#w) :
    (C != D * x) = (C * Y != x) := by
  rw [bne, bne, eq_mul_inv C D x Y h]

/-- The inverse modulo `2^64` of the pattern of `d` is an inverse of `d` at every width. -/
theorem inv_bv {w : Nat} (hw1 : 1 ≤ w) (hw : w ≤ 64) (d : Int) (y : Nat)
    (h : y * ((wrapInt 64 false d).emod (2 ^ 64)).toNat % 18446744073709551616 = 1) :
    BitVec.ofNat w y * BitVec.ofInt w d = 1#w := by
  apply BitVec.eq_of_toNat_eq
  have hp : (0 : Int) < 2 ^ 64 := by decide
  have hdv : (2 : Int) ^ w ∣ 2 ^ 64 := ⟨2 ^ (64 - w), by rw [← Int.pow_add]; congr 1; omega⟩
  have hX : ((wrapInt 64 false d).emod (2 ^ 64)).toNat % 2 ^ w = (BitVec.ofInt w d).toNat := by
    rw [toNat_ofInt, Magic.lowBits, wrapInt_false]
    show ((d % 2 ^ 64) % 2 ^ 64).toNat % 2 ^ w = (d % 2 ^ w).toNat
    rw [Int.emod_emod_of_dvd _ (Int.dvd_refl _)]
    apply Int.ofNat_inj.mp
    rw [Int.natCast_emod, Int.toNat_of_nonneg (Int.emod_nonneg d (by omega)),
      Int.toNat_of_nonneg (Int.emod_nonneg d (Int.ne_of_gt (Int.pow_pos (by decide))))]
    simp only [Int.natCast_pow, Int.cast_ofNat_Int]
    exact Int.emod_emod_of_dvd d hdv
  rw [BitVec.toNat_mul, BitVec.toNat_ofNat, ← hX, ← Nat.mul_mod,
    ← Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hw), show 2 ^ 64 = 18446744073709551616 by rfl, h,
    BitVec.toNat_ofNat]

theorem int_emod_eq (a b : Int) : a.emod b = a % b := rfl

theorem two_le_two_pow_int {w : Nat} (hw : 1 ≤ w) : (2 : Int) ≤ 2 ^ w := by
  have : 2 ^ 1 ≤ 2 ^ w := Nat.pow_le_pow_right (n := 2) (by decide) hw
  exact_mod_cast this

/-- `modularMultiplicativeInverse(uint64(d))` fails only on an even `d`. -/
theorem modInverse_err {w : Nat} (hw1 : 1 ≤ w) {c : Int} {s : String}
    (hodd : wrapInt w false (goRem (wrapInt w false c) 2) = 1)
    (h : Magic.modInverse ((wrapInt 64 false c).emod (2 ^ 64)).toNat = .error s) : False := by
  have h2 := two_le_two_pow_int hw1
  rw [wrapInt_false, wrapInt_false, goRem, int_emod_eq, int_emod_eq] at hodd
  have ha0 : 0 ≤ c % 2 ^ w := Int.emod_nonneg c (by omega)
  rw [Int.tmod_eq_emod_of_nonneg ha0] at hodd
  have hc2 : c % 2 ^ w % 2 = c % 2 :=
    Int.emod_emod_of_dvd c ⟨2 ^ (w - 1), by rw [← Int.pow_succ']; congr 1; omega⟩
  have hlt : c % 2 ^ w % 2 < 2 ^ w := by omega
  rw [Int.emod_eq_of_lt (Int.emod_nonneg _ (by decide)) hlt] at hodd
  unfold Magic.modInverse at h
  rw [wrapInt_false, int_emod_eq, int_emod_eq] at h
  split at h
  · rename_i hx
    simp only [bne_iff_ne, ne_eq] at hx
    omega
  · cases h

theorem toNat_ofInt_wrap {w v : Nat} (hwv : w ≤ v) (c : Int) :
    (BitVec.ofInt v (wrapInt w false c)).toNat = (BitVec.ofInt w c).toNat := by
  rw [BitVec.toNat_ofInt, BitVec.toNat_ofInt, wrapInt_false, int_emod_eq,
    show (((2 ^ v : Nat)) : Int) = 2 ^ v by simp, show (((2 ^ w : Nat)) : Int) = 2 ^ w by simp]
  have hp : (0 : Int) < 2 ^ w := Int.pow_pos (by decide)
  have hle : (2 : Int) ^ w ≤ 2 ^ v := by
    have : 2 ^ w ≤ 2 ^ v := Nat.pow_le_pow_right (by decide) hwv
    exact_mod_cast this
  rw [Int.emod_eq_of_lt (Int.emod_nonneg c (by omega))
    (Int.lt_of_lt_of_le (Int.emod_lt_of_pos c hp) hle)]

/-- Zero extension keeps the unsigned remainder. -/
theorem umod_widen {w v : Nat} (hwv : w ≤ v) (x : BitVec w) (c : Int) :
    (x % BitVec.ofInt w c == 0#w) =
      (BitVec.setWidth v x % BitVec.ofInt v (wrapInt w false c) == 0#v) := by
  have hc := toNat_ofInt_wrap hwv c
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← BitVec.toNat_inj, ← BitVec.toNat_inj,
    BitVec.toNat_umod, BitVec.toNat_umod, hc, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) hwv))]
  simp

theorem umod_widen_zero {w v : Nat} {c : Int} (h1 : ¬BitVec.ofInt w c = 0)
    (h2 : BitVec.ofInt v (wrapInt w false c) = 0) (hwv : w ≤ v) : False := by
  apply h1
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat h2
  rw [toNat_ofInt_wrap hwv] at this
  simpa using this

theorem toInt_ofInt_small {w v : Nat} (hw : 0 < w) (hwv : w ≤ v) {c : Int}
    (hlo : -(((2 ^ w : Nat) : Int) / 2) ≤ c) (hhi : c < (((2 ^ w : Nat) : Int) + 1) / 2) :
    (BitVec.ofInt v c).toInt = c ∧ (BitVec.ofInt w c).toInt = c := by
  have hp : (2 : Int) ^ w ≤ 2 ^ v := by
    have : 2 ^ w ≤ 2 ^ v := Nat.pow_le_pow_right (by decide) hwv
    exact_mod_cast this
  have h2 := two_le_two_pow_int hw
  simp only [Int.natCast_pow, Int.cast_ofNat_Int] at hlo hhi
  rw [BitVec.toInt_ofInt, BitVec.toInt_ofInt]
  constructor <;> apply Int.bmod_eq_of_le_mul_two <;> simp only [Int.natCast_pow, Int.cast_ofNat_Int] <;>
    omega

/-- Sign extension keeps the signed remainder. -/
theorem srem_widen {w v : Nat} (hw : 0 < w) (hwv : w ≤ v) (x : BitVec w) {c : Int}
    (hlo : -(((2 ^ w : Nat) : Int) / 2) ≤ c) (hhi : c < (((2 ^ w : Nat) : Int) + 1) / 2) :
    (x.srem (BitVec.ofInt w c) == 0#w) =
      ((BitVec.signExtend v x).srem (BitVec.ofInt v c) == 0#v) := by
  obtain ⟨hv, hw'⟩ := toInt_ofInt_small hw hwv hlo hhi
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, ← BitVec.toInt_inj, ← BitVec.toInt_inj,
    BitVec.toInt_srem, BitVec.toInt_srem, BitVec.toInt_signExtend_of_le hwv, hv, hw',
    BitVec.toInt_zero, BitVec.toInt_zero]

theorem srem_widen_zero {w v : Nat} {c : Int}
    (h1 : ¬BitVec.ofInt w c = 0) (h2 : BitVec.ofInt v c = 0) (hw : 0 < w) (hwv : w ≤ v)
    (hlo : -(((2 ^ w : Nat) : Int) / 2) ≤ c) (hhi : c < (((2 ^ w : Nat) : Int) + 1) / 2) :
    False := by
  obtain ⟨hv, hw'⟩ := toInt_ofInt_small hw hwv hlo hhi
  apply h1
  rw [← BitVec.toInt_inj, hw', show (0 : BitVec w) = 0#w from rfl, BitVec.toInt_zero]
  rw [h2] at hv
  rw [← hv]; exact BitVec.toInt_zero

end GoFV.Proof.Rules.Divisible

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

set_option hygiene false in
/-- `generic.rules:315–318`: the condition's first conjunct (`d` odd) evaluated, the
`modularMultiplicativeInverse` call split (failure contradicts `d` odd), `eq_mul_inv`. -/
macro "divisible_inv" : tactic => `(tactic| (
  rule_unfold
  (try rule_ands)
  (try rule_clear_oracle)
  divisible_gen
  simp (config := { decide := true }) only [rule_sem, rule_helper, rule_norm_s] at hcond
  obtain ⟨hodd, -⟩ := hcond
  rcases U with s | y
  · exact (GoFV.Proof.Rules.Divisible.modInverse_err (by decide) hodd hU).elim
  · obtain ⟨-, hy⟩ := GoFV.Proof.Rules.Divisible.modInverse_ok hU
    clear hU
    divisible_rest
    all_goals first
      | exact GoFV.Proof.Rules.Divisible.eq_mul_inv _ _ _ _
          (GoFV.Proof.Rules.Divisible.inv_bv (by decide) (by decide) _ _ hy)
      | exact GoFV.Proof.Rules.Divisible.ne_mul_inv _ _ _ _
          (GoFV.Proof.Rules.Divisible.inv_bv (by decide) (by decide) _ _ hy)))

set_option hygiene false in
/-- `generic.rules:1169–1175`: the condition is not needed; `umod_widen`/`srem_widen`, and the
case where only the widened divisor is zero is contradictory. -/
macro "divisible_widen" : tactic => `(tactic| (
  rule_unfold
  (try rule_ands)
  (try rule_clear_oracle)
  (try clear hcond)
  divisible_rest
  all_goals first
    | exact GoFV.Proof.Rules.Divisible.umod_widen (by decide) _ _
    | exact GoFV.Proof.Rules.Divisible.srem_widen (by decide) (by decide) _ (by omega) (by omega)
    | exact GoFV.Proof.Rules.Divisible.umod_widen_zero (by assumption) (by assumption) (by decide)
    | exact GoFV.Proof.Rules.Divisible.srem_widen_zero (by assumption) (by assumption) (by decide)
        (by decide) (by omega) (by omega)))

theorem r_generic_1169_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1169 := by
  divisible_widen

theorem r_generic_1171_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1171 := by
  divisible_widen

theorem r_generic_1173_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1173 := by
  divisible_widen

theorem r_generic_1175_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1175 := by
  divisible_widen

/-- `generic.rules:317`: `(Eq16 (Const16 [c]) (Mul16 (Const16 [d]) x))` at `c = 21`, `d = 3`,
`x = 7`. -/
theorem inst_r_generic_317 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_317
    (PEnv.ofLists [([1, 1], .i16 7)] [([], .bool)] (.int .w16) [([0], 21), ([0, 1], 3)])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_317]
  rule_eval
  rfl

end GoFV.Proof.Rules
