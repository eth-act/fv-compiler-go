import GoFV.Proof.Rules.FloatCmp
import GoFV.Rules.Generated.Generic.Values07

/-!
# Float arithmetic rules (`docs/proofs/rules.md`, #69)

`generic.rules:1328` `(Mul64F x (Const64F [2])) => (Add64F x x)`. In the IEEE core
(`GoFV.IEEE`), `round` only sees the value `mant * 2^exp`: moving a power of two between the
mantissa and the exponent does not change it (`round_scale`). `x * 2` rounds `m * 2^52` at
exponent `e - 51` (the constant `2` unpacks as `2^52 * 2^-51`), `x + x` rounds `2m` at `e`: the
same value (`mul_two_eq_add`, any format, either operand order). NaNs, infinities and zeros
give the same result case by case (the first NaN operand quietened, `±∞`, `±0` with `x`'s sign).
-/

namespace GoFV.Proof.Rules.FloatArith
open GoFV.IEEE

theorem log2_mul_pow (m k : Nat) (hm : m ≠ 0) : (m * 2 ^ k).log2 = m.log2 + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_comm _ 2, Nat.log2_two_mul, ih]; · omega
    exact Nat.mul_ne_zero hm (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k))

theorem truncShift_mul_pow (q t : Nat) (_ht : 0 < t) : truncShift (q * 2 ^ t) t false = (q, .exact) := by
  unfold truncShift
  simp [Nat.mul_div_cancel _ (Nat.two_pow_pos t)]

theorem truncShift_scale (m t k : Nat) (ht : 0 < t) :
    truncShift (m * 2 ^ k) (t + k) false = truncShift m t false := by
  unfold truncShift
  have hk := Nat.two_pow_pos k
  have h1 : m * 2 ^ k / 2 ^ (t + k) = m / 2 ^ t := by
    rw [Nat.pow_add, Nat.mul_div_mul_right _ _ hk]
  have h2 : m * 2 ^ k % 2 ^ (t + k) = m % 2 ^ t * 2 ^ k := by
    rw [Nat.pow_add, Nat.mul_mod_mul_right]
  have h3 : 2 ^ (t + k - 1) = 2 ^ (t - 1) * 2 ^ k := by
    rw [← Nat.pow_add]; congr 1; omega
  simp only [h1, h2, h3, Nat.mul_eq_zero, Nat.mul_lt_mul_right hk, Nat.pow_eq_zero,
    Nat.mul_left_inj (Nat.pos_iff_ne_zero.mp hk)]
  simp

theorem pair_scale (m k : Nat) (U e : Int) :
    (if U - (e - k) ≤ 0 then (m * 2 ^ k * 2 ^ (-(U - (e - k))).toNat, Err.exact)
      else truncShift (m * 2 ^ k) (U - (e - k)).toNat false) =
    (if U - e ≤ 0 then (m * 2 ^ (-(U - e)).toNat, Err.exact)
      else truncShift m (U - e).toNat false) := by
  by_cases ha : U - (e - k) ≤ 0
  · simp only [ha, show U - e ≤ 0 by omega, ↓reduceIte, Nat.mul_assoc, ← Nat.pow_add]
    congr 3; omega
  · simp only [ha, ↓reduceIte]
    by_cases hb : U - e ≤ 0
    · simp only [hb, ↓reduceIte]
      obtain ⟨t, ht⟩ : ∃ t, (U - (e - k)).toNat = t := ⟨_, rfl⟩
      obtain ⟨j, hj⟩ : ∃ j, (-(U - e)).toNat = j := ⟨_, rfl⟩
      have hk : 2 ^ k = 2 ^ j * 2 ^ t := by rw [← Nat.pow_add]; congr 1; omega
      rw [ht, hj, hk, ← Nat.mul_assoc, truncShift_mul_pow _ _ (by omega)]
    · simp only [hb, ↓reduceIte]
      rw [show (U - (e - k)).toNat = (U - e).toNat + k by omega,
        truncShift_scale _ _ _ (by omega)]

/-- Rounding is invariant under moving powers of two between the mantissa and the exponent. -/
theorem round_scale (f : Fmt) (rm : RMode) (s : Bool) (m k : Nat) (e : Int) :
    round f rm s (m * 2 ^ k) (e - k) = round f rm s m e := by
  by_cases hm : m = 0
  · simp [round, hm]
  have hm' : m * 2 ^ k ≠ 0 := Nat.mul_ne_zero hm (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k))
  unfold round
  simp only [hm, hm', ↓reduceIte]
  rw [log2_mul_pow m k hm]
  have hx : ((m.log2 + k : Nat) : Int) + (e - k) = m.log2 + e := by push_cast; omega
  simp only [hx, Bool.false_eq_true, ↓reduceIte, pair_scale]

theorem unpack_mant_ne_zero (f : Fmt) (x : Bits f)
    (ht : (unpack f x).1 = .denormal ∨ (unpack f x).1 = .nonzero) : (unpack f x).2.2.1 ≠ 0 := by
  revert ht
  unfold unpack
  dsimp only
  split <;> (try split) <;> (try split) <;> (try split) <;> simp_all

/-- `x * c = x + x` for a constant `c` that unpacks as `2` (`2^F * 2^(1-F)`), in either operand
order. -/
theorem mul_two_eq_add (f : Fmt) (rm : RMode) (c x : Bits f) (hF : 1 ≤ f.F)
    (hc : unpack f c = (.nonzero, false, 2 ^ f.F, 1 - (f.F : Int))) :
    mul f rm x c = add f rm x x ∧ mul f rm c x = add f rm x x := by
  unfold mul add
  rcases hx : unpack f x with ⟨t, s, m, e⟩
  simp only [hc]
  have key : t = .denormal ∨ t = .nonzero →
      round f rm (s != false) (m * 2 ^ f.F) (e + (1 - (f.F : Int))) =
        roundSum f rm (addExact s m e s m e).1 (addExact s m e s m e).2 := by
    intro ht
    have hm := unpack_mant_ne_zero f x (by rw [hx]; exact ht)
    simp only [hx] at hm
    have h1 : m * 2 ^ f.F = 2 * m * 2 ^ (f.F - 1) := by
      rw [Nat.mul_comm 2 m, Nat.mul_assoc, ← Nat.pow_succ']; congr 2; omega
    have h2 : e + (1 - (f.F : Int)) = e - ((f.F - 1 : Nat) : Int) := by omega
    rw [h1, h2, round_scale]
    unfold addExact roundSum signed
    simp only [Int.min_self, Int.sub_self, Int.toNat_zero, Nat.pow_zero, Nat.mul_one]
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · have h3 : ((m : Int) + m).natAbs = 2 * m := by omega
      have h4 : decide ((m : Int) + m < 0) = false := by simp only [decide_eq_false_iff_not]; omega
      rw [h3, h4]; simp only [show ¬((m : Int) + m = 0) by omega, ↓reduceIte]; rfl
    · have h3 : (-(m : Int) + -m).natAbs = 2 * m := by omega
      have h4 : decide (-(m : Int) + -m < 0) = true := by simp only [decide_eq_true_eq]; omega
      rw [h3, h4]; simp only [show ¬(-(m : Int) + -m = 0) by omega, ↓reduceIte]; rfl
  have key2 : round f rm (false != s) (2 ^ f.F * m) (1 - (f.F : Int) + e) =
      round f rm (s != false) (m * 2 ^ f.F) (e + (1 - (f.F : Int))) := by
    rw [Nat.mul_comm, Int.add_comm]; cases s <;> rfl
  cases t
  case denormal | nonzero =>
    have k := key (by simp)
    simp only [processNaNs, reduceCtorEq, ↓reduceIte, false_and, and_false, or_self]
    exact ⟨k, key2.trans k⟩
  all_goals cases s <;> simp_all [processNaNs, processNaN]

open GoFV.SSA GoFV.SSA.Sem

/-- `Mul64F v 2` is `Add64F v v` on every value (`poison` unless `v` is a 64-bit word). -/
theorem fops_mul_two64 (v : Val) :
    FOps.mul .w64 [v, .int .w64 0x4000000000000000#64] = FOps.add .w64 [v, v] := by
  have hu : unpack .b64 0x4000000000000000#64 = (.nonzero, false, 2 ^ 52, 1 - 52) := by decide
  have hm : FOps.mul .w64 [v, .int .w64 0x4000000000000000#64] =
      int2 .w64 (fun x y => .int .w64 (FOps.ordered (IEEE.mul .b64 .rne) x y))
        [v, .int .w64 0x4000000000000000#64] := rfl
  have ha : FOps.add .w64 [v, v] =
      int2 .w64 (fun x y => .int .w64 (FOps.ordered (IEEE.add .b64 .rne) x y)) [v, v] := rfl
  have hmul := fun x => mul_two_eq_add .b64 .rne 0x4000000000000000#64 x (by decide) hu
  rw [hm, ha]
  simp only [int2]
  cases h : v.asInt .w64 with
  | none => rfl
  | some x =>
    simp only [Val.asInt, ↓reduceDIte, FOps.ordered, Nat.lt_irrefl, ↓reduceIte]
    split
    · rw [(hmul x).2]
    · rw [(hmul x).1]

end GoFV.Proof.Rules.FloatArith

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem

/-- `generic.rules:1328`: `(Mul64F x (Const64F [2])) => (Add64F x x)` -/
theorem r_generic_1328_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1328 := by
  rule_unfold
  obtain ⟨-, h1⟩ := hat
  simp only [DV.f64.injEq] at hc
  have hk : Val.retype (e.ty [1]) (FOps.const64 (e.auxInt [1])) =
      .int .w64 0x4000000000000000#64 := by
    rw [h1, FOps.const64, hc]; rfl
  rw [hk, FloatArith.fops_mul_two64] at hty ⊢
  exact refines_retype_of_hasTy hty

end GoFV.Proof.Rules
