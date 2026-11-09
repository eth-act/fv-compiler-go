import GoFV.Proof.Rules.FloatCmp
import GoFV.Proof.Rules.NonVacuous
import GoFV.Rules.Generated.Generic.Values07
import GoFV.Rules.Generated.Generic.Values02

/-!
# Float arithmetic rules (`docs/proofs/rules.md`, #69)

`generic.rules:1328` `(Mul64F x (Const64F [2])) => (Add64F x x)`. In the IEEE core
(`GoFV.IEEE`), `round` only sees the value `mant * 2^exp`: moving a power of two between the
mantissa and the exponent does not change it (`round_scale`). `x * 2` rounds `m * 2^52` at
exponent `e - 51` (the constant `2` unpacks as `2^52 * 2^-51`), `x + x` rounds `2m` at `e`: the
same value (`mul_two_eq_add`, any format, either operand order). NaNs, infinities and zeros
give the same result case by case (the first NaN operand quietened, `±∞`, `±0` with `x`'s sign).

`generic.rules:1331` `(Div64F x (Const64F [c])) && reciprocalExact64(c) => (Mul64F x
(Const64F [1/c]))`. `reciprocalExact64` makes `c` a power of two `±2^(b-1023)` with biased
exponent `1 ≤ b ≤ 2045` (`recip_pack`), so `1/c` is exact: the power of two with biased exponent
`2046 - b` (`div_pow2_recip`, via `round_pow2`). Both unpack with mantissa `2^52`, and their
exponents add to `-104`; `x / c` rounds `m * 2^56` four places below where `x * (1/c)` rounds
`m * 2^52`, the same value (`div_eq_mul_pow2` by `round_scale`, either operand order of the
multiplication). NaNs, infinities and zeros again agree case by case.
-/

namespace GoFV.Proof.Rules.FloatArith
open GoFV.IEEE

variable [GoFV.SSA.Sem.Addrs]

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

/-- The encoding of a binary64 number with fraction 0 and biased exponent `b`. -/
theorem pack_b64_toNat (s : Bool) (b : Nat) (h2 : b ≤ 2046) :
    (pack .b64 s b 0).toNat = (if s then 9223372036854775808 else 0) + b * 4503599627370496 := by
  show (BitVec.ofNat 64 ((if s then 9223372036854775808 else 0) + b * 4503599627370496 + 0)).toNat = _
  rw [BitVec.toNat_ofNat, Nat.add_zero]
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- A normal binary64 power of two unpacks to its exponent. -/
theorem unpack_pack_pow2 (s : Bool) (b : Nat) (h1 : 1 ≤ b) (h2 : b ≤ 2046) :
    unpack .b64 (pack .b64 s b 0) = (.nonzero, s, 2 ^ 52, (b : Int) - 1075) := by
  have hv := pack_b64_toNat s b h2
  unfold unpack signOf expOf fracOf
  simp only [hv, Nat.reducePow, Nat.reduceAdd, Nat.reduceSub]
  have hexp : ((if s then 9223372036854775808 else 0) + b * 4503599627370496) /
      4503599627370496 % 2048 = b := by
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have hfr : ((if s then 9223372036854775808 else 0) + b * 4503599627370496) %
      4503599627370496 = 0 := by
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have hsg : decide (9223372036854775808 ≤
      (if s then 9223372036854775808 else 0) + b * 4503599627370496) = s := by
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq,
      decide_eq_false_iff_not] <;> omega
  have hb0 : b ≠ 0 := by omega
  have hb1 : b ≠ 2047 := by omega
  simp only [hexp, hfr, hsg, hb0, Fmt.expOnes, Fmt.bias, Nat.reducePow, Nat.reduceSub, hb1,
    ↓reduceIte, Nat.add_zero, Prod.mk.injEq, true_and]
  omega

/-- `round` of `2^108 * 2^e`, a normal binary64 power of two: exact. -/
theorem round_pow2 (s : Bool) (e : Int) (h1 : 1 ≤ 1131 + e) (h2 : 1131 + e ≤ 2046) :
    round .b64 .rne s (2 ^ 108) e = pack .b64 s (1131 + e).toNat 0 := by
  have hl : (2 ^ 108 : Nat).log2 = 108 := Nat.log2_two_pow
  have ht : truncShift (2 ^ 52 * 2 ^ 56) 56 false = (2 ^ 52, .exact) :=
    truncShift_mul_pow _ _ (by omega)
  unfold round
  have hmin : Fmt.b64.minExp = -1022 := by decide
  have hexp : Fmt.b64.expOnes = 2047 := by decide
  have hmax : max (((108 : Nat) : Int) + e - -1022 + 1) 0 = 1131 + e := by omega
  have hz : (1131 + e = 0) = False := by simp only [eq_iff_iff, iff_false]; omega
  have hs : (((108 : Nat) : Int) + e - ((52 : Nat) : Int) - e) = 56 := by omega
  have h56 : ¬ ((56 : Int) ≤ 0) := by omega
  simp only [hl, hmin, hexp, hmax, hz, ↓reduceIte, hs, h56, show (56 : Int).toNat = 56 by rfl]
  rw [show (2 ^ 108 : Nat) = 2 ^ 52 * 2 ^ 56 by rfl, ht]
  have h0 : (2 ^ 52 * 2 ^ 56 : Nat) ≠ 0 :=
    Nat.mul_ne_zero (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _))
      (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos _))
  have hb : ¬ ((((2047 : Nat) : Int)) ≤ 1131 + e) := by omega
  simp only [h0, ↓reduceIte, reduceCtorEq, false_and, or_self, decide_false,
    Bool.false_eq_true, hb, Nat.mod_self]

/-- `1 / c` for a binary64 power of two `c` whose reciprocal is normal: the reciprocal, exactly
(`one` is `1.0`). -/
theorem div_pow2_recip (sc : Bool) (b : Nat) (h1 : 1 ≤ b) (h2 : b ≤ 2045) (one c : Bits .b64)
    (hu : unpack .b64 one = (.nonzero, false, 2 ^ 52, -52))
    (hc : unpack .b64 c = (.nonzero, sc, 2 ^ 52, (b : Int) - 1075)) :
    IEEE.div .b64 .rne one c = pack .b64 sc (2046 - b) 0 := by
  have hl : (2 ^ 52 : Nat).log2 = 52 := Nat.log2_two_pow
  unfold IEEE.div
  rw [hu, hc]
  simp only [processNaNs, reduceCtorEq, ↓reduceIte, and_false, or_self, hl]
  have hq : 2 ^ 52 * 2 ^ (52 + 4 + 52) / 2 ^ 52 = 2 ^ 108 :=
    Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)
  have hr : 2 ^ 52 * 2 ^ (52 + 4 + 52) % 2 ^ 52 = 0 := Nat.mul_mod_right _ _
  rw [hq, hr]
  simp only [ne_eq, not_true_eq_false, decide_false, Bool.false_bne]
  rw [show (-52 - ((b : Int) - 1075) - ((52 + 4 + 52 : Nat) : Int)) = 915 - b by omega,
    round_pow2 sc (915 - b) (by omega) (by omega)]
  congr 1; omega

/-- `x / c = x * r = r * x` for powers of two `c` and `r` of the same sign whose exponents add up
to `0` (`2^52 * 2^ec * 2^52 * 2^er = 1`). -/
theorem div_eq_mul_pow2 (x c r : Bits .b64) (sc : Bool) (ec er : Int) (he : ec + er = -104)
    (hc : unpack .b64 c = (.nonzero, sc, 2 ^ 52, ec))
    (hr : unpack .b64 r = (.nonzero, sc, 2 ^ 52, er)) :
    IEEE.div .b64 .rne x c = IEEE.mul .b64 .rne x r ∧
      IEEE.div .b64 .rne x c = IEEE.mul .b64 .rne r x := by
  have hl : (2 ^ 52 : Nat).log2 = 52 := Nat.log2_two_pow
  unfold IEEE.div IEEE.mul
  rcases hx : unpack .b64 x with ⟨t, s, m, e⟩
  simp only [hc, hr]
  cases t
  case denormal | nonzero =>
    simp only [processNaNs, reduceCtorEq, ↓reduceIte, and_false, or_self, hl]
    have hm : m * 2 ^ (52 + 4 + 52) = m * 2 ^ 52 * 2 ^ 4 * 2 ^ 52 := by
      rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add]
    have hq : m * 2 ^ (52 + 4 + 52) / 2 ^ 52 = m * 2 ^ 52 * 2 ^ 4 := by
      rw [hm]; exact Nat.mul_div_cancel _ (Nat.two_pow_pos _)
    have hr : m * 2 ^ (52 + 4 + 52) % 2 ^ 52 = 0 := by rw [hm]; exact Nat.mul_mod_left _ _
    have hE : e - ec - ((52 + 4 + 52 : Nat) : Int) = (e + er) - ((4 : Nat) : Int) := by omega
    rw [hq, hr, hE]
    simp only [ne_eq, not_true_eq_false, decide_false]
    rw [round_scale]
    refine ⟨rfl, ?_⟩
    rw [Nat.mul_comm (2 ^ 52) m, Int.add_comm er e]
    cases s <;> cases sc <;> rfl
  all_goals cases s <;> cases sc <;> simp_all [processNaNs, processNaN]

/-- `reciprocalExact64(c)`: `c` is a power of two whose reciprocal is a normal number. -/
theorem recip_pack (c : BitVec 64) (h : GoFV.Proof.Rules.reciprocalExactB 11 52 c.toNat = true) :
    ∃ sc b, 1 ≤ b ∧ b ≤ 2045 ∧ c = pack .b64 sc b 0 := by
  unfold GoFV.Proof.Rules.reciprocalExactB at h
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Nat.reducePow, Nat.reduceSub] at h
  obtain ⟨⟨⟨hf, h0⟩, h1⟩, h2⟩ := h
  have hlt : c.toNat < 18446744073709551616 := c.isLt
  refine ⟨decide (9223372036854775808 ≤ c.toNat), c.toNat / 4503599627370496 % 2048,
    by omega, by omega, ?_⟩
  apply BitVec.eq_of_toNat_eq
  rw [pack_b64_toNat _ _ (by omega)]
  by_cases hs : 9223372036854775808 ≤ c.toNat <;>
    simp only [hs, decide_true, decide_false, ↓reduceIte, Bool.false_eq_true] <;> omega

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


/-- `Div64F v c` is `Mul64F v r` on every value when `x / c = x * r = r * x` for every `x`. -/
theorem fops_div_eq_mul64 (v : Val) (c r : BitVec 64)
    (h : ∀ x, IEEE.div .b64 .rne x c = IEEE.mul .b64 .rne x r ∧
      IEEE.div .b64 .rne x c = IEEE.mul .b64 .rne r x) :
    FOps.div .w64 [v, .int .w64 c] = FOps.mul .w64 [v, .int .w64 r] := by
  have hd : FOps.div .w64 [v, .int .w64 c] =
      int2 .w64 (fun x y => .int .w64 (IEEE.div .b64 .rne x y)) [v, .int .w64 c] := rfl
  have hm : FOps.mul .w64 [v, .int .w64 r] =
      int2 .w64 (fun x y => .int .w64 (FOps.ordered (IEEE.mul .b64 .rne) x y)) [v, .int .w64 r] := rfl
  rw [hd, hm]
  simp only [int2]
  cases hv : v.asInt .w64 with
  | none => rfl
  | some x =>
    simp only [Val.asInt, ↓reduceDIte, FOps.ordered]
    split
    · rw [(h x).2]
    · rw [(h x).1]
end GoFV.Proof.Rules.FloatArith

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem

section

variable [GoFV.SSA.Sem.Addrs]

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

/-- `generic.rules:1331`: `(Div64F x (Const64F <t> [c])) && reciprocalExact64(c) =>
(Mul64F x (Const64F <t> [1/c]))` -/
theorem r_generic_1331_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1331 := by
  rule_unfold
  obtain ⟨-, h1⟩ := hat
  obtain ⟨sc, b, hb1, hb2, hC⟩ := FloatArith.recip_pack _ hcond
  have hu : IEEE.unpack .b64 0x3ff0000000000000#64 = (.nonzero, false, 2 ^ 52, -52) := by decide
  have hc := FloatArith.unpack_pack_pow2 sc b hb1 (by omega)
  rw [← hC] at hc
  have hR := FloatArith.div_pow2_recip sc b hb1 hb2 _ _ hu hc
  have hr := FloatArith.unpack_pack_pow2 sc (2046 - b) (by omega) (by omega)
  rw [← hR] at hr
  have hk : ∀ C : BitVec 64, Val.retype (e.ty [1]) (FOps.const64 (Int64.ofInt C.toInt)) = .int .w64 C := by
    intro C; rw [h1, FOps.const64]; simp [Val.retype]
  have hk1 : Val.retype (e.ty [1]) (FOps.const64 (e.auxInt [1])) =
      .int .w64 (BitVec.ofInt 64 (e.auxInt [1]).toInt) := by
    rw [h1, FOps.const64]; simp [Val.retype]
  have hdm := FloatArith.fops_div_eq_mul64 (e.leaf [0]) _ _ (fun x =>
    FloatArith.div_eq_mul_pow2 x _ _ sc _ _ (by omega) hc hr)
  rw [hk1, hdm] at hty
  rw [hk, hk1, hdm]
  exact refines_retype_of_hasTy hty

end

open scoped GoFV.SSA.Sem.Fixed

/-- `generic.rules:1328` at `x = 1.0` (`rule-sat`'s random auxints miss the literal `2.0`). -/
theorem inst_r_generic_1328 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_1328
    (PEnv.ofLists [([0], .i64 0x3FF0000000000000)] [] (.int .w64) [([1], 0x4000000000000000)])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_1328]
  rule_eval
  intro h
  simp only [FOps.mul, FOps.bin, int2, Val.asInt, ↓reduceDIte, reduceCtorEq] at h

/-- `generic.rules:1331` at `x = 1.0`, `c = 2.0`. -/
theorem inst_r_generic_1331 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_1331
    (PEnv.ofLists [([0], .i64 0x3FF0000000000000)] [] (.int .w64) [([1], 0x4000000000000000)])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_1331]
  rule_eval
  refine ⟨congrArg DV.bool (by decide), fun h => ?_⟩
  simp only [FOps.div, FOps.bin, int2, Val.asInt, ↓reduceDIte, reduceCtorEq] at h
end GoFV.Proof.Rules
