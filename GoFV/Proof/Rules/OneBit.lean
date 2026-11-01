import GoFV.Proof.Rules.TacticRange
import GoFV.Proof.Rules.TacticCond
import GoFV.Rules.Generated.Generic.Values01

/-!
# Single-bit equality tests (`generic.rules:369`, `:372`)

`(OrB (Eq64 x (Const64 [c])) (Eq64 x (Const64 [d]))) && c|d == c && oneBit(c^d) =>
(Eq64 (Or64 x (Const64 [c^d])) (Const64 [c]))` and the `AndB`/`Neq` form: `d` is `c` with one
bit `b = c^d` cleared, so `x == c || x == d` iff `x | b == c` (`onebit_bv`). The condition
evaluates to `Int` facts about `bitwise`/`andPred`; `onebit_int` reads them in `BitVec`.
-/

namespace GoFV.Proof.Rules

open GoFV.Rules

/-- A nonzero `b` with `b &&& (b - 1) = 0` is a single bit. -/
theorem bv_twoPow_of_and_pred {w : Nat} (b : BitVec w) (h0 : b ≠ 0) (h : b &&& (b - 1#w) = 0) :
    ∃ k, k < w ∧ b = BitVec.twoPow w k := by
  have hpos : 0 < b.toNat := by
    rcases Nat.eq_zero_or_pos b.toNat with h1 | h1
    · exact absurd (BitVec.eq_of_toNat_eq (by simpa using h1)) h0
    · exact h1
  have hw : 0 < w := by
    rcases Nat.eq_zero_or_pos w with hw | hw
    · subst hw; exact absurd (BitVec.eq_of_toNat_eq (by have := b.isLt; simp at this; omega)) h0
    · exact hw
  have h1 : (1#w).toNat = 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))]
  have hsub : (b - 1#w).toNat = b.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h1]; omega), h1]
  have hn : b.toNat &&& (b.toNat - 1) = 0 := by
    have := congrArg BitVec.toNat h
    rw [BitVec.toNat_and, hsub] at this
    simpa using this
  have hp := pow2_of_and_pred hpos hn
  refine ⟨bitsLen b.toNat - 1, ?_, ?_⟩
  · have := b.isLt
    false_or_by_contra
    rename_i hk
    have : 2 ^ w ≤ 2 ^ (bitsLen b.toNat - 1) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_twoPow, ← hp, Nat.mod_eq_of_lt b.isLt]

/-- `x | (c^d) == c` iff `x == c || x == d`, when `d ⊆ c` and `c^d` is a single bit. -/
theorem onebit_bv {w : Nat} (x C D : BitVec w) (h1 : C ||| D = C)
    (h2 : (C ^^^ D) &&& ((C ^^^ D) - 1#w) = 0) (h3 : C ^^^ D ≠ 0) :
    ((x ||| (C ^^^ D)) == C) = (x == C || x == D) := by
  obtain ⟨k, hk, hb⟩ := bv_twoPow_of_and_pred _ h3 h2
  have hbit : ∀ i, (C ^^^ D).getLsbD i = (decide (k < w) && decide (k = i)) := by
    intro i; rw [hb, BitVec.getLsbD_twoPow]
  have hsub : ∀ i, D.getLsbD i = true → C.getLsbD i = true := by
    intro i hi
    have := congrArg (·.getLsbD i) h1
    simp only [BitVec.getLsbD_or, hi, Bool.or_true] at this
    exact this.symm
  have hCk : C.getLsbD k = true := by
    have := hbit k
    simp only [BitVec.getLsbD_xor, hk, decide_true, Bool.true_and] at this
    cases hD : D.getLsbD k
    · rw [hD, Bool.xor_false] at this; exact this
    · rw [hsub k hD, hD] at this; exact absurd this (by decide)
  have hDk : D.getLsbD k = false := by
    have := hbit k
    simp only [BitVec.getLsbD_xor, hk, decide_true, Bool.true_and, hCk] at this
    cases hD : D.getLsbD k
    · rfl
    · rw [hD] at this; exact absurd this (by decide)
  have hCD : ∀ i, i ≠ k → C.getLsbD i = D.getLsbD i := by
    intro i hi
    have := hbit i
    simp only [BitVec.getLsbD_xor, Ne.symm hi, decide_false, Bool.and_false] at this
    cases hC : C.getLsbD i <;> cases hD : D.getLsbD i <;> rw [hC, hD] at this <;>
      first | rfl | exact absurd this (by decide)
  rw [Bool.eq_iff_iff]
  simp only [beq_iff_eq, Bool.or_eq_true]
  constructor
  · intro h
    cases hx : x.getLsbD k
    · right
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      by_cases hik : i = k
      · subst hik; rw [hx, hDk]
      · have := congrArg (·.getLsbD i) h
        simp only [BitVec.getLsbD_or, BitVec.getLsbD_xor] at this
        rw [← hCD i hik, ← this]
        have := hbit i
        simp only [BitVec.getLsbD_xor, Ne.symm hik, decide_false, Bool.and_false] at this
        rw [this, Bool.or_false]
    · left
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      by_cases hik : i = k
      · subst hik; rw [hx, hCk]
      · have := congrArg (·.getLsbD i) h
        simp only [BitVec.getLsbD_or, BitVec.getLsbD_xor] at this
        rw [← this]
        have := hbit i
        simp only [BitVec.getLsbD_xor, Ne.symm hik, decide_false, Bool.and_false] at this
        rw [this, Bool.or_false]
  · rintro (h | h) <;> subst h <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      rw [BitVec.getLsbD_or, hbit i] <;> by_cases hik : k = i
    · subst hik; simp [hk, hCk]
    · simp [hik]
    · subst hik; simp [hk, hCk]
    · simp only [hik, decide_false, Bool.and_false, Bool.or_false]
      exact (hCD i (Ne.symm hik)).symm

/-- `bitwise` of a signed type in `BitVec`. -/
theorem ofInt_bitwise_s {T : GoTy} {w : Nat} (hT : T.intInfo? = some (w, true)) (f : Nat → Nat → Nat)
    (a b : Int) : BitVec.ofInt w (bitwise T f a b) = BitVec.ofNat w (f (pat64 a) (pat64 b)) := by
  simp only [bitwise, hT, Option.getD_some]
  rw [ofInt_wrapInt_true (Nat.le_refl w), BitVec.ofInt_natCast]

/-- The condition `c|d == c && oneBit(c^d)` of `generic.rules:369`/`:372` (signed `c`, `d` of
type `T`) in `BitVec`: `onebit_bv`. -/
theorem onebit_int {T : GoTy} {w : Nat} (hT : T.intInfo? = some (w, true)) (hw : w ≤ 64)
    (c d : Int) (y : BitVec w)
    (h1 : bitwise T (fun x1 x2 => x1 ||| x2) c d = c)
    (h2 : wrapInt w true (andPred T (bitwise T (fun x1 x2 => x1 ^^^ x2) c d)) = 0)
    (h3 : ¬bitwise T (fun x1 x2 => x1 ^^^ x2) c d = 0) :
    ((y ||| BitVec.ofInt w (bitwise T (fun x1 x2 => x1 ^^^ x2) c d)) == BitVec.ofInt w c) =
      (y == BitVec.ofInt w c || y == BitVec.ofInt w d) := by
  have hx : BitVec.ofInt w (bitwise T (fun x1 x2 => x1 ^^^ x2) c d) =
      BitVec.ofInt w c ^^^ BitVec.ofInt w d := by
    rw [ofInt_bitwise_s hT, BitVec.ofNat_xor, ofNat_pat64 hw, ofNat_pat64 hw]
  rw [hx]
  apply onebit_bv
  · have := congrArg (BitVec.ofInt w) h1
    rwa [ofInt_bitwise_s hT, BitVec.ofNat_or, ofNat_pat64 hw, ofNat_pat64 hw] at this
  · have := congrArg (BitVec.ofInt w) h2
    rw [ofInt_wrapInt_true (Nat.le_refl w), andPred, ofInt_bitwise_s hT, BitVec.ofNat_and,
      ofNat_pat64 hw, ofNat_pat64 hw, ofInt_sub', hx] at this
    simpa using this
  · intro h0
    apply h3
    have := congrArg BitVec.toInt (hx.trans h0)
    simp only [bitwise, hT, Option.getD_some, BitVec.toInt_ofInt, BitVec.toInt_zero] at this ⊢
    unfold wrapInt at this ⊢
    simp only [↓reduceIte, Int.bmod_bmod] at this ⊢
    simpa using this

/-- `onebit_int` for `Neq` (`generic.rules:369`): `x | (c^d) != c` iff `x != c && x != d`. -/
theorem onebit_int_ne {T : GoTy} {w : Nat} (hT : T.intInfo? = some (w, true)) (hw : w ≤ 64)
    (c d : Int) (y : BitVec w)
    (h1 : bitwise T (fun x1 x2 => x1 ||| x2) c d = c)
    (h2 : wrapInt w true (andPred T (bitwise T (fun x1 x2 => x1 ^^^ x2) c d)) = 0)
    (h3 : ¬bitwise T (fun x1 x2 => x1 ^^^ x2) c d = 0) :
    ((y ||| BitVec.ofInt w (bitwise T (fun x1 x2 => x1 ^^^ x2) c d)) != BitVec.ofInt w c) =
      (y != BitVec.ofInt w c && y != BitVec.ofInt w d) := by
  simp only [bne, onebit_int hT hw c d y h1 h2 h3, Bool.not_or]

end GoFV.Proof.Rules

namespace GoFV.Proof.Rules

open GoFV.Proof.Rules.KernelSafe

/-- `rule_range` for `generic.rules:369`/`:372`: `rule_unfold_getd` (the `oneBit` condition)
and `rule_norm` with proof terms (`KernelSafe`), the case splits of `rule_range`, then the
result rewritten by `onebit_int`. -/
macro "rule_onebit" : tactic => `(tactic| (
  rule_unfold_getd
  (try rule_ands)
  (try rule_clear_oracle)
  (try rule_norm)
  (try rule_ands)
  all_goals (repeat' (first | bool_split1 | rule_split1))
  all_goals (try rule_widths)
  all_goals (
    repeat rule_gen1
    try simp only [GoFV.Proof.Rules.DV.int.injEq, GoFV.Proof.Rules.DV.bool.injEq] at *
    try rule_ands
    try rule_subst
    try rule_norm
    first
    | done
    | with_reducible rfl
    | (simp (disch := first | rfl | decide | assumption) only [GoFV.Proof.Rules.ofInt_wrapInt_true,
         GoFV.Proof.Rules.ofInt_int64_ofInt, GoFV.Proof.Rules.onebit_int,
         GoFV.Proof.Rules.onebit_int_ne]
       simp_all))))


/-- `generic.rules:369`: `(AndB (Neq64 x cv:(Const64 [c])) (Neq64 x (Const64 [d]))) && c|d == c && oneBit(c^d) => (Neq64 (Or64 <x.Type> x (Const64 <x.Type> [c^d])) cv)` -/
theorem r_generic_369_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_369 := by
  rule_onebit

/-- `generic.rules:369`: `(AndB (Neq32 x cv:(Const32 [c])) (Neq32 x (Const32 [d]))) && c|d == c && oneBit(c^d) => (Neq32 (Or32 <x.Type> x (Const32 <x.Type> [c^d])) cv)` -/
theorem r_generic_369_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_369_2 := by
  rule_onebit

/-- `generic.rules:369`: `(AndB (Neq16 x cv:(Const16 [c])) (Neq16 x (Const16 [d]))) && c|d == c && oneBit(c^d) => (Neq16 (Or16 <x.Type> x (Const16 <x.Type> [c^d])) cv)` -/
theorem r_generic_369_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_369_3 := by
  rule_onebit

/-- `generic.rules:369`: `(AndB (Neq8 x cv:(Const8 [c])) (Neq8 x (Const8 [d]))) && c|d == c && oneBit(c^d) => (Neq8 (Or8 <x.Type> x (Const8 <x.Type> [c^d])) cv)` -/
theorem r_generic_369_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_369_4 := by
  rule_onebit

end GoFV.Proof.Rules
