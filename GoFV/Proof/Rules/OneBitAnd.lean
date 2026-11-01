import GoFV.Proof.Rules.OneBit
import GoFV.Rules.Generated.Generic.Values03
import GoFV.Rules.Generated.Generic.Values07
import GoFV.Rules.Generated.Generic.Values08
import GoFV.Rules.Generated.Generic.Values09

/-!
# Single-bit masks and covering masks (`generic.rules:1183`, `:1185`, `:742–745`)

`(Eq64 (And64 x (Const64 [y])) (Const64 [y])) && oneBit(y) => (Neq64 (And64 x (Const64 [y]))
(Const64 [0]))` and the `Neq` form: `x & y` is `0` or `y` for a single bit `y`
(`onebit_and_bv`). `(Or64 (And64 x (Const64 [c2])) (Const64 [c1])) && ^(c1 | c2) == 0 =>
(Or64 (Const64 [c1]) x)`: every bit is in `c1` or `c2` (`or_and_of_not_or`). All widths
(issue #69).
-/

namespace GoFV.Proof.Rules

open GoFV.Rules

/-- `x & C == C` iff `x & C != 0` for a single bit `C`. -/
theorem onebit_and_bv {w : Nat} (x C : BitVec w) (h2 : C &&& (C - 1#w) = 0) (h3 : C ≠ 0) :
    (x &&& C == C) = (x &&& C != 0#w) := by
  obtain ⟨k, hk, rfl⟩ := bv_twoPow_of_and_pred _ h3 h2
  have h0 : BitVec.twoPow w k ≠ 0#w := h3
  rw [BitVec.and_twoPow]
  split
  · simp only [beq_self_eq_true]; exact (bne_iff_ne.mpr h0).symm
  · simp only [bne_self_eq_false]; exact beq_eq_false_iff_ne.mpr (Ne.symm h0)

/-- A nonzero integer of magnitude below `2^w` is nonzero in `BitVec w`. -/
theorem ofInt_ne_zero_of_lt {w : Nat} {c : Int} (hc : ¬c = 0) (hlo : -(2 ^ w : Int) < c)
    (hhi : c < 2 ^ w) : BitVec.ofInt w c ≠ 0#w := by
  intro h
  have := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofInt, BitVec.toNat_zero] at this
  push_cast at this
  have hm : (0 : Int) < 2 ^ w := Int.pow_pos (by decide)
  have h1 : c % 2 ^ w = 0 := by have := Int.emod_nonneg c (Int.ne_of_gt hm); omega
  by_cases hnn : 0 ≤ c
  · rw [Int.emod_eq_of_lt hnn hhi] at h1; exact hc h1
  · have h2 : (c + 2 ^ w) % 2 ^ w = c % 2 ^ w := Int.add_emod_right _ _
    rw [h1, Int.emod_eq_of_lt (by omega) (by omega)] at h2
    omega

/-- The condition `oneBit(y)` of `generic.rules:1183` (signed `y` of type `T`) in `BitVec`:
`onebit_and_bv`. -/
theorem onebit_and_int {T : GoTy} {w : Nat} {c : Int} {y : BitVec w}
    (h2 : wrapInt w true (andPred T c) = 0) (hT : T.intInfo? = some (w, true)) (hw : w ≤ 64)
    (h3 : BitVec.ofInt w c ≠ 0) :
    (y &&& BitVec.ofInt w c == BitVec.ofInt w c) = (y &&& BitVec.ofInt w c != 0#w) := by
  apply onebit_and_bv _ _ _ h3
  have := congrArg (BitVec.ofInt w) h2
  rw [ofInt_wrapInt_true (Nat.le_refl w), andPred, ofInt_bitwise_s hT, BitVec.ofNat_and,
    ofNat_pat64 hw, ofNat_pat64 hw, ofInt_sub'] at this
  simpa using this

/-- `onebit_and_int` for `Neq` (`generic.rules:1185`). -/
theorem onebit_and_int_ne {T : GoTy} {w : Nat} {c : Int} {y : BitVec w}
    (h2 : wrapInt w true (andPred T c) = 0) (hT : T.intInfo? = some (w, true)) (hw : w ≤ 64)
    (h3 : BitVec.ofInt w c ≠ 0) :
    (y &&& BitVec.ofInt w c != BitVec.ofInt w c) = (y &&& BitVec.ofInt w c == 0#w) := by
  simp only [bne, onebit_and_int h2 hT hw h3, Bool.not_not]

/-- `(x & A) | B = B | x` when every bit is in `A` or `B`. -/
theorem or_and_of_not_or {w : Nat} (x A B : BitVec w) (h : ~~~(B ||| A) = 0#w) :
    (x &&& A ||| B) = (B ||| x) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have := congrArg (·.getLsbD i) h
  simp only [BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_zero, hi, decide_true,
    Bool.true_and] at this
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_and]
  cases hA : A.getLsbD i <;> cases hB : B.getLsbD i <;> cases x.getLsbD i <;> simp_all

/-- The condition `^(c1 | c2) == 0` of `generic.rules:742–745` (signed `c1`, `c2`) in `BitVec`. -/
theorem or_and_int {w : Nat} (hw : w ≤ 64) (c1 c2 : Int) (x : BitVec w)
    (h : wrapInt w true (-wrapInt w true ((pat64 c1 ||| pat64 c2 : Nat) : Int) - 1) = 0) :
    (x &&& BitVec.ofInt w c2 ||| BitVec.ofInt w c1) = (BitVec.ofInt w c1 ||| x) := by
  apply or_and_of_not_or
  have := congrArg (BitVec.ofInt w) h
  rw [ofInt_wrapInt_true (Nat.le_refl w), ofInt_sub', BitVec.ofInt_neg,
    ofInt_wrapInt_true (Nat.le_refl w), BitVec.ofInt_natCast, BitVec.ofNat_or, ofNat_pat64 hw,
    ofNat_pat64 hw] at this
  rw [BitVec.not_eq_neg_add]
  simpa using this

/-- `BitVec.ofInt w` of a wrapped auxint as `BitVec.ofInt w` of the auxint. -/
macro "onebit_simp" : tactic => `(tactic| (try simp (disch := first | rfl | decide) only
  [GoFV.Proof.Rules.ofInt_wrapInt_true, GoFV.Proof.Rules.ofInt_int64_ofInt, BitVec.ofInt_ofNat]))

/-- The case splits of `rule_onebit` (`OneBit.lean`), then the remaining goals closed by
`tac`. -/
macro "rule_onebit_with " tac:tacticSeq : tactic => `(tactic| (
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
    try rule_norm)
  all_goals first
    | done
    | ($tac)))

example : (0b0110#4 &&& 0b0100#4 == 0b0100#4) = (0b0110#4 &&& 0b0100#4 != 0#4) :=
  onebit_and_bv _ _ (by decide) (by decide)

example : (0b0110#4 &&& 0b0011#4 ||| 0b1100#4) = (0b1100#4 ||| 0b0110#4) :=
  or_and_of_not_or _ _ _ (by decide)

example : BitVec.ofInt 8 (-128) ≠ 0#8 := ofInt_ne_zero_of_lt (by decide) (by decide) (by decide)

/-- `generic.rules:1183`: `(Eq16 (And16 <t> x (Const16 <t> [y])) (Const16 <t> [y])) && oneBit(y) => (Neq16 (And16 <t> x (Const16 <t> [y])) (Const16 <t> [0]))` -/
theorem r_generic_1183_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1183 := by
  rule_onebit_with (onebit_simp; exact onebit_and_int (T := .int16) ‹_› rfl (by decide) (ofInt_ne_zero_of_lt ‹_› (by omega) (by omega)))

/-- `generic.rules:1183`: `(Eq32 (And32 <t> x (Const32 <t> [y])) (Const32 <t> [y])) && oneBit(y) => (Neq32 (And32 <t> x (Const32 <t> [y])) (Const32 <t> [0]))` -/
theorem r_generic_1183_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1183_2 := by
  rule_onebit_with (onebit_simp; exact onebit_and_int (T := .int32) ‹_› rfl (by decide) (ofInt_ne_zero_of_lt ‹_› (by omega) (by omega)))

/-- `generic.rules:1183`: `(Eq64 (And64 <t> x (Const64 <t> [y])) (Const64 <t> [y])) && oneBit(y) => (Neq64 (And64 <t> x (Const64 <t> [y])) (Const64 <t> [0]))` -/
theorem r_generic_1183_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1183_3 := by
  rule_onebit_with (onebit_simp; exact onebit_and_int (T := .int64) ‹_› rfl (by decide) (ofInt_ne_zero_of_lt ‹_› (by omega) (by omega)))

/-- `generic.rules:1183`: `(Eq8 (And8 <t> x (Const8 <t> [y])) (Const8 <t> [y])) && oneBit(y) => (Neq8 (And8 <t> x (Const8 <t> [y])) (Const8 <t> [0]))` -/
theorem r_generic_1183_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1183_4 := by
  rule_onebit_with (onebit_simp; exact onebit_and_int (T := .int8) ‹_› rfl (by decide) (ofInt_ne_zero_of_lt ‹_› (by omega) (by omega)))

/-- `generic.rules:1185`: `(Neq16 (And16 <t> x (Const16 <t> [y])) (Const16 <t> [y])) && oneBit(y) => (Eq16 (And16 <t> x (Const16 <t> [y])) (Const16 <t> [0]))` -/
theorem r_generic_1185_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1185 := by
  rule_onebit_with (onebit_simp; exact onebit_and_int_ne (T := .int16) ‹_› rfl (by decide) (ofInt_ne_zero_of_lt ‹_› (by omega) (by omega)))

/-- `generic.rules:1185`: `(Neq32 (And32 <t> x (Const32 <t> [y])) (Const32 <t> [y])) && oneBit(y) => (Eq32 (And32 <t> x (Const32 <t> [y])) (Const32 <t> [0]))` -/
theorem r_generic_1185_2_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1185_2 := by
  rule_onebit_with (onebit_simp; exact onebit_and_int_ne (T := .int32) ‹_› rfl (by decide) (ofInt_ne_zero_of_lt ‹_› (by omega) (by omega)))

/-- `generic.rules:1185`: `(Neq64 (And64 <t> x (Const64 <t> [y])) (Const64 <t> [y])) && oneBit(y) => (Eq64 (And64 <t> x (Const64 <t> [y])) (Const64 <t> [0]))` -/
theorem r_generic_1185_3_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1185_3 := by
  rule_onebit_with (onebit_simp; exact onebit_and_int_ne (T := .int64) ‹_› rfl (by decide) (ofInt_ne_zero_of_lt ‹_› (by omega) (by omega)))

/-- `generic.rules:1185`: `(Neq8 (And8 <t> x (Const8 <t> [y])) (Const8 <t> [y])) && oneBit(y) => (Eq8 (And8 <t> x (Const8 <t> [y])) (Const8 <t> [0]))` -/
theorem r_generic_1185_4_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1185_4 := by
  rule_onebit_with (onebit_simp; exact onebit_and_int_ne (T := .int8) ‹_› rfl (by decide) (ofInt_ne_zero_of_lt ‹_› (by omega) (by omega)))

/-- `generic.rules:742`: `(Or8 (And8 x (Const8 [c2])) (Const8 <t> [c1])) && ^(c1 | c2) == 0 => (Or8 (Const8 <t> [c1]) x)` -/
theorem r_generic_742_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_742 := by
  rule_onebit_with (onebit_simp; exact or_and_int (by decide) _ _ _ ‹_›)

/-- `generic.rules:743`: `(Or16 (And16 x (Const16 [c2])) (Const16 <t> [c1])) && ^(c1 | c2) == 0 => (Or16 (Const16 <t> [c1]) x)` -/
theorem r_generic_743_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_743 := by
  rule_onebit_with (onebit_simp; exact or_and_int (by decide) _ _ _ ‹_›)

/-- `generic.rules:744`: `(Or32 (And32 x (Const32 [c2])) (Const32 <t> [c1])) && ^(c1 | c2) == 0 => (Or32 (Const32 <t> [c1]) x)` -/
theorem r_generic_744_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_744 := by
  rule_onebit_with (onebit_simp; exact or_and_int (by decide) _ _ _ ‹_›)

/-- `generic.rules:745`: `(Or64 (And64 x (Const64 [c2])) (Const64 <t> [c1])) && ^(c1 | c2) == 0 => (Or64 (Const64 <t> [c1]) x)` -/
theorem r_generic_745_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_745 := by
  rule_onebit_with (onebit_simp; exact or_and_int (by decide) _ _ _ ‹_›)

end GoFV.Proof.Rules
