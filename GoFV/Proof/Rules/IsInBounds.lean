import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values03

/-!
# Rule lemmas: `IsInBounds` rules

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the P1/P2 rules whose top op is in the
`IsInBounds` family (`docs/proofs/rules.md`).

Both arguments are 64-bit integers (`argShapeOk`, `int` on the 64-bit target). `IsInBounds i n`
is `poison` for a negative `n` and `i <ᵤ n` otherwise, so a constant fold
`(IsInBounds (Const64 [c]) (Const64 [d])) => (ConstBool [0 <= c && c < d])` is
`ult_ofInt64` (`d ≥ 0`: `c <ᵤ d` iff `0 ≤ c < d`), and `(IsInBounds x x)` is `false` or
`poison` (`inBounds_self`). The 32-bit forms (`:241`, `:244–246`, `:248`, `:249`, `:251`,
`:254`) and `:257` (`Mod32u`, a 32-bit value at a 64-bit argument: always `poison`) have no
instance with 64-bit arguments; they fire only on 32-bit targets and are not proved.
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

theorem ofInt64_toNat {c : Int} (h1 : -2 ^ 63 ≤ c) (h2 : c < 2 ^ 63) :
    ((BitVec.ofInt 64 c).toNat : Int) = if 0 ≤ c then c else c + 2 ^ 64 := by
  rw [BitVec.toNat_ofInt]
  split <;> omega

/-- Unsigned `<` of two 64-bit constants, the second nonnegative: `0 ≤ c < d`. -/
theorem ult_ofInt64 {c d : Int} (hc1 : -2 ^ 63 ≤ c) (hc2 : c < 2 ^ 63) (hd1 : -2 ^ 63 ≤ d)
    (hd2 : d < 2 ^ 63) (hm : (BitVec.ofInt 64 d).msb = false) :
    (BitVec.ofInt 64 c).ult (BitVec.ofInt 64 d) = decide (0 ≤ c ∧ c < d) := by
  have e1 := ofInt64_toNat hc1 hc2
  have e2 := ofInt64_toNat hd1 hd2
  rw [BitVec.msb_eq_decide] at hm
  simp only [BitVec.ult, decide_eq_false_iff_not, Nat.not_le] at hm ⊢
  simp only [decide_eq_decide]
  split at e1 <;> split at e2 <;> omega

/-- Unsigned `≤` of two 64-bit constants, the second nonnegative: `0 ≤ c ≤ d`. -/
theorem ule_ofInt64 {c d : Int} (hc1 : -2 ^ 63 ≤ c) (hc2 : c < 2 ^ 63) (hd1 : -2 ^ 63 ≤ d)
    (hd2 : d < 2 ^ 63) (hm : (BitVec.ofInt 64 d).msb = false) :
    (BitVec.ofInt 64 c).ule (BitVec.ofInt 64 d) = decide (0 ≤ c ∧ c ≤ d) := by
  have e1 := ofInt64_toNat hc1 hc2
  have e2 := ofInt64_toNat hd1 hd2
  rw [BitVec.msb_eq_decide] at hm
  simp only [BitVec.ule, decide_eq_false_iff_not, Nat.not_le] at hm ⊢
  simp only [decide_eq_decide]
  split at e1 <;> split at e2 <;> omega

/-- A bounds check of a value against itself: `poison`, or `i ≤ᵤ i` (`slice`) / `i <ᵤ i`. -/
theorem inBounds_self (s : Bool) (v : Val) :
    Cmp.inBounds s [v, v] = .poison ∨ Cmp.inBounds s [v, v] = .bool s := by
  cases v <;> simp only [Cmp.inBounds, true_or]
  rename_i w x
  simp only [Val.asInt_int]
  split
  · exact .inl rfl
  · right; cases s <;> simp [BitVec.ult, BitVec.ule]

/-- `rule_auto` with the constant folds of unsigned comparisons as a last closer
(`ult_ofInt64`, `ule_ofInt64`; the auxints' ranges by `Int64.le_toInt`/`Int64.toInt_lt`). -/
macro "bounds_auto" : tactic => `(tactic| (
  rule_unfold
  (try rule_ands)
  (try rule_clear_oracle)
  (try rule_norm)
  (try rule_ands)
  all_goals (repeat rule_split1)
  all_goals (try rule_widths)
  all_goals first
    | rule_close
    | (first | rw [ult_ofInt64] | rw [ule_ofInt64]) <;>
        first | assumption | exact Int64.le_toInt _ | exact Int64.toInt_lt _ | omega | simp_all))

/-- `generic.rules:240`: `(IsInBounds (ZeroExt8to64 _) (Const64 [c])) && (1 << 8) <= c => (ConstBool [true])` -/
theorem r_generic_240_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_240 := by rule_auto

/-- `generic.rules:242`: `(IsInBounds (ZeroExt16to64 _) (Const64 [c])) && (1 << 16) <= c => (ConstBool [true])` -/
theorem r_generic_242_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_242 := by rule_auto

/-- `generic.rules:243`: `(IsInBounds x x) => (ConstBool [false])` -/
theorem r_generic_243_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_243 := by
  rule_unfold
  rw [hc] at hty ⊢
  rcases inBounds_self false (e.leaf [0]) with h | h <;> rw [h] at hty ⊢
  · exact Refines.poison _
  · exact refines_retype_of_hasTy hty

/-- `generic.rules:247`: `(IsInBounds (ZeroExt8to64 (And8 (Const8 [c]) _)) (Const64 [d])) && 0 <= c && int64(c) < d => (ConstBool [true])` -/
theorem r_generic_247_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_247 := by rule_auto

/-- `generic.rules:250`: `(IsInBounds (ZeroExt16to64 (And16 (Const16 [c]) _)) (Const64 [d])) && 0 <= c && int64(c) < d => (ConstBool [true])` -/
theorem r_generic_250_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_250 := by rule_auto

/-- `generic.rules:252`: `(IsInBounds (ZeroExt32to64 (And32 (Const32 [c]) _)) (Const64 [d])) && 0 <= c && int64(c) < d => (ConstBool [true])` -/
theorem r_generic_252_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_252 := by rule_auto

/-- `generic.rules:253`: `(IsInBounds (And64 (Const64 [c]) _) (Const64 [d])) && 0 <= c && c < d => (ConstBool [true])` -/
theorem r_generic_253_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_253 := by rule_auto

/-- `generic.rules:255`: `(IsInBounds (Const64 [c]) (Const64 [d])) => (ConstBool [0 <= c && c < d])` -/
theorem r_generic_255_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_255 := by
  bounds_auto

end GoFV.Proof.Rules
