import GoFV.Proof.Rules.Tactic
import GoFV.Rules.Generated.Generic.Values03

variable [GoFV.SSA.Sem.Addrs]

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

`(IsInBounds (ZeroExt<w>to64 (Rsh<w>Ux64 _ (Const64 [c]))) (Const64 [d])) && 0 < c && c < w &&
1<<uint(w-c)-1 < d => (ConstBool [true])` (`:260`, `:264`, `:267`; issue #69): the shifted value
is below `2^(w-c)` (`ult_shr`), and the condition, whose Go arithmetic wraps `1<<63` to
`-2^63` and back (`pow_cond`), says `2^(w-c) - 1 < d`.
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

private theorem emod_eq_mod (x y : Int) : x.emod y = x % y := rfl

private theorem wrap_small {W c : Int} (h1 : 0 < c) (h2 : c < W) (hW : W ≤ 64) :
    wrapInt 64 false (wrapInt 64 true (W - c)) = W - c := by
  simp only [wrapInt_true, wrapInt_false, Int.reducePow, Nat.reducePow, emod_eq_mod]
  rw [Int.bmod_eq_emod]
  split <;> omega

/-- Go's `1<<s - 1` at `int64` for `1 ≤ s ≤ 63`: `2^s - 1` (`1<<63` wraps, and back). -/
private theorem pow_cond (s : Nat) (hs1 : 1 ≤ s) (hs : s ≤ 63) :
    wrapInt 64 true (wrapInt 64 true (goShl 1 s 64) - 1) = ((2 ^ s : Nat) : Int) - 1 := by
  have hp : goShl 1 s 64 = ((2 ^ s : Nat) : Int) := by
    unfold goShl; rw [ite_eq_right (by omega)]; simp
  rw [hp]
  have hle : 2 ^ s ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) hs
  have hpos : 2 ^ 1 ≤ 2 ^ s := Nat.pow_le_pow_right (by decide) hs1
  generalize 2 ^ s = p at hle hpos
  simp only [Nat.reducePow] at hle hpos
  rw [wrapInt_true, wrapInt_true, Int.bmod_eq_emod, Int.bmod_eq_emod]
  have h : ((2 ^ 64 : Nat) : Int) = 18446744073709551616 := by rfl
  rw [h]
  split <;> split <;> omega

/-- A `W`-bit value shifted right by `k`, zero-extended, is below any `d > 2^(W-k) - 1`. -/
private theorem ult_shr {W : Nat} (xs : BitVec W) (s k : Nat) (d : Int) (hk : s + k = W)
    (hd : ((2 ^ s : Nat) : Int) - 1 < d) (hd2 : d < 2 ^ 63) (hW : W ≤ 64) :
    (BitVec.setWidth 64 (xs >>> k)).ult (BitVec.ofInt 64 d) = true := by
  have hx : xs.toNat < 2 ^ s * 2 ^ k := by rw [← Nat.pow_add, hk]; exact xs.isLt
  have hq : xs.toNat / 2 ^ k < 2 ^ s := Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
  have hs : 2 ^ s ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) (by omega)
  simp only [BitVec.ult, decide_eq_true_eq, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow, BitVec.toNat_ofInt]
  have hW' : 2 ^ W ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hW
  rw [Nat.mod_eq_of_lt (by omega)]
  simp only [Nat.reducePow] at hs ⊢
  omega

set_option hygiene false in
/-- `rule_auto`'s case split, the condition evaluated (`wrap_small`, `pow_cond`), then
`ult_shr`, for `w`-bit values (unhygienic: it names the rule's environment `e`). -/
local macro "bounds_shift" w:num : tactic => `(tactic| (
  rule_unfold
  (try rule_ands)
  (try rule_clear_oracle)
  (try rule_norm)
  (try rule_ands)
  all_goals (repeat rule_split1)
  all_goals (try rule_widths)
  all_goals (
    have hc1 : 0 < (e.auxInt [1, 0, 0]).toInt := by assumption
    have hc2 : (e.auxInt [1, 0, 0]).toInt < $w := by assumption
    simp only [wrap_small hc1 hc2 (by decide),
      show ¬ (($w : Int) - (e.auxInt [1, 0, 0]).toInt < 0) by omega, ite_false,
      pow_cond _ (show 1 ≤ (($w : Int) - (e.auxInt [1, 0, 0]).toInt).toNat by omega)
        (by omega)] at *
    have hd := Int64.toInt_lt (e.auxInt [1])
    simp only [DV.bool.injEq, decide_eq_true_eq] at *
    rw [BitVec.toNat_ofInt]
    exact ult_shr _ ((($w : Int) - (e.auxInt [1, 0, 0]).toInt).toNat) _ _ (by omega)
      (by assumption) hd (by decide))))

/-- `generic.rules:260`: `(IsInBounds (ZeroExt8to64 (Rsh8Ux64 _ (Const64 [c]))) (Const64 [d])) && 0 < c && c < 8 && 1<<uint( 8-c)-1 < d => (ConstBool [true])` -/
theorem r_generic_260_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_260 := by
  bounds_shift 8

/-- `generic.rules:264`: `(IsInBounds (ZeroExt16to64 (Rsh16Ux64 _ (Const64 [c]))) (Const64 [d])) && 0 < c && c < 16 && 1<<uint(16-c)-1 < d => (ConstBool [true])` -/
theorem r_generic_264_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_264 := by
  bounds_shift 16

/-- `generic.rules:267`: `(IsInBounds (ZeroExt32to64 (Rsh32Ux64 _ (Const64 [c]))) (Const64 [d])) && 0 < c && c < 32 && 1<<uint(32-c)-1 < d => (ConstBool [true])` -/
theorem r_generic_267_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_267 := by
  bounds_shift 32

end GoFV.Proof.Rules
