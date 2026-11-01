import GoFV.Rules.Helpers.Magic
import GoFV.Proof.Rules.Tactic

/-!
# The `divisible` helpers: inverses and trailing zeros (#69)

Specifications of `Magic.inv64` (Newton–Raphson inverse modulo `2^64`), `trailingZeros`,
`Magic.udivisible`, `Magic.sdivisible` and `Magic.modInverse`, used by the rule lemmas of
`DivisibleU.lean`, `DivisibleS.lean` and `DivisibleGen.lean`, and the tactics that eliminate
the helper calls after `rule_unfold`.
-/

namespace GoFV.Proof.Rules.Divisible

open GoFV.Rules

/-! ## `inv64` -/

/-- One Newton step of `inv64`: `m * (2 - m * d0)` in `uint64`. -/
def stepF (d0 m : Nat) : Nat := (m * ((2 + 2 ^ 64 * 2 ^ 64 - (m * d0) % 2 ^ 64) % 2 ^ 64)) % 2 ^ 64

theorem inv64_eq (d0 : Nat) :
    Magic.inv64 d0 = stepF d0 (stepF d0 (stepF d0 (stepF d0 (stepF d0 (d0 % 2 ^ 64))))) := by
  simp only [Magic.inv64, Id.run, Std.Legacy.Range.forIn_eq_forIn_range',
    Std.Legacy.Range.size, List.range', List.forIn_cons, List.forIn_nil, pure_bind]
  rfl

theorem stepF_cong (d0 m : Nat) :
    ∃ q : Int, ((stepF d0 m : Nat) : Int) = m * (2 - ((m * d0 : Nat) : Int)) + 2 ^ 64 * q := by
  unfold stepF
  generalize hT : (2 + 2 ^ 64 * 2 ^ 64 - (m * d0) % 2 ^ 64) % 2 ^ 64 = T
  have h1 := Nat.mod_add_div (m * T) (2 ^ 64)
  have h2 := Nat.mod_add_div (2 + 2 ^ 64 * 2 ^ 64 - (m * d0) % 2 ^ 64) (2 ^ 64)
  have h3 := Nat.mod_add_div (m * d0) (2 ^ 64)
  have h4 := Nat.mod_lt (m * d0) (show 2 ^ 64 > 0 by decide)
  rw [hT] at h2
  refine ⟨(m : Int) * 2 ^ 64 + m * ((m * d0 / 2 ^ 64 : Nat) : Int) -
    m * (((2 + 2 ^ 64 * 2 ^ 64 - (m * d0) % 2 ^ 64) / 2 ^ 64 : Nat) : Int) -
    ((m * T / 2 ^ 64 : Nat) : Int), ?_⟩
  have e1 : ((m * T % 2 ^ 64 : Nat) : Int) =
      (m : Int) * T - 2 ^ 64 * ((m * T / 2 ^ 64 : Nat) : Int) := by omega
  have e2 : (T : Int) = 2 + 2 ^ 64 * 2 ^ 64 - (((m * d0) % 2 ^ 64 : Nat) : Int) -
      2 ^ 64 * (((2 + 2 ^ 64 * 2 ^ 64 - (m * d0) % 2 ^ 64) / 2 ^ 64 : Nat) : Int) := by omega
  have e3 : (((m * d0) % 2 ^ 64 : Nat) : Int) =
      ((m * d0 : Nat) : Int) - 2 ^ 64 * ((m * d0 / 2 ^ 64 : Nat) : Int) := by omega
  rw [e1, e2, e3]
  generalize ((m * d0 : Nat) : Int) = A
  generalize (((2 + 2 ^ 64 * 2 ^ 64 - (m * d0) % 2 ^ 64) / 2 ^ 64 : Nat) : Int) = Q2
  generalize ((m * T / 2 ^ 64 : Nat) : Int) = Q1
  generalize ((m * d0 / 2 ^ 64 : Nat) : Int) = Q3
  grind

/-- Newton's step doubles the number of correct low bits (up to 64). -/
theorem newton_step (d0 m j j' : Nat) (h : (2 : Int) ^ j ∣ ((m * d0 : Nat) : Int) - 1)
    (h1 : j' ≤ 2 * j) (h2 : j' ≤ 64) : (2 : Int) ^ j' ∣ ((stepF d0 m * d0 : Nat) : Int) - 1 := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨q, hq⟩ := stepF_cong d0 m
  refine ⟨-(2 : Int) ^ (2 * j - j') * t * t + 2 ^ (64 - j') * q * d0, ?_⟩
  have p1 : (2 : Int) ^ (2 * j) = 2 ^ j' * 2 ^ (2 * j - j') := by
    rw [← Int.pow_add]; congr 1; omega
  have p2 : (2 : Int) ^ 64 = 2 ^ j' * 2 ^ (64 - j') := by rw [← Int.pow_add]; congr 1; omega
  have p3 : (2 : Int) ^ (2 * j) = 2 ^ j * 2 ^ j := by rw [← Int.pow_add]; congr 1; omega
  rw [Int.natCast_mul] at ht hq ⊢
  rw [hq]
  have ha : (m : Int) * d0 = 1 + 2 ^ j * t := by omega
  generalize (2 : Int) ^ j = P at *
  generalize (2 : Int) ^ j' = P' at *
  generalize (2 : Int) ^ (2 * j - j') = P1 at *
  generalize (2 : Int) ^ (64 - j') = P2 at *
  generalize (2 : Int) ^ (2 * j) = P3 at *
  subst p3
  rw [p2]
  grind

/-- `inv64 d0` is the inverse of the odd `d0` modulo `2^64`. -/
theorem inv64_spec {d0 : Nat} (hd0 : d0 % 2 = 1) : Magic.inv64 d0 * d0 % 2 ^ 64 = 1 := by
  have h0 : (2 : Int) ^ 3 ∣ (((d0 % 2 ^ 64) * d0 : Nat) : Int) - 1 := by
    have hm : (d0 % 2 ^ 64 * d0) % 8 = 1 := by
      rw [Nat.mul_mod, Nat.mod_mod_of_dvd _ (by decide : 8 ∣ 2 ^ 64)]
      have : d0 % 8 = 1 ∨ d0 % 8 = 3 ∨ d0 % 8 = 5 ∨ d0 % 8 = 7 := by omega
      rcases this with h | h | h | h <;> rw [h]
    show (8 : Int) ∣ _
    omega
  have h1 := newton_step d0 _ 3 6 h0 (by omega) (by omega)
  have h2 := newton_step d0 _ 6 12 h1 (by omega) (by omega)
  have h3 := newton_step d0 _ 12 24 h2 (by omega) (by omega)
  have h4 := newton_step d0 _ 24 48 h3 (by omega) (by omega)
  have h5 := newton_step d0 _ 48 64 h4 (by omega) (by omega)
  rw [← inv64_eq] at h5
  generalize Magic.inv64 d0 * d0 = X at *
  rw [show (2 : Int) ^ 64 = ((2 ^ 64 : Nat) : Int) by simp] at h5
  omega

/-! ## `trailingZeros` -/

theorem tz_loop (l : List Nat) : ∀ (n y : Nat), y ≠ 0 →
    ∃ t, (Id.run (forIn l (n, y) fun (_ : Nat) (s : Nat × Nat) =>
        if s.snd % 2 = 1 then pure (ForInStep.done (s.fst, s.snd))
        else pure (ForInStep.yield (s.fst + 1, s.snd / 2)))).fst = n + t ∧
      y = (Id.run (forIn l (n, y) fun (_ : Nat) (s : Nat × Nat) =>
        if s.snd % 2 = 1 then pure (ForInStep.done (s.fst, s.snd))
        else pure (ForInStep.yield (s.fst + 1, s.snd / 2)))).snd * 2 ^ t ∧
      ((Id.run (forIn l (n, y) fun (_ : Nat) (s : Nat × Nat) =>
        if s.snd % 2 = 1 then pure (ForInStep.done (s.fst, s.snd))
        else pure (ForInStep.yield (s.fst + 1, s.snd / 2)))).snd % 2 = 1 ∨ t = l.length) := by
  induction l with
  | nil => intro n y _; exact ⟨0, rfl, (Nat.mul_one y).symm, Or.inr rfl⟩
  | cons a l ih =>
    intro n y hy
    by_cases h : y % 2 = 1
    · exact ⟨0, by simp only [List.forIn_cons, h, ite_true]; exact ⟨rfl, (Nat.mul_one y).symm, Or.inl h⟩⟩
    · obtain ⟨t, h1, h2, h3⟩ := ih (n + 1) (y / 2) (by omega)
      refine ⟨t + 1, ?_⟩
      simp only [List.forIn_cons, h, ite_false, Id.run, pure_bind, List.length_cons] at h1 h2 h3 ⊢
      refine ⟨by omega, ?_, by omega⟩
      rw [Nat.pow_succ, ← Nat.mul_assoc, ← h2]; omega

/-- `x = d0 * 2^k` with `d0` odd, `k = trailingZeros x 64`. -/
theorem trailingZeros_spec (x : Nat) (hx0 : 0 < x) (hx : x < 2 ^ 64) :
    x = x / 2 ^ trailingZeros x 64 * 2 ^ trailingZeros x 64 ∧
      (x / 2 ^ trailingZeros x 64) % 2 = 1 := by
  have hm : ¬ x % 2 ^ 64 = 0 := by rw [Nat.mod_eq_of_lt hx]; omega
  obtain ⟨t, h1, h2, h3⟩ := tz_loop (List.range' 0 64) 0 x (by omega)
  have ht : trailingZeros x 64 = t := by
    unfold trailingZeros
    simp only [hm, ite_false, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.reduceSub, Nat.reduceAdd, Nat.reduceDiv, Nat.zero_add] at h1 ⊢
    exact h1
  subst ht
  have hr0 : 0 < (Id.run (forIn (List.range' 0 64) (0, x) fun (_ : Nat) (s : Nat × Nat) =>
        if s.snd % 2 = 1 then pure (ForInStep.done (s.fst, s.snd))
        else pure (ForInStep.yield (s.fst + 1, s.snd / 2)))).snd := by
    rcases Nat.eq_zero_or_pos (Id.run (forIn (List.range' 0 64) (0, x)
        fun (_ : Nat) (s : Nat × Nat) =>
        if s.snd % 2 = 1 then pure (ForInStep.done (s.fst, s.snd))
        else pure (ForInStep.yield (s.fst + 1, s.snd / 2)))).snd with h0 | h0
    · rw [h0] at h2; omega
    · exact h0
  generalize (Id.run (forIn (List.range' 0 64) (0, x) fun (_ : Nat) (s : Nat × Nat) =>
        if s.snd % 2 = 1 then pure (ForInStep.done (s.fst, s.snd))
        else pure (ForInStep.yield (s.fst + 1, s.snd / 2)))).snd = r at h2 h3 hr0
  have hp : 0 < 2 ^ trailingZeros x 64 := Nat.two_pow_pos _
  have hq : x / 2 ^ trailingZeros x 64 = r := Nat.div_eq_of_eq_mul_left hp h2
  rw [hq]
  refine ⟨h2, ?_⟩
  rcases h3 with h3 | h3
  · exact h3
  · simp only [List.length_range'] at h3
    rw [h3] at h2
    have : 2 ^ 64 ≤ r * 2 ^ 64 := Nat.le_mul_of_pos_left _ hr0
    omega

/-! ## The helpers -/

theorem lowBits_lt (n : Nat) (c : Int) : Magic.lowBits n c < 2 ^ n := by
  unfold Magic.lowBits
  rw [show c.emod (2 ^ n) = c % 2 ^ n from rfl]
  have hp : (0 : Int) < 2 ^ n := Int.pow_pos (by decide)
  have h0 := Int.emod_nonneg c (Int.ne_of_gt hp)
  have h1 := Int.emod_lt_of_pos c hp
  have : ((c % 2 ^ n).toNat : Int) < ((2 ^ n : Nat) : Int) := by
    rw [Int.toNat_of_nonneg h0]; simpa using h1
  exact_mod_cast this

theorem toNat_ofInt (n : Nat) (c : Int) : (BitVec.ofInt n c).toNat = Magic.lowBits n c := by
  rw [BitVec.toNat_ofInt]; rfl

/-- The inverse modulo `2^64` masked to `n` bits is the inverse modulo `2^n`. -/
theorem inv64_mask {n d0 : Nat} (hn1 : 1 ≤ n) (hn : n ≤ 64) (hd0 : d0 % 2 = 1) :
    (Magic.inv64 d0 &&& 2 ^ n - 1) * d0 % 2 ^ n = 1 := by
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.mod_mul_mod,
    ← Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 hn), inv64_spec hd0]
  exact Nat.mod_eq_of_lt (Nat.one_lt_two_pow (by omega))

/-- A failing `udivisible n c`: the divisor's low `n` bits are zero. -/
theorem udivisible_err {n : Nat} {c : Int} {s : String} (h : Magic.udivisible n c = .error s) :
    BitVec.ofInt n c = 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_ofInt, show (0 : BitVec n).toNat = 0 by simp]
  unfold Magic.udivisible at h
  generalize Magic.lowBits n c = d at *
  by_cases hd : d = 0
  · exact hd
  · simp [hd, pure, Except.pure] at h

/-- What `udivisible n c = .ok (k, m, max)` gives: the divisor `d = d0 * 2^k` (`d0` odd), `m`
the inverse of `d0` modulo `2^n`, `max = ⌊(2^n - 1) / d⌋`. -/
theorem udivisible_ok {n : Nat} {c : Int} {k : Int} {m mx : Nat} (hn1 : 1 ≤ n) (hn : n ≤ 64)
    (h : Magic.udivisible n c = .ok (k, m, mx)) :
    ∃ kk d0 : Nat, k = kk ∧ (BitVec.ofInt n c).toNat = d0 * 2 ^ kk ∧ d0 % 2 = 1 ∧
      m * d0 % 2 ^ n = 1 ∧ mx = (2 ^ n - 1) / (d0 * 2 ^ kk) := by
  rw [toNat_ofInt]
  have hlt := lowBits_lt n c
  unfold Magic.udivisible at h
  generalize Magic.lowBits n c = d at *
  by_cases hd : d = 0
  · simp [hd] at h; cases h
  simp only [hd, ite_false, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  have h64 : d < 2 ^ 64 := Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) hn)
  obtain ⟨he, hodd⟩ := trailingZeros_spec d (by omega) h64
  refine ⟨trailingZeros d 64, d / 2 ^ trailingZeros d 64, rfl, he, hodd, ?_, by rw [← he]⟩
  rw [Nat.shiftRight_eq_div_pow]
  exact inv64_mask hn1 hn hodd

/-- `modularMultiplicativeInverse`: on success the argument is odd and the result its inverse
modulo `2^64`. -/
theorem modInverse_ok {x y : Nat} (h : Magic.modInverse x = .ok y) :
    x % 2 = 1 ∧ y * x % 2 ^ 64 = 1 := by
  unfold Magic.modInverse at h
  by_cases hx : x % 2 = 1
  · simp only [hx, bne_self_eq_false, Bool.false_eq_true, ite_false, pure, Except.pure,
      Except.ok.injEq] at h
    subst h
    exact ⟨hx, inv64_spec hx⟩
  · have h0 : x % 2 = 0 := by omega
    simp [h0, throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map] at h

/-! ## Tactics

`rule_norm` cannot run on a goal that still applies a helper to a constant: `simp`'s match
reduction puts `udivisible 16 c` into `whnf` (Newton's iteration on 64-bit numbers). The call is
generalized first (`divisible_gen`), its result split into the error and success cases, and the
success case's fields replaced by fresh variables with their specification. -/

open Lean Meta Elab Tactic in
/-- Generalize the first call of `Magic.udivisible`, `Magic.sdivisible` or `Magic.modInverse`
(goal first, then the hypotheses) to `U`, with the equation `hU`. -/
elab "divisible_gen" : tactic => withMainContext do
  let isCall (t : Lean.Expr) := !t.hasLooseBVars &&
    (t.isAppOfArity ``GoFV.Rules.Magic.udivisible 2 ||
      t.isAppOfArity ``GoFV.Rules.Magic.sdivisible 2 ||
      t.isAppOfArity ``GoFV.Rules.Magic.modInverse 1)
  let mut cand := (← instantiateMVars (← getMainTarget)).find? isCall
  for h in ← getLCtx do
    if cand.isNone && !h.isImplementationDetail then
      cand := (← instantiateMVars h.type).find? isCall
  let some c := cand | throwError "divisible_gen: no helper call"
  let stx ← Term.exprToSyntax c
  evalTactic (← `(tactic| generalize $(mkIdent `hU) : $stx = $(mkIdent `U) at *))

open Lean Meta Elab Tactic in
/-- Generalize the result side `R` of a `Refines L R` goal (where the source `L` is `poison`,
the oracle's answers in `R` need not be normalized). -/
elab "divisible_gen_rhs" : tactic => withMainContext do
  let t := (← instantiateMVars (← getMainTarget)).consumeMData
  unless t.isApp do throwError "divisible_gen_rhs: not an application"
  let stx ← Term.exprToSyntax t.appArg!
  evalTactic (← `(tactic| generalize $stx = $(mkIdent `R)))

/-- The struct fields of an evaluated helper call, then `rule_auto`'s steps up to the final
arithmetic. -/
macro "divisible_rest" : tactic => `(tactic| (
  (try simp only [GoFV.Proof.Rules.udivDV, GoFV.Proof.Rules.sdivDV, GoFV.Proof.Rules.strctField,
    List.find?, Option.map, String.reduceBEq] at *)
  rule_norm
  (try rule_ands)
  all_goals (repeat rule_split1)
  all_goals (try rule_widths)
  all_goals (repeat rule_gen1)
  all_goals (try simp only [GoFV.Proof.Rules.DV.int.injEq, GoFV.Proof.Rules.DV.bool.injEq] at *)
  all_goals (try rule_ands)
  all_goals (try rule_subst)
  all_goals (try rule_norm)
  all_goals (try simp_all only [rule_arith, rule_close_s])))

end GoFV.Proof.Rules.Divisible
