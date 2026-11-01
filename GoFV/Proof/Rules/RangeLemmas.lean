import GoFV.Proof.Rules.Tactic

/-!
# The comparisons the range-check rules fold (`generic.rules:321–366`), any width

Each rule's result as the `&&`/`||` of its two comparisons, for `rule_range`
(`TacticRange.lean`): signed `s`, unsigned `u`; `1`: the constant is `c + 1`/`d + 1`; `_le`: the
`Leq…U` result. Proved once as `toNat`/`toInt` arithmetic (`toNat_sub_cases`,
`toNat_add_one_cases`, `BitVec.toInt_eq_toNat_cond`; `ite_facts`, `omega` with `2 ^ w` an atom):
`omega` on each rule's residual goals instead stored ~25k proof terms per rule (~800 kB of
`.olean`). The signed `1` lemmas are in `RangeLemmas2.lean` (`.olean` size).
-/

namespace GoFV.Proof.Rules

open Lean Meta Elab Tactic

theorem ite_or {α : Sort _} {c : Prop} [Decidable c] {a b : α} (x : α)
    (hx : x = if c then a else b) : (x = a ∧ c) ∨ (x = b ∧ ¬c) := by
  subst hx; by_cases h : c <;> simp [h]

/-- Both cases of every closed `if` in the goal and the hypotheses as a hypothesis
(`ite_or`), for `omega`. -/
elab "ite_facts" : tactic => withMainContext do
  let isIte (t : Lean.Expr) : Bool := t.isAppOfArity ``ite 5 && !t.hasLooseBVars
  let mut ts : Array Lean.Expr := subtermsWith isIte (← instantiateMVars (← getMainTarget))
  for h in ← getLCtx do
    if !h.isImplementationDetail then
      for t in subtermsWith isIte (← instantiateMVars h.type) do
        unless ts.contains t do ts := ts.push t
  for t in ts do
    let x ← Term.exprToSyntax t
    evalTactic (← `(tactic| have := GoFV.Proof.Rules.ite_or $x rfl))

/-- `toNat` of a difference: `y - z` without and with a borrow. -/
theorem toNat_sub_cases {w : Nat} (y z : BitVec w) :
    (y - z).toNat = if z.toNat ≤ y.toNat then y.toNat - z.toNat else 2 ^ w - z.toNat + y.toNat := by
  have hy := y.isLt
  have hz := z.isLt
  rw [BitVec.toNat_sub]
  split
  · rw [show 2 ^ w - z.toNat + y.toNat = (y.toNat - z.toNat) + 2 ^ w by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

/-- `toNat` of a successor, with and without the wrap to `0`. -/
theorem toNat_add_one_cases {w : Nat} (c : BitVec w) :
    (c + 1#w).toNat = if c.toNat + 1 < 2 ^ w then c.toNat + 1 else 0 := by
  have hc := c.isLt
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  rcases w with _ | w
  · simp at *; omega
  · rw [Nat.one_mod_two_pow (by omega)]
    split
    · exact Nat.mod_eq_of_lt ‹_›
    · rw [show c.toNat + 1 = 2 ^ (w + 1) by omega, Nat.mod_self]

/-- Proof of a `range_*` lemma. -/
macro "range_lemma " x:term:max c:term:max d:term:max : tactic => `(tactic| (
  simp only [BitVec.sub_sub, BitVec.ult, BitVec.ule, BitVec.slt, BitVec.sle, toNat_sub_cases, toNat_add_one_cases, BitVec.toInt_eq_toNat_cond] at *
  have := ($x).isLt
  have := ($c).isLt
  have := ($d).isLt
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.or_eq_true]
  ite_facts
  omega))

theorem range_and_s {w : Nat} (x c d : BitVec w) (h : c.toInt ≤ d.toInt) :
    (x - c).ult (d - c) = (c.sle x && x.slt d) := by
  range_lemma x c d

theorem range_and_s_le {w : Nat} (x c d : BitVec w) (h : c.toInt ≤ d.toInt) :
    (x - c).ule (d - c) = (c.sle x && x.sle d) := by
  range_lemma x c d

theorem range_or_s {w : Nat} (x c d : BitVec w) (h : d.toInt ≤ c.toInt) :
    (c - d).ult (x - d) = (c.slt x || x.slt d) := by
  range_lemma x c d

theorem range_or_s_le {w : Nat} (x c d : BitVec w) (h : d.toInt ≤ c.toInt) :
    (c - d).ule (x - d) = (c.sle x || x.slt d) := by
  range_lemma x c d

theorem range_and_u {w : Nat} (x c d : BitVec w) (h : c.toNat ≤ d.toNat) :
    (x - c).ult (d - c) = (c.ule x && x.ult d) := by
  range_lemma x c d

theorem range_and_u_le {w : Nat} (x c d : BitVec w) (h : c.toNat ≤ d.toNat) :
    (x - c).ule (d - c) = (c.ule x && x.ule d) := by
  range_lemma x c d

theorem range_and_u1 {w : Nat} (x c d : BitVec w) (h : c.toNat + 1 ≤ d.toNat) :
    (x - (c + 1#w)).ult (d - c - 1#w) = (c.ult x && x.ult d) := by
  range_lemma x c d

theorem range_and_u1_le {w : Nat} (x c d : BitVec w) (h : c.toNat + 1 ≤ d.toNat) :
    (x - (c + 1#w)).ule (d - c - 1#w) = (c.ult x && x.ule d) := by
  range_lemma x c d

theorem range_or_u {w : Nat} (x c d : BitVec w) (h : d.toNat ≤ c.toNat) :
    (c - d).ult (x - d) = (c.ult x || x.ult d) := by
  range_lemma x c d

theorem range_or_u_le {w : Nat} (x c d : BitVec w) (h : d.toNat ≤ c.toNat) :
    (c - d).ule (x - d) = (c.ule x || x.ult d) := by
  range_lemma x c d

theorem range_or_u1 {w : Nat} (x c d : BitVec w) (h : d.toNat + 1 ≤ c.toNat) :
    (c - d - 1#w).ult (x - (d + 1#w)) = (c.ult x || x.ule d) := by
  range_lemma x c d

theorem range_or_u1_le {w : Nat} (x c d : BitVec w) (h : d.toNat + 1 ≤ c.toNat) :
    (c - d - 1#w).ule (x - (d + 1#w)) = (c.ule x || x.ule d) := by
  range_lemma x c d

end GoFV.Proof.Rules
