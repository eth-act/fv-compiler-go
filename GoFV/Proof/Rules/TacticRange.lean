import GoFV.Proof.Rules.RangeLemmas2

/-!
# `rule_range`: integer range checks combined by `AndB`/`OrB` (`generic.rules:321–366`)

`(AndB (Leq64 (Const64 [c]) x) (Less64 x (Const64 [d])))` and its relatives fold two signed or
unsigned comparisons of `x` with constants into one unsigned comparison of `x - c`. `rule_auto`
fails on them for two reasons (#69, RuleProofs8):

* `AndB`/`OrB` evaluate their operands to `Option Bool`: with one operand a mistyped constant
  (`tyOtherInt`) its comparison is `none`, and the result is a `match none, some b`, which
  `rule_split1` does not split. `bool_split1` cases on such a `b`. `rule_auto`'s `repeat` also
  stops at the first case that cannot be split further; `rule_range` uses `repeat'`.
* The residual goals equate the result with the comparison the case splits decided. As
  `toNat`/`toInt` arithmetic they contain the signed reading
  `if 2 * x.toNat < 2 ^ w then x.toNat else x.toNat - 2 ^ w`, which `rule_cmpc`'s `split` (goal
  only) does not reach. `rule_range` instead rewrites the result by one of the `range_*` lemmas
  below (any width), e.g. `(x - c).ult (d - c) = (c.sle x && x.slt d)`, and `simp_all` closes
  the goal from the case hypotheses.

Kept out of `Tactic.lean`: changing it rebuilds every rule module.
-/

namespace GoFV.Proof.Rules

open Lean Meta Elab Tactic

/-- Case split on one non-literal `Bool` under `Option.some` in the goal or a hypothesis (the
other operand of `AndB`/`OrB` is `none`), then `rule_norm`. -/
elab "bool_split1" : tactic => withMainContext do
  let isB (t : Lean.Expr) : Bool := t.isAppOfArity ``Option.some 2 &&
    (t.getArg! 0).isConstOf ``Bool && !(t.getArg! 1).isConstOf ``Bool.true &&
    !(t.getArg! 1).isConstOf ``Bool.false && !t.hasLooseBVars
  let mut cand := (← instantiateMVars (← getMainTarget)).find? isB
  for h in ← getLCtx do
    if cand.isNone && !h.isImplementationDetail then
      cand := (← instantiateMVars h.type).find? isB
  let some c := cand | throwError "bool_split1: nothing to split"
  let b ← Term.exprToSyntax (c.getArg! 1)
  evalTactic (← `(tactic| (rcases hb : $b:term with _ | _ <;> (try rule_norm))))

theorem wrapInt_false_mod (w : Nat) (x : Int) : GoFV.Rules.wrapInt w false x = x % 2 ^ w := rfl

/-- Side conditions of the `range_*` lemmas at constants `BitVec.ofInt w c` of the auxint
ranges: as `Int` arithmetic. -/
macro "range_disch" : tactic => `(tactic| (
  simp (disch := omega) only [BitVec.toInt_ofInt, Int.bmod_eq_of_le, BitVec.toNat_ofInt,
    wrapInt_false_mod, Int.reducePow, Nat.reducePow] at *
  omega))

/-- `rule_auto` for the range rules: `bool_split1` next to `rule_split1` (each case split
on), then `rule_close`'s preparation and, instead of its closers, the result rewritten by a
`range_*` lemma to the `&&`/`||` of the comparisons the case splits decided (`simp_all`). No
`bv_decide`. -/
macro "rule_range" : tactic => `(tactic| (
  rule_unfold
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
    try simp_all only [rule_arith, rule_close_s]
    first
    | done
    | with_reducible rfl
    | (simp (disch := range_disch) only [range_and_s, range_and_s_le, range_and_s1,
         range_and_s1_le, range_or_s, range_or_s_le, range_or_s1, range_or_s1_le, range_and_u,
         range_and_u_le, range_and_u1, range_and_u1_le, range_or_u, range_or_u_le, range_or_u1,
         range_or_u1_le]
       simp_all))))

end GoFV.Proof.Rules
