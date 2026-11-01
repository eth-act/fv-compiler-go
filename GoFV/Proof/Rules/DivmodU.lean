import GoFV.Proof.Rules.Tactic
import GoFV.Proof.Rules.NonVacuous
import GoFV.Rules.Generated.Divmod.Values00
import GoFV.Proof.Rules.DivmodUMagic

/-!
# Unsigned magic-number division rules of `divmod.rules` (#69)

`umagic_elim` replaces the helper call `umagic w c` of a rule by `.ok (S, m)` (`umagic_ok`,
under `umagicOK w c`; otherwise the condition is false), then the `rule_auto` steps leave a
`BitVec` equation closed by the lemmas of `DivmodUMagic.lean`.
-/

namespace GoFV.Proof.Rules.DivmodU

open Lean Elab Tactic Meta

/-- Replace the call `umagic w c` of the goal by `.ok (S, m)` with `hspec : USpec w c S m`
when `umagicOK w c`; otherwise rewrite `umagicOK w c` to `false` everywhere (the condition is
then false). Run before `rule_ands`: splitting the condition first makes the kernel's check
hit "deep recursion" (`divmod.rules:159`). -/
elab "umagic_elim" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let some u := t.find? (fun s => s.isAppOfArity ``GoFV.Rules.Magic.umagic 2)
    | throwError "umagic_elim: no `umagic` call"
  let w ← Term.exprToSyntax (u.getArg! 0)
  let c ← Term.exprToSyntax (u.getArg! 1)
  let hok := mkIdent `hok
  let hspec := mkIdent `hspec
  let hum := mkIdent `hum
  evalTactic (← `(tactic| (
    rcases Bool.eq_false_or_eq_true (GoFV.Rules.Magic.umagicOK $w $c) with $hok:ident | $hok:ident
    all_goals first
      | (have hpos : GoFV.Rules.Magic.umagicOK $w $c = true := $hok:ident
         obtain ⟨S, m, $hum:ident, $hspec:ident⟩ := GoFV.Proof.Rules.DivmodU.umagic_ok hpos
         simp only [$hum:ident, $hok:ident, magicDV, strctField, List.find?_cons, String.reduceBEq,
           Option.map_some, Option.isSome_some, ite_true, Bool.cond_true] at *)
      | simp only [$hok:ident, Bool.cond_false, Bool.false_eq_true] at *)))

/-- `rule_auto` after `umagic_elim`, up to the closing step. -/
macro "divu_auto" : tactic => `(tactic| (
  umagic_elim
  all_goals (try rule_ands)
  all_goals (try rule_clear_oracle)
  all_goals (try rule_norm)
  all_goals (try rule_ands)
  all_goals (repeat rule_split1)
  all_goals (try rule_widths)
  all_goals (repeat rule_gen1)
  all_goals (try simp only [GoFV.Proof.Rules.DV.int.injEq, GoFV.Proof.Rules.DV.bool.injEq] at *)
  all_goals (try rule_ands)
  all_goals (try rule_subst)
  all_goals (try rule_norm)
  all_goals (try simp_all only [rule_arith, rule_close_s])))

/-- Side goals of the closing lemmas: constants and shift amounts as `Nat` arithmetic. -/
macro "divu_side" : tactic => `(tactic| (
  have := (‹GoFV.Proof.Rules.DivmodU.USpec _ _ _ _›).m_lt
  have := (‹GoFV.Proof.Rules.DivmodU.USpec _ _ _ _›).S_le
  have := (‹GoFV.Proof.Rules.DivmodU.USpec _ _ _ _›).S_ge
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofInt,
    Nat.reducePow, Nat.reduceMod] at *
  omega))

end GoFV.Proof.Rules.DivmodU

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules.DivmodU

theorem r_divmod_154_sound : Rule.Sound GoFV.Rules.Generated.Divmod.r_divmod_154 := by
  rule_unfold
  divu_auto
  all_goals exact close_mul_full _ _ _ _ hspec (by decide) (by divu_side) (by divu_side)

/-- `divmod.rules:154` at `x = 100`, `c = 7` (`umagic8(7) = (3, 37)`). -/
theorem inst_r_divmod_154 : Rule.Inst GoFV.Rules.Generated.Divmod.r_divmod_154
    (PEnv.ofLists [([0], .i8 100)] [] (.int .w8) [([1], 7)]) (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Divmod.r_divmod_154]
  rule_eval
  rfl

end GoFV.Proof.Rules
