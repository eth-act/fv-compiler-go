import GoFV.Proof.Rules.Tactic
import GoFV.Proof.Rules.NonVacuous
import GoFV.Rules.Generated.Divmod.Values00
import GoFV.Proof.Rules.DivmodUMagic

/-!
# Unsigned magic-number division rules of `divmod.rules` (#69)

`umagic_elim` replaces the helper call `umagic w c` of a rule by `.ok (S, m)` (`umagic_ok`,
under `umagicOK w c`; otherwise the condition is false), then the `rule_auto` steps leave a
`BitVec` equation closed by the lemmas of `DivmodUMagic.lean`.

`divu_unfold` is `rule_unfold` with the condition evaluated in a separate step after the
intros: in one `dsimp` cast together with the rest, the kernel's check of the cast hits
"deep recursion" on rules whose condition has more than the `umagicOK` call (`divmod.rules:159`,
`:166`, `:180`, …; `maxRecDepth 100000` does not help for `:180`).
-/

attribute [divu_unfold_ds] GoFV.Proof.Rules.Pat.den GoFV.Proof.Rules.Pat.dens
  GoFV.Proof.Rules.Pat.raw GoFV.Proof.Rules.sigma GoFV.Proof.Rules.Pat.binds
  GoFV.Proof.Rules.Pat.bindss GoFV.Proof.Rules.Pat.cons GoFV.Proof.Rules.Pat.conss
  GoFV.Proof.Rules.Pat.wf GoFV.Proof.Rules.Pat.wfs GoFV.Proof.Rules.Pat.typed
  GoFV.Proof.Rules.Pat.typeds GoFV.Proof.Rules.auxIntOk
  GoFV.Proof.Rules.Field.bindDV GoFV.Proof.Rules.resDen
  GoFV.Proof.Rules.nodeDen List.length List.getElem?_cons_zero List.getElem?_cons_succ List.map
  GoFV.Proof.Rules.reduceEvalPure GoFV.Proof.Rules.reduceAuxType GoFV.Proof.Rules.evalE
  GoFV.Proof.Rules.evalEs GoFV.Proof.Rules.auxIntDV List.lookup GoFV.Proof.Rules.toAuxIntD
  Option.getD List.cons_append List.nil_append GoFV.Proof.Rules.intBin GoFV.Proof.Rules.binDV
  GoFV.Rules.wrapTo GoFV.Proof.Rules.reduceIntInfo GoFV.Proof.Rules.litDV GoFV.Proof.Rules.fieldE
  GoFV.Proof.Rules.indexE GoFV.Proof.Rules.convE GoFV.Proof.Rules.callE GoFV.Proof.Rules.methodE
  GoFV.Proof.Rules.builtinE GoFV.Proof.Rules.unDV GoFV.Proof.Rules.fieldDV
  GoFV.Proof.Rules.DV.valOr GoFV.Proof.Rules.typesShape GoFV.Proof.Rules.shapeSize Option.map
  GoFV.Proof.Rules.exprTy List.getD List.getD_cons_zero List.getD_cons_succ List.zip_cons_cons
  List.zip_nil_left List.zip_nil_right and_true true_and Nat.reduceAdd Nat.reduceBEq Nat.reduceBNe
  reduceIte

namespace GoFV.Proof.Rules.DivmodU

open Lean Elab Tactic Meta

/-- `rule_unfold`, the condition evaluated after the intros (module doc). -/
elab "divu_unfold" : tactic => do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let some r := ty.getAppArgs[0]? | throwError "divu_unfold: goal is not `Rule.Sound r`"
  let some rn := r.constName? | throwError "divu_unfold: rule is not a constant"
  let rid := mkIdent rn
  let e := mkIdent `e
  let or := mkIdent `or
  let hbt := mkIdent `hbt
  let hwf := mkIdent `hwf
  let hc := mkIdent `hc
  let hcond := mkIdent `hcond
  let hty := mkIdent `hty
  let hlt := mkIdent `hlt
  evalTactic (← `(tactic| (
    refine ⟨rfl, ?_⟩
    intro $e:ident $or:ident $hbt:ident
    dsimp only [$rid:ident, divu_unfold_ds]
    simp only [rule_helper, rule_unfold_s]
    intro $hwf:ident $hc:ident $hcond:ident $hty:ident $hlt:ident
    dsimp only [GoFV.Proof.Rules.condHolds, rule_unfold_ds] at $hcond:ident
    (try simp only [rule_helper, rule_unfold_s] at $hcond:ident)
    rule_oracle_bool)))

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
