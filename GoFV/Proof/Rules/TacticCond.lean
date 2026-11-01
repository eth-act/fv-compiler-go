import GoFV.Proof.Rules.Tactic
import GoFV.Proof.Rules.AttrCond

/-!
# `rule_unfold_getd`: `rule_unfold` with the condition's `Option.getD` kept folded

`rule_unfold` evaluates the condition `hcond` by `dsimp only [condHolds, rule_unfold_ds]`, which
also unfolds every `Option.getD` (an expression's value or the oracle's answer) to its `match`.
For conditions with several helper calls (`divmod.rules:171`, `:180`, `:206`: `umagic64(c).m`;
`generic.rules:369`, `:372`: `oneBit`) the kernel's check of that `dsimp` step (the new type of
`hcond` against `condHolds …`) then fails with "deep recursion" as soon as the proof uses
`hcond`; `set_option maxRecDepth` does not help (#69, RuleProofs6/9/10). Without `Option.getD`
in the `dsimp` set the check passes: `rule_unfold_getd` evaluates the condition with
`rule_cond_ds` (= `rule_unfold_ds` without `Option.getD`), and the `Option.getD`s are rewritten
by `simp` (`Option.getD_some`, `Option.getD_none` in `rule_unfold_s`) as their arguments
evaluate. `rule_cond_bool_getd` is `rule_cond_bool` for the folded form
`(binDV o t X Y).getD (.bool w)` (`binDV_cmp_bool`).

Kept out of `Tactic.lean`: changing it rebuilds every rule module.
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules
open Lean Meta Elab Tactic

attribute [rule_cond_ds] GoFV.Proof.Rules.Pat.den GoFV.Proof.Rules.Pat.dens
  GoFV.Proof.Rules.Pat.raw GoFV.Proof.Rules.sigma GoFV.Proof.Rules.Pat.binds
  GoFV.Proof.Rules.Pat.bindss GoFV.Proof.Rules.Pat.cons GoFV.Proof.Rules.Pat.conss
  GoFV.Proof.Rules.Pat.wf GoFV.Proof.Rules.Pat.wfs GoFV.Proof.Rules.Pat.typed
  GoFV.Proof.Rules.Pat.typeds GoFV.Proof.Rules.auxIntOk
  GoFV.Proof.Rules.Field.bindDV GoFV.Proof.Rules.resDen
  GoFV.Proof.Rules.nodeDen List.length List.getElem?_cons_zero List.getElem?_cons_succ List.map
  GoFV.Proof.Rules.reduceEvalPure GoFV.Proof.Rules.reduceAuxType GoFV.Proof.Rules.evalE
  GoFV.Proof.Rules.evalEs GoFV.Proof.Rules.auxIntDV List.lookup GoFV.Proof.Rules.toAuxIntD
  List.cons_append List.nil_append GoFV.Proof.Rules.intBin GoFV.Proof.Rules.binDV
  GoFV.Rules.wrapTo GoFV.Proof.Rules.reduceIntInfo GoFV.Proof.Rules.litDV GoFV.Proof.Rules.fieldE
  GoFV.Proof.Rules.indexE GoFV.Proof.Rules.convE GoFV.Proof.Rules.callE GoFV.Proof.Rules.methodE
  GoFV.Proof.Rules.builtinE GoFV.Proof.Rules.unDV GoFV.Proof.Rules.fieldDV
  GoFV.Proof.Rules.DV.valOr GoFV.Proof.Rules.typesShape GoFV.Proof.Rules.shapeSize Option.map
  GoFV.Proof.Rules.exprTy List.getD List.getD_cons_zero List.getD_cons_succ List.zip_cons_cons
  List.zip_nil_left List.zip_nil_right and_true true_and Nat.reduceAdd Nat.reduceBEq Nat.reduceBNe
  reduceIte

/-- `Option.getD_some` with a proof term: as an `rfl` lemma `simp` applies it without one, and
the kernel must then see that the two sides of the next rewrite agree, which it may try by
unfolding the other side first (`cond (umagicOK 64 c) …`: deep recursion). -/
theorem getD_some_p {α : Type} (a b : α) : (some a).getD b = a := by
  simp only [Option.getD_some]

/-- `Option.getD_none` with a proof term (`getD_some_p`). -/
theorem getD_none_p {α : Type} (b : α) : (none : Option α).getD b = b := by
  simp only [Option.getD_none]

/-- `Option.elim_some` with a proof term (`getD_some_p`; `divmod.rules:232`: the kernel
compared `if x < y then …` with `(some y).elim …` and hit deep recursion). -/
theorem elim_some_p {α β : Type} (a : α) (b : β) (f : α → β) : (some a).elim b f = f a := by
  simp only [Option.elim_some]

/-! In this namespace `rule_norm` rewrites `(some a).getD b`, `(some a).elim b f` with proof
terms (`getD_some_p`, `elim_some_p`; listed first, they are tried before the `rfl` lemmas of
the simp sets, which `-Option.getD_some` would not erase): `open
GoFV.Proof.Rules.KernelSafe in theorem …` for the rules whose proofs the kernel otherwise
rejects with "deep recursion". -/

namespace KernelSafe

scoped macro_rules
  | `(tactic| rule_norm) => `(tactic|
    simp_all (config := { decide := true }) only [GoFV.Proof.Rules.elim_some_p,
      GoFV.Proof.Rules.getD_some_p, rule_sem, rule_helper, rule_norm_s])

end KernelSafe

attribute [rule_cond_s] GoFV.Proof.Rules.reduceCallH Option.isSome_some ite_true ite_false
  GoFV.Proof.Rules.binE_land_bool
  GoFV.Proof.Rules.binE_lor_bool GoFV.Proof.Rules.binE_eq GoFV.Proof.Rules.binE_ne
  GoFV.Proof.Rules.binE_lt GoFV.Proof.Rules.binE_le GoFV.Proof.Rules.binE_gt
  GoFV.Proof.Rules.binE_ge GoFV.Proof.Rules.binE_add GoFV.Proof.Rules.binE_sub
  GoFV.Proof.Rules.binE_mul GoFV.Proof.Rules.binE_quo GoFV.Proof.Rules.binE_rem
  GoFV.Proof.Rules.binE_and GoFV.Proof.Rules.binE_or GoFV.Proof.Rules.binE_xor
  GoFV.Proof.Rules.binE_shl GoFV.Proof.Rules.binE_shr GoFV.Proof.Rules.binE_andNot
  GoFV.Proof.Rules.dv_ite_land GoFV.Proof.Rules.dv_ite_lor GoFV.Proof.Rules.dv_land_true
  GoFV.Proof.Rules.dv_lor_true GoFV.Proof.Rules.DV.bool.injEq Bool.and_eq_true Bool.or_eq_true
  bne_iff_ne ne_eq beq_iff_eq GoFV.Proof.Rules.binDV GoFV.Proof.Rules.intBin
  GoFV.Proof.Rules.fieldDV Option.map_some Option.map_none GoFV.Proof.Rules.getD_some_p
  GoFV.Proof.Rules.getD_none_p
  reduceCtorEq true_or or_true and_true true_and beq_self_eq_true Bool.cond_false Bool.cond_true
  GoFV.Rules.wrapTo GoFV.Proof.Rules.reduceIntInfo

/-- `rule_cond_bool` for a comparison left as `(binDV o t X Y).getD (.bool w)` (`binDV` stuck
on an oracle answer): replaced by a fresh `Bool` (`binDV_cmp_bool`). -/
elab "rule_cond_bool_getd" : tactic => withMainContext do
  let hcs := mkIdent `hcond
  let mut tried : Array Lean.Expr := #[]
  for _ in [0:16] do
    let some hc := (← getLCtx).findFromUserName? `hcond | return
    let ty ← instantiateMVars hc.type
    let cands := subtermsWith (fun t => t.isAppOfArity ``Option.getD 3 &&
      !t.hasLooseBVars && !tried.contains t &&
      (t.getArg! 2).isAppOfArity ``DV.bool 1 &&
      (t.getArg! 1).isAppOfArity ``binDV 4) ty
    -- the value of a `DV.val` is not read by a field other than `Type`/`AuxInt`
    let readsInst (c : Lean.Expr) : Bool :=
      let c' := c.replace fun t =>
        if t.isAppOfArity ``DV.val 2 then some (mkConst ``True) else none
      (c'.find? fun t => (t.isAppOfArity ``PEnv.ty 2 || t.isAppOfArity ``PEnv.auxInt 2) &&
        !t.hasLooseBVars).isSome
    let some c := cands.find? (!readsInst ·) | return
    tried := tried.push c
    let a ← Term.exprToSyntax c
    for o in [``BinOp.eq, ``BinOp.ne, ``BinOp.lt, ``BinOp.le, ``BinOp.gt, ``BinOp.ge] do
      let saved ← saveState
      let ok ← try
          evalTactic (← `(tactic| (
            obtain ⟨_, hab⟩ : ∃ b, $a = DV.bool b :=
              GoFV.Proof.Rules.binDV_cmp_bool (o := $(mkIdent o)) (by decide) _ _ _ _
            simp only [hab, rule_cond_s] at $hcs:ident
            clear hab)))
          pure true
        catch _ => saved.restore; pure false
      if ok then break

/-- `rule_unfold` with the condition evaluated by `rule_cond_ds` (no `Option.getD`). -/
elab "rule_unfold_getd" : tactic => do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let some r := ty.getAppArgs[0]? | throwError "rule_unfold_getd: goal is not `Rule.Sound r`"
  let some rn := r.constName? | throwError "rule_unfold_getd: rule is not a constant"
  let rid := mkIdent rn
  let e := mkIdent `e
  let or := mkIdent `or
  let hbt := mkIdent `hbt
  let hwf := mkIdent `hwf
  let hc := mkIdent `hc
  let hcond := mkIdent `hcond
  let hty := mkIdent `hty
  let hlt := mkIdent `hlt
  let hat := mkIdent `hat
  let some ci := (← getEnv).find? rn | throwError "rule_unfold_getd: unknown rule"
  let usesArgShape := ci.value?.any fun v =>
    (v.find? fun t => (argShapeOps ++ eqShapeOps).any t.isConstOf).isSome
  evalTactic (← `(tactic| (
    refine ⟨rfl, ?_⟩
    intro $e:ident $or:ident $hbt:ident
    dsimp only [$rid:ident, rule_unfold_ds]
    simp only [rule_helper, rule_unfold_s]
    intro $hwf:ident $hc:ident $hcond:ident $hty:ident $hlt:ident $hat:ident $(mkIdent `hnn):ident
    (try dsimp only [GoFV.Proof.Rules.condHolds, rule_cond_ds] at $hcond:ident)
    (try simp only [rule_helper, rule_cond_s] at $hcond:ident)
    rule_oracle_bool
    rule_cond_bool_getd)))
  if usesArgShape then
    evalTactic (← `(tactic| try simp only [GoFV.Proof.Rules.Pat.argsOK, GoFV.Proof.Rules.Pat.argsOKs,
      GoFV.Proof.Rules.argShapeOk, GoFV.Proof.Rules.isPtrTy_iff, GoFV.Proof.Rules.isInt64Ty_iff,
      GoFV.Proof.Rules.isIntWTy_iff,
      GoFV.Proof.Rules.convArgOk, Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
      beq_iff_eq, Nat.reduceEqDiff, reduceIte, not_true_eq_false, false_or, true_or, or_true,
      and_true, true_and, Nat.succ_ne_zero, not_false_eq_true] at $hat:ident))
  else
    evalTactic (← `(tactic| clear $hat:ident))
  ruleNonNeg ci

end GoFV.Proof.Rules
