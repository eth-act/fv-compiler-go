import Lean
import GoFV.Proof.Low.Rules.Kit

/-!
# Tactics for the lowering rule lemmas (issue #385)

`arm_unfold` reduces `ArmRule.Sound r` (`r` a constant) to one goal per commutation choice of
its pattern (`Rule.swapC`): the semantic statement of the swapped pattern and the result, with
the hypotheses `hbt` (`Oracle.BoolTyped`), `hwf`, `hc`, `hcond`, `hty`, `hat`, `htop` as Phase 1's
`rule_unfold` names them (`GoFV/Proof/Rules/Tactic.lean`), the condition's oracle atoms
replaced by booleans (`rule_oracle_bool`, `rule_cond_bool`).

`arm_shape` splits the shape of the matched value when the top op is generic: `topOKL` (`htop`)
leaves the op's own shape (`.int w`, `.bool`, a pointer); the other cases close.
-/

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules GoFV.Proof.Low
open Lean Meta Elab Tactic

attribute [rule_unfold_ds] GoFV.Proof.Low.auxIntDVL

/-- `ArmRule.Sound r` (`r` a constant, or a constant applied to closed arguments): one goal per
commutation choice, unfolded (module doc). -/
elab "arm_unfold" : tactic => do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let some r := ty.getAppArgs[0]? | throwError "arm_unfold: goal is not `ArmRule.Sound r`"
  let some rn := r.getAppFn.constName? | throwError "arm_unfold: rule is not a constant"
  let rid := mkIdent rn
  let n ← withTransparency .all <| reduce
    (mkApp (mkConst ``GoFV.Opt.RewriteCheck.Pat.commutes) (mkApp (mkConst ``GoFV.Rules.Rule.pat) r))
  let some k := n.rawNatLit? <|> n.nat? | throwError "arm_unfold: commutation count {n}"
  let hsw := mkIdent `hsw
  let hsw' := mkIdent `hsw'
  evalTactic (← `(tactic| (
    intro $(mkIdent `sw):ident $hsw:ident
    simp only [$rid:ident, GoFV.Opt.RewriteCheck.Pat.commutes,
      GoFV.Opt.RewriteCheck.Pat.commutess, ite_true, ite_false, Bool.false_eq_true,
      Nat.reduceAdd, GoFV.Opt.RewriteCheck.choices, List.flatMap_cons, List.flatMap_nil,
      List.cons_append, List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil,
      or_false] at $hsw:ident)))
  for _ in [1:2 ^ k] do
    evalTactic (← `(tactic| all_goals (try (rcases $hsw:ident with $hsw':ident | $hsw:ident <;>
      (try subst $hsw':ident)))))
  evalTactic (← `(tactic| all_goals (try subst $hsw:ident)))
  evalTactic (← `(tactic| all_goals (
    refine ⟨rfl, ?_⟩
    intro $(mkIdent `tabs):ident $(mkIdent `e):ident $(mkIdent `or):ident $(mkIdent `hbt):ident
    dsimp only [Rule.swapC, Pat.swapC, Pat.swapCs, GoFV.Opt.RewriteCheck.swap01, $rid:ident,
      Pat.denL, Pat.densL, Pat.rawL, sigmaL, Pat.bindsL, Pat.bindssL, resDenL, nodeDenL, toAuxIntL,
      nodeTyL, nodeAuxL, Pat.auxPos, Pat.auxPoss, Pat.topOKL, rule_unfold_ds]
    simp only [Pat.denL, Pat.densL, Pat.rawL, sigmaL, Pat.bindsL, Pat.bindssL, nodeDenL,
      Pat.auxPos, Pat.auxPoss, GoFV.Rules.Field.bindsVar, Option.orElse_some, Option.orElse_none,
      rule_unfold_ds, rule_helper, rule_unfold_s]
    intro $(mkIdent `hwf):ident $(mkIdent `hc):ident $(mkIdent `hcond):ident
      $(mkIdent `hty):ident $(mkIdent `hat):ident $(mkIdent `htop):ident $(mkIdent `harg):ident
      $(mkIdent `hcs):ident $(mkIdent `hfit):ident $(mkIdent `hadr):ident
    (try simp (config := { decide := true }) only [Pat.argsOKL, Pat.argsOKLs, Bool.and_eq_true,
      Bool.or_eq_true, decide_eq_true_eq, and_true, true_and, false_or, true_or, or_true,
      Nat.reduceAdd] at $(mkIdent `harg):ident)
    (try simp only [copyShapeOK, sigmaL, Pat.bindsL, Pat.bindssL, Pat.denL, Pat.densL,
      rule_unfold_ds] at $(mkIdent `hcs):ident)
    (try dsimp only [GoFV.Proof.Rules.condHolds, rule_unfold_ds] at $(mkIdent `hcond):ident)
    (try simp only [sigmaL, Pat.bindsL, Pat.bindssL, Pat.denL, Pat.densL, rule_unfold_ds,
      rule_helper, rule_unfold_s] at $(mkIdent `hcond):ident)
    rule_oracle_bool
    rule_cond_bool
    (try simp only [GoFV.Proof.Rules.Pat.argsOK, GoFV.Proof.Rules.Pat.argsOKs,
      GoFV.Proof.Rules.argShapeOk, GoFV.Proof.Rules.isPtrTy_iff, GoFV.Proof.Rules.isInt64Ty_iff,
      GoFV.Proof.Rules.isIntWTy_iff, GoFV.Proof.Rules.isSliceTy_iff, Bool.and_eq_true,
      Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, Nat.reduceEqDiff, reduceIte,
      not_true_eq_false, false_or, true_or, or_true, and_true, true_and, Nat.succ_ne_zero,
      not_false_eq_true] at $(mkIdent `hat):ident))))

/-- Split the shape `T` of the matched value (`e.ty []`, generalized) by `htop`: the cases
`topOKL` rules out close. -/
elab "arm_shape" : tactic => withMainContext do
  let some h := (← getLCtx).findFromUserName? `htop | throwError "arm_shape: no htop"
  let some (_, lhs, _) := (← instantiateMVars h.type).eq? | throwError "arm_shape: htop"
  let t ← Term.exprToSyntax (lhs.getArg! 1)
  let T := mkIdent `T
  let htop := mkIdent `htop
  evalTactic (← `(tactic| (
    generalize $t = $T:ident at *
    rcases $T:ident with (_ | _ | _ | _) | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;>
      (try exact absurd $htop:ident Bool.false_ne_true))))

/-- The semantic normal form of an unfolded rule goal: `opValL` at its ops, their families
(`rule_sem`, `arm_sem`), auxint arithmetic pushed into `BitVec` (`rule_arith`). -/
macro "arm_norm" : tactic => `(tactic| (
  simp (disch := decide) only [opValL_arm, opValL_gen, reduceEvalPure, reduceArmEvalPure,
    rule_sem, rule_arith, arm_sem] at *))

/-- `BlockRuleL.Sound br` (`br` a constant with one control): the structural conjuncts, then one
goal per commutation choice of the control pattern, unfolded, with the hypotheses `hwf`, `hc`,
`hcond`, `hty`, `hat`, `htop`, `harg`, `hb` (`blockAuxOK`), `hai` (the new auxint) and `hbr` (the
old block takes edge `b`). -/
elab "arm_bunfold" : tactic => do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let some r := ty.getAppArgs[0]? | throwError "arm_bunfold: goal is not `BlockRuleL.Sound br`"
  let some rn := r.constName? | throwError "arm_bunfold: rule is not a constant"
  let rid := mkIdent rn
  let nk ← withTransparency .all <| whnf (mkApp (mkConst ``GoFV.Rules.BlockRule.newKind) r)
  let isFirst := nk.isConstOf ``GoFV.SSA.BlockKind.First
  if isFirst then
    evalTactic (← `(tactic| refine ⟨rfl, rfl, _, rfl, rfl, rfl, rfl, fun _ => rfl,
      fun h => absurd rfl h, ?_⟩))
  else
    evalTactic (← `(tactic| refine ⟨rfl, rfl, _, rfl, rfl, rfl, rfl,
      fun h => absurd h (by decide), fun _ => ⟨_, _, rfl, rfl⟩, ?_⟩))
  let pat ← withTransparency .all <| whnf (mkApp (mkConst ``GoFV.Rules.BlockRule.controls) r)
  let some p := (pat.getAppArgs[1]?) | throwError "arm_bunfold: controls"
  let n ← withTransparency .all <| reduce
    (mkApp (mkConst ``GoFV.Opt.RewriteCheck.Pat.commutes) p)
  let some k := n.rawNatLit? <|> n.nat? | throwError "arm_bunfold: commutation count {n}"
  let hsw := mkIdent `hsw
  let hsw' := mkIdent `hsw'
  evalTactic (← `(tactic| (
    intro $(mkIdent `sw):ident $hsw:ident
    simp only [GoFV.Opt.RewriteCheck.Pat.commutes,
      GoFV.Opt.RewriteCheck.Pat.commutess, ite_true, ite_false, Bool.false_eq_true,
      Nat.reduceAdd, GoFV.Opt.RewriteCheck.choices, List.flatMap_cons, List.flatMap_nil,
      List.cons_append, List.nil_append, List.append_nil, List.mem_cons, List.not_mem_nil,
      or_false] at $hsw:ident)))
  for _ in [1:2 ^ k] do
    evalTactic (← `(tactic| all_goals (try (rcases $hsw:ident with $hsw':ident | $hsw:ident <;>
      (try subst $hsw':ident)))))
  evalTactic (← `(tactic| all_goals (try subst $hsw:ident)))
  evalTactic (← `(tactic| all_goals (
    refine ⟨rfl, ?_⟩
    intro $(mkIdent `tabs):ident $(mkIdent `e):ident $(mkIdent `or):ident $(mkIdent `ai):ident
      $(mkIdent `ai'):ident $(mkIdent `hbt):ident
    dsimp only [Pat.swapC, Pat.swapCs, GoFV.Opt.RewriteCheck.swap01, $rid:ident, rule_unfold_ds]
    simp only [Pat.denL, Pat.densL, sigmaL, Pat.bindsL, Pat.bindssL, rule_unfold_ds, rule_helper,
      rule_unfold_s, newAuxL, blockAuxOK]
    intro $(mkIdent `hwf):ident $(mkIdent `hc):ident $(mkIdent `hcond):ident
      $(mkIdent `hty):ident $(mkIdent `hat):ident $(mkIdent `htop):ident $(mkIdent `harg):ident
      $(mkIdent `hb):ident $(mkIdent `hai):ident $(mkIdent `b):ident $(mkIdent `hbr):ident
    (try simp only [Option.some.injEq] at $(mkIdent `hai):ident)
    (try subst $(mkIdent `hai):ident))))

end GoFV.Proof.Low.Rules
