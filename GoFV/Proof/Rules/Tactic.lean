import Lean
import GoFV.Proof.Rules.Lemmas
import GoFV.Proof.Rules.Names

/-!
# Tactics for the rule lemmas (`docs/proofs/rules.md`, "Proof method")

`rule_auto` proves `Rule.Sound r` for a concrete exported rule `r`:

1. `rule_unfold`: reduce the denotation of the rule data (`dsimp`), then the helper names,
   conditions and constants (`simp` with `rule_helper`);
2. split the hypotheses into atoms, drop those about oracle values only, normalise with
   `rule_norm` (`simp_all` with `rule_sem`);
3. case splits: disjunctions, then whether a leaf is an integer of the width its consumer
   reads (the leaf is then replaced by that integer), whether a node's type is an integer of
   another width, `if` conditions;
4. `rule_close`: auxint reads generalized to bounded `Int`s and pushed into `BitVec`, then
   `rfl`, `bv_decide` or `grind`.

`evalPure` and `Op.auxType` are 446-arm `match`es: `simp` never unfolds them (LEARNINGS.md);
the dsimprocs below evaluate them at a constructor (one `delta` + `whnfCore`, a definitional
step for the kernel).
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules
open Lean Meta Elab Tactic

/-- `f op …` with `op` an `Op` constructor: unfold `f` once and reduce its `match`. -/
def reduceAtOp (e : Lean.Expr) : MetaM (Option Lean.Expr) := do
  let some e' ← delta? e | return none
  return some (← whnfCore e')

/-- `evalPure op …` at a constructor `op`: its family's definition. -/
dsimproc reduceEvalPure (evalPure _ _ _ _ _) := fun e => do
  unless e.isAppOfArity ``GoFV.SSA.Sem.evalPure 5 do return .continue
  unless (e.getArg! 0).isConst do return .continue
  match ← reduceAtOp e with
  | some e' => return .done e'
  | none => return .continue

/-- `Op.auxType op` at a constructor `op`. -/
dsimproc reduceAuxType (Op.auxType _) := fun e => do
  unless e.isAppOfArity ``GoFV.SSA.Op.auxType 1 do return .continue
  unless (e.getArg! 0).isConst do return .continue
  match ← reduceAtOp e with
  | some e' => return .done e'
  | none => return .continue

/-- `simp_all` with the semantics simp set: the families become `BitVec`/`Bool` terms, case
facts propagate, `hasTy` facts become type equations. -/
macro "rule_norm" : tactic => `(tactic|
  simp_all (config := { decide := true }) only [rule_sem, rule_helper, or_true, true_or,
    or_false, false_or, and_true, true_and, and_false, false_and, beq_self_eq_true,
    Bool.true_or, Bool.or_true, Bool.false_or, Bool.or_false, Bool.false_and, Bool.and_false,
    Bool.true_and, Bool.and_true, Bool.and_eq_true, Bool.or_eq_true, ne_eq, reduceCtorEq,
    bne_self_eq_false, Bool.false_eq_true, ite_false, ite_true, not_false_eq_true,
    not_true_eq_false, Bool.not_eq_true, Option.some.injEq, Option.getD_some,
    Option.getD_none, List.getD_cons_zero, List.getD_cons_succ, decide_eq_true_eq,
    decide_eq_false_iff_not, beq_iff_eq, bne_iff_ne, Nat.le_refl, Nat.lt_irrefl,
    BitVec.ofInt_ofNat, Nat.reducePow, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceAdd,
    Nat.reduceSub, Nat.reduceMod, GoFV.Rules.wrapTo, GoFV.Rules.GoTy.intInfo?, DV.int.injEq,
    DV.bool.injEq, callE, callH, Bool.cond_true, Bool.cond_false])

/-- Reduce `Rule.Sound r` (`r` a constant) to the semantic statement of its pattern and
result; the hypotheses are `hwf` (checker facts), `hc` (pattern checks), `hcond` (condition),
`hty` (top type). -/
elab "rule_unfold" : tactic => do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let some r := ty.getAppArgs[0]? | throwError "rule_unfold: goal is not `Rule.Sound r`"
  let some rn := r.constName? | throwError "rule_unfold: rule is not a constant"
  let rid := mkIdent rn
  let e := mkIdent `e
  let or := mkIdent `or
  let hwf := mkIdent `hwf
  let hc := mkIdent `hc
  let hcond := mkIdent `hcond
  let hty := mkIdent `hty
  evalTactic (← `(tactic| (
    refine ⟨rfl, ?_⟩
    intro $e:ident $or:ident
    dsimp only [$rid:ident, GoFV.Proof.Rules.Pat.den, GoFV.Proof.Rules.Pat.dens,
      GoFV.Proof.Rules.Pat.raw, GoFV.Proof.Rules.sigma, GoFV.Proof.Rules.Pat.binds,
      GoFV.Proof.Rules.Pat.bindss, GoFV.Proof.Rules.Pat.cons, GoFV.Proof.Rules.Pat.conss,
      GoFV.Proof.Rules.Pat.wf, GoFV.Proof.Rules.Pat.wfs, GoFV.Proof.Rules.auxIntOk,
      GoFV.Proof.Rules.Field.bindDV, GoFV.Proof.Rules.condHolds, GoFV.Proof.Rules.resDen,
      GoFV.Proof.Rules.nodeDen, List.length, List.getElem?_cons_zero, List.getElem?_cons_succ,
      List.map, GoFV.Proof.Rules.reduceEvalPure, GoFV.Proof.Rules.reduceAuxType,
      GoFV.Proof.Rules.evalE, GoFV.Proof.Rules.evalEs, GoFV.Proof.Rules.auxIntDV, List.lookup,
      GoFV.Proof.Rules.toAuxIntD, Option.getD, List.cons_append, List.nil_append,
      GoFV.Proof.Rules.intBin, GoFV.Proof.Rules.binDV, GoFV.Rules.wrapTo,
      GoFV.Rules.GoTy.intInfo?, GoFV.Proof.Rules.litDV, GoFV.Proof.Rules.fieldE,
      GoFV.Proof.Rules.indexE, GoFV.Proof.Rules.convE, GoFV.Proof.Rules.callE,
      GoFV.Proof.Rules.methodE, GoFV.Proof.Rules.builtinE, GoFV.Proof.Rules.unDV,
      GoFV.Proof.Rules.fieldDV, GoFV.Proof.Rules.DV.valOr, GoFV.Proof.Rules.typesShape,
      GoFV.Proof.Rules.shapeSize, Option.map, GoFV.Proof.Rules.exprTy, List.getD,
      List.getD_cons_zero, List.getD_cons_succ, List.zip_cons_cons, List.zip_nil_left,
      List.zip_nil_right, and_true, true_and, Nat.reduceAdd, Nat.reduceBEq, Nat.reduceBNe,
      reduceIte]
    simp only [rule_helper, GoFV.Proof.Rules.callH, GoFV.Proof.Rules.binE_land_bool,
      GoFV.Proof.Rules.binE_lor_bool, GoFV.Proof.Rules.binE_eq, GoFV.Proof.Rules.binE_ne,
      GoFV.Proof.Rules.binE_lt, GoFV.Proof.Rules.binE_le, GoFV.Proof.Rules.binE_gt,
      GoFV.Proof.Rules.binE_ge, GoFV.Proof.Rules.binE_add, GoFV.Proof.Rules.binE_sub,
      GoFV.Proof.Rules.binE_mul, GoFV.Proof.Rules.binE_quo, GoFV.Proof.Rules.binE_rem,
      GoFV.Proof.Rules.binE_and, GoFV.Proof.Rules.binE_or, GoFV.Proof.Rules.binE_xor,
      GoFV.Proof.Rules.binE_shl, GoFV.Proof.Rules.binE_shr, GoFV.Proof.Rules.binE_andNot,
      GoFV.Proof.Rules.dv_ite_land, GoFV.Proof.Rules.dv_ite_lor, GoFV.Proof.Rules.dv_land_true,
      GoFV.Proof.Rules.dv_lor_true, GoFV.Proof.Rules.DV.bool.injEq, Bool.and_eq_true,
      Bool.or_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, GoFV.Proof.Rules.binDV,
      GoFV.Proof.Rules.intBin, GoFV.Proof.Rules.fieldDV, Option.map_some, Option.map_none,
      Option.getD_some, Option.getD_none, reduceCtorEq, true_or, or_true, and_true, true_and,
      beq_self_eq_true, Bool.cond_false, Bool.cond_true, GoFV.Rules.wrapTo,
      GoFV.Rules.GoTy.intInfo?]
    intro $hwf:ident $hc:ident $hcond:ident $hty:ident)))

/-- A term to case on: `Val.asInt w l`, `Val.asBool l`, `Val.asNat l` of a pattern leaf `l`
(`PEnv.leaf e p`), `tyOtherInt t w`, or the condition of an `if`. -/
def splitCandidate? (e : Lean.Expr) : Option Lean.Expr :=
  e.find? fun t =>
    (t.isAppOfArity ``GoFV.SSA.Sem.Val.asInt 2 && (t.getArg! 1).isAppOfArity ``PEnv.leaf 2) ||
    (t.isAppOfArity ``GoFV.SSA.Sem.Val.asBool 1 && (t.getArg! 0).isAppOfArity ``PEnv.leaf 2) ||
    (t.isAppOfArity ``GoFV.SSA.Sem.Val.asNat 1 && (t.getArg! 0).isAppOfArity ``PEnv.leaf 2) ||
    (t.isAppOfArity ``tyOtherInt 2 && !(t.getArg! 0).hasLooseBVars) ||
    (t.isAppOfArity ``ite 5 && !(t.getArg! 1).hasLooseBVars)

/-- Case split on a disjunction among the hypotheses (the checker's `Bool` auxints, `||` in
conditions), then `rule_norm`. -/
elab "rule_split_or" : tactic => withMainContext do
  for h in ← getLCtx do
    if !h.isImplementationDetail && (← instantiateMVars h.type).isAppOfArity ``Or 2 then
      let hs ← Term.exprToSyntax h.toExpr
      evalTactic (← `(tactic| (rcases $hs:term with hor | hor <;> (try rule_norm))))
      return
  throwError "rule_split_or: no disjunction"

/-- One case split on a `splitCandidate?` of the goal or a hypothesis, followed by `rule_norm`
in every case. A leaf read as an integer (a boolean) is replaced by it. -/
elab "rule_split1" : tactic => withMainContext do
  let g ← getMainGoal
  let mut cand := splitCandidate? (← instantiateMVars (← g.getType))
  for h in ← getLCtx do
    if cand.isNone && !h.isImplementationDetail then
      let ty ← instantiateMVars h.type
      -- skip the equations of earlier splits (`c = none`, `c = true`, …)
      let isSplitEq := match ty.eq? with
        | some (_, lhs, rhs) => (splitCandidate? lhs).isSome && !(rhs.find? (fun t =>
            t.isAppOfArity ``PEnv.leaf 2)).isSome
        | none => false
      unless isSplitEq do
        cand := splitCandidate? ty
  if cand.isNone then
    for h in ← getLCtx do
      if cand.isNone && !h.isImplementationDetail then
        if (← instantiateMVars h.type).isAppOfArity ``Or 2 then
          let hs ← Term.exprToSyntax h.toExpr
          evalTactic (← `(tactic| (rcases $hs:term with hor | hor <;> (try rule_norm))))
          return
  let some c := cand | throwError "rule_split1: nothing to split"
  if c.isAppOfArity ``ite 5 then
    let p ← Term.exprToSyntax (c.getArg! 1)
    evalTactic (← `(tactic| (by_cases hif : $p <;> (try rule_norm))))
    return
  let stx ← Term.exprToSyntax c
  if c.isAppOfArity ``GoFV.SSA.Sem.Val.asInt 2 then
    evalTactic (← `(tactic| (
      rcases hsplit : $stx with _ | xs <;>
        (try have hv := val_asInt_eq_some.mp hsplit) <;> (try rule_norm))))
  else if c.isAppOfArity ``GoFV.SSA.Sem.Val.asBool 1 then
    evalTactic (← `(tactic| (
      rcases hsplit : $stx with _ | xs <;>
        (try have hv := val_asBool_eq_some.mp hsplit) <;> (try rule_norm))))
  else
    evalTactic (← `(tactic| (rcases hsplit : $stx with _ | xs <;> (try rule_norm))))

/-- An auxint read of the instance to generalize: `wrapInt k s (auxInt p).toInt`, a remaining
`(auxInt p).toInt`, or `auxInt p != 0`. -/
def genCandidate? (e : Lean.Expr) : Option Lean.Expr :=
  let isAux (t : Lean.Expr) := t.isAppOfArity ``PEnv.auxInt 2 && !t.hasLooseBVars
  let isToInt (t : Lean.Expr) := t.isAppOfArity ``Int64.toInt 1 && isAux (t.getArg! 0)
  (e.find? fun t => t.isAppOfArity ``GoFV.Rules.wrapInt 3 && isToInt (t.getArg! 2)) <|>
  (e.find? isToInt) <|>
  (e.find? fun t => t.isAppOfArity ``bne 4 && isAux (t.getArg! 2))

/-- Generalize one auxint read (with its range) in the goal and all hypotheses. -/
elab "rule_gen1" : tactic => withMainContext do
  let g ← getMainGoal
  let mut cand := genCandidate? (← instantiateMVars (← g.getType))
  for h in ← getLCtx do
    if cand.isNone && !h.isImplementationDetail then
      cand := genCandidate? (← instantiateMVars h.type)
  let some c := cand | throwError "rule_gen1: nothing to generalize"
  let stx ← Term.exprToSyntax c
  if c.isAppOfArity ``GoFV.Rules.wrapInt 3 then
    let w ← Term.exprToSyntax (c.getArg! 0)
    let x ← Term.exprToSyntax (c.getArg! 2)
    if (c.getArg! 1).isConstOf ``Bool.true then
      evalTactic (← `(tactic| have hrange := wrapInt_true_range $w $x))
    else
      evalTactic (← `(tactic| have hrange := wrapInt_false_range $w $x))
    evalTactic (← `(tactic| generalize $stx = cg at *))
  else if c.isAppOfArity ``Int64.toInt 1 then
    let a ← Term.exprToSyntax (c.getArg! 0)
    evalTactic (← `(tactic| have hrange := int64_toInt_range $a))
    evalTactic (← `(tactic| generalize $stx = cg at *))
  else
    evalTactic (← `(tactic| generalize $stx = cg at *))

/-- Clear hypotheses about oracle values only (conditions such as `x.Uses == 1`,
`clobber(x)`, `x.Op != OpConst64`): they say nothing about the instance. -/
elab "rule_clear_oracle" : tactic => withMainContext do
  let mut g ← getMainGoal
  for h in ← getLCtx do
    if h.isImplementationDetail then continue
    let ty ← instantiateMVars h.type
    let mentionsOracle := (ty.find? fun t => t.isAppOf ``Oracle.dv).isSome
    let mentionsInst := (ty.find? fun t => t.isAppOf ``PEnv.leaf || t.isAppOf ``PEnv.auxInt ||
      t.isAppOf ``PEnv.ty).isSome
    if mentionsOracle && !mentionsInst then
      g ← g.clear h.fvarId
  replaceMainGoal [g]

/-- Split every conjunction among the hypotheses. -/
elab "rule_ands" : tactic => withMainContext do
  replaceMainGoal [← (← getMainGoal).casesAnd]

/-- Give every `BitVec (Width.bits .wN)` local its literal width (`bv_decide` needs literal
widths). -/
elab "rule_widths" : tactic => withMainContext do
  let mut g ← getMainGoal
  for h in ← getLCtx do
    if h.isImplementationDetail then continue
    let ty ← instantiateMVars h.type
    if ty.isAppOfArity ``BitVec 1 && (ty.getArg! 0).isAppOfArity ``GoFV.SSA.Sem.Width.bits 1 then
      let some k ← (Meta.evalNat (← whnf (ty.getArg! 0))).run | continue
      g ← g.changeLocalDecl h.fvarId (mkApp (mkConst ``BitVec) (mkNatLit k))
  replaceMainGoal [g]

/-- Close the arithmetic left after the splits: auxint reads are generalized, constants
pushed into `BitVec`, then `rfl`, `bv_decide` or `grind`. -/
macro "rule_close" : tactic => `(tactic| (
  repeat rule_gen1
  try simp only [GoFV.Proof.Rules.DV.int.injEq, GoFV.Proof.Rules.DV.bool.injEq] at *
  try rule_ands
  try subst_vars
  try rule_norm
  try simp_all only [rule_arith, Nat.min_def, Nat.reduceLeDiff, Nat.reducePow, Nat.reduceLT,
    ite_true, ite_false, BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_neg,
    BitVec.ofInt_ofNat, Nat.le_refl, GoFV.SSA.Sem.Width.bits, GoFV.Proof.Rules.DV.int.injEq,
    GoFV.Proof.Rules.DV.bool.injEq]
  first
  | done
  | with_reducible rfl
  | bv_decide (config := { enums := false, structures := false })
  | grind))

/-- `rule_unfold`, the case splits, then `rule_close` on every remaining case. -/
macro "rule_auto" : tactic => `(tactic| (
  rule_unfold
  (try rule_ands)
  (try rule_clear_oracle)
  (try rule_norm)
  (try rule_ands)
  all_goals (repeat rule_split_or)
  all_goals (repeat rule_split1)
  all_goals (try rule_widths)
  all_goals rule_close))

end GoFV.Proof.Rules
