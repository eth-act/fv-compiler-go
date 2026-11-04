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
3. case splits: whether a leaf is an integer of the width its consumer reads (the leaf is
   then replaced by that integer), whether a node's type is an integer of another width, `if`
   conditions, and when none is left the disjunctions (splitting these last keeps the shared
   part of the proof once: 31% smaller proofs of the rotate rules);
4. `rule_close`: auxint reads generalized to bounded `Int`s and pushed into `BitVec`, then
   `rfl`, a rotation (`rule_rot`), `grind`, a per-bit identity, `bv_normalize`; never
   `bv_decide` (its `_native` axioms fail `scripts/axioms-audit.sh`): such a goal fails.

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

/-- `GoTy.intInfo? t` at a constructor `t`. Unfolding it by `simp` instead generates its
wildcard `match` equations and splitter in every rule module (~5000 terms, 0.2 MB of
`.olean` per module). -/
dsimproc reduceIntInfo (GoTy.intInfo? _) := fun e => do
  unless e.isAppOfArity ``GoFV.Rules.GoTy.intInfo? 1 do return .continue
  let some c := (e.getArg! 0).getAppFn.constName? | return .continue
  unless (← getEnv).isConstructor c do return .continue
  match ← reduceAtOp e with
  | some e' => return .done e'
  | none => return .continue

/-- `callH e h args` at a helper constructor `h` whose argument list is concrete enough to
select an arm: that arm. Unfolding `callH` by `simp` instead meets it on an undecided argument,
unfolds it to its 26-arm `match` and generates that `match`'s equations and splitter in every
rule module (`callH.match_5.eq_24`, 2.9 MB of `.olean`). -/
dsimproc reduceCallH (callH _ _ _) := fun e => do
  unless e.isAppOfArity ``callH 3 do return .continue
  let some c := (e.getArg! 1).getAppFn.constName? | return .continue
  unless (← getEnv).isConstructor c do return .continue
  let some e1 ← delta? e | return .continue
  let e1 := e1.headBeta
  let some m := e1.getAppFn.constName? | return .continue
  let e2 ← whnfCore e1
  if e2.getAppFn.constName? == some m then return .continue
  return .done e2

/-! The lemma lists of the tactics, as simp sets (`Attr.lean`). -/

attribute [rule_norm_s] or_true true_or or_false false_or and_true true_and and_false false_and
  beq_self_eq_true Bool.true_or Bool.or_true Bool.false_or Bool.or_false Bool.false_and
  Bool.and_false Bool.true_and Bool.and_true Bool.and_eq_true Bool.or_eq_true ne_eq reduceCtorEq
  bne_self_eq_false Bool.false_eq_true ite_false ite_true not_false_eq_true not_true_eq_false
  Bool.not_eq_true Option.some.injEq Option.getD_some Option.getD_none List.getD_cons_zero
  List.getD_cons_succ decide_eq_true_eq decide_eq_false_iff_not beq_iff_eq bne_iff_ne Nat.le_refl
  Nat.lt_irrefl BitVec.ofInt_ofNat Nat.reducePow Nat.reduceLT Nat.reduceLeDiff Nat.reduceAdd
  Nat.reduceSub Nat.reduceMod GoFV.Rules.wrapTo GoFV.Proof.Rules.reduceIntInfo DV.int.injEq
  DV.bool.injEq callE reduceCallH Bool.cond_true Bool.cond_false Option.map_some

attribute [rule_unfold_ds] GoFV.Proof.Rules.Pat.den GoFV.Proof.Rules.Pat.dens
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

attribute [rule_unfold_s] GoFV.Proof.Rules.reduceCallH Option.isSome_some ite_true ite_false
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
  GoFV.Proof.Rules.fieldDV Option.map_some Option.map_none Option.getD_some Option.getD_none
  reduceCtorEq true_or or_true and_true true_and beq_self_eq_true Bool.cond_false Bool.cond_true
  GoFV.Rules.wrapTo GoFV.Proof.Rules.reduceIntInfo

attribute [rule_close_s] GoFV.Proof.Rules.reduceIntInfo Option.getD_some Nat.reduceLeDiff Nat.reducePow Nat.reduceLT ite_true ite_false
  BitVec.ofInt_add BitVec.ofInt_mul BitVec.ofInt_neg BitVec.ofInt_ofNat Nat.le_refl
  GoFV.SSA.Sem.Width.bits GoFV.Proof.Rules.DV.int.injEq GoFV.Proof.Rules.DV.bool.injEq

/-- `simp_all` with the semantics simp set: the families become `BitVec`/`Bool` terms, case
facts propagate, `hasTy` facts become type equations. `decide := true` only under the option
`gofv.ruleNorm.decide` (`rule_auto`'s fallback): it evaluates a `Decidable` instance at every
proposition, most of them stuck on leaf reads (`e.ty p`), 10–15% of a rule module's time. What
it decided in most proofs were `Int` literal (in)equations (`if 8 == 0`), which the four `Int`
simprocs decide. -/
elab "rule_norm" : tactic => do
  if gofv.ruleNorm.decide.get (← getOptions) then
    evalTactic (← `(tactic|
      simp_all (config := { decide := true }) only [rule_sem, rule_helper, rule_norm_s]))
  else
    evalTactic (← `(tactic|
      simp_all only [rule_sem, rule_helper, rule_norm_s, Int.reduceEq, Int.reduceNe,
        Int.reduceBEq, Int.reduceBNe]))

/-- The subterms of `e` satisfying `p`, each once. -/
partial def subtermsWith (p : Lean.Expr → Bool) (e : Lean.Expr) : Array Lean.Expr :=
  (go e).run #[] |>.2
where
  go (e : Lean.Expr) : StateM (Array Lean.Expr) Unit := do
    if p e && !(← get).contains e then modify (·.push e)
    match e with
    | .app f a => go f; go a
    | .lam _ d b _ | .forallE _ d b _ => go d; go b
    | .letE _ t v b _ => go t; go v; go b
    | .mdata _ b | .proj _ _ b => go b
    | _ => pure ()

/-- Every oracle answer `or.dv X` in the condition `hcond` with `X` of Go type `bool` is a
boolean (`Oracle.BoolTyped`, hypothesis `hbt`): replaced by a fresh `Bool`, so that `&&`/`||`
with an oracle atom evaluate. -/
elab "rule_oracle_bool" : tactic => withMainContext do
  let some hbt := (← getLCtx).findFromUserName? `hbt | return
  let some hc := (← getLCtx).findFromUserName? `hcond | return
  let ty ← instantiateMVars hc.type
  let atoms := subtermsWith (fun t => t.isAppOfArity ``Oracle.dv 2 &&
    !(t.getArg! 1).hasFVar && !t.hasLooseBVars && !(t.getArg! 1).hasMVar) ty
  let hbs ← Term.exprToSyntax hbt.toExpr
  let hcs := mkIdent `hcond
  for a in atoms do
    let tyE := mkApp2 (mkConst ``exprTy) (← mkListLit (mkConst ``GoFV.Rules.GoTy) []) (a.getArg! 1)
    unless ← withNewMCtxDepth (isDefEq tyE (mkConst ``GoFV.Rules.GoTy.bool)) do continue
    let x ← Term.exprToSyntax (a.getArg! 1)
    let saved ← saveState
    try
      evalTactic (← `(tactic| (
        obtain ⟨_, hbo⟩ := $hbs $x (by rfl)
        simp only [hbo] at $hcs:ident
        clear hbo)))
    catch _ => saved.restore

/-- A comparison in the condition `hcond` that does not evaluate to a boolean literal (of an
oracle answer: `x.Op != OpConst64`, `div.Uses == 1`) is still a boolean (`binDV_cmp_bool`: a
comparison or the `bool` oracle's answer, `(binDV o t X Y).getD (.bool w)`). It is replaced by
a fresh `Bool`, so that `&&`/`||` around it evaluate. Not a comparison that reads instance
fields (`c.Type.Size() == 8`): it evaluates after the case splits, and replacing it would lose
its value. -/
elab "rule_cond_bool" : tactic => withMainContext do
  let hcs := mkIdent `hcond
  let mut tried : Array Lean.Expr := #[]
  for _ in [0:16] do
    let some hc := (← getLCtx).findFromUserName? `hcond | return
    let ty ← instantiateMVars hc.type
    -- `Option.getD (binDV …) (DV.bool w)` with `binDV` stuck, unfolded by `rule_unfold_ds`
    let cands := subtermsWith (fun t => t.isAppOfArity ``Option.getD.match_1 5 &&
      !t.hasLooseBVars && !tried.contains t &&
      (match t.getArg! 4 with
       | .lam _ _ b _ => b.isAppOfArity ``DV.bool 1
       | _ => false) &&
      ((t.getArg! 2).getAppFn.constName?.any fun n => n != ``DV.bool)) ty
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
              GoFV.Proof.Rules.binDV_cmp_bool (o := $(mkIdent o)) (by decide) .bool _ _ _
            simp only [hab, rule_unfold_s] at $hcs:ident
            clear hab)))
          pure true
        catch _ => saved.restore; pure false
      if ok then break

/-- The ops whose arguments `argShapeOk` constrains. -/
def argShapeOps : List Name :=
  [``Op.OffPtr, ``Op.AddPtr, ``Op.PtrIndex, ``Op.EqPtr, ``Op.NeqPtr, ``Op.IsNonNil, ``Op.Convert,
   ``Op.IsInBounds, ``Op.IsSliceInBounds, ``Op.Slicemask, ``Op.EqInter, ``Op.NeqInter,
   ``Op.SlicePtr, ``Op.SliceLen, ``Op.SliceCap,
   ``Op.Add64F, ``Op.Sub64F, ``Op.Mul64F, ``Op.Div64F, ``Op.Neg64F, ``Op.Min64F, ``Op.Max64F,
   ``Op.Eq64F, ``Op.Neq64F, ``Op.Less64F, ``Op.Leq64F, ``Op.Abs, ``Op.Copysign, ``Op.Sqrt,
   ``Op.Floor, ``Op.Ceil, ``Op.Trunc, ``Op.Round, ``Op.RoundToEven, ``Op.FMA, ``Op.Round64F,
   ``Op.Add32F, ``Op.Sub32F, ``Op.Mul32F, ``Op.Div32F, ``Op.Neg32F, ``Op.Min32F, ``Op.Max32F,
   ``Op.Eq32F, ``Op.Neq32F, ``Op.Less32F, ``Op.Leq32F, ``Op.Sqrt32, ``Op.Round32F]

/-- The comparisons whose arguments `argShapeOk` constrains to their width. `rule_unfold`
clears their argument shapes (no proof it closes needs them); `rule_unfold_getd` keeps them. -/
def eqShapeOps : List Name :=
  [``Op.Eq8, ``Op.Eq16, ``Op.Eq32, ``Op.Eq64, ``Op.Neq8, ``Op.Neq16, ``Op.Neq32, ``Op.Neq64]

/-- The hypothesis `hnn` (`Pat.nonNegOK`) of `rule_unfold`: reduced to `(e.leaf p).nonNeg =
true` for each `isNonNegative(x)` conjunct if the rule's condition has one, else cleared. -/
def ruleNonNeg (ci : ConstantInfo) : TacticM Unit := do
  let hnn := mkIdent `hnn
  let usesNonNeg := ci.value?.any fun v =>
    (v.find? fun t => t matches .lit (.strVal "isNonNegative")).isSome
  if usesNonNeg then
    evalTactic (← `(tactic| simp only [GoFV.Proof.Rules.Pat.nonNegOK,
      GoFV.Proof.Rules.nonNegVars, GoFV.Proof.Rules.Pat.leafPos, GoFV.Proof.Rules.Pat.leafPoss,
      String.reduceBEq, beq_self_eq_true, Nat.reduceBEq, reduceIte, List.nil_append,
      List.cons_append, List.all_cons, List.all_nil, Option.orElse_some, Option.orElse_none,
      Bool.and_true] at $hnn:ident))
  else
    evalTactic (← `(tactic| clear $hnn:ident))

/-- Reduce `Rule.Sound r` (`r` a constant) to the semantic statement of its pattern and
result; the hypotheses are `hbt` (`Oracle.BoolTyped`), `hwf` (checker facts), `hc` (pattern
checks), `hcond` (condition, its `bool` oracle atoms replaced by booleans,
`rule_oracle_bool`, `rule_cond_bool`), `hty` (top type), `hlt` (leaf types), `hat` (argument
shapes, `Pat.argsOK`: reduced to type equations if the pattern has an op `argShapeOk`
constrains, else cleared). The condition is
evaluated after the intros: evaluated in the same `dsimp` as the rest, the kernel's check of
the resulting cast hits "deep recursion" on conditions with several helper calls
(`divmod.rules:159`, `:180`). -/
elab "rule_unfold" : tactic => do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let some r := ty.getAppArgs[0]? | throwError "rule_unfold: goal is not `Rule.Sound r`"
  let some rn := r.constName? | throwError "rule_unfold: rule is not a constant"
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
  let some ci := (← getEnv).find? rn | throwError "rule_unfold: unknown rule"
  let usesArgShape := ci.value?.any fun v =>
    (v.find? fun t => argShapeOps.any t.isConstOf).isSome
  evalTactic (← `(tactic| (
    refine ⟨rfl, ?_⟩
    intro $e:ident $or:ident $hbt:ident
    dsimp only [$rid:ident, rule_unfold_ds]
    simp only [rule_helper, rule_unfold_s]
    intro $hwf:ident $hc:ident $hcond:ident $hty:ident $hlt:ident $hat:ident $(mkIdent `hnn):ident
    (try dsimp only [GoFV.Proof.Rules.condHolds, rule_unfold_ds] at $hcond:ident)
    (try simp only [rule_helper, rule_unfold_s] at $hcond:ident)
    rule_oracle_bool
    rule_cond_bool)))
  if usesArgShape then
    evalTactic (← `(tactic| try simp only [GoFV.Proof.Rules.Pat.argsOK, GoFV.Proof.Rules.Pat.argsOKs,
      GoFV.Proof.Rules.argShapeOk, GoFV.Proof.Rules.isPtrTy_iff, GoFV.Proof.Rules.isInt64Ty_iff,
      GoFV.Proof.Rules.isIntWTy_iff, GoFV.Proof.Rules.isSliceTy_iff,
      GoFV.Proof.Rules.convArgOk, GoFV.Proof.Rules.ifaceArgOk, Bool.and_eq_true, Bool.or_eq_true,
      bne_iff_ne, ne_eq,
      beq_iff_eq, Nat.reduceEqDiff, reduceIte, not_true_eq_false, false_or, true_or, or_true,
      and_true, true_and, Nat.succ_ne_zero, not_false_eq_true] at $hat:ident))
  else
    evalTactic (← `(tactic| clear $hat:ident))
  ruleNonNeg ci

/-- A term to case on: `Val.asInt w l`, `Val.asBool l`, `Val.asNat l` of a pattern leaf `l`
(`PEnv.leaf e p`), `tyOtherInt t w`, the condition of an `if`, or `Val.asInt w l` for a leaf
typed `Ty.int w` (`Pat.typed`). -/
def splitCandidate? (e : Lean.Expr) : Option Lean.Expr :=
  (e.find? fun t =>
    (t.isAppOfArity ``GoFV.SSA.Sem.Val.asInt 2 && (t.getArg! 1).isAppOfArity ``PEnv.leaf 2) ||
    (t.isAppOfArity ``GoFV.SSA.Sem.Val.asBool 1 && (t.getArg! 0).isAppOfArity ``PEnv.leaf 2) ||
    (t.isAppOfArity ``GoFV.SSA.Sem.Val.asNat 1 && (t.getArg! 0).isAppOfArity ``PEnv.leaf 2) ||
    (t.isAppOfArity ``tyOtherInt 2 && !(t.getArg! 0).hasLooseBVars) ||
    (t.isAppOfArity ``ite 5 && !(t.getArg! 1).hasLooseBVars)) <|>
  ((e.find? fun t => t.isAppOfArity ``GoFV.SSA.Sem.Val.hasTy 2 &&
      (t.getArg! 0).isAppOfArity ``PEnv.leaf 2 &&
      (t.getArg! 1).isAppOfArity ``GoFV.SSA.Sem.Ty.int 1 && !t.hasLooseBVars).map fun t =>
    mkApp2 (mkConst ``GoFV.SSA.Sem.Val.asInt) ((t.getArg! 1).getArg! 0) (t.getArg! 0))

/-- Case split on a disjunction among the hypotheses (the checker's `Bool` auxints, `||` in
conditions), then `rule_norm`. -/
elab "rule_split_or" : tactic => withMainContext do
  for h in ← getLCtx do
    if !h.isImplementationDetail && (← instantiateMVars h.type).isAppOfArity ``Or 2 then
      let hs ← Term.exprToSyntax h.toExpr
      evalTactic (← `(tactic| (rcases $hs:term with hor | hor <;> (try rule_norm))))
      return
  throwError "rule_split_or: no disjunction"

syntax "rule_split1" : tactic

/-- Case split on the shape `t` of a 64-bit integer leaf (`tyOtherInt t .w64 = false`: the
64-bit integer shape or a pointer shape, `tyOtherInt_w64_eq_false`) when the condition reads
`t` (`t.Size()`), then `rule_norm` and the further splits of `rule_split1` in both cases (the
pointer case is new with §3.3's pointer words; the caller's `repeat rule_split1` follows the
first goal only). -/
syntax "rule_split_ptr_or" : tactic

elab_rules : tactic
  | `(tactic| rule_split_ptr_or) => withMainContext do
    let some hc := (← getLCtx).findFromUserName? `hcond
      | throwError "rule_split_ptr_or: no condition"
    let cty ← instantiateMVars hc.type
    for h in ← getLCtx do
      if h.isImplementationDetail then continue
      let some (_, lhs, rhs) := (← instantiateMVars h.type).eq? | continue
      unless lhs.isAppOfArity ``tyOtherInt 2 && rhs.isConstOf ``Bool.false &&
          (lhs.getArg! 1).isConstOf ``GoFV.SSA.Sem.Width.w64 do continue
      let t := lhs.getArg! 0
      unless t.isAppOfArity ``PEnv.ty 2 && (cty.find? (· == t)).isSome do continue
      let ts ← Term.exprToSyntax t
      let hs ← Term.exprToSyntax h.toExpr
      evalTactic (← `(tactic| (
        rcases (GoFV.Proof.Rules.tyOtherInt_w64_eq_false $ts).1 $hs with hor | ⟨_, hor⟩ <;>
          (try rule_norm) <;> (try rule_split_ptr_or) <;> (repeat rule_split1))))
      return
    throwError "rule_split_ptr_or: no 64-bit leaf shape read by the condition"

/-- One case split on a `splitCandidate?` of the goal or a hypothesis, followed by `rule_norm`
in every case. A leaf read as an integer (a boolean) is replaced by it. -/
elab_rules : tactic | `(tactic| rule_split1) => withMainContext do
  let g ← getMainGoal
  let mut cand := splitCandidate? (← instantiateMVars (← g.getType))
  for h in ← getLCtx do
    if cand.isNone && !h.isImplementationDetail then
      let ty ← instantiateMVars h.type
      -- skip the equations of earlier splits (`c = none`, `c = true`, …), not a leaf's type
      let isSplitEq := match ty.eq? with
        | some (_, lhs, rhs) => (splitCandidate? lhs).isSome && !(rhs.find? (fun t =>
            t.isAppOfArity ``PEnv.leaf 2)).isSome &&
            !(lhs.isAppOfArity ``GoFV.SSA.Sem.Val.hasTy 2 &&
              (lhs.getArg! 0).isAppOfArity ``PEnv.leaf 2)
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
        (try have hv := val_asInt_eq_some.mp hsplit) <;>
        (try (have hv0 := val_poison_of_asInt_none hsplit (by with_reducible assumption)) <;>
          rcases hv0 with hv | ⟨hw64, pv, hv⟩) <;>
        (try rule_norm) <;> (try rule_split_ptr_or))))
  else if c.isAppOfArity ``GoFV.SSA.Sem.Val.asBool 1 then
    evalTactic (← `(tactic| (
      rcases hsplit : $stx with _ | xs <;>
        (try have hv := val_asBool_eq_some.mp hsplit) <;> (try rule_norm))))
  else if c.isAppOfArity ``GoFV.SSA.Sem.Val.asNat 1 then
    -- a rotation amount: the leaf is an integer of one of the four widths (its type then
    -- follows from `Pat.typed`) or not an amount
    let l ← Term.exprToSyntax (c.getArg! 0)
    evalTactic (← `(tactic| (
      rcases GoFV.Proof.Rules.val_asNat_cases $l with hsplit | ⟨(_ | _ | _ | _), xs, hv⟩ <;>
        (try rule_norm) <;> (try rule_split_ptr_or))))
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
    -- the same auxint read unwrapped elsewhere (`int32(c)` next to `c`): keep the equation
    let inner := c.getArg! 2
    let mut ts := #[← instantiateMVars (← g.getType)]
    for h in ← getLCtx do
      if !h.isImplementationDetail then ts := ts.push (← instantiateMVars h.type)
    let bare := ts.any fun t =>
      ((t.replace fun s => if s == c then some (mkConst ``True) else none).find?
        (· == inner)).isSome
    if bare then
      evalTactic (← `(tactic| generalize hgen : $stx = cg at *))
    else
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

/-- A rotation written as a sum, `or` or `xor` of two shifts of the same value: by `y` and
`w - y` (`rot_add_sub` …; the bound `y ≤ w` by `bv_omega` from the bounded shift), or by
amounts that add up to the width (`rot_add` …). -/
macro "rule_rot" : tactic => `(tactic| (
  first
  | rw [GoFV.Proof.Rules.rot_add_sub] | rw [GoFV.Proof.Rules.rot_add_sub']
  | rw [GoFV.Proof.Rules.rot_or_sub] | rw [GoFV.Proof.Rules.rot_or_sub']
  | rw [GoFV.Proof.Rules.rot_xor_sub] | rw [GoFV.Proof.Rules.rot_xor_sub']
  | rw [GoFV.Proof.Rules.rot_add] | rw [GoFV.Proof.Rules.rot_add']
  | rw [GoFV.Proof.Rules.rot_or] | rw [GoFV.Proof.Rules.rot_or']
  | rw [GoFV.Proof.Rules.rot_xor] | rw [GoFV.Proof.Rules.rot_xor']
  all_goals first
    | with_reducible rfl
    | decide
    | (apply GoFV.Proof.Rules.rotateLeft_congr; bv_omega)
    | bv_omega))

/-- `subst_vars` restricted to equations with a local on one side, found syntactically:
`subst_vars` puts both sides of every equation into `whnf`, which evaluates a condition such as
`bitwise int16 (· &&& ·) c 15 = 15` down to `2 ^ 64` and exceeds the recursion depth. -/
partial def substLocals (g : MVarId) : MetaM MVarId := g.withContext do
  for h in ← getLCtx do
    if h.isImplementationDetail then continue
    let some (_, l, r) := (← instantiateMVars h.type).eq? | continue
    for (side, other, symm) in [(r, l, true), (l, r, false)] do
      if side.isFVar && !other.containsFVar side.fvarId! then
        if let some (_, g') ← substCore? g h.fvarId (symm := symm) (tryToSkip := true) then
          return ← substLocals g'
  return g

elab "rule_subst" : tactic => do
  replaceMainGoal [← substLocals (← getMainGoal)]

/-- The atoms `omega` cannot see into, with their facts as hypotheses: for `a &&& b` on `Nat`
its bounds and, where `omega` proves that one side's low `k` bits are all ones or all zeros,
its remainder by `m = 2 ^ k` (`m` the first power-of-two modulus of the goal); `Int.tmod` by
its sign cases (`tmod_facts`). -/
elab "rule_omega_facts" : tactic => withMainContext do
  let mut ts : Array Lean.Expr := #[← instantiateMVars (← getMainTarget)]
  for h in ← getLCtx do
    if !h.isImplementationDetail then ts := ts.push (← instantiateMVars h.type)
  let isNatAnd (s : Lean.Expr) := s.isAppOfArity ``HAnd.hAnd 6 && (s.getArg! 0).isConstOf ``Nat
  let isTmod (s : Lean.Expr) := s.isAppOfArity ``Int.tmod 2
  let isUshrToNat (s : Lean.Expr) := s.isAppOfArity ``BitVec.toNat 2 &&
    (s.getArg! 1).isAppOfArity ``HShiftRight.hShiftRight 6 &&
    ((s.getArg! 1).getArg! 1).isConstOf ``Nat
  let isMod (s : Lean.Expr) := s.isAppOfArity ``HMod.hMod 6 && (s.getArg! 0).isConstOf ``Nat &&
    ((s.getArg! 5).rawNatLit? <|> (s.getArg! 5).nat?).any (fun m => m > 1 && m == 2 ^ m.log2)
  let modulus : Option Nat := (subtermsWith isMod ts[0]!)[0]?.bind fun s =>
    (s.getArg! 5).rawNatLit? <|> (s.getArg! 5).nat?
  let mut ands : Array Lean.Expr := #[]
  let mut tmods : Array Lean.Expr := #[]
  for t in ts do
    for s in subtermsWith isNatAnd t do
      unless ands.contains s do ands := ands.push s
    for s in subtermsWith isTmod t do
      unless tmods.contains s do tmods := tmods.push s
  for s in ands do
    let a ← Term.exprToSyntax (s.getArg! 4)
    let b ← Term.exprToSyntax (s.getArg! 5)
    evalTactic (← `(tactic| have := GoFV.Proof.Rules.nat_and_le $a $b))
  for s in tmods do
    let a ← Term.exprToSyntax (s.getArg! 0)
    let b ← Term.exprToSyntax (s.getArg! 1)
    evalTactic (← `(tactic| have := GoFV.Proof.Rules.tmod_facts $a $b))
  let mut ushrs : Array Lean.Expr := #[]
  for t in ts do
    for s in subtermsWith isUshrToNat t do
      unless ushrs.contains s do ushrs := ushrs.push s
  for s in ushrs do
    let x ← Term.exprToSyntax ((s.getArg! 1).getArg! 4)
    let n ← Term.exprToSyntax ((s.getArg! 1).getArg! 5)
    evalTactic (← `(tactic| have := GoFV.Proof.Rules.ushr_toNat_facts $x $n))
  -- Two rounds: a fact about one atom (a condition `c & 15 == 15`) may be needed to derive
  -- the fact about another (the amount `y &&& c`).
  if let some m := modulus then
    let ml := Syntax.mkNumLit (toString m)
    let kl := Syntax.mkNumLit (toString m.log2)
    let mut done : Array (Lean.Expr × Name) := #[]
    for _ in [0:2] do
      for s in ands do
        let a ← Term.exprToSyntax (s.getArg! 4)
        let b ← Term.exprToSyntax (s.getArg! 5)
        for lem in [``nat_and_ones_r, ``nat_and_ones_l, ``nat_and_zero_r, ``nat_and_zero_l] do
          if done.contains (s, lem) then continue
          let l := mkIdent lem
          let saved ← saveState
          let ok ← try
              evalTactic (← `(tactic| have := $l $a $b $ml $kl (by decide) (by omega)))
              pure true
            catch _ => saved.restore; pure false
          if ok then done := done.push (s, lem)

/-- A rotation of the same value by two amounts, a nested rotation, or a rotation by an
amount that is `0` modulo the width: the amounts modulo the width as `Nat`/`Int` arithmetic
(`rule_amt`), closed by `omega` (`rule_omega_facts`). -/
macro "rule_rotamt" : tactic => `(tactic| (
  first
  | with_reducible apply GoFV.Proof.Rules.rotateLeft_rotateLeft_congr
  | with_reducible apply GoFV.Proof.Rules.rotateLeft_congr
  | with_reducible apply GoFV.Proof.Rules.rotateLeft_eq_self
  try simp only [rule_amt] at *
  rule_omega_facts
  omega))

/-- Shifts by constant amounts: contradictory amount bounds (a bounded shift by less than the
width, an unsigned amount below zero), equal amounts (`x <<< a = x <<< b` with `a`, `b` the same
number), a shift by at least the width, and constant folds (`goShl`/`goShr` of an auxint,
`ofInt_goShl` …); the amounts as `Nat`/`Int` arithmetic (`rule_amt`), closed by `omega`. -/
macro "rule_shamt" : tactic => `(tactic| (
  (try simp (disch := omega) only [GoFV.Proof.Rules.ofInt_goShr_signed,
    GoFV.Proof.Rules.ofInt_goShr_nonneg] at *)
  (try simp only [rule_amt] at *)
  rule_omega_facts
  first
  | (with_reducible apply GoFV.Proof.Rules.shl_ushr_shl <;> omega)
  | (with_reducible apply GoFV.Proof.Rules.ushr_shl_ushr <;> omega)
  | (with_reducible apply GoFV.Proof.Rules.shl_shl; omega)
  | (with_reducible apply GoFV.Proof.Rules.ushr_ushr; omega)
  | (with_reducible apply GoFV.Proof.Rules.sshr_sshr; omega)
  | ((first
       | rw [GoFV.Proof.Rules.ushr_shl]
       | rw [GoFV.Proof.Rules.sshr_shl]
       | rw [GoFV.Proof.Rules.shl_ushr])
     (try simp only [rule_bits] at *)
     congr 2 <;> omega)
  | ((with_reducible congr 1) <;> omega)
  | (rw [BitVec.shiftLeft_eq_zero (by omega)])
  | (rw [BitVec.ushiftRight_eq_zero (by omega)])
  | (exfalso; omega)))

/-- A comparison of integers against constants or of constants: both sides as `toNat`/`toInt`
arithmetic (`rule_cmp`, `rule_amt`), sign cases split, closed by `omega`. -/
macro "rule_cmpc" : tactic => `(tactic| (
  rw [Bool.eq_iff_iff]
  simp only [rule_cmp, rule_amt] at *
  rule_omega_facts
  (repeat' split) <;> omega))

/-- A value truncated and extended again where a shift already cleared
(`ushr_setWidth_setWidth`) or sign-filled (`sshr_setWidth_signExtend`) the high bits, else
both sides as `toNat` arithmetic (low-bit masks as remainders, `rule_amt`) closed by `omega`. -/
macro "rule_ext" : tactic => `(tactic| (
  first
  | (with_reducible apply GoFV.Proof.Rules.ushr_setWidth_setWidth <;>
      (try simp only [rule_amt] at *) <;> omega)
  | (with_reducible apply GoFV.Proof.Rules.sshr_setWidth_signExtend <;>
      (try simp only [rule_amt] at *) <;> omega)
  | (apply BitVec.eq_of_toNat_eq
     simp only [rule_amt] at *
     rule_omega_facts
     omega)))

/-- Division and remainder: constant folds (`sdiv_ofInt`, `srem_ofInt` with the auxint ranges
by `omega`; `udiv_ofInt`, `umod_ofInt`), a negated divisor (`sdiv_neg_ofInt`,
`srem_neg_right`), the minimal divisor (`sdiv_intMin_and_neg`), a remainder as
`x - (x / y) * y` (`sub_udiv_mul`, `sub_sdiv_mul`), contradictory divisor facts by `omega`. -/
macro "rule_div" : tactic => `(tactic| (
  (try simp only [rule_bits, BitVec.neg_eq_zero_iff] at *)
  (try simp (disch := omega) only [GoFV.Proof.Rules.sdiv_ofInt, GoFV.Proof.Rules.srem_ofInt,
    GoFV.Proof.Rules.sdiv_neg_ofInt, GoFV.Proof.Rules.udiv_ofInt, GoFV.Proof.Rules.umod_ofInt,
    GoFV.Proof.Rules.srem_neg_right, BitVec.neg_neg, BitVec.toNat_ofNat, Nat.reduceMod])
  first
  | done
  | with_reducible rfl
  | rw [GoFV.Proof.Rules.sub_udiv_mul]
  | rw [GoFV.Proof.Rules.sub_sdiv_mul]
  | rw [GoFV.Proof.Rules.sdiv_intMin_and_neg (by decide)]
  | (exfalso; simp only [rule_cmp, rule_amt] at *; omega)))

/-- An unsigned division or remainder by a power of two (`isPowerOfTwo(uintN(c))`, a
hypothesis `wrapInt w false (andPred T (wrapInt w false c)) = 0`): the divisor's value by
`isPow2_toNat`, then the shift (`udiv_pow2`, amount by `omega`) or mask (`umod_pow2_and`); a
product with `c` or `-c` (`uintN(-c)`: `ofInt_wrap_neg`) is a shift (`mul_pow2`, `mul_negpow2`).
Divisibility by a signed power of two (`isPowerOfTwo(c)`, `wrapInt w true (andPred T c) = 0`,
`divisible.rules:17–26`): `isPow2_signed`, then `divisible_pow2_u`/`_s` (and `_ne`). -/
elab "rule_pow2" : tactic => withMainContext do
  for h in ← getLCtx do
    if h.isImplementationDetail then continue
    let ty ← instantiateMVars h.type
    let some (_, l, _) := ty.eq? | continue
    unless l.isAppOfArity ``GoFV.Rules.wrapInt 3 && (l.getArg! 2).isAppOfArity ``andPred 2 do
      continue
    let ap := l.getArg! 2
    let inner := ap.getArg! 1
    if (l.getArg! 1).isConstOf ``Bool.true then
      let T ← Term.exprToSyntax (ap.getArg! 0)
      let w ← Term.exprToSyntax (l.getArg! 0)
      let c ← Term.exprToSyntax inner
      let hs ← Term.exprToSyntax h.toExpr
      evalTactic (← `(tactic| (
        obtain ⟨k, hp2, hk⟩ := GoFV.Proof.Rules.isPow2_signed (T := $T) (w := $w) (c := $c) rfl
          (by decide) (by omega) (by omega) $hs
        first
        | with_reducible exact GoFV.Proof.Rules.divisible_pow2_u _ _ _ hp2
        | with_reducible exact GoFV.Proof.Rules.divisible_pow2_s _ _ _ hp2 hk
        | with_reducible exact GoFV.Proof.Rules.divisible_pow2_u_ne _ _ _ hp2
        | with_reducible exact GoFV.Proof.Rules.divisible_pow2_s_ne _ _ _ hp2 hk)))
      return
    unless inner.isAppOfArity ``GoFV.Rules.wrapInt 3 do continue
    let T ← Term.exprToSyntax (ap.getArg! 0)
    let w ← Term.exprToSyntax (inner.getArg! 0)
    let c ← Term.exprToSyntax (inner.getArg! 2)
    let hs ← Term.exprToSyntax h.toExpr
    evalTactic (← `(tactic| (
      obtain ⟨hp2, hb1, hb2⟩ := GoFV.Proof.Rules.isPow2_toNat (T := $T) (w := $w) (c := $c) rfl
        (by decide) (by first | assumption | omega) $hs
      first
      | (rw [GoFV.Proof.Rules.udiv_pow2 _ _ _ hp2]; congr 1; simp only [rule_amt] at *; omega)
      | rw [GoFV.Proof.Rules.umod_pow2_and _ _ _ hp2]
      | (rw [GoFV.Proof.Rules.mul_pow2 _ _ _ hp2]; congr 1; simp only [rule_amt] at *; omega)
      | (rw [GoFV.Proof.Rules.ofInt_wrap_neg] at hp2
         rw [GoFV.Proof.Rules.mul_negpow2 _ _ _ hp2]; congr 2; simp only [rule_amt] at *; omega))))
    return
  throwError "rule_pow2: no isPowerOfTwo condition"

/-- Close the arithmetic left after the splits: auxint reads are generalized, constants
pushed into `BitVec`, then `rfl`, a rotation (`rule_rot`, before `grind`: a failing `grind`
spends seconds on rotation goals), a ring identity (`grind` after complements and constant
shifts become ring terms), a per-bit identity, `rule_ext`, and `bv_decide`'s rewriting front
end `bv_normalize` (no SAT call, no axioms; without enum/structure preprocessing, which would
declare `PUnit.enumToBitVec` in every module). Never `bv_decide` itself: its `_native` axioms
fail `scripts/axioms-audit.sh` (#218 replaced 30 proofs that fell through to it); a goal none
of these closes fails here and needs a closer of its own. -/
macro "rule_close" : tactic => `(tactic| (
  repeat rule_gen1
  try simp only [GoFV.Proof.Rules.DV.int.injEq, GoFV.Proof.Rules.DV.bool.injEq] at *
  try rule_ands
  try rule_subst
  try rule_norm
  try simp_all only [rule_arith, rule_close_s]
  first
  | done
  | with_reducible rfl
  | rule_rot
  | rule_rotamt
  | rule_shamt
  | rule_cmpc
  | rule_div
  | rule_pow2
  | ((try simp only [GoFV.Proof.Rules.bv_not_eq, GoFV.Proof.Rules.bv_shl_nat, Nat.reducePow] at *)
     grind)
  | ((try simp only [rule_bits] at *)
     ext i hi
     simp
     done)
  | rule_ext
  | (bv_normalize (config := { enums := false, structures := false }); done)
  | fail "rule_close: no closer applies (bv_decide is not used: scripts/axioms-audit.sh)"))

/-- `rule_unfold`, the case splits, then `rule_close` on every remaining case. -/
macro "rule_auto_core" : tactic => `(tactic| (
  rule_unfold
  (try rule_ands)
  (try rule_clear_oracle)
  (try rule_norm)
  (try rule_ands)
  all_goals (repeat rule_split1)
  all_goals (try rule_widths)
  all_goals rule_close))

/-- `rule_auto_core` with `rule_norm`'s `decide := true` (`gofv.ruleNorm.decide`). Needed by the
nested rotations by sized amounts (`generic.rules:2246`, `:2247`, RotateLeft6/8/10/12): their
splits leave cases that only `decide` closes. Call it there directly: `rule_auto` would first
spend a failed `rule_auto_core` (6.5 of 9.9 s CPU for `r_generic_2246_2_sound`). -/
macro "rule_auto_dec" : tactic => `(tactic|
  set_option gofv.ruleNorm.decide true in rule_auto_core)

/-- `rule_auto_core`, and `rule_auto_dec` if that fails (proofs written against the old
`rule_norm`, which always used `decide := true`). -/
macro "rule_auto" : tactic => `(tactic| first
  | rule_auto_core
  | rule_auto_dec)

-- The congruence equations of the `match`es `simp` meets in the rule lemmas, generated here
-- once: generated in two rule modules they are two public declarations of the same name, and
-- the modules cannot be imported together (`scripts/axioms-audit.sh` imports all).
run_meta do
  for n in [``Option.getD.match_1, ``GoFV.Proof.Rules.binDV.match_4,
      ``GoFV.Proof.Rules.fieldDV.match_1] do
    discard <| Lean.Meta.Match.genMatchCongrEqns n

end GoFV.Proof.Rules
