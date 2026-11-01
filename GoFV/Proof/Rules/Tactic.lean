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
   `rfl`, a rotation (`rule_rot`), `grind`, and as the last resort `bv_decide`.

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

/-! The lemma lists of the tactics, as simp sets (`Attr.lean`). -/

attribute [rule_norm_s] or_true true_or or_false false_or and_true true_and and_false false_and
  beq_self_eq_true Bool.true_or Bool.or_true Bool.false_or Bool.or_false Bool.false_and
  Bool.and_false Bool.true_and Bool.and_true Bool.and_eq_true Bool.or_eq_true ne_eq reduceCtorEq
  bne_self_eq_false Bool.false_eq_true ite_false ite_true not_false_eq_true not_true_eq_false
  Bool.not_eq_true Option.some.injEq Option.getD_some Option.getD_none List.getD_cons_zero
  List.getD_cons_succ decide_eq_true_eq decide_eq_false_iff_not beq_iff_eq bne_iff_ne Nat.le_refl
  Nat.lt_irrefl BitVec.ofInt_ofNat Nat.reducePow Nat.reduceLT Nat.reduceLeDiff Nat.reduceAdd
  Nat.reduceSub Nat.reduceMod GoFV.Rules.wrapTo GoFV.Proof.Rules.reduceIntInfo DV.int.injEq
  DV.bool.injEq callE callH Bool.cond_true Bool.cond_false

attribute [rule_unfold_ds] GoFV.Proof.Rules.Pat.den GoFV.Proof.Rules.Pat.dens
  GoFV.Proof.Rules.Pat.raw GoFV.Proof.Rules.sigma GoFV.Proof.Rules.Pat.binds
  GoFV.Proof.Rules.Pat.bindss GoFV.Proof.Rules.Pat.cons GoFV.Proof.Rules.Pat.conss
  GoFV.Proof.Rules.Pat.wf GoFV.Proof.Rules.Pat.wfs GoFV.Proof.Rules.Pat.typed
  GoFV.Proof.Rules.Pat.typeds GoFV.Proof.Rules.auxIntOk
  GoFV.Proof.Rules.Field.bindDV GoFV.Proof.Rules.condHolds GoFV.Proof.Rules.resDen
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

attribute [rule_unfold_s] GoFV.Proof.Rules.callH GoFV.Proof.Rules.binE_land_bool
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
facts propagate, `hasTy` facts become type equations. -/
macro "rule_norm" : tactic => `(tactic|
  simp_all (config := { decide := true }) only [rule_sem, rule_helper, rule_norm_s])

/-- Reduce `Rule.Sound r` (`r` a constant) to the semantic statement of its pattern and
result; the hypotheses are `hwf` (checker facts), `hc` (pattern checks), `hcond` (condition),
`hty` (top type), `hlt` (leaf types). -/
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
  let hlt := mkIdent `hlt
  evalTactic (← `(tactic| (
    refine ⟨rfl, ?_⟩
    intro $e:ident $or:ident
    dsimp only [$rid:ident, rule_unfold_ds]
    simp only [rule_helper, rule_unfold_s]
    intro $hwf:ident $hc:ident $hcond:ident $hty:ident $hlt:ident)))

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

/-- One case split on a `splitCandidate?` of the goal or a hypothesis, followed by `rule_norm`
in every case. A leaf read as an integer (a boolean) is replaced by it. -/
elab "rule_split1" : tactic => withMainContext do
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
        (try have hv := val_poison_of_asInt_none hsplit (by with_reducible assumption)) <;>
        (try rule_norm))))
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
        (try rule_norm))))
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

/-- Close the arithmetic left after the splits: auxint reads are generalized, constants
pushed into `BitVec`, then `rfl`, a rotation (`rule_rot`, before `grind`: a failing `grind`
spends seconds on rotation goals), a ring identity (`grind` after complements and constant
shifts become ring terms), and as the last resort `bv_decide` on the `BitVec`-amount form
(`rule_bv`), whose LRAT certificate is stored in the `.olean` (megabytes for a 64-bit goal;
`scripts/rule-proofs.py probe` marks such rules `BV`). -/
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
  | ((try simp only [GoFV.Proof.Rules.bv_not_eq, GoFV.Proof.Rules.bv_shl_nat, Nat.reducePow] at *)
     grind)
  | ((try simp only [rule_bits] at *)
     ext i hi
     simp
     done)
  | rule_ext
  | ((try simp only [rule_bv, Nat.reducePow, Nat.reduceLT] at *)
     bv_decide (config := { enums := false, structures := false }))))

/-- `rule_unfold`, the case splits, then `rule_close` on every remaining case. -/
macro "rule_auto" : tactic => `(tactic| (
  rule_unfold
  (try rule_ands)
  (try rule_clear_oracle)
  (try rule_norm)
  (try rule_ands)
  all_goals (repeat rule_split1)
  all_goals (try rule_widths)
  all_goals rule_close))

-- The congruence equations of the `match`es `simp` meets in the rule lemmas, generated here
-- once: generated in two rule modules they are two public declarations of the same name, and
-- the modules cannot be imported together (`scripts/rule-proofs.py axioms` imports all).
run_meta do
  for n in [``Option.getD.match_1, ``GoFV.Proof.Rules.binDV.match_4,
      ``GoFV.Proof.Rules.fieldDV.match_1] do
    discard <| Lean.Meta.Match.genMatchCongrEqns n

end GoFV.Proof.Rules
