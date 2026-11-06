import GoFV.Proof.Low.RuleL
import GoFV.Opt.Lower

/-!
# Validating `lower` / `late lower` against their log (issue #385)

`validateL` is Phase 1's rewrite validator (`GoFV.Opt.RewriteCheck.validate`) for lowered SSA: the
log of `applyRewrite` with a lowering rule table is replayed on a map of definitions from the
input `f`, and the output `g` must have the replayed definitions. The differences:

* terms are the values `termVL` says (generic term ops, the monotone pure arm64 ops, `MOVDaddr`
  without a frame variable and the integer loads `MOV{B,BU,H,HU,W,WU,D}load`, of a frame variable
  in activation 0), shaped by their lowered shapes (`shpL`);
* a rule event is checked as an instance of one commutation choice of the rule (`ruleOKL`: the
  swapped pattern `Rule.swapC` matched argument for argument, `matchPatL`), for the obligation
  `ArmRule.Sound`; result nodes take the type `nodeTyL` gives (Go's `types.TypeFlags` is the
  flags shape) and the aux `nodeAuxL` gives (a pattern-bound `{sym}`); a result whose top is an
  integer load reads the matched shape's size (`resFitsL`); there are no block (`@b`) results;
* an ellipsis rule `(o ...) => (o' ...)` (`setOp`) is replayed as the op change: on a term whose
  new op is a term (`ArmRule.SetOp`), its `setArgW64` arguments (`AddPtr`'s index) values at a
  64-bit integer shape (`setArgsOK`), or on an atom renamed by `renameOp` (`ArmRule.Rename`);
* a block rule event is checked by `blockOKL` against `BlockRuleL.Sound`: one control matched by
  the rule's control pattern, the block's auxint (tracked in `BStateL`) as the rule asks, the new
  controls the rule's variables, the new auxint the rule's;
* atoms of `g` correspond to atoms of `f` by `atomPair`: the same fields, or an atom renamed by
  `renameOp` with the same type, auxint, aux and arguments' count, or a `Store` lowered to an
  arm64 store (`memLower`), or a `Zero` lowered to `LoweredZero`/`LoweredZeroLoop` (`zeroLower`),
  or a `LocalAddr` lowered to `MOVDaddr` (`addrLower`); a rule event lowering a store, a `Zero` or
  a frame address, or folding an `ADDconst` offset (`stFold`) or a global
  symbol's or frame variable's `MOVDaddr` (`stFoldAddr`) into an arm64 store, is replayed as its
  new definitions (`atomDef`); a rule event folding a lowered frame address into an integer load
  (a term) or into an `ADDconst` is replayed as the folded term (`frameFold`);
* a rule event folding a constant operand into a lowered bounds panic (`ARM64.rules:513-516`) is
  replayed as no change (`pbFoldEv`): the output's `LoweredPanicBounds{RC,CR,CC}` must keep the
  replayed `LoweredPanicBoundsRR`'s other arguments (`pbFinal`), and its aux constants are the
  `Const64` operands of `f`'s `PanicBounds` (`pbLower`, `pbConstOK`);
* each block evaluates `f`'s roots in the same order in `g` (a lowered `Zero` is not a root of
  lowered SSA: `g` may evaluate it earlier, which never fails without faulting memory);
* copies are compatible at the lowered shapes (`copyCompatL`); phi eliminations and snapshots
  reject.
-/

namespace GoFV.Opt.LowerCheck

open GoFV.SSA GoFV.Rules GoFV.Proof.Rules GoFV.Proof.Low GoFV.Opt.RewriteCheck

/-! ## Matching -/

mutual
/-- Match pattern `q` (no commutation: a swapped pattern, `Pat.swapC`) at value `w` (position
`p`) in `M`; every op node is a term (`termVL`) with the pattern's op and arity. -/
def matchPatL (tabs : Tables) (M : Defs) : Pat → Path → ID → Option Inst
  | .op o _ _ _ _ ar args _, p, w =>
    match M.get? w with
    | none => none
    | some x =>
      if x.op != o || !termVL tabs x || x.args.size != args.length ||
          !(match ar with | .fixed | .exact _ => true | _ => false) then none
      else
        match matchPatsL tabs M args p 0 x.args.toList with
        | none => none
        | some I => some ((p, w) :: I)
  | _, p, w => some [(p, w)]
/-- Match the patterns `qs` (argument positions `i, i+1, …` below `p`) at the values `as`. -/
def matchPatsL (tabs : Tables) (M : Defs) : List Pat → Path → Nat → List ID → Option Inst
  | [], _, _, [] => some []
  | q :: qs, p, i, a :: as =>
    match matchPatL tabs M q (i :: p) a with
    | none => none
    | some I =>
      match matchPatsL tabs M qs p (i + 1) as with
      | none => none
      | some J => some (I ++ J)
  | _, _, _, _ => none
end

/-- The static instance environment at the lowered shapes (`RewriteCheck.env`). -/
def envL (tabs : Tables) (M : Defs) (I : Inst) : PEnv where
  leaf _ := .poison
  ty p := ((M.get? (I.at p)).map fun x => shpL tabs x.type).getD .other
  auxInt p := ((M.get? (I.at p)).map (·.auxInt)).getD 0
  aux p := ((M.get? (I.at p)).map (·.aux)).getD none

/-- The subexpressions of a condition under an odd number of negations (through `&&`, `||`
and `!`): the validator's oracle answers an unmodelled boolean there `false`, elsewhere `true`,
so that a condition Go found true is true under the oracle too (any boolean answers are sound:
the obligations quantify over every `Oracle.BoolTyped` oracle). -/
def negAtoms : Bool → Expr → List Expr
  | neg, .unop .not y _ => negAtoms (!neg) y
  | neg, .binop .land a b _ => negAtoms neg a ++ negAtoms neg b
  | neg, .binop .lor a b _ => negAtoms neg a ++ negAtoms neg b
  | neg, e => if neg then [e] else []

/-- The validator's oracle (`RewriteCheck.oracle`) with the built nodes' lowered shapes and the
unmodelled booleans of `negs` answered `false`. -/
def oracleL (vtys : List GoTy) (tabs : Tables) (negs : List Expr) (nodes : List (RNode × Value)) :
    Oracle where
  dv e := if exprTy [] e == .bool || exprTy vtys e == .bool then .bool !(negs.contains e) else .other
  ty e := ((nodes.find? fun (n, _) => match n.ty with
      | some te => te == e | none => false).map fun (_, u) => shpL tabs u.type).getD .other
  auxInt e := ((nodes.find? fun (n, _) => match n.auxInt with
      | some ae => ae == e | none => false).map (·.2.auxInt)).getD 0
  aux e := ((nodes.find? fun (n, _) => match n.aux with
      | some xe => xe == e | none => false).map (·.2.aux)).getD none
  val _ := .poison

/-- Result node `n` was built as the term `u` (`nodeDenL`'s fields). -/
def nodeOKL (tabs : Tables) (e : PEnv) (pat : Pat) (ev : Expr → DV) (or : Oracle) (σ : Nat → DV)
    (I : Inst) (ids : List ID) (topTy : Sem.Ty) (n : RNode) (u : Value) : Bool :=
  u.op == n.op && termVL tabs u &&
  GoFV.Opt.CSE.tyEq (shpL tabs u.type) (nodeTyL ev or topTy n.ty) &&
  u.auxInt == (match n.auxInt with
    | some ae => (toAuxIntL n.op.auxType (ev ae)).getD (or.auxInt ae)
    | none => 0) &&
  u.aux == nodeAuxL e pat or n.aux &&
  u.args.size == n.args.length &&
  (n.args.zip u.args.toList).all fun (a, w) => argID σ I ids a == some w

/-- The built definitions are the result's (`resDenL`): a `copy` of a bound value of a compatible
shape (`copyOf` gives `v` the value's type; `copyCompat`: the same shape, or two pointer shapes),
or an in-place `build` whose other nodes are fresh. -/
def resultOKL (tabs : Tables) (M : Defs) (e : PEnv) (pat : Pat) (ev : Expr → DV) (or : Oracle)
    (σ : Nat → DV) (I : Inst) (r : Rule) (v : Value) (defs : List Value) : Bool :=
  let topTy := shpL tabs v.type
  match r.result, r.block, defs with
  | .copy ce, none, [u] =>
    match DV.pos? (ev ce) with
    | some p => u.id == v.id && u.op == .Copy && u.args == #[I.at p] &&
        (M.get? (I.at p)).any (fun y => y.type == u.type &&
          copyCompat (shpL tabs y.type) (shpL tabs v.type)) &&
        I.at p != v.id && u.auxInt == 0 && u.aux == none
    | none => false
  | .build nodes, none, u0 :: us =>
    let ids := us.map (·.id)
    u0.id == v.id && ids.head? == some v.id &&
    us.length == nodes.length &&
    (ids.drop 1).all (fun x => (M.get? x).isNone) && (ids.drop 1).Nodup &&
    !(ids.drop 1).contains v.id &&
    (nodes.zip us).all fun (n, u) => nodeOKL tabs e pat ev or σ I ids topTy n u
  | _, _, _ => false

/-- One commutation choice of a value rule event: `ruleOK` of Phase 1 on the swapped rule `r`,
without the generic-only checks (top shapes, frame helpers, `isNonNegative`). -/
def ruleOK1 (tabs : Tables) (M : Defs) (r : Rule) (v : ID) (x : Value) (defs : List Value) :
    Bool :=
  Pat.arityOk r.pat && patOK r.pat &&
  match matchPatL tabs M r.pat [] v with
  | none => false
  | some I =>
    let e := envL tabs M I
    let vtys := r.vars.map (·.ty)
    let σ := sigmaL tabs e r.pat
    let nodes := match r.result, defs with
      | .build ns, _ :: us => ns.zip us
      | _, _ => []
    let or := oracleL vtys tabs ((r.cond.map (negAtoms false)).getD []) nodes
    let ev := evalE vtys σ or e (Pat.denL tabs e [] r.pat)
    I.tail.all (·.2 != v) &&
    consOK ev σ e I [] r.pat && wfOK e [] r.pat &&
    (match r.cond with
      | some c => match ev c with | .bool true => true | _ => false
      | none => true) &&
    Pat.argsOK e.ty [] r.pat && Pat.topOKL (e.ty []) r.pat && Pat.argsOKL e.ty [] r.pat &&
    resFitsL (e.ty []) r.result && Pat.addrOKL e.ty e.aux e.auxInt [] r.pat && leavesOK M I [] r.pat &&
    resultOKL tabs M e r.pat ev or σ I r x defs

/-- The rule event `(v, r, defs)` is a sound instance of one commutation choice of `r` on `M`
(`ArmRule.Sound`). -/
def ruleOKL (tabs : Tables) (M : Defs) (r : Rule) (v : ID) (defs : List Value) : Bool :=
  match M.get? v with
  | none => false
  | some x =>
    termVL tabs x && x.id == v &&
    (choices (Pat.commutes r.pat)).any fun sw => ruleOK1 tabs M (Rule.swapC r sw) v x defs

/-- The arguments of `x` that `setArgW64` asks for are values of `M` at a 64-bit integer shape. -/
def setArgsOK (tabs : Tables) (M : Defs) (x : Value) : Bool :=
  (List.range x.args.size).all fun i =>
    !setArgW64 x.op i ||
      (M.get? x.args[i]!).any fun y => GoFV.Proof.Rules.isInt64Ty (shpL tabs y.type)

/-- An ellipsis rule `(o ...) => (o' ...)` at `v`: the new definition of `v` (`ArmRule.SetOp` on
terms, `ArmRule.Rename` on atoms). -/
def setOpDef (tabs : Tables) (M : Defs) (r : Rule) (v : ID) : Option Value :=
  match M.get? v, r.result with
  | some x, .setOp o' =>
    let x' := { x with op := o' }
    if x.id == v && ellipsisOn x.op r.pat && r.cond.isNone && r.block.isNone &&
        ((termVL tabs x && termVL tabs x' && topOKL x.op (shpL tabs x.type) &&
            setArgsOK tabs M x) ||
          (renameOp x.op o' && !termVL tabs x)) then some x'
    else none
  | _, _ => none

/-- The atom `u` folds the address `ADDconst [k2] b` of the arm64 store `x` (`x`'s argument 0 in
`M`, a term at a word shape) into its offset (`(MOV…store [k1] {sym} (ADDconst [k2] ptr) val mem)
=> (MOV…store [k1+int32(k2)] {sym} ptr val mem)`, `ARM64.rules:758-776`): the same op and type,
no aux, `b` for the address, the offset `k1 + k2`, all three offsets small and non-negative
(`offOK`). -/
def stFold (tabs : Tables) (M : Defs) (x u : Value) : Bool :=
  (stSize x.op).isSome && u.op == x.op && u.type == x.type && x.aux == none && u.aux == none &&
  x.args.size == 3 && offOK x.auxInt && offOK u.auxInt &&
  match M.get? x.args[0]! with
  | some y =>
    y.op == .ARM64ADDconst && termVL tabs y && y.args.size == 1 &&
      wordShape (shpL tabs y.type) && offOK y.auxInt &&
      u.auxInt.toInt == x.auxInt.toInt + y.auxInt.toInt &&
      u.args == #[y.args[0]!, x.args[1]!, x.args[2]!]
  | none => false

/-- The atom `u` folds the address `MOVDaddr [k2] {sym} b` of the arm64 store `x` (`x`'s argument
0 in `M`) into its offset and aux (`(MOV…store [k1] {sym1} (MOVDaddr [k2] {sym2} ptr) val mem) &&
canMergeSym(sym1,sym2) … => (MOV…store [k1+k2] {mergeSym(sym1,sym2)} ptr val mem)`,
`ARM64.rules:881-905`): the same op and type, `x` without aux, `u` with the `MOVDaddr`'s, `b` for
the address, the offset `k1 + k2` (`k1` and the sum small and non-negative, `offOK`); the
`MOVDaddr` either a term (a global symbol, at a word shape) or, at offset 0, the lowered frame
address of the `LocalAddr` of `f` with the same aux (a frame variable). -/
def stFoldAddr (tabs : Tables) (f : Func) (M : Defs) (x u : Value) : Bool :=
  (stSize x.op).isSome && u.op == x.op && u.type == x.type && x.aux == none &&
  x.args.size == 3 && offOK x.auxInt && offOK u.auxInt &&
  match M.get? x.args[0]! with
  | some m =>
    m.op == .ARM64MOVDaddr && m.args.size == 1 && m.aux.isSome && u.aux == m.aux &&
      u.auxInt.toInt == x.auxInt.toInt + m.auxInt.toInt &&
      u.args == #[m.args[0]!, x.args[1]!, x.args[2]!] &&
      (termVL tabs m && wordShape (shpL tabs m.type) ||
        !termVL tabs m && m.auxInt == 0 &&
          (f.value? x.args[0]!).any fun l => l.op == .LocalAddr && l.aux == m.aux)
  | none => false

/-- A rule event at the atom `v` replayed as the atom its top result node `u` defines (the log
lists the reset value, then the nodes, as for any `build`), with `v`'s type:
* a lowered store (`memLower` at offset 0 without aux: `(Store {t} ptr val mem) => (MOVDstore ptr
  val mem)` and the other sizes), on `v`'s arguments;
* a lowered `Zero` (`zeroLower`: `LoweredZero`, `LoweredZeroLoop`), on `v`'s arguments;
* an offset folded into an arm64 store lowering a `Store` of `f` (`stFold`), or a global symbol's
  or frame variable's address (`stFoldAddr`);
* a lowered frame address (`addrLower`): `(LocalAddr {sym} base _) => (MOVDaddr {sym} base)` on
  some of `v`'s arguments, or `(MOVDaddr {sym} (SPanchored base mem))`, whose second node `s` is a
  fresh term on some of `v`'s arguments (`u` reads no argument, `argFree`).
The new definitions: `u` and the fresh term, if any. -/
def atomDef (tabs : Tables) (f : Func) (M : Defs) (v : ID) (defs : List Value) :
    Option (Value × Option Value) :=
  match M.get? v, defs with
  | some x, [_, u] =>
    if x.id == v && u.id == v && !termVL tabs x && !termVL tabs u && u.type == x.type &&
        (u.args == x.args && memLower tabs x u && u.auxInt == 0 && u.aux == none ||
          u.args == x.args && zeroLower x u ||
          u.args.all x.args.contains && addrLower tabs x u ||
          (stFold tabs M x u || stFoldAddr tabs f M x u) && (f.value? v).any (·.op == .Store))
        then some (u, none)
    else none
  | some x, [_, u, s] =>
    if x.id == v && u.id == v && !termVL tabs x && !termVL tabs u && u.type == x.type &&
        addrLower tabs x u && u.args == #[s.id] && s.id != v && (M.get? s.id).isNone &&
        termVL tabs s && s.args.all x.args.contains then some (u, some s)
    else none
  | _, _ => none

/-- A rule event at the term `x` at `v` replayed as the term `u` that folds `x`'s address
argument, the lowered frame address `MOVDaddr {sym} b` of a `LocalAddr {sym}` of `f` (an atom,
offset 0), into its aux, with `x`'s type and offset (small and non-negative, `offOK`), `u` with
the `MOVDaddr`'s aux and `b` for the address:
* an integer load without aux (`(MOV…load [off1] {sym1} (MOVDaddr [off2] {sym2} ptr) mem) &&
  canMergeSym(sym1,sym2) … => (MOV…load [off1+off2] {mergeSym(sym1,sym2)} ptr mem)`,
  `ARM64.rules:832-856`), the same op;
* an `ADDconst` at a word shape (`(ADDconst [off1] (MOVDaddr [off2] {sym} ptr)) && … =>
  (MOVDaddr [int32(off1)+off2] {sym} ptr)`, `650`), a `MOVDaddr` term. -/
def frameFold (tabs : Tables) (f : Func) (M : Defs) (v : ID) (defs : List Value) :
    Option Value :=
  match M.get? v, defs with
  | some x, [_, u] =>
    match M.get? x.args[0]! with
    | some m =>
      if x.id == v && u.id == v && u.type == x.type && u.auxInt == x.auxInt && offOK x.auxInt &&
          termVL tabs x && termVL tabs u && m.op == .ARM64MOVDaddr && !termVL tabs m &&
          m.args.size == 1 && u.aux == m.aux &&
          (f.value? x.args[0]!).any (fun l => l.op == .LocalAddr && l.aux == m.aux) &&
          ((ldOp? x.op).isSome && u.op == x.op && x.aux == none && x.args.size == 2 &&
              u.args == #[m.args[0]!, x.args[1]!] ||
            x.op == .ARM64ADDconst && u.op == .ARM64MOVDaddr && x.args.size == 1 &&
              wordShape (shpL tabs x.type) && u.args == #[m.args[0]!])
      then some u else none
    | none => none
  | _, _ => none

/-- A rule event at the renamed bounds panic `LoweredPanicBoundsRR` at `v` building a lowered
bounds panic with constant operands (`pbKeep`; `ARM64.rules:513-516`, the later ones on the
result of the first): the replay keeps `v`'s definition, which `finalOKL` relates to the output's
(`pbFinal`). -/
def pbFoldEv (M : Defs) (v : ID) (defs : List Value) : Bool :=
  match M.get? v, defs with
  | some x, [_, u] => x.op == .ARM64LoweredPanicBoundsRR && u.id == v && (pbKeep u.op).isSome
  | _, _ => false

/-! ## Copies -/

/-- A `Copy` of shape `s` of a value of shape `t` is the identity on it (`RewriteCheck.copyCompat`
at the lowered shapes). -/
def copyCompatL (s t : Sem.Ty) : Bool := copyCompat s t

/-- `w` is `a`, or reached from `a` through at most `n` compatible `Copy`s (`copyReach` at the
lowered shapes). -/
def copyReachL (tabs : Tables) (M : Defs) : Nat → ID → ID → Bool
  | 0, a, w => a == w
  | n + 1, a, w =>
    a == w ||
    match M.get? a with
    | some x =>
      x.op == .Copy && x.args.size == 1 &&
      (match M.get? x.args[0]! with
        | some y => copyCompatL (shpL tabs x.type) (shpL tabs y.type)
        | none => false) &&
      copyReachL tabs M n x.args[0]! w
    | none => false

/-! ## Blocks -/

/-- The replayed terminator of a block: kind, controls, auxint, successors swapped. -/
structure BStateL where
  kind : BlockKind
  ctrls : Array ID
  auxInt : Int64
  swapped : Bool
  deriving Inhabited

/-- The replayed terminators of the blocks the log changed, latest first. -/
abbrev BMapL := List (ID × BStateL)

/-- The terminator of `b` in the replay: the latest replayed one, else the input's. -/
def bstateL (f : Func) (B : BMapL) (b : ID) : Option BStateL :=
  match B.lookup b with
  | some st => some st
  | none => (f.block? b).map fun fb =>
      { kind := fb.kind, ctrls := fb.controls, auxInt := fb.auxInt, swapped := false }

/-- `blockAuxOK` decided. -/
def blockAuxOKB (fl : GoFV.Rules.Field) (ai : Int64) : Bool :=
  match fl with
  | .any => true
  | .eq (.lit _ (.int i)) => ai.toInt == i
  | _ => false

/-- One commutation choice of a block-rule event: the swapped control pattern `pat` matches the
control `c`, its checks and condition hold, the block auxint is as the rule asks, the new controls
are the rule's variables and the new auxint the rule's. -/
def blockOK1 (tabs : Tables) (M : Defs) (br : BlockRule) (pat : Pat) (st : BStateL) (c : ID)
    (nc : Array ID) : Option BStateL :=
  if !Pat.arityOk pat then none else
  match matchPatL tabs M pat [] c with
  | none => none
  | some I =>
    let e := envL tabs M I
    let vtys := br.vars.map (·.ty)
    let σ := sigmaL tabs e pat
    let or := oracleL vtys tabs ((br.cond.map (negAtoms false)).getD []) []
    let ev := evalE vtys σ or e (Pat.denL tabs e [] pat)
    let ctrlsOK : Bool := match br.newKind, br.newControls, nc.toList with
      | .First, [], [] => true
      | k, [(.var x, _)], [c'] => k != .First && (DV.pos? (σ x)).map I.at == some c'
      | _, _, _ => false
    if (Pat.sames pat).all (fun x => !(Pat.opNames pat).contains x) &&
        consOK ev σ e I [] pat && wfOK e [] pat &&
        (match br.cond with
          | some cd => match ev cd with | .bool true => true | _ => false
          | none => true) &&
        Pat.argsOK e.ty [] pat && Pat.topOKL (e.ty []) pat && Pat.argsOKL e.ty [] pat &&
        leavesOK M I [] pat &&
        blockAuxOKB br.auxInt st.auxInt &&
        ctrlsOK then
      match newAuxL ev br.newAuxInt with
      | some ai' => some { kind := br.newKind, ctrls := nc, auxInt := ai',
                           swapped := st.swapped != br.swapSuccs }
      | none => none
    else none

/-- A block-rule event (rule `br`, new controls `nc`) on the replayed terminator `st`
(`BlockRuleL.Sound`): `st` has `br`'s kind, a conditional kind (`condKind`), and one control,
and some commutation choice of the control pattern validates (`blockOK1`). -/
def blockOKL (tabs : Tables) (M : Defs) (br : BlockRule) (st : BStateL) (nc : Array ID) :
    Option BStateL :=
  match br.controls, st.ctrls.toList with
  | [pat], [c] =>
    if st.kind == br.kind && condKind br.kind && br.aux matches .any && br.newAux.isNone then
      (choices (Pat.commutes pat)).findSome? fun sw =>
        blockOK1 tabs M br (Pat.swapC pat sw).1 st c nc
    else none
  | _, _ => none

/-! ## Replay -/

/-- Replay the log on the definitions `M` and the terminators `B`, from `f`'s; `none` if an event
is not validated. A copy-argument replacement the copies of `M` do not justify is skipped (`M`
keeps its definition; `finalOKL` decides); phi eliminations and snapshots reject. -/
def replayL (tabs : Tables) (t : Interp.Table) (f : Func) :
    Defs → BMapL → List RwEvent → Option (Defs × BMapL)
  | M, B, [] => some (M, B)
  | M, B, .rule v i _ defs :: evs =>
    match M.get? v with
    | none => none
    | some x =>
      if pbFoldEv M v defs.toList then replayL tabs t f M B evs else
      match (t.values[x.op.ctorIdx]?).bind (·[i]?) with
      | none => none
      | some cr =>
        match cr.rule.result with
        | .setOp _ =>
          match setOpDef tabs M cr.rule v with
          | some x' => replayL tabs t f (M.put v x') B evs
          | none => none
        | _ =>
          if ruleOKL tabs M cr.rule v defs.toList then
            replayL tabs t f (defs.foldl (fun M u => M.put u.id u) M) B evs
          else match atomDef tabs f M v defs.toList with
            | some (u, none) => replayL tabs t f (M.put v u) B evs
            | some (u, some s) => replayL tabs t f ((M.put s.id s).put v u) B evs
            | none =>
              match frameFold tabs f M v defs.toList with
              | some u => replayL tabs t f (M.put v u) B evs
              | none => none
  | M, B, .copyArg v i src :: evs =>
    match M.get? v with
    | none => none
    | some x =>
      if h : i < x.args.size then
        if copyReachL tabs M M.size x.args[i] src then
          replayL tabs t f (M.put v { x with args := x.args.set i src }) B evs
        else replayL tabs t f M B evs
      else none
  | M, B, .control b i c :: evs =>
    match bstateL f B b with
    | none => none
    | some st =>
      if h : i < st.ctrls.size then
        if copyReachL tabs M M.size st.ctrls[i] c then
          replayL tabs t f M ((b, { st with ctrls := st.ctrls.set i c }) :: B) evs
        else none
      else none
  | _, _, .phielim .. :: _ => none
  | _, _, .snap .. :: _ => none
  | M, B, .blockRule b i nc :: evs =>
    match bstateL f B b with
    | none => none
    | some st =>
      if ((f.block? b).map (·.succs.size)) != some 2 then none else
      match (t.blocks[st.kind.ctorIdx]?).bind (·[i]?) with
      | none => none
      | some br =>
        match blockOKL tabs M br st nc with
        | none => none
        | some st' => replayL tabs t f M ((b, st') :: B) evs

/-! ## The output -/

/-- A value that is not a term of a lowered function. -/
@[inline] def isAtomL (tabs : Tables) (x : Value) : Bool := !termVL tabs x

/-- The atoms listed in block `b`. -/
def atomsOfL (tabs : Tables) (h : Func) (b : Block) : List ID :=
  b.values.toList.filter fun x => match h.value? x with
    | some v => isAtomL tabs v
    | none => false

/-- The atom `w` of `g` corresponds to the atom `u` of `f`: the same fields, or `w` renames `u`
(`renameOp`) with the same type, auxint, aux and number of arguments, or `w` lowers the store `u`
(`memLower`) or the `Zero` `u` (`zeroLower`) with the same type and number of arguments, or the
frame address `u` (`addrLower`) or the bounds panic `u` with constant operands (`pbLower`) with the
same type. -/
def atomPair (tabs : Tables) (u w : Value) : Bool :=
  (((u.op == w.op || renameOp u.op w.op) && u.auxInt == w.auxInt && u.aux == w.aux ||
    memLower tabs u w || zeroLower u w) && u.args.size == w.args.size || addrLower tabs u w ||
    pbLower u w) &&
  u.type == w.type && u.block == w.block && u.id == w.id

/-- The operands of `PanicBounds [kind] x y mem` a lowered bounds panic with constant operands
carries in its aux (`Sem.arm64Op`'s `pbc`/`pbcc`): `RC` `y` (operand 1), `CR` `x` (0), `CC` both;
`none` for another op or aux. -/
def pbConsts (tabs : Tables) (w : Value) : Option (List (Nat × Int)) :=
  match w.op, w.aux.bind tabs.aux? with
  | .ARM64LoweredPanicBoundsRC, some { kind := .pbc k, .. } => some [(1, k)]
  | .ARM64LoweredPanicBoundsCR, some { kind := .pbc k, .. } => some [(0, k)]
  | .ARM64LoweredPanicBoundsCC, some { kind := .pbcc kx ky, .. } => some [(0, kx), (1, ky)]
  | _, _ => none

/-- Operand `i` of `u` is, in `f`, a `Const64 [k]` at the 64-bit integer shape of `f`'s mode. -/
def constArg (tabs : Tables) (f : Func) (u : Value) (i : Nat) (k : Int) : Bool :=
  match f.value? u.args[i]! with
  | some y => y.op == .Const64 && y.auxInt.toInt == k && y.args.size == 0 &&
      (shp f.lowered tabs y.type matches .int .w64)
  | none => false

/-- The aux constants of a bounds panic `w` with constant operands folded in are `f`'s operands
of the `PanicBounds` `u` it lowers (`pbLower`, `constArg`). Every other pair is unconstrained. -/
def pbConstOK (tabs : Tables) (f : Func) (u w : Value) : Bool :=
  !pbLower u w ||
    match pbConsts tabs w with
    | some l => l.all fun (i, k) => constArg tabs f u i k
    | none => false

/-- `RewriteCheck.atomsOK` with `atomPair` (and `pbConstOK`): the same entry, blocks and own aux; every atom of `g`
corresponds to an atom of `f`, the atoms only `f` has are droppable (`dropAtom`), and each block
evaluates `f`'s roots, atoms of `g`, in the same order (`Sem.schedule`; `g` may evaluate a lowered
`Zero`, which is not a root of lowered SSA, earlier). -/
def atomsOKL (tabs : Tables) (f g : Func) : Bool :=
  f.entry == g.entry && f.blocks == g.blocks && f.ownAux == g.ownAux &&
  f.blocks.all fun b =>
    match f.block? b, g.block? b with
    | some fb, some gb =>
      fb.id == gb.id &&
      let af := atomsOfL tabs f fb
      let ag := atomsOfL tabs g gb
      ag.all (fun x => af.contains x && match f.value? x, g.value? x with
        | some u, some w => atomPair tabs u w && pbConstOK tabs f u w
        | _, _ => false) &&
      af.all (fun x => ag.contains x || (f.value? x).any (dropAtom ·.op)) &&
      match Sem.schedule f fb, Sem.schedule g gb with
      | some of, some og =>
        of.toList.filter (fun x => (f.value? x).any (Sem.isRoot ·.op)) ==
          og.toList.filter (fun x => (f.value? x).any (Sem.isRoot ·.op) &&
            (g.value? x).any (fun w => !termVL tabs w))
      | _, _ => false
    | _, _ => false

/-- The listed terms' arguments by ID, the roots (controls and the listed atoms' arguments), and
the number of arguments of listed values (`RewriteCheck.liveInit` with `termVL`). -/
def liveInitL (tabs : Tables) (h : Func) : Array (Option (Array ID)) × List ID × Nat :=
  h.blocks.toList.foldl (init := (Array.replicate h.valueTab.size none, [], 0)) fun (T, R, n) b =>
    match h.block? b with
    | some hb =>
      hb.values.toList.foldl (init := (T, hb.controls.toList ++ R, n)) fun (T, R, n) x =>
        match h.value? x with
        | some u =>
          if termVL tabs u then (T.set! x (some u.args), R, n + u.args.size)
          else (T, u.args.toList ++ R, n + u.args.size)
        | none => (T, R, n)
    | none => (T, R, n)

/-- Marks of the values `h` reads (`liveOKL` checks them). -/
def liveMarksL (tabs : Tables) (h : Func) : Array Bool :=
  let (T, R, n) := liveInitL tabs h
  liveGo T (R.length + n + 1) R (Array.replicate h.valueTab.size false)

/-- The marks `L` hold the controls of `h`'s blocks, the arguments of its listed atoms, and the
arguments of its marked listed terms. -/
def liveOKL (tabs : Tables) (h : Func) (L : Array Bool) : Bool :=
  h.blocks.all fun b =>
    match h.block? b with
    | some hb =>
      hb.controls.all (fun c => L[c]? == some true) &&
      hb.values.all fun x => (h.value? x).all fun u =>
        (termVL tabs u && L[x]? != some true) || u.args.all fun a => L[a]? == some true
    | none => true

/-- The output's bounds panic `u` with constant operands at `x` keeps the other arguments of the
replayed `LoweredPanicBoundsRR` `m` (up to copies; `pbKeep`), with its type and auxint, and lowers
`f`'s `PanicBounds` at `x` (`pbLower`). -/
def pbFinal (tabs : Tables) (f : Func) (M : Defs) (n : Nat) (x : ID) (m u : Value) : Bool :=
  u.id == x && m.id == x && m.op == .ARM64LoweredPanicBoundsRR && u.type == m.type &&
    u.auxInt == m.auxInt && m.args.size == 3 && (f.value? x).any (pbLower · u) &&
    match pbKeep u.op with
    | some ks => u.args.size == ks.length &&
        (ks.zip u.args.toList).all fun (k, a') => copyReachL tabs M n m.args[k]! a'
    | none => false

/-- Every value listed in `g` has its replayed definition up to copies in its arguments (a bounds
panic with constant operands its replayed `LoweredPanicBoundsRR`'s, `pbFinal`), or is a
term `g` does not read; every block of `g` its replayed terminator (kind, auxint, successors as
the replay swapped them, controls up to copies). -/
def finalOKL (tabs : Tables) (f g : Func) (M : Defs) (B : BMapL) : Bool :=
  let n := M.size
  let L := liveMarksL tabs g
  liveOKL tabs g L &&
  g.blocks.all fun b =>
    match bstateL f B b, f.block? b, g.block? b with
    | some st, some fb, some gb =>
      gb.kind == st.kind && gb.auxInt == st.auxInt &&
      (if st.swapped then fb.succs.size == 2 && gb.succs == swapS fb.succs
       else gb.succs == fb.succs) &&
      gb.controls.size == st.ctrls.size &&
      (st.ctrls.toList.zip gb.controls.toList).all (fun (c, c') => copyReachL tabs M n c c') &&
      gb.values.all fun x =>
        match M.get? x, g.value? x with
        | some m, some u =>
          (u.id == x && m.id == x && u.op == m.op && u.type == m.type && u.auxInt == m.auxInt &&
            u.aux == m.aux && u.args.size == m.args.size &&
            (m.args.toList.zip u.args.toList).all fun (a, a') => copyReachL tabs M n a a') ||
          (termVL tabs u && L[x]? != some true) || pbFinal tabs f M n x m u
        | _, _ => false
    | _, _, _ => false

/-- The input's values have the same shape in both modes (`Sem.tyOfL` and Phase 1's `tyOf`), so
that `f`'s terms read in lowered mode refine their Phase 1 reading (`GoFV.Proof.Low.denL`). -/
def shapesOK (tabs : Tables) (f : Func) : Bool :=
  f.valueTab.all fun
    | some v => GoFV.Opt.CSE.tyEq (shpL tabs v.type) (tabs.ty v.type)
    | none => true

/-- **The validator**: `g` (the result of a lowering rewrite with table `t` on `f`, which logged
`log`) is related to `f` as `GoFV.Proof.Low.lower_refines` needs; `g` is lowered (`runL` reads it
in lowered mode) and `f` is lowered or has the same shapes in both modes. -/
def validateL (tabs : Tables) (t : Interp.Table) (f g : Func) (log : Array RwEvent) : Bool :=
  g.lowered && (f.lowered || shapesOK tabs f) &&
  atomsOKL tabs f g && closedOK f && closedOK g &&
  match replayL tabs t f f.valueTab [] log.toList with
  | some (M, B) => finalOKL tabs f g M B
  | none => false

/-! ## The checked pass -/

/-- `tabsAgree`, and every value of `f` has the same lowered shape in both tables (`Ctx.makeL`'s
`typeShapesL`): `f` runs alike under `runL` in both (`GoFV.Proof.Low.runL_tabsAgreeL`). -/
def tabsAgreeL (tabs tabs' : Tables) (f : Func) : Bool :=
  GoFV.Opt.tabsAgree tabs tabs' f &&
  f.valueTab.toList.all fun o =>
    Sem.Ty.beq (Sem.valueTy (Sem.typeShapesL tabs') o) (Sem.valueTy (Sem.typeShapesL tabs) o)

/-- `applyRewrite` with the lowering table `t` and its log; the result if the tables agree for
`f` (`tabsAgreeL`), both functions pass `check` and `validateL` accepts it, else `none`. -/
def checkedRunL (t : Interp.Table) (env : PassEnv) (f : Func) : Except String (Option PassOut) := do
  let (out, _, log) ← GoFV.Rules.rewriteRun t true true env f
  let ce : CheckEnv := { tabs := out.tables, typs := env.typs }
  return if tabsAgreeL env.tables out.tables f && checkOK { tabs := env.tables, typs := env.typs } f &&
      checkOK ce out.func && validateL out.tables t f out.func log then some out else none

/-- **The checked lowering pass** with table `t`: the validated result, else the input. -/
def checkedLowerWith (t : Interp.Table) : Pass := fun env f => do
  match ← checkedRunL t env f with
  | some out => return out
  | none => return { func := f, tables := env.tables }

end GoFV.Opt.LowerCheck
