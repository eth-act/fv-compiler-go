import GoFV.Proof.Low.RuleL
import GoFV.Opt.Lower

variable [GoFV.SSA.Sem.Addrs]

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
* a rule event of a strength-reduced multiplication by a constant (`ARM64.rules:1043`, `1044`,
  `Interp.mulResult`) is checked by its effect (`mulOKL`): the fresh values it built are linear
  combinations of the operand whose multiplier is the constant in the bits the `MUL` keeps
  (`mulCoef`); the replay adds them and the `MUL` as their `Copy`;
* a block rule event is checked by `blockOKL` against `BlockRuleL.Sound`: one control matched by
  the rule's control pattern, the block's auxint (tracked in `BStateL`) as the rule asks, the new
  control a rule variable or a node built on them, which the replay defines at its fresh value
  (`ctrlDefL`), the new auxint the rule's;
* atoms of `g` correspond to atoms of `f` by `atomPair`: the same fields, or an atom renamed by
  `renameOp` with the same type, auxint, aux and arguments' count, or a `Store` lowered to an
  arm64 store (`memLower`), or a `Zero` or `Move` lowered to `LoweredZero`/`LoweredZeroLoop` or
  `LoweredMove`/`LoweredMoveLoop` (`bulkLower`), or a `LocalAddr` lowered to `MOVDaddr`
  (`addrLower`), or a `Store` lowered to an indexed store (`idxLower`), or a `Zero` to an indexed
  store of `0` (`zeroIdxLower`); a rule event lowering a
  store, a `Zero`, a `Move` or a frame address, or folding an `ADDconst` offset (`stFold`) or a
  global symbol's or frame variable's `MOVDaddr` (`stFoldAddr`) into an arm64 store, or indexing
  an arm64 store at offset 0 without aux whose address is `ADD p i` or `ADDshiftLL [k] p i`
  (`stIdxFold`), or scaling such an indexed store's index `SLLconst [k] i` (`stIdxScale`), of a
  `Store` or of a single-store `Zero`, is replayed as its new definitions (`atomDef`); a rule
  event folding a lowered
  frame address into an integer load (a term) or into an `ADDconst` is replayed as the folded term
  (`frameFold`); one folding
  `ADDconst [0]` into the lowered frame address it reads (`650` at offset 0, whose result is an
  atom) is replayed as no change (`addrFoldEv`), and the later folds see through it (`frameAddr`);
  so is one lowering `OffPtr [off] SP` to `MOVDaddr [off] SP` (`305`, `spFoldEv`), which a store
  then folds as an offset (`stFold`) and a load replays as the folded load (`ldOffFold`);
* a rule event at an integer load of a read-only symbol (`ARM64.rules:1811-1817`, `roLoadRule`,
  which `ruleOKL` rejects) is replayed as the `MOVDconst` it builds when the load from the
  symbol's allocation alone gives its word (`roLoadDef`, only on an `f` whose values are generic
  memory-typed ops, `memTyAll`); the precondition pins the symbols `f`'s `Addr`s name on such an
  `f` (`RoImage` of `roPre`);
* a rule event folding a constant operand into a lowered bounds panic (`ARM64.rules:513-516`) is
  replayed as no change (`pbFoldEv`): the output's `LoweredPanicBounds{RC,CR,CC}` must keep the
  replayed `LoweredPanicBoundsRR`'s other arguments (`pbFinal`), and its aux constants are the
  `Const64` operands of `f`'s `PanicBounds` (`pbLower`, `pbConstOK`);
* each block evaluates `f`'s roots in the same order in `g` (a lowered `Zero` or `Move` is not a
  root of lowered SSA: `g` may evaluate it earlier, which never fails without faulting memory);
* copies are compatible at the lowered shapes (`copyCompatL`); the output's sign or zero extension
  or `W` op may also read the value a narrowing integer `Copy` of its replayed argument copies,
  when the `Copy` keeps the bits the op reads (`truncReachL`); phi eliminations and snapshots
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
    let σ := @sigmaL Sem.Addrs.fixed tabs e r.pat
    let nodes := match r.result, defs with
      | .build ns, _ :: us => ns.zip us
      | _, _ => []
    let or := oracleL vtys tabs ((r.cond.map (negAtoms false)).getD []) nodes
    let ev := evalE vtys σ or e (@Pat.denL Sem.Addrs.fixed tabs e [] r.pat)
    I.tail.all (·.2 != v) &&
    consOK ev σ e I [] r.pat && wfOK e [] r.pat &&
    (match r.cond with
      | some c => match ev c with | .bool true => true | _ => false
      | none => true) &&
    Pat.argsOK e.ty [] r.pat && Pat.topOKL (e.ty []) r.pat && argsOKLr r.loc e.ty r.pat &&
    resFitsL (e.ty []) r.result && Pat.addrOKL e.ty e.aux e.auxInt [] r.pat &&
    Pat.rangeL e.auxInt [] r.pat && leavesOK M I [] r.pat &&
    resultOKL tabs M e r.pat ev or σ I r x defs

/-- The built definitions of a `build` event with the arguments the rule gives its nodes (`argID`
on the binding of `r` at `v`), the other fields as logged. `lower` may give a node the source of
a narrowing `Copy` the rule binds (a truncation lowered to a `Copy`, eliminated inline by
`applyRewrite`): the replay keeps the rule's argument and `finalOKL` relates it to the output's
(`truncReachL`). Other results: `defs`. -/
def ruleDefsL (tabs : Tables) (M : Defs) (r : Rule) (v : ID) (defs : List Value) : List Value :=
  match r.result, defs, matchPatL tabs M r.pat [] v with
  | .build nodes, u0 :: us, some I =>
    let σ := @sigmaL Sem.Addrs.fixed tabs (envL tabs M I) r.pat
    let ids := us.map (·.id)
    u0 :: (nodes.zip us).map (fun (n, u) =>
      { u with args := (n.args.filterMap fun a => argID σ I ids a).toArray }) ++ us.drop nodes.length
  | _, _, _ => defs

/-- The rule event `(v, r, defs)` is a sound instance of one commutation choice of `r` on `M`
(`ArmRule.Sound`): the definitions to replay (`ruleDefsL` of that choice). The read-only-load
rules (`roLoadRule`) are rejected. -/
def ruleOKL (tabs : Tables) (M : Defs) (r : Rule) (v : ID) (defs : List Value) :
    Option (List Value) :=
  match M.get? v with
  | none => none
  | some x =>
    if termVL tabs x && x.id == v && !roLoadRule r then
      (choices (Pat.commutes r.pat)).findSome? fun sw =>
        let ds := ruleDefsL tabs M (Rule.swapC r sw) v defs
        if ruleOK1 tabs M (Rule.swapC r sw) v x ds then some ds else none
    else none

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

/-- The sign and zero extensions `MOV{B,H,W}{,U}reg` and the low bits of their argument they read
(`Arm64.ext`). -/
def extReadW : Op → Option Nat
  | .ARM64MOVBreg | .ARM64MOVBUreg => some 8
  | .ARM64MOVHreg | .ARM64MOVHUreg => some 16
  | .ARM64MOVWreg | .ARM64MOVWUreg => some 32
  | _ => none

/-- The `W` ops: `Arm64.evalPure` reads each argument as the low 32 bits of its register
(`Arm64.reg32`: `op1w`, `op2w`, `cmp1w`, `cmp2w`, `flags1w`, `flags2w`). -/
def w32Op : Op → Bool
  | .ARM64MULW | .ARM64MNEGW | .ARM64DIVW | .ARM64UDIVW | .ARM64MODW | .ARM64UMODW | .ARM64RORW
  | .ARM64RORWconst | .ARM64EXTRWconst | .ARM64CLZW | .ARM64RBITW | .ARM64REVW | .ARM64REV16W
  | .ARM64CMPW | .ARM64CMPWconst | .ARM64CMNW | .ARM64CMNWconst | .ARM64TSTW
  | .ARM64TSTWconst => true
  | _ => false

/-- The low bits of its argument `TSTWconst [c]` reads: up to `c`'s highest set bit (the `W`
register `&&& imm32 c`, `Arm64.evalPure`). -/
def tstReadW (c : Int64) : Nat := (Sem.Arm64.imm32 c).toNat.log2 + 1

/-- The low bits of argument `i` of `o` (auxint `ai`) that `o` reads, for the ops that read no
more: `TSTWconst [c]` its `tstReadW`, an extension its source width (`extReadW`, argument 0), a
`W` op 32 of each argument (`w32Op`). -/
def narrowReadW (o : Op) (ai : Int64) (i : Nat) : Option Nat :=
  if o == .ARM64TSTWconst then (if i == 0 then some (tstReadW ai) else none) else
  match extReadW o with
  | some k => if i == 0 then some k else none
  | none => if w32Op o then some 32 else none

/-- `b` reaches `a'` through at most `n` copies, each compatible (`copyCompatL`) or a narrowing
integer `Copy` of at least `k` and fewer than 64 bits: at an integer shape of `k` bits, `b` reads
as `a'` does (`(Trunc32to8 (Trunc64to32 x))`, both copies). -/
def narrowReachL (tabs : Tables) (M : Defs) : Nat → Nat → ID → ID → Bool
  | 0, _, b, w => b == w
  | n + 1, k, b, w =>
    b == w ||
    match M.get? b with
    | some x =>
      x.op == .Copy && x.args.size == 1 &&
      ((match M.get? x.args[0]! with
        | some y => copyCompatL (shpL tabs x.type) (shpL tabs y.type)
        | none => false) ||
       (match shpL tabs x.type with
        | .int w' => decide (k ≤ w'.bits) && w' != .w64
        | _ => false)) &&
      narrowReachL tabs M n k x.args[0]! w
    | none => false

/-- The value `a` of the replay is a `Copy` at an integer shape `int w` of at least `k` and fewer
than 64 bits (lowering a truncation, `(Trunc64to32 x) => x`), whose argument reaches `a'` through
at most `n` compatible or narrowing copies of at least `w` bits (`narrowReachL`): `a'` holds
`a`'s low `k` bits. -/
def truncFromL (tabs : Tables) (M : Defs) (n k : Nat) (a a' : ID) : Bool :=
  match M.get? a with
  | some c =>
    c.op == .Copy && c.args.size == 1 &&
      (match shpL tabs c.type with
        | .int w => decide (k ≤ w.bits) && w != .w64 && narrowReachL tabs M n w.bits c.args[0]! a'
        | _ => false)
  | none => false

/-- Argument `i` of the op `o` (auxint `ai`) in the replay is `a`, a narrowing `Copy` that keeps
the bits `o` reads of it (`narrowReadW`, `truncFromL`), and the output's is `a'`: `o` reads the
same bits of `a'` (`GoFV.Proof.Low.Val.op1_ext_retypeL`, `GoFV.Proof.Low.Val.w32_mono`,
`GoFV.Proof.Low.Val.tstw_retypeL`). `lower` eliminates such a copy inline (in an extension while
still generic, in a node a rule builds on it, `ruleDefsL`), which the replay follows when the
copy argument is replaced (`replayL`'s `copyArg`) and `finalOKL` accepts otherwise. -/
def truncReachL (tabs : Tables) (M : Defs) (n : Nat) (o : Op) (ai : Int64) (i : Nat) (a a' : ID) :
    Bool :=
  (narrowReadW o ai i).any fun k => truncFromL tabs M n k a a'

/-- The leading arguments of a lowered call that are no register pieces (`Sem.arm64Op`'s `call`):
none of `CALLstatic`, the closure's code and context of `CALLclosure`, the code of `CALLinter`. -/
def callLead : Op → Option Nat
  | .ARM64CALLstatic => some 0
  | .ARM64CALLclosure => some 2
  | .ARM64CALLinter => some 1
  | _ => none

/-- The input parameters of the ABI of the call `v` (`Sem.arm64Op`'s `call`). -/
def callIns (tabs : Tables) (v : Value) : List ABIParam :=
  ((Sem.callABI? tabs v.aux).map (·.params.toList.filter (!·.out))).getD []

/-- The leaf shapes `fitPieces` fits a call's register pieces at, in order (`none`: a piece it
keeps). -/
def fitTys (tabs : Tables) : List ABIParam → List (Option Sem.Ty)
  | [] => []
  | p :: ps =>
    if p.regs.isEmpty then fitTys tabs ps
    else (List.range p.regs.size).map (fun i => (Sem.leaves (tabs.ty p.type))[i]?.map (·.2)) ++
      fitTys tabs ps

/-- The shape the lowered call `v` fits its argument `i` at (`fitPieces`). -/
def callFitTy (tabs : Tables) (v : Value) (i : Nat) : Option Sem.Ty :=
  (callLead v.op).bind fun k => if i < k then none else ((fitTys tabs (callIns tabs v))[i - k]?).join

/-- The width of the value a narrow integer store writes (`MOVBstore`, `MOVHstore`, `MOVWstore`:
`Arm64.storeBytes` writes the low bytes of its register). -/
def stValW : Op → Option Sem.Width
  | .ARM64MOVBstore => some .w8
  | .ARM64MOVHstore => some .w16
  | .ARM64MOVWstore => some .w32
  | _ => none

/-- The width of the value a narrow indexed integer store writes (argument 2; `MOVBstoreidx`,
`MOVHstoreidx`, `MOVWstoreidx` and the scaled `MOVHstoreidx2`, `MOVWstoreidx4`). -/
def stIdxValW : Op → Option Sem.Width
  | .ARM64MOVBstoreidx => some .w8
  | .ARM64MOVHstoreidx | .ARM64MOVHstoreidx2 => some .w16
  | .ARM64MOVWstoreidx | .ARM64MOVWstoreidx4 => some .w32
  | _ => none

/-- The shape a narrow integer store reads its value (argument 1, `stValW`; argument 2 of an
indexed one, `stIdxValW`) at. -/
def stFitTy (o : Op) (i : Nat) : Option Sem.Ty :=
  if i == 1 then (stValW o).map .int else if i == 2 then (stIdxValW o).map .int else none

/-- The shape the atom `v` reads its argument `i` at, for the atoms that read no more of it: a
lowered call the leaf it fits the register piece at (`callFitTy`, `fitPieces`), a narrow integer
store its value's width (`stFitTy`). -/
def atomFitTy (tabs : Tables) (v : Value) (i : Nat) : Option Sem.Ty :=
  match callLead v.op with
  | some _ => callFitTy tabs v i
  | none => stFitTy v.op i

/-- The shape the value `v` reads its argument `i` at, for the values that read no more of it: an
atom's `atomFitTy`, a `Phi` its own shape, a `MakeResult` its result's (`Val.retypeL` of the
value's shape). -/
def argFitTy (tabs : Tables) (v : Value) (i : Nat) : Option Sem.Ty :=
  if v.op == .Phi then some (shpL tabs v.type)
  else if v.op == .MakeResult then
    match shpL tabs v.type with
    | .tuple ts => ts[i]?
    | _ => none
  else atomFitTy tabs v i

/-- Argument `i` of the atom `v` in the replay is `a`, a narrowing `Copy` keeping the bits of the
integer shape `v` reads the argument at (`argFitTy`, `truncFromL`), and the output's is `a'`: `v`
reads the same bits (`GoFV.Proof.Low.Val.fitPiece_retypeL`). -/
def truncFitL (tabs : Tables) (M : Defs) (n : Nat) (v : Value) (i : Nat) (a a' : ID) : Bool :=
  match argFitTy tabs v i with
  | some (.int w) => truncFromL tabs M n w.bits a a'
  | _ => false

/-- The ops whose value at a narrow integer shape `int w` (`w < 64`) is a function of the low `w`
bits of their first `d` arguments' registers when none is a pointer (`Arm64.evalPure`: `op1`/`op2`
of a ring or bitwise operation, `ADD`/`SUB`/`addK` on registers, the operands `CSEL` selects),
with `d` (the others, `CSEL`'s flags, read whole). -/
def lowOpArgs : Op → Option Nat
  | .ARM64ADD | .ARM64SUB | .ARM64MUL | .ARM64MNEG | .ARM64AND | .ARM64OR | .ARM64XOR | .ARM64BIC
  | .ARM64CSEL => some 2
  | .ARM64ADDconst | .ARM64SUBconst | .ARM64NEG | .ARM64MVN | .ARM64ANDconst | .ARM64ORconst
  | .ARM64XORconst => some 1
  | _ => none

/-- The low bits `m` reads of its first `d` arguments (`lowOpArgs`): `m` is at a narrow integer
shape `int w`, and each of those arguments has a narrow integer shape in `M` (so none is a
pointer). -/
def lowShape (tabs : Tables) (M : Defs) (m : Value) : Option Nat :=
  match shpL tabs m.type, lowOpArgs m.op with
  | .int w, some d =>
    if w != .w64 && d ≤ m.args.size && (List.range d).all (fun j =>
        (M.get? m.args[j]!).any fun y =>
          match shpL tabs y.type with
          | .int w' => w' != .w64
          | _ => false) then some w.bits
    else none
  | _, _ => none

/-- Argument `j` of `m` in the replay is `a`, one of the arguments `m` reads the low bits of
(`lowShape`), a narrowing `Copy` keeping those bits (`truncFromL`), and the output's is `a'`. -/
def lowReachL (tabs : Tables) (M : Defs) (n : Nat) (m : Value) (j : Nat) (a a' : ID) : Bool :=
  (lowShape tabs M m).any fun k => decide (j < (lowOpArgs m.op).getD 0) && truncFromL tabs M n k a a'

/-! ## Atom events -/

/-- The atom `u` folds the address `ADDconst [k2] b` of the arm64 store `x` (`x`'s argument 0 in
`M`, a term at a word shape) into its offset (`(MOV…store [k1] {sym} (ADDconst [k2] ptr) val mem)
=> (MOV…store [k1+int32(k2)] {sym} ptr val mem)`, `ARM64.rules:758-776`), or the address
`OffPtr [k2] b` (`305`'s `MOVDaddr [k2] SP`, replayed as no change, `spFoldEv`, folded by `893` and
the other stores of `881-905` without a symbol): the same op and type, no aux, `b` for the
address, the offset `k1 + k2`, all three offsets small and non-negative (`offOK`). -/
def stFold (tabs : Tables) (M : Defs) (x u : Value) : Bool :=
  (stSize x.op).isSome && u.op == x.op && u.type == x.type && x.aux == none && u.aux == none &&
  x.args.size == 3 && offOK x.auxInt && offOK u.auxInt &&
  match M.get? x.args[0]! with
  | some y =>
    (y.op == .ARM64ADDconst || y.op == .OffPtr) && termVL tabs y && y.args.size == 1 &&
      wordShape (shpL tabs y.type) && offOK y.auxInt &&
      u.auxInt.toInt == x.auxInt.toInt + y.auxInt.toInt &&
      u.args == #[y.args[0]!, x.args[1]!, x.args[2]!]
  | none => false

/-- The value `p` of `M` is a lowered frame address: the atom `m` (`MOVDaddr {sym}` at offset 0) at
`a = p`, or a term `ADDconst [0]` at a word shape of the atom `m` at `a` (`650` at offset 0, which
the replay keeps unchanged, `addrFoldEv`). -/
def frameAddr (tabs : Tables) (M : Defs) (p : ID) : Option (ID × Value) :=
  match M.get? p with
  | some y =>
    if y.op == .ARM64MOVDaddr && !termVL tabs y then some (p, y)
    else if y.op == .ARM64ADDconst && y.auxInt == 0 && termVL tabs y &&
        wordShape (shpL tabs y.type) && y.args.size == 1 then
      match y.args[0]? with
      | some a =>
        match M.get? a with
        | some m => if m.op == .ARM64MOVDaddr && !termVL tabs m then some (a, m) else none
        | none => none
      | none => none
    else none
  | none => none

/-- The atom `u` folds the address `MOVDaddr [k2] {sym} b` of the arm64 store `x` (`x`'s argument
0 in `M`) into its offset and aux (`(MOV…store [k1] {sym1} (MOVDaddr [k2] {sym2} ptr) val mem) &&
canMergeSym(sym1,sym2) … => (MOV…store [k1+k2] {mergeSym(sym1,sym2)} ptr val mem)`,
`ARM64.rules:881-905`): the same op and type, `x` without aux, `u` with the `MOVDaddr`'s, `b` for
the address, the offset `k1 + k2` (`k1` and the sum small and non-negative, `offOK`); the
`MOVDaddr` either a term (a global symbol, at a word shape) or the lowered frame address
(`frameAddr`, offset 0) of the `LocalAddr` of `f` at its ID with the same aux (a frame variable). -/
def stFoldAddr (tabs : Tables) (f : Func) (M : Defs) (x u : Value) : Bool :=
  (stSize x.op).isSome && u.op == x.op && u.type == x.type && x.aux == none &&
  x.args.size == 3 && offOK x.auxInt && offOK u.auxInt &&
  ((match M.get? x.args[0]! with
    | some m =>
      m.op == .ARM64MOVDaddr && m.args.size == 1 && m.aux.isSome && u.aux == m.aux &&
        u.auxInt.toInt == x.auxInt.toInt + m.auxInt.toInt &&
        u.args == #[m.args[0]!, x.args[1]!, x.args[2]!] &&
        termVL tabs m && wordShape (shpL tabs m.type)
    | none => false) ||
   match frameAddr tabs M x.args[0]! with
   | some (a, m) =>
     m.args.size == 1 && m.aux.isSome && u.aux == m.aux && u.auxInt == x.auxInt &&
       u.args == #[m.args[0]!, x.args[1]!, x.args[2]!] &&
       (f.value? a).any fun l => l.op == .LocalAddr && l.aux == m.aux
   | none => false)

/-- The scale of an index shifted left by `k` in `ADDshiftLL [k] ptr idx` that an indexed store
takes (`ARM64.rules:806-808`). -/
def idxShift (k : Int64) : Option Nat :=
  if k == 1 then some 2 else if k == 2 then some 4 else if k == 3 then some 8 else none

/-- The atom `u` indexes the arm64 store `x` (offset 0, no aux) whose address (`x`'s argument 0
in `M`) is the term `ADD ptr idx` or `ADDshiftLL [k] ptr idx` at a word shape (`(MOV…store [off]
{sym} (ADD ptr idx) val mem) && off == 0 && sym == nil => (MOV…storeidx ptr idx val mem)`,
`ARM64.rules:786-791`; `ADDshiftLL [3]`, `[2]`, `[1]` to `MOVDstoreidx8`, `MOVWstoreidx4`,
`MOVHstoreidx2`, `806-808`): `u` indexes `x`'s op (`idxStore`) at the scale 1 or `2^k`
(`idxShift`), with `x`'s type, no offset or aux, and the arguments `ptr idx val mem`. -/
def stIdxFold (tabs : Tables) (M : Defs) (x u : Value) : Bool :=
  (stSize x.op).isSome && u.type == x.type && x.auxInt == 0 && x.aux == none && u.auxInt == 0 &&
  u.aux == none && x.args.size == 3 &&
  match M.get? x.args[0]!, idxStore u.op with
  | some y, some (o, s) =>
    o == x.op && termVL tabs y && y.args.size == 2 && wordShape (shpL tabs y.type) &&
      (y.op == .ARM64ADD && s == 1 || y.op == .ARM64ADDshiftLL && idxShift y.auxInt == some s) &&
      u.args == #[y.args[0]!, y.args[1]!, x.args[1]!, x.args[2]!]
  | _, _ => false

/-- The atom `u` scales the index of the indexed store `x` at the scale 1 (no offset or aux) whose
index (`x`'s argument 1 in `M`) is the term `SLLconst [k] idx` at a word shape (`(MOVDstoreidx ptr
(SLLconst [3] idx) val mem) => (MOVDstoreidx8 ptr idx val mem)`, `ARM64.rules:809`; `MOVWstoreidx`
by `[2]` to `MOVWstoreidx4`, `810`): `u` indexes the arm64 store `x` indexes (`idxStore`) at the
scale `2^k` (`idxShift`), with `x`'s type, no offset or aux, and the arguments `ptr idx val mem`. -/
def stIdxScale (tabs : Tables) (M : Defs) (x u : Value) : Bool :=
  u.type == x.type && x.auxInt == 0 && x.aux == none && u.auxInt == 0 && u.aux == none &&
  x.args.size == 4 &&
  match idxStore x.op, idxStore u.op, M.get? x.args[1]! with
  | some (o, 1), some (o', s), some y =>
    o' == o && termVL tabs y && y.op == .ARM64SLLconst && y.args.size == 1 &&
      wordShape (shpL tabs y.type) && idxShift y.auxInt == some s &&
      u.args == #[x.args[0]!, y.args[0]!, x.args[2]!, x.args[3]!]
  | _, _, _ => false

/-- The position of a narrow integer store's value: 1 (`stValW`), 2 for an indexed one
(`stIdxValW`). -/
def stValIx (o : Op) : Option Nat :=
  if (stValW o).isSome then some 1 else if (stIdxValW o).isSome then some 2 else none

/-- The store `u` a rule event builds at the store `x` (both atoms), with its value (`stValIx`)
read back as `x`'s (argument 1) where `u` reads it through a narrowing `Copy` that `lower`
eliminated inline (`(Trunc64to32 x) => x`, a copy argument replacement `copyReachL` cannot
follow): the source of `x`'s narrowing `Copy` of at least the store's width (`truncFitL` at
`stFitTy`). The replay keeps the `Copy`; `finalOKL` relates the output's value to it
(`truncFitL`). -/
def stValPick (tabs : Tables) (M : Defs) (x u : Value) : Value :=
  match stValIx u.op with
  | some k =>
    if x.args.size == 3 && k < u.args.size && truncFitL tabs M M.size u k x.args[1]! u.args[k]! then
      { u with args := u.args.set! k x.args[1]! }
    else u
  | none => u

/-- The atom `u` folds the address of the 128-bit store `x` lowering a `Move` (`moveDef`), or of
the store `x` lowering a `Zero` (`zeroDef`, `zStore`), into its offset and aux, as `stFold` and
`stFoldAddr` do for a store lowering a `Store`: `ADDconst [k2] b` or `OffPtr [k2] b` into the
offset (`ARM64.rules:757`-`770`, `779`, `782`), a global symbol's `MOVDaddr [k2] {sym} b` into the
offset and aux (`879`-`897`, `909`, `913`), or a frame variable's lowered address (`frameAddr`) into
the aux; `b` for the address, the other arguments kept, all offsets small and non-negative
(`offOK`). -/
def qFold (tabs : Tables) (f : Func) (M : Defs) (x u : Value) : Bool :=
  (qStore x.op || zStore x.op) && u.op == x.op && u.type == x.type && x.aux == none &&
    decide (3 ≤ x.args.size) &&
    offOK x.auxInt && offOK u.auxInt &&
    ((match M.get? x.args[0]! with
      | some y =>
        (y.op == .ARM64ADDconst || y.op == .OffPtr) && termVL tabs y && y.args.size == 1 &&
            wordShape (shpL tabs y.type) && offOK y.auxInt && u.aux == none &&
            u.auxInt.toInt == x.auxInt.toInt + y.auxInt.toInt &&
            u.args == x.args.set! 0 y.args[0]! ||
          y.op == .ARM64MOVDaddr && y.args.size == 1 && y.aux.isSome && u.aux == y.aux &&
            u.auxInt.toInt == x.auxInt.toInt + y.auxInt.toInt &&
            u.args == x.args.set! 0 y.args[0]! && termVL tabs y && wordShape (shpL tabs y.type)
      | none => false) ||
     match frameAddr tabs M x.args[0]! with
     | some (a, m) =>
       m.args.size == 1 && m.aux.isSome && u.aux == m.aux && u.auxInt == x.auxInt &&
         u.args == x.args.set! 0 m.args[0]! &&
         (f.value? a).any fun l => l.op == .LocalAddr && l.aux == m.aux
     | none => false)

/-- `atomDef` for one new definition `u` at the atom `x` at `v`. -/
def atomDef1 (tabs : Tables) (f : Func) (M : Defs) (v : ID) (x u : Value) :
    Option (Value × Option Value) :=
  if x.id == v && u.id == v && !termVL tabs x && !termVL tabs u && u.type == x.type &&
      (u.args == x.args && memLower tabs x u && u.auxInt == 0 && u.aux == none ||
        u.args == x.args && bulkLower x u ||
        u.args.all x.args.contains && addrLower tabs x u ||
        (stFold tabs M x u || stFoldAddr tabs f M x u || stIdxFold tabs M x u) &&
          (f.value? v).any (·.op == .Store) ||
        stIdxScale tabs M x u && (f.value? v).any (fun a => a.op == .Store && a.args.size == 3) ||
        (stIdxFold tabs M x u || stIdxScale tabs M x u) &&
          (f.value? v).any (fun a => a.op == .Zero && a.args.size == 2 && (zeroOp a.auxInt).isSome) ||
        qFold tabs f M x u && match f.value? v with
          | some a =>
            a.op == .Move && qStore x.op || a.op == .Zero && a.args.size == 2 && zStore x.op
          | none => qStore x.op || zStore x.op)
    then some (u, none)
  else none

/-- A rule event at the atom `v` replayed as the atom its top result node `u` defines (the log
lists the reset value, then the nodes, as for any `build`), with `v`'s type, a narrow store's
value read back through the narrowing `Copy` `lower` eliminated (`stValPick`):
* a lowered store (`memLower` at offset 0 without aux: `(Store {t} ptr val mem) => (MOVDstore ptr
  val mem)` and the other sizes), on `v`'s arguments;
* a lowered `Zero` or `Move` (`bulkLower`: `LoweredZero`, `LoweredZeroLoop`, `LoweredMove`,
  `LoweredMoveLoop`), on `v`'s arguments;
* an offset folded into an arm64 store lowering a `Store` of `f` (`stFold`), or a global symbol's
  or frame variable's address (`stFoldAddr`), or the store indexed (`stIdxFold`), or the index of
  such an indexed store scaled (`stIdxScale`);
* the store of `0` lowering a `Zero [n]` of `f` (two arguments, `zeroOp n` a single store, so not
  the outer of two) indexed (`stIdxFold`), or its index scaled (`stIdxScale`): paired with the
  `Zero` by `zeroIdxLower`;
* a lowered frame address (`addrLower`): `(LocalAddr {sym} base _) => (MOVDaddr {sym} base)` on
  some of `v`'s arguments, or `(MOVDaddr {sym} (SPanchored base mem))`, whose second node `s` is a
  fresh term on some of `v`'s arguments (`u` reads no argument, `argFree`).
The new definitions: `u` and the fresh term, if any. -/
def atomDef (tabs : Tables) (f : Func) (M : Defs) (v : ID) (defs : List Value) :
    Option (Value × Option Value) :=
  match M.get? v, defs with
  | some x, [_, u] => atomDef1 tabs f M v x (stValPick tabs M x u)
  | some x, [_, u, s] =>
    if x.id == v && u.id == v && !termVL tabs x && !termVL tabs u && u.type == x.type &&
        addrLower tabs x u && u.args == #[s.id] && s.id != v && (M.get? s.id).isNone &&
        termVL tabs s && s.args.all x.args.contains then some (u, some s)
    else none
  | _, _ => none

/-- A load term `l` of `x`'s source and memory (arguments 1 and 2) at offset 0 without aux, at a
fresh ID of `M` other than `v`. -/
def moveLd (tabs : Tables) (M : Defs) (v : ID) (x l : Value) : Bool :=
  l.auxInt == 0 && l.aux == none && l.args == #[x.args[1]!, x.args[2]!] && l.id != v &&
    (M.get? l.id).isNone && termVL tabs l

/-- A selector `s` (`o`, offset 0, no aux) of `p`, a `Vec128` at a fresh ID of `M` other than
`v`. -/
def moveSel (tabs : Tables) (M : Defs) (v : ID) (o : Op) (p s : Value) : Bool :=
  s.op == o && s.args == #[p.id] && s.auxInt == 0 && s.aux == none && s.id != v &&
    (M.get? s.id).isNone && termVL tabs s && Sem.Ty.beq (shpL tabs s.type) (.blob 16)

/-- A rule event at the `Move [16]` or `Move [32]` `x` at `v` (a `Move` in `f`) lowering it to a
128-bit copy (`ARM64.rules:418`, `426`; `moveQOp`), replayed as its new definitions: the 128-bit
store `u` at `v` (`x`'s type, offset 0, no aux) on `x`'s destination and memory, whose values are
fresh load terms of `x`'s source and memory (`moveLd`) at their lowered shapes: an `FMOVQload` (a
`Vec128`) for `FMOVQstore`, `Select0` and `Select1` (`moveSel`) of one `FLDPQ` (a pair of
`Vec128`s) for `FSTPQ`. The result is `u` and the fresh terms, each after those it reads. -/
def moveDef (tabs : Tables) (f : Func) (M : Defs) (v : ID) (defs : List Value) :
    Option (Value × List Value) :=
  match M.get? v, defs with
  | some x, _ :: u :: rest =>
    if x.id == v && u.id == v && x.op == .Move && x.args.size == 3 && !termVL tabs x &&
        !termVL tabs u && u.type == x.type && u.auxInt == 0 && u.aux == none &&
        (rest.map (·.id)).Nodup &&
        (f.value? v).any (fun a => a.op == .Move && a.auxInt == x.auxInt) then
      match moveQOp x.auxInt, rest with
      | some (o, _), [l] =>
        if o == .ARM64FMOVQstore && u.op == o && l.op == .ARM64FMOVQload && moveLd tabs M v x l &&
            Sem.Ty.beq (shpL tabs l.type) (.blob 16) &&
            u.args == #[x.args[0]!, l.id, x.args[2]!] then some (u, [l]) else none
      | some (o, _), [s0, p, s1] =>
        if o == .ARM64FSTPQ && u.op == o && p.op == .ARM64FLDPQ && moveLd tabs M v x p &&
            Sem.Ty.beq (shpL tabs p.type) (.tuple [.blob 16, .blob 16]) &&
            moveSel tabs M v .Select0 p s0 && moveSel tabs M v .Select1 p s1 &&
            u.args == #[x.args[0]!, s0.id, s1.id, x.args[2]!] then some (u, [p, s0, s1])
        else none
      | _, _ => none
    else none
  | _, _ => none

/-- A load term `l` of `x`'s source and memory (arguments 1 and 2) at offset `k` without aux, at a
fresh ID of `M` other than `v` (`moveLd` at an offset). -/
def moveLdK (tabs : Tables) (M : Defs) (v : ID) (x l : Value) (k : Int64) : Bool :=
  l.auxInt == k && l.aux == none && l.args == #[x.args[1]!, x.args[2]!] && l.id != v &&
    (M.get? l.id).isNone && termVL tabs l

/-- The value nodes `ns` of a 128-bit store `o` copying `x`'s source in its memory at offset `k`
(`moveDef`'s, at an offset): an `FMOVQload [k]` (a `Vec128`) for `FMOVQstore`; `Select0` and
`Select1` (`moveSel`) of an `FLDPQ [k]` (a pair of `Vec128`s) for `FSTPQ`; fresh load terms
(`moveLdK`). The IDs of the values, and the nodes each after those it reads. -/
def qVals (tabs : Tables) (M : Defs) (v : ID) (x : Value) (o : Op) (k : Int64) :
    List Value → Option (List ID × List Value)
  | [l] =>
    if o == .ARM64FMOVQstore && l.op == .ARM64FMOVQload && moveLdK tabs M v x l k &&
        Sem.Ty.beq (shpL tabs l.type) (.blob 16) then some ([l.id], [l]) else none
  | [s0, p, s1] =>
    if o == .ARM64FSTPQ && p.op == .ARM64FLDPQ && moveLdK tabs M v x p k &&
        Sem.Ty.beq (shpL tabs p.type) (.tuple [.blob 16, .blob 16]) &&
        moveSel tabs M v .Select0 p s0 && moveSel tabs M v .Select1 p s1 then
      some ([s0.id, s1.id], [p, s0, s1])
    else none
  | _ => none

/-- The number of value nodes of the 128-bit store `o` (`qVals`). -/
def qNodes (o : Op) : Nat := if o == .ARM64FMOVQstore then 1 else 3

/-- A rule event at the `Move [s]` `x` at `v` (a `Move` in `f`) lowering it to two 128-bit stores
(`ARM64.rules:423`, `431`, `434`; `moveQ2Op`), replayed as its new definitions: the outer store
`u` at `v` (`x`'s type, offset `q2Off s`, no aux) on `x`'s destination, values copying `x`'s
source at that offset (`qVals`) and the inner store `w`; `w` (`x`'s type, an atom at a fresh ID
`f` does not define, offset 0, no aux) on `x`'s destination, values copying the source from
offset 0 and `x`'s memory. The log lists the nodes in pre-order: the outer store's values, `w`,
`w`'s values; each is fresh where the replay puts it. The result is `u`, the fresh terms and
`w`. -/
def moveDef2 (tabs : Tables) (f : Func) (M : Defs) (v : ID) (defs : List Value) :
    Option (Value × List Value × Value) :=
  match M.get? v, defs with
  | some x, _ :: u :: rest =>
    if x.id == v && u.id == v && x.op == .Move && x.args.size == 3 && !termVL tabs x &&
        !termVL tabs u && u.type == x.type && u.aux == none &&
        (rest.map (·.id)).Nodup &&
        (f.value? v).any (fun a => a.op == .Move && a.auxInt == x.auxInt) then
      match moveQ2Op x.auxInt, rest.drop (qNodes u.op) with
      | some (oo, _, oi, _), w :: ins =>
        let k : Int64 := Int64.ofNat (q2Off x.auxInt)
        match qVals tabs M v x oo k (rest.take (qNodes u.op)) with
        | some (os, ons) =>
          let M1 := ons.foldl (fun M s => M.put s.id s) M
          match qVals tabs M1 v x oi 0 ins with
          | some (is, ins') =>
            if u.op == oo && u.auxInt == k && w.op == oi && w.auxInt == 0 && w.aux == none &&
                w.type == x.type && !termVL tabs w && w.id != v &&
                ((ins'.foldl (fun M s => M.put s.id s) M1).get? w.id).isNone &&
                (f.value? w.id).isNone &&
                w.args == #[x.args[0]!] ++ is.toArray ++ #[x.args[2]!] &&
                u.args == #[x.args[0]!] ++ os.toArray ++ #[w.id] then
              some (u, ons ++ ins', w)
            else none
          | none => none
        | none => none
      | _, _ => none
    else none
  | _, _ => none

/-- A fresh `MOVDconst [0]` term `c` (no aux or arguments) at a fresh ID of `M` other than `v`, at
the 64-bit integer shape: the value of the stores lowering a `Zero` (`zeroDef`, `zeroDef2`). -/
def zConst (tabs : Tables) (M : Defs) (v : ID) (c : Value) : Bool :=
  c.op == .ARM64MOVDconst && c.auxInt == 0 && c.aux == none && c.args.size == 0 && c.id != v &&
    (M.get? c.id).isNone && termVL tabs c && Sem.Ty.beq (shpL tabs c.type) (.int .w64)

/-- A rule event at the `Zero [n]` `x` at `v` (a `Zero` in `f`) lowering it to a store of `0`
(`ARM64.rules:336`, `337`, `338`, `351`, `373`; `zeroOp`), replayed as its new definitions: the
store `u` at `v` (`x`'s type, offset 0, no aux) on `x`'s pointer and memory, whose values (one, or
two for `STP`) are the fresh term `c` (`zConst`). The result is `u` and `c`. -/
def zeroDef (tabs : Tables) (f : Func) (M : Defs) (v : ID) (defs : List Value) :
    Option (Value × Value) :=
  match M.get? v, defs with
  | some x, [_, u, c] =>
    if x.id == v && u.id == v && x.op == .Zero && x.args.size == 2 && !termVL tabs x &&
        !termVL tabs u && u.type == x.type && u.auxInt == 0 && u.aux == none &&
        zConst tabs M v c &&
        (f.value? v).any (fun a => a.op == .Zero && a.auxInt == x.auxInt) then
      match zeroOp x.auxInt with
      | some (o, k) =>
        if u.op == o && u.args == (if k == 3 then #[x.args[0]!, c.id, x.args[1]!]
            else #[x.args[0]!, c.id, c.id, x.args[1]!]) then some (u, c)
        else none
      | none => none
    else none
  | _, _ => none

/-- A rule event at the `Zero [n]` `x` at `v` (a `Zero` in `f`) lowering it to two stores of `0`
(`ARM64.rules:339`-`370`; `zero2Op`), replayed as its new definitions: the outer store `u` at `v`
(`x`'s type, the outer offset, no aux) on `x`'s pointer, the fresh term `c` (`zConst`) and the
inner store `w`; `w` (`x`'s type, an atom at a fresh ID `f` does not define, offset 0, no aux) on
`x`'s pointer, `c` and `x`'s memory. The log lists the nodes in pre-order: `u`, `c`, `w`. The
result is `u`, `c` and `w`. -/
def zeroDef2 (tabs : Tables) (f : Func) (M : Defs) (v : ID) (defs : List Value) :
    Option (Value × Value × Value) :=
  match M.get? v, defs with
  | some x, [_, u, c, w] =>
    if x.id == v && u.id == v && x.op == .Zero && x.args.size == 2 && !termVL tabs x &&
        !termVL tabs u && u.type == x.type && u.aux == none && zConst tabs M v c &&
        (f.value? v).any (fun a => a.op == .Zero && a.auxInt == x.auxInt) then
      match zero2Op x.auxInt with
      | some (oo, k, oi) =>
        if u.op == oo && u.auxInt == Int64.ofNat k && w.op == oi && w.auxInt == 0 &&
            w.aux == none && w.type == x.type && !termVL tabs w && w.id != v && w.id != c.id &&
            (M.get? w.id).isNone && (f.value? w.id).isNone &&
            w.args == #[x.args[0]!, c.id, x.args[1]!] && u.args == #[x.args[0]!, c.id, w.id] then
          some (u, c, w)
        else none
      | none => none
    else none
  | _, _ => none

/-- A rule event at the term `x` at `v` replayed as the term `u` that folds `x`'s address
argument, a lowered frame address (`frameAddr`: the atom `MOVDaddr {sym} b` at offset 0 of a
`LocalAddr {sym}` of `f`, or `ADDconst [0]` of it), into its aux, with `x`'s type and offset (small
and non-negative, `offOK`), `u` with the `MOVDaddr`'s aux and `b` for the address:
* a load without aux, an integer one (`(MOV…load [off1] {sym1} (MOVDaddr [off2] {sym2} ptr) mem) &&
  canMergeSym(sym1,sym2) … => (MOV…load [off1+off2] {mergeSym(sym1,sym2)} ptr mem)`,
  `ARM64.rules:832-856`) or a 128-bit one (`FMOVQload`, `FLDPQ`: `870`, `874`; `ldAny`; an `FLDPQ`'s
  second half at a small offset too), the same op;
* an `ADDconst` at a word shape (`(ADDconst [off1] (MOVDaddr [off2] {sym} ptr)) && … =>
  (MOVDaddr [int32(off1)+off2] {sym} ptr)`, `650`), a `MOVDaddr` term.

`x` without arguments is rejected before its address argument is read (no panic default). -/
def frameFold (tabs : Tables) (f : Func) (M : Defs) (v : ID) (defs : List Value) :
    Option Value :=
  match M.get? v, defs with
  | some x, [_, u] =>
    match x.args[0]? with
    | none => none
    | some p =>
    match frameAddr tabs M p with
    | some (a, m) =>
      if x.id == v && u.id == v && u.type == x.type && u.auxInt == x.auxInt && offOK x.auxInt &&
          termVL tabs x && termVL tabs u && m.args.size == 1 && u.aux == m.aux &&
          (f.value? a).any (fun l => l.op == .LocalAddr && l.aux == m.aux) &&
          (ldAny x.op && (ldQ? x.op != some 32 || offOK (x.auxInt + Int64.ofNat 16)) &&
              u.op == x.op && x.aux == none && x.args.size == 2 &&
              u.args == #[m.args[0]!, x.args[1]!] ||
            x.op == .ARM64ADDconst && u.op == .ARM64MOVDaddr && x.args.size == 1 &&
              wordShape (shpL tabs x.type) && u.args == #[m.args[0]!])
      then some u else none
    | none => none
  | _, _ => none

/-- A rule event at the integer load `x` at `v` (no aux) whose address is `OffPtr [k2] b` in `M`
(`305`'s `MOVDaddr [k2] SP`, replayed as no change, `spFoldEv`) replayed as the load `u` of `b` at
offset `k1 + k2` (`(MOV…load [off1] {sym1} (MOVDaddr [off2] {sym2} ptr) mem) && canMergeSym(sym1,sym2)
… => (MOV…load [off1+off2] {mergeSym(sym1,sym2)} ptr mem)`, `ARM64.rules:832-856`, without a
symbol): the same op and type, the `OffPtr` a term at a word shape on a value of `M`, all three
offsets small and non-negative (`offOK`). -/
def ldOffFold (tabs : Tables) (M : Defs) (v : ID) (defs : List Value) : Option Value :=
  match M.get? v, defs with
  | some x, [_, u] =>
    match x.args[0]? with
    | none => none
    | some p =>
    match M.get? p with
    | some y =>
      if x.id == v && u.id == v && u.op == x.op && u.type == x.type && (ldOp? x.op).isSome &&
          x.aux == none && u.aux == none && x.args.size == 2 && offOK x.auxInt &&
          offOK u.auxInt && y.op == .OffPtr && termVL tabs y && y.args.size == 1 &&
          wordShape (shpL tabs y.type) && offOK y.auxInt &&
          u.auxInt.toInt == x.auxInt.toInt + y.auxInt.toInt && u.args == #[y.args[0]!, x.args[1]!] &&
          (M.get? y.args[0]!).isSome
      then some u else none
    | none => none
  | _, _ => none

/-- A value whose shape may hold a memory is a memory op or of `memFreeOps`, and no write-barrier
op: `WBCheck.memTyOK`'s condition on one value. -/
def memTyV (tabs : Tables) (v : Value) : Bool :=
  v.op != .WB && v.op != .WBend && v.op != .StoreWB && v.op != .MoveWB && v.op != .ZeroWB &&
    (WBCheck.memFree (tabs.ty v.type) || WBCheck.memOpOK v.op ||
      WBCheck.memFreeOps.contains v.op)

/-- Every value of `f`'s table (listed or not) is a generic op passing `memTyV`: then `f` runs as
Phase 1's `run` and every memory its run holds keeps the read-only symbols of its precondition
(`GoFV.Proof.MemInv`, `WBCheck.memTyOK`). -/
def memTyAll (tabs : Tables) (f : Func) : Bool :=
  f.valueTab.all fun o => o.all fun v => v.op.generic && memTyV tabs v

/-- The read-only symbols `GoFV.Proof.Low.lower_refines`'s precondition pins for `f`: those its
`Addr`s name (`RewriteCheck.roSyms`) when `roLoadDef` may replay a load of `f` (`memTyAll`), else
none. -/
def roPre (tabs : Tables) (f : Func) : List (String × Sem.Alloc) :=
  if memTyAll tabs f then roSyms tabs f else []

/-- The 64-bit register word an `n`-byte integer load (`signed`, `Arm64.loadN`) at offset `o` of
the global `name` reads from its allocation `a` alone, at `Addrs.fixed` (if the allocation holds
no frame pointer, so that every address assignment reads it alike, `Mem.load_agree`): `some none`
if the load gives `poison` (out of the allocation), `some (some x)` for the word `x`, `none`
otherwise (a pointer the register would hold). -/
def roLoadWord (name : String) (a : Sem.Alloc) (n : Nat) (signed : Bool) (o : BitVec 64) :
    Option (Option (BitVec 64)) :=
  let m := ({} : Sem.Mem).set (.global name) a
  if m.lowB then
    match @Sem.Arm64.loadN Sem.Addrs.fixed .other n signed m ⟨.global name, o⟩ with
    | .int .w64 x => some (some x)
    | .poison => some none
    | _ => none
  else none

/-- A rule event at the integer load `x` at `v` of a read-only symbol (`{sym}`: an `SRODATA`
symbol or a type descriptor, `RewriteCheck.roSym?`, that an `Addr` of `f` names, so that the
precondition's `RoImage` pins it) replayed as the constant `u` (`ARM64.rules:1811-1817`,
`roLoadRule`): `u` is `MOVDconst [c]` with `x`'s type, and the load from the symbol's allocation
alone gives `c`'s word or `poison` (`roLoadWord`); `x`'s memory argument is an atom of `M`, and
every value of `f` that may hold a memory is a memory op (`memTyAll`), so the memory it reads
holds the allocation. -/
def roLoadDef (tabs : Tables) (f : Func) (M : Defs) (v : ID) (defs : List Value) :
    Option Value :=
  match M.get? v, defs with
  | some x, [_, u] =>
    match ldOp? x.op, roSym? tabs x.aux with
    | some (n, s), some (name, a) =>
      if x.id == v && u.id == v && u.op == .ARM64MOVDconst && u.args.size == 0 &&
          u.type == x.type && u.aux == none && x.args.size == 2 && termVL tabs x &&
          termVL tabs u && (M.get? x.args[1]!).all (fun w => !termVL tabs w) &&
          f.valueTab.any (fun o => o.any fun w => w.op == .Addr && w.aux == x.aux) &&
          memTyAll tabs f &&
          (match roLoadWord name a n s (BitVec.ofInt 64 x.auxInt.toInt) with
           | some none => true
           | some (some w) => w == Sem.Arm64.imm u.auxInt
           | none => false)
      then some u else none
    | _, _ => none
  | _, _ => none

/-- A rule event at the renamed bounds panic `LoweredPanicBoundsRR` at `v` building a lowered
bounds panic with constant operands (`pbKeep`; `ARM64.rules:513-516`, the later ones on the
result of the first): the replay keeps `v`'s definition, which `finalOKL` relates to the output's
(`pbFinal`). -/
def pbFoldEv (M : Defs) (v : ID) (defs : List Value) : Bool :=
  match M.get? v, defs with
  | some x, [_, u] => x.op == .ARM64LoweredPanicBoundsRR && u.id == v && (pbKeep u.op).isSome
  | _, _ => false

/-- A rule event folding `ADDconst [0]` at `v` into the lowered frame address it reads (`650` at
offset 0: its result, `MOVDaddr {sym}` at offset 0, is an atom, not a term): the replay keeps
`v`'s definition, which `frameAddr` sees through when a later event folds the address into a load,
a store or an offset; `finalOKL` compares it with the output's (`lower` deletes `v` once nothing
reads it). -/
def addrFoldEv (tabs : Tables) (M : Defs) (v : ID) (defs : List Value) : Bool :=
  match M.get? v, defs with
  | some x, [_, u] =>
    x.op == .ARM64ADDconst && u.id == v && u.op == .ARM64MOVDaddr && !termVL tabs u &&
      (frameAddr tabs M v).any fun (_, m) => u.aux == m.aux && u.args == m.args
  | _, _ => false

/-- A rule event lowering `OffPtr [off]` of the stack pointer `SP` at `v` to `MOVDaddr [off] SP`
(`305`; `SP` is an atom, so `ruleOKL` never matches the rule's `(SP)` node): the replay keeps
`v`'s definition, which `stFold` folds into a store; `finalOKL` compares it with the output's
(`lower` deletes `v` once nothing reads it). -/
def spFoldEv (M : Defs) (v : ID) (defs : List Value) : Bool :=
  match M.get? v, defs with
  | some x, [_, u] =>
    x.op == .OffPtr && u.id == v && u.op == .ARM64MOVDaddr && u.aux == none && u.args == x.args &&
      x.args.size == 1 && (M.get? x.args[0]!).any (·.op == .SP)
  | _, _ => false

/-! ## Multiplications by a constant (`ARM64.rules:1043`, `1044`) -/

/-- The register map of an op `mulStrengthReduce` builds (`GoFV.Rules.Arm64.buildCombo`) on its
arguments' registers, as `Arm64.evalPure` computes it (`none` for another op or arity). Each is
linear: on multiples of one register it is the multiple by its value on the multipliers. -/
def comboFn (o : Op) (k : Int64) : List (BitVec 64) → Option (BitVec 64)
  | [a, b] => match o with
    | .ARM64ADD => some (a + b)
    | .ARM64SUB => some (a - b)
    | .ARM64ADDshiftLL => some (a + Sem.Arm64.shifted .ll k b)
    | .ARM64SUBshiftLL => some (a + -Sem.Arm64.shifted .ll k b)
    | _ => none
  | [a] => match o with
    | .ARM64NEG => some (-a)
    | .ARM64SLLconst => some (Sem.Arm64.shifted .ll k a)
    | .ARM64NEGshiftLL => some (-Sem.Arm64.shifted .ll k a)
    | _ => none
  | _ => none

/-- The multiplier of `a`'s register the value `w` computes from the definitions `bs`, within `n`
steps: 1 at `a`, `comboFn` of its arguments' multipliers at a value of `bs`. -/
def mulCoef (bs : List Value) (a : ID) (n : Nat) (w : ID) : Option (BitVec 64) :=
  if w == a then some 1 else
  match n with
  | 0 => none
  | n + 1 =>
    match bs.find? (·.id == w) with
    | some u => (u.args.toList.mapM fun y => mulCoef bs a n y).bind (comboFn u.op u.auxInt)
    | none => none

/-- The checks of `mulOKL` on `x` (the multiplication), its operand `a`, the constant's
definition `kd`, the integer shape's width `w`, `x`'s new definition `u` (a `Copy` of `m`) and the
fresh values `bs`. -/
def mulCond (tabs : Tables) (x : Value) (a : ID) (kd : Value) (w : Sem.Width) (u : Value) (m : ID)
    (bs : List Value) : Bool :=
  let ids := bs.map (·.id)
  kd.op == .ARM64MOVDconst && termVL tabs kd && kd.args.isEmpty &&
    decide (w.bits ≤ argWidth (shpL tabs kd.type)) &&
    (x.op == .ARM64MUL || x.op == .ARM64MULW && decide (w.bits ≤ 32)) &&
    u.id == x.id && u.op == .Copy && u.type == x.type && u.auxInt == 0 && u.aux == none &&
    ids.Nodup && !ids.contains x.id &&
    bs.all (fun b => termVL tabs b && b.type == x.type &&
      b.args.all fun y => y == a || ids.contains y) &&
    ids.contains m && (mulCoef bs a bs.length m).any fun c =>
      c.setWidth w.bits == (Sem.Arm64.imm kd.auxInt).setWidth w.bits

/-- `mulOKL` with the multiplication's operand `a` and constant `k`: the fresh values are the
logged definitions after `x`'s that `M` lacks. -/
def mulOKL1 (tabs : Tables) (M : Defs) (x : Value) (a k : ID) (defs : List Value) :
    Option (List Value) :=
  match shpL tabs x.type, M.get? k, defs with
  | .int w, some kd, u :: rest =>
    match u.args.toList with
    | [m] =>
      let bs := rest.filter fun b => (M.get? b.id).isNone
      if mulCond tabs x a kd w u m bs then some (u :: bs) else none
    | _ => none
  | _, _, _ => none

/-- A rule event at `v` whose result is `mulStrengthReduce{,32}(v, x, c)` (`ARM64.rules:1043`,
`1044`; `GoFV.Rules.Interp.mulResult`), checked by its effect: `v` is a term `MUL` or `MULW` (at
most 32 bits wide) at an integer shape of an operand `a` and a `MOVDconst [c]` term `k` (either
order) whose shape holds the bits `v` keeps, and becomes a `Copy` of a fresh value `m`; the fresh
values `bs` the event logged (`Interp.mulDefs`; the logged definitions `M` has are skipped) are
terms of `v`'s type, each a linear combination (`comboFn`) of `a` and values of `bs`, and `m` is
`c` times `a` in the bits `v` keeps (`mulCoef`). The replay adds `v`'s `Copy` and `bs`. -/
def mulOKL (tabs : Tables) (M : Defs) (v : ID) (defs : List Value) : Option (List Value) :=
  match M.get? v with
  | some x =>
    if x.id == v && termVL tabs x && x.args.size == 2 then
      match mulOKL1 tabs M x x.args[0]! x.args[1]! defs with
      | some ds => some ds
      | none => mulOKL1 tabs M x x.args[1]! x.args[0]! defs
    else none
  | none => none

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

/-- The definition of the control a block rule builds (`build [n]` on rule variables, `ctrlNodeOK`)
at the fresh `c'`: `n`'s op, auxint and aux on the bound values (`nodeDenL`'s fields), with the
fields of the matched control `x` otherwise (its type: Go's flags type, which `nodeOKL` checks
against `n`'s). -/
def ctrlDefL (e : PEnv) (pat : Pat) (ev : Expr → DV) (or : Oracle) (σ : Nat → DV) (I : Inst)
    (n : RNode) (x : Value) (c' : ID) : Value :=
  { x with
    id := c'
    op := n.op
    auxInt := (match n.auxInt with
      | some ae => (toAuxIntL n.op.auxType (ev ae)).getD (or.auxInt ae)
      | none => 0)
    aux := nodeAuxL e pat or n.aux
    args := (n.args.filterMap fun a => argID σ I [c'] a).toArray }

/-- The new control of a block-rule event (new controls `nc`, matched control `c`): none for
`First`, a rule variable's value, or one node built on rule variables at a fresh value
(`ctrlDefL`, `nodeOKL`); the definitions the replay adds (the built one). A `ZW`/`NZW` control
reads the low 32 bits of its register (`Sem.Arm64.taken`), so it may also be the source of a
narrowing `Copy` of at least 32 bits that the rule variable's value is (`truncFromL`), which
`lower` eliminates inline (`GoFV.Proof.Low.Val.brVal_r32`). -/
def builtL (tabs : Tables) (M : Defs) (br : BlockRule) (e : PEnv) (pat : Pat) (ev : Expr → DV)
    (or : Oracle) (σ : Nat → DV) (I : Inst) (c : ID) (nc : Array ID) : Option (List Value) :=
  match br.newKind, br.newControls, nc.toList with
  | .First, [], [] => some []
  | k, [(.var x, _)], [c'] =>
    if k != .First && ((DV.pos? (σ x)).map I.at == some c' ||
        (k == .ARM64ZW || k == .ARM64NZW) &&
          (DV.pos? (σ x)).any fun p => truncFromL tabs M M.size 32 (I.at p) c') then some []
    else none
  | k, [(.build [n], _)], [c'] =>
    match M.get? c with
    | some x =>
      if k != .First && ctrlNodeOK (.build [n]) && (M.get? c').isNone &&
          nodeOKL tabs e pat ev or σ I [c'] .other n (ctrlDefL e pat ev or σ I n x c') then
        some [ctrlDefL e pat ev or σ I n x c']
      else none
    | none => none
  | _, _, _ => none

/-- One commutation choice of a block-rule event: the swapped control pattern `pat` matches the
control `c`, its checks and condition hold, the block auxint is as the rule asks, the new control
is as `builtL` asks, and the new auxint the rule's. The result: the new terminator and the built
definitions. -/
def blockOK1 (tabs : Tables) (M : Defs) (br : BlockRule) (pat : Pat) (st : BStateL) (c : ID)
    (nc : Array ID) : Option (BStateL × List Value) :=
  if !Pat.arityOk pat then none else
  match matchPatL tabs M pat [] c with
  | none => none
  | some I =>
    let e := envL tabs M I
    let vtys := br.vars.map (·.ty)
    let σ := @sigmaL Sem.Addrs.fixed tabs e pat
    let or := oracleL vtys tabs ((br.cond.map (negAtoms false)).getD []) []
    let ev := evalE vtys σ or e (@Pat.denL Sem.Addrs.fixed tabs e [] pat)
    if (Pat.sames pat).all (fun x => !(Pat.opNames pat).contains x) &&
        consOK ev σ e I [] pat && wfOK e [] pat &&
        (match br.cond with
          | some cd => match ev cd with | .bool true => true | _ => false
          | none => true) &&
        Pat.argsOK e.ty [] pat && Pat.topOKL (e.ty []) pat && argsOKLr br.loc e.ty pat &&
        leavesOK M I [] pat &&
        blockAuxOKB br.auxInt st.auxInt then
      match builtL tabs M br e pat ev or σ I c nc, newAuxL ev br.newAuxInt with
      | some us, some ai' => some ({ kind := br.newKind, ctrls := nc, auxInt := ai',
                                     swapped := st.swapped != br.swapSuccs }, us)
      | _, _ => none
    else none

/-- A block-rule event (rule `br`, new controls `nc`) on the replayed terminator `st`
(`BlockRuleL.Sound`): `st` has `br`'s kind, a conditional kind (`condKind`), and one control,
and some commutation choice of the control pattern validates (`blockOK1`). -/
def blockOKL (tabs : Tables) (M : Defs) (br : BlockRule) (st : BStateL) (nc : Array ID) :
    Option (BStateL × List Value) :=
  match br.controls, st.ctrls.toList with
  | [pat], [c] =>
    if st.kind == br.kind && condKind br.kind && br.aux matches .any && br.newAux.isNone then
      (choices (Pat.commutes pat)).findSome? fun sw =>
        blockOK1 tabs M br (Pat.swapC pat sw).1 st c nc
    else none
  | _, _ => none

/-- A jump-table event (`ARM64.rules:478`, `(JumpTable idx) => (JUMPTABLE {sym} idx (MOVDaddr
{sym} (SB)))`) on the replayed terminator `st` of a `JumpTable` block (one control `c`, not
swapped): the new controls are `c` and the address `a` of the table, a fresh `MOVDaddr` term on a
fresh `SB` term (`defs`: the values the rule built). `JUMPTABLE` takes the successor its first
control's register selects, as `JumpTable` does on that integer (`Sem.stepTermL`), and reads no
other control, so the event needs no rule obligation (`BlockRuleL.Checked`). The new terminator
keeps the auxint; the replay adds the two terms. -/
def jumpOKL (tabs : Tables) (M : Defs) (st : BStateL) (nc : Array ID) (defs : List Value) :
    Option (BStateL × List Value) :=
  match st.ctrls.toList, nc.toList, defs with
  | [c], [c', a], [ma, sb] =>
    if !st.swapped && c' == c && ma.id == a && ma.op == .ARM64MOVDaddr && termVL tabs ma &&
        ma.args == #[sb.id] && sb.op == .SB && termVL tabs sb && sb.args.isEmpty && sb.id != a &&
        (M.get? a).isNone && (M.get? sb.id).isNone then
      some ({ kind := .ARM64JUMPTABLE, ctrls := nc, auxInt := st.auxInt, swapped := false },
        [sb, ma])
    else none
  | _, _, _ => none

/-! ## Replay -/

/-- Argument `i` of the replayed `v` replaced by `src` if the copies of `M` justify it: `src` is
what the argument copies (`copyReachL`), or the source of a narrowing `Copy` keeping the bits
`v`'s op reads (`truncReachL`); else `M`. -/
def copyStepL (tabs : Tables) (M : Defs) (v : ID) (i : Nat) (src : ID) : Defs :=
  match M.get? v with
  | some x =>
    if h : i < x.args.size then
      if copyReachL tabs M M.size x.args[i] src ||
          truncReachL tabs M M.size x.op x.auxInt i x.args[i] src then
        M.put v { x with args := x.args.set i src }
      else M
    else M
  | none => M

/-- `copyStepL` for each `(v, i, src)` in turn. -/
def copyFixL (tabs : Tables) : Defs → List (ID × Nat × ID) → Defs
  | M, [] => M
  | M, (v, i, src) :: cs => copyFixL tabs (copyStepL tabs M v i src) cs

/-- The arguments `lower` gave its definitions `ds'` (as logged) where the replay's `us` (in
order) have others: `lower` eliminates a `Copy` argument inline, in a node a rule builds and in an
op an ellipsis rule changes. -/
def argCopies (us ds' : List Value) : List (ID × Nat × ID) :=
  (us.zip ds').flatMap fun (u, d) =>
    (List.range d.args.size).filterMap fun j =>
      if u.args[j]? != d.args[j]? then d.args[j]?.map fun a => (u.id, j, a) else none

/-- A rule event at the narrow left shift `v` that `lower` renames to `o'`
(`GoFV.Rules.Derive.lshWide`) is the rename itself (`(Lsh32x<a> ...) => (Lsh64x<a> ...)`,
`ARM64.rules:148-150`, logged with `v`'s new definition alone, of op `o'`). The replay keeps `v`
as it is (the narrow shift) and checks the later events at `v` by `lshRule`; `finalOKL` rejects
a `v` still renamed at the end. -/
def lshRenEv (o' : Op) (v : ID) (defs : List Value) : Bool :=
  match defs with
  | [u] => u.id == v && u.op == o'
  | _ => false

/-- The rule of a later event at the narrow left shift of op `o` that `lower` renamed to `o'`:
rule `i` of `o'`'s row, in its form on `o` (`GoFV.Rules.Derive.lshDerive`), which the rule set
lists after the rename (`GoFV.Rules.Derive.lshSplit`): the rule of `o`'s row with its location
that builds its result and is no strength-reduced multiplication. -/
def lshRule (t : Interp.Table) (o o' : Op) (i : Nat) : Option Interp.CRule :=
  match (t.values[o'.ctorIdx]?).bind (·[i]?), t.values[o.ctorIdx]? with
  | some c, some row => row.find? fun d =>
      d.rule.loc == c.rule.loc && (d.rule.result matches .build _) && !Interp.mulResult d.rule
  | _, _ => none

/-- The logged definitions of a later event at the renamed narrow left shift `v` of op `o`, with
`v` built as an `Lsh64x<b>` (`171`) read as the narrow shift its derived form builds
(`GoFV.Rules.Derive.lshAt`). -/
def lshDefs (o : Op) (v : ID) (defs : List Value) : List Value :=
  defs.map fun u => if u.id == v then { u with op := GoFV.Rules.Derive.lshAt o u.op } else u

/-- Replay the log on the definitions `M` and the terminators `B`, from `f`'s; `none` if an event
is not validated. A copy-argument replacement the copies of `M` do not justify is skipped (`M`
keeps its definition; `finalOKL` decides), as is one of the arguments `lower` gave a rule's new
definitions (`argCopies`, `copyFixL`); phi eliminations and snapshots reject. A narrow left
shift's rename is replayed as no change and the later events at it by their derived rules
(`lshRenEv`, `lshRule`). -/
def replayL (tabs : Tables) (t : Interp.Table) (f : Func) :
    Defs → BMapL → List RwEvent → Option (Defs × BMapL)
  | M, B, [] => some (M, B)
  | M, B, .rule v i _ defs :: evs =>
    match M.get? v with
    | none => none
    | some x =>
      if pbFoldEv M v defs.toList || addrFoldEv tabs M v defs.toList || spFoldEv M v defs.toList then
        replayL tabs t f M B evs
      else
      match GoFV.Rules.Derive.lshWide x.op with
      | some o' =>
        if lshRenEv o' v defs.toList then replayL tabs t f M B evs
        else
        match lshRule t x.op o' i with
        | none => none
        | some cr =>
          match ruleOKL tabs M cr.rule v (lshDefs x.op v defs.toList) with
          | some ds =>
            replayL tabs t f (copyFixL tabs (ds.foldl (fun M u => M.put u.id u) M)
              (argCopies (ds.drop 1) (defs.toList.drop 1))) B evs
          | none => none
      | none =>
      match (t.values[x.op.ctorIdx]?).bind (·[i]?) with
      | none => none
      | some cr =>
        match cr.rule.result with
        | .setOp _ =>
          match setOpDef tabs M cr.rule v with
          | some x' =>
            replayL tabs t f (copyFixL tabs (M.put v x') (argCopies [x'] (defs.toList.take 1))) B evs
          | none => none
        | _ =>
          if Interp.mulResult cr.rule then
            match mulOKL tabs M v defs.toList with
            | some ds => replayL tabs t f (ds.foldl (fun M u => M.put u.id u) M) B evs
            | none => none
          else
          match ruleOKL tabs M cr.rule v defs.toList with
          | some ds =>
            replayL tabs t f (copyFixL tabs (ds.foldl (fun M u => M.put u.id u) M)
              (argCopies (ds.drop 1) (defs.toList.drop 1))) B evs
          | none =>
            match atomDef tabs f M v defs.toList with
            | some (u, none) => replayL tabs t f (M.put v u) B evs
            | some (u, some s) => replayL tabs t f ((M.put s.id s).put v u) B evs
            | none =>
              match moveDef tabs f M v defs.toList with
              | some (u, ts) =>
                replayL tabs t f ((ts.foldl (fun M s => M.put s.id s) M).put v u) B evs
              | none =>
              match moveDef2 tabs f M v defs.toList with
              | some (u, ts, w) =>
                replayL tabs t f (((ts.foldl (fun M s => M.put s.id s) M).put w.id w).put v u) B
                  evs
              | none =>
              match zeroDef tabs f M v defs.toList with
              | some (u, c) => replayL tabs t f ((M.put c.id c).put v u) B evs
              | none =>
              match zeroDef2 tabs f M v defs.toList with
              | some (u, c, w) => replayL tabs t f (((M.put c.id c).put w.id w).put v u) B evs
              | none =>
              match frameFold tabs f M v defs.toList with
              | some u => replayL tabs t f (M.put v u) B evs
              | none =>
                match ldOffFold tabs M v defs.toList with
                | some u => replayL tabs t f (M.put v u) B evs
                | none =>
                  match roLoadDef tabs f M v defs.toList with
                  | some u => replayL tabs t f (M.put v u) B evs
                  | none => none
  | M, B, .copyArg v i src :: evs =>
    match M.get? v with
    | none => none
    | some x =>
      if i < x.args.size then replayL tabs t f (copyStepL tabs M v i src) B evs
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
  | M, B, .blockRule b i nc defs :: evs =>
    match bstateL f B b with
    | none => none
    | some st =>
      if st.kind == .JumpTable then
        match jumpOKL tabs M st nc defs.toList with
        | none => none
        | some (st', us) => replayL tabs t f (us.foldl (fun M u => M.put u.id u) M) ((b, st') :: B) evs
      else
      if ((f.block? b).map (·.succs.size)) != some 2 then none else
      match (t.blocks[st.kind.ctorIdx]?).bind (·[i]?) with
      | none => none
      | some br =>
        match blockOKL tabs M br st nc with
        | none => none
        | some (st', us) => replayL tabs t f (us.foldl (fun M u => M.put u.id u) M) ((b, st') :: B) evs

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
(`memLower`) or the `Zero` or `Move` `u` (`bulkLower`) with the same type and number of
arguments, or the frame address `u` (`addrLower`), the bounds panic `u` with constant operands
(`pbLower`), the store `u` to an indexed store (`idxLower`), the `Move` `u` to a 128-bit store
(`moveQLower`) or to two, the outer one (`moveQ2Lower`), or the `Zero` `u` to a store of `0`
(`zeroLower`), to two, the outer one (`zero2Lower`), or to an indexed one (`zeroIdxLower`), with
the same type. -/
def atomPair (tabs : Tables) (u w : Value) : Bool :=
  (((u.op == w.op || renameOp u.op w.op) && u.auxInt == w.auxInt && u.aux == w.aux ||
    memLower tabs u w || bulkLower u w) && u.args.size == w.args.size || addrLower tabs u w ||
    pbLower u w || idxLower tabs u w || moveQLower tabs u w || moveQ2Lower u w ||
    zeroLower tabs u w || zero2Lower u w || zeroIdxLower u w) &&
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

/-- The atoms `lower` may delete: `RewriteCheck.dropAtom`'s, and `Invalid` values (a value an
earlier pass invalidated, with no arguments and no uses, which `lower`'s dead-value removal frees).
Neither is a root (`Sem.isRoot`): the schedule check of `atomsOKL` already requires that of every
atom only `f` has, and the simulation (`GoFV.Proof.Low.Sim.atomsOKL_spec`) needs nothing else. -/
def dropAtomL (op : Op) : Bool := GoFV.Opt.RewriteCheck.dropAtom op || op == .Invalid

/-- The atom `w` of `g` at `x` is a lowered frame address (`MOVDaddr {n}` at offset 0, an atom by
`termVL`) where `f` has a term: `lower` folded the term `ADDconst [0]` (`OffPtr [0]`, `306`) of a
frame variable's address into it (`650` at offset 0, `addrFoldEv`; `finalOKL` relates the two,
`frameFinal`). It reads no argument (its address is `n`'s, `Sem.symAddr`) and is no root. -/
def frameAtomG (tabs : Tables) (f : Func) (x : ID) (w : Value) : Bool :=
  w.op == .ARM64MOVDaddr && !termVL tabs w && w.args.size == 1 && (f.value? x).any (termVL tabs ·)

/-- The atom after `x` in the schedule `og` of a block of `g` (`termVL`). -/
def nextAtomL (tabs : Tables) (g : Func) (og : List ID) (x : ID) : Option ID :=
  match og.dropWhile (· != x) with
  | _ :: rest => rest.find? fun y => (g.value? y).any (!termVL tabs ·)
  | [] => none

/-- The atom `w` of `g` at `x`, where `f` has no value, is the inner store of the two stores
lowering a `Move` (`moveQ2In`, `ARM64.rules:423`, `431`, `434`; `moveDef2` replays it at a fresh
ID) or a `Zero` (`zero2In`, `339`-`370`; `zeroDef2`), a memory: the next atom `v` of `g`'s
schedule `og` is the outer one (`moveQ2Lower`, `zero2Lower`) of the `Move` or `Zero` of `f` at
`v`, its last argument `x`. -/
def compOKL (tabs : Tables) (f g : Func) (og : List ID) (x : ID) (w : Value) : Bool :=
  (f.value? x).isNone && !termVL tabs w && Sem.Ty.beq (shpL tabs w.type) .mem &&
  match nextAtomL tabs g og x with
  | some v =>
    match f.value? v, g.value? v with
    | some u, some wv =>
      (moveQ2Lower u wv && moveQ2In u w || zero2Lower u wv && zero2In u w) &&
        wv.args[wv.args.size - 1]! == x
    | _, _ => false
  | none => false

/-- The outer store `w` at `x` of a `Move` or `Zero` `u` lowered to two stores (`st2Lower`) is
the next atom of `g`'s schedule `og` after its memory, the inner store (`compOKL` from that side):
both are in the same block, the inner one evaluated first. -/
def q2OKL (tabs : Tables) (g : Func) (og : List ID) (x : ID) (u w : Value) : Bool :=
  !st2Lower u w || nextAtomL tabs g og w.args[w.args.size - 1]! == some x

/-- `RewriteCheck.atomsOK` with `atomPair` (and `pbConstOK`, `q2OKL`): the same entry, blocks and
own aux; every atom of `g` corresponds to an atom of `f` or is a lowered frame address where `f`
has a term (`frameAtomG`) or the inner store of a `Move` lowered to two 128-bit stores
(`compOKL`), the atoms only `f` has are droppable (`dropAtomL`), and each block evaluates `f`'s
roots, atoms of `g`, in the same order (`Sem.schedule`; `g` may evaluate a lowered `Zero` or
`Move`, which is not a root of lowered SSA, earlier). -/
def atomsOKL (tabs : Tables) (f g : Func) : Bool :=
  f.entry == g.entry && f.blocks == g.blocks && f.ownAux == g.ownAux &&
  f.blocks.all fun b =>
    match f.block? b, g.block? b with
    | some fb, some gb =>
      fb.id == gb.id &&
      let af := atomsOfL tabs f fb
      let ag := atomsOfL tabs g gb
      ag.all (fun x => (af.contains x && match f.value? x, g.value? x with
        | some u, some w => atomPair tabs u w && pbConstOK tabs f u w &&
          q2OKL tabs g (((Sem.schedule g gb).map (·.toList)).getD []) x u w
        | _, _ => false) || (g.value? x).any (frameAtomG tabs f x) ||
          (g.value? x).any (compOKL tabs f g (((Sem.schedule g gb).map (·.toList)).getD []) x)) &&
      af.all (fun x => ag.contains x || (f.value? x).any (dropAtomL ·.op)) &&
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

/-- The output's lowered frame address `u` at `x` (`frameAtomG`, at a word shape) is the replayed
term `m` at `x`: `ADDconst [0]` at `u`'s type of the lowered frame address of `f`'s `LocalAddr`
with `u`'s aux (`frameAddr`; `650` at offset 0 replayed as no change, `addrFoldEv`). -/
def frameFinal (tabs : Tables) (f : Func) (M : Defs) (x : ID) (m u : Value) : Bool :=
  u.id == x && u.op == .ARM64MOVDaddr && !termVL tabs u && u.args.size == 1 && termVL tabs m &&
    u.type == m.type && u.auxInt == m.auxInt && wordShape (shpL tabs u.type) &&
    (frameAddr tabs M x).any fun (a, l) => l.aux == u.aux &&
      (f.value? a).any fun v => v.op == .LocalAddr && v.aux == u.aux

/-- The output's `MOVDaddr [off] sp` at `x` (no aux: a term, the stack pointer moved by `off`) is
the replayed `OffPtr [off] sp` of `f`'s `SP` (`305` replayed as no change, `spFoldEv`): the same
type, offset and argument. -/
def spFinal (f : Func) (M : Defs) (x : ID) (m u : Value) : Bool :=
  u.id == x && m.op == .OffPtr && u.op == .ARM64MOVDaddr && u.aux == none && u.type == m.type &&
    u.auxInt == m.auxInt && m.args.size == 1 && u.args == m.args &&
    (M.get? m.args[0]!).any (·.op == .SP) && (f.value? m.args[0]!).any (·.op == .SP)

/-- Every value listed in `g` has its replayed definition up to copies in its arguments (an
extension's or `W` op's argument also up to a narrowing `Copy`, `truncReachL`; a bounds panic with
constant operands its replayed `LoweredPanicBoundsRR`'s, `pbFinal`; a lowered frame address the
replayed `ADDconst [0]` of it, `frameFinal`; the stack pointer moved by an offset the replayed
`OffPtr` of it, `spFinal`), or is a term `g` does not read; every block of `g` its replayed
terminator (kind, auxint, successors as the replay swapped them, controls up to copies). -/
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
            (List.range m.args.size).all fun j =>
              copyReachL tabs M n m.args[j]! u.args[j]! ||
                truncReachL tabs M n m.op m.auxInt j m.args[j]! u.args[j]! ||
                truncFitL tabs M n m j m.args[j]! u.args[j]! ||
                lowReachL tabs M n m j m.args[j]! u.args[j]!) ||
          (termVL tabs u && L[x]? != some true) || pbFinal tabs f M n x m u ||
            frameFinal tabs f M x m u || spFinal f M x m u
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

/-! ## Values reset in place -/

/-- `v`, read as `Unknown` if its op is `Invalid`. Go resets a value it gives up in place to
`OpInvalid` (`clobber`, `rewrite.go:1053-1058`, which `memcombine` calls; `writebarrier.go:582-583`
for an unused nil check; `fuse.go:172`): the value stays in its block without arguments (a value
it left dead may still read it) until an `applyRewrite` frees it (`rewrite.go:208-235`; `lower`'s
own). `run` reads both ops alike (neither is a root nor `frameVal`'s, and `evalPure` of either is
`poison`), but `Invalid` is not a generic op, so such a function is `Func.lowered` and `runL`
would read it in lowered mode. -/
def invUnknownV (v : Value) : Value := if v.op == .Invalid then { v with op := .Unknown } else v

/-- `f` holds a value whose op is `Invalid`. -/
def hasInvalid (f : Func) : Bool := f.valueTab.any fun | some v => v.op == .Invalid | none => false

/-- `f` with its `Invalid` values read as `Unknown` (`invUnknownV`), `f` itself if it has none:
what `checkedRunL` validates `lower`'s result against. -/
def invUnknown (f : Func) : Func :=
  if hasInvalid f then { f with valueTab := f.valueTab.map (Option.map invUnknownV) } else f

/-! ## The checked pass -/

/-- `tabsAgree`, and every value of `f` has the same lowered shape in both tables (`Ctx.makeL`'s
`typeShapesL`): `f` runs alike under `runL` in both (`GoFV.Proof.Low.runL_tabsAgreeL`). -/
def tabsAgreeL (tabs tabs' : Tables) (f : Func) : Bool :=
  GoFV.Opt.tabsAgree tabs tabs' f &&
  f.valueTab.toList.all fun o =>
    Sem.Ty.beq (Sem.valueTy (Sem.typeShapesL tabs') o) (Sem.valueTy (Sem.typeShapesL tabs) o)

/-- `applyRewrite` with the lowering table `t` and its log on `f`; the result if the tables agree
for `f₀ = invUnknown f` (`tabsAgreeL`) and give it the same read-only symbols (`roPre`, which the
precondition of `GoFV.Proof.Low.lower_refines` pins in the input's tables), `f₀` and the result
pass `check` and `validateL` accepts the result against `f₀`, else `none`. (`f₀` is `f` unless
`f` has `Invalid` values, which no rule matches and which `applyRewrite` frees.) -/
def checkedRunL (t : Interp.Table) (env : PassEnv) (f : Func) : Except String (Option PassOut) := do
  let (out, _, log) ← GoFV.Rules.rewriteRun t true true env f
  let f₀ := invUnknown f
  let ce : CheckEnv := { tabs := out.tables, typs := env.typs }
  return if tabsAgreeL env.tables out.tables f₀ && checkOK { tabs := env.tables, typs := env.typs } f₀ &&
      checkOK ce out.func && validateL out.tables t f₀ out.func log &&
      decide (roPre out.tables f₀ = roPre env.tables f₀) then some out else none

/-- **The checked lowering pass** with table `t`: the validated result, else the input with its
`Invalid` values read as `Unknown` (`invUnknown`). -/
def checkedLowerWith (t : Interp.Table) : Pass := fun env f => do
  match ← checkedRunL t env f with
  | some out => return out
  | none => return { func := invUnknown f, tables := env.tables }

end GoFV.Opt.LowerCheck
