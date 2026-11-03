import GoFV.Opt.RewriteCheck
import GoFV.Opt.LowerTerm

/-!
# The obligation of an `ARM64.rules` / `ARM64latelower.rules` rule (issue #385)

Phase 1's `Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) denotes a pattern by Phase 1's `evalPure`
and `Val.retype`. A lowering rule relates generic and arm64 ops, so its denotation is the one
`runL` gives a term of a lowered function (`Sem.evalOpL`, `Sem.LMode.retype` with `low`):

* `opValL`: a generic op by Phase 1's `Rules.opVal` (`evalPure`, the tables for
  `Addr`/`ConstString`), `MOVDaddr` without a frame variable by `movAddr` (`Sem.symAddr` from
  the tables alone), any other arm64 op by `Arm64.evalPure`;
* every node is shaped by `Val.retypeL` at its lowered shape (`Sem.tyOfL`: Go's `flags` type is
  `Ty.flags`).

`ArmRule.Sound r`: for every commutation choice of the pattern (`Rule.swapC`, the validator
matches the swapped pattern argument for argument; no op symmetry is needed, so `ADD`'s pointer
cases need not commute), every instance whose checks and condition hold, whose leaves have their
shapes and whose op nodes' arguments the shapes `argShapeOk` asks for, the rewritten value
refines the matched one, both at the matched value's shape. Unlike Phase 1 the top is compared
after `retypeL` (an arm64 op computes a 64-bit register that `retypeL` narrows to a narrow type),
so there is no `hasTy` assumption on the top.

`SetOpSound o o'`: the ellipsis rule `(o ...) => (o' ...)` on a term (same arguments, type and
fields). `BlockRuleL.Sound`: a block rule `(K ctrl) && cond => (K' x)` (or `First`, successors
possibly swapped) on one control, of a conditional kind (`If` or an arm64 flags/register kind):
whenever the old block takes a successor (`brVal`), the new one takes the same edge.
-/

namespace GoFV.Proof.Low

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules GoFV.Opt.LowerTerm

/-! ## Shapes and values of lowered terms -/

/-- The lowered shape of type `t` (`Sem.tyOfL`, `runL`'s `Ctx.makeL` of a lowered function). -/
def shpL (tabs : Tables) (t : TypeRef) : Ty := tyOfL tabs 32 t

/-- The shape of type `t` in mode `low` (`Ctx.makeL`): lowered or Phase 1's. -/
def shp (low : Bool) (tabs : Tables) (t : TypeRef) : Ty := if low then shpL tabs t else tabs.ty t

/-- A value at shape `t` in mode `low` (`Sem.LMode.retype`). -/
def rty (low : Bool) (t : Ty) (v : Val) : Val := if low then v.retypeL t else v.retype t

/-- The address of `MOVDaddr [ai] {ax} a` without a frame variable aux: a global symbol at the
offset, or the base moved by the offset (`Sem.symAddr` without the frame). -/
def movPtr (tabs : Tables) (ai : Int64) (ax : Option AuxRef) (a : Val) : Option Ptr :=
  match ax with
  | some n =>
    match tabs.aux? n with
    | some { kind := .sym name .., .. } => some ⟨.global name.toStringLossy, BitVec.ofInt 64 ai.toInt⟩
    | _ => none
  | none => Arm64.addr a (BitVec.ofInt 64 ai.toInt)

/-- `MOVDaddr [ai] {ax} a` without a frame variable aux (`Sem.arm64Op`). -/
def movAddr (tabs : Tables) (ai : Int64) (ax : Option AuxRef) (args : List Val) : Val :=
  match args with
  | [a] => (movPtr tabs ai ax a).elim .poison PtrOps.ptrRes
  | _ => .poison

/-- The value of a lowered term node before shaping: Phase 1's `opVal` for a generic op,
`movAddr` for `MOVDaddr`, `Arm64.evalPure` otherwise. -/
def opValL (tabs : Tables) (op : Op) (ty : Ty) (ai : Int64) (ax : Option AuxRef)
    (args : List Val) : Val :=
  if op.generic then Rules.opVal tabs op ty ai ax args
  else if op == .ARM64MOVDaddr then movAddr tabs ai ax args
  else Arm64.evalPure op ty ai ax args

/-- The value `v` is a term of a lowered function (module doc of `GoFV.Opt.LowerTerm`). -/
def termVL (tabs : Tables) (v : Value) : Bool :=
  if v.op.generic then GoFV.Opt.RewriteCheck.termOp v.op
  else if v.op == .ARM64MOVDaddr then !auxIsName tabs v.aux
  else armTerm v.op && !actOp v.op && !isRoot v.op

/-! ## Commutation choices -/

mutual
/-- The pattern with the first two arguments of its commutative nodes swapped as the choices
`sw` say (preorder: a node's choice, then its arguments'); the nodes are then matched as
written (`commute := false`). Missing choices are `false`. -/
def Pat.swapC : Pat → List Bool → Pat × List Bool
  | .op o n ty ai ax ar args comm, sw =>
    let (c, sw) : Bool × List Bool :=
      if comm then (match sw with | c :: sw => (c, sw) | [] => (false, [])) else (false, sw)
    let (args, sw) := Pat.swapCs args sw
    (.op o n ty ai ax ar (if c then GoFV.Opt.RewriteCheck.swap01 args else args) false, sw)
  | p, sw => (p, sw)
/-- `Pat.swapC` of each argument, threading the choices. -/
def Pat.swapCs : List Pat → List Bool → List Pat × List Bool
  | [], sw => ([], sw)
  | q :: qs, sw =>
    let (q, sw) := Pat.swapC q sw
    let (qs, sw) := Pat.swapCs qs sw
    (q :: qs, sw)
end

/-- The rule with its pattern swapped as `sw` says. -/
def Rule.swapC (r : Rule) (sw : List Bool) : Rule := { r with pat := (Pat.swapC r.pat sw).1 }

/-! ## Denotation -/

mutual
/-- `Pat.den` with `opValL` and `Val.retypeL`. -/
def Pat.denL (tabs : Tables) (e : PEnv) (p : Path) : Pat → Val
  | .op o _ _ _ _ _ args _ =>
    (opValL tabs o (e.ty p) (e.auxInt p) (e.aux p) (Pat.densL tabs e p 0 args)).retypeL (e.ty p)
  | _ => e.leaf p
/-- The values of argument patterns `i, i+1, …` of the node at `p`. -/
def Pat.densL (tabs : Tables) (e : PEnv) (p : Path) (i : Nat) : List Pat → List Val
  | [] => []
  | q :: qs => Pat.denL tabs e (i :: p) q :: Pat.densL tabs e p (i + 1) qs
end

/-- The value of the top node before `retypeL`. -/
def Pat.rawL (tabs : Tables) (e : PEnv) : Pat → Val
  | .op o _ _ _ _ _ args _ =>
    opValL tabs o (e.ty []) (e.auxInt []) (e.aux []) (Pat.densL tabs e [] 0 args)
  | _ => e.leaf []

mutual
/-- `Pat.binds` with `Pat.denL` for named op nodes. -/
def Pat.bindsL (tabs : Tables) (e : PEnv) (p : Path) : Pat → List (Nat × DV)
  | .wild | .same _ => []
  | .bind x => [(x, .val (e.leaf p) (some p))]
  | pat@(.op o name ty ai _ _ args _) =>
    (match name with | some x => [(x, .val (Pat.denL tabs e p pat) (some p))] | none => []) ++
    (match ty with | .bind x => [(x, .ty (e.ty p))] | _ => []) ++
    (match ai with | .bind x => [(x, auxIntDV o.auxType (e.auxInt p))] | _ => []) ++
    Pat.bindssL tabs e p 0 args
def Pat.bindssL (tabs : Tables) (e : PEnv) (p : Path) (i : Nat) : List Pat → List (Nat × DV)
  | [] => []
  | q :: qs => Pat.bindsL tabs e (i :: p) q ++ Pat.bindssL tabs e p (i + 1) qs
end

/-- The rule variables' values (`sigma` with `Pat.denL`). -/
def sigmaL (tabs : Tables) (e : PEnv) (pat : Pat) (x : Nat) : DV :=
  ((Pat.bindsL tabs e [] pat).lookup x).getD .other

/-- The type shape a result node gets: its `<type>` (a bound type, a `typ.<T>`), Go's
`types.TypeFlags` as `Ty.flags`, else the oracle's; the matched value's shape for the top without
a type. -/
def nodeTyL (ev : Expr → DV) (or : Oracle) (topTy : Ty) : Option Expr → Ty
  | some te =>
    match ev te with
    | .ty t => t
    | _ =>
      match te with
      | .glob "types.TypeFlags" _ => Ty.flags
      | _ => or.ty te
  | none => topTy

/-- The aux of a result node: the aux a rule variable bound in the pattern (`{sym}`), else the
oracle's. -/
def nodeAuxL (e : PEnv) (pat : Pat) (or : Oracle) : Option Expr → Option AuxRef
  | some (.var x) =>
    match Pat.auxPos x [] pat with
    | some p => e.aux p
    | none => or.aux (.var x)
  | some xe => or.aux xe
  | none => none

/-- `nodeDen` with `opValL`, `retypeL`, `nodeTyL` and `nodeAuxL`. -/
def nodeDenL (tabs : Tables) (e : PEnv) (pat : Pat) (ev : Expr → DV) (or : Oracle)
    (σ : Nat → DV) (topTy : Ty) (nodes : List RNode) : Nat → Nat → Val
  | 0, _ => .poison
  | fuel + 1, k =>
    match nodes[k]? with
    | none => .poison
    | some n =>
      let t := nodeTyL ev or topTy n.ty
      let ai := match n.auxInt with
        | some ae => (toAuxIntD n.op.auxType (ev ae)).getD (or.auxInt ae)
        | none => 0
      let ax := nodeAuxL e pat or n.aux
      let argv := n.args.map fun
        | .var x => (σ x).valOr (or.val (.var x))
        | .node j => nodeDenL tabs e pat ev or σ topTy nodes fuel j
        | .expr e => (ev e).valOr (or.val e)
      (opValL tabs n.op t ai ax argv).retypeL t

/-- The value `v` has after the rewrite: a `copy` is the bound value (`v.copyOf(w)` gives `v`
`w`'s type), a `build` its top node. -/
def resDenL (tabs : Tables) (e : PEnv) (pat : Pat) (ev : Expr → DV) (or : Oracle)
    (σ : Nat → DV) (topTy : Ty) : Result → Val
  | .copy ce => (ev ce).valOr (or.val ce)
  | .build nodes => nodeDenL tabs e pat ev or σ topTy nodes nodes.length 0
  | .setOp o => or.val (.op o)

/-- **The obligation of one swapped form of a value rule** (module doc). -/
def ArmRule.Sound1 (r : Rule) : Prop :=
  Pat.arityOk r.pat = true ∧
  ∀ (tabs : Tables) (e : PEnv) (or : Oracle), Oracle.BoolTyped or →
    let σ := sigmaL tabs e r.pat
    let ev := evalE (r.vars.map (·.ty)) σ or e (Pat.denL tabs e [] r.pat)
    Pat.wf e [] r.pat →
    Pat.cons ev σ e [] r.pat →
    condHolds ev r.cond →
    Pat.typed e [] r.pat →
    Pat.argsOK e.ty [] r.pat = true →
    Refines ((Pat.rawL tabs e r.pat).retypeL (e.ty []))
      (resDenL tabs e r.pat ev or σ (e.ty []) r.result)

/-- **The obligation of a lowering value rule**: every commutation choice of its pattern. -/
def ArmRule.Sound (r : Rule) : Prop :=
  ∀ sw ∈ GoFV.Opt.RewriteCheck.choices (GoFV.Opt.RewriteCheck.Pat.commutes r.pat),
    ArmRule.Sound1 (Rule.swapC r sw)

/-- An ellipsis pattern on op `o` (`(o ...)`). -/
def ellipsisOn (o : Op) : Pat → Bool
  | .op o' none .any .any .any .ellipsis [] _ => o' == o
  | _ => false

/-- **The obligation of an ellipsis rule `(o ...) => (o' ...)` on terms**: on any arguments, type
shape and fields, `o'` at the shape refines `o` at the shape. -/
def SetOpSound (o o' : Op) : Prop :=
  ∀ (tabs : Tables) (ty : Ty) (ai : Int64) (ax : Option AuxRef) (args : List Val),
    Refines ((opValL tabs o ty ai ax args).retypeL ty) ((opValL tabs o' ty ai ax args).retypeL ty)

/-- An ellipsis rule without a condition, from `o` to `o'`, both term ops of every value
(generic term ops or `armTerm` ops: not `MOVDaddr`, whose being a term depends on the aux), with
`SetOpSound o o'`. -/
def ArmRule.SetOp (r : Rule) : Prop :=
  ∃ o o', ellipsisOn o r.pat = true ∧ r.result = .setOp o' ∧ r.cond = none ∧ r.block = none ∧
    (∀ tabs (v : Value), v.op = o → termVL tabs v = true) ∧
    (∀ tabs (v : Value), v.op = o' → termVL tabs v = true) ∧ SetOpSound o o'

/-- The atom ellipsis rules the atom simulation relates by itself (`GoFV.Opt.LowerCheck.atomPair`):
the input atom and its renamed output have the same arguments and fields, and the output's
evaluation refines the input's (`GoFV.Proof.Low.atomPair_eval`). -/
def renameOp : Op → Op → Bool
  | .NilCheck, .ARM64LoweredNilCheck => true
  | .StaticCall, .ARM64CALLstatic => true
  | .ClosureCall, .ARM64CALLclosure => true
  | .InterCall, .ARM64CALLinter => true
  | _, _ => false

/-- An ellipsis rule without a condition renaming an atom (`renameOp`). -/
def ArmRule.Rename (r : Rule) : Prop :=
  ∃ o o', ellipsisOn o r.pat = true ∧ r.result = .setOp o' ∧ r.cond = none ∧ r.block = none ∧
    renameOp o o' = true

/-! ## Block rules -/

/-- Whether a conditional block of kind `k` (auxint `ai`) on the control `c` takes its first
successor (`Sem.stepTermL`): `If` on a boolean, the arm64 conditional kinds by `Arm64.taken`;
`none` if it gets stuck (or is no conditional kind). -/
def brVal (k : BlockKind) (ai : Int64) (c : Val) : Option Bool :=
  match k with
  | .If => match c with
    | .bool b => some b
    | _ => none
  | .ARM64JUMPTABLE => none
  | k => if k.isArm64 then Arm64.taken k ai c else none

/-- A conditional block kind `brVal` decides. -/
def condKind (k : BlockKind) : Bool := k == .If || (k.isArm64 && k != .ARM64JUMPTABLE)

/-- The block auxint the rule asks for: any, or a literal. -/
def blockAuxOK (f : GoFV.Rules.Field) (ai : Int64) : Prop :=
  match f with
  | .any => True
  | .eq (.lit _ (.int i)) => ai.toInt = i
  | _ => False

/-- The new block auxint (`toAuxIntD .Int64` of the expression; 0 without one). -/
def newAuxL (ev : Expr → DV) : Option Expr → Option Int64
  | some ae => toAuxIntD .Int64 (ev ae)
  | none => some 0

/-- **The obligation of a block rule** `(K ctrl) && cond => (K' x…)` on one control of a
conditional kind: the new controls are rule variables (none for `First`, one otherwise), and
for every instance of `ctrl` whose checks and condition hold (leaves of their shapes, op nodes'
arguments of the checked shapes), with the block auxint `ai` the rule asks for and the new one
`ai'`: if the old block takes an edge, the new one takes the same (`brVal`, `First` always its
first successor, swapped successors flip it). -/
def BlockRuleL.Sound (br : BlockRule) : Prop :=
  condKind br.kind = true ∧ (br.newKind == .First || condKind br.newKind) = true ∧
  ∃ pat, br.controls = [pat] ∧ Pat.arityOk pat = true ∧ br.aux = .any ∧ br.newAux = none ∧
  (br.newKind = .First → br.newControls = []) ∧
  (br.newKind ≠ .First → ∃ x pos, br.newControls = [(.var x, pos)]) ∧
  ∀ sw ∈ GoFV.Opt.RewriteCheck.choices (GoFV.Opt.RewriteCheck.Pat.commutes pat),
    let pat' := (Pat.swapC pat sw).1
    Pat.arityOk pat' = true ∧
    ∀ (tabs : Tables) (e : PEnv) (or : Oracle) (ai ai' : Int64), Oracle.BoolTyped or →
      let σ := sigmaL tabs e pat'
      let ev := evalE (br.vars.map (·.ty)) σ or e (Pat.denL tabs e [] pat')
      Pat.wf e [] pat' → Pat.cons ev σ e [] pat' → condHolds ev br.cond →
      Pat.typed e [] pat' → Pat.argsOK e.ty [] pat' = true → blockAuxOK br.auxInt ai →
      newAuxL ev br.newAuxInt = some ai' →
      ∀ b, brVal br.kind ai (Pat.denL tabs e [] pat') = some b →
        (match br.newKind, br.newControls with
          | .First, _ => some true
          | k, [(.var x, _)] => brVal k ai' ((σ x).valOr .poison)
          | _, _ => none) = some (b != br.swapSuccs)

/-! ## Rule sets -/

/-- A value rule of a lowering rule set the checked `lower` may fire: a sound rule, a sound
ellipsis rule on terms, or an atom rename. -/
def ArmRule.Checked (r : Rule) : Prop := ArmRule.Sound r ∨ ArmRule.SetOp r ∨ ArmRule.Rename r

/-- Every value rule of `s` is `ArmRule.Checked`, every block rule `BlockRuleL.Sound`, and `s`
has no rules in the per-instance tables (`nilChecks` … `phiSels`, Phase 1's generic layers). -/
def ArmRuleSet.AllSound (s : RuleSet) : Prop :=
  ForallL (fun (p : SSA.Op × List Rule) => ForallL ArmRule.Checked p.2) s.values ∧
  ForallL (fun (p : SSA.BlockKind × List BlockRule) => ForallL BlockRuleL.Sound p.2) s.blocks ∧
  s.nilChecks = [] ∧ s.loads = [] ∧ s.structLoads = [] ∧ s.structStores = [] ∧ s.segs = [] ∧
  s.phiSels = []

end GoFV.Proof.Low
