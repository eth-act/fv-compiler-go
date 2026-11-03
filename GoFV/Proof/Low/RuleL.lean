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
after `retypeL` (an arm64 op computes a 64-bit register that `retypeL` narrows to a narrow type);
a generic top op is assumed to produce its shape (`topOKL`, Phase 1's `topOK`). Two premises the
validator checks on the instance: an integer load at the top reads as many bytes as the shape has
(`resFitsL`), and an addressing node whose base the rule folds has no symbol and small
non-negative offsets (`Pat.addrOKL`).

`SetOpSound o o'`: the ellipsis rule `(o ...) => (o' ...)` on a term (same arguments, type and
fields), at shapes where a generic `o` produces its shape (`topOKL`). `BlockRuleL.Sound`: a block
rule `(K ctrl) && cond => (K' x)` (or `First`, successors
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

/-- The integer loads `Load` lowers to, with their size and signedness (`MOV{B,BU,H,HU,W,WU,D}load`;
`Sem.arm64Op`'s `ld`). -/
def ldOp? : Op → Option (Nat × Bool)
  | .ARM64MOVBload => some (1, true)
  | .ARM64MOVBUload => some (1, false)
  | .ARM64MOVHload => some (2, true)
  | .ARM64MOVHUload => some (2, false)
  | .ARM64MOVWload => some (4, true)
  | .ARM64MOVWUload => some (4, false)
  | .ARM64MOVDload => some (8, false)
  | _ => none

/-- An `n`-byte integer load `[ai] {ax} a mem` without a frame variable aux (`Sem.arm64Op`'s `ld`):
the memory at `movPtr`, `poison` without an address. -/
def ldVal (tabs : Tables) (n : Nat) (s : Bool) (ty : Ty) (ai : Int64) (ax : Option AuxRef) :
    List Val → Val
  | [a, .mem m] => (movPtr tabs ai ax a).elim .poison (Arm64.loadN ty n s m)
  | _ => .poison

/-- The value of a lowered term node before shaping: Phase 1's `opVal` for a generic op,
`movAddr` for `MOVDaddr`, `ldVal` for an integer load, `Arm64.evalPure` otherwise. -/
def opValL (tabs : Tables) (op : Op) (ty : Ty) (ai : Int64) (ax : Option AuxRef)
    (args : List Val) : Val :=
  if op.generic then Rules.opVal tabs op ty ai ax args
  else if op == .ARM64MOVDaddr then movAddr tabs ai ax args
  else match ldOp? op with
    | some (n, s) => ldVal tabs n s ty ai ax args
    | none => Arm64.evalPure op ty ai ax args

/-- The integer loads are activation ops (`Sem.arm64Op`). -/
theorem ldOp?_of_act {o : Op} (h : actOp o = false) : ldOp? o = none := by
  unfold ldOp?
  split <;> first | rfl | exact absurd h (by decide)

theorem ldOp?_mem {o : Op} {p : Nat × Bool} (h : ldOp? o = some p) :
    o = .ARM64MOVBload ∨ o = .ARM64MOVBUload ∨ o = .ARM64MOVHload ∨ o = .ARM64MOVHUload ∨
      o = .ARM64MOVWload ∨ o = .ARM64MOVWUload ∨ o = .ARM64MOVDload := by
  unfold ldOp? at h
  split at h <;> simp_all

/-- The value `v` is a term of a lowered function (module doc of `GoFV.Opt.LowerTerm`). -/
def termVL (tabs : Tables) (v : Value) : Bool :=
  if v.op.generic then GoFV.Opt.RewriteCheck.termOp v.op
  else if v.op == .ARM64MOVDaddr then !auxIsName tabs v.aux
  else if (ldOp? v.op).isSome then !auxIsName tabs v.aux
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
    match te with
    | .glob "types.TypeFlags" _ => Ty.flags
    | _ =>
      match ev te with
      | .ty t => t
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

/-- `toAuxIntD` for lowered result nodes: an op at a `CCop` auxint (`CSEL [OpARM64LessThanU]`) is
its Go opcode number (Go's `opToAuxInt`, `GoFV.Rules.Interp.toAuxInt`). -/
def toAuxIntL (aty : AuxType) : DV → Option Int64
  | .op o => match aty with
    | .CCop => some (Int64.ofNat o.goNum)
    | _ => none
  | d => toAuxIntD aty d

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
        | some ae => (toAuxIntL n.op.auxType (ev ae)).getD (or.auxInt ae)
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

/-- A generic top op produces a value of its type's shape (Phase 1's `RewriteCheck.topOK`: Go types
these values at their op's width, and a narrow generic op read at a wider shape would be widened by
`retypeL` where the arm64 op keeps its register), as does `Load` (`loadOp` decodes at the shape);
arm64 tops are unconstrained (`retypeL` narrows their 64-bit register). -/
def topOKL (o : Op) (ty : Ty) : Bool :=
  !o.generic || o == .Load || GoFV.Opt.RewriteCheck.topOK o ty

/-- `topOKL` of the top op of a pattern (a leaf top: unconstrained). -/
def Pat.topOKL (ty : Ty) : Pat → Bool
  | .op o _ _ _ _ _ _ _ => GoFV.Proof.Low.topOKL o ty
  | _ => true

/-- The bits of a value of shape `t` a register holds defined: an integer its width, a boolean 1,
a pointer, flags or another aggregate 64; 0 for other shapes. -/
def argWidth : Ty → Nat
  | .int w => w.bits
  | .bool => 1
  | .ptr _ => 64
  | .agg _ _ => 64
  | _ => 0

/-- The low bits of argument `i` an arm64 op of shape `ty` reads (`Arm64.reg` zero-extends a
narrow value, while Go's registers hold full words): low-bit ops (add, subtract, multiply,
logic, negate, left shift's operand) their result's width, `W` ops 32, sign and zero
extensions their source width, an integer load none of its memory argument, every other op the
whole register. -/
def armReadW (o : Op) (ty : Ty) (i : Nat) : Nat :=
  let w := match ty with
    | .int w => w.bits
    | .bool => 1
    | _ => 64
  match o with
  | .ARM64ADD | .ARM64ADDconst | .ARM64SUB | .ARM64SUBconst | .ARM64MUL | .ARM64MNEG
  | .ARM64NEG | .ARM64MVN | .ARM64AND | .ARM64ANDconst | .ARM64OR | .ARM64ORconst | .ARM64XOR
  | .ARM64XORconst | .ARM64BIC | .ARM64EON | .ARM64ORN | .ARM64MADD | .ARM64MSUB => w
  | .ARM64SLL | .ARM64SLLconst => if i == 0 then w else 64
  | .ARM64MULW | .ARM64MNEGW | .ARM64DIVW | .ARM64UDIVW | .ARM64MODW | .ARM64UMODW
  | .ARM64MADDW | .ARM64MSUBW | .ARM64CMPW | .ARM64CMPWconst | .ARM64CMNW | .ARM64CMNWconst
  | .ARM64TSTW | .ARM64TSTWconst | .ARM64RORW | .ARM64RORWconst | .ARM64EXTRWconst
  | .ARM64CLZW | .ARM64RBITW | .ARM64REVW | .ARM64REV16W | .ARM64MOVWreg | .ARM64MOVWUreg => 32
  | .ARM64MOVBreg | .ARM64MOVBUreg => 8
  | .ARM64MOVHreg | .ARM64MOVHUreg => 16
  | .ARM64MOVBload | .ARM64MOVBUload | .ARM64MOVHload | .ARM64MOVHUload | .ARM64MOVWload
  | .ARM64MOVWUload | .ARM64MOVDload => if i == 0 then 64 else 0
  | _ => 64

/-- The arm64 ops with pointer provenance cases (`Arm64.addP`, `add`, `sub`). -/
def provOp (o : Op) : Bool :=
  o matches .ARM64ADD | .ARM64ADDconst | .ARM64SUB | .ARM64SUBconst | .ARM64ADDshiftLL |
    .ARM64ADDshiftRL | .ARM64ADDshiftRA | .ARM64SUBshiftLL | .ARM64SUBshiftRL | .ARM64SUBshiftRA

/-- A word shape: a pointer or a 64-bit integer. -/
def wordShape : Ty → Bool
  | .ptr _ | .int .w64 => true
  | _ => false

mutual
/-- Every argument of every arm64 op node of the pattern at `p` holds the low bits the op reads
(`armReadW`, `argWidth`), by the instance's types `ty`, and a provenance op (`provOp`) with a
pointer-shaped argument has a word shape: Go types the operands of these ops at least as wide. -/
def Pat.argsOKL (ty : Path → Ty) (p : Path) : Pat → Bool
  | .op o _ _ _ _ _ args _ => Pat.argsOKLs ty p o 0 args
  | _ => true
/-- `Pat.argsOKL` of the arguments `i, i+1, …` of an `o` node at `p`. -/
def Pat.argsOKLs (ty : Path → Ty) (p : Path) (o : Op) (i : Nat) : List Pat → Bool
  | [] => true
  | q :: qs => (o.generic || decide (armReadW o (ty p) i ≤ argWidth (ty (i :: p)))) &&
      (!provOp o || !isPtrTy (ty (i :: p)) || wordShape (ty p)) &&
      Pat.argsOKL ty (i :: p) q && Pat.argsOKLs ty p o (i + 1) qs
end

/-- A `copy` result copies a value of a shape compatible with the matched value's
(`RewriteCheck.copyCompat`: the same shape, or two pointer shapes). -/
def copyShapeOK (ev : Expr → DV) (e : PEnv) : Result → Prop
  | .copy ce => match ev ce with
    | .val _ (some p) => GoFV.Opt.RewriteCheck.copyCompat (e.ty p) (e.ty []) = true
    | _ => True
  | _ => True

/-- A scalar shape of `n` bytes: a boolean (1), an integer (its width), a pointer (8). -/
def fitsB (ty : Ty) (n : Nat) : Bool :=
  match ty with
  | .bool => n == 1
  | .int w => n == w.bytes
  | .ptr _ => n == 8
  | _ => false

/-- A result whose top node is an integer load (`ldOp?`) reads as many bytes as the matched
shape `ty` has (`fitsB`): Go's conditions (`is8BitInt(t)`, `t.IsBoolean()`, …) say so, the
validator checks it on the instance (`ruleOK1`). -/
def resFitsL (ty : Ty) : Result → Bool
  | .build (n :: _) => match ldOp? n.op with
    | some (k, _) => fitsB ty k
    | none => true
  | _ => true

/-- An arm64 op whose address is `Sem.symAddr` of its aux, auxint and base (its argument 0): an
integer load (`ldOp?`) or `MOVDaddr`. -/
def addrOp (o : Op) : Bool := (ldOp? o).isSome || o == .ARM64MOVDaddr

/-- A small non-negative offset: `[0, 2^23)`. -/
def offOK (k : Int64) : Bool := decide (0 ≤ k.toInt) && decide (k.toInt < 2 ^ 23)

mutual
/-- An addressing node (`addrOp`) of the pattern whose base is an op node (folded into the
address by the rule) has no aux, and its offset and the base node's are small and non-negative
(`offOK`): under the semantics a symbol's address ignores the base (`Sem.symAddr`), and a
register pointer outside its block's window (`Ptr.inWindow`) moved back into it by the base's
offset has a concrete address that the second offset could carry into another allocation
(`Ptr.ofAddr`), where the folded offset stays in the first. -/
def Pat.addrOKL (ax : Path → Option AuxRef) (ai : Path → Int64) (p : Path) : Pat → Bool
  | .op o _ _ _ _ _ args _ =>
    (match args with
      | .op .. :: _ => !addrOp o || (ax p == none && offOK (ai p) && offOK (ai (0 :: p)))
      | _ => true) && Pat.addrOKLs ax ai p 0 args
  | _ => true
/-- `Pat.addrOKL` of the arguments `i, i+1, …` of the node at `p`. -/
def Pat.addrOKLs (ax : Path → Option AuxRef) (ai : Path → Int64) (p : Path) (i : Nat) :
    List Pat → Bool
  | [] => true
  | q :: qs => Pat.addrOKL ax ai (i :: p) q && Pat.addrOKLs ax ai p (i + 1) qs
end

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
    Pat.topOKL (e.ty []) r.pat = true →
    Pat.argsOKL e.ty [] r.pat = true →
    copyShapeOK ev e r.result →
    resFitsL (e.ty []) r.result = true →
    Pat.addrOKL e.aux e.auxInt [] r.pat = true →
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
    topOKL o ty = true →
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
  | .GetClosurePtr, .ARM64LoweredGetClosurePtr => true
  | _, _ => false

/-- An ellipsis rule without a condition renaming an atom (`renameOp`). -/
def ArmRule.Rename (r : Rule) : Prop :=
  ∃ o o', ellipsisOn o r.pat = true ∧ r.result = .setOp o' ∧ r.cond = none ∧ r.block = none ∧
    renameOp o o' = true

/-- The access size of the arm64 stores `(Store {t} ptr val mem)` lowers to
(`MOV{B,H,W,D}store`, `FMOV{S,D}store`). -/
def stSize : Op → Option Nat
  | .ARM64MOVBstore => some 1
  | .ARM64MOVHstore => some 2
  | .ARM64MOVWstore | .ARM64FMOVSstore => some 4
  | .ARM64MOVDstore | .ARM64FMOVDstore => some 8
  | _ => none

/-- An arm64 store's aux `Sem.symAddr` reads: none (the base's address), a global symbol, or a
frame variable. -/
def stAux (tabs : Tables) : Option AuxRef → Bool
  | none => true
  | some n =>
    match tabs.aux? n with
    | some { kind := .sym .., .. } | some { kind := .name .., .. } => true
    | _ => false

/-- The atom `w` lowers the memory atom `u`: a `Store {t}` of a scalar `t` of the arm64 store's
size, at a small non-negative offset (`offOK`: 0 as lowered, or a folded `ADDconst` offset,
`ARM64.rules:758-776`) and an aux `Sem.symAddr` reads (`stAux`: none, or a symbol or frame
variable folded in, `881-905`; `GoFV.Proof.Low.Sim.store_lower_eval`). -/
def memLower (tabs : Tables) (u w : Value) : Bool :=
  offOK w.auxInt && stAux tabs w.aux && u.op == .Store &&
    (stSize w.op).any (fitsB (auxTy tabs u.aux))

/-- The atom `w` lowers the frame address `u`: `(LocalAddr <t> {sym} base _) => (MOVDaddr {sym}
base)` and `(MOVDaddr {sym} (SPanchored base mem))`, with the same frame variable `{sym}` (a
`.name` aux) at offset 0 and one argument, whose value it ignores
(`GoFV.Proof.Low.addr_lower_eval`). -/
def addrLower (tabs : Tables) (u w : Value) : Bool :=
  u.op == .LocalAddr && w.op == .ARM64MOVDaddr && w.auxInt == 0 && w.aux == u.aux &&
    auxIsName tabs u.aux && w.args.size == 1

/-- An atom whose value reads no argument: `MOVDaddr` of a frame variable (a `.name` aux,
`Sem.symAddr`). -/
def argFree (tabs : Tables) (w : Value) : Bool :=
  w.op == .ARM64MOVDaddr && auxIsName tabs w.aux

/-- A lowered store lowers a `Store`. -/
theorem memLower_op {tabs : Tables} {u w : Value} (h : memLower tabs u w = true) :
    u.op = .Store := by
  unfold memLower at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.2

/-- Renamed atoms are no arm64 stores. -/
theorem renameOp_stSize {o o' : Op} (h : renameOp o o' = true) :
    stSize o = none ∧ stSize o' = none := by
  unfold renameOp at h
  split at h <;> first | (cases h; done) | exact ⟨rfl, rfl⟩

/-- Generic ops are no arm64 stores. -/
theorem stSize_generic {o : Op} (h : o.generic = true) : stSize o = none := by
  unfold stSize
  split <;> first | rfl | exact absurd h (by decide)

/-- What `addrLower` says. -/
theorem addrLower_cases {tabs : Tables} {u w : Value} (h : addrLower tabs u w = true) :
    u.op = .LocalAddr ∧ w.op = .ARM64MOVDaddr ∧ w.auxInt = 0 ∧ w.aux = u.aux ∧
      auxIsName tabs u.aux = true ∧ w.args.size = 1 := by
  unfold addrLower at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-- What `argFree` says. -/
theorem argFree_cases {tabs : Tables} {w : Value} (h : argFree tabs w = true) :
    w.op = .ARM64MOVDaddr ∧ auxIsName tabs w.aux = true := by
  unfold argFree at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h

/-- A lowered frame address reads no argument. -/
theorem argFree_of_addrLower {tabs : Tables} {u w : Value} (h : addrLower tabs u w = true) :
    argFree tabs w = true := by
  obtain ⟨-, h2, -, h4, h5, -⟩ := addrLower_cases h
  simp only [argFree, h2, h4, h5, beq_self_eq_true, Bool.and_self]

/-- `argFree` reads the op and the aux. -/
theorem argFree_congr {tabs : Tables} {u w : Value} (hop : u.op = w.op) (hax : u.aux = w.aux) :
    argFree tabs u = argFree tabs w := by
  unfold argFree; rw [hop, hax]

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
      Pat.typed e [] pat' → Pat.argsOK e.ty [] pat' = true → Pat.topOKL (e.ty []) pat' = true →
      Pat.argsOKL e.ty [] pat' = true → blockAuxOK br.auxInt ai →
      newAuxL ev br.newAuxInt = some ai' →
      ∀ b, brVal br.kind ai (Pat.denL tabs e [] pat') = some b →
        (match br.newKind, br.newControls with
          | .First, _ => some true
          | k, [(.var x, _)] => brVal k ai' ((σ x).valOr .poison)
          | _, _ => none) = some (b != br.swapSuccs)

/-! ## Rule sets -/

/-- A rule on a memory or frame atom (`(Store {t} ptr val mem)`, `(LocalAddr {sym} base mem)`, an
arm64 store `stSize` knows): the validator accepts its events only as a lowered store, a folded
store offset or a frame address it pairs with the atom itself (`GoFV.Opt.LowerCheck.atomDef`,
`memLower`, `stFold`, `addrLower`), so the rule carries no obligation of its own. -/
def ArmRule.Mem (r : Rule) : Prop :=
  ∃ o n ty ai ax ar args c, r.pat = .op o n ty ai ax ar args c ∧
    (o = .Store ∨ o = .LocalAddr ∨ (stSize o).isSome)

/-- A value rule of a lowering rule set the checked `lower` may fire: a sound rule, a sound
ellipsis rule on terms, an atom rename, or a rule on a memory or frame atom. -/
def ArmRule.Checked (r : Rule) : Prop :=
  ArmRule.Sound r ∨ ArmRule.SetOp r ∨ ArmRule.Rename r ∨ ArmRule.Mem r

/-- Every value rule of `s` is `ArmRule.Checked`, every block rule `BlockRuleL.Sound`, and `s`
has no rules in the per-instance tables (`nilChecks` … `phiSels`, Phase 1's generic layers). -/
def ArmRuleSet.AllSound (s : RuleSet) : Prop :=
  ForallL (fun (p : SSA.Op × List Rule) => ForallL ArmRule.Checked p.2) s.values ∧
  ForallL (fun (p : SSA.BlockKind × List BlockRule) => ForallL BlockRuleL.Sound p.2) s.blocks ∧
  s.nilChecks = [] ∧ s.loads = [] ∧ s.structLoads = [] ∧ s.structStores = [] ∧ s.segs = [] ∧
  s.phiSels = []

end GoFV.Proof.Low
