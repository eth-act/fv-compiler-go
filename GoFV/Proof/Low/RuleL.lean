import GoFV.Opt.RewriteCheck
import GoFV.Opt.LowerTerm
import GoFV.Rules.Derive

variable [GoFV.SSA.Sem.Addrs]

/-!
# The obligation of an `ARM64.rules` / `ARM64latelower.rules` rule (issue #385)

Phase 1's `Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) denotes a pattern by Phase 1's `evalPure`
and `Val.retype`. A lowering rule relates generic and arm64 ops, so its denotation is the one
`runL` gives a term of a lowered function (`Sem.evalOpL`, `Sem.LMode.retype` with `low`):

* `opValL`: a generic op by Phase 1's `Rules.opVal` (`evalPure`, the tables for
  `Addr`/`ConstString`), `MOVDaddr` by `movAddr` and an integer load by `ldVal` (`Sem.symAddr`
  in activation 0, `runL`'s, `symPtr`), any other arm64 op by `Arm64.evalPure`;
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
non-negative offsets, an `ADDconst` folded into a `MOVDaddr` an aux (`Pat.addrOKL`).

`SetOpSoundT o o'`: the ellipsis rule `(o ...) => (o' ...)` on a term (same arguments, type and
fields), at shapes where a generic `o` produces its shape (`topOKL`), on arguments whose
`setArgW64` ones are 64-bit integers (`AddPtr`'s index). `BlockRuleL.Sound`: a block
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

/-- The address `[ai] {ax} a` of `MOVDaddr` and of an integer load (`Sem.symAddr` in activation
0, the activation `runL` runs a function in, `Ctx.makeL`): a global symbol at the offset, a frame
variable's block at the offset, or the base moved by the offset. -/
def symPtr (tabs : Tables) (ai : Int64) (ax : Option AuxRef) (a : Val) : Option Ptr :=
  match ax with
  | some n =>
    match tabs.aux? n with
    | some { kind := .sym name .., .. } => some ⟨.global name.toStringLossy, BitVec.ofInt 64 ai.toInt⟩
    | some { kind := .name .., .. } => some ⟨frameBlk tabs 0 n, BitVec.ofInt 64 ai.toInt⟩
    | _ => none
  | none => Arm64.addr a (BitVec.ofInt 64 ai.toInt)

/-- `MOVDaddr [ai] {ax} a` (`Sem.arm64Op` in activation 0). -/
def movAddr (tabs : Tables) (ai : Int64) (ax : Option AuxRef) (args : List Val) : Val :=
  match args with
  | [a] => (symPtr tabs ai ax a).elim .poison PtrOps.ptrRes
  | _ => .poison

/-- The scalar loads `Load` lowers to, with their size and signedness (`MOV{B,BU,H,HU,W,WU,D}load`
and the float loads `FMOV{S,D}load`, which load as `MOVWUload`/`MOVDload` do: a float shape is
the integer shape of its size; `Sem.arm64Op`'s `ld`). -/
def ldOp? : Op → Option (Nat × Bool)
  | .ARM64MOVBload => some (1, true)
  | .ARM64MOVBUload => some (1, false)
  | .ARM64MOVHload => some (2, true)
  | .ARM64MOVHUload => some (2, false)
  | .ARM64MOVWload => some (4, true)
  | .ARM64MOVWUload => some (4, false)
  | .ARM64MOVDload => some (8, false)
  | .ARM64FMOVSload => some (4, false)
  | .ARM64FMOVDload => some (8, false)
  | _ => none

/-- An `n`-byte integer load `[ai] {ax} a mem` (`Sem.arm64Op`'s `ld` in activation 0): the memory
at `symPtr`, `poison` without an address. -/
def ldVal (tabs : Tables) (n : Nat) (s : Bool) (ty : Ty) (ai : Int64) (ax : Option AuxRef) :
    List Val → Val
  | [a, .mem m] => (symPtr tabs ai ax a).elim .poison (Arm64.loadN ty n s m)
  | _ => .poison

/-- The 128-bit loads: `FMOVQload` (16 bytes, one `Vec128`) and `FLDPQ` (32 bytes, two). -/
def ldQ? : Op → Option Nat
  | .ARM64FMOVQload => some 16
  | .ARM64FLDPQ => some 32
  | _ => none

/-- A 128-bit load `[ai] {ax} a mem` in activation 0 (`Sem.arm64Op`'s `ld16` and `ldPair 16`):
16 bytes at `symPtr` as a blob (`Arm64.load16`), or 32 as two blobs at `symPtr` of the offset and
of the offset moved by 16 (`Sem.pairAddr`, `Arm64.loadPair`); `poison` without an address. -/
def ldQVal (tabs : Tables) (n : Nat) (ty : Ty) (ai : Int64) (ax : Option AuxRef) :
    List Val → Val
  | [a, .mem m] =>
    if n = 32 then
      match symPtr tabs ai ax a, symPtr tabs (ai + Int64.ofNat 16) ax a with
      | some p, some q => Arm64.loadPair ty 16 false m p q
      | _, _ => .poison
    else (symPtr tabs ai ax a).elim .poison (Arm64.load16 m)
  | _ => .poison

/-- An arm64 load term: a scalar load (`ldOp?`) or a 128-bit one (`ldQ?`). -/
def ldAny (o : Op) : Bool := (ldOp? o).isSome || (ldQ? o).isSome

/-- The value of a lowered term node before shaping: Phase 1's `opVal` for a generic op,
`movAddr` for `MOVDaddr`, `ldVal` for an integer load, `ldQVal` for a 128-bit load,
`Arm64.evalPure` otherwise. -/
def opValL (tabs : Tables) (op : Op) (ty : Ty) (ai : Int64) (ax : Option AuxRef)
    (args : List Val) : Val :=
  if op.generic then Rules.opVal tabs op ty ai ax args
  else if op == .ARM64MOVDaddr then movAddr tabs ai ax args
  else match ldOp? op with
    | some (n, s) => ldVal tabs n s ty ai ax args
    | none => match ldQ? op with
      | some n => ldQVal tabs n ty ai ax args
      | none => Arm64.evalPure op ty ai ax args

/-- `opValL` of an integer load: `ldVal`. -/
theorem opValL_ld {o : Op} {n : Nat} {s : Bool} (hg : o.generic = false)
    (hm : (o == .ARM64MOVDaddr) = false) (hl : ldOp? o = some (n, s)) (tabs : Tables) (ty : Ty)
    (ai : Int64) (ax : Option AuxRef) (args : List Val) :
    opValL tabs o ty ai ax args = ldVal tabs n s ty ai ax args := by
  simp only [opValL, hg, hm, hl, Bool.false_eq_true, ite_false]

/-- The integer loads are activation ops (`Sem.arm64Op`). -/
theorem ldOp?_of_act {o : Op} (h : actOp o = false) : ldOp? o = none := by
  unfold ldOp?
  split <;> first | rfl | exact absurd h (by decide)

/-- The 128-bit loads are activation ops. -/
theorem ldQ?_of_act {o : Op} (h : actOp o = false) : ldQ? o = none := by
  unfold ldQ?
  split <;> first | rfl | exact absurd h (by decide)

/-- No load term is an activation op. -/
theorem ldAny_of_act {o : Op} (h : actOp o = false) : ldAny o = false := by
  simp [ldAny, ldOp?_of_act h, ldQ?_of_act h]

/-- An op that is no load term is neither kind of load. -/
theorem ldAny_false {o : Op} (h : ldAny o = false) : ldOp? o = none ∧ ldQ? o = none := by
  simp only [ldAny, Bool.or_eq_false_iff, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]
    at h
  exact h

theorem ldQ?_mem {o : Op} {n : Nat} (h : ldQ? o = some n) :
    (o = .ARM64FMOVQload ∧ n = 16) ∨ (o = .ARM64FLDPQ ∧ n = 32) := by
  unfold ldQ? at h
  split at h <;> simp_all

/-- `opValL` of a 128-bit load: `ldQVal`. -/
theorem opValL_ldQ {o : Op} {n : Nat} (hq : ldQ? o = some n) (tabs : Tables) (ty : Ty)
    (ai : Int64) (ax : Option AuxRef) (args : List Val) :
    opValL tabs o ty ai ax args = ldQVal tabs n ty ai ax args := by
  rcases ldQ?_mem hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

theorem ldOp?_mem {o : Op} {p : Nat × Bool} (h : ldOp? o = some p) :
    o = .ARM64MOVBload ∨ o = .ARM64MOVBUload ∨ o = .ARM64MOVHload ∨ o = .ARM64MOVHUload ∨
      o = .ARM64MOVWload ∨ o = .ARM64MOVWUload ∨ o = .ARM64MOVDload ∨ o = .ARM64FMOVSload ∨
      o = .ARM64FMOVDload := by
  unfold ldOp? at h
  split at h <;> simp_all

theorem pureActOp_cases {o : Op} (h : pureActOp o = true) :
    o = .ARM64LDAR ∨ o = .ARM64LDARB ∨ o = .ARM64LDARW ∨ o = .ARM64LoweredMemEq := by
  unfold pureActOp at h
  split at h <;> simp_all

/-- The acquiring loads and `LoweredMemEq` are activation ops (`Sem.arm64Op`). -/
theorem pureActOp_of_act {o : Op} (h : actOp o = false) : pureActOp o = false := by
  cases hd : pureActOp o
  · rfl
  · rcases pureActOp_cases hd with rfl | rfl | rfl | rfl <;> exact absurd h (by decide)

/-- The acquiring loads and `LoweredMemEq` are no integer loads. -/
theorem ldOp?_of_pureAct {o : Op} (h : pureActOp o = true) : ldOp? o = none := by
  rcases pureActOp_cases h with rfl | rfl | rfl | rfl <;> rfl

/-- The acquiring loads and `LoweredMemEq` are no load terms. -/
theorem ldAny_of_pureAct {o : Op} (h : pureActOp o = true) : ldAny o = false := by
  rcases pureActOp_cases h with rfl | rfl | rfl | rfl <;> rfl

/-- The value `v` is a term of a lowered function (module doc of `GoFV.Opt.LowerTerm`). -/
def termVL (tabs : Tables) (v : Value) : Bool :=
  if v.op.generic then GoFV.Opt.RewriteCheck.termOp v.op
  else if v.op == .ARM64MOVDaddr then !(auxIsName tabs v.aux && v.auxInt == 0)
  else if ldAny v.op then true
  else if pureActOp v.op then true
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

/-- A `CCop` auxint as the op of that Go opcode number (Go's `auxIntToOp`,
`GoFV.Rules.Interp.auxIntVal`), else unknown. -/
def ccDV (i : Int64) : DV :=
  match (if i.toInt < 0 then none else Op.ofGoNum? i.toInt.toNat) with
  | some o => .op o
  | none => .other

/-- `auxIntDV` for lowered ops: a `CCop` auxint (`CSEL [cc]`) is an op (`ccDV`), so a rule can
test and rewrite `cc`; an `ARM64BitField` auxint (`UBFX [bfc]`) is its integer
(`Interp.auxIntVal`), whose `lsb()` and `width()` a rule reads (`methodE`). -/
def auxIntDVL (aty : AuxType) (i : Int64) : DV :=
  match aty with
  | .CCop => ccDV i
  | .ARM64BitField => .int i.toInt
  | _ => auxIntDV aty i

mutual
/-- `Pat.binds` with `Pat.denL` for named op nodes. -/
def Pat.bindsL (tabs : Tables) (e : PEnv) (p : Path) : Pat → List (Nat × DV)
  | .wild | .same _ => []
  | .bind x => [(x, .val (e.leaf p) (some p))]
  | pat@(.op o name ty ai _ _ args _) =>
    (match name with | some x => [(x, .val (Pat.denL tabs e p pat) (some p))] | none => []) ++
    (match ty with | .bind x => [(x, .ty (e.ty p))] | _ => []) ++
    (match ai with | .bind x => [(x, auxIntDVL o.auxType (e.auxInt p))] | _ => []) ++
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

/-- The aux of a result node: the aux a rule variable bound in the pattern (`{sym}`), Go's
`mergeSym(sym1,sym2)` of two bound auxes (the one that is set, if the other is not), else the
oracle's. -/
def nodeAuxL (e : PEnv) (pat : Pat) (or : Oracle) : Option Expr → Option AuxRef
  | some (.var x) =>
    match Pat.auxPos x [] pat with
    | some p => e.aux p
    | none => or.aux (.var x)
  | some (.call "mergeSym" [.var x, .var y] t) =>
    match Pat.auxPos x [] pat, Pat.auxPos y [] pat with
    | some p, some q =>
      match e.aux p, e.aux q with
      | none, a => a
      | a, none => a
      | _, _ => or.aux (.call "mergeSym" [.var x, .var y] t)
    | _, _ => or.aux (.call "mergeSym" [.var x, .var y] t)
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

/-- A word shape: a pointer or a 64-bit integer. -/
def wordShape : Ty → Bool
  | .ptr _ | .int .w64 => true
  | _ => false

/-- The atomic loads (`atomicLoad`: the location's value and the memory at the tuple shape). -/
def atomicLoadOp : Op → Bool
  | .AtomicLoad8 | .AtomicLoad32 | .AtomicLoad64 | .AtomicLoadPtr => true
  | _ => false

/-- The 64-bit shifts and `Const64`: generic ops whose value is a 64-bit integer whatever their
type (`divmod.rules` builds `(Rsh64Ux64 <typ.UInt32> …)`, Go types `Const64` at narrower shapes),
so at a narrower integer shape both they and their arm64 lowering are read at their low bits. -/
def top64Op : Op → Bool
  | .Lsh64x8 | .Lsh64x16 | .Lsh64x32 | .Lsh64x64 | .Rsh64x8 | .Rsh64x16 | .Rsh64x32 | .Rsh64x64
  | .Rsh64Ux8 | .Rsh64Ux16 | .Rsh64Ux32 | .Rsh64Ux64 | .Const64 => true
  | _ => false

/-- A generic top op produces a value of its type's shape (Phase 1's `RewriteCheck.topOK`: Go types
these values at their op's width, and a narrow generic op read at a wider shape would be widened by
`retypeL` where the arm64 op keeps its register), as do `Load` (`loadOp` decodes at the shape) and
the atomic loads (`atomicLoad`, likewise), `Addr` at a word shape (a `uintptr`-typed `Addr`:
the symbol's address, which `MOVDaddr` computes alike, `refines_addr_movAddr` at every shape),
and `CondSelect` at a word or integer shape (an arm, which `CSEL` moves as its register, `regVal`,
and such a shape reads back as the arm's own reading), the 64-bit shifts and `Const64` at an
integer shape (`top64Op`: `retypeL` reads both sides' 64-bit integers at their low bits), and `WB`
(`wbOp`, which `LoweredWB` computes alike, at every shape); arm64 tops are unconstrained
(`retypeL` narrows their 64-bit register). -/
def topOKL (o : Op) (ty : Ty) : Bool :=
  !o.generic || o == .Load || atomicLoadOp o || ((o == .Addr || o == .CondSelect) && wordShape ty) ||
    ((o == .CondSelect || top64Op o) && ty matches .int _) || o == .WB ||
    GoFV.Opt.RewriteCheck.topOK o ty

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
logic, negate, left shift's operand) their result's width, `CSEL` of its arms likewise (it moves
the selected arm's register, `regVal`, which `retypeL` reads at the result's low bits), `W` ops
32, sign and zero extensions their source width, an integer or indexed load none of its memory
argument, every other op the whole register. -/
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
  | .ARM64CSEL => if i < 2 then w else 64
  | .ARM64MULW | .ARM64MNEGW | .ARM64DIVW | .ARM64UDIVW | .ARM64MODW | .ARM64UMODW
  | .ARM64MADDW | .ARM64MSUBW | .ARM64CMPW | .ARM64CMPWconst | .ARM64CMNW | .ARM64CMNWconst
  | .ARM64TSTW | .ARM64TSTWconst | .ARM64RORW | .ARM64RORWconst | .ARM64EXTRWconst
  | .ARM64CLZW | .ARM64RBITW | .ARM64REVW | .ARM64REV16W | .ARM64MOVWreg | .ARM64MOVWUreg => 32
  | .ARM64MOVBreg | .ARM64MOVBUreg => 8
  | .ARM64MOVHreg | .ARM64MOVHUreg => 16
  | .ARM64MOVBload | .ARM64MOVBUload | .ARM64MOVHload | .ARM64MOVHUload | .ARM64MOVWload
  | .ARM64MOVWUload | .ARM64MOVDload | .ARM64FMOVSload
  | .ARM64FMOVDload | .ARM64FMOVQload | .ARM64FLDPQ => if i == 0 then 64 else 0
  | .ARM64MOVDloadidx | .ARM64MOVWloadidx | .ARM64MOVWUloadidx | .ARM64MOVHloadidx
  | .ARM64MOVHUloadidx | .ARM64MOVBloadidx | .ARM64MOVBUloadidx | .ARM64FMOVSloadidx
  | .ARM64FMOVDloadidx | .ARM64MOVHloadidx2 | .ARM64MOVHUloadidx2 | .ARM64MOVWloadidx4
  | .ARM64MOVWUloadidx4 | .ARM64MOVDloadidx8 | .ARM64FMOVSloadidx4
  | .ARM64FMOVDloadidx8 => if i == 2 then 0 else 64
  | _ => 64

/-- The arm64 ops with pointer provenance cases (`Arm64.addP`, `add`, `sub`). -/
def provOp (o : Op) : Bool :=
  o matches .ARM64ADD | .ARM64ADDconst | .ARM64SUB | .ARM64SUBconst | .ARM64ADDshiftLL |
    .ARM64ADDshiftRL | .ARM64ADDshiftRA | .ARM64SUBshiftLL | .ARM64SUBshiftRL | .ARM64SUBshiftRA

mutual
/-- Every argument of every arm64 op node of the pattern at `p` holds the low bits the op reads
(`armReadW`, `argWidth`), by the instance's types `ty`, and a provenance op (`provOp`) at a
non-word shape has no word-shaped argument (the shapes a pointer without an integer form has,
`Val.hasTy`): its register then holds the low bits its result keeps, where a pointer argument's
provenance case (`Arm64.add`, `addP`) moves the pointer by the other argument's whole register,
which a narrow argument zero-extends (`ARM64.rules:970`). -/
def Pat.argsOKL (ty : Path → Ty) (p : Path) : Pat → Bool
  | .op o _ _ _ _ _ args _ => Pat.argsOKLs ty p o 0 args
  | _ => true
/-- `Pat.argsOKL` of the arguments `i, i+1, …` of an `o` node at `p`. -/
def Pat.argsOKLs (ty : Path → Ty) (p : Path) (o : Op) (i : Nat) : List Pat → Bool
  | [] => true
  | q :: qs => (o.generic || decide (armReadW o (ty p) i ≤ argWidth (ty (i :: p)))) &&
      (!provOp o || !wordShape (ty (i :: p)) || wordShape (ty p)) &&
      Pat.argsOKL ty (i :: p) q && Pat.argsOKLs ty p o (i + 1) qs
end

/-- An op node of a pattern (not a leaf: `wild`, `bind`, `same`). -/
def Pat.isOpL : Pat → Bool
  | .op .. => true
  | _ => false

mutual
/-- `Pat.argsOKL` without the width check at a leaf argument: an op may read more bits of a bound
value than its shape holds, which `Arm64.reg` zero-extends (the provenance check stays). -/
def Pat.argsOKLn (ty : Path → Ty) (p : Path) : Pat → Bool
  | .op o _ _ _ _ _ args _ => Pat.argsOKLns ty p o 0 args
  | _ => true
/-- `Pat.argsOKLn` of the arguments `i, i+1, …` of an `o` node at `p`. -/
def Pat.argsOKLns (ty : Path → Ty) (p : Path) (o : Op) (i : Nat) : List Pat → Bool
  | [] => true
  | q :: qs => (o.generic || !Pat.isOpL q || decide (armReadW o (ty p) i ≤ argWidth (ty (i :: p)))) &&
      (!provOp o || !wordShape (ty (i :: p)) || wordShape (ty p)) &&
      Pat.argsOKLn ty (i :: p) q && Pat.argsOKLns ty p o (i + 1) qs
end

/-- The rules whose obligation holds when an op of the pattern reads more bits of a bound value
than its shape holds (`Pat.argsOKLn`; their proofs read no leaf's width): `(cc (CMPWconst [0]
x:(ANDconst [c] y)))` as `(cc (TSTWconst [int32(c)] y))` (`ARM64.rules:561`, `566`) reads `y`'s
register on both sides, where Go builds the `ANDconst` at 32 bits on a narrow `y` (`(MOVBUreg
(ANDconst [c] y)) => (ANDconst [c&(1<<8-1)] y)`); then `(EQ|NE (TSTWconst [c] x))` as `TBZ`/`TBNZ`
on `x`'s register (`623`, `624`); the conditional selects on `InvertFlags` move their arms'
registers alike (`1352`-`1357`). -/
def leafWideL (loc : Loc) : Bool :=
  (loc.line == 561 || loc.line == 566 || loc.line == 623 || loc.line == 624 ||
    loc.line == 1352 || loc.line == 1353 || loc.line == 1354 || loc.line == 1355 ||
    loc.line == 1356 || loc.line == 1357) && loc.file == "ARM64"

/-- The argument check of the rule at `loc` on the pattern `pat`: `Pat.argsOKLn` for the rules
of `leafWideL`, `Pat.argsOKL` otherwise. -/
def argsOKLr (loc : Loc) (ty : Path → Ty) (pat : Pat) : Bool :=
  if leafWideL loc then Pat.argsOKLn ty [] pat else Pat.argsOKL ty [] pat

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

/-- An arm64 op whose address is `Sem.symAddr` of its aux, auxint and base (its argument 0): a
load term (`ldAny`) or `MOVDaddr`. -/
def addrOp (o : Op) : Bool := ldAny o || o == .ARM64MOVDaddr

/-- A small non-negative offset: `[0, 2^23)`. -/
def offOK (k : Int64) : Bool := decide (0 ≤ k.toInt) && decide (k.toInt < 2 ^ 23)

mutual
/-- An addressing node (`addrOp`) of the pattern whose base is an op node (folded into the
address by the rule) has no aux, and its offset and the base node's are small and non-negative
(`offOK`): under the semantics a symbol's address ignores the base (`Sem.symAddr`), and a
register pointer outside its block's window (`Ptr.inWindow`) moved back into it by the base's
offset has a concrete address that the second offset could carry into another allocation
(`Ptr.ofAddr`), where the folded offset stays in the first. An `ADDconst` on a `MOVDaddr` node
(folded into its offset, `ARM64.rules:650`) needs the `MOVDaddr` to have an aux, both offsets
small and non-negative and both nodes word shapes (`ty`): without a symbol, `ADDconst` adds to a
word without the window check of `MOVDaddr`'s `ptrRes`, and at a narrow or boolean shape it
reads a frame variable's address word as an integer where `retypeL` makes the folded address
`poison`. A pair load `FLDPQ` (`ldQ? = some 32`) also reads at its offset moved by 16, which must
stay small (`offOK`) for its folded second address to stay in the first allocation too. -/
def Pat.addrOKL (ty : Path → Ty) (ax : Path → Option AuxRef) (ai : Path → Int64) (p : Path) :
    Pat → Bool
  | .op o _ _ _ _ _ args _ =>
    (match args with
      | .op o' .. :: _ => (!addrOp o || (ax p == none && offOK (ai p) && offOK (ai (0 :: p)))) &&
          ((o != .ARM64ADDconst || o' != .ARM64MOVDaddr ||
            ((ax (0 :: p)).isSome && offOK (ai p) && offOK (ai (0 :: p)) && wordShape (ty p) &&
              wordShape (ty (0 :: p)))) &&
            (ldQ? o != some 32 || offOK (ai p + Int64.ofNat 16)))
      | _ => true) && Pat.addrOKLs ty ax ai p 0 args
  | _ => true
/-- `Pat.addrOKL` of the arguments `i, i+1, …` of the node at `p`. -/
def Pat.addrOKLs (ty : Path → Ty) (ax : Path → Option AuxRef) (ai : Path → Int64) (p : Path)
    (i : Nat) : List Pat → Bool
  | [] => true
  | q :: qs => Pat.addrOKL ty ax ai (i :: p) q && Pat.addrOKLs ty ax ai p (i + 1) qs
end

/-- A bit field `width | lsb<<8` (`arm64BitField`): `lsb ≤ 63`, `1 ≤ width` and
`lsb + width ≤ 64`, as `armBFAuxInt` builds every one (it panics otherwise). -/
def bfOK (k : Int64) : Bool :=
  decide (0 ≤ k.toInt) && decide (k.toInt / 256 ≤ 63) && decide (1 ≤ k.toInt % 256) &&
    decide (k.toInt / 256 + k.toInt % 256 ≤ 64)

/-- The auxint of an arm64 op in the range Go builds it in: a constant shift amount below 64
(`SLLconst`, `SRLconst`, `SRAconst`; Go's rules mask or bound every one), a bit field (`bfOK`:
`UBFX`, `UBFIZ`, `SBFX`, `SBFIZ`, `BFI`, `BFXIL`). The semantics reads any auxint
(`Arm64.amt`, `Arm64.bf`); Go's helpers on them (`armBFAuxInt`, `bfc.lsb()`) agree with it in
these ranges. -/
def auxRangeL (o : Op) (k : Int64) : Bool :=
  if o == .ARM64SLLconst || o == .ARM64SRLconst || o == .ARM64SRAconst then
    decide (0 ≤ k.toInt) && decide (k.toInt < 64)
  else if o == .ARM64UBFX || o == .ARM64UBFIZ || o == .ARM64SBFX || o == .ARM64SBFIZ ||
      o == .ARM64BFI || o == .ARM64BFXIL then bfOK k
  else true

mutual
/-- Every op node of the pattern has its auxint in range (`auxRangeL`). -/
def Pat.rangeL (ai : Path → Int64) (p : Path) : Pat → Bool
  | .op o _ _ _ _ _ args _ => auxRangeL o (ai p) && Pat.rangeLs ai p 0 args
  | _ => true
/-- `Pat.rangeL` of the arguments `i, i+1, …` of the node at `p`. -/
def Pat.rangeLs (ai : Path → Int64) (p : Path) (i : Nat) : List Pat → Bool
  | [] => true
  | q :: qs => Pat.rangeL ai (i :: p) q && Pat.rangeLs ai p (i + 1) qs
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
    argsOKLr r.loc e.ty r.pat = true →
    copyShapeOK ev e r.result →
    resFitsL (e.ty []) r.result = true →
    Pat.addrOKL e.ty e.aux e.auxInt [] r.pat = true →
    Pat.rangeL e.auxInt [] r.pat = true →
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

/-- The arguments of an ellipsis rule's op the validator requires at a 64-bit integer shape
(`GoFV.Opt.LowerCheck.setOpDef`): `AddPtr`'s index, which `PtrOps.addPtr` sign-extends where
`ADD` reads the register. -/
def setArgW64 (o : Op) (i : Nat) : Bool := o == .AddPtr && i == 1

/-- `SetOpSound` on arguments whose `setArgW64` ones hold 64-bit integers (`Val.hasTy`). -/
def SetOpSoundT (o o' : Op) : Prop :=
  ∀ (tabs : Tables) (ty : Ty) (ai : Int64) (ax : Option AuxRef) (args : List Val),
    topOKL o ty = true →
    (∀ i v, args[i]? = some v → setArgW64 o i = true → v.hasTy (.int .w64) = true) →
    Refines ((opValL tabs o ty ai ax args).retypeL ty) ((opValL tabs o' ty ai ax args).retypeL ty)

theorem SetOpSound.typed {o o' : Op} (h : SetOpSound o o') : SetOpSoundT o o' :=
  fun tabs ty ai ax args htop _ => h tabs ty ai ax args htop

/-- An ellipsis rule without a condition, from `o` to `o'`, both term ops of every value
(generic term ops or `armTerm` ops: not `MOVDaddr`, whose being a term depends on the aux), with
`SetOpSoundT o o'`. -/
def ArmRule.SetOp (r : Rule) : Prop :=
  ∃ o o', ellipsisOn o r.pat = true ∧ r.result = .setOp o' ∧ r.cond = none ∧ r.block = none ∧
    (∀ tabs (v : Value), v.op = o → termVL tabs v = true) ∧
    (∀ tabs (v : Value), v.op = o' → termVL tabs v = true) ∧ SetOpSoundT o o'

/-- The calls, tail calls, nil checks, the closure pointer, the caller's stack pointer and the
bounds panic `renameOp` relates (`panicBounds` on both sides for the bounds panic). -/
def callRename : Op → Op → Bool
  | .NilCheck, .ARM64LoweredNilCheck => true
  | .StaticCall, .ARM64CALLstatic => true
  | .ClosureCall, .ARM64CALLclosure => true
  | .InterCall, .ARM64CALLinter => true
  | .GetClosurePtr, .ARM64LoweredGetClosurePtr => true
  | .GetCallerSP, .ARM64LoweredGetCallerSP => true
  | .TailCall, .ARM64CALLtail => true
  | .TailCallInter, .ARM64CALLtailinter => true
  | .PanicBounds, .ARM64LoweredPanicBoundsRR => true
  | _, _ => false

/-- An arm64 atomic of the generic atomic it is (`Arm64.atomicOf`, `ARM64.rules:487-504`), or
`STLR` of `AtomicStorePtrNoWB` (`490`): `STLR` runs as `AtomicStore64`, which stores what
`AtomicStorePtrNoWB` stores (`encode` at a pointer and at a 64-bit integer agree;
`GoFV.Proof.Low.Sim.atomicRoot_ptrStore`). -/
def atomicRen (o o' : Op) : Bool :=
  Arm64.atomicOf o' == some o || o == .AtomicStorePtrNoWB && o' == .ARM64STLR

/-- The atom ellipsis rules the atom simulation relates by itself (`GoFV.Opt.LowerCheck.atomPair`):
the input atom and its renamed output have the same arguments and fields, and the output's
evaluation refines the input's (`GoFV.Proof.Low.atomPair_eval`): `callRename`'s, and an arm64
atomic of a generic atomic (`atomicRen`; `Sem.arm64Op` runs it as the generic atomic
`Arm64.atomicOf` gives on its operands fitted to the location, `Sem.atomicArgs`). -/
def renameOp (o o' : Op) : Bool := callRename o o' || atomicRen o o'

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

/-- The indexed arm64 stores, with the store each indexes and the index's scale: `MOV…storeidx
ptr idx val mem` stores as `MOV…store` at `ptr + idx`, `MOV…storeidx{2,4,8}` at `ptr + idx*scale`
(`Sem.arm64Op`'s `stIdx`). -/
def idxStore : Op → Option (Op × Nat)
  | .ARM64MOVBstoreidx => some (.ARM64MOVBstore, 1)
  | .ARM64MOVHstoreidx => some (.ARM64MOVHstore, 1)
  | .ARM64MOVWstoreidx => some (.ARM64MOVWstore, 1)
  | .ARM64MOVDstoreidx => some (.ARM64MOVDstore, 1)
  | .ARM64FMOVSstoreidx => some (.ARM64FMOVSstore, 1)
  | .ARM64FMOVDstoreidx => some (.ARM64FMOVDstore, 1)
  | .ARM64MOVHstoreidx2 => some (.ARM64MOVHstore, 2)
  | .ARM64MOVWstoreidx4 => some (.ARM64MOVWstore, 4)
  | .ARM64MOVDstoreidx8 => some (.ARM64MOVDstore, 8)
  | .ARM64FMOVSstoreidx4 => some (.ARM64FMOVSstore, 4)
  | .ARM64FMOVDstoreidx8 => some (.ARM64FMOVDstore, 8)
  | _ => none

/-- The atom `w` lowers the `Store` `u` to an indexed store (`idxStore`; `ARM64.rules:786-791`,
`806-808` index the arm64 store lowering it): no offset or aux, `u`'s three arguments and `w`'s four
(`ptr idx val mem`), a scalar `Store` type of the indexed store's size
(`GoFV.Proof.Low.Sim.idx_lower_eval`). -/
def idxLower (tabs : Tables) (u w : Value) : Bool :=
  u.op == .Store && u.args.size == 3 && w.args.size == 4 && w.auxInt == 0 && w.aux == none &&
    (idxStore w.op).any fun p => (stSize p.1).any (fitsB (auxTy tabs u.aux))

/-- The 128-bit store `lower` copies `Move [n]` with, and its number of arguments:
`(Move [16] dst src mem) => (FMOVQstore dst (FMOVQload src mem) mem)` (`ARM64.rules:418`) and
`(Move [32] dst src mem) => (FSTPQ dst (Select0 (FLDPQ src mem)) (Select1 (FLDPQ src mem)) mem)`
(`426`). -/
def moveQOp (n : Int64) : Option (Op × Nat) :=
  if n == 16 then some (.ARM64FMOVQstore, 3) else if n == 32 then some (.ARM64FSTPQ, 4) else none

/-- The 128-bit stores a `Move` lowers to (`moveQOp`). -/
def qStore (o : Op) : Bool := o == .ARM64FMOVQstore || o == .ARM64FSTPQ

theorem qStore_cases {o : Op} (h : qStore o = true) : o = .ARM64FMOVQstore ∨ o = .ARM64FSTPQ := by
  simpa [qStore] using h

/-- The 128-bit stores are neither scalar nor indexed arm64 stores. -/
theorem qStore_st {o : Op} (h : qStore o = true) : stSize o = none ∧ idxStore o = none := by
  rcases qStore_cases h with rfl | rfl <;> exact ⟨rfl, rfl⟩

/-- No scalar arm64 store is a 128-bit one. -/
theorem qStore_of_st {o : Op} (h : (stSize o).isSome = true) : qStore o = false := by
  cases hq : qStore o
  · rfl
  · rw [(qStore_st hq).1] at h; cases h

/-- The atom `w` lowers the `Move [n]` `u` (three arguments) to the 128-bit store `moveQOp n`, at
a small non-negative offset (`offOK`: 0 as lowered, or a folded `ADDconst` offset,
`ARM64.rules:779`, `782`) and an aux `Sem.symAddr` reads (`stAux`: none, or a symbol or frame
variable folded in, `909`, `913`). Its value arguments are the 16-byte halves `u` copies
(`GoFV.Proof.Low.qPart`; `GoFV.Proof.Low.Sim.moveQ_lower_eval`). -/
def moveQLower (tabs : Tables) (u w : Value) : Bool :=
  u.op == .Move && u.args.size == 3 && offOK w.auxInt && stAux tabs w.aux &&
    (moveQOp u.auxInt).any fun (o, k) => w.op == o && w.args.size == k

/-- The two 128-bit stores `lower` copies `Move [n]` with (`ARM64.rules:423`, `431`, `434`): the
outer store's op and number of arguments, then the inner one's. The inner store copies the first
16 or 32 bytes at offset 0, the outer the last ones at `n - 16 c` (`c` its 16-byte halves,
`q2Off`) on the inner one's memory:
* `(Move [s] dst src mem) && s > 24 && s < 32 => (FMOVQstore [int32(s-16)] dst (FMOVQload
  [int32(s-16)] src mem) (FMOVQstore dst (FMOVQload src mem) mem))` (`423`);
* `s > 40 && s <= 48`: the outer an `FMOVQstore [s-16]`, the inner an `FSTPQ` (`431`);
* `s > 48 && s <= 64`: the outer an `FSTPQ [s-32]`, the inner an `FSTPQ` (`434`). -/
def moveQ2Op (n : Int64) : Option (Op × Nat × Op × Nat) :=
  if 24 < n.toInt ∧ n.toInt < 32 then some (.ARM64FMOVQstore, 3, .ARM64FMOVQstore, 3)
  else if 40 < n.toInt ∧ n.toInt ≤ 48 then some (.ARM64FMOVQstore, 3, .ARM64FSTPQ, 4)
  else if 48 < n.toInt ∧ n.toInt ≤ 64 then some (.ARM64FSTPQ, 4, .ARM64FSTPQ, 4)
  else none

/-- The offset of the outer store of `Move [n]`'s two 128-bit stores (`moveQ2Op`): `n - 16 c`,
`c` the outer store's halves. -/
def q2Off (n : Int64) : Nat :=
  match moveQ2Op n with
  | some (_, ko, _, _) => n.toInt.toNat - 16 * (ko - 2)
  | none => 0

/-- The atom `w` is the outer store of the two 128-bit stores lowering the `Move [n]` `u` (three
arguments; `moveQ2Op`). Its last argument is the inner store (`moveQ2In`), a fresh atom
(`GoFV.Opt.LowerCheck.moveDef2`, `compOKL`; `GoFV.Proof.Low.Sim.moveQ2_outer_eval`). -/
def moveQ2Lower (u w : Value) : Bool :=
  u.op == .Move && u.args.size == 3 &&
    (moveQ2Op u.auxInt).any fun (o, k, _, _) => w.op == o && w.args.size == k

/-- The atom `w` is the inner store of the two 128-bit stores lowering the `Move [n]` `u`
(`moveQ2Op`). -/
def moveQ2In (u w : Value) : Bool :=
  (moveQ2Op u.auxInt).any fun (_, _, o, k) => w.op == o && w.args.size == k

/-- The arm64 store `lower` zeroes `Zero [n]` with, and its number of arguments: `(Zero [1] ptr
mem) => (MOVBstore ptr (MOVDconst [0]) mem)` (`ARM64.rules:336`), `MOVHstore` for `Zero [2]`
(`337`), `MOVWstore` for `Zero [4]` (`338`), `MOVDstore` for `Zero [8]` (`351`), and `(Zero [16]
ptr mem) => (STP [0] ptr (MOVDconst [0]) (MOVDconst [0]) mem)` (`373`). -/
def zeroOp (n : Int64) : Option (Op × Nat) :=
  if n == 1 then some (.ARM64MOVBstore, 3) else if n == 2 then some (.ARM64MOVHstore, 3)
  else if n == 4 then some (.ARM64MOVWstore, 3) else if n == 8 then some (.ARM64MOVDstore, 3)
  else if n == 16 then some (.ARM64STP, 4) else none

/-- The stores lowering a `Zero` (`zeroOp`): the scalar integer stores and `STP`. -/
def zStore (o : Op) : Bool :=
  o == .ARM64MOVBstore || o == .ARM64MOVHstore || o == .ARM64MOVWstore || o == .ARM64MOVDstore ||
    o == .ARM64STP

/-- The atom `w` lowers the `Zero [n]` `u` (two arguments) to the store `zeroOp n` of the constant
`0`, at a small non-negative offset (`offOK`: 0 as lowered, or a folded offset) and an aux
`Sem.symAddr` reads (`stAux`: none, or a symbol or frame variable folded in). -/
def zeroLower (tabs : Tables) (u w : Value) : Bool :=
  u.op == .Zero && u.args.size == 2 && offOK w.auxInt && stAux tabs w.aux &&
    (zeroOp u.auxInt).any fun (o, k) => w.op == o && w.args.size == k

/-- The atom `w` lowers the `Zero [n]` `u` (two arguments) to an indexed store (`idxStore`) of the
store `zeroOp n` of the constant `0`: the store at offset 0 without aux indexed (`ARM64.rules:786`
-`791`, `806`-`808`) and its index scaled (`809`, `810`), with four arguments `ptr idx val mem` and
no offset or aux (`GoFV.Opt.LowerCheck.atomDef1`; `GoFV.Proof.Low.Sim.zeroIdx_lower_eval`). -/
def zeroIdxLower (u w : Value) : Bool :=
  u.op == .Zero && u.args.size == 2 && w.args.size == 4 && w.auxInt == 0 && w.aux == none &&
    (zeroOp u.auxInt).any fun (o, _) => (idxStore w.op).any (·.1 == o)

/-- The two stores `lower` zeroes `Zero [n]` with (`ARM64.rules:339`-`370`): the outer store's op
and offset, then the inner one's op (offset 0), all of three arguments, the outer store on the
inner one's memory, the two overlapping where `n` is not their sizes' sum: `(Zero [3] ptr mem) =>
(MOVBstore [2] ptr (MOVDconst [0]) (MOVHstore ptr (MOVDconst [0]) mem))` (`339`), `Zero [5]`,
`[6]`, `[7]` on a `MOVWstore` (`342`, `345`, `348`), `Zero [9]` … `[15]` on a `MOVDstore` (`352`
… `370`). -/
def zero2Op (n : Int64) : Option (Op × Nat × Op) :=
  if n == 3 then some (.ARM64MOVBstore, 2, .ARM64MOVHstore)
  else if n == 5 then some (.ARM64MOVBstore, 4, .ARM64MOVWstore)
  else if n == 6 then some (.ARM64MOVHstore, 4, .ARM64MOVWstore)
  else if n == 7 then some (.ARM64MOVWstore, 3, .ARM64MOVWstore)
  else if n == 9 then some (.ARM64MOVBstore, 8, .ARM64MOVDstore)
  else if n == 10 then some (.ARM64MOVHstore, 8, .ARM64MOVDstore)
  else if n == 11 then some (.ARM64MOVDstore, 3, .ARM64MOVDstore)
  else if n == 12 then some (.ARM64MOVWstore, 8, .ARM64MOVDstore)
  else if n == 13 then some (.ARM64MOVDstore, 5, .ARM64MOVDstore)
  else if n == 14 then some (.ARM64MOVDstore, 6, .ARM64MOVDstore)
  else if n == 15 then some (.ARM64MOVDstore, 7, .ARM64MOVDstore)
  else none

/-- The offset of the outer store of `Zero [n]`'s two stores (`zero2Op`). -/
def z2Off (n : Int64) : Nat :=
  match zero2Op n with
  | some (_, k, _) => k
  | none => 0

/-- The atom `w` is the outer store of the two stores lowering the `Zero [n]` `u` (two arguments;
`zero2Op`). Its last argument is the inner store (`zero2In`), a fresh atom
(`GoFV.Opt.LowerCheck.zeroDef2`, `compOKL`; `GoFV.Proof.Low.Sim.zero2_outer_eval`). -/
def zero2Lower (u w : Value) : Bool :=
  u.op == .Zero && u.args.size == 2 &&
    (zero2Op u.auxInt).any fun (o, _, _) => w.op == o && w.args.size == 3

/-- The atom `w` is the inner store of the two stores lowering the `Zero [n]` `u` (`zero2Op`). -/
def zero2In (u w : Value) : Bool :=
  (zero2Op u.auxInt).any fun (_, _, o) => w.op == o && w.args.size == 3

/-- The atom `w` is the outer store of two lowering `u`: a `Move` (`moveQ2Lower`) or a `Zero`
(`zero2Lower`). -/
def st2Lower (u w : Value) : Bool := moveQ2Lower u w || zero2Lower u w

/-- The atom `w` lowers the frame address `u`: `(LocalAddr <t> {sym} base _) => (MOVDaddr {sym}
base)` and `(MOVDaddr {sym} (SPanchored base mem))`, with the same frame variable `{sym}` (a
`.name` aux) at offset 0 and one argument, whose value it ignores
(`GoFV.Proof.Low.addr_lower_eval`). -/
def addrLower (tabs : Tables) (u w : Value) : Bool :=
  u.op == .LocalAddr && w.op == .ARM64MOVDaddr && w.auxInt == 0 && w.aux == u.aux &&
    auxIsName tabs u.aux && w.args.size == 1

/-- The atom `w` lowers `Zero {t} [n] ptr mem` to `LoweredZero [n] ptr mem` (`ARM64.rules:376`; from
192 bytes `LoweredZeroLoop`, `377`), or `Move {t} [n] dst src mem` to `LoweredMove [n] dst src
mem` (`438`; from 192 bytes `LoweredMoveLoop`, `439`): the same size; both zero or copy `n` bytes
(`GoFV.Proof.Low.Sim.zero_lower_eval`, `move_lower_eval`). The validator keeps the arguments
(`atomDef`). -/
def bulkLower (u w : Value) : Bool :=
  (u.op == .Zero && (w.op == .ARM64LoweredZero || w.op == .ARM64LoweredZeroLoop) ||
    u.op == .Move && (w.op == .ARM64LoweredMove || w.op == .ARM64LoweredMoveLoop)) &&
    u.auxInt == w.auxInt

/-- What `bulkLower` says. -/
theorem bulkLower_cases {u w : Value} (h : bulkLower u w = true) :
    (u.op = .Zero ∧ (w.op = .ARM64LoweredZero ∨ w.op = .ARM64LoweredZeroLoop) ∨
      u.op = .Move ∧ (w.op = .ARM64LoweredMove ∨ w.op = .ARM64LoweredMoveLoop)) ∧
      u.auxInt = w.auxInt := by
  unfold bulkLower at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact h

/-- The ops a lowered `Zero` or `Move` (`bulkLower`) is. -/
theorem bulkLower_op {u w : Value} (h : bulkLower u w = true) :
    w.op = .ARM64LoweredZero ∨ w.op = .ARM64LoweredZeroLoop ∨ w.op = .ARM64LoweredMove ∨
      w.op = .ARM64LoweredMoveLoop := by
  rcases (bulkLower_cases h).1 with ⟨-, h | h⟩ | ⟨-, h | h⟩ <;> simp [h]

/-- The arguments of `PanicBounds [kind] x y mem` that a lowering with constant operands folded
into its aux keeps (`ARM64.rules:513-516`): `LoweredPanicBoundsRC [kind] {C} x mem` keeps `x` and
`mem`, `CR` keeps `y` and `mem`, `CC` keeps `mem`. -/
def pbKeep : Op → Option (List Nat)
  | .ARM64LoweredPanicBoundsRC => some [0, 2]
  | .ARM64LoweredPanicBoundsCR => some [1, 2]
  | .ARM64LoweredPanicBoundsCC => some [2]
  | _ => none

/-- The atom `w` lowers the bounds panic `u` with constant operands folded into its aux
(`pbKeep`): the same auxint (the bounds kind), and `w` has one argument per kept one of `u`'s three.
`GoFV.Opt.LowerCheck.pbConstOK` relates the aux to `u`'s dropped operands. -/
def pbLower (u w : Value) : Bool :=
  u.op == .PanicBounds && u.args.size == 3 && u.auxInt == w.auxInt &&
    (pbKeep w.op).any (w.args.size == ·.length)

/-- The argument of the atom `u` that argument `i` of its corresponding atom `w` reads: the kept
one for a bounds panic with constant operands (`pbLower`), else `i`. -/
def argIx (u w : Value) (i : Nat) : Nat :=
  if pbLower u w then ((pbKeep w.op).getD [])[i]?.getD i else i

/-- What `pbKeep` says. -/
theorem pbKeep_cases {o : Op} {ks : List Nat} (h : pbKeep o = some ks) :
    (o = .ARM64LoweredPanicBoundsRC ∧ ks = [0, 2]) ∨ (o = .ARM64LoweredPanicBoundsCR ∧ ks = [1, 2]) ∨
      (o = .ARM64LoweredPanicBoundsCC ∧ ks = [2]) := by
  unfold pbKeep at h
  split at h <;> simp_all

/-- What `pbLower` says. -/
theorem pbLower_cases {u w : Value} (h : pbLower u w = true) :
    u.op = .PanicBounds ∧ u.args.size = 3 ∧ u.auxInt = w.auxInt ∧
      ∃ ks, pbKeep w.op = some ks ∧ w.args.size = ks.length := by
  unfold pbLower at h
  simp only [Bool.and_eq_true, beq_iff_eq, Option.any_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, ks, hk, hs⟩ := h
  exact ⟨h1, h2, h3, ks, hk, by simpa using hs⟩

/-- `argIx` is the identity unless `w` lowers a bounds panic with constant operands. -/
theorem argIx_of_not {u w : Value} (h : pbLower u w = false) (i : Nat) : argIx u w i = i := by
  simp [argIx, h]

/-- `argIx` of a bounds panic with constant operands: the kept argument. -/
theorem argIx_of_pb {u w : Value} (h : pbLower u w = true) {ks : List Nat}
    (hk : pbKeep w.op = some ks) {i : Nat} (hi : i < ks.length) : argIx u w i = ks[i] := by
  simp [argIx, h, hk, hi]

/-- The kept arguments are among the three of `PanicBounds`. -/
theorem pbKeep_lt {o : Op} {ks : List Nat} (h : pbKeep o = some ks) {i : Nat} (hi : i < ks.length) :
    ks[i] < 3 := by
  rcases pbKeep_cases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
    (simp only [List.length_cons, List.length_nil] at hi) <;> (rcases i with _ | _ | i) <;>
    first | omega | simp

/-- A bounds panic with constant operands keeps fewer than the three arguments. -/
theorem pbKeep_len {o : Op} {ks : List Nat} (h : pbKeep o = some ks) : ks.length < 3 := by
  rcases pbKeep_cases h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide

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

/-- An indexed store (`idxStore`): an arm64 root, no plain arm64 store, `Phi`, `MOVDaddr` or
bounds panic, indexing an arm64 store at the scale 1, 2, 4 or 8. -/
theorem idxStore_facts {o p : Op} {s : Nat} (h : idxStore o = some (p, s)) :
    o.generic = false ∧ stSize o = none ∧ (stSize p).isSome = true ∧ isRoot o = true ∧
      o ≠ .Phi ∧ o ≠ .ARM64MOVDaddr ∧ pbKeep o = none ∧ (s = 1 ∨ s = 2 ∨ s = 4 ∨ s = 8) := by
  unfold idxStore at h
  split at h <;> first | (cases h; done) | (cases h; decide)

/-- What `idxLower` says. -/
theorem idxLower_cases {tabs : Tables} {u w : Value} (h : idxLower tabs u w = true) :
    u.op = .Store ∧ u.args.size = 3 ∧ w.args.size = 4 ∧ w.auxInt = 0 ∧ w.aux = none ∧
      ∃ p s n, idxStore w.op = some (p, s) ∧ stSize p = some n ∧
        fitsB (auxTy tabs u.aux) n = true := by
  unfold idxLower at h
  simp only [Bool.and_eq_true, beq_iff_eq, Option.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, ⟨p, s⟩, hp, n, hn, hf⟩ := h
  exact ⟨h1, h2, h3, h4, h5, p, s, n, hp, hn, hf⟩

/-- An arm64 atomic and the generic atomic it is (`Arm64.atomicOf`): a generic root
`atomicRoot` models and an arm64 root, neither an arm64 store, a `Phi` or `MOVDaddr`. -/
theorem atomicOf_facts {o o' : Op} (h : Arm64.atomicOf o' = some o) :
    o.generic = true ∧ o'.generic = false ∧ stSize o = none ∧ stSize o' = none ∧
      isRoot o = true ∧ isRoot o' = true ∧ o ≠ .Phi ∧ o' ≠ .Phi ∧ o' ≠ .ARM64MOVDaddr ∧
      ((Atomic.info? o).isSome || (Atomic.casWidth? o).isSome) = true := by
  unfold Arm64.atomicOf at h
  split at h <;> first | (cases h; done) | (cases h; decide)

/-- `atomicRen`'s ops: `atomicOf_facts`'. -/
theorem atomicRen_facts {o o' : Op} (h : atomicRen o o' = true) :
    o.generic = true ∧ o'.generic = false ∧ stSize o = none ∧ stSize o' = none ∧
      isRoot o = true ∧ isRoot o' = true ∧ o ≠ .Phi ∧ o' ≠ .Phi ∧ o' ≠ .ARM64MOVDaddr ∧
      ((Atomic.info? o).isSome || (Atomic.casWidth? o).isSome) = true := by
  unfold atomicRen at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with h | ⟨rfl, rfl⟩
  · exact atomicOf_facts h
  · decide

/-- Renamed atoms are no arm64 stores. -/
theorem renameOp_stSize {o o' : Op} (h : renameOp o o' = true) :
    stSize o = none ∧ stSize o' = none := by
  unfold renameOp at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · unfold callRename at h
    split at h <;> first | (cases h; done) | exact ⟨rfl, rfl⟩
  · obtain ⟨-, -, h1, h2, -⟩ := atomicRen_facts h
    exact ⟨h1, h2⟩

/-- Renamed atoms are no 128-bit stores. -/
theorem renameOp_qStore {o o' : Op} (h : renameOp o o' = true) :
    qStore o = false ∧ qStore o' = false := by
  unfold renameOp at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · unfold callRename at h
    split at h <;> first | (cases h; done) | exact ⟨rfl, rfl⟩
  · have hg := (atomicRen_facts h).1
    refine ⟨?_, ?_⟩
    · cases hq : qStore o
      · rfl
      · rcases qStore_cases hq with rfl | rfl <;> cases hg
    · cases hq : qStore o'
      · rfl
      · unfold atomicRen at h
        rcases qStore_cases hq with rfl | rfl <;> simp at h <;> cases h

/-- The stores lowering a `Zero` are scalar arm64 stores or `STP`. -/
theorem zStore_cases {o : Op} (h : zStore o = true) : (stSize o).isSome = true ∨ o = .ARM64STP := by
  unfold zStore at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (((rfl | rfl) | rfl) | rfl) | rfl
  all_goals first | exact .inr rfl | exact .inl rfl

/-- No store lowering a `Zero` is a 128-bit store. -/
theorem zStore_qStore {o : Op} (h : zStore o = true) : qStore o = false := by
  rcases zStore_cases h with h | rfl
  · exact qStore_of_st h
  · rfl

/-- Renamed atoms are no stores lowering a `Zero`. -/
theorem renameOp_zStore {o o' : Op} (h : renameOp o o' = true) : zStore o = false := by
  cases hz : zStore o
  · rfl
  · rcases zStore_cases hz with h1 | rfl
    · rw [(renameOp_stSize h).1] at h1; cases h1
    · unfold renameOp at h
      simp only [Bool.or_eq_true] at h
      rcases h with h | h
      · unfold callRename at h; cases h
      · cases (atomicRen_facts h).1

/-- A `Zero` is renamed to no atom. -/
theorem renameOp_zero (o' : Op) : renameOp .Zero o' = false := by
  cases h : renameOp .Zero o'
  · rfl
  · unfold renameOp at h
    simp only [Bool.or_eq_true] at h
    rcases h with h | h
    · unfold callRename at h; cases h
    · exact absurd (atomicRen_facts h).2.2.2.2.2.2.2.2.2 (by decide)

/-- No store lowering a `Zero` is an indexed store. -/
theorem zStore_idx {o : Op} (h : zStore o = true) : idxStore o = none := by
  unfold zStore at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (((rfl | rfl) | rfl) | rfl) | rfl <;> rfl

/-- What `zeroOp` says: a store lowering a `Zero`, of at least three arguments. -/
theorem zeroOp_some {n : Int64} {o : Op} {k : Nat} (h : zeroOp n = some (o, k)) :
    zStore o = true ∧ 3 ≤ k := by
  unfold zeroOp at h
  split at h
  · cases h; exact ⟨rfl, by omega⟩
  split at h
  · cases h; exact ⟨rfl, by omega⟩
  split at h
  · cases h; exact ⟨rfl, by omega⟩
  split at h
  · cases h; exact ⟨rfl, by omega⟩
  split at h
  · cases h; exact ⟨rfl, by omega⟩
  · cases h

/-- What `zeroLower` says: a `Zero` of two arguments and a store lowering it (`zeroOp`) at a small
non-negative offset and an aux `Sem.symAddr` reads. -/
theorem zeroLower_facts {tabs : Tables} {u w : Value} (h : zeroLower tabs u w = true) :
    u.op = .Zero ∧ u.args.size = 2 ∧ offOK w.auxInt = true ∧ stAux tabs w.aux = true ∧
      zStore w.op = true ∧ 3 ≤ w.args.size := by
  unfold zeroLower at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hu, h2⟩, hk⟩, hax⟩, h⟩ := h
  cases hz : zeroOp u.auxInt with
  | none => rw [hz] at h; cases h
  | some p =>
    obtain ⟨o, k⟩ := p
    rw [hz] at h
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hzs, hk3⟩ := zeroOp_some hz
    exact ⟨hu, h2, hk, hax, h.1 ▸ hzs, h.2 ▸ hk3⟩

/-- A scalar arm64 store `zeroOp n` gives is of `n` bytes, 1, 2, 4 or 8. -/
theorem zeroOp_st {n : Int64} {o : Op} {k : Nat} (h : zeroOp n = some (o, k))
    (hs : (stSize o).isSome = true) :
    stSize o = some n.toInt.toNat ∧
      (n.toInt.toNat = 1 ∨ n.toInt.toNat = 2 ∨ n.toInt.toNat = 4 ∨ n.toInt.toNat = 8) := by
  unfold zeroOp at h
  split at h
  · rename_i hc; cases h; obtain rfl : n = 1 := by simpa using hc
    exact ⟨rfl, by decide⟩
  split at h
  · rename_i hc; cases h; obtain rfl : n = 2 := by simpa using hc
    exact ⟨rfl, by decide⟩
  split at h
  · rename_i hc; cases h; obtain rfl : n = 4 := by simpa using hc
    exact ⟨rfl, by decide⟩
  split at h
  · rename_i hc; cases h; obtain rfl : n = 8 := by simpa using hc
    exact ⟨rfl, by decide⟩
  split at h
  · cases h; exact absurd hs (by decide)
  · cases h

/-- What `zeroIdxLower` says: a `Zero` of two arguments and an indexed store of four arguments
without offset or aux, indexing the store `zeroOp` gives. -/
theorem zeroIdxLower_facts {u w : Value} (h : zeroIdxLower u w = true) :
    u.op = .Zero ∧ u.args.size = 2 ∧ w.args.size = 4 ∧ w.auxInt = 0 ∧ w.aux = none ∧
      ∃ o k s, zeroOp u.auxInt = some (o, k) ∧ idxStore w.op = some (o, s) := by
  unfold zeroIdxLower at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hu, h2⟩, h4⟩, hk⟩, hax⟩, h⟩ := h
  refine ⟨hu, h2, h4, hk, hax, ?_⟩
  cases hz : zeroOp u.auxInt with
  | none => rw [hz] at h; cases h
  | some p =>
    obtain ⟨o, k⟩ := p
    rw [hz] at h
    simp only [Option.any_some] at h
    cases hi : idxStore w.op with
    | none => rw [hi] at h; cases h
    | some q =>
      obtain ⟨o', s⟩ := q
      rw [hi] at h
      simp only [Option.any_some, beq_iff_eq] at h
      exact ⟨o, k, s, rfl, by rw [h]⟩

/-- The indexed store of `zeroIdxLower` stores `n` bytes, 1, 2, 4 or 8, of the `Zero [n]`. -/
theorem zeroIdxLower_size {u w : Value} (h : zeroIdxLower u w = true) :
    ∃ o s, idxStore w.op = some (o, s) ∧ stSize o = some u.auxInt.toInt.toNat ∧
      (u.auxInt.toInt.toNat = 1 ∨ u.auxInt.toInt.toNat = 2 ∨ u.auxInt.toInt.toNat = 4 ∨
        u.auxInt.toInt.toNat = 8) := by
  obtain ⟨-, -, -, -, -, o, k, s, hz, hi⟩ := zeroIdxLower_facts h
  obtain ⟨h1, h2⟩ := zeroOp_st hz (idxStore_facts hi).2.2.1
  exact ⟨o, s, hi, h1, h2⟩

/-- What `moveQLower` says about the ops: a `Move` with three arguments and a 128-bit store. -/
theorem moveQLower_qStore {tabs : Tables} {u w : Value} (h : moveQLower tabs u w = true) :
    u.op = .Move ∧ u.args.size = 3 ∧ qStore w.op = true := by
  unfold moveQLower moveQOp at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hu, h3⟩, -⟩, -⟩, h⟩ := h
  refine ⟨hu, h3, ?_⟩
  split at h
  · simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h; rw [h.1]; rfl
  · split at h
    · simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h; rw [h.1]; rfl
    · simp at h

/-- What `moveQ2Op` says: two 128-bit stores, the outer at `q2Off n` (`k`) writing up to `n`, the
inner from 0 up to at least `k` and at most `n ≤ 64` (`ARM64.rules:423`, `431`, `434`). -/
theorem moveQ2Op_cases {n : Int64} {oo : Op} {ko : Nat} {oi : Op} {ki : Nat}
    (h : moveQ2Op n = some (oo, ko, oi, ki)) :
    ((oo = .ARM64FMOVQstore ∧ ko = 3) ∨ (oo = .ARM64FSTPQ ∧ ko = 4)) ∧
    ((oi = .ARM64FMOVQstore ∧ ki = 3) ∨ (oi = .ARM64FSTPQ ∧ ki = 4)) ∧
    q2Off n + 16 * (ko - 2) = n.toInt.toNat ∧ q2Off n ≤ 16 * (ki - 2) ∧
    16 * (ki - 2) ≤ n.toInt.toNat ∧ n.toInt.toNat ≤ 64 ∧ 24 < n.toInt ∧ n.toInt ≠ 32 := by
  have hq : q2Off n = n.toInt.toNat - 16 * (ko - 2) := by unfold q2Off; rw [h]
  rw [hq]
  unfold moveQ2Op at h
  split at h
  · rename_i hc; cases h
    exact ⟨.inl ⟨rfl, rfl⟩, .inl ⟨rfl, rfl⟩, by omega⟩
  · split at h
    · rename_i hc; cases h
      exact ⟨.inl ⟨rfl, rfl⟩, .inr ⟨rfl, rfl⟩, by omega⟩
    · split at h
      · rename_i hc; cases h
        exact ⟨.inr ⟨rfl, rfl⟩, .inr ⟨rfl, rfl⟩, by omega⟩
      · cases h

/-- What `moveQ2Lower` says: a `Move` with three arguments and the outer store of `moveQ2Op`. -/
theorem moveQ2Lower_facts {u w : Value} (h : moveQ2Lower u w = true) :
    u.op = .Move ∧ u.args.size = 3 ∧ ∃ ko oi ki, moveQ2Op u.auxInt = some (w.op, ko, oi, ki) ∧
      w.args.size = ko := by
  unfold moveQ2Lower at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hu, h3⟩, h⟩ := h
  refine ⟨hu, h3, ?_⟩
  cases hq : moveQ2Op u.auxInt with
  | none => rw [hq] at h; cases h
  | some q =>
    obtain ⟨oo, ko, oi, ki⟩ := q
    rw [hq] at h
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨ko, oi, ki, by rw [h.1], h.2⟩

/-- What `moveQ2In` says: the inner store of `moveQ2Op`. -/
theorem moveQ2In_facts {u w : Value} (h : moveQ2In u w = true) :
    ∃ oo ko, moveQ2Op u.auxInt = some (oo, ko, w.op, w.args.size) := by
  unfold moveQ2In at h
  cases hq : moveQ2Op u.auxInt with
  | none => rw [hq] at h; cases h
  | some q =>
    obtain ⟨oo, ko, oi, ki⟩ := q
    rw [hq] at h
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨oo, ko, by rw [h.1, h.2]⟩

/-- The outer store of `moveQ2Lower` is a 128-bit store. -/
theorem moveQ2Lower_qStore {u w : Value} (h : moveQ2Lower u w = true) : qStore w.op = true := by
  obtain ⟨-, -, ko, oi, ki, hq, -⟩ := moveQ2Lower_facts h
  rcases (moveQ2Op_cases hq).1 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> rfl

/-- The inner store of `moveQ2In` is a 128-bit store. -/
theorem moveQ2In_qStore {u w : Value} (h : moveQ2In u w = true) : qStore w.op = true := by
  obtain ⟨oo, ko, hq⟩ := moveQ2In_facts h
  rcases (moveQ2Op_cases hq).2.1 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1] <;> rfl

/-- No `Move` lowers to a single 128-bit store and to two. -/
theorem moveQ2Lower_not_moveQ {tabs : Tables} {u w w' : Value} (h : moveQ2Lower u w = true) :
    moveQLower tabs u w' = false := by
  obtain ⟨-, -, ko, oi, ki, hq, -⟩ := moveQ2Lower_facts h
  have hc := moveQ2Op_cases hq
  cases h2 : moveQLower tabs u w'
  · rfl
  · exfalso
    unfold moveQLower moveQOp at h2
    simp only [Bool.and_eq_true, beq_iff_eq] at h2
    have h2 := h2.2
    split at h2
    · rename_i h16
      have : u.auxInt.toInt = 16 := by rw [show u.auxInt = 16 by simpa using h16]; decide
      omega
    · split at h2
      · rename_i h32
        have : u.auxInt.toInt = 32 := by rw [show u.auxInt = 32 by simpa using h32]; decide
        omega
      · simp at h2

/-- A scalar integer store of `s` bytes (`MOV{B,H,W,D}store`). -/
def ZSt (o : Op) (s : Nat) : Prop :=
  (o = .ARM64MOVBstore ∧ s = 1) ∨ (o = .ARM64MOVHstore ∧ s = 2) ∨ (o = .ARM64MOVWstore ∧ s = 4) ∨
    (o = .ARM64MOVDstore ∧ s = 8)

/-- A scalar integer store lowers a `Zero` (`zStore`) and has its size (`stSize`). -/
theorem ZSt.facts {o : Op} {s : Nat} (h : ZSt o s) : zStore o = true ∧ stSize o = some s := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨rfl, rfl⟩

/-- What `zero2Op` says: two scalar integer stores, the outer of `so` bytes at `z2Off n` (`k`)
writing up to `n`, the inner of `si` bytes from 0 up to at least `k` (`ARM64.rules:339`-`370`). -/
theorem zero2Op_cases {n : Int64} {oo : Op} {k : Nat} {oi : Op}
    (h : zero2Op n = some (oo, k, oi)) :
    z2Off n = k ∧ ∃ so si, ZSt oo so ∧ ZSt oi si ∧ k + so = n.toInt.toNat ∧ 0 < k ∧ k ≤ si ∧
      si ≤ n.toInt.toNat := by
  refine ⟨by unfold z2Off; rw [h], ?_⟩
  unfold zero2Op at h
  split at h
  · rename_i hc; cases h; obtain rfl : n = 3 := by simpa using hc
    exact ⟨1, 2, by unfold ZSt; decide, by unfold ZSt; decide, by decide, by decide, by decide,
      by decide⟩
  split at h
  · rename_i hc; cases h; obtain rfl : n = 5 := by simpa using hc
    exact ⟨1, 4, by unfold ZSt; decide, by unfold ZSt; decide, by decide, by decide, by decide,
      by decide⟩
  split at h
  · rename_i hc; cases h; obtain rfl : n = 6 := by simpa using hc
    exact ⟨2, 4, by unfold ZSt; decide, by unfold ZSt; decide, by decide, by decide, by decide,
      by decide⟩
  split at h
  · rename_i hc; cases h; obtain rfl : n = 7 := by simpa using hc
    exact ⟨4, 4, by unfold ZSt; decide, by unfold ZSt; decide, by decide, by decide, by decide,
      by decide⟩
  split at h
  · rename_i hc; cases h; obtain rfl : n = 9 := by simpa using hc
    exact ⟨1, 8, by unfold ZSt; decide, by unfold ZSt; decide, by decide, by decide, by decide,
      by decide⟩
  split at h
  · rename_i hc; cases h; obtain rfl : n = 10 := by simpa using hc
    exact ⟨2, 8, by unfold ZSt; decide, by unfold ZSt; decide, by decide, by decide, by decide,
      by decide⟩
  split at h
  · rename_i hc; cases h; obtain rfl : n = 11 := by simpa using hc
    exact ⟨8, 8, by unfold ZSt; decide, by unfold ZSt; decide, by decide, by decide, by decide,
      by decide⟩
  split at h
  · rename_i hc; cases h; obtain rfl : n = 12 := by simpa using hc
    exact ⟨4, 8, by unfold ZSt; decide, by unfold ZSt; decide, by decide, by decide, by decide,
      by decide⟩
  split at h
  · rename_i hc; cases h; obtain rfl : n = 13 := by simpa using hc
    exact ⟨8, 8, by unfold ZSt; decide, by unfold ZSt; decide, by decide, by decide, by decide,
      by decide⟩
  split at h
  · rename_i hc; cases h; obtain rfl : n = 14 := by simpa using hc
    exact ⟨8, 8, by unfold ZSt; decide, by unfold ZSt; decide, by decide, by decide, by decide,
      by decide⟩
  split at h
  · rename_i hc; cases h; obtain rfl : n = 15 := by simpa using hc
    exact ⟨8, 8, by unfold ZSt; decide, by unfold ZSt; decide, by decide, by decide, by decide,
      by decide⟩
  · cases h

/-- No `Zero` lowers to one store and to two. -/
theorem zero2Op_zeroOp {n : Int64} {p : Op × Nat × Op} (h : zero2Op n = some p) :
    zeroOp n = none := by
  unfold zero2Op at h
  split at h
  · rename_i hc; obtain rfl : n = 3 := by simpa using hc
    decide
  split at h
  · rename_i hc; obtain rfl : n = 5 := by simpa using hc
    decide
  split at h
  · rename_i hc; obtain rfl : n = 6 := by simpa using hc
    decide
  split at h
  · rename_i hc; obtain rfl : n = 7 := by simpa using hc
    decide
  split at h
  · rename_i hc; obtain rfl : n = 9 := by simpa using hc
    decide
  split at h
  · rename_i hc; obtain rfl : n = 10 := by simpa using hc
    decide
  split at h
  · rename_i hc; obtain rfl : n = 11 := by simpa using hc
    decide
  split at h
  · rename_i hc; obtain rfl : n = 12 := by simpa using hc
    decide
  split at h
  · rename_i hc; obtain rfl : n = 13 := by simpa using hc
    decide
  split at h
  · rename_i hc; obtain rfl : n = 14 := by simpa using hc
    decide
  split at h
  · rename_i hc; obtain rfl : n = 15 := by simpa using hc
    decide
  · cases h

/-- What `zero2Lower` says: a `Zero` of two arguments and the outer store of `zero2Op`, of three
arguments. -/
theorem zero2Lower_facts {u w : Value} (h : zero2Lower u w = true) :
    u.op = .Zero ∧ u.args.size = 2 ∧ w.args.size = 3 ∧
      ∃ k oi, zero2Op u.auxInt = some (w.op, k, oi) := by
  unfold zero2Lower at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hu, h2⟩, h⟩ := h
  refine ⟨hu, h2, ?_⟩
  cases hq : zero2Op u.auxInt with
  | none => rw [hq] at h; cases h
  | some q =>
    obtain ⟨oo, k, oi⟩ := q
    rw [hq] at h
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨h.2, k, oi, by rw [h.1]⟩

/-- What `zero2In` says: the inner store of `zero2Op`, of three arguments. -/
theorem zero2In_facts {u w : Value} (h : zero2In u w = true) :
    w.args.size = 3 ∧ ∃ oo k, zero2Op u.auxInt = some (oo, k, w.op) := by
  unfold zero2In at h
  cases hq : zero2Op u.auxInt with
  | none => rw [hq] at h; cases h
  | some q =>
    obtain ⟨oo, k, oi⟩ := q
    rw [hq] at h
    simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨h.2, oo, k, by rw [h.1]⟩

/-- The outer store of `zero2Lower` lowers a `Zero` (`zStore`), a scalar store. -/
theorem zero2Lower_zStore {u w : Value} (h : zero2Lower u w = true) :
    zStore w.op = true ∧ (stSize w.op).isSome = true := by
  obtain ⟨-, -, -, k, oi, hq⟩ := zero2Lower_facts h
  obtain ⟨-, so, -, hso, -⟩ := zero2Op_cases hq
  rw [hso.facts.2]
  exact ⟨hso.facts.1, rfl⟩

/-- The inner store of `zero2In` lowers a `Zero` (`zStore`), a scalar store. -/
theorem zero2In_zStore {u w : Value} (h : zero2In u w = true) :
    zStore w.op = true ∧ (stSize w.op).isSome = true := by
  obtain ⟨-, oo, k, hq⟩ := zero2In_facts h
  obtain ⟨-, so, si, -, hsi, -⟩ := zero2Op_cases hq
  rw [hsi.facts.2]
  exact ⟨hsi.facts.1, rfl⟩

/-- No `Zero` lowers to a single store and to two. -/
theorem zero2Lower_not_zero {tabs : Tables} {u w w' : Value} (h : zero2Lower u w = true) :
    zeroLower tabs u w' = false := by
  obtain ⟨-, -, -, k, oi, hq⟩ := zero2Lower_facts h
  unfold zeroLower
  rw [zero2Op_zeroOp hq]
  simp

/-- The outer store of two lowering a `Zero` is no 128-bit store. -/
theorem zero2Lower_not_moveQ2 {u w w' : Value} (h : zero2Lower u w = true) :
    moveQ2Lower u w' = false := by
  cases h2 : moveQ2Lower u w'
  · rfl
  · obtain ⟨hu, -⟩ := zero2Lower_facts h
    rw [(moveQ2Lower_facts h2).1] at hu; cases hu

/-- The atom `w` is the inner store of two lowering `u`: of a `Move` (`moveQ2In`) or of a `Zero`
(`zero2In`). -/
def st2In (u w : Value) : Bool := u.op == .Move && moveQ2In u w || u.op == .Zero && zero2In u w

/-- What `st2Lower` says: the outer store of two lowering a `Move` or a `Zero`. -/
theorem st2Lower_cases {u w : Value} (h : st2Lower u w = true) :
    moveQ2Lower u w = true ∨ zero2Lower u w = true := by
  unfold st2Lower at h; simpa using h

/-- `st2In` of a `Move`: `moveQ2In`. -/
theorem st2In_move {u w : Value} (hu : u.op = .Move) : st2In u w = moveQ2In u w := by
  unfold st2In; simp [hu]

/-- `st2In` of a `Zero`: `zero2In`. -/
theorem st2In_zero {u w : Value} (hu : u.op = .Zero) : st2In u w = zero2In u w := by
  unfold st2In; simp [hu]

/-- The inner store of two is a 128-bit store or a store lowering a `Zero`. -/
theorem st2In_store {u w : Value} (h : st2In u w = true) : (qStore w.op || zStore w.op) = true := by
  unfold st2In at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ⟨-, h⟩ | ⟨-, h⟩
  · simp [moveQ2In_qStore h]
  · simp [(zero2In_zStore h).1]

/-- The outer store of two is a 128-bit store or a store lowering a `Zero`. -/
theorem st2Lower_store {u w : Value} (h : st2Lower u w = true) :
    (qStore w.op || zStore w.op) = true := by
  rcases st2Lower_cases h with h | h
  · simp [moveQ2Lower_qStore h]
  · simp [(zero2Lower_zStore h).1]

/-- The outer and inner stores of two lowering a `Move` (`moveQ2Lower`, `moveQ2In`) or a `Zero`
(`zero2Lower`, `zero2In`). -/
theorem st2_of {u w wi : Value}
    (h : (moveQ2Lower u w && moveQ2In u wi || zero2Lower u w && zero2In u wi) = true) :
    st2Lower u w = true ∧ st2In u wi = true := by
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨by simp [st2Lower, h1], by rw [st2In_move (moveQ2Lower_facts h1).1]; exact h2⟩
  · exact ⟨by simp [st2Lower, h1], by rw [st2In_zero (zero2Lower_facts h1).1]; exact h2⟩

/-- The outer store of two has at least three arguments. -/
theorem st2Lower_size {u w : Value} (h : st2Lower u w = true) : 3 ≤ w.args.size := by
  rcases st2Lower_cases h with h | h
  · obtain ⟨-, -, ko, oi, ki, hq, hsz⟩ := moveQ2Lower_facts h
    rcases (moveQ2Op_cases hq).1 with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> omega
  · have := (zero2Lower_facts h).2.2.1; omega

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

/-- A new block control the validator relates: a rule variable, or one built node (`build [n]`)
on rule variables (`ctrlDefL`). -/
def ctrlNodeOK : NewControl → Bool
  | .var _ => true
  | .build [n] => n.args.all (fun a => (a matches .var _))
  | _ => false

/-- **The obligation of a block rule** `(K ctrl) && cond => (K' x…)` on one control of a
conditional kind: the new controls are a rule variable or a node built on rule variables
(`ctrlNodeOK`; none for `First`, one otherwise), and for every instance of `ctrl` whose checks
and condition hold (leaves of their shapes, op nodes' arguments of the checked shapes), with the
block auxint `ai` the rule asks for and the new one `ai'`: if the old block takes an edge, the
new one takes the same (`brVal` of the variable's value or of the built node's, `nodeDenL`;
`First` always its first successor, swapped successors flip it). -/
def BlockRuleL.Sound (br : BlockRule) : Prop :=
  condKind br.kind = true ∧ (br.newKind == .First || condKind br.newKind) = true ∧
  ∃ pat, br.controls = [pat] ∧ Pat.arityOk pat = true ∧ br.aux = .any ∧ br.newAux = none ∧
  (br.newKind = .First → br.newControls = []) ∧
  (br.newKind ≠ .First → ∃ nc pos, br.newControls = [(nc, pos)] ∧ ctrlNodeOK nc = true) ∧
  ∀ sw ∈ GoFV.Opt.RewriteCheck.choices (GoFV.Opt.RewriteCheck.Pat.commutes pat),
    let pat' := (Pat.swapC pat sw).1
    Pat.arityOk pat' = true ∧
    ∀ (tabs : Tables) (e : PEnv) (or : Oracle) (ai ai' : Int64), Oracle.BoolTyped or →
      let σ := sigmaL tabs e pat'
      let ev := evalE (br.vars.map (·.ty)) σ or e (Pat.denL tabs e [] pat')
      Pat.wf e [] pat' → Pat.cons ev σ e [] pat' → condHolds ev br.cond →
      Pat.typed e [] pat' → Pat.argsOK e.ty [] pat' = true → Pat.topOKL (e.ty []) pat' = true →
      argsOKLr br.loc e.ty pat' = true → blockAuxOK br.auxInt ai →
      newAuxL ev br.newAuxInt = some ai' →
      ∀ b, brVal br.kind ai (Pat.denL tabs e [] pat') = some b →
        (match br.newKind, br.newControls with
          | .First, _ => some true
          | k, [(.var x, _)] => brVal k ai' ((σ x).valOr .poison)
          | k, [(.build [n], _)] => brVal k ai' (nodeDenL tabs e pat' ev or σ .other [n] 1 0)
          | _, _ => none) = some (b != br.swapSuccs)

/-- A block rule of a lowering rule set the checked `lower` may fire: a sound rule on a
conditional kind, or a rule on a `JumpTable`, whose events the validator checks by their effect
alone (`GoFV.Opt.LowerCheck.jumpOKL`), so the rule carries no obligation of its own. -/
def BlockRuleL.Checked (br : BlockRule) : Prop :=
  BlockRuleL.Sound br ∨ br.kind = .JumpTable

/-! ## Rule sets -/

/-- The bounds-panic atoms a rule folds a constant operand of (`ARM64.rules:513-516`). -/
def pbAtom : Op → Bool
  | .ARM64LoweredPanicBoundsRR | .ARM64LoweredPanicBoundsRC | .ARM64LoweredPanicBoundsCR => true
  | _ => false

/-- A rule on a memory or frame atom (`(Store {t} ptr val mem)`, `(LocalAddr {sym} base mem)`, an
arm64 store `stSize` knows or an indexed one, `idxStore`, a `Zero`, a `Move` or a 128-bit store
lowering a `Move`, `qStore`) or on a lowered bounds panic (`pbAtom`): the validator accepts its
events only as a lowered store, `Zero` or `Move`, a folded store offset, a scaled store index or a
frame address it pairs with the atom itself (`GoFV.Opt.LowerCheck.atomDef`, `memLower`,
`bulkLower`, `stFold`, `qFold`, `stIdxScale`, `addrLower`, `moveDef`), or as a constant folded
into a bounds panic, which the replay keeps as the renamed atom (`GoFV.Opt.LowerCheck.pbFoldEv`;
`finalOKL` and `atomsOKL` relate the result, `pbLower`), so the rule carries no obligation of its
own. -/
def ArmRule.Mem (r : Rule) : Prop :=
  ∃ o n ty ai ax ar args c, r.pat = .op o n ty ai ax ar args c ∧
    (o = .Store ∨ o = .LocalAddr ∨ ((stSize o).isSome ∨ (idxStore o).isSome) ∨ pbAtom o ∨
      o = .Zero ∨ o = .Move ∨ qStore o ∨ o = .ARM64STP)

/-- A rule whose result is `mulStrengthReduce{,32}(v, x, c)` (`ARM64.rules:1043`, `1044`): the
validator checks its events by their effect alone (`GoFV.Opt.LowerCheck.mulOKL`: the values the
helper built compute the product in the bits `v` keeps), so the rule carries no obligation of its
own. -/
def ArmRule.Mul (r : Rule) : Prop := GoFV.Rules.Interp.mulResult r = true

/-- A narrow left shift renamed to the 64-bit one (`(Lsh32x<a> ...) => (Lsh64x<a> ...)`,
`ARM64.rules:148-150`, `GoFV.Rules.Derive.lshWide`). It is false as an ellipsis rule (`Lsh64x<a>`
asks for a 64-bit operand), so the validator replays its event as no change and checks the rules
`lower` then fires on the renamed value in their form on the narrow shift, which the rule set
lists after the rename (`GoFV.Rules.Derive.lshSplit`, `GoFV.Opt.LowerCheck.lshRule`); the rule
carries no obligation of its own. -/
def ArmRule.Lsh (r : Rule) : Prop :=
  ∃ o o', ellipsisOn o r.pat = true ∧ r.result = .setOp o' ∧ GoFV.Rules.Derive.lshWide o = some o'

/-- A value rule of a lowering rule set the checked `lower` may fire: a sound rule, a sound
ellipsis rule on terms, an atom rename, a rule on a memory or frame atom, a strength-reduced
multiplication, or a narrow left shift's rename. -/
def ArmRule.Checked (r : Rule) : Prop :=
  ArmRule.Sound r ∨ ArmRule.SetOp r ∨ ArmRule.Rename r ∨ ArmRule.Mem r ∨ ArmRule.Mul r ∨
    ArmRule.Lsh r

/-- Every value rule of `s` is `ArmRule.Checked`, every block rule `BlockRuleL.Checked`, and `s`
has no rules in the per-instance tables (`nilChecks` … `phiSels`, Phase 1's generic layers). -/
def ArmRuleSet.AllSound (s : RuleSet) : Prop :=
  ForallL (fun (p : SSA.Op × List Rule) => ForallL ArmRule.Checked p.2) s.values ∧
  ForallL (fun (p : SSA.BlockKind × List BlockRule) => ForallL BlockRuleL.Checked p.2) s.blocks ∧
  s.nilChecks = [] ∧ s.loads = [] ∧ s.structLoads = [] ∧ s.structStores = [] ∧ s.segs = [] ∧
  s.phiSels = []

end GoFV.Proof.Low
