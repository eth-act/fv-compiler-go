import GoFV.SSA.Sem.RunSched
import GoFV.Opt.SpecSafe

/-!
# The `schedule` validator (`scheduleCheck`, #385, #407)

`schedule` (`GoFV.Opt.schedule`, `schedule.go:107-373`) permutes each block's values into an
execution order, then bypasses `SPanchored` and nil-check results in every argument and control,
frees the `SPanchored` values and gives the nil checks `types.TypeVoid`. `scheduleCheck tabs f g`
accepts `g` as such a scheduling of `f` (decision (b) of #384, `docs/plans/semantics2.md` §6):

* **Shape** (`valueOK`, `blockOK`, `usesOK`): `g` has `f`'s blocks with the same kind, `auxInt`,
  successors and predecessors; each block lists a permutation of `f`'s values minus the
  `SPanchored`s, which `g` drops and nothing in `f` uses; every value keeps its op, aux, auxint,
  block and type (a nil check may change its type), and its arguments and the block controls are
  `f`'s with a chain of nil checks replaced by the pointer at its end (`rep`, which iterates
  `rep1` as `schedule.go:331-344` loops: each check's pointer is a value, no `SPanchored`, of the
  check's lowered shape, `ncChain`) and an `SPanchored` by its first argument; entry, `OwnAux`,
  value and block tables' sizes and `Func.lowered` are kept.
* **Order** (`orderOK`): `runSched`'s order of `g`'s block (`schedOrder`) exists, and the values
  that may fail keep `runL`'s order (`kahn`, `Sem.schedule`) of `f`'s block: if the target runs
  `y` before `x` and the source runs `x` before `y`, `y` is a parameter's register piece (it
  evaluates, `argOK`), or `x` never fails (`Cls.safe`) or never faults (a load or nil check whose
  pointer is a nil check's result, `SP`, `GetG` or the closure pointer, `nnBase`), or `y` is a
  load (a `faultOp`, including `LDAR*`) and `x` a load or nil check on the same memory, so that
  whichever fails first fails with `nilDeref` of that memory, or `y` is a nil check on that
  memory of `x`'s base or of a pointer-shaped parameter's register piece the source runs before
  `x` or outside the block (`argPtr`: on the inputs where those read nil or a pointer that is not
  wild, `GoFV.Proof.ArgPtrsOK`, it panics alike or passes) (`swapOKB`), or of another
  pointer-shaped value the source runs before `x` or outside the block (`nilPtrSwap`, on the
  inputs where checked pointers are nil or not wild, `GoFV.Proof.NilPtrsOK`) (`swapOK`). This is
  the ready-root rule (#96) for runs where memory ops fault (`LMode.faulting`).
-/

namespace GoFV.Opt.ScheduleCheck

open GoFV.SSA GoFV.SSA.Sem

/-- The arm64 ops `evalOpL` evaluates with `arm64Op` (its list). -/
def actOps : List Op :=
  [.ARM64MOVBload, .ARM64MOVBUload, .ARM64MOVHload, .ARM64MOVHUload, .ARM64MOVWload,
   .ARM64MOVWUload, .ARM64MOVDload, .ARM64FMOVSload, .ARM64FMOVDload, .ARM64FMOVQload,
   .ARM64LDP, .ARM64LDPW, .ARM64LDPSW, .ARM64FLDPD, .ARM64FLDPS, .ARM64FLDPQ,
   .ARM64MOVBstore, .ARM64MOVHstore, .ARM64MOVWstore, .ARM64MOVDstore, .ARM64FMOVSstore,
   .ARM64FMOVDstore, .ARM64FMOVQstore, .ARM64STP, .ARM64STPW, .ARM64FSTPD, .ARM64FSTPS,
   .ARM64FSTPQ, .ARM64MOVBstoreidx, .ARM64MOVHstoreidx, .ARM64MOVWstoreidx,
   .ARM64MOVDstoreidx, .ARM64FMOVSstoreidx, .ARM64FMOVDstoreidx, .ARM64MOVHstoreidx2,
   .ARM64MOVWstoreidx4, .ARM64MOVDstoreidx8, .ARM64FMOVSstoreidx4, .ARM64FMOVDstoreidx8,
   .ARM64MOVDaddr, .ARM64MOVDreg, .ARM64MOVDnop, .ARM64LoweredGetClosurePtr,
   .ARM64LoweredGetCallerSP, .ARM64CALLstatic, .ARM64CALLclosure, .ARM64CALLinter,
   .ARM64LoweredNilCheck, .ARM64LoweredPanicBoundsRR, .ARM64LoweredPanicBoundsRC,
   .ARM64LoweredPanicBoundsCR, .ARM64LoweredPanicBoundsCC, .ARM64LoweredMemEq, .ARM64DMB,
   .ARM64PRFM, .ARM64STLRB, .ARM64STLRW, .ARM64STLR, .ARM64LoweredAtomicExchange8,
   .ARM64LoweredAtomicExchange32, .ARM64LoweredAtomicExchange64,
   .ARM64LoweredAtomicExchange8Variant, .ARM64LoweredAtomicExchange32Variant,
   .ARM64LoweredAtomicExchange64Variant, .ARM64LoweredAtomicAdd32, .ARM64LoweredAtomicAdd64,
   .ARM64LoweredAtomicAdd32Variant, .ARM64LoweredAtomicAdd64Variant,
   .ARM64LoweredAtomicCas32, .ARM64LoweredAtomicCas64, .ARM64LoweredAtomicCas32Variant,
   .ARM64LoweredAtomicCas64Variant, .ARM64LoweredAtomicAnd8, .ARM64LoweredAtomicAnd32,
   .ARM64LoweredAtomicAnd64, .ARM64LoweredAtomicOr8, .ARM64LoweredAtomicOr32,
   .ARM64LoweredAtomicOr64, .ARM64LoweredAtomicAnd8Variant, .ARM64LoweredAtomicAnd32Variant,
   .ARM64LoweredAtomicAnd64Variant, .ARM64LoweredAtomicOr8Variant,
   .ARM64LoweredAtomicOr32Variant, .ARM64LoweredAtomicOr64Variant, .ARM64LDAR, .ARM64LDARB,
   .ARM64LDARW, .ARM64LoweredZero, .ARM64LoweredZeroLoop, .ARM64LoweredMove,
   .ARM64LoweredMoveLoop]

/-- `op` is evaluated by `arm64Op`. -/
def actOp (op : Op) : Bool := decide (op ∈ actOps)

/-- The arm64 loads (`arm64Op`'s `ld`, `ldPair`, `ld16`). -/
def ldOps : List Op :=
  [.ARM64MOVBload, .ARM64MOVBUload, .ARM64MOVHload, .ARM64MOVHUload, .ARM64MOVWload,
   .ARM64MOVWUload, .ARM64MOVDload, .ARM64FMOVSload, .ARM64FMOVDload, .ARM64FMOVQload,
   .ARM64LDP, .ARM64LDPW, .ARM64LDPSW, .ARM64FLDPD, .ARM64FLDPS, .ARM64FLDPQ]

/-- `op` is an arm64 load. -/
def ldOp (op : Op) : Bool := decide (op ∈ ldOps)

/-- The arm64 ops that evaluate (`.ok`) unless they fault (`nilFaults`): the loads, `LoweredZero`,
`LoweredMove` (and their loops), `LoweredMemEq` and the acquiring loads `LDAR*`. -/
def faultOps : List Op :=
  ldOps ++ [.ARM64LoweredZero, .ARM64LoweredZeroLoop, .ARM64LoweredMove, .ARM64LoweredMoveLoop,
    .ARM64LoweredMemEq, .ARM64LDAR, .ARM64LDARB, .ARM64LDARW]

/-- `op` is in `faultOps`. -/
def faultOp (op : Op) : Bool := decide (op ∈ faultOps)

/-- The arm64 stores `arm64Op` writes at `symAddr` (`st`, `stPair`). -/
def stOps : List Op :=
  [.ARM64MOVBstore, .ARM64MOVHstore, .ARM64MOVWstore, .ARM64MOVDstore, .ARM64FMOVSstore,
   .ARM64FMOVDstore, .ARM64FMOVQstore, .ARM64STP, .ARM64STPW, .ARM64FSTPD, .ARM64FSTPS,
   .ARM64FSTPQ]

/-- The ops of `arm64Op` that read their first argument only as the base of `symAddr` (also in
`nilFaults`): the loads, the stores and `MOVDaddr`. -/
def symAddrOps : List Op := ldOps ++ stOps ++ [.ARM64MOVDaddr]

/-- `op` is in `symAddrOps`. -/
def symAddrOp (op : Op) : Bool := decide (op ∈ symAddrOps)

/-- The aux of `v` is a symbol or a frame variable: `symAddr` ignores the base. -/
def symbolic (tabs : Tables) (v : Value) : Bool :=
  match v.aux.bind tabs.aux? with
  | some { kind := .sym .., .. } | some { kind := .name .., .. } => true
  | _ => false

/-- The ops of `arm64Op` that always evaluate (no memory access). -/
def actSafeOps : List Op :=
  [.ARM64MOVDaddr, .ARM64MOVDreg, .ARM64MOVDnop, .ARM64LoweredGetClosurePtr,
   .ARM64LoweredGetCallerSP]

/-- `op` is in `actSafeOps`. -/
def actSafeOp (op : Op) : Bool := decide (op ∈ actSafeOps)

/-- How a value may fail under `runSched`'s evaluation (memory ops fault). -/
inductive Cls where
  /-- Evaluates whenever its arguments have registers. -/
  | safe
  /-- A `faultOp`: evaluates or panics with `nilDeref` of its last argument's memory. -/
  | load
  /-- A nil check: evaluates, is stuck, or panics with `nilDeref` of its memory argument. -/
  | nil
  /-- Anything else. -/
  | other
  deriving DecidableEq, Repr, Inhabited

/-- The class of value `v` (from its op, aux and number of arguments; `tabs`: the aux table). -/
def cls (tabs : Tables) (v : Value) : Cls :=
  if v.op.generic then (if specSafeOp v.op then .safe else .other)
  else if v.op == .ARM64LoweredNilCheck && v.args.size == 2 then .nil
  else if ldOp v.op && symbolic tabs v then .safe
  else if faultOp v.op then .load
  else if actSafeOp v.op then .safe
  else if !actOp v.op && !isRoot v.op then .safe
  else .other

/-- Value `x` is in `f` and may fail. -/
def mayFail (tabs : Tables) (f : Func) (x : ID) : Bool :=
  ((f.value? x).map (cls tabs · != .safe)).getD true

/-- Value `v` may panic: a generic op only if it is a call or a nil check (`evalOp_panic_op`),
an arm64 op unless it is `Cls.safe`. -/
def mayPanic (tabs : Tables) (v : Value) : Bool :=
  if v.op.generic then v.op.call || v.op.nilCheck else cls tabs v != .safe

/-- A pointer-word shape: `.int .w64` or `.ptr _`. -/
def wordShape : Ty → Bool
  | .int .w64 | .ptr _ => true
  | _ => false

/-- The value `a` is an `SPanchored`. -/
def isSPA (f : Func) (a : ID) : Bool := ((f.value? a).map (·.op == .SPanchored)).getD false

/-- The value `a` is a nil check. -/
def isNC (f : Func) (a : ID) : Bool := ((f.value? a).map (·.op.nilCheck)).getD false

/-- Value `a`, once evaluated, holds no nil base: a nil check (it passed), an `SP` (the
outgoing-arguments area) or `GetG` (the current goroutine) at a word shape (`tys`: `f`'s `runL`
shapes), or the closure pointer (`poison`: a run of the function itself has no closure
context). -/
def isNN (tys : Array Ty) (f : Func) (a : ID) : Bool :=
  match f.value? a with
  | some v => v.op.nilCheck || v.op == .ARM64LoweredGetClosurePtr ||
      (v.op == .SP || v.op == .GetG) && wordShape (tys[a]?.getD .other)
  | none => false

/-- A load or nil check whose pointer is `isNN`: its base is not nil, so it does not fault
(`late nilcheck` later removes a check of a nil check's result). -/
def nnBase (tabs : Tables) (tys : Array Ty) (f : Func) (v : Value) : Bool :=
  (ldOp v.op || cls tabs v == .nil) && (v.args[0]?.any (isNN tys f))

/-- A register argument piece (`ArgIntReg`) of a parameter of the function (`params`: its
input parameters' names, `Ctx.params`): it reads the parameter's image, which every frame of the
activation has, so it evaluates. -/
def argOK (tabs : Tables) (params : Array (Option AuxRef)) (v : Value) : Bool :=
  v.op == .ArgIntReg && v.args.isEmpty &&
    match v.aux.bind tabs.aux? with
    | some { kind := .nameOff n _, .. } => params.contains (some n)
    | _ => false

/-- A pointer shape (`.ptr _`). -/
def ptrShape : Ty → Bool
  | .ptr _ => true
  | _ => false

/-- Value `p` of `f` is a parameter's register piece (`argOK`) at a pointer shape (`tys`: `f`'s
`runL` shapes): on the inputs where such a piece reads nil or a pointer that is not wild
(`GoFV.Proof.ArgPtrsOK`, a Go-level assumption), a nil check of it panics with `nilDeref` or
passes. -/
def argPtr (tabs : Tables) (params : Array (Option AuxRef)) (tys : Array Ty) (f : Func) (p : ID) :
    Bool :=
  match f.value? p with
  | some vp => argOK tabs params vp && ptrShape (tys[p]?.getD .other)
  | none => false

/-- `swapOK` without its `NilPtrsOK` case (`nilPtrSwap`). The source runs `x` before `y`, the
target `y` before `x` (both may fail). Allowed if `y` evaluates (a parameter's register piece,
`argOK`; `params`: `f`'s input parameters' names); or if `x` never panics (so the source cannot
stop at `x` with `y` not run: a value that never panics, or a load or nil check whose base is not
nil, `nnBase`; `tys`: `f`'s `runL` shapes); or `x` and `y` fault alike: `x` is a `faultOp` or a
nil check, and `y` on the same memory is a `faultOp` (whichever stops first panics with
`nilDeref` of it), a nil check of the base of `x` when `x` is a load or nil check (if `x` faults,
its base is nil, so `y` panics as well), or a nil check of a pointer-shaped parameter's register
piece (`argPtr`) that the source runs before `x` or that is outside the block (`pS`: the source
positions from 1, 0 for a value not in the block), which panics with `nilDeref` of that memory
or passes. -/
def swapOKB (tabs : Tables) (params : Array (Option AuxRef)) (tys : Array Ty) (f : Func)
    (pS : Array Nat) (x y : ID) : Bool :=
  match f.value? x, f.value? y with
  | some vx, some vy =>
    argOK tabs params vy || !mayPanic tabs vx || nnBase tabs tys f vx ||
      ((cls tabs vx == .load || cls tabs vx == .nil) && vx.args.back? == vy.args.back? &&
        !(vx.args.back?.any (isSPA f)) &&
        (cls tabs vy == .load ||
          cls tabs vy == .nil && (ldOp vx.op || cls tabs vx == .nil) && vx.args[0]? == vy.args[0]? &&
            (vy.args[0]?.all fun p => !isSPA f p) ||
          cls tabs vy == .nil &&
            (vy.args[0]?.any fun p => argPtr tabs params tys f p && pS[p]! < pS[x]!)))
  | _, _ => false

/-- `swapOK`'s `NilPtrsOK` case: `x` is a `faultOp` or a nil check and `y` a nil check on the same
memory of a pointer-shaped value `q` (`tys`), no nil check or `SPanchored`, that the source runs
before `x` or that is outside the block (`pS`). On the inputs where every pointer-shaped value a
nil check checks reads nil or a pointer that is not wild once evaluated (`GoFV.Proof.NilPtrsOK`,
a Go-level assumption), `y` panics with `nilDeref` of that memory, as `x` would, or passes. -/
def nilPtrSwap (tabs : Tables) (tys : Array Ty) (f : Func) (pS : Array Nat) (x y : ID) : Bool :=
  match f.value? x, f.value? y with
  | some vx, some vy =>
    (cls tabs vx == .load || cls tabs vx == .nil) && vx.args.back? == vy.args.back? &&
      !(vx.args.back?.any (isSPA f)) && cls tabs vy == .nil &&
      (vy.args[0]?.any fun q => ptrShape (tys[q]?.getD .other) && !isNC f q && !isSPA f q &&
        pS[q]! < pS[x]!)
  | _, _ => false

/-- The source runs `x` before `y`, the target `y` before `x` (both may fail): allowed by
`swapOKB` or by its `NilPtrsOK` case `nilPtrSwap`. -/
def swapOK (tabs : Tables) (params : Array (Option AuxRef)) (tys : Array Ty) (f : Func)
    (pS : Array Nat) (x y : ID) : Bool :=
  swapOKB tabs params tys f pS x y || nilPtrSwap tabs tys f pS x y

/-- `posFill l i a`: `a` with each element of `l` set to its position (from `i`). -/
def posFill : List ID → Nat → Array Nat → Array Nat
  | [], _, a => a
  | x :: xs, i, a => posFill xs (i + 1) (a.set! x i)

/-- The source positions of the order `oS` (from 1; 0 for a value not in `oS`). `n`: the size of
the value table. -/
def srcPos (n : Nat) (oS : List ID) : Array Nat := posFill oS 1 (Array.replicate n 0)

/-- The values of the block that may fail keep their source order up to `swapOK`: for failing
values `y` before `x` in the target order `oT`, if the source order `oS` runs `x` before `y`
then `swapOK tabs params tys f (srcPos n oS) x y`. `n`: the size of the value table. -/
def orderOK (tabs : Tables) (params : Array (Option AuxRef)) (tys : Array Ty) (f : Func) (n : Nat)
    (oS oT : Array ID) : Bool :=
  let pS := srcPos n oS.toList
  decide ((oT.toList.filter (mayFail tabs f)).Pairwise
    fun y x => (!(pS[x]! < pS[y]!) || swapOK tabs params tys f pS x y) = true)

/-- The arguments of value `x` of `f` (none if `x` is not in `f`). -/
def argsOf (f : Func) (x : ID) : List ID := ((f.value? x).map (·.args.toList)).getD []

/-- No value of `l` takes an argument listed at or after it (a dependency order). -/
def topoB (f : Func) : List ID → Bool
  | [] => true
  | x :: s => (argsOf f x).all (fun a => !(x :: s).contains a) && topoB f s

/-- `x` is a `Phi` of `f`. -/
def isPhi (f : Func) (x : ID) : Bool := ((f.value? x).map (·.op == .Phi)).getD false

/-- One step of `schedule`'s bypass of an argument or control `a`: the first argument of an
`SPanchored` or a nil check. -/
def rep1 (f : Func) (a : ID) : ID :=
  match f.value? a with
  | some v => if v.op == .SPanchored || v.op.nilCheck then (v.args[0]?).getD a else a
  | none => a

/-- `rep1` repeated until it stops changing `a`, at most `k` times. -/
def repK (f : Func) : Nat → ID → ID
  | 0, a => a
  | k + 1, a => if rep1 f a == a then a else repK f k (rep1 f a)

/-- `schedule`'s bypass of an argument or control `a` (`schedule.go:331-344`): `rep1` while `a`
is an `SPanchored` or a nil check (at most the size of the value table times). -/
def rep (f : Func) (a : ID) : ID := repK f f.valueTab.size a

/-- A nil check `a` and its pointer `rep1 f a`: they differ, the pointer is a value and no
`SPanchored`, and it has the check's type or both have word shapes (`tys`: `f`'s `runL`
shapes). -/
def ncStep (tys : Array Ty) (f : Func) (a : ID) : Bool :=
  let p := rep1 f a
  p != a && !isSPA f p && ((f.value? p).map (·.type)).isSome &&
    ((f.value? p).map (·.type) == (f.value? a).map (·.type) ||
      wordShape (tys[a]?.getD .other) && wordShape (tys[p]?.getD .other))

/-- A chain of nil checks from `a`, each the pointer of the one before (`ncStep`), ends within
`k` steps at a value that is no nil check. -/
def ncChain (tys : Array Ty) (f : Func) : Nat → ID → Bool
  | 0, _ => false
  | k + 1, a => ncStep tys f a && (!isNC f (rep1 f a) || ncChain tys f k (rep1 f a))

/-- A use `a` of `f`, argument `k` of the value `user` (`none`: a control). If `schedule`
bypasses it: an `SPanchored` is only the base (`k = 0`) of a `symAddrOp` at a symbol or frame
variable, and its first argument exists and is no `SPanchored` or nil check; a nil check starts
a chain of nil checks (`ncChain`, `tys`: `f`'s `runL` shapes). -/
def useOK (tabs : Tables) (tys : Array Ty) (f : Func) (user : Option Value) (k : Nat) (a : ID) :
    Bool :=
  if isSPA f a then
    k == 0 && (user.map fun u => symAddrOp u.op && symbolic tabs u).getD false &&
      let p := rep1 f a
      p != a && (f.value? p).isSome && !isNC f p && !isSPA f p
  else if isNC f a then ncChain tys f f.valueTab.size a
  else true

/-- Every use in `f` is `useOK`. -/
def usesOK (tabs : Tables) (f : Func) : Bool :=
  let tys := (Ctx.makeL tabs f).tys
  f.valueTab.all (fun
    | some u => (List.range u.args.size).all fun k => useOK tabs tys f (some u) k u.args[k]!
    | none => true) &&
    f.blockTab.all (fun | some b => b.controls.all (useOK tabs tys f none 0) | none => true)

/-- Value `id` of `g` is `f`'s, rewired by `rep` (an `SPanchored` is dropped). -/
def valueOK (f g : Func) (id : ID) : Bool :=
  match f.value? id, g.value? id with
  | none, none => true
  | some fv, none => fv.op == .SPanchored
  | some fv, some gv =>
    fv.op != .SPanchored && gv.id == fv.id && gv.op == fv.op && gv.aux == fv.aux &&
      gv.auxInt == fv.auxInt && gv.block == fv.block && gv.args == fv.args.map (rep f) &&
      (fv.op.nilCheck || gv.type == fv.type) &&
      ((gv.args[0]?.bind g.value?).map (Arm64.signExtendsIn g.value?)) ==
        ((fv.args[0]?.bind f.value?).map (Arm64.signExtendsIn f.value?))
  | none, some _ => false

/-- Block `b` of `g` is `f`'s with its values permuted (minus the `SPanchored`s) and its controls
rewired by `rep`. -/
def blockOK (f g : Func) (b : ID) : Bool :=
  match f.block? b, g.block? b with
  | none, none => true
  | some fb, some gb =>
    gb.id == fb.id && gb.kind == fb.kind && gb.auxInt == fb.auxInt && gb.succs == fb.succs &&
      gb.preds == fb.preds && gb.controls == fb.controls.map (rep f) &&
      gb.values.toList.isPerm (fb.values.toList.filter (!isSPA f ·))
  | _, _ => false

/-- Every block of `f` has `runL`'s order `oS` (`Ctx.makeL`) and `g`'s block `runSched`'s
order `oT` (`Ctx.makeSched`), with `orderOK`. -/
def ordersOK (tabs : Tables) (f g : Func) : Bool :=
  let cS := Ctx.makeL tabs f
  let sT := (Ctx.makeSched tabs g).sched
  (List.range f.blockTab.size).all fun b =>
    match f.block? b with
    | none => true
    | some _ =>
      match cS.sched[b]?.join, sT[b]?.join, g.block? b with
      | some oS, some oT, some gb =>
        oT.toList == gb.values.toList.filter (!isPhi g ·) && topoB g oT.toList &&
          orderOK tabs cS.params cS.tys f f.valueTab.size oS oT
      | _, _, _ => false

/-- The shape conditions of `scheduleCheck` (see the module doc). -/
def shapeOK (tabs : Tables) (f g : Func) : Bool :=
  g.entry == f.entry && g.ownAux == f.ownAux && g.lowered == f.lowered &&
    g.valueTab.size == f.valueTab.size && g.blockTab.size == f.blockTab.size &&
    (List.range f.valueTab.size).all (valueOK f g) &&
    (List.range f.blockTab.size).all (blockOK f g) && usesOK tabs f

end ScheduleCheck

open GoFV.SSA ScheduleCheck in
/-- **The `schedule` validator**: `g` is a scheduling of `f` (module doc). -/
def scheduleCheck (tabs : Tables) (f g : Func) : Bool :=
  shapeOK tabs f g && ordersOK tabs f g

end GoFV.Opt
