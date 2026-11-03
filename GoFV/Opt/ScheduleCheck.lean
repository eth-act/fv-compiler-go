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
  `f`'s with a nil check replaced by its pointer (`rep`, one step: the pointer is no nil check or
  `SPanchored` and has the check's lowered shape); entry, `OwnAux`, value and block tables'
  sizes and `Func.lowered` are kept.
* **Order** (`orderOK`): `runSched`'s order of `g`'s block (`schedOrder`) exists, and the values
  that may fail keep `runL`'s order (`kahn`, `Sem.schedule`) of `f`'s block: if the target runs
  `y` before `x` and the source runs `x` before `y`, one of them never fails (`Cls.safe`), or `y`
  is a load and `x` a load or nil check on the same memory, so that whichever fails first fails
  with `nilDeref` of that memory (`swapOK`). This is the ready-root rule (#96) for runs where
  memory ops fault (`LMode.faulting`).
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
`LoweredMove` (and their loops) and `LoweredMemEq`. -/
def faultOps : List Op :=
  ldOps ++ [.ARM64LoweredZero, .ARM64LoweredZeroLoop, .ARM64LoweredMove, .ARM64LoweredMoveLoop,
    .ARM64LoweredMemEq]

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

/-- The source runs `x` before `y`, the target `y` before `x` (both may fail). Allowed if `x`
never panics (so the source cannot stop at `x` with `y` not run); or `x` and `y` fault alike:
`y` is a `faultOp` and `x` a `faultOp` or a nil check on the same memory (whichever stops first
panics with `nilDeref` of it); or `y` is a nil check of the base of `x`, a load or nil check on
the same memory, of a word shape (`tys`: `f`'s `runL` shapes; if `x` faults, `y`'s pointer is a
pointer word, so `y` is not stuck). -/
def swapOK (tabs : Tables) (tys : Array Ty) (f : Func) (x y : ID) : Bool :=
  match f.value? x, f.value? y with
  | some vx, some vy =>
    !mayPanic tabs vx ||
      ((cls tabs vx == .load || cls tabs vx == .nil) && vx.args.back? == vy.args.back? &&
        !(vx.args.back?.any (isSPA f)) &&
        (cls tabs vy == .load ||
          cls tabs vy == .nil && (ldOp vx.op || cls tabs vx == .nil) && vx.args[0]? == vy.args[0]? &&
            (vy.args[0]?.all fun p => !isSPA f p && wordShape (tys[p]?.getD .other))))
  | _, _ => false

/-- `posFill l i a`: `a` with each element of `l` set to its position (from `i`). -/
def posFill : List ID → Nat → Array Nat → Array Nat
  | [], _, a => a
  | x :: xs, i, a => posFill xs (i + 1) (a.set! x i)

/-- The values of the block that may fail keep their source order up to `swapOK`: for failing
values `y` before `x` in the target order `oT`, if the source order `oS` runs `x` before `y`
then `swapOK tabs tys f x y`. `n`: the size of the value table. -/
def orderOK (tabs : Tables) (tys : Array Ty) (f : Func) (n : Nat) (oS oT : Array ID) : Bool :=
  let pS := posFill oS.toList 0 (Array.replicate n 0)
  decide ((oT.toList.filter (mayFail tabs f)).Pairwise
    fun y x => (!(pS[x]! < pS[y]!) || swapOK tabs tys f x y) = true)

/-- The arguments of value `x` of `f` (none if `x` is not in `f`). -/
def argsOf (f : Func) (x : ID) : List ID := ((f.value? x).map (·.args.toList)).getD []

/-- No value of `l` takes an argument listed at or after it (a dependency order). -/
def topoB (f : Func) : List ID → Bool
  | [] => true
  | x :: s => (argsOf f x).all (fun a => !(x :: s).contains a) && topoB f s

/-- `x` is a `Phi` of `f`. -/
def isPhi (f : Func) (x : ID) : Bool := ((f.value? x).map (·.op == .Phi)).getD false

/-- `schedule`'s bypass of an argument or control `a`, one step: the first argument of an
`SPanchored` or a nil check. -/
def rep (f : Func) (a : ID) : ID :=
  match f.value? a with
  | some v => if v.op == .SPanchored || v.op.nilCheck then (v.args[0]?).getD a else a
  | none => a

/-- A use `a` of `f`, argument `k` of the value `user` (`none`: a control). If `schedule`
bypasses it, its first argument `rep f a` exists and is no `SPanchored` or nil check; an
`SPanchored` is only the base (`k = 0`) of a `symAddrOp` at a symbol or frame variable, a nil
check's pointer has the check's type or both have word shapes (`tys`: `f`'s `runL` shapes). -/
def useOK (tabs : Tables) (tys : Array Ty) (f : Func) (user : Option Value) (k : Nat) (a : ID) :
    Bool :=
  if isSPA f a then
    k == 0 && (user.map fun u => symAddrOp u.op && symbolic tabs u).getD false &&
      let p := rep f a
      p != a && (f.value? p).isSome && !isNC f p && !isSPA f p
  else if isNC f a then
    let p := rep f a
    p != a && !isNC f p && !isSPA f p && ((f.value? p).map (·.type)).isSome &&
      ((f.value? p).map (·.type) == (f.value? a).map (·.type) ||
        wordShape (tys[a]?.getD .other) && wordShape (tys[p]?.getD .other))
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
          orderOK tabs cS.tys f f.valueTab.size oS oT
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
