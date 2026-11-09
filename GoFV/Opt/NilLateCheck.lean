import GoFV.SSA.Sem.RunSched
import GoFV.Proof.Cong

variable [GoFV.SSA.Sem.Addrs]

/-!
# `nilLateB`: a validator for `late nilcheck` (`nilcheckelim2`, #408)

`nilLateB tabs f g` accepts when `g` is `f` with some `LoweredNilCheck`s removed (the removed
set `rm`: the values of `f` that `g` lacks), each made redundant under `runSched` by a later
value of its block that faults on the same pointer. Exactly (`GoFV.Proof.NilLateL` proves
`RefinesSched` from it):

* **Shape** (`shapeB`): `g` has `f`'s entry, `ownAux`, `lowered`, and, up to positions and use
  counts (`eraseV`, `eraseB`), `f`'s value table with the removed values absent and `f`'s blocks
  with the removed values dropped from `b.Values`.
* **Unused** (`unusedB`): the removed values are `LoweredNilCheck`s; no remaining value and no
  control reads one.
* **Scheduled** (`blockOKB`): where `f`'s block is a schedule (`schedOrder`), it is its
  non-`Phi`s in order and `g`'s is it without the removed values.
* **Redundant** (`blockB`): in the order of the block's non-`Phi` values, a removed check of `p`
  on memory `mm` (`LoweredNilCheck p mm`) is followed by a value `u` that faults on `p` when
  `p` is nil (`faultsOnB`: an arm64 memory op `arm64Op` runs, not `LoweredMemEq`, with `p` as
  its `faultOnNilArg0` argument at a `SymOff` offset in `[0, minZeroPage)` without a symbol, or
  as its `faultOnNilArg1` argument, and memory `mm`), and every value between is a removed check
  or `safeOpB`: an op that cannot be `stuck` and panics only with `nilDeref` of memory `mm` (a
  non-root generic op but `Arg`/`ArgIntReg`/`PanicBounds`, a pure arm64 op,
  `MOVDaddr`/`MOVDreg`/`MOVDnop`/the closure pointer/caller SP, a load on `mm`),
  not `p` or `mm` themselves. Every argument of these values is defined before them in the
  block (`avail`), or a `Phi` of the block, or outside the block (then, by dominance, already
  computed).

Under `runSched` the check panics (`nilDeref`, memory `m`) exactly when `p` is nil
(`nilFaults`; a wild `p` is `stuck`, `wildNil`), and then `u` faults on `nil + k`
(`k < minZeroPage`) with the same memory; otherwise the check does nothing observable.
-/

namespace GoFV.Opt.NilLate

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof

/-- The arm64 ops `evalOpL` runs with `arm64Op`. -/
def arm64Listed : Op → Bool
  | .ARM64MOVBload | .ARM64MOVBUload | .ARM64MOVHload | .ARM64MOVHUload | .ARM64MOVWload
  | .ARM64MOVWUload | .ARM64MOVDload | .ARM64FMOVSload | .ARM64FMOVDload | .ARM64FMOVQload
  | .ARM64LDP | .ARM64LDPW | .ARM64LDPSW | .ARM64FLDPD | .ARM64FLDPS | .ARM64FLDPQ
  | .ARM64MOVBstore | .ARM64MOVHstore | .ARM64MOVWstore | .ARM64MOVDstore | .ARM64FMOVSstore
  | .ARM64FMOVDstore | .ARM64FMOVQstore | .ARM64STP | .ARM64STPW | .ARM64FSTPD | .ARM64FSTPS
  | .ARM64FSTPQ | .ARM64MOVBstoreidx | .ARM64MOVHstoreidx | .ARM64MOVWstoreidx
  | .ARM64MOVDstoreidx | .ARM64FMOVSstoreidx | .ARM64FMOVDstoreidx | .ARM64MOVHstoreidx2
  | .ARM64MOVWstoreidx4 | .ARM64MOVDstoreidx8 | .ARM64FMOVSstoreidx4 | .ARM64FMOVDstoreidx8
  | .ARM64MOVDaddr | .ARM64MOVDreg | .ARM64MOVDnop | .ARM64LoweredGetClosurePtr
  | .ARM64LoweredGetCallerSP | .ARM64CALLstatic | .ARM64CALLclosure | .ARM64CALLinter
  | .ARM64LoweredNilCheck | .ARM64LoweredPanicBoundsRR | .ARM64LoweredPanicBoundsRC
  | .ARM64LoweredPanicBoundsCR | .ARM64LoweredPanicBoundsCC | .ARM64LoweredMemEq | .ARM64DMB
  | .ARM64PRFM | .ARM64STLRB | .ARM64STLRW | .ARM64STLR | .ARM64LoweredAtomicExchange8
  | .ARM64LoweredAtomicExchange32 | .ARM64LoweredAtomicExchange64
  | .ARM64LoweredAtomicExchange8Variant | .ARM64LoweredAtomicExchange32Variant
  | .ARM64LoweredAtomicExchange64Variant | .ARM64LoweredAtomicAdd32 | .ARM64LoweredAtomicAdd64
  | .ARM64LoweredAtomicAdd32Variant | .ARM64LoweredAtomicAdd64Variant
  | .ARM64LoweredAtomicCas32 | .ARM64LoweredAtomicCas64 | .ARM64LoweredAtomicCas32Variant
  | .ARM64LoweredAtomicCas64Variant | .ARM64LoweredAtomicAnd8 | .ARM64LoweredAtomicAnd32
  | .ARM64LoweredAtomicAnd64 | .ARM64LoweredAtomicOr8 | .ARM64LoweredAtomicOr32
  | .ARM64LoweredAtomicOr64 | .ARM64LoweredAtomicAnd8Variant | .ARM64LoweredAtomicAnd32Variant
  | .ARM64LoweredAtomicAnd64Variant | .ARM64LoweredAtomicOr8Variant
  | .ARM64LoweredAtomicOr32Variant | .ARM64LoweredAtomicOr64Variant | .ARM64LDAR | .ARM64LDARB
  | .ARM64LDARW | .ARM64LoweredZero | .ARM64LoweredZeroLoop | .ARM64LoweredMove
  | .ARM64LoweredMoveLoop => true
  | _ => false

/-- The arm64 loads `arm64Op` runs as `ld`/`ldPair`/`ld16` (`.ok`, or a nil fault). -/
def loadOp : Op → Bool
  | .ARM64MOVBload | .ARM64MOVBUload | .ARM64MOVHload | .ARM64MOVHUload | .ARM64MOVWload
  | .ARM64MOVWUload | .ARM64MOVDload | .ARM64FMOVSload | .ARM64FMOVDload | .ARM64FMOVQload
  | .ARM64LDP | .ARM64LDPW | .ARM64LDPSW | .ARM64FLDPD | .ARM64FLDPS | .ARM64FLDPQ => true
  | _ => false

/-- The other ops `arm64Op` runs that are always `.ok`. -/
def okOp : Op → Bool
  | .ARM64MOVDaddr | .ARM64MOVDreg | .ARM64MOVDnop | .ARM64LoweredGetClosurePtr
  | .ARM64LoweredGetCallerSP => true
  | _ => false

/-- `w` (a value between a removed check of `p` on memory `mm` and its fault) cannot be `stuck`
and panics only with `nilDeref` of memory `mm`: a non-root generic op other than `Arg`,
`ArgIntReg`, `PanicBounds` (Phase 1's `frameVal` or `evalPure`: `InlMark`, `Convert`,
`Select0`/`Select1`, `GetG`, …), a non-root arm64 op `arm64Op` does not run (`Arm64.evalPure`),
an `okOp`, or a load on `mm`. -/
def safeOpB (w : Value) (mm : ID) : Bool :=
  (w.op.generic && !isRoot w.op && w.op != .Arg && w.op != .ArgIntReg &&
      w.op != .PanicBounds) ||
    (!w.op.generic && !arm64Listed w.op && !isRoot w.op) || okOp w.op ||
    (loadOp w.op && w.args.back? == some mm)

/-- `u` faults on a nil `p` (memory `mm`): see the module doc. -/
def faultsOnB (u : Value) (p mm : ID) : Bool :=
  !u.op.generic && arm64Listed u.op && u.op != .ARM64LoweredMemEq && u.args.back? == some mm &&
    ((u.op.faultOnNilArg0 && u.args[0]? == some p &&
        (u.op.auxType != .SymOff ||
          (u.aux.isNone && 0 ≤ u.auxInt.toInt && u.auxInt.toInt < (minZeroPage : Int)))) ||
      (u.op.faultOnNilArg1 && u.args[1]? == some p))

/-- Every argument of `w` is available: in `avail` (defined before it in the block, or a `Phi`
of the block) or not in the block (`blk`). -/
def argsAvailB (blk : Array ID) (avail : List ID) (w : Value) : Bool :=
  w.args.all fun a => avail.contains a || !blk.contains a

/-- The values `rest` after a removed check of `p` on memory `mm` reach a value faulting on `p`
through removed checks and safe values (`avail`: the values available before `rest`). -/
def segB (f : Func) (rm : ID → Bool) (blk : Array ID) (p mm : ID) :
    List ID → List ID → Bool
  | _, [] => false
  | avail, x :: xs =>
    if rm x then segB f rm blk p mm avail xs else
    match f.value? x with
    | none => false
    | some w =>
      argsAvailB blk avail w &&
        (faultsOnB w p mm ||
          (safeOpB w mm && x != p && x != mm && segB f rm blk p mm (x :: avail) xs))

/-- A removed value `x` (with the values `avail` before it and `rest` after it in the block's
order) is a `LoweredNilCheck p mm` made redundant within `rest`. -/
def removedB (f : Func) (rm : ID → Bool) (blk : Array ID) (x : ID) (avail rest : List ID) :
    Bool :=
  match f.value? x with
  | some v =>
    v.op == .ARM64LoweredNilCheck &&
      match v.args.toList with
      | [p, mm] => !rm p && !rm mm && segB f rm blk p mm avail rest
      | _ => false
  | none => false

/-- Every removed value of the order `o` (after `pre`) is redundant. -/
def blockB (f : Func) (rm : ID → Bool) (blk : Array ID) : List ID → List ID → Bool
  | _, [] => true
  | pre, x :: xs => (!rm x || removedB f rm blk x pre xs) && blockB f rm blk (x :: pre) xs

/-- The `Phi`s of a block. -/
def phisOf (f : Func) (b : Block) : List ID :=
  b.values.toList.filter fun x => ((f.value? x).map (·.op == .Phi)).getD false

/-- The non-`Phi`s of a block, in order. -/
def orderOf (f : Func) (b : Block) : List ID :=
  b.values.toList.filter fun x => !((f.value? x).map (·.op == .Phi)).getD false

/-- `f`'s block `b` with the removed values dropped. -/
def dropB (rm : ID → Bool) (b : Block) : Block := { b with values := b.values.filter (!rm ·) }

/-- The shape condition (module doc). -/
def shapeB (f g : Func) (rm : ID → Bool) : Bool :=
  f.entry == g.entry && f.ownAux == g.ownAux && f.lowered == g.lowered &&
    g.valueTab.size == f.valueTab.size && g.blockTab.size == f.blockTab.size &&
    (List.range f.valueTab.size).all (fun i =>
      (g.value? i).map eraseV == if rm i then none else (f.value? i).map eraseV) &&
    (List.range f.blockTab.size).all (fun i =>
      (g.block? i).map eraseB == (f.block? i).map (eraseB ∘ dropB rm))

/-- Every removed value is a `LoweredNilCheck`; no remaining value or control reads one. -/
def unusedB (f : Func) (rm : ID → Bool) : Bool :=
  (List.range f.valueTab.size).all (fun i =>
    if rm i then ((f.value? i).map (·.op == .ARM64LoweredNilCheck)).getD false
    else ((f.value? i).map fun v => v.args.all (!rm ·)).getD true) &&
  (List.range f.blockTab.size).all (fun i =>
    ((f.block? i).map fun b => b.controls.all (!rm ·)).getD true)

/-- Block `bid` (`fb` in `f`): if `f`'s schedule of it exists (`runSched` of `f` is not `stuck`
entering it), it is `orderOf f fb`, `g`'s is it without the removed values, and every removed
value of it is redundant (`blockB`). `cS`, `cT`: the `runSched` contexts of `f` and `g`. -/
def blockOKB (f : Func) (rm : ID → Bool) (cS cT : Ctx) (bid : ID) (fb : Block) : Bool :=
  match (cS.sched[bid]?).join with
  | none => true
  | some o =>
    o.toList == orderOf f fb &&
      (cT.sched[bid]?).join == some ((orderOf f fb).filter (!rm ·)).toArray &&
      blockB f rm fb.values (phisOf f fb) (orderOf f fb)

/-- The removed values: those of `f` that `g` lacks. -/
def removedSet (f g : Func) : Array Bool :=
  (Array.range f.valueTab.size).map fun i => (f.value? i).isSome && (g.value? i).isNone

/-- **The `late nilcheck` validator** (module doc). -/
def nilLateB (tabs : Tables) (f g : Func) : Bool :=
  let rs := removedSet f g
  let rm : ID → Bool := fun i => rs.getD i false
  let cS := Ctx.makeSched tabs f
  let cT := Ctx.makeSched tabs g
  shapeB f g rm && unusedB f rm &&
    f.blocks.all fun bid => match f.block? bid with
      | some fb => blockOKB f rm cS cT bid fb
      | none => true

end GoFV.Opt.NilLate
