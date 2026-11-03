import GoFV.Opt.LoweredCSE
import GoFV.SSA.Sem.RunL

/-!
# The lowered cse checker (`CSEL.crel`)

`lowered cse` runs `generic cse`'s port unchanged (`loweredCsePass`). `CSEL.crel` checks its
result against the substitution `cseRw` returns, as `CSE.crel tabs true` does for `generic cse`,
with conditions the `runL` proof (`GoFV.Proof.CSEL.loweredCse_refinesL`) can use on lowered code:

* a replaced value and its representative have the same op, aux, auxint and type, and the same
  (substituted) arguments in the result (`congr`; no `Load`/`LocalAddr`/`NilCheck` special case:
  lowered memory arguments compare by identity);
* the op's value is a function of the op, aux, auxint, argument registers and the producer of
  the first argument (`substOp`): a generic non-root op, a non-root arm64 op `Arm64.evalPure`
  evaluates, an arm64 load, `MOVDaddr`, `MOVDreg`, `MOVDnop`, `LoweredMemEq`, or
  `LoweredNilCheck` (its pointer, if it does not panic);
* arguments are redirected (and the first two of a commutative op possibly swapped) as
  `CSE.valueOK` checks: every commutative arm64 op evaluates symmetrically on them;
* blocks keep their `auxInt` (an arm64 terminator reads it).

`CSEL.frag env f`: the checker accepts `cse`'s result on `f` (the hypothesis of
`loweredCse_refinesL`); `lake exe csel-probe` measures it on the corpus.
-/

namespace GoFV.Opt.CSEL

open GoFV.SSA GoFV.Opt.CSE

/-- The arm64 ops `Sem.evalOpL` evaluates with the activation (`Sem.arm64Op`). -/
def arm64Act : Op → Bool
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

/-- The ops of `arm64Act` whose value is a function of the op, aux, auxint, argument registers
and the first argument's producer: the `SymOff` loads, `MOVDaddr`, `MOVDreg`, `MOVDnop`. -/
def actOK : Op → Bool
  | .ARM64MOVBload | .ARM64MOVBUload | .ARM64MOVHload | .ARM64MOVHUload | .ARM64MOVWload
  | .ARM64MOVWUload | .ARM64MOVDload | .ARM64FMOVSload | .ARM64FMOVDload | .ARM64FMOVQload
  | .ARM64LDP | .ARM64LDPW | .ARM64LDPSW | .ARM64FLDPD | .ARM64FLDPS | .ARM64FLDPQ
  | .ARM64MOVDaddr | .ARM64MOVDreg | .ARM64MOVDnop => true
  | _ => false

/-- The ops whose substitution the proof covers: `LoweredNilCheck` (its value is its pointer
argument, if it does not panic), `LoweredMemEq` (a function of its arguments), and the ops that
are not roots and are generic, evaluated by `Arm64.evalPure`, or in `actOK`. -/
def substOp (op : Op) : Bool :=
  op == .ARM64LoweredNilCheck || op == .ARM64LoweredMemEq ||
    !Sem.isRoot op && (op.generic || !arm64Act op || actOK op)

/-- Whether `v`'s first argument sign-extends (what `MOVDreg`/`MOVDnop` read of the function,
`GoFV.Proof.sxOf`). -/
def sx (f : Func) (v : Value) : Option Bool :=
  (v.args[0]?.bind f.value?).map (Sem.Arm64.signExtendsIn f.value?)

/-- Value `x` reads in `g` what it reads in `f` of its first argument's producer (unless its op
is commutative: such an op reads only its argument registers). -/
def sxOK (f g : Func) (x : ID) : Bool :=
  match f.value? x, g.value? x with
  | some fv, some gv => fv.op.commutative || sx g gv == sx f fv
  | _, _ => true

/-- Block `bid` keeps its `auxInt`. -/
def auxOK (f g : Func) (bid : ID) : Bool :=
  match f.block? bid, g.block? bid with
  | some fb, some gb => gb.auxInt == fb.auxInt
  | _, _ => false

/-- The shape of type `t` in `runL`'s context (`GoFV.Proof.shapesL`). -/
def shape (tabs : Tables) (low : Bool) (t : TypeRef) : Sem.Ty :=
  (if low then Sem.typeShapesL tabs else Sem.typeShapes tabs)[t]?.getD .other

/-- The replaced value `x` and its representative `r` are congruent: the same op, aux and auxint,
the same type or types of the same shape in `runL`, and the same arguments in `g`. -/
def congr (tabs : Tables) (low : Bool) (fx fr gx gr : Value) : Bool :=
  fr.op == fx.op && fr.aux == fx.aux && fr.auxInt == fx.auxInt &&
    (fr.type == fx.type || tyEq (shape tabs low fr.type) (shape tabs low fx.type)) &&
    gx.args == gr.args

/-- The substitution of `x`, if any, is sound: as `CSE.substOK`, with `congr` and `substOp`. -/
def substOK (tabs : Tables) (c : DomCert.Cert) (rw : Array (Option ID)) (f g : Func) (x : ID) : Bool :=
  match rw.getD x none with
  | none => true
  | some r =>
    (rw.getD r none).isNone &&
    match f.value? x, f.value? r, g.value? x, g.value? r with
    | some fx, some fr, some gx, some gr =>
      congr tabs f.lowered fx fr gx gr && substOp fx.op &&
        (fx.op != .Phi || fr.block == fx.block) && c.anc fr.block fx.block &&
        f.blocks.contains fr.block && ((f.block? fr.block).map (·.values.contains r)).getD false
    | _, _, _, _ => false

/-- **lowered cse's output relation**, checked against the substitution `rw`. -/
def crel (tabs : Tables) (f g : Func) (rw : Array (Option ID)) : Bool :=
  DomCert.cfgView g == DomCert.cfgView f && g.ownAux == f.ownAux &&
  g.valueTab.size == f.valueTab.size && g.lowered == f.lowered &&
  f.blocks.all (blockOK rw f g) && f.blocks.all (auxOK f g) &&
  (List.range f.valueTab.size).all (valueOK rw f g) &&
  (List.range f.valueTab.size).all (sxOK f g) &&
  (List.range rw.size).all (substOK tabs (DomCert.make f) rw f g) &&
  f.blocks.all (schedOK true f g)

/-- The fragment of `loweredCse_refinesL`: the checker accepts cse's result on `f` (or cse
fails). -/
def frag (env : PassEnv) (f : Func) : Bool :=
  match cseCtx env with
  | .ok c =>
    match cseRw c f with
    | .ok (g, rw) => crel c.tabs f g rw
    | .error _ => true
  | .error _ => true

end GoFV.Opt.CSEL
