import GoFV.SSA.Sem.RunL

variable [GoFV.SSA.Sem.Addrs]

/-!
# Term ops of lowered SSA (issue #385)

Which values of a lowered function the checked `lower` treats as *terms* (functions of their
arguments' values, `GoFV.Proof.Low.denL`) rather than atoms (`GoFV.Proof.Low.AtomSimL`):

* a generic op: Phase 1's `RewriteCheck.termOp`;
* an arm64 op `runL` evaluates without the activation (`Sem.evalOpL`: not `actOp`, not a root)
  whose `Arm64.evalPure` is proven monotone (`armTerm`, `GoFV.Proof.Low.armPure_mono`);
* `MOVDaddr` unless it is a frame variable's address at offset 0 (`auxIsName`, the `LocalAddr`
  it lowers, an atom): its value is its base moved by its offset, or a global symbol's or frame
  variable's address at its offset (`Sem.symAddr`; a frame variable's address is the
  activation's, and `runL` runs a function in activation 0, `Sem.Ctx.makeL`);
* an integer load `MOV{B,BU,H,HU,W,WU,D}load`: the memory argument read at its address
  (`GoFV.Proof.Low.ldVal`, activation 0 likewise), as Phase 1's `Load` is a term;
* an activation op `Sem.arm64Op` runs in non-faulting mode as `Arm64.evalPure` (`pureActOp`):
  the acquiring loads `LDAR`/`LDARB`/`LDARW`, Phase 1's `atomicLoad` (the `AtomicLoad*` they
  lower are terms), and `LoweredMemEq`, Phase 1's `memEq` (the `MemEq` it lowers is a term).

Every other arm64 op is an atom; the checked `lower` only accepts atoms of the output that
correspond to atoms of the input (`GoFV.Opt.LowerCheck.atomPair`).
-/

namespace GoFV.Opt.LowerTerm

open GoFV.SSA

/-- The activation ops (`actOp`) whose `Sem.arm64Op` in non-faulting mode is `Arm64.evalPure`:
the acquiring loads (`atomicLoad`) and `LoweredMemEq` (`memEq`), so they are terms of lowered
SSA. -/
def pureActOp : Op → Bool
  | .ARM64LDAR | .ARM64LDARB | .ARM64LDARW | .ARM64LoweredMemEq => true
  | _ => false

/-- The arm64 ops `Sem.evalOpL` evaluates with the activation (`Sem.arm64Op`). -/
def actOp : Op → Bool
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

/-- The pure arm64 ops whose `Arm64.evalPure` is proven monotone in the arguments
(`GoFV.Proof.Low.armPure_mono`): the term ops of lowered SSA besides the generic ones. -/
def armTerm : Op → Bool
  | .ARM64ADD | .ARM64ADDconst | .ARM64SUB | .ARM64SUBconst | .ARM64MUL | .ARM64MULW
  | .ARM64MNEG | .ARM64MNEGW | .ARM64MULH | .ARM64UMULH | .ARM64MULL | .ARM64UMULL
  | .ARM64DIV | .ARM64UDIV | .ARM64DIVW | .ARM64UDIVW | .ARM64MOD | .ARM64UMOD | .ARM64MODW
  | .ARM64UMODW | .ARM64MADD | .ARM64MADDW | .ARM64MSUB | .ARM64MSUBW | .ARM64NEG | .ARM64MVN
  | .ARM64AND | .ARM64ANDconst | .ARM64OR | .ARM64ORconst | .ARM64XOR | .ARM64XORconst
  | .ARM64BIC | .ARM64EON | .ARM64ORN
  | .ARM64SLL | .ARM64SRL | .ARM64SRA | .ARM64ROR | .ARM64RORW | .ARM64SLLconst
  | .ARM64SRLconst | .ARM64SRAconst | .ARM64RORconst | .ARM64RORWconst | .ARM64EXTRconst
  | .ARM64EXTRWconst
  | .ARM64MVNshiftLL | .ARM64MVNshiftRL | .ARM64MVNshiftRA | .ARM64MVNshiftRO
  | .ARM64NEGshiftLL | .ARM64NEGshiftRL | .ARM64NEGshiftRA
  | .ARM64ADDshiftLL | .ARM64ADDshiftRL | .ARM64ADDshiftRA | .ARM64SUBshiftLL
  | .ARM64SUBshiftRL | .ARM64SUBshiftRA | .ARM64ANDshiftLL | .ARM64ANDshiftRL
  | .ARM64ANDshiftRA | .ARM64ANDshiftRO | .ARM64ORshiftLL | .ARM64ORshiftRL | .ARM64ORshiftRA
  | .ARM64ORshiftRO | .ARM64XORshiftLL | .ARM64XORshiftRL | .ARM64XORshiftRA
  | .ARM64XORshiftRO | .ARM64BICshiftLL | .ARM64BICshiftRL | .ARM64BICshiftRA
  | .ARM64BICshiftRO | .ARM64EONshiftLL | .ARM64EONshiftRL | .ARM64EONshiftRA
  | .ARM64EONshiftRO | .ARM64ORNshiftLL | .ARM64ORNshiftRL | .ARM64ORNshiftRA
  | .ARM64ORNshiftRO
  | .ARM64UBFX | .ARM64SBFX | .ARM64UBFIZ | .ARM64SBFIZ | .ARM64BFI | .ARM64BFXIL
  | .ARM64CLZ | .ARM64CLZW | .ARM64RBIT | .ARM64RBITW | .ARM64REV | .ARM64REVW | .ARM64REV16
  | .ARM64REV16W
  | .ARM64MOVBreg | .ARM64MOVBUreg | .ARM64MOVHreg | .ARM64MOVHUreg | .ARM64MOVWreg
  | .ARM64MOVWUreg | .ARM64MOVDconst | .ARM64ZERO
  | .ARM64MOVDloadidx | .ARM64MOVWloadidx | .ARM64MOVWUloadidx | .ARM64MOVHloadidx
  | .ARM64MOVHUloadidx | .ARM64MOVBloadidx | .ARM64MOVBUloadidx | .ARM64FMOVSloadidx
  | .ARM64FMOVDloadidx | .ARM64MOVHloadidx2 | .ARM64MOVHUloadidx2 | .ARM64MOVWloadidx4
  | .ARM64MOVWUloadidx4 | .ARM64MOVDloadidx8 | .ARM64FMOVSloadidx4 | .ARM64FMOVDloadidx8
  | .ARM64CMP | .ARM64CMPconst | .ARM64CMPW | .ARM64CMPWconst | .ARM64CMN | .ARM64CMNconst
  | .ARM64CMNW | .ARM64CMNWconst | .ARM64TST | .ARM64TSTconst | .ARM64TSTW | .ARM64TSTWconst
  | .ARM64CMPshiftLL | .ARM64CMPshiftRL | .ARM64CMPshiftRA | .ARM64CMNshiftLL
  | .ARM64CMNshiftRL | .ARM64CMNshiftRA | .ARM64TSTshiftLL | .ARM64TSTshiftRL
  | .ARM64TSTshiftRA | .ARM64TSTshiftRO | .ARM64FlagConstant | .ARM64InvertFlags
  | .ARM64CSEL | .ARM64CSEL0 | .ARM64CSINC | .ARM64CSINV | .ARM64CSNEG | .ARM64CSETM
  | .ARM64Equal | .ARM64NotEqual | .ARM64LessThan | .ARM64LessEqual | .ARM64GreaterThan
  | .ARM64GreaterEqual | .ARM64LessThanU | .ARM64LessEqualU | .ARM64GreaterThanU
  | .ARM64GreaterEqualU | .ARM64LessThanF | .ARM64LessEqualF | .ARM64GreaterThanF
  | .ARM64GreaterEqualF | .ARM64NotLessThanF | .ARM64NotLessEqualF | .ARM64NotGreaterThanF
  | .ARM64NotGreaterEqualF | .ARM64LessThanNoov | .ARM64GreaterEqualNoov
  | .ARM64FADDS | .ARM64FADDD | .ARM64FSUBS | .ARM64FSUBD | .ARM64FMULS | .ARM64FMULD
  | .ARM64FNMULS | .ARM64FNMULD | .ARM64FDIVS | .ARM64FDIVD | .ARM64FABSS | .ARM64FABSD
  | .ARM64FNEGS | .ARM64FNEGD | .ARM64FSQRTS | .ARM64FSQRTD | .ARM64FMINS | .ARM64FMIND
  | .ARM64FMAXS | .ARM64FMAXD | .ARM64FMADDS | .ARM64FMADDD | .ARM64FMSUBS | .ARM64FMSUBD
  | .ARM64FNMADDS | .ARM64FNMADDD | .ARM64FNMSUBS | .ARM64FNMSUBD
  | .ARM64FRINTAD | .ARM64FRINTMD | .ARM64FRINTND | .ARM64FRINTPD | .ARM64FRINTZD
  | .ARM64LoweredRound32F | .ARM64LoweredRound64F
  | .ARM64FCMPS | .ARM64FCMPD | .ARM64FCMPS0 | .ARM64FCMPD0 | .ARM64FCVTSD | .ARM64FCVTDS
  | .ARM64SCVTFWS | .ARM64SCVTFWD | .ARM64UCVTFWS | .ARM64UCVTFWD | .ARM64SCVTFS
  | .ARM64SCVTFD | .ARM64UCVTFS | .ARM64UCVTFD | .ARM64FCVTZSSW | .ARM64FCVTZSDW
  | .ARM64FCVTZUSW | .ARM64FCVTZUDW | .ARM64FCVTZSS | .ARM64FCVTZSD | .ARM64FCVTZUS
  | .ARM64FCVTZUD | .ARM64FMOVSconst | .ARM64FMOVDconst | .ARM64FMOVDgpfp | .ARM64FMOVDfpgp
  | .ARM64FMOVSgpfp | .ARM64FMOVSfpgp
  -- the write barrier's buffer allocation (`wbOp`, Phase 1's `WB`, a term there too)
  | .ARM64LoweredWB => true
  | _ => false

/-- The aux names a frame variable (`Sem.symAddr` then needs the activation). -/
def auxIsName (tabs : Tables) (ax : Option AuxRef) : Bool :=
  match ax.bind tabs.aux? with
  | some { kind := .name .., .. } => true
  | _ => false

end GoFV.Opt.LowerTerm
