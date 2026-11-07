import GoFV.SSA.Sem.Arm64.Int
import GoFV.SSA.Sem.Arm64.Float
import GoFV.SSA.Sem.Arm64.Mem

/-!
# `Arm64.evalPure`: the pure arm64 ops of lowered SSA (`docs/plans/semantics2.md` §3–§4)

The arm64 ops `runL` evaluates without the activation (no symbol, frame or closure): the
arithmetic, logic, shift, bitfield, multiply/divide, compare, conditional, float and conversion
ops, the register-indexed loads (`MOV*loadidx*`, no symbol), `LDAR*` (Phase 1's `AtomicLoad*`),
`LoweredMemEq` (Phase 1's `MemEq`; `Sem.arm64Op` runs it so, after its nil check),
`LoweredZero`/`LoweredMove` and their loop forms, `LoweredWB` (Phase 1's `WB`), `FlagConstant`,
`InvertFlags` (`invertFlags`, the flags of the swapped compare; Go fails if one reaches codegen);
`poison` for every other op. The ops that need the activation (loads and stores with a symbol,
`MOVDaddr`, `MOVDreg`, calls, nil checks, panics, atomics, barriers) are `Sem.arm64Op`
(`Sem/RunL.lean`). Phase 1's `evalPure` is unchanged: lowered ops reach this module only through
`runL`.

One arm per op, calling its family (`Sem/Arm64/*`). Never `simp [Arm64.evalPure]` on an op
variable.
-/

namespace GoFV.SSA.Sem.Arm64

/-- The register value of operand `b` shifted by `k` (`ShiftReg`). -/
def shifted (sh : Shift) (k : Int64) (b : BitVec 64) : BitVec 64 := sh.apply b (amt k)

/-- A shifted-register ALU op `f a (b SHIFT k)`. -/
@[inline] def opSh (ty : Ty) (sh : Shift) (k : Int64) (f : BitVec 64 → BitVec 64 → BitVec 64) :
    List Val → Val :=
  op2 ty fun x y => f x (shifted sh k y)

/-- `ADD a (b SHIFT k)` with the provenance case of a pointer `a`. -/
def addSh (ty : Ty) (sh : Shift) (k : Int64) : List Val → Val
  | [a, b] => match reg b with
    | some y => addP ty a (shifted sh k y)
    | none => .poison
  | _ => .poison

/-- `SUB a (b SHIFT k)` with the provenance case of a pointer `a`. -/
def subSh (ty : Ty) (sh : Shift) (k : Int64) : List Val → Val
  | [a, b] => match reg b with
    | some y => addP ty a (-(shifted sh k y))
    | none => .poison
  | _ => .poison

/-- `ADDconst [k] a` / `SUBconst [k] a`. -/
def addK (ty : Ty) (k : BitVec 64) : List Val → Val
  | [a] => addP ty a k
  | _ => .poison

/-- An indexed load at `p + i·scale` of `n` bytes (unscaled: either argument may be the
pointer, as `ADD` is commutative, `(MOVDload (ADD ptr idx))`). -/
def loadIdx (ty : Ty) (n scale : Nat) (signed : Bool) : List Val → Val
  | [a, i, .mem m] =>
    let s := if scale = 1 then add .other [a, i] else
      match reg i with
      | some k => add .other [a, .int .w64 (k * BitVec.ofNat 64 scale)]
      | none => .poison
    match addr s 0 with
    | some p => loadN ty n signed m p
    | none => .poison
  | _ => .poison
/-- The pure arm64 op `op` (see the module comment); `poison` for any other op. -/
def evalPure (op : Op) (ty : Ty) (k : Int64) (_aux : Option AuxRef) (args : List Val) : Val :=
  match op with
  -- arithmetic
  | .ARM64ADD => add ty args
  | .ARM64ADDconst => addK ty (imm k) args
  | .ARM64SUB => sub ty args
  | .ARM64SUBconst => addK ty (-imm k) args
  | .ARM64MUL => op2 ty (· * ·) args
  | .ARM64MULW => op2w ty (· * ·) args
  | .ARM64MNEG => op2 ty (fun x y => -(x * y)) args
  | .ARM64MNEGW => op2w ty (fun x y => -(x * y)) args
  | .ARM64MULH => op2 ty smulh args
  | .ARM64UMULH => op2 ty umulh args
  | .ARM64MULL => op2 ty smull args
  | .ARM64UMULL => op2 ty umull args
  | .ARM64DIV => op2 ty sdiv args
  | .ARM64UDIV => op2 ty udiv args
  | .ARM64DIVW => op2w ty sdiv args
  | .ARM64UDIVW => op2w ty udiv args
  | .ARM64MOD => op2 ty srem args
  | .ARM64UMOD => op2 ty urem args
  | .ARM64MODW => op2w ty srem args
  | .ARM64UMODW => op2w ty urem args
  | .ARM64MADD => madd ty false args
  | .ARM64MADDW => op3w ty (fun a x y => a + x * y) args
  | .ARM64MSUB => madd ty true args
  | .ARM64MSUBW => op3w ty (fun a x y => a - x * y) args
  | .ARM64NEG => op1 ty (- ·) args
  | .ARM64MVN => op1 ty (~~~ ·) args
  -- logic
  | .ARM64AND => op2 ty (· &&& ·) args
  | .ARM64ANDconst => op1 ty (· &&& imm k) args
  | .ARM64OR => op2 ty (· ||| ·) args
  | .ARM64ORconst => op1 ty (· ||| imm k) args
  | .ARM64XOR => op2 ty (· ^^^ ·) args
  | .ARM64XORconst => op1 ty (· ^^^ imm k) args
  | .ARM64BIC => op2 ty (fun x y => x &&& ~~~y) args
  | .ARM64EON => op2 ty (fun x y => x ^^^ ~~~y) args
  | .ARM64ORN => op2 ty (fun x y => x ||| ~~~y) args
  -- shifts and rotates (register amount modulo the width)
  | .ARM64SLL => op2 ty (fun x y => x <<< (y.toNat % 64)) args
  | .ARM64SRL => op2 ty (fun x y => x >>> (y.toNat % 64)) args
  | .ARM64SRA => op2 ty (fun x y => x.sshiftRight (y.toNat % 64)) args
  | .ARM64ROR => op2 ty (fun x y => x.rotateRight (y.toNat % 64)) args
  | .ARM64RORW => op2w ty (fun x y => x.rotateRight (y.toNat % 32)) args
  | .ARM64SLLconst => op1 ty (Shift.ll.apply · (amt k)) args
  | .ARM64SRLconst => op1 ty (Shift.rl.apply · (amt k)) args
  | .ARM64SRAconst => op1 ty (Shift.ra.apply · (amt k)) args
  | .ARM64RORconst => op1 ty (Shift.ro.apply · (amt k)) args
  | .ARM64RORWconst => op1w ty (Shift.ro.apply · (amt k)) args
  | .ARM64EXTRconst => op2 ty (extr (amt k)) args
  | .ARM64EXTRWconst => op2w ty (extr (amt k)) args
  -- shifted-register forms
  | .ARM64MVNshiftLL => op1 ty (fun x => ~~~(shifted .ll k x)) args
  | .ARM64MVNshiftRL => op1 ty (fun x => ~~~(shifted .rl k x)) args
  | .ARM64MVNshiftRA => op1 ty (fun x => ~~~(shifted .ra k x)) args
  | .ARM64MVNshiftRO => op1 ty (fun x => ~~~(shifted .ro k x)) args
  | .ARM64NEGshiftLL => op1 ty (fun x => -(shifted .ll k x)) args
  | .ARM64NEGshiftRL => op1 ty (fun x => -(shifted .rl k x)) args
  | .ARM64NEGshiftRA => op1 ty (fun x => -(shifted .ra k x)) args
  | .ARM64ADDshiftLL => addSh ty .ll k args
  | .ARM64ADDshiftRL => addSh ty .rl k args
  | .ARM64ADDshiftRA => addSh ty .ra k args
  | .ARM64SUBshiftLL => subSh ty .ll k args
  | .ARM64SUBshiftRL => subSh ty .rl k args
  | .ARM64SUBshiftRA => subSh ty .ra k args
  | .ARM64ANDshiftLL => opSh ty .ll k (· &&& ·) args
  | .ARM64ANDshiftRL => opSh ty .rl k (· &&& ·) args
  | .ARM64ANDshiftRA => opSh ty .ra k (· &&& ·) args
  | .ARM64ANDshiftRO => opSh ty .ro k (· &&& ·) args
  | .ARM64ORshiftLL => opSh ty .ll k (· ||| ·) args
  | .ARM64ORshiftRL => opSh ty .rl k (· ||| ·) args
  | .ARM64ORshiftRA => opSh ty .ra k (· ||| ·) args
  | .ARM64ORshiftRO => opSh ty .ro k (· ||| ·) args
  | .ARM64XORshiftLL => opSh ty .ll k (· ^^^ ·) args
  | .ARM64XORshiftRL => opSh ty .rl k (· ^^^ ·) args
  | .ARM64XORshiftRA => opSh ty .ra k (· ^^^ ·) args
  | .ARM64XORshiftRO => opSh ty .ro k (· ^^^ ·) args
  | .ARM64BICshiftLL => opSh ty .ll k (fun x y => x &&& ~~~y) args
  | .ARM64BICshiftRL => opSh ty .rl k (fun x y => x &&& ~~~y) args
  | .ARM64BICshiftRA => opSh ty .ra k (fun x y => x &&& ~~~y) args
  | .ARM64BICshiftRO => opSh ty .ro k (fun x y => x &&& ~~~y) args
  | .ARM64EONshiftLL => opSh ty .ll k (fun x y => x ^^^ ~~~y) args
  | .ARM64EONshiftRL => opSh ty .rl k (fun x y => x ^^^ ~~~y) args
  | .ARM64EONshiftRA => opSh ty .ra k (fun x y => x ^^^ ~~~y) args
  | .ARM64EONshiftRO => opSh ty .ro k (fun x y => x ^^^ ~~~y) args
  | .ARM64ORNshiftLL => opSh ty .ll k (fun x y => x ||| ~~~y) args
  | .ARM64ORNshiftRL => opSh ty .rl k (fun x y => x ||| ~~~y) args
  | .ARM64ORNshiftRA => opSh ty .ra k (fun x y => x ||| ~~~y) args
  | .ARM64ORNshiftRO => opSh ty .ro k (fun x y => x ||| ~~~y) args
  -- bitfields, bit operations, extensions
  | .ARM64UBFX => op1 ty (ubfx k) args
  | .ARM64SBFX => op1 ty (sbfx k) args
  | .ARM64UBFIZ => op1 ty (ubfiz k) args
  | .ARM64SBFIZ => op1 ty (sbfiz k) args
  | .ARM64BFI => op2 ty (bfi k) args
  | .ARM64BFXIL => op2 ty (bfxil k) args
  | .ARM64CLZ => op1 ty clz args
  | .ARM64CLZW => op1w ty clz args
  | .ARM64RBIT => op1 ty rbit args
  | .ARM64RBITW => op1w ty rbit args
  | .ARM64REV => op1 ty rev args
  | .ARM64REVW => op1w ty rev args
  | .ARM64REV16 => op1 ty rev16 args
  | .ARM64REV16W => op1w ty rev16 args
  | .ARM64VCNT => op1 ty vcnt args
  | .ARM64VUADDLV => op1 ty vuaddlv args
  | .ARM64MOVBreg => op1 ty (ext true 8) args
  | .ARM64MOVBUreg => op1 ty (ext false 8) args
  | .ARM64MOVHreg => op1 ty (ext true 16) args
  | .ARM64MOVHUreg => op1 ty (ext false 16) args
  | .ARM64MOVWreg => op1 ty (ext true 32) args
  | .ARM64MOVWUreg => op1 ty (ext false 32) args
  | .ARM64MOVDconst => res ty (imm k)
  | .ARM64ZERO => res ty 0
  -- compares
  | .ARM64CMP => match args with
    | [a, b] => cmp a b
    | _ => .poison
  | .ARM64CMPconst => match args with
    | [a] => cmp a (.int .w64 (imm k))
    | _ => .poison
  | .ARM64CMPW => cmp2w (fun x y => subFlags x y) args
  | .ARM64CMPWconst => cmp1w (fun x => subFlags x (imm32 k)) args
  | .ARM64CMN => cmpP (fun x y => addWithCarry x y false) args
  | .ARM64CMNconst => cmp1P (fun x => addWithCarry x (imm k) false) args
  | .ARM64CMNW => cmp2w (fun x y => addWithCarry x y false) args
  | .ARM64CMNWconst => cmp1w (fun x => addWithCarry x (imm32 k) false) args
  | .ARM64TST => flags2 (fun x y => logicFlags (x &&& y)) args
  | .ARM64TSTconst => flags1 (fun x => logicFlags (x &&& imm k)) args
  | .ARM64TSTW => flags2w (fun x y => logicFlags (x &&& y)) args
  | .ARM64TSTWconst => flags1w (fun x => logicFlags (x &&& imm32 k)) args
  | .ARM64CMPshiftLL => cmpSh (fun x y => subFlags x (shifted .ll k y)) args
  | .ARM64CMPshiftRL => cmpSh (fun x y => subFlags x (shifted .rl k y)) args
  | .ARM64CMPshiftRA => cmpSh (fun x y => subFlags x (shifted .ra k y)) args
  | .ARM64CMNshiftLL => cmpSh (fun x y => addWithCarry x (shifted .ll k y) false) args
  | .ARM64CMNshiftRL => cmpSh (fun x y => addWithCarry x (shifted .rl k y) false) args
  | .ARM64CMNshiftRA => cmpSh (fun x y => addWithCarry x (shifted .ra k y) false) args
  | .ARM64TSTshiftLL => flags2 (fun x y => logicFlags (x &&& shifted .ll k y)) args
  | .ARM64TSTshiftRL => flags2 (fun x y => logicFlags (x &&& shifted .rl k y)) args
  | .ARM64TSTshiftRA => flags2 (fun x y => logicFlags (x &&& shifted .ra k y)) args
  | .ARM64TSTshiftRO => flags2 (fun x y => logicFlags (x &&& shifted .ro k y)) args
  | .ARM64FlagConstant => (Flags.ofFlagConstant k.toInt.toNat).toVal
  | .ARM64InvertFlags => match args with
    | [f] => invertFlags f
    | _ => .poison
  -- flag-setting arithmetic
  | .ARM64ADDSflags => adds ty args
  | .ARM64ADDSconstflags => addsConst ty k args
  | .ARM64SUBSflags => subs ty args
  | .ARM64ADCSflags => adcs ty args
  | .ARM64SBCSflags => sbcs ty args
  | .ARM64NEGSflags => negs ty args
  | .ARM64ADCzerocarry => adcZero ty args
  | .ARM64NGCzerocarry => ngcZero ty args
  -- conditional ops
  | .ARM64CSEL => csel ty k none args
  | .ARM64CSEL0 => csel0 ty k args
  | .ARM64CSINC => csinc ty k args
  | .ARM64CSINV => csel ty k (some (~~~ ·)) args
  | .ARM64CSNEG => csel ty k (some (- ·)) args
  | .ARM64CSETM => csetm ty k args
  | .ARM64CCMP => ccmp false false false k args
  | .ARM64CCMN => ccmp true false false k args
  | .ARM64CCMPconst => ccmp false false true k args
  | .ARM64CCMNconst => ccmp true false true k args
  | .ARM64CCMPW => ccmp false true false k args
  | .ARM64CCMNW => ccmp true true false k args
  | .ARM64CCMPWconst => ccmp false true true k args
  | .ARM64CCMNWconst => ccmp true true true k args
  | .ARM64Equal | .ARM64NotEqual | .ARM64LessThan | .ARM64LessEqual | .ARM64GreaterThan
  | .ARM64GreaterEqual | .ARM64LessThanU | .ARM64LessEqualU | .ARM64GreaterThanU
  | .ARM64GreaterEqualU | .ARM64LessThanF | .ARM64LessEqualF | .ARM64GreaterThanF
  | .ARM64GreaterEqualF | .ARM64NotLessThanF | .ARM64NotLessEqualF | .ARM64NotGreaterThanF
  | .ARM64NotGreaterEqualF | .ARM64LessThanNoov | .ARM64GreaterEqualNoov => cset ty op args
  -- floating point
  | .ARM64FADDS => fop .w32 FOps.add args
  | .ARM64FADDD => fop .w64 FOps.add args
  | .ARM64FSUBS => fop .w32 FOps.sub args
  | .ARM64FSUBD => fop .w64 FOps.sub args
  | .ARM64FMULS => fop .w32 FOps.mul args
  | .ARM64FMULD => fop .w64 FOps.mul args
  | .ARM64FNMULS => fnmul .w32 args
  | .ARM64FNMULD => fnmul .w64 args
  | .ARM64FDIVS => fop .w32 FOps.div args
  | .ARM64FDIVD => fop .w64 FOps.div args
  | .ARM64FABSS => fop .w32 FOps.abs args
  | .ARM64FABSD => fop .w64 FOps.abs args
  | .ARM64FNEGS => fop .w32 FOps.neg args
  | .ARM64FNEGD => fop .w64 FOps.neg args
  | .ARM64FSQRTS => fop .w32 FOps.sqrt args
  | .ARM64FSQRTD => fop .w64 FOps.sqrt args
  | .ARM64FMINS => fop .w32 FOps.min args
  | .ARM64FMIND => fop .w64 FOps.min args
  | .ARM64FMAXS => fop .w32 FOps.max args
  | .ARM64FMAXD => fop .w64 FOps.max args
  | .ARM64FMADDS => fmadd .w32 false false args
  | .ARM64FMADDD => fmadd .w64 false false args
  | .ARM64FMSUBS => fmadd .w32 false true args
  | .ARM64FMSUBD => fmadd .w64 false true args
  | .ARM64FNMADDS => fmadd .w32 true true args
  | .ARM64FNMADDD => fmadd .w64 true true args
  | .ARM64FNMSUBS => fmadd .w32 true false args
  | .ARM64FNMSUBD => fmadd .w64 true false args
  | .ARM64FRINTAS => fop .w32 (FOps.roundInt .rna) args
  | .ARM64FRINTAD => fop .w64 (FOps.roundInt .rna) args
  | .ARM64FRINTMS => fop .w32 (FOps.roundInt .rmi) args
  | .ARM64FRINTMD => fop .w64 (FOps.roundInt .rmi) args
  | .ARM64FRINTNS => fop .w32 (FOps.roundInt .rne) args
  | .ARM64FRINTND => fop .w64 (FOps.roundInt .rne) args
  | .ARM64FRINTPS => fop .w32 (FOps.roundInt .rpi) args
  | .ARM64FRINTPD => fop .w64 (FOps.roundInt .rpi) args
  | .ARM64FRINTZS => fop .w32 (FOps.roundInt .rz) args
  | .ARM64FRINTZD => fop .w64 (FOps.roundInt .rz) args
  | .ARM64LoweredRound32F => fop .w32 FOps.round args
  | .ARM64LoweredRound64F => fop .w64 FOps.round args
  | .ARM64FCMPS => fcmp .w32 false args
  | .ARM64FCMPD => fcmp .w64 false args
  | .ARM64FCMPS0 => fcmp .w32 true args
  | .ARM64FCMPD0 => fcmp .w64 true args
  | .ARM64FCVTSD => FOps.f32to64 (args.map (fval .w32))
  | .ARM64FCVTDS => FOps.f64to32 (args.map (fval .w64))
  | .ARM64SCVTFWS => cvtf false .w32 .w32 args
  | .ARM64SCVTFWD => cvtf false .w32 .w64 args
  | .ARM64UCVTFWS => cvtf true .w32 .w32 args
  | .ARM64UCVTFWD => cvtf true .w32 .w64 args
  | .ARM64SCVTFS => cvtf false .w64 .w32 args
  | .ARM64SCVTFD => cvtf false .w64 .w64 args
  | .ARM64UCVTFS => cvtf true .w64 .w32 args
  | .ARM64UCVTFD => cvtf true .w64 .w64 args
  | .ARM64FCVTZSSW => fcvtz ty false .w32 .w32 args
  | .ARM64FCVTZSDW => fcvtz ty false .w64 .w32 args
  | .ARM64FCVTZUSW => fcvtz ty true .w32 .w32 args
  | .ARM64FCVTZUDW => fcvtz ty true .w64 .w32 args
  | .ARM64FCVTZSS => fcvtz ty false .w32 .w64 args
  | .ARM64FCVTZSD => fcvtz ty false .w64 .w64 args
  | .ARM64FCVTZUS => fcvtz ty true .w32 .w64 args
  | .ARM64FCVTZUD => fcvtz ty true .w64 .w64 args
  | .ARM64FMOVSconst => FOps.const32 k
  | .ARM64FMOVDconst => FOps.const64 k
  | .ARM64FMOVDgpfp | .ARM64FMOVDfpgp => fmov .w64 ty args
  | .ARM64FMOVSgpfp | .ARM64FMOVSfpgp => fmov .w32 ty args
  -- register-indexed loads
  | .ARM64MOVDloadidx => loadIdx ty 8 1 false args
  | .ARM64MOVWloadidx => loadIdx ty 4 1 true args
  | .ARM64MOVWUloadidx => loadIdx ty 4 1 false args
  | .ARM64MOVHloadidx => loadIdx ty 2 1 true args
  | .ARM64MOVHUloadidx => loadIdx ty 2 1 false args
  | .ARM64MOVBloadidx => loadIdx ty 1 1 true args
  | .ARM64MOVBUloadidx => loadIdx ty 1 1 false args
  | .ARM64FMOVSloadidx => loadIdx ty 4 1 false args
  | .ARM64FMOVDloadidx => loadIdx ty 8 1 false args
  | .ARM64MOVHloadidx2 => loadIdx ty 2 2 true args
  | .ARM64MOVHUloadidx2 => loadIdx ty 2 2 false args
  | .ARM64MOVWloadidx4 => loadIdx ty 4 4 true args
  | .ARM64MOVWUloadidx4 => loadIdx ty 4 4 false args
  | .ARM64MOVDloadidx8 => loadIdx ty 8 8 false args
  | .ARM64FMOVSloadidx4 => loadIdx ty 4 4 false args
  | .ARM64FMOVDloadidx8 => loadIdx ty 8 8 false args
  -- memory pseudo-ops without a symbol
  | .ARM64LDAR | .ARM64LDARB | .ARM64LDARW => atomicLoad ty args
  | .ARM64LoweredMemEq => memEq args
  | .ARM64LoweredZero | .ARM64LoweredZeroLoop => zero k args
  | .ARM64LoweredMove | .ARM64LoweredMoveLoop => move k args
  | .ARM64LoweredWB => wbOp k args
  | _ => .poison

end GoFV.SSA.Sem.Arm64

namespace GoFV.SSA.Sem.Arm64

/-- Whether a register is zero (`CBZ`); a pointer is zero when it is nil (Phase 1's `IsNonNil`):
a pointer's register (`ptrReg`) is 0 exactly when it is nil, and a pointer without a register is
never nil. -/
def isZero : Val → Option Bool
  | .ptr p => some p.isNil
  | v => (reg v).map (· == 0)

/-- Whether the conditional arm64 block of kind `kind` (auxint `k`, control value `c`) takes its
first successor (`docs/plans/semantics2.md` §5, `ssaGenBlock`'s `blockJump`): the flags kinds by
`ConditionHolds` (`FLT` `MI`, `FLE` `LS`, `FGT` `GT`, `FGE` `GE`, `LTnoov` `MI`, `GEnoov` `PL`;
`LEnoov`/`GTnoov`, which `ssaGenBlock` does not emit, as `N ∨ Z` and `¬N ∧ ¬Z`), `Z`/`NZ` on
the register (`isZero`), `ZW`/`NZW` on its low word (`CBZ`/`CBNZ`), `TBZ`/`TBNZ` on bit `k`.
`none`: the control is not defined (or not a conditional arm64 kind). -/
def taken (kind : BlockKind) (k : Int64) (c : Val) : Option Bool :=
  let fl (cc : Cond) := cc.onVal c
  match kind with
  | .ARM64EQ => fl .eq
  | .ARM64NE => fl .ne
  | .ARM64LT => fl .lt
  | .ARM64LE => fl .le
  | .ARM64GT => fl .gt
  | .ARM64GE => fl .ge
  | .ARM64ULT => fl .lo
  | .ARM64ULE => fl .ls
  | .ARM64UGT => fl .hi
  | .ARM64UGE => fl .hs
  | .ARM64FLT => fl .mi
  | .ARM64FLE => fl .ls
  | .ARM64FGT => fl .gt
  | .ARM64FGE => fl .ge
  | .ARM64LTnoov => fl .mi
  | .ARM64GEnoov => fl .pl
  | .ARM64LEnoov => match c with
    | .agg [n, z, _, _, _] => do let n ← n.flagBit; let z ← z.flagBit; pure (n || z)
    | _ => none
  | .ARM64GTnoov => match c with
    | .agg [n, z, _, _, _] => do let n ← n.flagBit; let z ← z.flagBit; pure (!n && !z)
    | _ => none
  | .ARM64Z => isZero c
  | .ARM64NZ => (isZero c).map (!·)
  | .ARM64ZW => (reg32 c).map (· == 0)
  | .ARM64NZW => (reg32 c).map (· != 0)
  | .ARM64TBZ => (reg c).map fun x => !x.getLsbD k.toInt.toNat
  | .ARM64TBNZ => (reg c).map fun x => x.getLsbD k.toInt.toNat
  | _ => none

/-- A block kind never reads a flags value's fifth component `g` (`Cond.onVal_ghost`). -/
theorem taken_ghost (kind : BlockKind) (k : Int64) (n z cf v g g' : Val) :
    taken kind k (.agg [n, z, cf, v, g]) = taken kind k (.agg [n, z, cf, v, g']) := by
  cases kind <;> rfl

/-- `ADCS`/`SBCS` read only `C`, never `g`. -/
theorem carry_ghost (n z cf v g g' : Val) :
    carry (.agg [n, z, cf, v, g]) = carry (.agg [n, z, cf, v, g']) := rfl

/-- The loads and register-indexed loads that sign-extend their result (`LDRS*`), and the
sign extensions: the producers whose narrow-typed result holds a sign-extended register, which
`MOVDreg`/`MOVDnop` of them pass on (`ARM64latelower.rules` "don't extend after proper load",
"fold double extensions"). -/
def signExtends : Op → Bool
  | .ARM64MOVBload | .ARM64MOVHload | .ARM64MOVWload | .ARM64MOVBloadidx | .ARM64MOVHloadidx
  | .ARM64MOVWloadidx | .ARM64MOVHloadidx2 | .ARM64MOVWloadidx4 | .ARM64MOVBreg | .ARM64MOVHreg
  | .ARM64MOVWreg => true
  | _ => false

/-- The generic atomic op an arm64 atomic is (`ARM64.rules:482-504`; the `*Variant` LSE forms
mean the same in a single thread). -/
def atomicOf : Op → Option Op
  | .ARM64STLRB => some .AtomicStore8
  | .ARM64STLRW => some .AtomicStore32
  | .ARM64STLR => some .AtomicStore64
  | .ARM64LoweredAtomicExchange8 => some .AtomicExchange8
  | .ARM64LoweredAtomicExchange32 => some .AtomicExchange32
  | .ARM64LoweredAtomicExchange64 => some .AtomicExchange64
  | .ARM64LoweredAtomicExchange8Variant => some .AtomicExchange8Variant
  | .ARM64LoweredAtomicExchange32Variant => some .AtomicExchange32Variant
  | .ARM64LoweredAtomicExchange64Variant => some .AtomicExchange64Variant
  | .ARM64LoweredAtomicAdd32 => some .AtomicAdd32
  | .ARM64LoweredAtomicAdd64 => some .AtomicAdd64
  | .ARM64LoweredAtomicAdd32Variant => some .AtomicAdd32Variant
  | .ARM64LoweredAtomicAdd64Variant => some .AtomicAdd64Variant
  | .ARM64LoweredAtomicCas32 => some .AtomicCompareAndSwap32
  | .ARM64LoweredAtomicCas64 => some .AtomicCompareAndSwap64
  | .ARM64LoweredAtomicCas32Variant => some .AtomicCompareAndSwap32Variant
  | .ARM64LoweredAtomicCas64Variant => some .AtomicCompareAndSwap64Variant
  | .ARM64LoweredAtomicAnd8 => some .AtomicAnd8value
  | .ARM64LoweredAtomicAnd32 => some .AtomicAnd32value
  | .ARM64LoweredAtomicAnd64 => some .AtomicAnd64value
  | .ARM64LoweredAtomicOr8 => some .AtomicOr8value
  | .ARM64LoweredAtomicOr32 => some .AtomicOr32value
  | .ARM64LoweredAtomicOr64 => some .AtomicOr64value
  | .ARM64LoweredAtomicAnd8Variant => some .AtomicAnd8valueVariant
  | .ARM64LoweredAtomicAnd32Variant => some .AtomicAnd32valueVariant
  | .ARM64LoweredAtomicAnd64Variant => some .AtomicAnd64valueVariant
  | .ARM64LoweredAtomicOr8Variant => some .AtomicOr8valueVariant
  | .ARM64LoweredAtomicOr32Variant => some .AtomicOr32valueVariant
  | .ARM64LoweredAtomicOr64Variant => some .AtomicOr64valueVariant
  | _ => none

end GoFV.SSA.Sem.Arm64
