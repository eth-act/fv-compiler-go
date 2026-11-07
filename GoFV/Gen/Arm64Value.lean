import GoFV.Gen.State
import GoFV.Asm.Reg
import GoFV.Asm.OpAsm

/-!
# arm64 `ssaGenValue`, part A, and the arm64 frame helpers

Exact port (`docs/PASSES3.md` C3, I3 #549) of `cmd/compile/internal/arm64/ssa.go` (go1.27.3
pin 2aae1000ea1d):

* `loadByType`, `storeByType`, `loadByType2`, `storeByType2`, `makeshift`, `genshift`,
  `genIndexedOperand` (lines 23-171), the SIMD register helpers part A uses (`simdRegArng`,
  `simdV01Imm`, `simdV11Asm`, `simdV11`, `simdV11Scalar`: 174-183, 285-308, 333-341, with
  `obj/arm64.RegisterArrangement`, `asm7.go:8753`);
* the `ssaGenValue` cases of lines 579-1037 (moves, `Copy`, `LoadReg`/`StoreReg`,
  `ArgIntReg`/`ArgFloatReg`, ALU, flag tuples, shifts, constants, compares, `MOVDaddr`, loads
  and stores incl. pairs and indexed, `LDAR`/`STLR`, bit fields), 1353-1494 (extension elision,
  unary ops, `LoweredRound*`, `VCNT`, `VUADDLV`, conditional selects and compares) and
  1851-1877 (flag predicates → `CSET`);
* `loadRegResult`, `spillArgReg` (2095-2112);
* `arm64/ggen.go`: `padframe`, `zerorange`, `ginsnop`.

`ssaGenValueA v` is `true` iff `v.Op` is one of these cases (then emitted); the other ops are
part B's (`Arm64ValueRt.lean`). Go's `Fatalf`/`panic` are `throw`s. The SIMD type predicate
`t.IsSIMD()` is false for every type (GOEXPERIMENT simd off).
-/

namespace GoFV.Gen.Arm64

open GoFV.SSA GoFV.Asm

/-! ## Types -/

private def tdef (t : TypeRef) : GenM SSA.TypeDef := do GenM.lift ((← GenM.env).typeDef t)

/-- `t.Size()`. -/
private def tsize (t : TypeRef) (d : SSA.TypeDef) : GenM Int :=
  match d.size with
  | some s => pure s
  | none => throw s!"type t{t}: size not calculated"

/-- `t.IsFloat()`. -/
private def isFloatT (d : SSA.TypeDef) : Bool := d.kind == TypeKind.FLOAT32 || d.kind == TypeKind.FLOAT64

/-- `t.IsSigned()`. -/
private def isSignedT (d : SSA.TypeDef) : Bool :=
  [TypeKind.INT8, .INT16, .INT32, .INT64, .INT].contains d.kind

/-- A `typs` pseudo-type of the `.ssa` file (`types.TypeMem` is `Mem`, `types.TypeFlags` is
`Flags`); Go compares these by pointer. -/
private def pseudoType (name : String) : GenM TypeRef := do
  let e ← GenM.env
  let typs := ((e.file.sections[0]?).bind (·.typs)).getD #[]
  match typs.find? (·.1 == name) with
  | some (_, t) => pure t
  | none => throw s!"typs: no {name}"

/-- `t.IsFlags()`. -/
private def isFlags (t : TypeRef) : GenM Bool := return t == (← pseudoType "Flags")

/-- `t.IsMemory()`. -/
private def isMemory (t : TypeRef) : GenM Bool := do
  let mem ← pseudoType "Mem"
  if t == mem then return true
  let d ← tdef t
  match d.tail with
  | TypeTail.tuple _ s => return d.kind == TypeKind.TUPLE && s == mem
  | .results ts => return d.kind == TypeKind.RESULTS && ts.back? == some mem
  | _ => return false

/-! ## Opcode selection (`ssa.go:23-130`) -/

/-- `loadByType`: the load instruction of type `t`. -/
def loadByType (t : TypeRef) : GenM As := do
  let d ← tdef t
  if isFloatT d then
    match ← tsize t d with
    | 4 => return .FMOVS
    | 8 => return .FMOVD
    | _ => pure ()
  else
    match ← tsize t d with
    | 1 => return if isSignedT d then .MOVB else .MOVBU
    | 2 => return if isSignedT d then .MOVH else .MOVHU
    | 4 => return if isSignedT d then .MOVW else .MOVWU
    | 8 => return .MOVD
    | _ => pure ()
  throw s!"bad load type t{t}"

/-- `storeByType`: the store instruction of type `t`. -/
def storeByType (t : TypeRef) : GenM As := do
  let d ← tdef t
  if isFloatT d then
    match ← tsize t d with
    | 4 => return .FMOVS
    | 8 => return .FMOVD
    | _ => pure ()
  else
    match ← tsize t d with
    | 1 => return .MOVB
    | 2 => return .MOVH
    | 4 => return .MOVW
    | 8 => return .MOVD
    | _ => pure ()
  throw s!"bad store type t{t}"

/-- `loadByType2`: a load of two consecutive slots of type `t` into two registers (`XXX`:
none). -/
private def loadByType2 (t : TypeRef) : GenM As := do
  let d ← tdef t
  if isFloatT d then
    match ← tsize t d with
    | 4 => return .FLDPS
    | 8 => return .FLDPD
    | _ => return .XXX
  else
    match ← tsize t d with
    | 4 => return .LDPW
    | 8 => return .LDP
    | _ => return .XXX

/-- `storeByType2`. -/
private def storeByType2 (t : TypeRef) : GenM As := do
  let d ← tdef t
  if isFloatT d then
    match ← tsize t d with
    | 4 => return .FSTPS
    | 8 => return .FSTPD
    | _ => return .XXX
  else
    match ← tsize t d with
    | 4 => return .STPW
    | 8 => return .STP
    | _ => return .XXX

/-! ## Operands -/

private def regA (r : Int) : Addr := { type := .REG, reg := r }
private def constA (o : Int) : Addr := { type := .CONST, offset := o }
/-- `TYPE_SPECIAL` with the condition in `Offset`. -/
private def specialA (o : Int) : Addr := { type := .SPECIAL, offset := o }

/-- `p.AddRestSource(a)`: appends `a` at `obj.Source` (0). -/
private def addRestSource (a : Addr) (p : Prog) : Prog := { p with rest := p.rest.push (0, a) }

/-- `v.Reg()`. -/
private def vreg (v : Value) : GenM Int := do GenM.lift ((← GenM.env).reg v.id)
private def vreg0 (v : Value) : GenM Int := do GenM.lift ((← GenM.env).reg0 v.id)
private def vreg1 (v : Value) : GenM Int := do GenM.lift ((← GenM.env).reg1 v.id)

/-- `v.Args[i]`. -/
private def argV (v : Value) (i : Nat) : GenM Value := do
  let some a := v.args[i]? | throw s!"v{v.id}: no argument {i}"
  GenM.lift ((← GenM.env).value a)

/-- `v.Args[i].Reg()`. -/
private def argReg (v : Value) (i : Nat) : GenM Int := do
  let some a := v.args[i]? | throw s!"v{v.id}: no argument {i}"
  GenM.lift ((← GenM.env).reg a)

/-- `v.RegName()`: the name of the register `f.RegAlloc` assigns `v`. -/
private def regName (id : ID) : GenM String := do
  match (← GenM.env).loc? id with
  | some (.reg r) =>
    match GoFV.SSA.ARM64.registers[r]? with
    | some x => pure x.name
    | none => throw s!"v{id}: no register {r}"
  | l => throw s!"v{id}: RegName of {repr l}"

/-- `s.Prog(as)` followed by setting the operands. -/
private def emit (as : As) (f : Prog → Prog) : GenM Nat := do
  let p ← GenM.sprog as
  GenM.modP p f
  return p

/-- `makeshift` (`ssa.go:133`): a register shifted by a constant, as an `Offset`. -/
private def makeshift (v : Value) (reg : Int) (typ : Int) (s : Int64) : GenM Int := do
  if s < 0 || s >= 64 then throw s!"v{v.id}: shift out of range: {s.toInt}"
  return ((Int64.ofInt reg &&& 31) <<< 16 ||| Int64.ofInt typ ||| (s &&& 63) <<< 10).toInt

/-- `genshift` (`ssa.go:141`): `r = r0 op (r1 shifted by n)`. -/
private def genshift (v : Value) (as : As) (r0 r1 r : Int) (typ : Int) (n : Int64) :
    GenM Nat := do
  let p ← GenM.sprog as
  let off ← makeshift v r1 typ n
  GenM.modP p fun x =>
    let x := { x with from_ := { x.from_ with type := .SHIFT, offset := off }, reg := r0 }
    if r != 0 then { x with to := { x.to with type := .REG, reg := r } } else x
  return p

/-- `genIndexedOperand` (`ssa.go:155`): the memory operand of an indexed load or store. -/
private def genIndexedOperand (op : Op) (base idx : Int) : Addr :=
  let lsl (k : Int64) : Int :=
    (Int64.ofInt ARM64.REG_LSL ||| k <<< 5 ||| (Int64.ofInt idx &&& 31)).toInt
  let index := match op with
    | .ARM64MOVDloadidx8 | .ARM64MOVDstoreidx8 | .ARM64FMOVDloadidx8 | .ARM64FMOVDstoreidx8 =>
      lsl 3
    | .ARM64MOVWloadidx4 | .ARM64MOVWUloadidx4 | .ARM64MOVWstoreidx4 | .ARM64FMOVSloadidx4
    | .ARM64FMOVSstoreidx4 => lsl 2
    | .ARM64MOVHloadidx2 | .ARM64MOVHUloadidx2 | .ARM64MOVHstoreidx2 => lsl 1
    | _ => idx
  { type := .MEM, reg := base, index }

/-- `simdRegArng` (`ssa.go:174`) with `RegisterArrangement(reg, arng, false)` for the vector
arrangements part A uses (`ARNG_8B`, `ARNG_16B`). -/
private def simdRegArng (reg : Int) (arng : Int) : GenM Int := do
  if reg < ARM64.REG_F0 || ARM64.REG_F31 < reg then throw s!"expected fp register: r{reg}"
  if arng != ARM64.ARNG_8B && arng != ARM64.ARNG_16B then
    throw s!"bad simd register arrangement: {arng}"
  let a := Int64.ofInt arng &&& 15
  return ARM64.REG_ARNG + (Int64.ofInt reg &&& 31).toInt + (a <<< 5).toInt

/-- `simdV11Asm` (`ssa.go:296`). -/
private def simdV11Asm (as : As) (src dst : Int) (arng : Int) : GenM Nat := do
  let p ← GenM.sprog as
  let s ← simdRegArng src arng
  let d ← simdRegArng dst arng
  GenM.modP p fun x => { x with from_ := { x.from_ with type := .REG, reg := s },
                                to := { x.to with type := .REG, reg := d } }
  return p

/-- `v.AuxUInt8()`. -/
private def auxUInt8 (v : Value) : GenM Int := do
  if v.op.auxType != .UInt8 then throw s!"op {v.op.exportName} doesn't have a uint8 aux field"
  return v.auxInt.toInt % 256

/-- `condBits[op]` (absent: 0). -/
private def condBitsOf (op : Option Op) : Int :=
  match op with
  | some o => (ARM64.condBits o).getD 0
  | none => 0

/-- `ssa.Op(k)` for an `int64` auxint (`Op` is `int32`). -/
private def opOfAux (k : Int64) : Option Op :=
  let n := k.toInt32.toInt
  if n < 0 then none else Op.ofGoNum? n.toNat

/-! ## `ssaGenValue` cases -/

/-- `Copy`, `MOVDreg` (`ssa.go:579`). -/
private def genCopy (v : Value) : GenM Unit := do
  if ← isMemory v.type then return
  let x ← argReg v 0
  let y ← vreg v
  if x == y then return
  let d ← tdef v.type
  let as ← if isFloatT d then
      match ← tsize v.type d with
      | 4 => pure As.FMOVS
      | 8 => pure As.FMOVD
      | _ => throw "bad float size"
    else pure As.MOVD
  discard <| emit as fun p => { p with from_ := { p.from_ with type := .REG, reg := x },
                                       to := { p.to with type := .REG, reg := y } }

/-- `ArgIntReg`, `ArgFloatReg` (`ssa.go:633`): the first one records `f.RegArgs` as the
`FuncInfo` spills, pairing adjacent same-class slots. -/
private def genArgReg (v : Value) : GenM Unit := do
  let e ← GenM.env
  if e.f.entry != v.block then
    throw s!"in {e.file.name.toStringLossy}, badly placed ArgIReg or ArgFReg: b{v.block} v{v.id}"
  let args := (← get).regArgs
  if args.isEmpty then return
  modify fun s => { s with regArgs := #[] }
  let mut i := 0
  while i < args.size do
    let a := args[i]!
    let addr := GenM.spillSlotAddr a ARM64.REGSP 8
    let mut paired := false
    if i + 1 < args.size then
      let b := args[i + 1]!
      let da ← tdef a.type
      let db ← tdef b.type
      let sa ← tsize a.type da
      if sa == (← tsize b.type db) && isFloatT da == isFloatT db && b.off == a.off + sa then
        let ld ← loadByType2 a.type
        let st ← storeByType2 a.type
        if ld != .XXX && st != .XXX then
          let sp : Spill := { addr, reg := a.reg, reg2 := b.reg, spill := st, unspill := ld }
          modify fun s => { s with spills := s.spills.push sp }
          paired := true
    if paired then
      i := i + 2
    else
      let ld ← loadByType a.type
      let st ← storeByType a.type
      let sp : Spill := { addr, reg := a.reg, reg2 := 0, spill := st, unspill := ld }
      modify fun s => { s with spills := s.spills.push sp }
      i := i + 1

/-- `ssagen.AddAux(&p.From, v)` / `(&p.To, v)` on Prog `p`. -/
private def addAuxFrom (p : Nat) (v : Value) : GenM Unit := do
  let x ← GenM.getP p
  let f ← GenM.addAux x.from_ v
  GenM.modP p fun x => { x with from_ := f }

private def addAuxTo (p : Nat) (v : Value) : GenM Unit := do
  let x ← GenM.getP p
  let t ← GenM.addAux x.to v
  GenM.modP p fun x => { x with to := t }

/-- `MOVDaddr` (`ssa.go:896`). -/
private def genMOVDaddr (v : Value) : GenM Unit := do
  let r0 ← argReg v 0
  let r ← vreg v
  let p ← emit .MOVD fun p => { p with from_ := { p.from_ with type := .ADDR, reg := r0 },
                                       to := { p.to with type := .REG, reg := r } }
  let e ← GenM.env
  let (wantreg, auxType) ← match v.aux with
    | none =>
      GenM.modP p fun x => { x with from_ := { x.from_ with offset := v.auxInt.toInt } }
      pure ("SP", "<nil>")
    | some a =>
      match (← GenM.lift (e.auxDef a)).kind with
      | .sym .. => addAuxFrom p v; pure ("SB", "*obj.LSym")
      | .name .. => addAuxFrom p v; pure ("SP", "*ir.Name")
      | _ => throw s!"v{v.id}: aux is of unknown type"
  let some a0 := v.args[0]? | throw s!"v{v.id}: no argument 0"
  let reg ← regName a0
  if reg != wantreg then
    throw s!"v{v.id}: bad reg {reg} for symbol type {auxType}, want {wantreg}"

/-- The unary cases (`MVN`, `NEG`, …, `ssa.go:1386`): `op Rarg0, Rout`. -/
private def genUnary (v : Value) : GenM Unit := do
  let r0 ← argReg v 0
  let r ← vreg v
  discard <| emit (opAsm v.op) fun p =>
    { p with from_ := { p.from_ with type := .REG, reg := r0 },
             to := { p.to with type := .REG, reg := r } }

/-- `MOVBreg` … `MOVWUreg` (`ssa.go:1353`): a move instead of an extension when the argument
(through copies) is a load of the proper type; else the unary case. -/
private partial def genExt (v : Value) : GenM Unit := do
  let rec walk (a : Value) : GenM Value := do
    if a.op == .Copy || a.op == .ARM64MOVDreg then walk (← argV a 0) else pure a
  let a ← walk (← argV v 0)
  if a.op == .LoadReg then
    let d ← tdef a.type
    let sz ← tsize a.type d
    let sg := isSignedT d
    let proper := match v.op with
      | .ARM64MOVBreg => sz == 1 && sg
      | .ARM64MOVBUreg => sz == 1 && !sg
      | .ARM64MOVHreg => sz == 2 && sg
      | .ARM64MOVHUreg => sz == 2 && !sg
      | .ARM64MOVWreg => sz == 4 && sg
      | .ARM64MOVWUreg => sz == 4 && !sg
      | _ => false
    if proper then
      let r ← vreg v
      let r0 ← argReg v 0
      if r == r0 then return
      discard <| emit .MOVD fun p =>
        { p with from_ := { p.from_ with type := .REG, reg := r0 },
                 to := { p.to with type := .REG, reg := r } }
      return
  genUnary v

/-- The op groups of part A. -/
private inductive Case where
  | copy | nop | vmovi16b | loadReg | storeReg | argReg
  | binary | ternary | constOp | addsConstFlags | adcZeroCarry | flagsBinary | negsFlags
  | ngcZeroCarry | extr
  | shiftUnary (typ : Int) | shiftBinary (typ : Int) | shiftCmp (typ : Int)
  | movDconst | fconst | fcmp0 | cmp | cmpConst | movDaddr | load | loadPair | loadIdx | ldar
  | store | storeIdx | storePair | bfi | bfx
  | ext | unary | vcnt | vuaddlv | csel | csinc | csetm | ccmp | cset

private def caseOf : Op → Option Case
  | .Copy | .ARM64MOVDreg => some .copy
  | .ARM64MOVDnop | .ARM64ZERO => some .nop
  | .ARM64VMOVI16B => some .vmovi16b
  | .LoadReg => some .loadReg
  | .StoreReg => some .storeReg
  | .ArgIntReg | .ArgFloatReg => some .argReg
  | .ARM64ADD | .ARM64SUB | .ARM64AND | .ARM64OR | .ARM64XOR | .ARM64BIC | .ARM64EON
  | .ARM64ORN | .ARM64MUL | .ARM64MULW | .ARM64MNEG | .ARM64MNEGW | .ARM64MULH | .ARM64UMULH
  | .ARM64MULL | .ARM64UMULL | .ARM64DIV | .ARM64UDIV | .ARM64DIVW | .ARM64UDIVW | .ARM64MOD
  | .ARM64UMOD | .ARM64MODW | .ARM64UMODW | .ARM64SLL | .ARM64SRL | .ARM64SRA | .ARM64FADDS
  | .ARM64FADDD | .ARM64FSUBS | .ARM64FSUBD | .ARM64FMULS | .ARM64FMULD | .ARM64FNMULS
  | .ARM64FNMULD | .ARM64FDIVS | .ARM64FDIVD | .ARM64FMINS | .ARM64FMIND | .ARM64FMAXS
  | .ARM64FMAXD | .ARM64ROR | .ARM64RORW => some .binary
  | .ARM64FMADDS | .ARM64FMADDD | .ARM64FNMADDS | .ARM64FNMADDD | .ARM64FMSUBS
  | .ARM64FMSUBD | .ARM64FNMSUBS | .ARM64FNMSUBD | .ARM64MADD | .ARM64MADDW | .ARM64MSUB
  | .ARM64MSUBW => some .ternary
  | .ARM64ADDconst | .ARM64SUBconst | .ARM64ANDconst | .ARM64ORconst | .ARM64XORconst
  | .ARM64SLLconst | .ARM64SRLconst | .ARM64SRAconst | .ARM64RORconst | .ARM64RORWconst =>
    some .constOp
  | .ARM64ADDSconstflags => some .addsConstFlags
  | .ARM64ADCzerocarry => some .adcZeroCarry
  | .ARM64ADCSflags | .ARM64ADDSflags | .ARM64SBCSflags | .ARM64SUBSflags => some .flagsBinary
  | .ARM64NEGSflags => some .negsFlags
  | .ARM64NGCzerocarry => some .ngcZeroCarry
  | .ARM64EXTRconst | .ARM64EXTRWconst => some .extr
  | .ARM64MVNshiftLL | .ARM64NEGshiftLL => some (.shiftUnary ARM64.SHIFT_LL)
  | .ARM64MVNshiftRL | .ARM64NEGshiftRL => some (.shiftUnary ARM64.SHIFT_LR)
  | .ARM64MVNshiftRA | .ARM64NEGshiftRA => some (.shiftUnary ARM64.SHIFT_AR)
  | .ARM64MVNshiftRO => some (.shiftUnary ARM64.SHIFT_ROR)
  | .ARM64ADDshiftLL | .ARM64SUBshiftLL | .ARM64ANDshiftLL | .ARM64ORshiftLL
  | .ARM64XORshiftLL | .ARM64EONshiftLL | .ARM64ORNshiftLL | .ARM64BICshiftLL =>
    some (.shiftBinary ARM64.SHIFT_LL)
  | .ARM64ADDshiftRL | .ARM64SUBshiftRL | .ARM64ANDshiftRL | .ARM64ORshiftRL
  | .ARM64XORshiftRL | .ARM64EONshiftRL | .ARM64ORNshiftRL | .ARM64BICshiftRL =>
    some (.shiftBinary ARM64.SHIFT_LR)
  | .ARM64ADDshiftRA | .ARM64SUBshiftRA | .ARM64ANDshiftRA | .ARM64ORshiftRA
  | .ARM64XORshiftRA | .ARM64EONshiftRA | .ARM64ORNshiftRA | .ARM64BICshiftRA =>
    some (.shiftBinary ARM64.SHIFT_AR)
  | .ARM64ANDshiftRO | .ARM64ORshiftRO | .ARM64XORshiftRO | .ARM64EONshiftRO
  | .ARM64ORNshiftRO | .ARM64BICshiftRO => some (.shiftBinary ARM64.SHIFT_ROR)
  | .ARM64MOVDconst => some .movDconst
  | .ARM64FMOVSconst | .ARM64FMOVDconst => some .fconst
  | .ARM64FCMPS0 | .ARM64FCMPD0 => some .fcmp0
  | .ARM64CMP | .ARM64CMPW | .ARM64CMN | .ARM64CMNW | .ARM64TST | .ARM64TSTW | .ARM64FCMPS
  | .ARM64FCMPD => some .cmp
  | .ARM64CMPconst | .ARM64CMPWconst | .ARM64CMNconst | .ARM64CMNWconst | .ARM64TSTconst
  | .ARM64TSTWconst => some .cmpConst
  | .ARM64CMPshiftLL | .ARM64CMNshiftLL | .ARM64TSTshiftLL => some (.shiftCmp ARM64.SHIFT_LL)
  | .ARM64CMPshiftRL | .ARM64CMNshiftRL | .ARM64TSTshiftRL => some (.shiftCmp ARM64.SHIFT_LR)
  | .ARM64CMPshiftRA | .ARM64CMNshiftRA | .ARM64TSTshiftRA => some (.shiftCmp ARM64.SHIFT_AR)
  | .ARM64TSTshiftRO => some (.shiftCmp ARM64.SHIFT_ROR)
  | .ARM64MOVDaddr => some .movDaddr
  | .ARM64MOVBload | .ARM64MOVBUload | .ARM64MOVHload | .ARM64MOVHUload | .ARM64MOVWload
  | .ARM64MOVWUload | .ARM64MOVDload | .ARM64FMOVSload | .ARM64FMOVDload
  | .ARM64FMOVQload => some .load
  | .ARM64LDP | .ARM64LDPW | .ARM64LDPSW | .ARM64FLDPD | .ARM64FLDPS | .ARM64FLDPQ =>
    some .loadPair
  | .ARM64MOVBloadidx | .ARM64MOVBUloadidx | .ARM64MOVHloadidx | .ARM64MOVHUloadidx
  | .ARM64MOVWloadidx | .ARM64MOVWUloadidx | .ARM64MOVDloadidx | .ARM64FMOVSloadidx
  | .ARM64FMOVDloadidx | .ARM64MOVHloadidx2 | .ARM64MOVHUloadidx2 | .ARM64MOVWloadidx4
  | .ARM64MOVWUloadidx4 | .ARM64MOVDloadidx8 | .ARM64FMOVDloadidx8
  | .ARM64FMOVSloadidx4 => some .loadIdx
  | .ARM64LDAR | .ARM64LDARB | .ARM64LDARW => some .ldar
  | .ARM64MOVBstore | .ARM64MOVHstore | .ARM64MOVWstore | .ARM64MOVDstore
  | .ARM64FMOVSstore | .ARM64FMOVDstore | .ARM64FMOVQstore | .ARM64STLRB | .ARM64STLR
  | .ARM64STLRW => some .store
  | .ARM64MOVBstoreidx | .ARM64MOVHstoreidx | .ARM64MOVWstoreidx | .ARM64MOVDstoreidx
  | .ARM64FMOVSstoreidx | .ARM64FMOVDstoreidx | .ARM64MOVHstoreidx2 | .ARM64MOVWstoreidx4
  | .ARM64FMOVSstoreidx4 | .ARM64MOVDstoreidx8 | .ARM64FMOVDstoreidx8 => some .storeIdx
  | .ARM64STP | .ARM64STPW | .ARM64FSTPD | .ARM64FSTPS | .ARM64FSTPQ => some .storePair
  | .ARM64BFI | .ARM64BFXIL => some .bfi
  | .ARM64SBFIZ | .ARM64SBFX | .ARM64UBFIZ | .ARM64UBFX => some .bfx
  | .ARM64MOVBreg | .ARM64MOVBUreg | .ARM64MOVHreg | .ARM64MOVHUreg | .ARM64MOVWreg
  | .ARM64MOVWUreg => some .ext
  | .ARM64MVN | .ARM64NEG | .ARM64FABSD | .ARM64FABSS | .ARM64FMOVDfpgp | .ARM64FMOVDgpfp
  | .ARM64FMOVSfpgp | .ARM64FMOVSgpfp | .ARM64FNEGS | .ARM64FNEGD | .ARM64FSQRTS
  | .ARM64FSQRTD | .ARM64FCVTZSSW | .ARM64FCVTZSDW | .ARM64FCVTZUSW | .ARM64FCVTZUDW
  | .ARM64FCVTZSS | .ARM64FCVTZSD | .ARM64FCVTZUS | .ARM64FCVTZUD | .ARM64SCVTFWS
  | .ARM64SCVTFWD | .ARM64SCVTFS | .ARM64SCVTFD | .ARM64UCVTFWS | .ARM64UCVTFWD
  | .ARM64UCVTFS | .ARM64UCVTFD | .ARM64FCVTSD | .ARM64FCVTDS | .ARM64REV | .ARM64REVW
  | .ARM64REV16 | .ARM64REV16W | .ARM64RBIT | .ARM64RBITW | .ARM64CLZ | .ARM64CLZW
  | .ARM64FRINTAD | .ARM64FRINTMD | .ARM64FRINTND | .ARM64FRINTPD | .ARM64FRINTZD
  | .ARM64FRINTAS | .ARM64FRINTMS | .ARM64FRINTNS | .ARM64FRINTPS | .ARM64FRINTZS => some .unary
  | .ARM64LoweredRound32F | .ARM64LoweredRound64F => some .nop
  | .ARM64VCNT => some .vcnt
  | .ARM64VUADDLV => some .vuaddlv
  | .ARM64CSEL | .ARM64CSEL0 => some .csel
  | .ARM64CSINC | .ARM64CSINV | .ARM64CSNEG => some .csinc
  | .ARM64CSETM => some .csetm
  | .ARM64CCMP | .ARM64CCMN | .ARM64CCMPconst | .ARM64CCMNconst | .ARM64CCMPW | .ARM64CCMNW
  | .ARM64CCMPWconst | .ARM64CCMNWconst => some .ccmp
  | .ARM64Equal | .ARM64NotEqual | .ARM64LessThan | .ARM64LessEqual | .ARM64GreaterThan
  | .ARM64GreaterEqual | .ARM64LessThanU | .ARM64LessEqualU | .ARM64GreaterThanU
  | .ARM64GreaterEqualU | .ARM64LessThanF | .ARM64LessEqualF | .ARM64GreaterThanF
  | .ARM64GreaterEqualF | .ARM64NotLessThanF | .ARM64NotLessEqualF | .ARM64NotGreaterThanF
  | .ARM64NotGreaterEqualF | .ARM64LessThanNoov | .ARM64GreaterEqualNoov => some .cset
  | _ => none

/-- Emits the part-A case `c` of `v`. -/
private def genCase (v : Value) : Case → GenM Unit
  | .copy => genCopy v
  | .nop => pure ()
  | .vmovi16b => do
    -- simdV01Imm(s, v, ARNG_16B)
    let p ← GenM.sprog (opAsm v.op)
    let k ← auxUInt8 v
    let r ← simdRegArng (← vreg v) ARM64.ARNG_16B
    GenM.modP p fun x => { x with from_ := { x.from_ with type := .CONST, offset := k },
                                  to := { x.to with type := .REG, reg := r } }
  | .loadReg => do
    if ← isFlags v.type then throw s!"v{v.id}: load flags not implemented"
    let p ← GenM.sprog (← loadByType v.type)
    let f ← GenM.addrAuto (← argV v 0)
    let r ← vreg v
    GenM.modP p fun x => { x with from_ := f, to := { x.to with type := .REG, reg := r } }
  | .storeReg => do
    if ← isFlags v.type then throw s!"v{v.id}: store flags not implemented"
    let p ← GenM.sprog (← storeByType v.type)
    let r ← argReg v 0
    let t ← GenM.addrAuto v
    GenM.modP p fun x => { x with from_ := { x.from_ with type := .REG, reg := r }, to := t }
  | .argReg => genArgReg v
  | .binary => do
    let r ← vreg v
    let r1 ← argReg v 0
    let r2 ← argReg v 1
    discard <| emit (opAsm v.op) fun p =>
      { p with from_ := { p.from_ with type := .REG, reg := r2 }, reg := r1,
               to := { p.to with type := .REG, reg := r } }
  | .ternary => do
    let rt ← vreg v
    let ra ← argReg v 0
    let rm ← argReg v 1
    let rn ← argReg v 2
    discard <| emit (opAsm v.op) fun p =>
      addRestSource (regA rn)
        { p with reg := ra, from_ := { p.from_ with type := .REG, reg := rm },
                 to := { p.to with type := .REG, reg := rt } }
  | .constOp => do
    let r0 ← argReg v 0
    let r ← vreg v
    discard <| emit (opAsm v.op) fun p =>
      { p with from_ := { p.from_ with type := .CONST, offset := v.auxInt.toInt }, reg := r0,
               to := { p.to with type := .REG, reg := r } }
  | .addsConstFlags => do
    let r0 ← argReg v 0
    let r ← vreg0 v
    discard <| emit (opAsm v.op) fun p =>
      { p with from_ := { p.from_ with type := .CONST, offset := v.auxInt.toInt }, reg := r0,
               to := { p.to with type := .REG, reg := r } }
  | .adcZeroCarry => do
    let r ← vreg v
    discard <| emit (opAsm v.op) fun p =>
      { p with from_ := { p.from_ with type := .REG, reg := ARM64.REGZERO }, reg := ARM64.REGZERO,
               to := { p.to with type := .REG, reg := r } }
  | .flagsBinary => do
    let r ← vreg0 v
    let r1 ← argReg v 0
    let r2 ← argReg v 1
    discard <| emit (opAsm v.op) fun p =>
      { p with from_ := { p.from_ with type := .REG, reg := r2 }, reg := r1,
               to := { p.to with type := .REG, reg := r } }
  | .negsFlags => do
    let r0 ← argReg v 0
    let r ← vreg0 v
    discard <| emit (opAsm v.op) fun p =>
      { p with from_ := { p.from_ with type := .REG, reg := r0 },
               to := { p.to with type := .REG, reg := r } }
  | .ngcZeroCarry => do
    let r ← vreg v
    discard <| emit (opAsm v.op) fun p =>
      { p with from_ := { p.from_ with type := .REG, reg := ARM64.REGZERO },
               to := { p.to with type := .REG, reg := r } }
  | .extr => do
    let r0 ← argReg v 0
    let r1 ← argReg v 1
    let r ← vreg v
    discard <| emit (opAsm v.op) fun p =>
      { (addRestSource (regA r0)
          { p with from_ := { p.from_ with type := .CONST, offset := v.auxInt.toInt } }) with
        reg := r1, to := { p.to with type := .REG, reg := r } }
  | .shiftUnary typ => do
    discard <| genshift v (opAsm v.op) 0 (← argReg v 0) (← vreg v) typ v.auxInt
  | .shiftBinary typ => do
    discard <| genshift v (opAsm v.op) (← argReg v 0) (← argReg v 1) (← vreg v) typ v.auxInt
  | .shiftCmp typ => do
    discard <| genshift v (opAsm v.op) (← argReg v 0) (← argReg v 1) 0 typ v.auxInt
  | .movDconst => do
    let r ← vreg v
    discard <| emit (opAsm v.op) fun p =>
      { p with from_ := { p.from_ with type := .CONST, offset := v.auxInt.toInt },
               to := { p.to with type := .REG, reg := r } }
  | .fconst => do
    let r ← vreg v
    discard <| emit (opAsm v.op) fun p =>
      { p with from_ := { p.from_ with type := .FCONST, val := .float v.auxInt.toUInt64 },
               to := { p.to with type := .REG, reg := r } }
  | .fcmp0 => do
    let r0 ← argReg v 0
    discard <| emit (opAsm v.op) fun p =>
      { p with from_ := { p.from_ with type := .FCONST, val := .float 0 }, reg := r0 }
  | .cmp => do
    let r1 ← argReg v 1
    let r0 ← argReg v 0
    discard <| emit (opAsm v.op) fun p =>
      { p with from_ := { p.from_ with type := .REG, reg := r1 }, reg := r0 }
  | .cmpConst => do
    let r0 ← argReg v 0
    discard <| emit (opAsm v.op) fun p =>
      { p with from_ := { p.from_ with type := .CONST, offset := v.auxInt.toInt }, reg := r0 }
  | .movDaddr => genMOVDaddr v
  | .load => do
    let r0 ← argReg v 0
    let r ← vreg v
    let p ← emit (opAsm v.op) fun p => { p with from_ := { p.from_ with type := .MEM, reg := r0 } }
    addAuxFrom p v
    GenM.modP p fun x => { x with to := { x.to with type := .REG, reg := r } }
  | .loadPair => do
    let r0 ← argReg v 0
    let ra ← vreg0 v
    let rb ← vreg1 v
    let p ← emit (opAsm v.op) fun p => { p with from_ := { p.from_ with type := .MEM, reg := r0 } }
    addAuxFrom p v
    GenM.modP p fun x => { x with to := { x.to with type := .REGREG, reg := ra, offset := rb } }
  | .loadIdx => do
    let f := genIndexedOperand v.op (← argReg v 0) (← argReg v 1)
    let r ← vreg v
    discard <| emit (opAsm v.op) fun p => { p with from_ := f,
                                                   to := { p.to with type := .REG, reg := r } }
  | .ldar => do
    let r0 ← argReg v 0
    let r ← vreg0 v
    let p ← emit (opAsm v.op) fun p => { p with from_ := { p.from_ with type := .MEM, reg := r0 } }
    addAuxFrom p v
    GenM.modP p fun x => { x with to := { x.to with type := .REG, reg := r } }
  | .store => do
    let r1 ← argReg v 1
    let r0 ← argReg v 0
    let p ← emit (opAsm v.op) fun p =>
      { p with from_ := { p.from_ with type := .REG, reg := r1 },
               to := { p.to with type := .MEM, reg := r0 } }
    addAuxTo p v
  | .storeIdx => do
    let t := genIndexedOperand v.op (← argReg v 0) (← argReg v 1)
    let r2 ← argReg v 2
    discard <| emit (opAsm v.op) fun p =>
      { p with to := t, from_ := { p.from_ with type := .REG, reg := r2 } }
  | .storePair => do
    let r1 ← argReg v 1
    let r2 ← argReg v 2
    let r0 ← argReg v 0
    let p ← emit (opAsm v.op) fun p =>
      { p with from_ := { p.from_ with type := .REGREG, reg := r1, offset := r2 },
               to := { p.to with type := .MEM, reg := r0 } }
    addAuxTo p v
  | .bfi => do
    let r1 ← argReg v 1
    let r ← vreg v
    discard <| emit (opAsm v.op) fun p =>
      { (addRestSource (constA (v.auxInt &&& 0xff).toInt)
          { p with from_ := { p.from_ with type := .CONST, offset := (v.auxInt >>> 8).toInt } })
        with reg := r1, to := { p.to with type := .REG, reg := r } }
  | .bfx => do
    let r0 ← argReg v 0
    let r ← vreg v
    discard <| emit (opAsm v.op) fun p =>
      { (addRestSource (constA (v.auxInt &&& 0xff).toInt)
          { p with from_ := { p.from_ with type := .CONST, offset := (v.auxInt >>> 8).toInt } })
        with reg := r0, to := { p.to with type := .REG, reg := r } }
  | .ext => genExt v
  | .unary => genUnary v
  | .vcnt => do
    discard <| simdV11Asm (opAsm v.op) (← argReg v 0) (← vreg v) ARM64.ARNG_8B
  | .vuaddlv => do
    -- simdV11Scalar(s, v, ARNG_8B)
    let p ← GenM.sprog (opAsm v.op)
    let s ← simdRegArng (← argReg v 0) ARM64.ARNG_8B
    let r ← vreg v
    let rv := r - ARM64.REG_F0 + ARM64.REG_V0
    GenM.modP p fun x => { x with from_ := { x.from_ with type := .REG, reg := s },
                                  to := { x.to with type := .REG, reg := rv } }
  | .csel => do
    let r1 ← if v.op != .ARM64CSEL0 then argReg v 1 else pure ARM64.REGZERO
    let cc := condBitsOf (opOfAux v.auxInt)
    let r0 ← argReg v 0
    let r ← vreg v
    discard <| emit (opAsm v.op) fun p =>
      addRestSource (regA r1)
        { p with from_ := specialA cc, reg := r0, to := { p.to with type := .REG, reg := r } }
  | .csinc => do
    let cc := condBitsOf (opOfAux v.auxInt)
    let r0 ← argReg v 0
    let r1 ← argReg v 1
    let r ← vreg v
    discard <| emit (opAsm v.op) fun p =>
      addRestSource (regA r1)
        { p with from_ := specialA cc, reg := r0, to := { p.to with type := .REG, reg := r } }
  | .csetm => do
    let cc := condBitsOf (opOfAux v.auxInt)
    let r ← vreg v
    discard <| emit .CSETM fun p =>
      { p with from_ := specialA cc, to := { p.to with type := .REG, reg := r } }
  | .ccmp => do
    -- v.AuxArm64ConditionalParams() (`rewrite.go:699`)
    if v.op.auxType != .ARM64ConditionalParams then
      throw s!"op {v.op.exportName} doesn't have a ARM64ConditionalParams aux field"
    let i := v.auxInt
    let cond := Op.ofGoNum? (i &&& 0xffff).toInt.toNat
    let nzcv := ((i >>> 16) &&& 0x0f).toInt
    let constValue := ((i >>> 20) &&& 0x1f).toInt
    let ind := (i >>> 25) == 1
    let r0 ← argReg v 0
    let rest ← if ind then pure (constA constValue) else regA <$> argReg v 1
    discard <| emit (opAsm v.op) fun p =>
      addRestSource rest
        { p with reg := r0, from_ := specialA (condBitsOf cond),
                 to := { p.to with type := .CONST, offset := nzcv } }
  | .cset => do
    let r ← vreg v
    discard <| emit .CSET fun p =>
      { p with from_ := specialA (condBitsOf (some v.op)),
               to := { p.to with type := .REG, reg := r } }

/-- C3 part A: `true` iff `v.Op` is one of part A's ops (then emitted, `ssa.go:579-1037,
1353-1494, 1851-1877`). -/
def ssaGenValueA (v : Value) : GenM Bool := do
  match caseOf v.op with
  | some c => genCase v c; return true
  | none => return false

/-! ## Results, arguments and the frame (`ssa.go:2095-2112`, `ggen.go`) -/

/-- `arm64.ginsnop`: `HINT $0`. -/
def ginsnop : GenM Nat := do
  let p ← GenM.prog .HINT
  GenM.modP p fun x => { x with from_ := { x.from_ with type := .CONST } }
  return p

/-- `arm64.zerorange`: zeroes `cnt` bytes at `off` (above the saved LR) after Prog `p`;
returns the last Prog appended. -/
def zeroRange (p : Nat) (off cnt : Int) : GenM Nat := do
  if cnt.tmod 8 != 0 then throw "zeroed region not aligned"
  let mut p := p
  let mut off := off + 8
  let mut cnt := cnt
  while cnt >= 16 && off < 512 do
    p ← GenM.append p .STP .REGREG ARM64.REGZERO ARM64.REGZERO .MEM ARM64.REGSP off
    off := off + 16
    cnt := cnt - 16
  while cnt != 0 do
    p ← GenM.append p .MOVD .REG ARM64.REGZERO 0 .MEM ARM64.REGSP off
    off := off + 8
    cnt := cnt - 8
  return p

/-- `arm64.spillArgReg`: stores `reg` to the parameter `n` (offset `off` within it) after
Prog `p`. -/
def spillArgReg (p : Nat) (t : TypeRef) (reg : Int) (n : Nat) (off : Int) : GenM Nat := do
  let as ← storeByType t
  let q ← GenM.append p as .REG reg 0 .MEM 0 ((← GenM.frameOffset n) + off)
  let y ← GenM.nameSym n
  GenM.modP q fun x => { x with to := { x.to with name := .PARAM, sym := some y },
                                pos := x.pos.withNotStmt }
  return q

/-- `arm64.loadRegResult`: loads the result `n` (offset `off` within it) into `reg`. -/
def loadRegResult (t : TypeRef) (reg : Int) (n : Nat) (off : Int) : GenM Nat := do
  let p ← GenM.sprog (← loadByType t)
  let y ← GenM.nameSym n
  let o := (← GenM.frameOffset n) + off
  GenM.modP p fun x => { x with from_ := { x.from_ with type := .MEM, name := .AUTO,
                                                         sym := some y, offset := o },
                                to := { x.to with type := .REG, reg := reg } }
  return p

/-- `arm64.padframe`: rounds the frame up to 16 bytes. -/
def padFrame (frame : Int) : Int :=
  if frame.tmod 16 != 0 then frame + (16 - frame.tmod 16) else frame

end GoFV.Gen.Arm64
