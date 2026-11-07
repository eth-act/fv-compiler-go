import GoFV.Arm64.State

/-!
# ARM64 instructions of the emitted subset (`docs/plans/semantics3.md` §3 (a))

One constructor per encoding class of the Arm ARM (DDI 0487, C4.1 "A64 instruction set
encoding") that the Go compiler and assembler emit on linux/arm64 (the words of the quick
corpus' asm sections, `docs/contracts/export.md` "gofv-prog 1"). Fields are the encoding's
fields, unchanged, so `decode` (`Decode.lean`) is field extraction plus the validity conditions,
and `exec` (`Exec.lean`) carries the instruction's pseudocode. Field names follow the Arm ARM
(`sf`, `opc`, `S`, `sh`, `imm12`, …); boolean fields are single encoding bits.
-/

namespace GoFV.Arm64

/-- Kinds of unconditional branch to a register. -/
inductive BrKind where
  | br | blr | ret
  deriving DecidableEq, Repr

/-- Indexing of the 9-bit signed immediate load/store forms (bits 11:10). -/
inductive Idx where
  /-- `LDUR`/`STUR` (00). -/
  | unscaled
  /-- Post-index (01): access at the base, then base += imm. -/
  | post
  /-- Pre-index (11): base += imm, then access at the base. -/
  | pre
  deriving DecidableEq, Repr

/-- The addressing mode of a single-register load/store. -/
inductive AMode where
  /-- `[Rn, #imm12 << scale]` (unsigned offset). -/
  | uimm (imm12 : BitVec 12)
  /-- `[Rn, #simm9]`, `[Rn], #simm9`, `[Rn, #simm9]!`. -/
  | simm (imm9 : BitVec 9) (idx : Idx)
  /-- `[Rn, Rm, <extend> #(S ? scale : 0)]` (`option` ∈ {UXTW, LSL, SXTW, SXTX}). -/
  | reg (rm : Reg) (option : BitVec 3) (s : Bool)
  deriving DecidableEq, Repr

inductive Insn where
  /-- `ADR`/`ADRP` (`page`): PC-relative address. `imm = immhi:immlo`. -/
  | adr (page : Bool) (imm : BitVec 21) (rd : Reg)
  /-- `ADD`/`ADDS`/`SUB`/`SUBS` (immediate); `sh`: `imm12 << 12`. -/
  | addSubImm (sf sub setf sh : Bool) (imm12 : BitVec 12) (rn rd : Reg)
  /-- `AND`/`ORR`/`EOR`/`ANDS` (immediate, `DecodeBitMasks`). -/
  | logImm (sf : Bool) (opc : BitVec 2) (n : Bool) (immr imms : BitVec 6) (rn rd : Reg)
  /-- `MOVN` (opc 00), `MOVZ` (10), `MOVK` (11). -/
  | movWide (sf : Bool) (opc : BitVec 2) (hw : BitVec 2) (imm16 : BitVec 16) (rd : Reg)
  /-- `SBFM` (opc 00), `BFM` (01), `UBFM` (10). -/
  | bitfield (sf : Bool) (opc : BitVec 2) (immr imms : BitVec 6) (rn rd : Reg)
  /-- `EXTR`. -/
  | extr (sf : Bool) (rm : Reg) (imms : BitVec 6) (rn rd : Reg)
  /-- `B`/`BL` (`link`). -/
  | b (link : Bool) (imm26 : BitVec 26)
  /-- `B.cond`. -/
  | bcond (cond : BitVec 4) (imm19 : BitVec 19)
  /-- `CBZ`/`CBNZ` (`nz`). -/
  | cbz (sf nz : Bool) (imm19 : BitVec 19) (rt : Reg)
  /-- `TBZ`/`TBNZ` (`nz`); `bit = b5:b40`. -/
  | tbz (nz : Bool) (bit : BitVec 6) (imm14 : BitVec 14) (rt : Reg)
  /-- `BR`/`BLR`/`RET`. -/
  | br (kind : BrKind) (rn : Reg)
  /-- `NOP` (`HINT #0`). The other hints are other instructions (`PACIASP`, `BTI`, …), which Go
  does not emit. -/
  | nop
  /-- `DMB`/`DSB`/`ISB`/`CLREX` (`op2` bits 7:5): no effect on one core. -/
  | barrier (op2 : BitVec 3) (crm : BitVec 4)
  /-- `BRK #imm16`. -/
  | brk (imm16 : BitVec 16)
  /-- `UDF #imm16` (the all-zero word is `UDF #0`). -/
  | udf (imm16 : BitVec 16)
  /-- `AND`/`BIC`/`ORR`/`ORN`/`EOR`/`EON`/`ANDS`/`BICS` (shifted register; `n` inverts). -/
  | logShift (sf : Bool) (opc : BitVec 2) (shift : BitVec 2) (n : Bool) (rm : Reg)
      (imm6 : BitVec 6) (rn rd : Reg)
  /-- `ADD`/`ADDS`/`SUB`/`SUBS` (shifted register). -/
  | addSubShift (sf sub setf : Bool) (shift : BitVec 2) (rm : Reg) (imm6 : BitVec 6) (rn rd : Reg)
  /-- `ADD`/`ADDS`/`SUB`/`SUBS` (extended register). -/
  | addSubExt (sf sub setf : Bool) (rm : Reg) (option : BitVec 3) (imm3 : BitVec 3) (rn rd : Reg)
  /-- `ADC`/`ADCS`/`SBC`/`SBCS`. -/
  | addSubCarry (sf sub setf : Bool) (rm rn rd : Reg)
  /-- `CCMN` (`sub = false`)/`CCMP`, register (`imm = false`, `rm` a register) or immediate. -/
  | condCmp (sf sub imm : Bool) (rm : BitVec 5) (cond : BitVec 4) (rn : Reg) (nzcv : BitVec 4)
  /-- `CSEL` (op 0, op2 0), `CSINC` (0, 1), `CSINV` (1, 0), `CSNEG` (1, 1). -/
  | condSel (sf op op2 : Bool) (rm : Reg) (cond : BitVec 4) (rn rd : Reg)
  /-- Data-processing (1 source): opcode 0 `RBIT`, 1 `REV16`, 2 `REV`(W)/`REV32`(X),
  3 `REV` (X), 4 `CLZ`, 5 `CLS`. -/
  | dp1 (sf : Bool) (opc : BitVec 3) (rn rd : Reg)
  /-- Data-processing (2 source): opcode 2 `UDIV`, 3 `SDIV`, 8 `LSLV`, 9 `LSRV`, 10 `ASRV`,
  11 `RORV`. -/
  | dp2 (sf : Bool) (opc : BitVec 6) (rm rn rd : Reg)
  /-- Data-processing (3 source): `op31` 000 `MADD`/`MSUB` (`o0`), 001 `SMADDL`/`SMSUBL`,
  010 `SMULH`, 101 `UMADDL`/`UMSUBL`, 110 `UMULH`. -/
  | dp3 (sf : Bool) (op31 : BitVec 3) (o0 : Bool) (rm ra rn rd : Reg)
  /-- Single-register load/store (`LDR*`/`STR*`/`LDUR*`/`STUR*`/`PRFM`), integer or SIMD&FP
  (`vec`). `size` and `opc` as encoded. -/
  | ldst (size : BitVec 2) (vec : Bool) (opc : BitVec 2) (mode : AMode) (rn rt : Reg)
  /-- `LDP`/`STP`/`LDPSW` and the SIMD&FP pairs; `mode` 01 post-index, 10 offset, 11 pre-index. -/
  | ldstPair (opc : BitVec 2) (vec : Bool) (mode : BitVec 2) (load : Bool) (imm7 : BitVec 7)
      (rt2 rn rt : Reg)
  /-- `LDR` (literal), `LDRSW` (literal), `PRFM` (literal). -/
  | ldrLit (opc : BitVec 2) (vec : Bool) (imm19 : BitVec 19) (rt : Reg)
  /-- Load/store exclusive and ordered: `LDAXR`/`STLXR`/`LDAR`/`STLR` and their `B`/`H`/`W`
  sizes (`o2` = ordered, `load`, `o1` = pair, must be 0, `o0` = acquire/release). -/
  | ldstExcl (size : BitVec 2) (o2 load o0 : Bool) (rs : Reg) (rn rt : Reg)
  /-- `CAS`/`CASA`/`CASL`/`CASAL` (`acq` = L, `rel` = o0). -/
  | cas (size : BitVec 2) (acq rel : Bool) (rs rn rt : Reg)
  /-- LSE atomic memory operations: `LDADD` (o3 0, opc 000), `LDCLR` (001), `LDEOR` (010),
  `LDSET` (011), `SWP` (o3 1, opc 000), with acquire `a` and release `r`. -/
  | atomic (size : BitVec 2) (a r : Bool) (rs : Reg) (o3 : Bool) (opc : BitVec 3) (rn rt : Reg)
  /-- Floating-point data-processing (1 source); `ftype` 00 single, 01 double. -/
  | fp1 (ftype : BitVec 2) (opc : BitVec 6) (rn rd : Reg)
  /-- Floating-point data-processing (2 source): 0 `FMUL`, 1 `FDIV`, 2 `FADD`, 3 `FSUB`,
  4 `FMAX`, 5 `FMIN`, 8 `FNMUL`. -/
  | fp2 (ftype : BitVec 2) (opc : BitVec 4) (rm rn rd : Reg)
  /-- `FMADD`/`FMSUB`/`FNMADD`/`FNMSUB` (`o1`, `o0`). -/
  | fp3 (ftype : BitVec 2) (o1 o0 : Bool) (rm ra rn rd : Reg)
  /-- `FCMP`/`FCMPE` (`e`), with zero (`zero`: `Rm` is 0). -/
  | fcmp (ftype : BitVec 2) (rm rn : Reg) (zero e : Bool)
  /-- `FMOV` (scalar, immediate). -/
  | fmovImm (ftype : BitVec 2) (imm8 : BitVec 8) (rd : Reg)
  /-- `FCSEL`. -/
  | fcsel (ftype : BitVec 2) (rm : Reg) (cond : BitVec 4) (rn rd : Reg)
  /-- Conversion between floating-point and integer: (`rmode`, `opc`) (00, 010) `SCVTF`,
  (00, 011) `UCVTF`, (11, 000) `FCVTZS`, (11, 001) `FCVTZU`, (00, 110) `FMOV` to general,
  (00, 111) `FMOV` from general. -/
  | fcvtInt (sf : Bool) (ftype : BitVec 2) (rmode : BitVec 2) (opc : BitVec 3) (rn rd : Reg)
  /-- `CNT Vd.8B, Vn.8B`. -/
  | cnt8b (rn rd : Reg)
  /-- `UADDLV Hd, Vn.8B`. -/
  | uaddlv8b (rn rd : Reg)
  deriving DecidableEq, Repr, Inhabited

namespace Insn

/-- The size letter of an integer access. -/
private def sz : BitVec 2 → String
  | 0 => "B" | 1 => "H" | 2 => "W" | _ => "X"

private def wx (sf : Bool) : String := if sf then "X" else "W"

private def ftyName (t : BitVec 2) : String := if t = 0 then "S" else "D"

/-- The form of an instruction: the mnemonic with the operand shape and width, ignoring
registers and immediates. Co-simulation coverage is counted per form. -/
def form : Insn → String
  | .adr page .. => if page then "ADRP" else "ADR"
  | .addSubImm sf sub setf _ .. =>
    s!"{if sub then "SUB" else "ADD"}{if setf then "S" else ""} imm {wx sf}"
  | .logImm sf opc .. =>
    s!"{#["AND", "ORR", "EOR", "ANDS"][opc.toNat]!} imm {wx sf}"
  | .movWide sf opc .. => s!"{#["MOVN", "?", "MOVZ", "MOVK"][opc.toNat]!} {wx sf}"
  | .bitfield sf opc .. => s!"{#["SBFM", "BFM", "UBFM", "?"][opc.toNat]!} {wx sf}"
  | .extr sf .. => s!"EXTR {wx sf}"
  | .b link _ => if link then "BL" else "B"
  | .bcond .. => "B.cond"
  | .cbz sf nz .. => s!"{if nz then "CBNZ" else "CBZ"} {wx sf}"
  | .tbz nz .. => if nz then "TBNZ" else "TBZ"
  | .br k _ => match k with | .br => "BR" | .blr => "BLR" | .ret => "RET"
  | .nop => "NOP"
  | .barrier op2 _ => s!"barrier {op2.toNat}"
  | .brk .. => "BRK"
  | .udf .. => "UDF"
  | .logShift sf opc _ n .. =>
    let base := #["AND", "ORR", "EOR", "ANDS"][opc.toNat]!
    s!"{base}{if n then "N" else ""} shifted {wx sf}"
  | .addSubShift sf sub setf .. =>
    s!"{if sub then "SUB" else "ADD"}{if setf then "S" else ""} shifted {wx sf}"
  | .addSubExt sf sub setf .. =>
    s!"{if sub then "SUB" else "ADD"}{if setf then "S" else ""} extended {wx sf}"
  | .addSubCarry sf sub setf .. =>
    s!"{if sub then "SBC" else "ADC"}{if setf then "S" else ""} {wx sf}"
  | .condCmp sf sub imm .. =>
    s!"{if sub then "CCMP" else "CCMN"} {if imm then "imm" else "reg"} {wx sf}"
  | .condSel sf op op2 .. =>
    s!"{#["CSEL", "CSINC", "CSINV", "CSNEG"][2 * op.toNat + op2.toNat]!} {wx sf}"
  | .dp1 sf opc .. => s!"{#["RBIT", "REV16", "REV32", "REV", "CLZ", "CLS", "?", "?"][opc.toNat]!} {wx sf}"
  | .dp2 sf opc .. =>
    let n := match opc.toNat with
      | 2 => "UDIV" | 3 => "SDIV" | 8 => "LSLV" | 9 => "LSRV" | 10 => "ASRV" | 11 => "RORV"
      | _ => "?"
    s!"{n} {wx sf}"
  | .dp3 sf op31 o0 .. =>
    let n := match op31.toNat, o0 with
      | 0, false => "MADD" | 0, true => "MSUB" | 1, false => "SMADDL" | 1, true => "SMSUBL"
      | 2, _ => "SMULH" | 5, false => "UMADDL" | 5, true => "UMSUBL" | 6, _ => "UMULH"
      | _, _ => "?"
    s!"{n} {wx sf}"
  | .ldst size vec opc mode .. =>
    let m := match mode with
      | .uimm _ => "uimm" | .reg .. => "reg"
      | .simm _ .unscaled => "unscaled" | .simm _ .post => "post" | .simm _ .pre => "pre"
    let what :=
      if vec then
        let n := if size = 0 && opc.getLsbD 1 then "Q" else #["B", "H", "S", "D"][size.toNat]!
        s!"{if opc.getLsbD 0 then "LDR" else "STR"} {n}"
      else if size = 3 && opc = 2 then "PRFM"
      else match opc.toNat with
        | 0 => s!"STR {sz size}" | 1 => s!"LDR {sz size}"
        | 2 => s!"LDRS {sz size} X" | _ => s!"LDRS {sz size} W"
    s!"{what} {m}"
  | .ldstPair opc vec mode load .. =>
    let n := if vec then #["S", "D", "Q", "?"][opc.toNat]!
      else #["W", "SW", "X", "?"][opc.toNat]!
    let m := match mode.toNat with | 1 => "post" | 2 => "off" | 3 => "pre" | _ => "?"
    s!"{if load then "LDP" else "STP"} {n} {m}"
  | .ldrLit opc vec .. => s!"LDR literal {opc.toNat}{if vec then " V" else ""}"
  | .ldstExcl size o2 load o0 .. =>
    let n := match o2, load with
      | false, true => "LDXR" | false, false => "STXR" | true, true => "LDAR" | true, false => "STLR"
    s!"{n}{if o0 then " o0" else ""} {sz size}"
  | .cas size acq rel .. => s!"CAS{if acq then "A" else ""}{if rel then "L" else ""} {sz size}"
  | .atomic size a r _ o3 opc .. =>
    let n := if o3 then "SWP" else #["LDADD", "LDCLR", "LDEOR", "LDSET", "?", "?", "?", "?"][opc.toNat]!
    s!"{n}{if a then "A" else ""}{if r then "L" else ""} {sz size}"
  | .fp1 t opc .. =>
    let n := match opc.toNat with
      | 0 => "FMOV" | 1 => "FABS" | 2 => "FNEG" | 3 => "FSQRT" | 4 => "FCVT to S"
      | 5 => "FCVT to D" | 8 => "FRINTN" | 9 => "FRINTP" | 10 => "FRINTM" | 11 => "FRINTZ"
      | 12 => "FRINTA" | 14 => "FRINTX" | 15 => "FRINTI" | _ => "?"
    s!"{n} {ftyName t}"
  | .fp2 t opc .. =>
    s!"{#["FMUL", "FDIV", "FADD", "FSUB", "FMAX", "FMIN", "FMAXNM", "FMINNM", "FNMUL"].getD opc.toNat "?"} {ftyName t}"
  | .fp3 t o1 o0 .. =>
    s!"{#["FMADD", "FMSUB", "FNMADD", "FNMSUB"][2 * o1.toNat + o0.toNat]!} {ftyName t}"
  | .fcmp t _ _ zero e => s!"FCMP{if e then "E" else ""}{if zero then " zero" else ""} {ftyName t}"
  | .fmovImm t .. => s!"FMOV imm {ftyName t}"
  | .fcsel t .. => s!"FCSEL {ftyName t}"
  | .fcvtInt sf t rmode opc .. =>
    match rmode.toNat, opc.toNat with
    | 0, 2 => s!"SCVTF {ftyName t} from {wx sf}"
    | 0, 3 => s!"UCVTF {ftyName t} from {wx sf}"
    | 3, 0 => s!"FCVTZS {wx sf} from {ftyName t}"
    | 3, 1 => s!"FCVTZU {wx sf} from {ftyName t}"
    | 0, 6 => s!"FMOV {wx sf} from {ftyName t}"
    | 0, 7 => s!"FMOV {ftyName t} from {wx sf}"
    | r, o => s!"fcvt {r}/{o} {wx sf} {ftyName t}"
  | .cnt8b .. => "CNT 8B"
  | .uaddlv8b .. => "UADDLV 8B"

end Insn

end GoFV.Arm64
