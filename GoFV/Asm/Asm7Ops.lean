import GoFV.Asm.Aclass

/-!
# `asmout`'s encoding helpers (`asm7.go`; `docs/PASSES3.md` D5)

The helpers the `asmout` cases (`GoFV.Asm.AsmoutA`, `GoFV.Asm.AsmoutB`) call, ported literally
with Go's names and argument order (receiver `c` dropped). Register arguments are obj register
numbers (`Int`, Go `int16`), machine words `UInt32` (Go's wrapping `uint32` arithmetic), Go
`int32`/`int64` values `Int` (callers pass values already in range, as Go's types guarantee).
`ctxt.Diag` is a `throw` whose message starts with the function name. `p` is the Prog (`Prog`)
where Go only prints it in diagnostics, its ID (`Nat`) where Go reads it.

## Signatures (namespace `GoFV.Asm`)

Go conversions (truncating, two's complement):
- `Go.u32 (x : Int) : UInt32` — `uint32(x)`
- `Go.u64 (x : Int) : UInt64` — `uint64(x)`
- `Go.i32 (x : Int) : Int` — `int32(x)`
- `Go.i16 (x : Int) : Int` — `int16(x)`
- `Go.i64 (x : Int) : Int` — `int64(x)`

Constants `asm7.go:204-210` as words (the generated `ARM64.S64` … are `Int`):
- `W.S32 W.S64 W.Sbit W.LSL0_32 W.LSL0_64 : UInt32`

Encoding macros `asm7.go:212-307`:
- `OPDP2 (x : UInt32) : UInt32`
- `OPDP3 (sf op54 op31 o0 : UInt32) : UInt32`
- `OPBcc (x : UInt32) : UInt32`
- `OPBLR (x : UInt32) : UInt32`
- `SYSOP (l op0 op1 crn crm op2 rt : UInt32) : UInt32`
- `SYSHINT (x : UInt32) : UInt32`
- `LDSTR (sz v opc : UInt32) : UInt32`
- `LD2STR (o : UInt32) : UInt32`
- `LDSTX (sz o2 l o1 o0 : UInt32) : UInt32`
- `FPCMP (m s type_ op op2 : UInt32) : UInt32`
- `FPCCMP (m s type_ op : UInt32) : UInt32`
- `FPOP1S (m s type_ op : UInt32) : UInt32`
- `FPOP2S (m s type_ op : UInt32) : UInt32`
- `FPOP3S (m s type_ op op2 : UInt32) : UInt32`
- `FPCVTI (sf s type_ rmode op : UInt32) : UInt32`
- `ADR (p o rt : UInt32) : UInt32`
- `OPBIT (x : UInt32) : UInt32`
- `MOVCONST (d : Int) (s : Int) (rt : Int) : UInt32` — `d` int64, `s`/`rt` int
- `ASIMDALL (u size opcode : UInt32) : UInt32`
- `ASIMDDIFF (u opcode : UInt32) : UInt32`
- `ASIMDMISC (u size opcode : UInt32) : UInt32`
- `ASIMDPERM (opcode : UInt32) : UInt32`
- `ASIMDSAME (u size opcode : UInt32) : UInt32`
- `ASIMDSHF (u opcode : UInt32) : UInt32`

Checks `asm7.go:3502-3614`:
- `SYSARG5 (op0 op1 Cn Cm op2 : Int) : Int`
- `SYSARG4 (op1 Cn Cm op2 : Int) : Int`
- `checkUnpredictable (p : Prog) (isload wback : Bool) (rn rt1 rt2 : Int) : AsmM Unit`
- `checkindex (p : Prog) (index maxindex : Int) : AsmM Unit`
- `checkoffset (p : Nat) (as : As) : AsmM Unit`
- `checkShiftAmount (p : Nat) (a : Addr) : AsmM Unit`

Encoders and operand helpers `asm7.go:6219-8549`:
- `addrRelocType (p : Nat) : AsmM String` — the `objabi.RelocType` name (`"R_ARM64_PCREL_LDST64"` …)
- `oprrr (p : Prog) (a : As) (rd rn rm : Int) : AsmM UInt32`
- `oprrrr (p : Prog) (a : As) (rd rn rm ra : Int) : AsmM UInt32`
- `opirr (p : Prog) (a : As) : AsmM UInt32`
- `opbit (p : Prog) (a : As) : AsmM UInt32`
- `opxrrr (p : Prog) (a : As) (rd rn rm : Int) (extend : Bool) : AsmM UInt32`
- `opimm (p : Prog) (a : As) : AsmM UInt32`
- `brdist (p : Nat) (preshift flen shift : Int) : AsmM Int` — the `int64` result
- `opbra (p : Prog) (a : As) : AsmM UInt32`
- `opbrr (p : Prog) (a : As) : AsmM UInt32`
- `op0 (p : Prog) (a : As) : AsmM UInt32`
- `opload (p : Prog) (a : As) : AsmM UInt32`
- `opstore (p : Prog) (a : As) : AsmM UInt32`
- `olsr12u (p : Prog) (o : UInt32) (v : Int) (rn rt : Int) : AsmM UInt32` — `v` int32
- `olsr9s (p : Prog) (o : UInt32) (v : Int) (rn rt : Int) : AsmM UInt32` — `v` int32
- `opstr (p : Nat) (a : As) : AsmM UInt32`
- `opldr (p : Prog) (a : As) : AsmM UInt32`
- `opldrr (p : Prog) (a : As) (rt rn rm : Int) (extension : Bool) : AsmM UInt32`
- `opstrr (p : Prog) (a : As) (rt rn rm : Int) (extension : Bool) : AsmM UInt32`
- `oaddi (p : Prog) (a : As) (v : Int) (rd rn : Int) : AsmM UInt32` — `v` int32
- `oaddi12 (p : Prog) (v : Int) (rd rn : Int) : AsmM UInt32` — `v` int32
- `omovlit (as : As) (p : Nat) (a : Addr) (dr : Int) : AsmM UInt32`
- `omovconst (as : As) (p : Prog) (a : Addr) (rt : Int) : AsmM UInt32`
- `omovlconst (as : As) (p : Prog) (a : Addr) (rt : Int) (os : Array UInt32) : AsmM (Nat × Array UInt32)`
  — Go's `num` and the caller's `os` slice after the writes (`os` must have ≥ 4 entries)
- `opbfm (p : Prog) (a : As) (r s : Int) (rf rt : Int) : AsmM UInt32` — `r`/`s` int64
- `opextr (p : Prog) (a : As) (v : Int) (rn rm rt : Int) : AsmM UInt32` — `v` int64
- `opldpstp (p : Nat) (o : ARM64.Optab) (vo : Int) (rbase rl rh : Int) (ldp : UInt32) : AsmM UInt32`
- `maskOpvldvst (p : Nat) (o1 : UInt32) : AsmM UInt32`
- `roff (rm : Int) (o : UInt32) (amount : Int) : UInt32`
- `encRegShiftOrExt (p : Nat) (a : Addr) (r : Int) : AsmM UInt32`
- `pack (q : UInt32) (arngA arngB : Nat) : UInt32` — `arngA`/`arngB` uint8

`movesize` is `GoFV.Asm.Aclass`'s.
-/

namespace GoFV.Asm

open AsmM ARM64

/-- Shifts elaborate like `|||` and `&&&` (`binop%`), so that a literal shifted into a word is a
word: `0xd6 <<< 21 : UInt32` as in Go's untyped constant expressions. -/
local macro_rules | `($x <<< $y) => `(binop% HShiftLeft.hShiftLeft $x $y)

/-! ## Go integer conversions -/

namespace Go

/-- `uint32(x)`: `x` truncated to 32 bits. -/
def u32 (x : Int) : UInt32 := UInt32.ofNat (x % 4294967296).toNat

/-- `uint64(x)`: `x` truncated to 64 bits. -/
def u64 (x : Int) : UInt64 := UInt64.ofNat (x % 18446744073709551616).toNat

/-- `int32(x)`: `x` truncated to 32 bits, two's complement. -/
def i32 (x : Int) : Int := x.bmod 4294967296

/-- `int16(x)`: `x` truncated to 16 bits, two's complement. -/
def i16 (x : Int) : Int := x.bmod 65536

/-- `int64(x)`: `x` truncated to 64 bits, two's complement. -/
def i64 (x : Int) : Int := x.bmod 18446744073709551616

/-- `x & m` for a signed Go integer `x` (at most 64 bits) and a non-negative mask `m`. -/
def andN (x : Int) (m : Nat) : Int := Int.ofNat ((u64 x).toNat &&& m)

/-- `bits.RotateLeft64(x, k)` for `k ≥ 0`. -/
def rotateLeft64 (x : UInt64) (k : Nat) : UInt64 :=
  let s := k % 64
  if s == 0 then x else (x <<< s.toUInt64) ||| (x >>> (64 - s).toUInt64)

end Go

/-! ## Constants and encoding macros (`asm7.go:204-307`) -/

namespace W
/-- `S32` (`asm7.go:205`). -/
def S32 : UInt32 := 0 <<< 31
/-- `S64` (`asm7.go:206`). -/
def S64 : UInt32 := 1 <<< 31
/-- `Sbit` (`asm7.go:207`). -/
def Sbit : UInt32 := 1 <<< 29
/-- `LSL0_32` (`asm7.go:208`). -/
def LSL0_32 : UInt32 := 2 <<< 13
/-- `LSL0_64` (`asm7.go:209`). -/
def LSL0_64 : UInt32 := 3 <<< 13
end W

/-- `OPDP2` (`asm7.go:212-214`). -/
def OPDP2 (x : UInt32) : UInt32 := 0 <<< 30 ||| 0 <<< 29 ||| 0xd6 <<< 21 ||| x <<< 10

/-- `OPDP3` (`asm7.go:216-218`). -/
def OPDP3 (sf op54 op31 o0 : UInt32) : UInt32 :=
  sf <<< 31 ||| op54 <<< 29 ||| 0x1B <<< 24 ||| op31 <<< 21 ||| o0 <<< 15

/-- `OPBcc` (`asm7.go:220-222`). -/
def OPBcc (x : UInt32) : UInt32 := 0x2A <<< 25 ||| 0 <<< 24 ||| 0 <<< 4 ||| x &&& 15

/-- `OPBLR` (`asm7.go:224-227`): `x` = 0 JMP, 1 CALL, 2 RET. -/
def OPBLR (x : UInt32) : UInt32 := 0x6B <<< 25 ||| 0 <<< 23 ||| x <<< 21 ||| 0x1F <<< 16 ||| 0 <<< 10

/-- `SYSOP` (`asm7.go:229-231`). -/
def SYSOP (l op0 op1 crn crm op2 rt : UInt32) : UInt32 :=
  0x354 <<< 22 ||| l <<< 21 ||| op0 <<< 19 ||| op1 <<< 16 ||| (crn &&& 15) <<< 12
    ||| (crm &&& 15) <<< 8 ||| op2 <<< 5 ||| rt

/-- `SYSHINT` (`asm7.go:233-235`). -/
def SYSHINT (x : UInt32) : UInt32 := SYSOP 0 0 3 2 0 x 0x1F

/-- `LDSTR` (`asm7.go:237-239`). -/
def LDSTR (sz v opc : UInt32) : UInt32 := sz <<< 30 ||| 7 <<< 27 ||| v <<< 26 ||| opc <<< 22

/-- `LD2STR` (`asm7.go:241-243`). -/
def LD2STR (o : UInt32) : UInt32 := o &&& ~~~(3 <<< 22)

/-- `LDSTX` (`asm7.go:245-247`). -/
def LDSTX (sz o2 l o1 o0 : UInt32) : UInt32 :=
  sz <<< 30 ||| 0x8 <<< 24 ||| o2 <<< 23 ||| l <<< 22 ||| o1 <<< 21 ||| o0 <<< 15

/-- `FPCMP` (`asm7.go:249-251`). -/
def FPCMP (m s type_ op op2 : UInt32) : UInt32 :=
  m <<< 31 ||| s <<< 29 ||| 0x1E <<< 24 ||| type_ <<< 22 ||| 1 <<< 21 ||| op <<< 14 ||| 8 <<< 10
    ||| op2

/-- `FPCCMP` (`asm7.go:253-255`). -/
def FPCCMP (m s type_ op : UInt32) : UInt32 :=
  m <<< 31 ||| s <<< 29 ||| 0x1E <<< 24 ||| type_ <<< 22 ||| 1 <<< 21 ||| 1 <<< 10 ||| op <<< 4

/-- `FPOP1S` (`asm7.go:257-259`). -/
def FPOP1S (m s type_ op : UInt32) : UInt32 :=
  m <<< 31 ||| s <<< 29 ||| 0x1E <<< 24 ||| type_ <<< 22 ||| 1 <<< 21 ||| op <<< 15 ||| 0x10 <<< 10

/-- `FPOP2S` (`asm7.go:261-263`). -/
def FPOP2S (m s type_ op : UInt32) : UInt32 :=
  m <<< 31 ||| s <<< 29 ||| 0x1E <<< 24 ||| type_ <<< 22 ||| 1 <<< 21 ||| op <<< 12 ||| 2 <<< 10

/-- `FPOP3S` (`asm7.go:265-267`). -/
def FPOP3S (m s type_ op op2 : UInt32) : UInt32 :=
  m <<< 31 ||| s <<< 29 ||| 0x1F <<< 24 ||| type_ <<< 22 ||| op <<< 21 ||| op2 <<< 15

/-- `FPCVTI` (`asm7.go:269-271`). -/
def FPCVTI (sf s type_ rmode op : UInt32) : UInt32 :=
  sf <<< 31 ||| s <<< 29 ||| 0x1E <<< 24 ||| type_ <<< 22 ||| 1 <<< 21 ||| rmode <<< 19
    ||| op <<< 16 ||| 0 <<< 10

/-- `ADR` (`asm7.go:273-275`). -/
def ADR (p o rt : UInt32) : UInt32 :=
  p <<< 31 ||| (o &&& 3) <<< 29 ||| 0x10 <<< 24 ||| ((o >>> (2 : UInt32)) &&& 0x7FFFF) <<< 5 ||| rt &&& 31

/-- `OPBIT` (`asm7.go:277-279`). -/
def OPBIT (x : UInt32) : UInt32 := 1 <<< 30 ||| 0 <<< 29 ||| 0xD6 <<< 21 ||| 0 <<< 16 ||| x <<< 10

/-- `MOVCONST(d int64, s int, rt int)` (`asm7.go:281-283`): `uint(s*16)` of a negative `s` is
a shift by at least 64. -/
def MOVCONST (d : Int) (s : Int) (rt : Int) : UInt32 :=
  let sh : Nat := if s * 16 < 0 then 64 else (s * 16).toNat
  Go.u32 (Go.andN (Go.i64 d >>> sh) 0xFFFF * 32) ||| (Go.u32 s &&& 3) <<< 21 ||| Go.u32 (Go.andN rt 31)

/-- `ASIMDALL` (`asm7.go:285-287`). -/
def ASIMDALL (u size opcode : UInt32) : UInt32 :=
  u <<< 29 ||| 0x7 <<< 25 ||| size <<< 22 ||| 3 <<< 20 ||| opcode <<< 12 ||| 1 <<< 11

/-- `ASIMDDIFF` (`asm7.go:289-291`). -/
def ASIMDDIFF (u opcode : UInt32) : UInt32 := u <<< 29 ||| 0x7 <<< 25 ||| 1 <<< 21 ||| opcode <<< 12

/-- `ASIMDMISC` (`asm7.go:293-295`). -/
def ASIMDMISC (u size opcode : UInt32) : UInt32 :=
  u <<< 29 ||| 0x7 <<< 25 ||| size <<< 22 ||| 1 <<< 21 ||| opcode <<< 12 ||| 1 <<< 11

/-- `ASIMDPERM` (`asm7.go:297-299`). -/
def ASIMDPERM (opcode : UInt32) : UInt32 := 0x7 <<< 25 ||| opcode <<< 12 ||| 1 <<< 11

/-- `ASIMDSAME` (`asm7.go:301-303`). -/
def ASIMDSAME (u size opcode : UInt32) : UInt32 :=
  u <<< 29 ||| 0x7 <<< 25 ||| size <<< 22 ||| 1 <<< 21 ||| opcode <<< 11 ||| 1 <<< 10

/-- `ASIMDSHF` (`asm7.go:305-307`). -/
def ASIMDSHF (u opcode : UInt32) : UInt32 := u <<< 29 ||| 0xF <<< 24 ||| opcode <<< 11 ||| 1 <<< 10

/-! ## Operand checks (`asm7.go:3502-3614`) -/

/-- `SYSARG5` (`asm7.go:3502-3504`), Go `int` arithmetic. -/
def SYSARG5 (op0 op1 Cn Cm op2 : Int) : Int :=
  Go.i64 (Go.u64 op0 <<< 19 ||| Go.u64 op1 <<< 16 ||| Go.u64 Cn <<< 12 ||| Go.u64 Cm <<< 8
    ||| Go.u64 op2 <<< 5).toNat

/-- `SYSARG4` (`asm7.go:3506-3508`). -/
def SYSARG4 (op1 Cn Cm op2 : Int) : Int := SYSARG5 0 op1 Cn Cm op2

/-- `ctxt7.checkUnpredictable` (`asm7.go:3512-3519`). -/
def checkUnpredictable (_p : Prog) (isload wback : Bool) (rn rt1 rt2 : Int) : AsmM Unit := do
  if wback && rn != REGSP && (rn == rt1 || rn == rt2) then
    throw "checkUnpredictable: constrained unpredictable behavior"
  if isload && rt1 == rt2 then
    throw "checkUnpredictable: constrained unpredictable behavior"

/-- `ctxt7.checkindex` (`asm7.go:3522-3526`). -/
def checkindex (_p : Prog) (index maxindex : Int) : AsmM Unit := do
  if index < 0 || index > maxindex then
    throw s!"checkindex: register element index out of range 0 to {maxindex}"

/-- `ctxt7.checkoffset` (`asm7.go:3529-3587`): the post-increment offset of `VLD[1-4].P` and
`VST[1-4].P`. -/
def checkoffset (p : Nat) (as : As) : AsmM Unit := do
  let pp ← getP p
  let (offset, list) ← match as with
    | .VLD1 | .VLD2 | .VLD3 | .VLD4 | .VLD1R | .VLD2R | .VLD3R | .VLD4R =>
      pure (pp.from_.offset, pp.to.offset)
    | .VST1 | .VST2 | .VST3 | .VST4 => pure (pp.to.offset, pp.from_.offset)
    | _ => throw s!"checkoffset: invalid operation on op {as.name}"
  let opcode := Go.andN (list >>> 12) 15
  let q := Go.andN (list >>> 30) 1
  let size := Go.andN (list >>> 10) 3
  if offset == 0 then return
  let n : Int ← match opcode with
    | 0x7 => pure 1
    | 0xa => pure 2
    | 0x6 => pure 3
    | 0x2 => pure 4
    | _ => throw "checkoffset: invalid register numbers in ARM64 register list"
  match as with
  | .VLD1R | .VLD2R | .VLD3R | .VLD4R =>
    if offset != n * 2 ^ size.toNat then throw "checkoffset: invalid post-increment offset"
  | _ =>
    if !(q == 0 && offset == n * 8) && !(q == 1 && offset == n * 16) then
      throw "checkoffset: invalid post-increment offset"
  match as with
  | .VLD1 | .VST1 => return
  | _ => pure ()
  let expect : Int := match as with
    | .VLD1R => 1
    | .VLD2 | .VST2 | .VLD2R => 2
    | .VLD3 | .VST3 | .VLD3R => 3
    | .VLD4 | .VST4 | .VLD4R => 4
    | _ => 0
  if expect != n then throw s!"checkoffset: expected {expect} registers, got {n}"

/-- `ctxt7.checkShiftAmount` (`asm7.go:3591-3614`): the index shift amount of a load with
register offset. -/
def checkShiftAmount (p : Nat) (a : Addr) : AsmM Unit := do
  let pp ← getP p
  let amount := Go.andN (Go.i16 a.index >>> 5) 7
  match pp.as with
  | .MOVB | .MOVBU =>
    if amount != 0 then throw "checkShiftAmount: invalid index shift amount"
  | .MOVH | .MOVHU =>
    if amount != 1 && amount != 0 then throw "checkShiftAmount: invalid index shift amount"
  | .MOVW | .MOVWU | .FMOVS =>
    if amount != 2 && amount != 0 then throw "checkShiftAmount: invalid index shift amount"
  | .MOVD | .FMOVD =>
    if amount != 3 && amount != 0 then throw "checkShiftAmount: invalid index shift amount"
  | _ => throw "checkShiftAmount: invalid operation"

/-! ## Opcode encoders (`asm7.go:6219-8549`) -/

/-- `ctxt7.addrRelocType` (`asm7.go:6219-6233`): the PC-relative load/store relocation of the
access size of `p.As` (`objabi.RelocType.String()`). -/
def addrRelocType (p : Nat) : AsmM String := do
  let pp ← getP p
  match movesize pp.as with
  | 0 => pure "R_ARM64_PCREL_LDST8"
  | 1 => pure "R_ARM64_PCREL_LDST16"
  | 2 => pure "R_ARM64_PCREL_LDST32"
  | 3 => pure "R_ARM64_PCREL_LDST64"
  | _ => throw s!"addrRelocType: use R_ADDRARM64 relocation type for: {pp.as.name}"

/-- `ctxt7.oprrr` (`asm7.go:6241-7136`): basic `Rm op Rn -> Rd` (shifted register with 0), also
`op Rn -> Rt`, `Rm*Rn op Ra -> Rd`, `Vm op Vn -> Vd`. -/
def oprrr (_p : Prog) (a : As) (rd rn rm : Int) : AsmM UInt32 := do
  let op ← match a with
    | .ADC => pure (W.S64 ||| 0 <<< 30 ||| 0 <<< 29 ||| 0xd0 <<< 21 ||| 0 <<< 10)
    | .ADCW => pure (W.S32 ||| 0 <<< 30 ||| 0 <<< 29 ||| 0xd0 <<< 21 ||| 0 <<< 10)
    | .ADCS => pure (W.S64 ||| 0 <<< 30 ||| 1 <<< 29 ||| 0xd0 <<< 21 ||| 0 <<< 10)
    | .ADCSW => pure (W.S32 ||| 0 <<< 30 ||| 1 <<< 29 ||| 0xd0 <<< 21 ||| 0 <<< 10)
    | .NGC | .SBC => pure (W.S64 ||| 1 <<< 30 ||| 0 <<< 29 ||| 0xd0 <<< 21 ||| 0 <<< 10)
    | .NGCS | .SBCS => pure (W.S64 ||| 1 <<< 30 ||| 1 <<< 29 ||| 0xd0 <<< 21 ||| 0 <<< 10)
    | .NGCW | .SBCW => pure (W.S32 ||| 1 <<< 30 ||| 0 <<< 29 ||| 0xd0 <<< 21 ||| 0 <<< 10)
    | .NGCSW | .SBCSW => pure (W.S32 ||| 1 <<< 30 ||| 1 <<< 29 ||| 0xd0 <<< 21 ||| 0 <<< 10)
    | .ADD => pure (W.S64 ||| 0 <<< 30 ||| 0 <<< 29 ||| 0x0b <<< 24 ||| 0 <<< 22 ||| 0 <<< 21 ||| 0 <<< 10)
    | .ADDW => pure (W.S32 ||| 0 <<< 30 ||| 0 <<< 29 ||| 0x0b <<< 24 ||| 0 <<< 22 ||| 0 <<< 21 ||| 0 <<< 10)
    | .CMN | .ADDS => pure (W.S64 ||| 0 <<< 30 ||| 1 <<< 29 ||| 0x0b <<< 24 ||| 0 <<< 22 ||| 0 <<< 21 ||| 0 <<< 10)
    | .CMNW | .ADDSW => pure (W.S32 ||| 0 <<< 30 ||| 1 <<< 29 ||| 0x0b <<< 24 ||| 0 <<< 22 ||| 0 <<< 21 ||| 0 <<< 10)
    | .SUB => pure (W.S64 ||| 1 <<< 30 ||| 0 <<< 29 ||| 0x0b <<< 24 ||| 0 <<< 22 ||| 0 <<< 21 ||| 0 <<< 10)
    | .SUBW => pure (W.S32 ||| 1 <<< 30 ||| 0 <<< 29 ||| 0x0b <<< 24 ||| 0 <<< 22 ||| 0 <<< 21 ||| 0 <<< 10)
    | .CMP | .SUBS => pure (W.S64 ||| 1 <<< 30 ||| 1 <<< 29 ||| 0x0b <<< 24 ||| 0 <<< 22 ||| 0 <<< 21 ||| 0 <<< 10)
    | .CMPW | .SUBSW => pure (W.S32 ||| 1 <<< 30 ||| 1 <<< 29 ||| 0x0b <<< 24 ||| 0 <<< 22 ||| 0 <<< 21 ||| 0 <<< 10)
    | .AND => pure (W.S64 ||| 0 <<< 29 ||| 0xA <<< 24)
    | .ANDW => pure (W.S32 ||| 0 <<< 29 ||| 0xA <<< 24)
    | .MOVD | .ORR => pure (W.S64 ||| 1 <<< 29 ||| 0xA <<< 24)
    | .MOVWU | .ORRW => pure (W.S32 ||| 1 <<< 29 ||| 0xA <<< 24)
    | .EOR => pure (W.S64 ||| 2 <<< 29 ||| 0xA <<< 24)
    | .EORW => pure (W.S32 ||| 2 <<< 29 ||| 0xA <<< 24)
    | .ANDS | .TST => pure (W.S64 ||| 3 <<< 29 ||| 0xA <<< 24)
    | .ANDSW | .TSTW => pure (W.S32 ||| 3 <<< 29 ||| 0xA <<< 24)
    | .BIC => pure (W.S64 ||| 0 <<< 29 ||| 0xA <<< 24 ||| 1 <<< 21)
    | .BICW => pure (W.S32 ||| 0 <<< 29 ||| 0xA <<< 24 ||| 1 <<< 21)
    | .BICS => pure (W.S64 ||| 3 <<< 29 ||| 0xA <<< 24 ||| 1 <<< 21)
    | .BICSW => pure (W.S32 ||| 3 <<< 29 ||| 0xA <<< 24 ||| 1 <<< 21)
    | .EON => pure (W.S64 ||| 2 <<< 29 ||| 0xA <<< 24 ||| 1 <<< 21)
    | .EONW => pure (W.S32 ||| 2 <<< 29 ||| 0xA <<< 24 ||| 1 <<< 21)
    | .MVN | .ORN => pure (W.S64 ||| 1 <<< 29 ||| 0xA <<< 24 ||| 1 <<< 21)
    | .MVNW | .ORNW => pure (W.S32 ||| 1 <<< 29 ||| 0xA <<< 24 ||| 1 <<< 21)
    | .ASR => pure (W.S64 ||| OPDP2 10)
    | .ASRW => pure (W.S32 ||| OPDP2 10)
    | .LSL => pure (W.S64 ||| OPDP2 8)
    | .LSLW => pure (W.S32 ||| OPDP2 8)
    | .LSR => pure (W.S64 ||| OPDP2 9)
    | .LSRW => pure (W.S32 ||| OPDP2 9)
    | .ROR => pure (W.S64 ||| OPDP2 11)
    | .RORW => pure (W.S32 ||| OPDP2 11)
    | .CCMN => pure (W.S64 ||| 0 <<< 30 ||| 1 <<< 29 ||| 0xD2 <<< 21 ||| 0 <<< 11 ||| 0 <<< 10 ||| 0 <<< 4)
    | .CCMNW => pure (W.S32 ||| 0 <<< 30 ||| 1 <<< 29 ||| 0xD2 <<< 21 ||| 0 <<< 11 ||| 0 <<< 10 ||| 0 <<< 4)
    | .CCMP => pure (W.S64 ||| 1 <<< 30 ||| 1 <<< 29 ||| 0xD2 <<< 21 ||| 0 <<< 11 ||| 0 <<< 10 ||| 0 <<< 4)
    | .CCMPW => pure (W.S32 ||| 1 <<< 30 ||| 1 <<< 29 ||| 0xD2 <<< 21 ||| 0 <<< 11 ||| 0 <<< 10 ||| 0 <<< 4)
    | .CRC32B => pure (W.S32 ||| OPDP2 16)
    | .CRC32H => pure (W.S32 ||| OPDP2 17)
    | .CRC32W => pure (W.S32 ||| OPDP2 18)
    | .CRC32X => pure (W.S64 ||| OPDP2 19)
    | .CRC32CB => pure (W.S32 ||| OPDP2 20)
    | .CRC32CH => pure (W.S32 ||| OPDP2 21)
    | .CRC32CW => pure (W.S32 ||| OPDP2 22)
    | .CRC32CX => pure (W.S64 ||| OPDP2 23)
    | .CSEL => pure (W.S64 ||| 0 <<< 30 ||| 0 <<< 29 ||| 0xD4 <<< 21 ||| 0 <<< 11 ||| 0 <<< 10)
    | .CSELW => pure (W.S32 ||| 0 <<< 30 ||| 0 <<< 29 ||| 0xD4 <<< 21 ||| 0 <<< 11 ||| 0 <<< 10)
    | .CSET => pure (W.S64 ||| 0 <<< 30 ||| 0 <<< 29 ||| 0xD4 <<< 21 ||| 0 <<< 11 ||| 1 <<< 10)
    | .CSETW => pure (W.S32 ||| 0 <<< 30 ||| 0 <<< 29 ||| 0xD4 <<< 21 ||| 0 <<< 11 ||| 1 <<< 10)
    | .CSETM => pure (W.S64 ||| 1 <<< 30 ||| 0 <<< 29 ||| 0xD4 <<< 21 ||| 0 <<< 11 ||| 0 <<< 10)
    | .CSETMW => pure (W.S32 ||| 1 <<< 30 ||| 0 <<< 29 ||| 0xD4 <<< 21 ||| 0 <<< 11 ||| 0 <<< 10)
    | .CINC | .CSINC => pure (W.S64 ||| 0 <<< 30 ||| 0 <<< 29 ||| 0xD4 <<< 21 ||| 0 <<< 11 ||| 1 <<< 10)
    | .CINCW | .CSINCW => pure (W.S32 ||| 0 <<< 30 ||| 0 <<< 29 ||| 0xD4 <<< 21 ||| 0 <<< 11 ||| 1 <<< 10)
    | .CINV | .CSINV => pure (W.S64 ||| 1 <<< 30 ||| 0 <<< 29 ||| 0xD4 <<< 21 ||| 0 <<< 11 ||| 0 <<< 10)
    | .CINVW | .CSINVW => pure (W.S32 ||| 1 <<< 30 ||| 0 <<< 29 ||| 0xD4 <<< 21 ||| 0 <<< 11 ||| 0 <<< 10)
    | .CNEG | .CSNEG => pure (W.S64 ||| 1 <<< 30 ||| 0 <<< 29 ||| 0xD4 <<< 21 ||| 0 <<< 11 ||| 1 <<< 10)
    | .CNEGW | .CSNEGW => pure (W.S32 ||| 1 <<< 30 ||| 0 <<< 29 ||| 0xD4 <<< 21 ||| 0 <<< 11 ||| 1 <<< 10)
    | .MUL | .MADD => pure (W.S64 ||| 0 <<< 29 ||| 0x1B <<< 24 ||| 0 <<< 21 ||| 0 <<< 15)
    | .MULW | .MADDW => pure (W.S32 ||| 0 <<< 29 ||| 0x1B <<< 24 ||| 0 <<< 21 ||| 0 <<< 15)
    | .MNEG | .MSUB => pure (W.S64 ||| 0 <<< 29 ||| 0x1B <<< 24 ||| 0 <<< 21 ||| 1 <<< 15)
    | .MNEGW | .MSUBW => pure (W.S32 ||| 0 <<< 29 ||| 0x1B <<< 24 ||| 0 <<< 21 ||| 1 <<< 15)
    | .MRS => pure (SYSOP 1 2 0 0 0 0 0)
    | .MSR => pure (SYSOP 0 2 0 0 0 0 0)
    | .NEG => pure (W.S64 ||| 1 <<< 30 ||| 0 <<< 29 ||| 0xB <<< 24 ||| 0 <<< 21)
    | .NEGW => pure (W.S32 ||| 1 <<< 30 ||| 0 <<< 29 ||| 0xB <<< 24 ||| 0 <<< 21)
    | .NEGS => pure (W.S64 ||| 1 <<< 30 ||| 1 <<< 29 ||| 0xB <<< 24 ||| 0 <<< 21)
    | .NEGSW => pure (W.S32 ||| 1 <<< 30 ||| 1 <<< 29 ||| 0xB <<< 24 ||| 0 <<< 21)
    | .REM | .SDIV => pure (W.S64 ||| OPDP2 3)
    | .REMW | .SDIVW => pure (W.S32 ||| OPDP2 3)
    | .SMULL | .SMADDL => pure (OPDP3 1 0 1 0)
    | .SMNEGL | .SMSUBL => pure (OPDP3 1 0 1 1)
    | .SMULH => pure (OPDP3 1 0 2 0)
    | .UMULL | .UMADDL => pure (OPDP3 1 0 5 0)
    | .UMNEGL | .UMSUBL => pure (OPDP3 1 0 5 1)
    | .UMULH => pure (OPDP3 1 0 6 0)
    | .UREM | .UDIV => pure (W.S64 ||| OPDP2 2)
    | .UREMW | .UDIVW => pure (W.S32 ||| OPDP2 2)
    | .AESE => pure (0x4E <<< 24 ||| 2 <<< 20 ||| 8 <<< 16 ||| 4 <<< 12 ||| 2 <<< 10)
    | .AESD => pure (0x4E <<< 24 ||| 2 <<< 20 ||| 8 <<< 16 ||| 5 <<< 12 ||| 2 <<< 10)
    | .AESMC => pure (0x4E <<< 24 ||| 2 <<< 20 ||| 8 <<< 16 ||| 6 <<< 12 ||| 2 <<< 10)
    | .AESIMC => pure (0x4E <<< 24 ||| 2 <<< 20 ||| 8 <<< 16 ||| 7 <<< 12 ||| 2 <<< 10)
    | .SHA1C => pure (0x5E <<< 24 ||| 0 <<< 12)
    | .SHA1P => pure (0x5E <<< 24 ||| 1 <<< 12)
    | .SHA1M => pure (0x5E <<< 24 ||| 2 <<< 12)
    | .SHA1SU0 => pure (0x5E <<< 24 ||| 3 <<< 12)
    | .SHA256H => pure (0x5E <<< 24 ||| 4 <<< 12)
    | .SHA256H2 => pure (0x5E <<< 24 ||| 5 <<< 12)
    | .SHA256SU1 => pure (0x5E <<< 24 ||| 6 <<< 12)
    | .SHA1H => pure (0x5E <<< 24 ||| 2 <<< 20 ||| 8 <<< 16 ||| 0 <<< 12 ||| 2 <<< 10)
    | .SHA1SU1 => pure (0x5E <<< 24 ||| 2 <<< 20 ||| 8 <<< 16 ||| 1 <<< 12 ||| 2 <<< 10)
    | .SHA256SU0 => pure (0x5E <<< 24 ||| 2 <<< 20 ||| 8 <<< 16 ||| 2 <<< 12 ||| 2 <<< 10)
    | .SHA512H => pure (0xCE <<< 24 ||| 3 <<< 21 ||| 8 <<< 12)
    | .SHA512H2 => pure (0xCE <<< 24 ||| 3 <<< 21 ||| 8 <<< 12 ||| 4 <<< 8)
    | .SHA512SU1 => pure (0xCE <<< 24 ||| 3 <<< 21 ||| 8 <<< 12 ||| 8 <<< 8)
    | .SHA512SU0 => pure (0xCE <<< 24 ||| 3 <<< 22 ||| 8 <<< 12)
    | .FCVTZSD => pure (FPCVTI 1 0 1 3 0)
    | .FCVTZSDW => pure (FPCVTI 0 0 1 3 0)
    | .FCVTZSS => pure (FPCVTI 1 0 0 3 0)
    | .FCVTZSSW => pure (FPCVTI 0 0 0 3 0)
    | .FCVTZUD => pure (FPCVTI 1 0 1 3 1)
    | .FCVTZUDW => pure (FPCVTI 0 0 1 3 1)
    | .FCVTZUS => pure (FPCVTI 1 0 0 3 1)
    | .FCVTZUSW => pure (FPCVTI 0 0 0 3 1)
    | .SCVTFD => pure (FPCVTI 1 0 1 0 2)
    | .SCVTFS => pure (FPCVTI 1 0 0 0 2)
    | .SCVTFWD => pure (FPCVTI 0 0 1 0 2)
    | .SCVTFWS => pure (FPCVTI 0 0 0 0 2)
    | .UCVTFD => pure (FPCVTI 1 0 1 0 3)
    | .UCVTFS => pure (FPCVTI 1 0 0 0 3)
    | .UCVTFWD => pure (FPCVTI 0 0 1 0 3)
    | .UCVTFWS => pure (FPCVTI 0 0 0 0 3)
    | .FADDS => pure (FPOP2S 0 0 0 2)
    | .FADDD => pure (FPOP2S 0 0 1 2)
    | .FSUBS => pure (FPOP2S 0 0 0 3)
    | .FSUBD => pure (FPOP2S 0 0 1 3)
    | .FMADDD => pure (FPOP3S 0 0 1 0 0)
    | .FMADDS => pure (FPOP3S 0 0 0 0 0)
    | .FMSUBD => pure (FPOP3S 0 0 1 0 1)
    | .FMSUBS => pure (FPOP3S 0 0 0 0 1)
    | .FNMADDD => pure (FPOP3S 0 0 1 1 0)
    | .FNMADDS => pure (FPOP3S 0 0 0 1 0)
    | .FNMSUBD => pure (FPOP3S 0 0 1 1 1)
    | .FNMSUBS => pure (FPOP3S 0 0 0 1 1)
    | .FMULS => pure (FPOP2S 0 0 0 0)
    | .FMULD => pure (FPOP2S 0 0 1 0)
    | .FDIVS => pure (FPOP2S 0 0 0 1)
    | .FDIVD => pure (FPOP2S 0 0 1 1)
    | .FMAXS => pure (FPOP2S 0 0 0 4)
    | .FMINS => pure (FPOP2S 0 0 0 5)
    | .FMAXD => pure (FPOP2S 0 0 1 4)
    | .FMIND => pure (FPOP2S 0 0 1 5)
    | .FMAXNMS => pure (FPOP2S 0 0 0 6)
    | .FMAXNMD => pure (FPOP2S 0 0 1 6)
    | .FMINNMS => pure (FPOP2S 0 0 0 7)
    | .FMINNMD => pure (FPOP2S 0 0 1 7)
    | .FNMULS => pure (FPOP2S 0 0 0 8)
    | .FNMULD => pure (FPOP2S 0 0 1 8)
    | .FCMPS => pure (FPCMP 0 0 0 0 0)
    | .FCMPD => pure (FPCMP 0 0 1 0 0)
    | .FCMPES => pure (FPCMP 0 0 0 0 16)
    | .FCMPED => pure (FPCMP 0 0 1 0 16)
    | .FCCMPS => pure (FPCCMP 0 0 0 0)
    | .FCCMPD => pure (FPCCMP 0 0 1 0)
    | .FCCMPES => pure (FPCCMP 0 0 0 1)
    | .FCCMPED => pure (FPCCMP 0 0 1 1)
    | .FCSELS => pure (0x1E <<< 24 ||| 0 <<< 22 ||| 1 <<< 21 ||| 3 <<< 10)
    | .FCSELD => pure (0x1E <<< 24 ||| 1 <<< 22 ||| 1 <<< 21 ||| 3 <<< 10)
    | .FMOVS => pure (FPOP1S 0 0 0 0)
    | .FABSS => pure (FPOP1S 0 0 0 1)
    | .FNEGS => pure (FPOP1S 0 0 0 2)
    | .FSQRTS => pure (FPOP1S 0 0 0 3)
    | .FCVTSD => pure (FPOP1S 0 0 0 5)
    | .FCVTSH => pure (FPOP1S 0 0 0 7)
    | .FRINTNS => pure (FPOP1S 0 0 0 8)
    | .FRINTPS => pure (FPOP1S 0 0 0 9)
    | .FRINTMS => pure (FPOP1S 0 0 0 10)
    | .FRINTZS => pure (FPOP1S 0 0 0 11)
    | .FRINTAS => pure (FPOP1S 0 0 0 12)
    | .FRINTXS => pure (FPOP1S 0 0 0 14)
    | .FRINTIS => pure (FPOP1S 0 0 0 15)
    | .FMOVD => pure (FPOP1S 0 0 1 0)
    | .FABSD => pure (FPOP1S 0 0 1 1)
    | .FNEGD => pure (FPOP1S 0 0 1 2)
    | .FSQRTD => pure (FPOP1S 0 0 1 3)
    | .FCVTDS => pure (FPOP1S 0 0 1 4)
    | .FCVTDH => pure (FPOP1S 0 0 1 7)
    | .FRINTND => pure (FPOP1S 0 0 1 8)
    | .FRINTPD => pure (FPOP1S 0 0 1 9)
    | .FRINTMD => pure (FPOP1S 0 0 1 10)
    | .FRINTZD => pure (FPOP1S 0 0 1 11)
    | .FRINTAD => pure (FPOP1S 0 0 1 12)
    | .FRINTXD => pure (FPOP1S 0 0 1 14)
    | .FRINTID => pure (FPOP1S 0 0 1 15)
    | .FCVTHS => pure (FPOP1S 0 0 3 4)
    | .FCVTHD => pure (FPOP1S 0 0 3 5)
    | .VADD => pure (ASIMDSAME 0 0 0x10)
    | .VSUB => pure (ASIMDSAME 1 0 0x10)
    | .VSHADD => pure (ASIMDSAME 0 0 0x0)
    | .VSRHADD => pure (ASIMDSAME 0 0 0x2)
    | .VSSHL => pure (ASIMDSAME 0 0 0x8)
    | .VUSHL => pure (ASIMDSAME 1 0 0x8)
    | .VUHADD => pure (ASIMDSAME 1 0 0x0)
    | .VURHADD => pure (ASIMDSAME 1 0 0x2)
    | .VADDP => pure (ASIMDSAME 0 0 0x17)
    | .VSQADD => pure (ASIMDSAME 0 0 0x1)
    | .VUQADD => pure (ASIMDSAME 1 0 0x1)
    | .VSQSHL => pure (ASIMDSAME 0 0 0x9)
    | .VUQSHL => pure (ASIMDSAME 1 0 0x9)
    | .VSQSUB => pure (ASIMDSAME 0 0 0x5)
    | .VUQSUB => pure (ASIMDSAME 1 0 0x5)
    | .VMUL => pure (ASIMDSAME 0 0 0x13)
    | .VMLA => pure (ASIMDSAME 0 0 0x12)
    | .VMLS => pure (ASIMDSAME 1 0 0x12)
    | .VAND => pure (ASIMDSAME 0 0 0x03)
    | .VBIC => pure (ASIMDSAME 0 1 0x03)
    | .VBCAX => pure (0xCE <<< 24 ||| 1 <<< 21)
    | .VCMEQ => pure (ASIMDSAME 1 0 0x11)
    | .VCMGE => pure (ASIMDSAME 0 0 0x07)
    | .VCMGT => pure (ASIMDSAME 0 0 0x06)
    | .VCMHI => pure (ASIMDSAME 1 0 0x06)
    | .VCMHS => pure (ASIMDSAME 1 0 0x07)
    | .VFCMEQ => pure (ASIMDSAME 0 0 0x1C)
    | .VFCMGE => pure (ASIMDSAME 1 0 0x1C)
    | .VFCMGT => pure (ASIMDSAME 1 2 0x1C)
    | .VCNT => pure (ASIMDMISC 0 0 0x05)
    | .VCLS => pure (ASIMDMISC 0 0 0x04)
    | .VCLZ => pure (ASIMDMISC 1 0 0x04)
    | .VZIP1 => pure (ASIMDPERM 0x3)
    | .VZIP2 => pure (ASIMDPERM 0x7)
    | .VEOR => pure (ASIMDSAME 1 0 0x03)
    | .VEOR3 => pure (0xCE <<< 24)
    | .VORR => pure (ASIMDSAME 0 2 0x03)
    | .VORN => pure (ASIMDSAME 0 3 0x03)
    | .VRAX1 => pure (0xCE <<< 24 ||| 3 <<< 21 ||| 1 <<< 15 ||| 3 <<< 10)
    | .VREV16 => pure (ASIMDMISC 0 0 0x01)
    | .VREV32 => pure (ASIMDMISC 1 0 0x00)
    | .VREV64 => pure (ASIMDMISC 0 0 0x00)
    | .VABS => pure (ASIMDMISC 0 0 0xB)
    | .VNEG => pure (ASIMDMISC 1 0 0xB)
    | .VFABS => pure (ASIMDMISC 0 2 0xF)
    | .VFNEG => pure (ASIMDMISC 1 2 0xF)
    | .VFSQRT => pure (ASIMDMISC 1 2 0x1F)
    | .VFRINTN => pure (ASIMDMISC 0 0 0x18)
    | .VFRINTP => pure (ASIMDMISC 0 2 0x18)
    | .VFRINTM => pure (ASIMDMISC 0 0 0x19)
    | .VFRINTZ => pure (ASIMDMISC 0 2 0x19)
    | .VFCVTZS => pure (ASIMDMISC 0 2 0x1B)
    | .VFCVTZU => pure (ASIMDMISC 1 2 0x1B)
    | .VSCVTF => pure (ASIMDMISC 0 0 0x1D)
    | .VUCVTF => pure (ASIMDMISC 1 0 0x1D)
    | .VSQABS => pure (ASIMDMISC 0 0 0x7)
    | .VSQNEG => pure (ASIMDMISC 1 0 0x7)
    | .VNOT => pure (ASIMDMISC 1 0 0x5)
    | .VMOV => pure (7 <<< 25 ||| 5 <<< 21 ||| 7 <<< 10)
    | .VADDV => pure (ASIMDALL 0 0 0x1B)
    | .VFMAXV => pure (ASIMDALL 1 0 0xF)
    | .VFMAXNMV => pure (ASIMDALL 1 0 0xC)
    | .VFMINV => pure (ASIMDALL 1 2 0xF)
    | .VFMINNMV => pure (ASIMDALL 1 2 0xC)
    | .VSMAXV => pure (ASIMDALL 0 0 0xA)
    | .VSMINV => pure (ASIMDALL 0 0 0x1A)
    | .VUMAXV => pure (ASIMDALL 1 0 0xA)
    | .VUMINV => pure (ASIMDALL 1 0 0x1A)
    | .VUADDLV => pure (ASIMDALL 1 0 0x03)
    | .VFMLA => pure (ASIMDSAME 0 0 0x19)
    | .VFMLS => pure (ASIMDSAME 0 2 0x19)
    | .VFADD => pure (ASIMDSAME 0 0 0x1A)
    | .VFSUB => pure (ASIMDSAME 0 2 0x1A)
    | .VFMUL => pure (ASIMDSAME 1 0 0x1B)
    | .VFDIV => pure (ASIMDSAME 1 0 0x1F)
    | .VFMAX => pure (ASIMDSAME 0 0 0x1E)
    | .VFMAXNM => pure (ASIMDSAME 0 0 0x18)
    | .VFMAXP => pure (ASIMDSAME 1 0 0x1E)
    | .VFADDP => pure (ASIMDSAME 1 0 0x1A)
    | .VFMIN => pure (ASIMDSAME 0 2 0x1E)
    | .VFMINNM => pure (ASIMDSAME 0 2 0x18)
    | .VFMINP => pure (ASIMDSAME 1 2 0x1E)
    | .VFMAXNMP => pure (ASIMDSAME 1 0 0x18)
    | .VFMINNMP => pure (ASIMDSAME 1 2 0x18)
    | .VPMULL | .VPMULL2 => pure (ASIMDDIFF 0 0xE)
    | .VSMLAL | .VSMLAL2 => pure (ASIMDDIFF 0 0x8)
    | .VSMLSL | .VSMLSL2 => pure (ASIMDDIFF 0 0xA)
    | .VSMULL | .VSMULL2 => pure (ASIMDDIFF 0 0xC)
    | .VUMLAL | .VUMLAL2 => pure (ASIMDDIFF 1 0x8)
    | .VUMLSL | .VUMLSL2 => pure (ASIMDDIFF 1 0xA)
    | .VUMULL | .VUMULL2 => pure (ASIMDDIFF 1 0xC)
    | .VRBIT => pure (ASIMDMISC 1 1 0x05)
    | .VLD1 | .VLD2 | .VLD3 | .VLD4 => pure (3 <<< 26 ||| 1 <<< 22)
    | .VLD1R | .VLD3R => pure (0xD <<< 24 ||| 1 <<< 22)
    | .VLD2R | .VLD4R => pure (0xD <<< 24 ||| 3 <<< 21)
    | .VBIF => pure (ASIMDSAME 1 3 0x03)
    | .VBIT => pure (ASIMDSAME 1 2 0x03)
    | .VBSL => pure (ASIMDSAME 1 1 0x03)
    | .VCMTST => pure (ASIMDSAME 0 0 0x11)
    | .VUMAX => pure (ASIMDSAME 1 0 0x0C)
    | .VUMIN => pure (ASIMDSAME 1 0 0x0D)
    | .VUMAXP => pure (ASIMDSAME 1 0 0x14)
    | .VUMINP => pure (ASIMDSAME 1 0 0x15)
    | .VSMAX => pure (ASIMDSAME 0 0 0x0C)
    | .VSMIN => pure (ASIMDSAME 0 0 0x0D)
    | .VSMAXP => pure (ASIMDSAME 0 0 0x14)
    | .VSMINP => pure (ASIMDSAME 0 0 0x15)
    | .VUZP1 => pure (ASIMDPERM 0x1)
    | .VUZP2 => pure (ASIMDPERM 0x5)
    | .VUADDW | .VUADDW2 => pure (ASIMDDIFF 1 0x1)
    | .VTRN1 => pure (ASIMDPERM 0x2)
    | .VTRN2 => pure (ASIMDPERM 0x6)
    | _ => throw s!"oprrr: bad rrr {a.goNum} {a.name}"
  return op ||| (Go.u32 rm &&& 0x1f) <<< 16 ||| (Go.u32 rn &&& 0x1f) <<< 5 ||| (Go.u32 rd &&& 0x1f)

/-- `ctxt7.oprrrr` (`asm7.go:7138-7140`). -/
def oprrrr (p : Prog) (a : As) (rd rn rm ra : Int) : AsmM UInt32 := do
  return (← oprrr p a rd rn rm) ||| (Go.u32 ra &&& 0x1f) <<< 10

/-- `ctxt7.opirr` (`asm7.go:7146-7422`): `imm -> Rd`, `imm op Rn -> Rd`. -/
def opirr (_p : Prog) (a : As) : AsmM UInt32 :=
  match a with
  | .MOVD | .ADD => pure (W.S64 ||| 0 <<< 30 ||| 0 <<< 29 ||| 0x11 <<< 24)
  | .CMN | .ADDS => pure (W.S64 ||| 0 <<< 30 ||| 1 <<< 29 ||| 0x11 <<< 24)
  | .MOVW | .ADDW => pure (W.S32 ||| 0 <<< 30 ||| 0 <<< 29 ||| 0x11 <<< 24)
  | .CMNW | .ADDSW => pure (W.S32 ||| 0 <<< 30 ||| 1 <<< 29 ||| 0x11 <<< 24)
  | .SUB => pure (W.S64 ||| 1 <<< 30 ||| 0 <<< 29 ||| 0x11 <<< 24)
  | .CMP | .SUBS => pure (W.S64 ||| 1 <<< 30 ||| 1 <<< 29 ||| 0x11 <<< 24)
  | .SUBW => pure (W.S32 ||| 1 <<< 30 ||| 0 <<< 29 ||| 0x11 <<< 24)
  | .CMPW | .SUBSW => pure (W.S32 ||| 1 <<< 30 ||| 1 <<< 29 ||| 0x11 <<< 24)
  | .ADR => pure (0 <<< 31 ||| 0x10 <<< 24)
  | .ADRP => pure (1 <<< 31 ||| 0x10 <<< 24)
  | .AND | .BIC => pure (W.S64 ||| 0 <<< 29 ||| 0x24 <<< 23)
  | .ANDW | .BICW => pure (W.S32 ||| 0 <<< 29 ||| 0x24 <<< 23 ||| 0 <<< 22)
  | .ORR | .ORN => pure (W.S64 ||| 1 <<< 29 ||| 0x24 <<< 23)
  | .ORRW | .ORNW => pure (W.S32 ||| 1 <<< 29 ||| 0x24 <<< 23 ||| 0 <<< 22)
  | .EOR | .EON => pure (W.S64 ||| 2 <<< 29 ||| 0x24 <<< 23)
  | .EORW | .EONW => pure (W.S32 ||| 2 <<< 29 ||| 0x24 <<< 23 ||| 0 <<< 22)
  | .ANDS | .BICS | .TST => pure (W.S64 ||| 3 <<< 29 ||| 0x24 <<< 23)
  | .ANDSW | .BICSW | .TSTW => pure (W.S32 ||| 3 <<< 29 ||| 0x24 <<< 23 ||| 0 <<< 22)
  | .ASR => pure (W.S64 ||| 0 <<< 29 ||| 0x26 <<< 23)
  | .ASRW => pure (W.S32 ||| 0 <<< 29 ||| 0x26 <<< 23 ||| 0 <<< 22)
  | .BFI => pure (W.S64 ||| 2 <<< 29 ||| 0x26 <<< 23 ||| 1 <<< 22)
  | .BFIW => pure (W.S32 ||| 2 <<< 29 ||| 0x26 <<< 23 ||| 0 <<< 22)
  | .BFM => pure (W.S64 ||| 1 <<< 29 ||| 0x26 <<< 23 ||| 1 <<< 22)
  | .BFMW => pure (W.S32 ||| 1 <<< 29 ||| 0x26 <<< 23 ||| 0 <<< 22)
  | .SBFM => pure (W.S64 ||| 0 <<< 29 ||| 0x26 <<< 23 ||| 1 <<< 22)
  | .SBFMW => pure (W.S32 ||| 0 <<< 29 ||| 0x26 <<< 23 ||| 0 <<< 22)
  | .UBFM => pure (W.S64 ||| 2 <<< 29 ||| 0x26 <<< 23 ||| 1 <<< 22)
  | .UBFMW => pure (W.S32 ||| 2 <<< 29 ||| 0x26 <<< 23 ||| 0 <<< 22)
  | .BFXIL => pure (W.S64 ||| 1 <<< 29 ||| 0x26 <<< 23 ||| 1 <<< 22)
  | .BFXILW => pure (W.S32 ||| 1 <<< 29 ||| 0x26 <<< 23 ||| 0 <<< 22)
  | .EXTR => pure (W.S64 ||| 0 <<< 29 ||| 0x27 <<< 23 ||| 1 <<< 22 ||| 0 <<< 21)
  | .EXTRW => pure (W.S32 ||| 0 <<< 29 ||| 0x27 <<< 23 ||| 0 <<< 22 ||| 0 <<< 21)
  | .CBNZ => pure (W.S64 ||| 0x1A <<< 25 ||| 1 <<< 24)
  | .CBNZW => pure (W.S32 ||| 0x1A <<< 25 ||| 1 <<< 24)
  | .CBZ => pure (W.S64 ||| 0x1A <<< 25 ||| 0 <<< 24)
  | .CBZW => pure (W.S32 ||| 0x1A <<< 25 ||| 0 <<< 24)
  | .CCMN => pure (W.S64 ||| 0 <<< 30 ||| 1 <<< 29 ||| 0xD2 <<< 21 ||| 1 <<< 11 ||| 0 <<< 10 ||| 0 <<< 4)
  | .CCMNW => pure (W.S32 ||| 0 <<< 30 ||| 1 <<< 29 ||| 0xD2 <<< 21 ||| 1 <<< 11 ||| 0 <<< 10 ||| 0 <<< 4)
  | .CCMP => pure (W.S64 ||| 1 <<< 30 ||| 1 <<< 29 ||| 0xD2 <<< 21 ||| 1 <<< 11 ||| 0 <<< 10 ||| 0 <<< 4)
  | .CCMPW => pure (W.S32 ||| 1 <<< 30 ||| 1 <<< 29 ||| 0xD2 <<< 21 ||| 1 <<< 11 ||| 0 <<< 10 ||| 0 <<< 4)
  | .MOVK => pure (W.S64 ||| 3 <<< 29 ||| 0x25 <<< 23)
  | .MOVKW => pure (W.S32 ||| 3 <<< 29 ||| 0x25 <<< 23)
  | .MOVN => pure (W.S64 ||| 0 <<< 29 ||| 0x25 <<< 23)
  | .MOVNW => pure (W.S32 ||| 0 <<< 29 ||| 0x25 <<< 23)
  | .MOVZ => pure (W.S64 ||| 2 <<< 29 ||| 0x25 <<< 23)
  | .MOVZW => pure (W.S32 ||| 2 <<< 29 ||| 0x25 <<< 23)
  | .MSR => pure (SYSOP 0 0 0 4 0 0 0x1F)
  | .AT | .DC | .IC | .TLBI | .SYS => pure (SYSOP 0 1 0 0 0 0 0)
  | .SYSL => pure (SYSOP 1 1 0 0 0 0 0)
  | .TBZ => pure (0x36 <<< 24)
  | .TBNZ => pure (0x37 <<< 24)
  | .DSB => pure (SYSOP 0 0 3 3 0 4 0x1F)
  | .DMB => pure (SYSOP 0 0 3 3 0 5 0x1F)
  | .ISB => pure (SYSOP 0 0 3 3 0 6 0x1F)
  | .HINT => pure (SYSHINT 0)
  | .VCMEQ => pure (ASIMDMISC 0 0 0x09)
  | .VCMGE => pure (ASIMDMISC 1 0 0x08)
  | .VCMGT => pure (ASIMDMISC 0 0 0x08)
  | .VCMLE => pure (ASIMDMISC 1 0 0x09)
  | .VCMLT => pure (ASIMDMISC 0 0 0x0A)
  | .VFCMEQ => pure (ASIMDMISC 0 2 0x0D)
  | .VFCMGE => pure (ASIMDMISC 1 2 0x0C)
  | .VFCMGT => pure (ASIMDMISC 0 2 0x0C)
  | .VFCMLE => pure (ASIMDMISC 1 2 0x0D)
  | .VFCMLT => pure (ASIMDMISC 0 2 0x0E)
  | .VEXT => pure (0x2E <<< 24 ||| 0 <<< 23 ||| 0 <<< 21 ||| 0 <<< 15)
  | .VUSHR => pure (ASIMDSHF 1 0x00)
  | .VSSHR => pure (ASIMDSHF 0 0x00)
  | .VSRSHR => pure (ASIMDSHF 0 0x04)
  | .VSHL => pure (ASIMDSHF 0 0x0A)
  | .VSQSHL => pure (ASIMDSHF 0 0xE)
  | .VUQSHL => pure (ASIMDSHF 1 0xE)
  | .VSHRN | .VSHRN2 => pure (ASIMDSHF 0 0x10)
  | .VXTN | .VXTN2 => pure (ASIMDMISC 0 0 0x12)
  | .VSQXTN | .VSQXTN2 => pure (ASIMDMISC 0 0 0x14)
  | .VSQXTUN | .VSQXTUN2 => pure (ASIMDMISC 1 0 0x12)
  | .VUQXTN | .VUQXTN2 => pure (ASIMDMISC 1 0 0x14)
  | .VFCVTN | .VFCVTN2 => pure (ASIMDMISC 0 1 0x16)
  | .VFCVTL | .VFCVTL2 => pure (ASIMDMISC 0 1 0x17)
  | .VSRI => pure (ASIMDSHF 1 0x08)
  | .VSLI => pure (ASIMDSHF 1 0x0A)
  | .VUSHLL | .VUXTL | .VUSHLL2 | .VUXTL2 => pure (ASIMDSHF 1 0x14)
  | .VSSHLL | .VSSHLL2 | .VSXTL | .VSXTL2 => pure (ASIMDSHF 0 0x14)
  | .VXAR => pure (0xCE <<< 24 ||| 1 <<< 23)
  | .VUSRA => pure (ASIMDSHF 1 0x02)
  | .PRFM => pure (0xf9 <<< 24 ||| 2 <<< 22)
  | .RPRFM => pure (0xf8 <<< 24 ||| 5 <<< 21 ||| 18 <<< 10 ||| 3 <<< 3)
  | _ => throw s!"opirr: bad irr {a.name}"

/-- `ctxt7.opbit` (`asm7.go:7424-7463`). -/
def opbit (_p : Prog) (a : As) : AsmM UInt32 :=
  match a with
  | .CLS => pure (W.S64 ||| OPBIT 5)
  | .CLSW => pure (W.S32 ||| OPBIT 5)
  | .CLZ => pure (W.S64 ||| OPBIT 4)
  | .CLZW => pure (W.S32 ||| OPBIT 4)
  | .RBIT => pure (W.S64 ||| OPBIT 0)
  | .RBITW => pure (W.S32 ||| OPBIT 0)
  | .REV => pure (W.S64 ||| OPBIT 3)
  | .REVW => pure (W.S32 ||| OPBIT 2)
  | .REV16 => pure (W.S64 ||| OPBIT 1)
  | .REV16W => pure (W.S32 ||| OPBIT 1)
  | .REV32 => pure (W.S64 ||| OPBIT 2)
  | _ => throw s!"opbit: bad bit op {a.name}"

/-- `ctxt7.opxrrr` (`asm7.go:7468-7514`): add/subtract sign- or zero-extended register. -/
def opxrrr (_p : Prog) (a : As) (rd rn rm : Int) (extend : Bool) : AsmM UInt32 := do
  let mut extension : UInt32 := 0
  if !extend then
    if isADDop a then
      extension := W.LSL0_64
    if isADDWop a then
      extension := W.LSL0_32
  let op ← match a with
    | .ADD => pure (W.S64 ||| 0 <<< 30 ||| 0 <<< 29 ||| 0x0b <<< 24 ||| 0 <<< 22 ||| 1 <<< 21 ||| extension)
    | .ADDW => pure (W.S32 ||| 0 <<< 30 ||| 0 <<< 29 ||| 0x0b <<< 24 ||| 0 <<< 22 ||| 1 <<< 21 ||| extension)
    | .CMN | .ADDS => pure (W.S64 ||| 0 <<< 30 ||| 1 <<< 29 ||| 0x0b <<< 24 ||| 0 <<< 22 ||| 1 <<< 21 ||| extension)
    | .CMNW | .ADDSW => pure (W.S32 ||| 0 <<< 30 ||| 1 <<< 29 ||| 0x0b <<< 24 ||| 0 <<< 22 ||| 1 <<< 21 ||| extension)
    | .SUB => pure (W.S64 ||| 1 <<< 30 ||| 0 <<< 29 ||| 0x0b <<< 24 ||| 0 <<< 22 ||| 1 <<< 21 ||| extension)
    | .SUBW => pure (W.S32 ||| 1 <<< 30 ||| 0 <<< 29 ||| 0x0b <<< 24 ||| 0 <<< 22 ||| 1 <<< 21 ||| extension)
    | .CMP | .SUBS => pure (W.S64 ||| 1 <<< 30 ||| 1 <<< 29 ||| 0x0b <<< 24 ||| 0 <<< 22 ||| 1 <<< 21 ||| extension)
    | .CMPW | .SUBSW => pure (W.S32 ||| 1 <<< 30 ||| 1 <<< 29 ||| 0x0b <<< 24 ||| 0 <<< 22 ||| 1 <<< 21 ||| extension)
    | _ => throw s!"opxrrr: bad opxrrr {a.name}"
  return op ||| (Go.u32 rm &&& 0x1f) <<< 16 ||| (Go.u32 rn &&& 0x1f) <<< 5 ||| (Go.u32 rd &&& 0x1f)

/-- `ctxt7.opimm` (`asm7.go:7516-7551`). -/
def opimm (_p : Prog) (a : As) : AsmM UInt32 :=
  match a with
  | .SVC => pure (0xD4 <<< 24 ||| 0 <<< 21 ||| 1)
  | .HVC => pure (0xD4 <<< 24 ||| 0 <<< 21 ||| 2)
  | .SMC => pure (0xD4 <<< 24 ||| 0 <<< 21 ||| 3)
  | .BRK => pure (0xD4 <<< 24 ||| 1 <<< 21 ||| 0)
  | .HLT => pure (0xD4 <<< 24 ||| 2 <<< 21 ||| 0)
  | .DCPS1 => pure (0xD4 <<< 24 ||| 5 <<< 21 ||| 1)
  | .DCPS2 => pure (0xD4 <<< 24 ||| 5 <<< 21 ||| 2)
  | .DCPS3 => pure (0xD4 <<< 24 ||| 5 <<< 21 ||| 3)
  | .CLREX => pure (SYSOP 0 0 3 3 0 2 0x1F)
  | .SB => pure (SYSOP 0 0 3 3 0 0 0xFF)
  | _ => throw s!"opimm: bad imm {a.name}"

/-- `Addr.Target()` (`link.go:254-259`): the branch target, `none` when not a branch or nil. -/
private def addrTarget (a : Addr) : Option Nat :=
  if a.type == .BRANCH then
    match a.val with
    | .target id => some id
    | _ => none
  else none

/-- `ctxt7.brdist` (`asm7.go:7553-7581`): the `flen`-bit field of the distance from `c.pc` to
the branch target (or `p.Pool`), both shifted right by `preshift`, then by `shift`. -/
def brdist (p : Nat) (preshift flen shift : Int) : AsmM Int := do
  let pp ← getP p
  let mut v : Int := 0
  let mut t : Int := 0
  let mut q : Option Nat := none
  if pp.to.type == .BRANCH then
    q := addrTarget pp.to
  else if pp.from_.type == .BRANCH then -- adr, adrp
    q := addrTarget pp.from_
  if q.isNone then
    q := pp.pool
  if let some qi := q then
    let qp ← getP qi
    let pc := (← get).pc
    v := (qp.pc >>> preshift.toNat) - (pc >>> preshift.toNat)
    if Go.andN v (2 ^ shift.toNat - 1) != 0 then
      throw "brdist: misaligned label"
    v := v >>> shift.toNat
    t := 2 ^ (flen - 1).toNat
    if v < -t || v >= t then
      throw s!"brdist: branch too far {v} vs {t}"
  -- `v & ((t << 1) - 1)`; `t = 0` is the mask `-1`.
  return if t == 0 then v else Go.andN v (t * 2 - 1).toNat

/-- `ctxt7.opbra` (`asm7.go:7586-7645`): pc-relative branches. -/
def opbra (_p : Prog) (a : As) : AsmM UInt32 :=
  match a with
  | .BEQ => pure (OPBcc 0x0)
  | .BNE => pure (OPBcc 0x1)
  | .BCS => pure (OPBcc 0x2)
  | .BHS => pure (OPBcc 0x2)
  | .BCC => pure (OPBcc 0x3)
  | .BLO => pure (OPBcc 0x3)
  | .BMI => pure (OPBcc 0x4)
  | .BPL => pure (OPBcc 0x5)
  | .BVS => pure (OPBcc 0x6)
  | .BVC => pure (OPBcc 0x7)
  | .BHI => pure (OPBcc 0x8)
  | .BLS => pure (OPBcc 0x9)
  | .BGE => pure (OPBcc 0xa)
  | .BLT => pure (OPBcc 0xb)
  | .BGT => pure (OPBcc 0xc)
  | .BLE => pure (OPBcc 0xd)
  | .JMP => pure (0 <<< 31 ||| 5 <<< 26)
  | .CALL => pure (1 <<< 31 ||| 5 <<< 26)
  | _ => throw s!"opbra: bad bra {a.name}"

/-- `ctxt7.opbrr` (`asm7.go:7647-7661`). -/
def opbrr (_p : Prog) (a : As) : AsmM UInt32 :=
  match a with
  | .CALL => pure (OPBLR 1)
  | .JMP => pure (OPBLR 0)
  | .RET => pure (OPBLR 2)
  | _ => throw s!"opbrr: bad brr {a.name}"

/-- `ctxt7.op0` (`asm7.go:7663-7710`). -/
def op0 (_p : Prog) (a : As) : AsmM UInt32 :=
  match a with
  | .DRPS => pure (0x6B <<< 25 ||| 5 <<< 21 ||| 0x1F <<< 16 ||| 0x1F <<< 5)
  | .ERET => pure (0x6B <<< 25 ||| 4 <<< 21 ||| 0x1F <<< 16 ||| 0 <<< 10 ||| 0x1F <<< 5)
  | .NOOP => pure (SYSHINT 0)
  | .YIELD => pure (SYSHINT 1)
  | .WFE => pure (SYSHINT 2)
  | .WFI => pure (SYSHINT 3)
  | .SEV => pure (SYSHINT 4)
  | .SEVL => pure (SYSHINT 5)
  | .PACIASP => pure (SYSHINT 25)
  | .AUTIASP => pure (SYSHINT 29)
  | .PACIBSP => pure (SYSHINT 27)
  | .AUTIBSP => pure (SYSHINT 31)
  | .AUTIA1716 => pure (SYSHINT 12)
  | .AUTIB1716 => pure (SYSHINT 14)
  | _ => throw s!"op0: bad op0 {a.name}"

/-- `ctxt7.opload` (`asm7.go:7715-7768`). -/
def opload (_p : Prog) (a : As) : AsmM UInt32 :=
  match a with
  | .LDAR => pure (LDSTX 3 1 1 0 1 ||| 0x1F <<< 10)
  | .LDARW => pure (LDSTX 2 1 1 0 1 ||| 0x1F <<< 10)
  | .LDARB => pure (LDSTX 0 1 1 0 1 ||| 0x1F <<< 10)
  | .LDARH => pure (LDSTX 1 1 1 0 1 ||| 0x1F <<< 10)
  | .LDAXP => pure (LDSTX 3 0 1 1 1)
  | .LDAXPW => pure (LDSTX 2 0 1 1 1)
  | .LDAXR => pure (LDSTX 3 0 1 0 1 ||| 0x1F <<< 10)
  | .LDAXRW => pure (LDSTX 2 0 1 0 1 ||| 0x1F <<< 10)
  | .LDAXRB => pure (LDSTX 0 0 1 0 1 ||| 0x1F <<< 10)
  | .LDAXRH => pure (LDSTX 1 0 1 0 1 ||| 0x1F <<< 10)
  | .LDXR => pure (LDSTX 3 0 1 0 0 ||| 0x1F <<< 10)
  | .LDXRB => pure (LDSTX 0 0 1 0 0 ||| 0x1F <<< 10)
  | .LDXRH => pure (LDSTX 1 0 1 0 0 ||| 0x1F <<< 10)
  | .LDXRW => pure (LDSTX 2 0 1 0 0 ||| 0x1F <<< 10)
  | .LDXP => pure (LDSTX 3 0 1 1 0)
  | .LDXPW => pure (LDSTX 2 0 1 1 0)
  | _ => throw s!"opload: bad opload {a.name}"

/-- `ctxt7.opstore` (`asm7.go:7770-7823`). -/
def opstore (_p : Prog) (a : As) : AsmM UInt32 :=
  match a with
  | .STLR => pure (LDSTX 3 1 0 0 1 ||| 0x1F <<< 10)
  | .STLRB => pure (LDSTX 0 1 0 0 1 ||| 0x1F <<< 10)
  | .STLRH => pure (LDSTX 1 1 0 0 1 ||| 0x1F <<< 10)
  | .STLRW => pure (LDSTX 2 1 0 0 1 ||| 0x1F <<< 10)
  | .STLXP => pure (LDSTX 3 0 0 1 1)
  | .STLXPW => pure (LDSTX 2 0 0 1 1)
  | .STLXR => pure (LDSTX 3 0 0 0 1 ||| 0x1F <<< 10)
  | .STLXRB => pure (LDSTX 0 0 0 0 1 ||| 0x1F <<< 10)
  | .STLXRH => pure (LDSTX 1 0 0 0 1 ||| 0x1F <<< 10)
  | .STLXRW => pure (LDSTX 2 0 0 0 1 ||| 0x1F <<< 10)
  | .STXR => pure (LDSTX 3 0 0 0 0 ||| 0x1F <<< 10)
  | .STXRB => pure (LDSTX 0 0 0 0 0 ||| 0x1F <<< 10)
  | .STXRH => pure (LDSTX 1 0 0 0 0 ||| 0x1F <<< 10)
  | .STXP => pure (LDSTX 3 0 0 1 0)
  | .STXPW => pure (LDSTX 2 0 0 1 0)
  | .STXRW => pure (LDSTX 2 0 0 0 0 ||| 0x1F <<< 10)
  | _ => throw s!"opstore: bad opstore {a.name}"

/-- `ctxt7.olsr12u` (`asm7.go:7829-7838`): load/store register, scaled 12-bit unsigned
immediate (C3.3.13). `v` is an `int32`. -/
def olsr12u (_p : Prog) (o : UInt32) (v : Int) (rn rt : Int) : AsmM UInt32 := do
  if v < 0 || v >= 2 ^ 12 then
    throw s!"olsr12u: offset out of range: {v}"
  let mut o := o
  o := o ||| (Go.u32 v &&& 0xFFF) <<< 10
  o := o ||| (Go.u32 rn &&& 31) <<< 5
  o := o ||| (Go.u32 rt &&& 31)
  o := o ||| 1 <<< 24
  return o

/-- `ctxt7.olsr9s` (`asm7.go:7843-7851`): load/store register, unscaled 9-bit signed immediate
(C3.3.12). `v` is an `int32`. -/
def olsr9s (_p : Prog) (o : UInt32) (v : Int) (rn rt : Int) : AsmM UInt32 := do
  if v < -256 || v > 255 then
    throw s!"olsr9s: offset out of range: {v}"
  let mut o := o
  o := o ||| Go.u32 (Go.i32 (Go.andN v 0x1FF * 4096))
  o := o ||| (Go.u32 rn &&& 31) <<< 5
  o := o ||| (Go.u32 rt &&& 31)
  return o

/-- `ctxt7.opldr` (`asm7.go:7874-7909`): load (immediate), the scaled 12-bit, unscaled 9-bit
and pre/post-indexed forms. -/
def opldr (_p : Prog) (a : As) : AsmM UInt32 :=
  match a with
  | .MOVD => pure (LDSTR 3 0 1)
  | .MOVW => pure (LDSTR 2 0 2)
  | .MOVWU => pure (LDSTR 2 0 1)
  | .MOVH => pure (LDSTR 1 0 2)
  | .MOVHU => pure (LDSTR 1 0 1)
  | .MOVB => pure (LDSTR 0 0 2)
  | .MOVBU => pure (LDSTR 0 0 1)
  | .FMOVS | .VMOVS => pure (LDSTR 2 1 1)
  | .FMOVD | .VMOVD => pure (LDSTR 3 1 1)
  | .FMOVQ | .VMOVQ => pure (LDSTR 0 1 3)
  | _ => throw s!"opldr: bad opldr {a.name}"

/-- `ctxt7.opstr` (`asm7.go:7858-7867`): store (immediate). Switches on `p.As`, not `a`. -/
def opstr (p : Nat) (a : As) : AsmM UInt32 := do
  let pp ← getP p
  let enc ← opldr pp a
  match pp.as with
  | .FMOVQ => return enc &&& ~~~(1 <<< 22)
  | _ => return LD2STR enc

/-- `ctxt7.opldrr` (`asm7.go:7914-7949`): load with register offset (`(Rn)(Rm.UXTW<<2)`,
`(Rn)(Rm<<2)`, `(Rn)(Rm)`). -/
def opldrr (_p : Prog) (a : As) (rt rn rm : Int) (extension : Bool) : AsmM UInt32 := do
  let mut OptionS : UInt32 := 0x1a
  if extension then
    OptionS := 0 -- option value and S value have been encoded into p.From.Offset.
  let op ← match a with
    | .MOVD => pure (OptionS <<< 10 ||| 0x3 <<< 21 ||| 0x1f <<< 27)
    | .MOVW => pure (OptionS <<< 10 ||| 0x5 <<< 21 ||| 0x17 <<< 27)
    | .MOVWU => pure (OptionS <<< 10 ||| 0x3 <<< 21 ||| 0x17 <<< 27)
    | .MOVH => pure (OptionS <<< 10 ||| 0x5 <<< 21 ||| 0x0f <<< 27)
    | .MOVHU => pure (OptionS <<< 10 ||| 0x3 <<< 21 ||| 0x0f <<< 27)
    | .MOVB => pure (OptionS <<< 10 ||| 0x5 <<< 21 ||| 0x07 <<< 27)
    | .MOVBU => pure (OptionS <<< 10 ||| 0x3 <<< 21 ||| 0x07 <<< 27)
    | .FMOVS => pure (OptionS <<< 10 ||| 0x3 <<< 21 ||| 0x17 <<< 27 ||| 1 <<< 26)
    | .FMOVD => pure (OptionS <<< 10 ||| 0x3 <<< 21 ||| 0x1f <<< 27 ||| 1 <<< 26)
    | .FMOVQ => pure (OptionS <<< 10 ||| 0x7 <<< 21 ||| 0x07 <<< 27 ||| 1 <<< 26)
    | _ => throw s!"opldrr: bad opldrr {a.name}"
  return op ||| (Go.u32 rm &&& 31) <<< 16 ||| (Go.u32 rn &&& 31) <<< 5 ||| (Go.u32 rt &&& 31)

/-- `ctxt7.opstrr` (`asm7.go:7954-7983`): store with register offset. -/
def opstrr (_p : Prog) (a : As) (rt rn rm : Int) (extension : Bool) : AsmM UInt32 := do
  let mut OptionS : UInt32 := 0x1a
  if extension then
    OptionS := 0 -- option value and S value have been encoded into p.To.Offset.
  let op ← match a with
    | .MOVD => pure (OptionS <<< 10 ||| 0x1 <<< 21 ||| 0x1f <<< 27)
    | .MOVW | .MOVWU => pure (OptionS <<< 10 ||| 0x1 <<< 21 ||| 0x17 <<< 27)
    | .MOVH | .MOVHU => pure (OptionS <<< 10 ||| 0x1 <<< 21 ||| 0x0f <<< 27)
    | .MOVB | .MOVBU => pure (OptionS <<< 10 ||| 0x1 <<< 21 ||| 0x07 <<< 27)
    | .FMOVS => pure (OptionS <<< 10 ||| 0x1 <<< 21 ||| 0x17 <<< 27 ||| 1 <<< 26)
    | .FMOVD => pure (OptionS <<< 10 ||| 0x1 <<< 21 ||| 0x1f <<< 27 ||| 1 <<< 26)
    | .FMOVQ => pure (OptionS <<< 10 ||| 0x5 <<< 21 ||| 0x07 <<< 27 ||| 1 <<< 26)
    | _ => throw s!"opstrr: bad opstrr {a.name}"
  return op ||| (Go.u32 rm &&& 31) <<< 16 ||| (Go.u32 rn &&& 31) <<< 5 ||| (Go.u32 rt &&& 31)

/-- `ctxt7.oaddi` (`asm7.go:7985-7999`). `v` is an `int32`. -/
def oaddi (p : Prog) (a : As) (v : Int) (rd rn : Int) : AsmM UInt32 := do
  let mut op ← opirr p a
  let mut v := v
  if Go.andN v 0xFFF000 != 0 then
    if Go.andN v 0xFFF != 0 then
      throw "oaddi: misuses oaddi"
    v := v >>> 12
    op := op ||| 1 <<< 22
  op := op ||| ((Go.u32 v &&& 0xFFF) <<< 10) ||| ((Go.u32 rn &&& 31) <<< 5) ||| (Go.u32 rd &&& 31)
  return op

/-- `ctxt7.oaddi12` (`asm7.go:8001-8012`). `v` is an `int32`. -/
def oaddi12 (p : Prog) (v : Int) (rd rn : Int) : AsmM UInt32 := do
  if v < -4095 || v > 4095 then
    throw s!"oaddi12: {v} is not a 12 bit immediate"
  let mut a : As := .ADD
  let mut v := v
  if v < 0 then
    a := .SUB
    v := -v
  oaddi p a v rd rn

/-- `ctxt7.omovlit` (`asm7.go:8017-8077`): load a literal value into `dr` (an `ADD` from `ZR`
when `p.Pool` is nil, else a PC-relative literal load from the pool entry). The `Logf` is
debug output and has no effect. Go's `c.aclass(a)` may clear `a.Reg` (`REGSP` of a stack
operand) in place; `oplook` has already stored that update into the Prog (`aclassAddr`), and a
second update is a no-op, so only `instoffset` is taken here. -/
def omovlit (as : As) (p : Nat) (a : Addr) (dr : Int) : AsmM UInt32 := do
  let pp ← getP p
  match pp.pool with
  | none => -- not in literal pool
    let _ ← aclass a
    let mut o1 ← opirr pp .ADD
    let mut v := Go.i32 (← get).instoffset
    if v != 0 && Go.andN v 0xFFF == 0 then
      v := v >>> 12
      o1 := o1 ||| 1 <<< 22 -- shift, by 12
    o1 := o1 ||| ((Go.u32 v &&& 0xFFF) <<< 10) ||| ((Go.u32 REGZERO &&& 31) <<< 5)
      ||| (Go.u32 dr &&& 31)
    return o1
  | some pool =>
    let (fp, w) ← match as with
      | .FMOVS | .VMOVS => pure ((1 : Int), (0 : Int)) -- 32-bit SIMD/FP
      | .FMOVD | .VMOVD => pure (1, 1) -- 64-bit SIMD/FP
      | .VMOVQ => pure (1, 2) -- 128-bit SIMD/FP
      | .MOVD => do
        let poolP ← getP pool
        if poolP.as == .DWORD then pure (0, 1) -- 64-bit
        else if poolP.to.offset < 0 then pure (0, 2) -- 32-bit, sign-extended to 64-bit
        else if poolP.to.offset >= 0 then pure (0, 0) -- 32-bit, zero-extended to 64-bit
        else throw "omovlit: invalid operand"
      | .MOVBU | .MOVHU | .MOVWU => pure (0, 0) -- 32-bit, zero-extended to 64-bit
      | .MOVB | .MOVH | .MOVW => pure (0, 2) -- 32-bit, sign-extended to 64-bit
      | _ => throw s!"omovlit: invalid operation {as.name}"
    let v := Go.i32 (← brdist p 0 19 2)
    let mut o1 : UInt32 := Go.u32 w <<< 30 ||| Go.u32 fp <<< 26 ||| 3 <<< 27
    o1 := o1 ||| (Go.u32 v &&& 0x7FFFF) <<< 5
    o1 := o1 ||| (Go.u32 dr &&& 31)
    return o1

/-- `ctxt7.omovconst` (`asm7.go:8079-8128`): load a constant (`MOVCON` or `BITCON`) into `rt`.
`a.Class` is the class `oplook` cached. -/
def omovconst (as : As) (p : Prog) (a : Addr) (rt : Int) : AsmM UInt32 := do
  let cls := a.cls
  if (cls == C_BITCON || cls == C_ABCON || cls == C_ABCON0) && rt != REGZERO then
    -- or $bitcon, REGZERO, rt. rt can't be ZR.
    let mut mode : Nat := 64
    let mut as1 : As := .XXX
    match as with
    | .MOVW =>
      as1 := .ORRW
      mode := 32
    | .MOVD =>
      as1 := .ORR
    | _ => pure ()
    let o1 ← opirr p as1
    return o1 ||| bitconEncode (Go.u64 a.offset) mode ||| (Go.u32 REGZERO &&& 31) <<< 5
      ||| (Go.u32 rt &&& 31)
  let mut o1 : UInt32 := 0
  if as == .MOVW then
    let mut d : UInt32 := Go.u32 a.offset
    let mut s := movcon (Int.ofNat d.toNat)
    if s < 0 || s >= 32 then
      d := ~~~d
      s := movcon (Int.ofNat d.toNat)
      if s < 0 || s >= 32 then
        throw s!"omovconst: impossible 32-bit move wide: {(Go.u32 a.offset).toNat}"
      o1 ← opirr p .MOVNW
    else
      o1 ← opirr p .MOVZW
    o1 := o1 ||| MOVCONST (Int.ofNat d.toNat) (s >>> 4) rt
  if as == .MOVD then
    let mut d := a.offset
    let mut s := movcon d
    if s < 0 || s >= 64 then
      d := -d - 1
      s := movcon d
      if s < 0 || s >= 64 then
        throw s!"omovconst: impossible 64-bit move wide: {(Go.u64 a.offset).toNat}"
      o1 ← opirr p .MOVN
    else
      o1 ← opirr p .MOVZ
    o1 := o1 ||| MOVCONST d (s >>> 4) rt
  return o1

/-- `os[k] = w` (a Go slice store: out of range is a panic). -/
private def setOs (os : Array UInt32) (k : Nat) (w : UInt32) : AsmM (Array UInt32) :=
  if k < os.size then pure (os.set! k w)
  else throw s!"omovlconst: index out of range [{k}] with length {os.size}"

/-- `ctxt7.omovlconst` (`asm7.go:8131-8298`): load a 32-bit/64-bit large constant (`LCON` or
`VCON`) `a.Offset` into `rt`; returns the number of instructions `num` and the caller's `os`
with the instructions written into it. -/
def omovlconst (as : As) (p : Prog) (a : Addr) (rt : Int) (os : Array UInt32) :
    AsmM (Nat × Array UInt32) := do
  let mut os := os
  match as with
  | .MOVW =>
    let d : UInt32 := Go.u32 a.offset
    -- use MOVZW and MOVKW to load a constant to rt
    os ← setOs os 0 ((← opirr p .MOVZW) ||| MOVCONST (Int.ofNat d.toNat) 0 rt)
    os ← setOs os 1 ((← opirr p .MOVKW) ||| MOVCONST (Int.ofNat d.toNat) 1 rt)
    return (2, os)
  | .MOVD =>
    let d := a.offset
    let dn := -d - 1
    let mut immh : Array Int := #[0, 0, 0, 0]
    let mut zeroCount := 0
    let mut negCount := 0
    for i in [0:4] do
      immh := immh.set! i (Go.andN (Go.i64 d >>> (i * 16)) 0xffff)
      if immh[i]! == 0 then
        zeroCount := zeroCount + 1
      else if immh[i]! == 0xffff then
        negCount := negCount + 1
    if zeroCount == 4 || negCount == 4 then
      throw "omovlconst: the immediate should be MOVCON"
    if zeroCount == 3 then
      -- one MOVZ
      for i in [0:4] do
        if immh[i]! != 0 then
          os ← setOs os 0 ((← opirr p .MOVZ) ||| MOVCONST d i rt)
          break
      return (1, os)
    else if negCount == 3 then
      -- one MOVN
      for i in [0:4] do
        if immh[i]! != 0xffff then
          os ← setOs os 0 ((← opirr p .MOVN) ||| MOVCONST dn i rt)
          break
      return (1, os)
    else if zeroCount == 2 then
      -- one MOVZ and one MOVK
      let mut i := 4
      for k in [0:4] do
        if immh[k]! != 0 then
          os ← setOs os 0 ((← opirr p .MOVZ) ||| MOVCONST d k rt)
          i := k + 1
          break
      for k in [i:4] do
        if immh[k]! != 0 then
          os ← setOs os 1 ((← opirr p .MOVK) ||| MOVCONST d k rt)
      return (2, os)
    else if negCount == 2 then
      -- one MOVN and one MOVK
      let mut i := 4
      for k in [0:4] do
        if immh[k]! != 0xffff then
          os ← setOs os 0 ((← opirr p .MOVN) ||| MOVCONST dn k rt)
          i := k + 1
          break
      for k in [i:4] do
        if immh[k]! != 0xffff then
          os ← setOs os 1 ((← opirr p .MOVK) ||| MOVCONST d k rt)
      return (2, os)
    -- Look for a two instruction pair, a bit pattern encodeable as a bitcon immediate plus a
    -- fixup MOVK instruction.
    for i in [0:4] do
      let mask : UInt64 := (0xffff : UInt64) <<< (i * 16).toUInt64
      for period in [2, 4, 8, 16, 32] do
        -- Copy in bits from outside of the masked region
        let x := Go.u64 d &&& ~~~mask ||| Go.rotateLeft64 (Go.u64 d) (max period 16) &&& mask
        if isbitcon x then
          -- ORR $c1, ZR, rt
          os ← setOs os 0 ((← opirr p .ORR) ||| bitconEncode x 64
            ||| (Go.u32 REGZERO &&& 31) <<< 5 ||| (Go.u32 rt &&& 31))
          -- MOVK $c2<<(i*16), rt
          os ← setOs os 1 ((← opirr p .MOVK) ||| MOVCONST d i rt)
          return (2, os)
    if zeroCount == 1 then
      -- one MOVZ and two MOVKs
      let mut i := 4
      for k in [0:4] do
        if immh[k]! != 0 then
          os ← setOs os 0 ((← opirr p .MOVZ) ||| MOVCONST d k rt)
          i := k + 1
          break
      let mut j := 1
      for k in [i:4] do
        if immh[k]! != 0 then
          os ← setOs os j ((← opirr p .MOVK) ||| MOVCONST d k rt)
          j := j + 1
      return (3, os)
    else if negCount == 1 then
      -- one MOVN and two MOVKs
      let mut i := 4
      for k in [0:4] do
        if immh[k]! != 0xffff then
          os ← setOs os 0 ((← opirr p .MOVN) ||| MOVCONST dn k rt)
          i := k + 1
          break
      let mut j := 1
      for k in [i:4] do
        if immh[k]! != 0xffff then
          os ← setOs os j ((← opirr p .MOVK) ||| MOVCONST d k rt)
          j := j + 1
      return (3, os)
    else
      -- one MOVZ and 3 MOVKs
      os ← setOs os 0 ((← opirr p .MOVZ) ||| MOVCONST d 0 rt)
      for i in [1:4] do
        os ← setOs os i ((← opirr p .MOVK) ||| MOVCONST d i rt)
      return (4, os)
  | _ => return (0, os)

/-- `ctxt7.opbfm` (`asm7.go:8300-8318`). `r`, `s` are `int64`. -/
def opbfm (p : Prog) (a : As) (r s : Int) (rf rt : Int) : AsmM UInt32 := do
  let mut o ← opirr p a
  let b : UInt32 := if o &&& (1 <<< 31) == 0 then 32 else 64
  if r < 0 || Go.u32 r >= b then
    throw "opbfm: illegal bit number"
  o := o ||| (Go.u32 r &&& 0x3F) <<< 16
  if s < 0 || Go.u32 s >= b then
    throw "opbfm: illegal bit number"
  o := o ||| (Go.u32 s &&& 0x3F) <<< 10
  o := o ||| ((Go.u32 rf &&& 31) <<< 5) ||| (Go.u32 rt &&& 31)
  return o

/-- `ctxt7.opextr` (`asm7.go:8320-8337`). `v` is an `int64`. -/
def opextr (p : Prog) (a : As) (v : Int) (rn rm rt : Int) : AsmM UInt32 := do
  let mut o ← opirr p a
  let b : UInt32 := if o &&& (1 <<< 31) != 0 then 63 else 31
  if v < 0 || Go.u32 v > b then
    throw "opextr: illegal bit number"
  o := o ||| Go.u32 v <<< 10
  o := o ||| (Go.u32 rn &&& 31) <<< 5
  o := o ||| (Go.u32 rm &&& 31) <<< 16
  o := o ||| (Go.u32 rt &&& 31)
  return o

/-- `ctxt7.opldpstp` (`asm7.go:8339-8422`): `LDP`/`STP` and their variants. `vo` is an `int32`;
Go's `%` and `/` truncate. -/
def opldpstp (p : Nat) (o : ARM64.Optab) (vo : Int) (rbase rl rh : Int) (ldp : UInt32) :
    AsmM UInt32 := do
  let pp ← getP p
  let mut vo := vo
  let mut wback := false
  if (o.scond : Int) == C_XPOST || (o.scond : Int) == C_XPRE then
    wback := true
  match pp.as with
  | .LDP | .LDPW | .LDPSW =>
    checkUnpredictable pp true wback pp.from_.reg pp.to.reg (Go.i16 pp.to.offset)
  | .STP | .STPW =>
    if wback then
      checkUnpredictable pp false true pp.to.reg pp.from_.reg (Go.i16 pp.from_.offset)
  | .FLDPD | .FLDPQ | .FLDPS =>
    checkUnpredictable pp true false pp.from_.reg pp.to.reg (Go.i16 pp.to.offset)
  | _ => pure ()
  let mut ret : UInt32 := 0
  -- check offset
  match pp.as with
  | .FLDPQ | .FSTPQ =>
    if vo < -1024 || vo > 1008 || vo.tmod 16 != 0 then
      throw "opldpstp: invalid offset"
    vo := vo.tdiv 16
    ret := 2 <<< 30 ||| 1 <<< 26
  | .FLDPD | .FSTPD =>
    if vo < -512 || vo > 504 || vo.tmod 8 != 0 then
      throw "opldpstp: invalid offset"
    vo := vo.tdiv 8
    ret := 1 <<< 30 ||| 1 <<< 26
  | .FLDPS | .FSTPS =>
    if vo < -256 || vo > 252 || vo.tmod 4 != 0 then
      throw "opldpstp: invalid offset"
    vo := vo.tdiv 4
    ret := 1 <<< 26
  | .LDP | .STP =>
    if vo < -512 || vo > 504 || vo.tmod 8 != 0 then
      throw "opldpstp: invalid offset"
    vo := vo.tdiv 8
    ret := 2 <<< 30
  | .LDPW | .STPW =>
    if vo < -256 || vo > 252 || vo.tmod 4 != 0 then
      throw "opldpstp: invalid offset"
    vo := vo.tdiv 4
    ret := 0
  | .LDPSW =>
    if vo < -256 || vo > 252 || vo.tmod 4 != 0 then
      throw "opldpstp: invalid offset"
    vo := vo.tdiv 4
    ret := 1 <<< 30
  | _ => throw s!"opldpstp: invalid instruction {pp.as.name}"
  -- check register pair
  match pp.as with
  | .FLDPQ | .FLDPD | .FLDPS | .FSTPQ | .FSTPD | .FSTPS =>
    if rl < REG_F0 || REG_F31 < rl || rh < REG_F0 || REG_F31 < rh then
      throw "opldpstp: invalid register pair"
  | .LDP | .LDPW | .LDPSW =>
    if rl < REG_R0 || REG_R31 < rl || rh < REG_R0 || REG_R31 < rh then
      throw "opldpstp: invalid register pair"
  | .STP | .STPW =>
    if rl < REG_R0 || REG_R31 < rl || rh < REG_R0 || REG_R31 < rh then
      throw "opldpstp: invalid register pair"
  | _ => pure ()
  -- other conditional flag bits
  if (o.scond : Int) == C_XPOST then
    ret := ret ||| 1 <<< 23
  else if (o.scond : Int) == C_XPRE then
    ret := ret ||| 3 <<< 23
  else
    ret := ret ||| 2 <<< 23
  ret := ret ||| 5 <<< 27 ||| (ldp &&& 1) <<< 22 ||| (Go.u32 vo &&& 0x7f) <<< 15
    ||| (Go.u32 rh &&& 31) <<< 10 ||| (Go.u32 rbase &&& 31) <<< 5 ||| (Go.u32 rl &&& 31)
  return ret

/-- `ctxt7.maskOpvldvst` (`asm7.go:8424-8447`): the `opcode` field of `VLD[1-4]`, `VST[1-4]`. -/
def maskOpvldvst (p : Nat) (o1 : UInt32) : AsmM UInt32 := do
  let pp ← getP p
  if pp.as == .VLD1 || pp.as == .VST1 then
    return o1
  let mut o1 := o1 &&& ~~~0xf000 -- mask out "opcode" field (bit 12-15)
  match pp.as with
  | .VLD1R | .VLD2R => o1 := o1 ||| 0xC <<< 12
  | .VLD3R | .VLD4R => o1 := o1 ||| 0xE <<< 12
  | .VLD2 | .VST2 => o1 := o1 ||| 8 <<< 12
  | .VLD3 | .VST3 => o1 := o1 ||| 4 <<< 12
  | .VLD4 | .VST4 => pure ()
  | _ => throw s!"maskOpvldvst: unsupported instruction:{pp.as.name}"
  return o1

/-- `roff` (`asm7.go:8471-8474`): `rm` is the Rm register value, `o` the extension, `amount`
the left shift value (`int16`). -/
def roff (rm : Int) (o : UInt32) (amount : Int) : UInt32 :=
  (Go.u32 rm &&& 31) <<< 16 ||| o <<< 13 ||| Go.u32 amount <<< 10

/-- `ctxt7.encRegShiftOrExt` (`asm7.go:8477-8543`): the encoding of a shifted/extended register,
`Rx<<n`, `Rx.UXTW<<n`, …. `r` is an `int16`. -/
def encRegShiftOrExt (p : Nat) (a : Addr) (r : Int) : AsmM UInt32 := do
  let pp ← getP p
  let num := Go.andN (r >>> 5) 7
  let rm := Go.andN r 31
  if REG_UXTB <= r && r < REG_UXTH then
    return roff rm 0 num
  else if REG_UXTH <= r && r < REG_UXTW then
    return roff rm 1 num
  else if REG_UXTW <= r && r < REG_UXTX then
    if a.type == .MEM then
      if num == 0 then
        -- MOVB, MOVBU and FMOVB need extension amount 0; Go encodes Rn.UXTW like Rn.UXTW<<0 as
        -- "not present" (also for LSL, SXTW and SXTX).
        return roff rm 2 2
      else
        return roff rm 2 6
    else
      return roff rm 2 num
  else if REG_UXTX <= r && r < REG_SXTB then
    return roff rm 3 num
  else if REG_SXTB <= r && r < REG_SXTH then
    return roff rm 4 num
  else if REG_SXTH <= r && r < REG_SXTW then
    return roff rm 5 num
  else if REG_SXTW <= r && r < REG_SXTX then
    if a.type == .MEM then
      if num == 0 then
        return roff rm 6 2
      else
        return roff rm 6 6
    else
      return roff rm 6 num
  else if REG_SXTX <= r && r < REG_SPECIAL then
    if a.type == .MEM then
      if num == 0 then
        return roff rm 7 2
      else
        return roff rm 7 6
    else
      return roff rm 7 num
  else if REG_LSL <= r && r < REG_ARNG then
    if a.type == .MEM then -- (R1)(R2<<1)
      if num == 0 then
        return roff rm 3 2
      else
        return roff rm 3 6
    else if isADDWop pp.as then
      return roff rm 2 num
    return roff rm 3 num
  else
    throw "encRegShiftOrExt: unsupported register extension type."

/-- `pack` (`asm7.go:8546-8548`): the "Q" field and two arrangement specifiers (`uint8`). -/
def pack (q : UInt32) (arngA arngB : Nat) : UInt32 :=
  q <<< 16 ||| (arngA % 256).toUInt32 <<< 8 ||| (arngB % 256).toUInt32

end GoFV.Asm
