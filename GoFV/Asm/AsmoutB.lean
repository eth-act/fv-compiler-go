import GoFV.Asm.Asm7Ops

/-!
# `asmout` cases 46 and above (`asm7.go:4496-6183`; `docs/PASSES3.md` D5)

`asmoutB case p o` is the arm `case` of `ctxt7.asmout`'s `switch o.type_` for the cases from 46
on: `some #[o1, o2, …]` (the words it sets, missing trailing words are 0), `none` for a case it
does not handle (`GoFV.Asm.Asmout` then reports it). Relocations are appended to the text symbol
(`c.cursym.AddRel`) in Go's order, at `ctxt7.pc`.

Each case is a function ported literally from its arm (same checks, same order of the helper
calls, Go's integer conversions via `Go.u32`/`Go.i16`/…). `ctxt.Diag` is a `throw` (no corpus
function has assembler diagnostics), so a case stops at its first diagnostic where Go would
continue and report more. Case 127 (SVE, `insts`) is unreachable from compiled code: no SVE
opcode exists in `As`; it is a port error.
-/

namespace GoFV.Asm

open ARM64 AsmM

namespace AsmoutB

/-- `c.ctxt.Diag(msg, p)` in `asmout`. -/
private def diag {α} (p : Prog) (msg : String) : AsmM α :=
  throw s!"asmout: {msg}: {p.as.name}"

/-- `uint32(r & 31)` of an `int16` register. -/
private def r31 (r : Int) : UInt32 := Go.u32 r &&& 31

/-- `(r >> 5) & 15` of an `int16` register: its arrangement field. -/
private def arng (r : Int) : Int := (((Go.u32 r >>> 5) &&& 15).toNat : Int)

/-- `c.cursym.AddRel(c.ctxt, obj.Reloc{Type, Off: int32(c.pc), Siz, Sym, Add})`. -/
private def addRel (type : String) (siz : Nat) (sym : Option Nat) (add : Int) : AsmM Unit := do
  let s ← get
  set { s with textR := s.textR.push { off := Go.i32 s.pc, siz, type, add, sym } }

/-- `p.GetFrom3()` (`link.go:356-363`). -/
private def getFrom3 (p : Prog) : Option Addr := (p.rest.find? (·.1 == 0)).map (·.2)

/-- `p.GetTo2()` (`link.go:389-396`). -/
private def getTo2 (p : Prog) : Option Addr := (p.rest.find? (·.1 == 1)).map (·.2)

/-- `*p.GetFrom3()`: Go dereferences it without a check (a nil pointer panics). -/
private def from3! (p : Prog) : AsmM Addr :=
  match getFrom3 p with
  | some a => pure a
  | none => diag p "nil GetFrom3"

/-- `*p.GetTo2()`, as `from3!`. -/
private def to2! (p : Prog) : AsmM Addr :=
  match getTo2 p with
  | some a => pure a
  | none => diag p "nil GetTo2"

/-- `p.From.Val.(float64)`: the raw bits (the type assertion panics on other values). -/
private def fval (p : Prog) (a : Addr) : AsmM UInt64 :=
  match a.val with
  | .float b => pure b
  | _ => diag p "Val is not a float64"

/-- `float64 == 0.0` of raw bits (`+0` and `-0`). -/
private def isZeroF (b : UInt64) : Bool := b &&& 0x7fffffffffffffff == 0

/-- Case 46, `cls` (`asm7.go:4496-4500`). -/
def c46 (p : Prog) : AsmM (Array UInt32) := do
  let mut o1 ← opbit p p.as
  o1 := o1 ||| (r31 p.from_.reg <<< 5)
  o1 := o1 ||| r31 p.to.reg
  return #[o1]

/-- Case 47, `SWPx/LDADDx/… Rs, (Rb), Rt` (`asm7.go:4502-4513`). -/
def c47 (p : Prog) : AsmM (Array UInt32) := do
  let rs := p.from_.reg
  let rt := p.regTo2
  let rb := p.to.reg
  if rt == REG_RSP then diag p "illegal destination register"
  let mut o1 := (atomicLDADD p.as).getD 0 ||| (atomicSWP p.as).getD 0
  o1 := o1 ||| (r31 rs <<< 16) ||| (r31 rb <<< 5) ||| r31 rt
  return #[o1]

/-- Case 48, `ADD $C_ADDCON2, Rm, Rd` (`asm7.go:4515-4527`). -/
def c48 (p : Prog) : AsmM (Array UInt32) := do
  let op ← opirr p p.as
  if op &&& W.Sbit != 0 then
    diag p "can not break addition/subtraction when S bit is set"
  let rt := p.to.reg
  let mut r := p.reg
  if r == 0 then r := rt
  let v1 ← regoff p.from_
  let o1 ← oaddi p p.as (Go.u32 v1 &&& 0x000fff).toNat rt r
  let v2 ← regoff p.from_
  let o2 ← oaddi p p.as (Go.u32 v2 &&& 0xfff000).toNat rt rt
  return #[o1, o2]

/-- Case 49, `op Vm.<T>, Vn, Vd` (`asm7.go:4529-4540`). -/
def c49 (p : Prog) : AsmM (Array UInt32) := do
  let rt := p.to.reg
  let r := p.reg
  let rf := p.from_.reg
  let cf ← aclass p.from_
  let af := arng rf
  let sz := if p.as == .SHA512H || p.as == .SHA512H2 then ARNG_2D else ARNG_4S
  if (cf : Int) == C_ARNG && af != sz then diag p "invalid arrangement"
  let o1 ← oprrr p p.as rt r rf
  return #[o1]

/-- Case 50, `sys/sysl` (`asm7.go:4542-4553`). -/
def c50 (p : Prog) : AsmM (Array UInt32) := do
  let mut o1 ← opirr p p.as
  if Go.u64 p.from_.offset &&& ~~~(Go.u64 (SYSARG4 0x7 0xF 0xF 0x7)) != 0 then
    diag p "illegal SYS argument"
  o1 := o1 ||| Go.u32 p.from_.offset
  if p.to.type == .REG then
    o1 := o1 ||| r31 p.to.reg
  else
    o1 := o1 ||| 0x1F
  return #[o1]

/-- Case 51, `dmb` (`asm7.go:4555-4560`). -/
def c51 (p : Prog) : AsmM (Array UInt32) := do
  let mut o1 ← opirr p p.as
  if p.from_.type == .CONST then
    o1 := o1 ||| ((Go.u32 p.from_.offset &&& 0xF) <<< 8)
  return #[o1]

/-- Case 52, `hint` (`asm7.go:4562-4565`). -/
def c52 (p : Prog) : AsmM (Array UInt32) := do
  let mut o1 ← opirr p p.as
  o1 := o1 ||| ((Go.u32 p.from_.offset &&& 0x7F) <<< 5)
  return #[o1]

/-- Case 53, `and/or/eor/bic/tst/… $bitcon, Rn, Rd` (`asm7.go:4567-4593`). -/
def c53 (p : Prog) : AsmM (Array UInt32) := do
  let a := p.as
  let mut rt := p.to.reg
  if p.to.type == .NONE then rt := REGZERO
  let mut r := p.reg
  if r == 0 then r := rt
  if r == REG_RSP then diag p "illegal source register"
  let mut mode : Nat := 64
  let mut v := Go.u64 p.from_.offset
  match p.as with
  | .ANDW | .ORRW | .EORW | .ANDSW | .TSTW => mode := 32
  | .BIC | .ORN | .EON | .BICS => v := ~~~v
  | .BICW | .ORNW | .EONW | .BICSW =>
    v := ~~~v
    mode := 32
  | _ => pure ()
  let mut o1 ← opirr p a
  o1 := o1 ||| bitconEncode v mode ||| (r31 r <<< 5) ||| r31 rt
  return #[o1]

/-- Case 54, floating point arith (`asm7.go:4595-4603`). -/
def c54 (p : Prog) : AsmM (Array UInt32) := do
  let rt := p.to.reg
  let mut r := p.reg
  let mut rf := p.from_.reg
  let o1 ← oprrr p p.as 0 0 0
  if o1 &&& ((0x1F : UInt32) <<< 24) == ((0x1E : UInt32) <<< 24) && o1 &&& ((1 : UInt32) <<< 11) == 0 then -- monadic
    r := rf
    rf := 0
  else if r == 0 then
    r := rt
  let o1 ← oprrr p p.as rt r rf
  return #[o1]

/-- Case 55, floating-point constant (`asm7.go:4605-4615`). -/
def c55 (p : Prog) : AsmM (Array UInt32) := do
  let mut o1 : UInt32 := ((0xf : UInt32) <<< 25) ||| ((1 : UInt32) <<< 21) ||| ((1 : UInt32) <<< 12)
  let rf := chipfloat7 (← fval p p.from_)
  if rf < 0 then diag p "invalid floating-point immediate"
  if p.as == .FMOVD then o1 := o1 ||| ((1 : UInt32) <<< 22)
  o1 := o1 ||| ((Go.u32 rf &&& 0xff) <<< 13) ||| r31 p.to.reg
  return #[o1]

/-- Case 56, floating point compare (`asm7.go:4617-4623`). -/
def c56 (p : Prog) : AsmM (Array UInt32) := do
  let r := p.reg
  let mut rf := p.from_.reg
  let mut o1 : UInt32 := 0
  if p.from_.type == .FCONST then
    o1 := o1 ||| 8 -- zero
    rf := 0
  o1 := o1 ||| (← oprrr p p.as 0 r rf)
  return #[o1]

/-- Case 57, floating point conditional compare (`asm7.go:4625-4643`). -/
def c57 (p : Prog) : AsmM (Array UInt32) := do
  let mut cond := p.from_.offset
  if cond < SPOP_EQ || cond > SPOP_NV then
    diag p "invalid condition"
  else
    cond := cond - SPOP_EQ
  let nzcv := p.to.offset
  if Go.u64 nzcv &&& ~~~0xF != 0 then diag p "implausible condition"
  let f3 ← match getFrom3 p with
    | some f3 => if f3.reg < REG_F0 || f3.reg > REG_F31 then diag p "illegal FCCMP" else pure f3
    | none => diag p "illegal FCCMP"
  let mut o1 ← oprrr p p.as 0 f3.reg p.reg
  o1 := o1 ||| ((Go.u32 cond &&& 15) <<< 12) ||| Go.u32 nzcv
  return #[o1]

/-- Case 58, `ldar/ldarb/ldarh/ldaxp/ldxp/ldaxr/ldxr` (`asm7.go:4645-4658`). -/
def c58 (p : Prog) : AsmM (Array UInt32) := do
  let mut o1 ← opload p p.as
  o1 := o1 ||| ((0x1F : UInt32) <<< 16)
  o1 := o1 ||| (r31 p.from_.reg <<< 5)
  if p.as == .LDXP || p.as == .LDXPW || p.as == .LDAXP || p.as == .LDAXPW then
    if p.to.reg == p.to.offset then diag p "constrained unpredictable behavior"
    o1 := o1 ||| ((Go.u32 p.to.offset &&& 31) <<< 10)
  else
    o1 := o1 ||| ((0x1F : UInt32) <<< 10)
  o1 := o1 ||| r31 p.to.reg
  return #[o1]

/-- Case 59, `stxr/stlxr/stxp/stlxp` (`asm7.go:4660-4687`). -/
def c59 (p : Prog) : AsmM (Array UInt32) := do
  let pp := p
  let s := pp.regTo2
  let n := pp.to.reg
  let t := pp.from_.reg
  if isSTLXRop pp.as then
    if s == t || (s == n && n != REGSP) then diag pp "constrained unpredictable behavior"
  else if isSTXPop pp.as then
    let t2 := Go.i16 pp.from_.offset
    if (s == t || s == t2) || (s == n && n != REGSP) then
      diag pp "constrained unpredictable behavior"
  if s == REG_RSP then diag pp "illegal destination register"
  let mut o1 ← opstore pp pp.as
  if pp.regTo2 != 0 then
    o1 := o1 ||| (r31 pp.regTo2 <<< 16)
  else
    o1 := o1 ||| ((0x1F : UInt32) <<< 16)
  if isSTXPop pp.as then
    o1 := o1 ||| ((Go.u32 pp.from_.offset &&& 31) <<< 10)
  o1 := o1 ||| (r31 pp.to.reg <<< 5) ||| r31 pp.from_.reg
  return #[o1]

/-- Case 60, `adrp label,r` (`asm7.go:4689-4692`). -/
def c60 (p : Nat) (pp : Prog) : AsmM (Array UInt32) := do
  let d ← brdist p 12 21 0
  return #[ADR 1 (Go.u32 d) (Go.u32 pp.to.reg)]

/-- Case 61, `adr label, r` (`asm7.go:4694-4697`). -/
def c61 (p : Nat) (pp : Prog) : AsmM (Array UInt32) := do
  let d ← brdist p 0 21 0
  return #[ADR 0 (Go.u32 d) (Go.u32 pp.to.reg)]

/-- Case 62, `op $movcon, [R], R -> mov $movcon, REGTMP + op REGTMP, [R], R`
(`asm7.go:4699-4726`). -/
def c62 (p : Prog) : AsmM (Array UInt32) := do
  if p.reg == REGTMP then diag p "cannot use REGTMP as source"
  if p.to.reg == REG_RSP && isADDSop p.as then diag p "illegal destination register"
  let mut lsl0 := W.LSL0_64
  let mut o1 : UInt32 := 0
  if isADDWop p.as || isANDWop p.as then
    o1 ← omovconst .MOVW p p.from_ REGTMP
    lsl0 := W.LSL0_32
  else
    o1 ← omovconst .MOVD p p.from_ REGTMP
  let mut rt := p.to.reg
  let mut r := p.reg
  let rf := REGTMP
  if p.to.type == .NONE then rt := REGZERO
  if r == 0 then r := rt
  let mut o2 : UInt32 := 0
  if rt == REGSP || r == REGSP then
    o2 ← opxrrr p p.as rt r rf false
    o2 := o2 ||| lsl0
  else
    o2 ← oprrr p p.as rt r rf
  return #[o1, o2]

/-- Case 63, `op Vm.<t>, Vn.<T>, Vd.<T>` (`asm7.go:4728-4740`). -/
def c63 (p : Prog) : AsmM (Array UInt32) := do
  let rt := p.to.reg
  let r := p.reg
  let rf := p.from_.reg
  let af := arng rf
  let aT := arng rt
  let ar := arng r
  let sz := if p.as == .SHA512SU1 then ARNG_2D else ARNG_4S
  if af != aT || af != ar || af != sz then diag p "invalid arrangement"
  let o1 : UInt32 := 0 ||| (← oprrr p p.as rt r rf)
  return #[o1]

/-- Case 64, `movT R,addr -> adrp + movT R, (REGTMP)` (`asm7.go:4743-4764`). -/
def c64 (p : Nat) (pp : Prog) (o : ARM64.Optab) : AsmM (Array UInt32) := do
  if pp.from_.reg == REGTMP then diag pp "cannot use REGTMP as source"
  let o1 := ADR 1 0 (Go.u32 REGTMP)
  let mut o2 : UInt32 := 0
  let mut o3 : UInt32 := 0
  let mut typ := ""
  -- For unaligned access, fall back to adrp + add + movT R, (REGTMP).
  if (← optabSize o p) != 8 then
    o2 := (← opirr pp .ADD) ||| (r31 REGTMP <<< 5) ||| r31 REGTMP
    o3 ← olsr12u pp (← opstr p pp.as) 0 REGTMP pp.from_.reg
    typ := "R_ADDRARM64"
  else
    o2 ← olsr12u pp (← opstr p pp.as) 0 REGTMP pp.from_.reg
    typ ← addrRelocType p
  addRel typ 8 pp.to.sym pp.to.offset
  return #[o1, o2, o3]

/-- Case 65, `movT addr,R -> adrp + movT (REGTMP), R` (`asm7.go:4766-4784`). -/
def c65 (p : Nat) (pp : Prog) (o : ARM64.Optab) : AsmM (Array UInt32) := do
  let o1 := ADR 1 0 (Go.u32 REGTMP)
  let mut o2 : UInt32 := 0
  let mut o3 : UInt32 := 0
  let mut typ := ""
  -- For unaligned access, fall back to adrp + add + movT (REGTMP), R.
  if (← optabSize o p) != 8 then
    o2 := (← opirr pp .ADD) ||| (r31 REGTMP <<< 5) ||| r31 REGTMP
    o3 ← olsr12u pp (← opldr pp pp.as) 0 REGTMP pp.to.reg
    typ := "R_ADDRARM64"
  else
    o2 ← olsr12u pp (← opldr pp pp.as) 0 REGTMP pp.to.reg
    typ ← addrRelocType p
  addRel typ 8 pp.from_.sym pp.from_.offset
  return #[o1, o2, o3]

/-- Case 66, `ldp O(R)!, (r1, r2); ldp (R)O!, (r1, r2)` (`asm7.go:4786-4795`). -/
def c66 (p : Nat) (pp : Prog) (o : ARM64.Optab) : AsmM (Array UInt32) := do
  let mut rf := pp.from_.reg
  let rt1 := pp.to.reg
  let rt2 := Go.i16 pp.to.offset
  if rf == 0 then rf := o.param
  if rf == 0 then diag pp "invalid ldp source"
  let v ← regoff pp.from_
  return #[← opldpstp p o v rf rt1 rt2 1]

/-- Case 67, `stp (r1, r2), O(R)!; stp (r1, r2), (R)O!` (`asm7.go:4797-4806`). -/
def c67 (p : Nat) (pp : Prog) (o : ARM64.Optab) : AsmM (Array UInt32) := do
  let mut rt := pp.to.reg
  let rf1 := pp.from_.reg
  let rf2 := Go.i16 pp.from_.offset
  if rt == 0 then rt := o.param
  if rt == 0 then diag pp "invalid stp destination"
  let v ← regoff pp.to
  return #[← opldpstp p o v rt rf1 rf2 0]

/-- Case 68, `movT $vconaddr(SB), reg -> adrp + add + reloc` (`asm7.go:4808-4822`). -/
def c68 (p : Prog) : AsmM (Array UInt32) := do
  if p.as == .MOVW then diag p "invalid load of 32-bit address"
  let o1 := ADR 1 0 (Go.u32 p.to.reg)
  let o2 := (← opirr p .ADD) ||| (r31 p.to.reg <<< 5) ||| r31 p.to.reg
  addRel "R_ADDRARM64" 8 p.from_.sym p.from_.offset
  return #[o1, o2]

/-- Case 69, LE model `movd $tlsvar, reg -> movz reg, 0 + reloc` (`asm7.go:4824-4835`). -/
def c69 (p : Prog) : AsmM (Array UInt32) := do
  let mut o1 ← opirr p .MOVZ
  o1 := o1 ||| r31 p.to.reg
  addRel "R_ARM64_TLS_LE" 4 p.from_.sym 0
  if p.from_.offset != 0 then diag p "invalid offset on MOVW $tlsvar"
  return #[o1]

/-- Case 70, IE model `movd $tlsvar, reg -> adrp REGTMP, 0; ldr reg, [REGTMP, #0] + relocs`
(`asm7.go:4837-4848`). -/
def c70 (p : Prog) : AsmM (Array UInt32) := do
  let o1 := ADR 1 0 (Go.u32 REGTMP)
  let o2 ← olsr12u p (← opldr p .MOVD) 0 REGTMP p.to.reg
  addRel "R_ARM64_TLS_IE" 8 p.from_.sym 0
  if p.from_.offset != 0 then diag p "invalid offset on MOVW $tlsvar"
  return #[o1, o2]

/-- Case 71, `movd sym@GOT, reg -> adrp REGTMP, #0; ldr reg, [REGTMP, #0] + relocs`
(`asm7.go:4850-4858`). -/
def c71 (p : Prog) : AsmM (Array UInt32) := do
  let o1 := ADR 1 0 (Go.u32 REGTMP)
  let o2 ← olsr12u p (← opldr p .MOVD) 0 REGTMP p.to.reg
  addRel "R_ARM64_GOTPCREL" 8 p.from_.sym 0
  return #[o1, o2]

/-- `Q, size` of the integer arrangements (cases 72, 83; `asm7.go:4871-4895, 5263-5287`). -/
private def qSize (p : Prog) (af : Int) : AsmM (UInt32 × UInt32) :=
  if af == ARNG_8B then pure (0, 0)
  else if af == ARNG_16B then pure (1, 0)
  else if af == ARNG_4H then pure (0, 1)
  else if af == ARNG_8H then pure (1, 1)
  else if af == ARNG_2S then pure (0, 2)
  else if af == ARNG_4S then pure (1, 2)
  else if af == ARNG_2D then pure (1, 3)
  else diag p "invalid arrangement"

/-- The floating-point vector opcodes of case 72's arrangement checks (`asm7.go:4902`). -/
private def isVFArith : As → Bool
  | .VFMLA | .VFMLS | .VFCMEQ | .VFCMGE | .VFCMGT | .VFADD | .VFSUB | .VFMUL | .VFDIV
  | .VFMAX | .VFMAXNM | .VFMAXP | .VFADDP | .VFMIN | .VFMINNM | .VFMINP | .VFMAXNMP
  | .VFMINNMP => true
  | _ => false

/-- Case 72, `vaddp/vand/vcmeq/… Vm.<T>, Vn.<T>, Vd.<T>` (`asm7.go:4860-4933`). -/
def c72 (p : Prog) : AsmM (Array UInt32) := do
  let af := arng p.from_.reg
  let af3 := arng p.reg
  let aT := arng p.to.reg
  if af != af3 || af != aT then diag p "operand mismatch"
  let (q0, size0) ← qSize p af
  let mut q := q0
  let mut size := size0
  match p.as with
  | .VORR | .VAND | .VEOR | .VBIT | .VBSL | .VBIF | .VBIC | .VORN =>
    if af != ARNG_16B && af != ARNG_8B then diag p "invalid arrangement"
  | .VUMAX | .VUMIN | .VUMAXP | .VUMINP | .VMUL | .VMLA | .VMLS | .VSMAX | .VSMIN | .VSMAXP
  | .VSMINP =>
    if af == ARNG_2D then diag p "invalid arrangement"
  | a =>
    if isVFArith a then
      if af != ARNG_2D && af != ARNG_2S && af != ARNG_4S then diag p "invalid arrangement"
  match p.as with
  | .VAND | .VEOR | .VBIC | .VORN => size := 0
  | .VBSL => size := 1
  | .VORR | .VBIT | .VBIF => size := 2
  | .VRAX1 =>
    if af != ARNG_2D then diag p "invalid arrangement"
    size := 0
    q := 0
  | a =>
    if isVFArith a then
      size := if af == ARNG_2D then 1 else 0
  let mut o1 ← oprrr p p.as p.to.reg p.reg p.from_.reg
  o1 := o1 ||| ((q &&& 1) <<< 30) ||| ((size &&& 3) <<< 22)
  return #[o1]

/-- `imm5` of an element index (cases 73, 78, 80; `asm7.go:4941-4961`): the element size bit
and `index` above it, after `checkindex`; `none` for a non-element arrangement. -/
private def elemImm5 (p : Prog) (arr : Int) (index : Int) : AsmM (Option UInt32) := do
  if arr == ARNG_B then
    checkindex p index 15
    return some ((1 : UInt32) ||| (Go.u32 index <<< 1))
  else if arr == ARNG_H then
    checkindex p index 7
    return some ((2 : UInt32) ||| (Go.u32 index <<< 2))
  else if arr == ARNG_S then
    checkindex p index 3
    return some ((4 : UInt32) ||| (Go.u32 index <<< 3))
  else if arr == ARNG_D then
    checkindex p index 1
    return some ((8 : UInt32) ||| (Go.u32 index <<< 4))
  else
    return none

/-- Case 73, `vmov V.<T>[index], R` (`asm7.go:4935-4962`). -/
def c73 (p : Prog) : AsmM (Array UInt32) := do
  let rf := p.from_.reg
  let rt := p.to.reg
  let mut o1 : UInt32 := ((7 : UInt32) <<< 25) ||| ((0xf : UInt32) <<< 10)
  let index := p.from_.index
  let arr := arng p.from_.reg
  let imm5 ← match ← elemImm5 p arr index with
    | some i => pure i
    | none => diag p "invalid arrangement"
  if arr == ARNG_D then o1 := o1 ||| ((1 : UInt32) <<< 30)
  o1 := o1 ||| ((imm5 &&& 0x1f) <<< 16) ||| (r31 rf <<< 5) ||| r31 rt
  return #[o1]

/-- Case 74, `add $O, R, Rtmp or sub $O, R, Rtmp; ldp (Rtmp), (R1, R2)`
(`asm7.go:4964-4976`). -/
def c74 (p : Nat) (pp : Prog) (o : ARM64.Optab) : AsmM (Array UInt32) := do
  let mut rf := pp.from_.reg
  let rt1 := pp.to.reg
  let rt2 := Go.i16 pp.to.offset
  if rf == 0 then rf := o.param
  if rf == 0 then diag pp "invalid ldp source"
  let v ← regoff pp.from_
  let o1 ← oaddi12 pp v REGTMP rf
  let o2 ← opldpstp p o 0 REGTMP rt1 rt2 1
  return #[o1, o2]

/-- Case 75, `ldp` with a large offset: `add $lo, R, Rtmp; add $hi, Rtmp, Rtmp; ldp (Rtmp),
(R1, R2)`, or from the constant pool `mov $L, Rtmp; add Rtmp, R, Rtmp; ldp (Rtmp), (R1, R2)`
(`asm7.go:4978-5024`). -/
def c75 (p : Nat) (pp : Prog) (o : ARM64.Optab) : AsmM (Array UInt32) := do
  let mut rf := pp.from_.reg
  let rt1 := pp.to.reg
  let rt2 := Go.i16 pp.to.offset
  if rf == REGTMP then diag pp "REGTMP used in large offset load"
  if rf == 0 then rf := o.param
  if rf == 0 then diag pp "invalid ldp source"
  let v ← regoff pp.from_
  if v >= -4095 && v <= 4095 then
    diag pp s!"bad type for offset {v} (should be add/sub+ldp)"
  match splitImm24uScaled v 0 with
  | .ok (hi, lo) =>
    if pp.pool.isSome then diag pp s!"unused constant in pool ({v})"
    let o1 ← oaddi pp .ADD lo REGTMP rf
    let o2 ← oaddi pp .ADD hi REGTMP REGTMP
    let o3 ← opldpstp p o 0 REGTMP rt1 rt2 1
    return #[o1, o2, o3]
  | .error _ =>
    -- loadpairusepool:
    if pp.pool.isNone then diag pp "constant is not in pool"
    if rf == REGTMP || pp.from_.reg == REGTMP then diag pp "REGTMP used in large offset load"
    let o1 ← omovlit .MOVD p pp.from_ REGTMP
    let o2 ← opxrrr pp .ADD REGTMP rf REGTMP false
    let o3 ← opldpstp p o 0 REGTMP rt1 rt2 1
    return #[o1, o2, o3]

/-- Case 76, `add $O, R, Rtmp or sub $O, R, Rtmp; stp (R1, R2), (Rtmp)`
(`asm7.go:5026-5041`). -/
def c76 (p : Nat) (pp : Prog) (o : ARM64.Optab) : AsmM (Array UInt32) := do
  let mut rt := pp.to.reg
  let rf1 := pp.from_.reg
  let rf2 := Go.i16 pp.from_.offset
  if rf1 == REGTMP || rf2 == REGTMP then diag pp "cannot use REGTMP as source"
  if rt == 0 then rt := o.param
  if rt == 0 then diag pp "invalid stp destination"
  let v ← regoff pp.to
  let o1 ← oaddi12 pp v REGTMP rt
  let o2 ← opldpstp p o 0 REGTMP rf1 rf2 0
  return #[o1, o2]

/-- Case 77, `stp` with a large offset, as case 75 (`asm7.go:5043-5089`). -/
def c77 (p : Nat) (pp : Prog) (o : ARM64.Optab) : AsmM (Array UInt32) := do
  let mut rt := pp.to.reg
  let rf1 := pp.from_.reg
  let rf2 := Go.i16 pp.from_.offset
  if rt == REGTMP || rf1 == REGTMP || rf2 == REGTMP then
    diag pp "REGTMP used in large offset store"
  if rt == 0 then rt := o.param
  if rt == 0 then diag pp "invalid stp destination"
  let v ← regoff pp.to
  if v >= -4095 && v <= 4095 then
    diag pp s!"bad type for offset {v} (should be add/sub+stp)"
  match splitImm24uScaled v 0 with
  | .ok (hi, lo) =>
    if pp.pool.isSome then diag pp s!"unused constant in pool ({v})"
    let o1 ← oaddi pp .ADD lo REGTMP rt
    let o2 ← oaddi pp .ADD hi REGTMP REGTMP
    let o3 ← opldpstp p o 0 REGTMP rf1 rf2 0
    return #[o1, o2, o3]
  | .error _ =>
    -- storepairusepool:
    if pp.pool.isNone then diag pp "constant is not in pool"
    if rt == REGTMP || pp.from_.reg == REGTMP then diag pp "REGTMP used in large offset store"
    let o1 ← omovlit .MOVD p pp.to REGTMP
    let o2 ← opxrrr pp .ADD REGTMP rt REGTMP false
    let o3 ← opldpstp p o 0 REGTMP rf1 rf2 0
    return #[o1, o2, o3]

/-- Case 78, `vmov R, V.<T>[index]` (`asm7.go:5091-5117`). -/
def c78 (p : Prog) : AsmM (Array UInt32) := do
  let rf := p.from_.reg
  let rt := p.to.reg
  let mut o1 : UInt32 := ((1 : UInt32) <<< 30) ||| ((7 : UInt32) <<< 25) ||| ((7 : UInt32) <<< 10)
  let index := p.to.index
  let imm5 ← match ← elemImm5 p (arng p.to.reg) index with
    | some i => pure i
    | none => diag p "invalid arrangement"
  o1 := o1 ||| ((imm5 &&& 0x1f) <<< 16) ||| (r31 rf <<< 5) ||| r31 rt
  return #[o1]

/-- Case 79, `vdup Vn.<T>[index], Vd.<T>` (`asm7.go:5119-5165`). -/
def c79 (p : Prog) : AsmM (Array UInt32) := do
  let rf := p.from_.reg
  let rt := p.to.reg
  let mut o1 : UInt32 := ((7 : UInt32) <<< 25) ||| ((1 : UInt32) <<< 10)
  let index := p.from_.index
  let aT := arng p.to.reg
  let (q, imm5) : UInt32 × UInt32 ←
    if aT == ARNG_16B then do checkindex p index 15; pure (1, (1 : UInt32) ||| (Go.u32 index <<< 1))
    else if aT == ARNG_2D then do checkindex p index 1; pure (1, (8 : UInt32) ||| (Go.u32 index <<< 4))
    else if aT == ARNG_2S then do checkindex p index 3; pure (0, (4 : UInt32) ||| (Go.u32 index <<< 3))
    else if aT == ARNG_4H then do checkindex p index 7; pure (0, (2 : UInt32) ||| (Go.u32 index <<< 2))
    else if aT == ARNG_4S then do checkindex p index 3; pure (1, (4 : UInt32) ||| (Go.u32 index <<< 3))
    else if aT == ARNG_8B then do checkindex p index 15; pure (0, (1 : UInt32) ||| (Go.u32 index <<< 1))
    else if aT == ARNG_8H then do checkindex p index 7; pure (1, (2 : UInt32) ||| (Go.u32 index <<< 2))
    else diag p "invalid arrangement"
  o1 := o1 ||| ((q &&& 1) <<< 30) ||| ((imm5 &&& 0x1f) <<< 16)
  o1 := o1 ||| (r31 rf <<< 5) ||| r31 rt
  return #[o1]

/-- Case 80, `vmov/vdup V.<T>[index], Vn` (`asm7.go:5167-5198`). -/
def c80 (p : Prog) : AsmM (Array UInt32) := do
  let rf := p.from_.reg
  let rt := p.to.reg
  let index := p.from_.index
  match p.as with
  | .VMOV | .VDUP =>
    let mut o1 : UInt32 := ((1 : UInt32) <<< 30) ||| ((15 : UInt32) <<< 25) ||| ((1 : UInt32) <<< 10)
    let imm5 ← match ← elemImm5 p (arng p.from_.reg) index with
      | some i => pure i
      | none => diag p "invalid arrangement"
    o1 := o1 ||| ((imm5 &&& 0x1f) <<< 16) ||| (r31 rf <<< 5) ||| r31 rt
    return #[o1]
  | _ => throw s!"asmout: unsupported op {p.as.name}"

/-- Case 81, `vld[1-4]|vld[1-4]r (Rn), [Vt1.<T>, Vt2.<T>, ...]` (`asm7.go:5200-5220`). -/
def c81 (p : Nat) (pp : Prog) (o : ARM64.Optab) : AsmM (Array UInt32) := do
  checkoffset p pp.as
  let rn := pp.from_.reg
  let mut o1 ← oprrr pp pp.as 0 rn 0
  if (o.scond : Int) == C_XPOST then
    o1 := o1 ||| ((1 : UInt32) <<< 23)
    if pp.from_.index == 0 then
      -- immediate offset variant
      o1 := o1 ||| ((0x1f : UInt32) <<< 16)
    else
      -- register offset variant
      if isRegShiftOrExt pp.from_ then diag pp "invalid extended register op"
      o1 := o1 ||| ((Go.u32 pp.from_.index &&& 0x1f) <<< 16)
  o1 := o1 ||| Go.u32 pp.to.offset
  -- RegisterListOffset; add opcode(bit 12-15) for vld1, mask it off if it's not vld1
  o1 ← maskOpvldvst p o1
  return #[o1]

/-- Case 82, `vmov/vdup Rn, Vd.<T>` (`asm7.go:5222-5253`). -/
def c82 (p : Prog) : AsmM (Array UInt32) := do
  let rf := p.from_.reg
  let rt := p.to.reg
  let mut o1 : UInt32 := ((7 : UInt32) <<< 25) ||| ((3 : UInt32) <<< 10)
  let aT := arng p.to.reg
  let (q, imm5) : UInt32 × UInt32 ←
    if aT == ARNG_16B then pure (1, 1)
    else if aT == ARNG_2D then pure (1, 8)
    else if aT == ARNG_2S then pure (0, 4)
    else if aT == ARNG_4H then pure (0, 2)
    else if aT == ARNG_4S then pure (1, 4)
    else if aT == ARNG_8B then pure (0, 1)
    else if aT == ARNG_8H then pure (1, 2)
    else diag p "invalid arrangement"
  o1 := o1 ||| ((q &&& 1) <<< 30) ||| ((imm5 &&& 0x1f) <<< 16)
  o1 := o1 ||| (r31 rf <<< 5) ||| r31 rt
  return #[o1]

/-- Case 83, `vmov Vn.<T>, Vd.<T>` (`asm7.go:5255-5335`). -/
def c83 (p : Prog) : AsmM (Array UInt32) := do
  let af := arng p.from_.reg
  let aT := arng p.to.reg
  if af != aT then diag p "invalid arrangement"
  let (q, size0) ← qSize p af
  let mut size := size0
  let as := p.as
  if (as == .VMOV || as == .VRBIT || as == .VCNT) && (af != ARNG_16B && af != ARNG_8B) then
    diag p "invalid arrangement"
  if as == .VREV32 && (af == ARNG_2S || af == ARNG_4S) then diag p "invalid arrangement"
  if as == .VREV16 && af != ARNG_8B && af != ARNG_16B then diag p "invalid arrangement"
  if as == .VNOT && (af != ARNG_8B && af != ARNG_16B) then diag p "invalid arrangement"
  -- VCLS and VCLZ only support integer arrangements (B, H, S), not D arrangements
  if (as == .VCLS || as == .VCLZ) && (af == ARNG_1D || af == ARNG_2D) then
    diag p "invalid arrangement"
  -- Floating-point instructions only allow floating-point arrangements
  -- and use 1-bit size field: 0 for S arrangements, 1 for D arrangements
  if as == .VFABS || as == .VFNEG || as == .VFSQRT ||
      as == .VFRINTN || as == .VFRINTP || as == .VFRINTM || as == .VFRINTZ ||
      as == .VFCVTZS || as == .VFCVTZU || as == .VSCVTF || as == .VUCVTF then
    if af != ARNG_2S && af != ARNG_4S && af != ARNG_2D then diag p "invalid arrangement"
    -- Override size for floating-point instructions: 0 for S, 1 for D
    if af == ARNG_2S || af == ARNG_4S then size := 0
    else if af == ARNG_2D then size := 1
  if as == .VRBIT then size := 1
  let rt := p.to.reg
  let mut r : Int := 0
  let rf := p.from_.reg
  if as == .VMOV then r := rf
  let mut o1 ← oprrr p p.as rt rf r
  o1 := o1 ||| ((q &&& 1) <<< 30) ||| ((size &&& 3) <<< 22)
  return #[o1]

/-- Case 84, `vst[1-4] [Vt1.<T>, Vt2.<T>, ...], (Rn)` (`asm7.go:5337-5358`). -/
def c84 (p : Nat) (pp : Prog) (o : ARM64.Optab) : AsmM (Array UInt32) := do
  checkoffset p pp.as
  let r := pp.to.reg
  let mut o1 : UInt32 := (3 : UInt32) <<< 26
  if (o.scond : Int) == C_XPOST then
    o1 := o1 ||| ((1 : UInt32) <<< 23)
    if pp.to.index == 0 then
      -- immediate offset variant
      o1 := o1 ||| ((0x1f : UInt32) <<< 16)
    else
      -- register offset variant
      if isRegShiftOrExt pp.to then diag pp "invalid extended register"
      o1 := o1 ||| ((Go.u32 pp.to.index &&& 31) <<< 16)
  o1 := o1 ||| Go.u32 pp.from_.offset
  -- RegisterListOffset; add opcode(bit 12-15) for vst1, mask it off if it's not vst1
  o1 ← maskOpvldvst p o1
  o1 := o1 ||| (r31 r <<< 5)
  return #[o1]

/-- Case 85, `vaddv/vuaddlv Vn.<T>, Vd` (`asm7.go:5360-5392`). -/
def c85 (p : Prog) : AsmM (Array UInt32) := do
  let af := arng p.from_.reg
  let (q, size0) : UInt32 × UInt32 ←
    if af == ARNG_8B then pure (0, 0)
    else if af == ARNG_16B then pure (1, 0)
    else if af == ARNG_4H then pure (0, 1)
    else if af == ARNG_8H then pure (1, 1)
    else if af == ARNG_4S then pure (1, 2)
    else diag p "invalid arrangement"
  let mut size := size0
  match p.as with
  -- Floating-point reduction instructions only support .S4 arrangement and don't have a size
  -- field.
  | .VFMAXV | .VFMINV | .VFMAXNMV | .VFMINNMV =>
    if af != ARNG_4S then diag p "invalid arrangement"
    size := 0
  | _ => pure ()
  let mut o1 ← oprrr p p.as p.to.reg p.from_.reg 0
  o1 := o1 ||| ((q &&& 1) <<< 30) ||| ((size &&& 3) <<< 22)
  return #[o1]

/-- Case 86, `vmovi $imm8, Vd.<T>` (`asm7.go:5394-5411`). -/
def c86 (p : Prog) : AsmM (Array UInt32) := do
  let aT := arng p.to.reg
  let r := p.from_.offset
  if r > 255 || r < 0 then diag p "immediate constant out of range"
  let rt := p.to.reg
  let q : UInt32 ←
    if aT == ARNG_8B then pure 0
    else if aT == ARNG_16B then pure 1
    else diag p "invalid arrangement"
  let mut o1 : UInt32 := ((0xf : UInt32) <<< 24) ||| ((0xe : UInt32) <<< 12) ||| ((1 : UInt32) <<< 10)
  o1 := o1 ||| ((q &&& 1) <<< 30) ||| (((Go.u32 r >>> 5) &&& 7) <<< 16) |||
    ((Go.u32 r &&& 0x1f) <<< 5) ||| r31 rt
  return #[o1]

/-- Case 87, `stp (r,r), addr(SB) -> adrp + add + stp` (`asm7.go:5413-5427`). -/
def c87 (p : Nat) (pp : Prog) (o : ARM64.Optab) : AsmM (Array UInt32) := do
  let rf1 := pp.from_.reg
  let rf2 := Go.i16 pp.from_.offset
  if rf1 == REGTMP || rf2 == REGTMP then diag pp "cannot use REGTMP as source"
  let o1 := ADR 1 0 (Go.u32 REGTMP)
  let o2 := (← opirr pp .ADD) ||| (r31 REGTMP <<< 5) ||| r31 REGTMP
  addRel "R_ADDRARM64" 8 pp.to.sym pp.to.offset
  let o3 ← opldpstp p o 0 REGTMP rf1 rf2 0
  return #[o1, o2, o3]

/-- Case 88, `ldp addr(SB), (r,r) -> adrp + add + ldp` (`asm7.go:5429-5440`). -/
def c88 (p : Nat) (pp : Prog) (o : ARM64.Optab) : AsmM (Array UInt32) := do
  let rt1 := pp.to.reg
  let rt2 := Go.i16 pp.to.offset
  let o1 := ADR 1 0 (Go.u32 REGTMP)
  let o2 := (← opirr pp .ADD) ||| (r31 REGTMP <<< 5) ||| r31 REGTMP
  addRel "R_ADDRARM64" 8 pp.from_.sym pp.from_.offset
  let o3 ← opldpstp p o 0 REGTMP rt1 rt2 1
  return #[o1, o2, o3]

/-- Case 89, `vadd/vsub Vm, Vn, Vd` (`asm7.go:5442-5461`). -/
def c89 (p : Prog) : AsmM (Array UInt32) := do
  let mut o1 : UInt32 ← match p.as with
    | .VADD => pure (((5 : UInt32) <<< 28) ||| ((7 : UInt32) <<< 25) ||| ((7 : UInt32) <<< 21) ||| ((1 : UInt32) <<< 15) ||| ((1 : UInt32) <<< 10))
    | .VSUB => pure (((7 : UInt32) <<< 28) ||| ((7 : UInt32) <<< 25) ||| ((7 : UInt32) <<< 21) ||| ((1 : UInt32) <<< 15) ||| ((1 : UInt32) <<< 10))
    | _ => diag p "bad opcode"
  let rf := p.from_.reg
  let rt := p.to.reg
  let mut r := p.reg
  if r == 0 then r := rt
  o1 := o1 ||| (r31 rf <<< 16) ||| (r31 r <<< 5) ||| r31 rt
  return #[o1]

/-- Case 91, `prfm imm(Rn), <prfop | $imm5>` (`asm7.go:5471-5487`). -/
def c91 (p : Prog) : AsmM (Array UInt32) := do
  let imm := Go.u32 p.from_.offset
  let r := p.from_.reg
  let (v, ok) : UInt32 × Bool :=
    if p.to.type == .CONST then
      let v := Go.u32 p.to.offset
      (v, v ≤ 31)
    else
      match ARM64.prfopfield p.to.offset with
      | some v => (v, true)
      | none => (0, false)
  if !ok then diag p "illegal prefetch operation"
  let mut o1 ← opirr p p.as
  o1 := o1 ||| (r31 r <<< 5) ||| (((imm >>> 3) &&& 0xfff) <<< 10) ||| (v &&& 31)
  return #[o1]

/-- Case 92, `vmov Vn.<T>[index], Vd.<T>[index]` (`asm7.go:5489-5528`). -/
def c92 (p : Prog) : AsmM (Array UInt32) := do
  let rf := p.from_.reg
  let rt := p.to.reg
  let mut o1 : UInt32 := ((3 : UInt32) <<< 29) ||| ((7 : UInt32) <<< 25) ||| ((1 : UInt32) <<< 10)
  let index1 := p.to.index
  let index2 := p.from_.index
  if arng p.to.reg != arng p.from_.reg then diag p "operand mismatch"
  let aT := arng p.to.reg
  let (imm5, imm4) : UInt32 × UInt32 ←
    if aT == ARNG_B then do
      checkindex p index1 15
      checkindex p index2 15
      pure ((1 : UInt32) ||| (Go.u32 index1 <<< 1), Go.u32 index2)
    else if aT == ARNG_H then do
      checkindex p index1 7
      checkindex p index2 7
      pure ((2 : UInt32) ||| (Go.u32 index1 <<< 2), Go.u32 index2 <<< 1)
    else if aT == ARNG_S then do
      checkindex p index1 3
      checkindex p index2 3
      pure ((4 : UInt32) ||| (Go.u32 index1 <<< 3), Go.u32 index2 <<< 2)
    else if aT == ARNG_D then do
      checkindex p index1 1
      checkindex p index2 1
      pure ((8 : UInt32) ||| (Go.u32 index1 <<< 4), Go.u32 index2 <<< 3)
    else diag p "invalid arrangement"
  o1 := o1 ||| ((imm5 &&& 0x1f) <<< 16) ||| ((imm4 &&& 0xf) <<< 11) ||| (r31 rf <<< 5) |||
    r31 rt
  return #[o1]

/-- Case 93, `vpmull{2}/v(s|u)(mla|mls|mul)l{2} Vm.<Tb>, Vn.<Tb>, Vd.<Ta>`
(`asm7.go:5530-5565`). -/
def c93 (p : Prog) : AsmM (Array UInt32) := do
  let af := (arng p.from_.reg).toNat
  let aT := (arng p.to.reg).toNat
  let a := (arng p.reg).toNat
  if af != a then diag p "invalid arrangement"
  let q : UInt32 := match p.as with
    | .VPMULL2 | .VSMLAL2 | .VSMLSL2 | .VSMULL2 | .VUMLAL2 | .VUMLSL2 | .VUMULL2 => 1
    | _ => 0
  let k := pack q aT af
  let A (x : Int) : Nat := x.toNat
  let size : UInt32 ←
    if k == pack 0 (A ARNG_8H) (A ARNG_8B) || k == pack 1 (A ARNG_8H) (A ARNG_16B) then pure 0
    else if k == pack 0 (A ARNG_4S) (A ARNG_4H) || k == pack 1 (A ARNG_4S) (A ARNG_8H) then
      pure 1
    else if k == pack 0 (A ARNG_2D) (A ARNG_2S) || k == pack 1 (A ARNG_2D) (A ARNG_4S) then
      pure 2
    else if k == pack 0 (A ARNG_1Q) (A ARNG_1D) || k == pack 1 (A ARNG_1Q) (A ARNG_2D) then
      pure 3
    else diag p "operand mismatch"
  if p.as == .VPMULL || p.as == .VPMULL2 then
    if size != 0 && size != 3 then diag p "invalid arrangement"
  else if size == 3 then
    diag p "invalid arrangement"
  let mut o1 ← oprrr p p.as p.to.reg p.reg p.from_.reg
  o1 := o1 ||| ((q &&& 1) <<< 30) ||| ((size &&& 3) <<< 22)
  return #[o1]

/-- Case 94, `vext $imm4, Vm.<T>, Vn.<T>, Vd.<T>` (`asm7.go:5567-5600`). -/
def c94 (p : Prog) : AsmM (Array UInt32) := do
  let f3 ← from3! p
  let af := arng f3.reg
  let aT := arng p.to.reg
  let a := arng p.reg
  let index := p.from_.offset
  if af != a || af != aT then diag p "invalid arrangement"
  let (q, b) : UInt32 × Int ←
    if af == ARNG_8B then pure (0, 7)
    else if af == ARNG_16B then pure (1, 15)
    else diag p "invalid arrangement, should be B8 or B16"
  if index < 0 || index > b then diag p "illegal offset"
  let mut o1 ← opirr p p.as
  let rf := f3.reg
  let rt := p.to.reg
  let r := p.reg
  o1 := o1 ||| ((q &&& 1) <<< 30) ||| (r31 r <<< 16) ||| ((Go.u32 index &&& 15) <<< 11) |||
    (r31 rf <<< 5) ||| r31 rt
  return #[o1]

/-- Case 95, shifts `vushr/vshl/vsri/vsli/vusra/vsshr/vsrshr $shift, Vn.<T>, Vd.<T>`, narrowing
shifts `vshrn[2]` and truncations `vxtn/v{s,u}qxt{n,un}/vfcvtn[2]` (`asm7.go:5602-5697`). -/
def c95 (p : Prog) : AsmM (Array UInt32) := do
  let as := p.as
  let aT := arng p.to.reg
  let rt := p.to.reg
  -- Truncation instructions (narrow without immediate).
  let trunc := as == .VXTN || as == .VXTN2 || as == .VSQXTN || as == .VSQXTN2 ||
    as == .VSQXTUN || as == .VSQXTUN2 || as == .VUQXTN || as == .VUQXTN2 ||
    as == .VFCVTN || as == .VFCVTN2
  let (af, rf, shift) : Int × Int × Int :=
    if trunc then (arng p.from_.reg, p.from_.reg, 0)
    else (arng p.reg, p.reg, p.from_.offset)
  let narrow := trunc || as == .VSHRN || as == .VSHRN2
  if af != aT && !narrow then
    diag p "invalid arrangement on op Vn.<T>, Vd.<T>"
  let q : UInt32 ←
    if aT == ARNG_8B || aT == ARNG_4H || aT == ARNG_2S then pure 0
    else if aT == ARNG_16B || aT == ARNG_8H || aT == ARNG_4S || aT == ARNG_2D then pure 1
    else diag p "invalid arrangement on op Vn.<T>, Vd.<T>"
  let (imax, esize, atwice) : Int × Int × Int :=
    if aT == ARNG_8B || aT == ARNG_16B then (15, 8, ARNG_8H)
    else if aT == ARNG_4H || aT == ARNG_8H then (31, 16, ARNG_4S)
    else if aT == ARNG_2S || aT == ARNG_4S then (63, 32, ARNG_2D)
    else if aT == ARNG_2D then (127, 64, -1)
    else (0, 0, -1)
  if narrow then
    let wantQ : UInt32 :=
      if as == .VXTN2 || as == .VSQXTN2 || as == .VSQXTUN2 || as == .VUQXTN2 ||
          as == .VFCVTN2 || as == .VSHRN2 then 1 else 0
    if q != wantQ || atwice != af then diag p "invalid arrangement on op"
  let mut o1 ← opirr p p.as
  if trunc && as != .VFCVTN && as != .VFCVTN2 then
    -- Integer trunc ops encode size from destination element width.
    -- FCVTN has size already in opirr base.
    let size := Go.u32 (esize >>> 4)
    o1 := o1 ||| (size <<< 22)
  -- Shift instructions: encode immediate from shift amount.
  match as with
  | .VUSHR | .VSRI | .VUSRA | .VSSHR | .VSRSHR | .VSHRN | .VSHRN2 =>
    let imm := esize * 2 - shift
    if imm < esize || imm > imax then diag p "shift out of range"
    o1 := o1 ||| ((Go.u32 imm &&& 0x7f) <<< 16)
  | .VSHL | .VSLI | .VSQSHL | .VUQSHL =>
    let imm := esize + shift
    if imm > imax then diag p "shift out of range"
    o1 := o1 ||| ((Go.u32 imm &&& 0x7f) <<< 16)
  | _ => pure ()
  o1 := o1 ||| ((q &&& 1) <<< 30) ||| (r31 rf <<< 5) ||| r31 rt
  return #[o1]

/-- `Q, S, size, opcode` of a single-element `vst1`/`vld1` (cases 96, 97;
`asm7.go:5722-5761`), after `checkindex` and the post-increment offset check. -/
private def ldst1Elem (p : Prog) (o : ARM64.Optab) (arr index offset : Int) :
    AsmM (Nat × Nat × Nat × UInt32) := do
  let xpost := (o.scond : Int) == C_XPOST
  if arr == ARNG_B then
    checkindex p index 15
    if xpost && offset != 0 && offset != 1 then diag p "invalid offset"
    let i := index.toNat
    return (i >>> 3, (i >>> 2) &&& 1, i &&& 3, 0)
  else if arr == ARNG_H then
    checkindex p index 7
    if xpost && offset != 0 && offset != 2 then diag p "invalid offset"
    let i := index.toNat
    return (i >>> 2, (i >>> 1) &&& 1, (i &&& 1) <<< 1, 2)
  else if arr == ARNG_S then
    checkindex p index 3
    if xpost && offset != 0 && offset != 4 then diag p "invalid offset"
    let i := index.toNat
    return (i >>> 1, i &&& 1, 0, 4)
  else if arr == ARNG_D then
    checkindex p index 1
    if xpost && offset != 0 && offset != 8 then diag p "invalid offset"
    return (index.toNat, 0, 1, 4)
  else
    diag p "invalid arrangement"

/-- Case 96, `vst1 Vt1.<T>[index], offset(Rn)` (`asm7.go:5699-5769`). -/
def c96 (p : Prog) (o : ARM64.Optab) : AsmM (Array UInt32) := do
  let af := arng p.from_.reg
  let rt := p.from_.reg
  let rf := p.to.reg
  let mut r := p.to.index
  let index := p.from_.index
  let offset ← regoff p.to
  if (o.scond : Int) == C_XPOST then
    if p.to.index != 0 && offset != 0 then diag p "invalid offset"
    if p.to.index == 0 && offset == 0 then diag p "invalid offset"
  if offset != 0 then r := 31
  let (q, s, size, opcode) ← ldst1Elem p o af index offset
  let mut o1 : UInt32 := 0
  if (o.scond : Int) == C_XPOST then
    o1 := o1 ||| ((27 : UInt32) <<< 23)
  else
    o1 := o1 ||| ((26 : UInt32) <<< 23)
  o1 := o1 ||| ((q.toUInt32 &&& 1) <<< 30) ||| (r31 r <<< 16) ||| ((opcode &&& 7) <<< 13) |||
    ((s.toUInt32 &&& 1) <<< 12) ||| ((size.toUInt32 &&& 3) <<< 10) ||| (r31 rf <<< 5) |||
    r31 rt
  return #[o1]

/-- Case 97, `vld1 offset(Rn), vt.<T>[index]` (`asm7.go:5771-5843`). -/
def c97 (p : Prog) (o : ARM64.Optab) : AsmM (Array UInt32) := do
  let aT := arng p.to.reg
  let rt := p.to.reg
  let rf := p.from_.reg
  let mut r := p.from_.index
  let index := p.to.index
  let offset ← regoff p.from_
  if (o.scond : Int) == C_XPOST then
    if p.from_.index != 0 && offset != 0 then diag p "invalid offset"
    if p.from_.index == 0 && offset == 0 then diag p "invalid offset"
  if offset != 0 then r := 31
  let (q, s, size, opcode) ← ldst1Elem p o aT index offset
  let mut o1 : UInt32 := 0
  if (o.scond : Int) == C_XPOST then
    o1 := o1 ||| ((110 : UInt32) <<< 21)
  else
    o1 := o1 ||| ((106 : UInt32) <<< 21)
  o1 := o1 ||| ((q.toUInt32 &&& 1) <<< 30) ||| (r31 r <<< 16) ||| ((opcode &&& 7) <<< 13) |||
    ((s.toUInt32 &&& 1) <<< 12) ||| ((size.toUInt32 &&& 3) <<< 10) ||| (r31 rf <<< 5) |||
    r31 rt
  return #[o1]

/-- Case 98, `MOVD (Rn)(Rm.SXTW[<<amount]),Rd` (`asm7.go:5845-5857`). -/
def c98 (p : Nat) (pp : Prog) : AsmM (Array UInt32) := do
  let rt := pp.to.reg
  let rf := pp.from_.reg
  if isRegShiftOrExt pp.from_ then
    -- extended or shifted offset register.
    checkShiftAmount p pp.from_
    let mut o1 ← opldrr pp pp.as rt rf 0 true
    o1 := o1 ||| (← encRegShiftOrExt p pp.from_ pp.from_.index) -- includes reg, op, etc
    return #[o1]
  else
    -- (Rn)(Rm), no extension or shift.
    let mut o1 ← opldrr pp pp.as rt rf 0 false
    o1 := o1 ||| ((Go.u32 pp.from_.index &&& 31) <<< 16)
    return #[o1]

/-- Case 99, `MOVD Rt, (Rn)(Rm.SXTW[<<amount])` (`asm7.go:5859-5871`). -/
def c99 (p : Nat) (pp : Prog) : AsmM (Array UInt32) := do
  let rt := pp.to.reg
  let rf := pp.from_.reg
  if isRegShiftOrExt pp.to then
    -- extended or shifted offset register.
    checkShiftAmount p pp.to
    let mut o1 ← opstrr pp pp.as rf rt 0 true
    o1 := o1 ||| (← encRegShiftOrExt p pp.to pp.to.index) -- includes reg, op, etc
    return #[o1]
  else
    -- (Rn)(Rm), no extension or shift.
    let mut o1 ← opstrr pp pp.as rf rt 0 false
    o1 := o1 ||| ((Go.u32 pp.to.index &&& 31) <<< 16)
    return #[o1]

/-- Case 100, `VTBL/VTBX Vn.<T>, [Vt1.<T>, Vt2.<T>, ...], Vd.<T>` (`asm7.go:5873-5912`). -/
def c100 (p : Prog) : AsmM (Array UInt32) := do
  let af := arng p.from_.reg
  let aT := arng p.to.reg
  if af != aT then diag p "invalid arrangement"
  let q : UInt32 ←
    if af == ARNG_8B then pure 0
    else if af == ARNG_16B then pure 1
    else diag p "invalid arrangement"
  let rf := p.from_.reg
  let rt := p.to.reg
  let offset := (← from3! p).offset
  let opcode := (Go.u64 offset >>> 12) &&& 15
  let len : UInt32 ←
    if opcode == 0x7 then pure 0 -- one register
    else if opcode == 0xa then pure 1 -- two register
    else if opcode == 0x6 then pure 2 -- three registers
    else if opcode == 0x2 then pure 3 -- four registers
    else diag p "invalid register numbers in ARM64 register list"
  let op : UInt32 := match p.as with
    | .VTBL => 0
    | .VTBX => 1
    | _ => 0
  let mut o1 : UInt32 := (q <<< 30) ||| ((0xe : UInt32) <<< 24) ||| (len <<< 13) ||| (op <<< 12)
  o1 := o1 ||| (r31 rf <<< 16) ||| ((Go.u32 offset &&& 31) <<< 5) ||| r31 rt
  return #[o1]

/-- Case 102, long shifts `v{s,u}shll[2] $shift, Vn.<Ta>, Vd.<Tb>` and lengthenings
`v{s,u}xtl[2], vfcvtl[2] Vn.<Ta>, Vd.<Tb>` (`asm7.go:5914-5958`). -/
def c102 (p : Prog) : AsmM (Array UInt32) := do
  let as := p.as
  let mut o1 ← opirr p p.as
  let mut rf := p.reg
  let mut af := (arng p.reg).toNat
  let aT := (arng p.to.reg).toNat
  let mut shift := p.from_.offset
  if as == .VUXTL || as == .VUXTL2 || as == .VSXTL || as == .VSXTL2 || as == .VFCVTL ||
      as == .VFCVTL2 then
    rf := p.from_.reg
    af := (arng p.from_.reg).toNat
    shift := 0
  let q : UInt32 :=
    if as == .VUXTL2 || as == .VSXTL2 || as == .VUSHLL2 || as == .VSSHLL2 || as == .VFCVTL2 then 1
    else 0
  let A (x : Int) : Nat := x.toNat
  if as == .VFCVTL || as == .VFCVTL2 then
    if (af != A ARNG_2S && af != A ARNG_4S) || aT != A ARNG_2D then diag p "operand mismatch"
    o1 := o1 ||| (q <<< 30) ||| (r31 rf <<< 5) ||| r31 p.to.reg
    return #[o1]
  let k := pack q af aT
  let (immh, width) : UInt8 × UInt8 ←
    if k == pack 0 (A ARNG_8B) (A ARNG_8H) then pure (1, 8)
    else if k == pack 1 (A ARNG_16B) (A ARNG_8H) then pure (1, 8)
    else if k == pack 0 (A ARNG_4H) (A ARNG_4S) then pure (2, 16)
    else if k == pack 1 (A ARNG_8H) (A ARNG_4S) then pure (2, 16)
    else if k == pack 0 (A ARNG_2S) (A ARNG_2D) then pure (4, 32)
    else if k == pack 1 (A ARNG_4S) (A ARNG_2D) then pure (4, 32)
    else diag p "operand mismatch"
  if !(0 ≤ shift && shift ≤ ((width - 1).toNat : Int)) then
    diag p "shift amount out of range"
  o1 := o1 ||| (q <<< 30) ||| (immh.toUInt32 <<< 19) ||| (Go.u32 shift <<< 16) |||
    (r31 rf <<< 5) ||| r31 p.to.reg
  return #[o1]

/-- Case 103, `VEOR3/VBCAX Va.B16, Vm.B16, Vn.B16, Vd.B16` (`asm7.go:5960-5971`). -/
def c103 (p : Prog) : AsmM (Array UInt32) := do
  let f3 ← from3! p
  let ta := arng p.from_.reg
  let tm := arng p.reg
  let td := arng p.to.reg
  let tn := arng f3.reg
  if ta != tm || ta != tn || ta != td || ta != ARNG_16B then diag p "invalid arrangement"
  return #[← oprrrr p p.as p.to.reg f3.reg p.reg p.from_.reg]

/-- Case 104, `vxar $imm4, Vm.<T>, Vn.<T>, Vd.<T>` (`asm7.go:5973-5998`). -/
def c104 (p : Prog) : AsmM (Array UInt32) := do
  let f3 ← from3! p
  let af := arng f3.reg
  let aT := arng p.to.reg
  let a := arng p.reg
  let index := p.from_.offset
  if af != a || af != aT then diag p "invalid arrangement"
  if af != ARNG_2D then diag p "invalid arrangement, should be D2"
  if index < 0 || index > 63 then diag p "illegal offset"
  let mut o1 ← opirr p p.as
  let rf := f3.reg
  let rt := p.to.reg
  let r := p.reg
  o1 := o1 ||| (r31 r <<< 16) ||| ((Go.u32 index &&& 63) <<< 10) ||| (r31 rf <<< 5) ||| r31 rt
  return #[o1]

/-- Case 105, `vuaddw{2} Vm.<Tb>, Vn.<Ta>, Vd.<Ta>` (`asm7.go:6000-6025`). -/
def c105 (p : Prog) : AsmM (Array UInt32) := do
  let af := (arng p.from_.reg).toNat
  let aT := (arng p.to.reg).toNat
  let a := (arng p.reg).toNat
  if aT != a then diag p "invalid arrangement"
  let q : UInt32 := if p.as == .VUADDW2 then 1 else 0
  let k := pack q aT af
  let A (x : Int) : Nat := x.toNat
  let size : UInt32 ←
    if k == pack 0 (A ARNG_8H) (A ARNG_8B) || k == pack 1 (A ARNG_8H) (A ARNG_16B) then pure 0
    else if k == pack 0 (A ARNG_4S) (A ARNG_4H) || k == pack 1 (A ARNG_4S) (A ARNG_8H) then
      pure 1
    else if k == pack 0 (A ARNG_2D) (A ARNG_2S) || k == pack 1 (A ARNG_2D) (A ARNG_4S) then
      pure 2
    else diag p "operand mismatch"
  let mut o1 ← oprrr p p.as p.to.reg p.reg p.from_.reg
  o1 := o1 ||| ((q &&& 1) <<< 30) ||| ((size &&& 3) <<< 22)
  return #[o1]

/-- Case 106, `CASPx (Rs, Rs+1), (Rb), (Rt, Rt+1)` (`asm7.go:6027-6057`). -/
def c106 (p : Prog) : AsmM (Array UInt32) := do
  let t2 ← to2! p
  let rs := p.from_.reg
  let rt := t2.reg
  let rb := p.to.reg
  let rs1 := Go.i16 p.from_.offset
  let rt1 := Go.i16 t2.offset
  let enc ← match atomicCASP p.as with
    | some e => pure e
    | none => diag p "invalid CASP-like atomic instructions"
  -- for CASPx-like instructions, Rs<0> != 1 && Rt<0> != 1
  if Go.u32 rs &&& 1 != 0 then
    diag p "source register pair must start from even register"
  else if Go.u32 rt &&& 1 != 0 then
    diag p "destination register pair must start from even register"
  else if rs != Go.i16 (rs1 - 1) then
    diag p "source register pair must be contiguous"
  else if rt != Go.i16 (rt1 - 1) then
    diag p "destination register pair must be contiguous"
  -- rt can't be sp.
  if rt == REG_RSP then diag p "illegal destination register"
  let o1 : UInt32 := (0 : UInt32) ||| enc ||| (r31 rs <<< 16) ||| (r31 rb <<< 5) ||| r31 rt
  return #[o1]

/-- Case 107, `tlbi, dc` (`asm7.go:6059-6077`). -/
def c107 (p : Prog) : AsmM (Array UInt32) := do
  let op ← match ARM64.sysInstFields p.from_.offset with
    | some op =>
      if (p.as == .TLBI && op.cn != 8) || (p.as == .DC && op.cn != 7) then
        diag p "illegal argument"
      else pure op
    | none => diag p "illegal argument"
  let mut o1 ← opirr p p.as
  if op.hasOperand2 then
    if p.to.reg == 0 then diag p "missing register at operand 2"
    o1 := o1 ||| (Go.u32 p.to.reg &&& 0x1F)
  else
    if p.to.reg != 0 || p.reg != 0 then diag p "extraneous register at operand 2"
    o1 := o1 ||| 0x1F
  o1 := o1 ||| Go.u32 (SYSARG4 op.op1 op.cn op.cm op.op2)
  return #[o1]

/-- Case 108, `bti` (`asm7.go:6079-6095`). -/
def c108 (p : Prog) : AsmM (Array UInt32) := do
  let mut o1 := SYSHINT 32
  if p.from_.type != .SPECIAL then diag p "missing operand"
  let s := p.from_.offset
  if s == SPOP_C then o1 := o1 ||| ((1 : UInt32) <<< 6)
  else if s == SPOP_J then o1 := o1 ||| ((2 : UInt32) <<< 6)
  else if s == SPOP_JC then o1 := o1 ||| ((3 : UInt32) <<< 6)
  else diag p "illegal argument"
  return #[o1]

/-- Case 109, `[cm|fcm][eq|ge|gt|le|lt] $0, Vn.<T>, Vd.<T>` (`asm7.go:6097-6154`). -/
def c109 (p : Prog) : AsmM (Array UInt32) := do
  -- Encoding is same as case 83 (this is a separate case because $0 occupies p.From)
  let fzero ← if p.from_.type == .FCONST then pure (isZeroF (← fval p p.from_)) else pure false
  if !(p.from_.type == .CONST && p.from_.offset == 0) && !(p.from_.type == .FCONST && fzero) then
    diag p "expected a constant zero immediate operand"
  let an := arng p.reg
  let ad := arng p.to.reg
  if an != ad then diag p "operand mismatch"
  let (q, size) : UInt32 × UInt32 ←
    if p.from_.type == .FCONST then
      if an == ARNG_2D then pure (1, 1)
      else if an == ARNG_2S then pure (0, 0)
      else if an == ARNG_4S then pure (1, 0)
      else diag p "invalid arrangement"
    else
      if an == ARNG_16B then pure (1, 0)
      else if an == ARNG_2D then pure (1, 3)
      else if an == ARNG_2S then pure (0, 2)
      else if an == ARNG_4H then pure (0, 1)
      else if an == ARNG_4S then pure (1, 2)
      else if an == ARNG_8B then pure (0, 0)
      else if an == ARNG_8H then pure (1, 1)
      else diag p "invalid arrangement"
  let mut o1 ← opirr p p.as
  let rd := r31 p.to.reg
  let rn := r31 p.reg
  o1 := o1 ||| (q <<< 30) ||| (size <<< 22) ||| (rn <<< 5) ||| rd
  return #[o1]

/-- Case 110, `rprfm (Rn), Rm, <rprfop/imm6>` (`asm7.go:6156-6183`). -/
def c110 (p : Prog) : AsmM (Array UInt32) := do
  let rn := p.from_.reg
  let rm := p.reg
  -- Operation is either a 6-bit immediate or named prefetch operation.
  let operation : UInt32 ←
    if p.to.type == .CONST then do
      let operation := Go.u32 p.to.offset
      if operation > 63 then diag p "range prefetch immediate must be 0 to 63"
      pure operation
    else
      match ARM64.rprfopfield p.to.offset with
      | some v => pure v
      | none =>
        diag p "illegal range prefetch operand, expected PLDKEEP, PSTKEEP, PLDSTRM or PSTSTRM"
  -- 6-bit placement: the 6-bit value is scattered to match the architectural encoding
  -- (bits 15,13,12,2-0): option2 (bit5) -> bit15, option0 (bit4) -> bit13, S (bit3) -> bit12,
  -- Rt<2:0> (bits2-0) -> bits2-0. Rt<4:3> are already set by c.opirr() and are fixed for RPRFM.
  let option2 := (operation &&& ((1 : UInt32) <<< 5)) <<< 10
  let option0 := (operation &&& ((1 : UInt32) <<< 4)) <<< 9
  let s := (operation &&& ((1 : UInt32) <<< 3)) <<< 9
  let rt := operation &&& 0x7
  let encodedOperation := option2 ||| option0 ||| s ||| rt
  let mut o1 ← opirr p p.as
  o1 := o1 ||| (r31 rm <<< 16) ||| (r31 rn <<< 5) ||| encodedOperation
  return #[o1]

end AsmoutB

open AsmoutB in
/-- `ctxt7.asmout`'s `switch o.type_` for the cases from 46 on (`asm7.go:4496-6183`): the
words `o1, o2, …` the case sets, `none` for any other case. -/
def asmoutB (case : Int) (p : Nat) (o : ARM64.Optab) : AsmM (Option (Array UInt32)) := do
  if case < 46 then return none
  let pp ← getP p
  match case.toNat with
  | 46 => some <$> c46 pp
  | 47 => some <$> c47 pp
  | 48 => some <$> c48 pp
  | 49 => some <$> c49 pp
  | 50 => some <$> c50 pp
  | 51 => some <$> c51 pp
  | 52 => some <$> c52 pp
  | 53 => some <$> c53 pp
  | 54 => some <$> c54 pp
  | 55 => some <$> c55 pp
  | 56 => some <$> c56 pp
  | 57 => some <$> c57 pp
  | 58 => some <$> c58 pp
  | 59 => some <$> c59 pp
  | 60 => some <$> c60 p pp
  | 61 => some <$> c61 p pp
  | 62 => some <$> c62 pp
  | 63 => some <$> c63 pp
  | 64 => some <$> c64 p pp o
  | 65 => some <$> c65 p pp o
  | 66 => some <$> c66 p pp o
  | 67 => some <$> c67 p pp o
  | 68 => some <$> c68 pp
  | 69 => some <$> c69 pp
  | 70 => some <$> c70 pp
  | 71 => some <$> c71 pp
  | 72 => some <$> c72 pp
  | 73 => some <$> c73 pp
  | 74 => some <$> c74 p pp o
  | 75 => some <$> c75 p pp o
  | 76 => some <$> c76 p pp o
  | 77 => some <$> c77 p pp o
  | 78 => some <$> c78 pp
  | 79 => some <$> c79 pp
  | 80 => some <$> c80 pp
  | 81 => some <$> c81 p pp o
  | 82 => some <$> c82 pp
  | 83 => some <$> c83 pp
  | 84 => some <$> c84 p pp o
  | 85 => some <$> c85 pp
  | 86 => some <$> c86 pp
  | 87 => some <$> c87 p pp o
  | 88 => some <$> c88 p pp o
  | 89 => some <$> c89 pp
  -- UDF: stops execution (`asm7.go:5463-5469`).
  | 90 => return some #[0]
  | 91 => some <$> c91 pp
  | 92 => some <$> c92 pp
  | 93 => some <$> c93 pp
  | 94 => some <$> c94 pp
  | 95 => some <$> c95 pp
  | 96 => some <$> c96 pp o
  | 97 => some <$> c97 pp o
  | 98 => some <$> c98 p pp
  | 99 => some <$> c99 p pp
  | 100 => some <$> c100 pp
  | 102 => some <$> c102 pp
  | 103 => some <$> c103 pp
  | 104 => some <$> c104 pp
  | 105 => some <$> c105 pp
  | 106 => some <$> c106 pp
  | 107 => some <$> c107 pp
  | 108 => some <$> c108 pp
  | 109 => some <$> c109 pp
  | 110 => some <$> c110 pp
  -- Generic SVE instruction encoding: compiled code has no SVE opcodes.
  | 127 => throw s!"asmout: illegal combination from SVE: {pp.as.name}"
  | _ => return none

end GoFV.Asm
