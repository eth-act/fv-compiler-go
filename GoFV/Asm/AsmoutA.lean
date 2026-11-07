import GoFV.Asm.Asm7Ops

/-!
# `asmout`, cases 0–45 (`asm7.go:3628-4495`; `docs/PASSES3.md` D5)

The first half of the `switch o.type_` of `ctxt7.asmout` (`asm7.go:3616-6217`): each case
computes the words `o1 … o5` of Prog `p` with the optab entry `o` that `oplook` selected, and
appends its relocations to the text symbol (`c.cursym.AddRel`) at `ctxt7.pc`. `asmoutA` returns
`none` for the case numbers it does not cover (46 and above are `GoFV.Asm.AsmoutB`; the
dispatcher is `GoFV.Asm.asmout`), else the words `o1, o2, …` (trailing zero words omitted).
`c.ctxt.Diag` is a port error (`throw`).

Not ported: cases 35 and 36 (`MRS`/`MSR`, which need `SysRegEnc`'s system register table) and 37
(`MSR $imm, PSTATEfield`, which needs the `pstatefield` table); neither table is generated, and
the compiler never emits these instructions.
-/

namespace GoFV.Asm

open AsmM ARM64

/-- `x & m` for a mask `m ≥ 0` (two's complement `x`). -/
private def aoAnd (x : Int) (m : Nat) : Int :=
  Int.ofNat ((x % 18446744073709551616).toNat &&& m)

/-- `p.GetFrom3()` (`link.go:356-363`): the first `RestArgs` operand at position `Source`. -/
private def aoFrom3? (p : Prog) : Option Addr :=
  (p.rest.find? (·.1 == 0)).map (·.2)

/-- `p.GetFrom3()` where Go dereferences it unconditionally (a nil pointer is a port error). -/
private def aoFrom3 (p : Prog) : AsmM Addr :=
  match aoFrom3? p with
  | some a => pure a
  | none => throw s!"asmout: {p.as.name}: no from3 operand"

/-- `p.From3Type()` (`link.go:343-349`). -/
private def aoFrom3Type (p : Prog) : AddrType :=
  match aoFrom3? p with
  | some a => a.type
  | none => .NONE

/-- `c.cursym.AddRel(c.ctxt, obj.Reloc{…})` (`data.go:206`): appends to the text symbol's `R`. -/
private def aoAddRel (r : Reloc) : AsmM Unit :=
  modify fun s => { s with textR := s.textR.push r }

/-- `int32(c.pc)`. -/
private def aoPc : AsmM Int := return Go.i32 (← get).pc

/-- `asm7.go:4145-4199` (case 30) and `asm7.go:4201-4255` (case 31): `splitImm24uScaled`'s
error is the `goto …usepool`. -/
private def aoSplit (v : Int) (s : Int) : Option (Int × Int) :=
  match splitImm24uScaled v s.toNat with
  | .ok hl => some hl
  | .error _ => none

/-- `c.aclass(&p.From)` (`to = false`) or `c.aclass(&p.To)`: Go updates the operand in place
(`a.Reg = REG_NONE` for `NAME_AUTO`/`NAME_PARAM` off `REGSP`, `asm7.go:2141-2217`). -/
private def aoAclass (p : Nat) (to : Bool) : AsmM Nat := do
  let pp ← getP p
  let (c, a) ← aclassAddr (if to then pp.to else pp.from_)
  modP p fun x => if to then { x with to := a } else { x with from_ := a }
  return c

/-- `c.regoff(&p.From)` / `c.regoff(&p.To)` (`asm7.go:1486-1490`), updating the operand as
`aoAclass` does. -/
private def aoRegoff (p : Nat) (to : Bool) : AsmM Int := do
  modify fun s => { s with instoffset := 0 }
  discard <| aoAclass p to
  return Go.i32 (← get).instoffset

/-- `int32(1 << uint(movesize(a)))` (`asm7.go:3961`, `3976`): an `int` shift, 0 when the
amount is 64 or more. -/
private def aoMoveSz (a : As) : AsmM Int := do
  let m := movesize a
  let n : Nat := if m < 0 then 64 else m.toNat
  return if n ≥ 64 then 0 else Go.i32 (Go.i64 (2 ^ n))

/-- Go's `v % sz` on `int32`: truncated remainder; a zero divisor panics. -/
private def aoRem (v sz : Int) : AsmM Int :=
  if sz == 0 then throw "asmout: integer divide by zero" else pure (v.tmod sz)

/-- `ctxt7.asmout`'s cases 0–45 (`asm7.go:3632-4494`) for Prog `p` with optab entry `o`:
`none` for any other case. -/
def asmoutA (case : Int) (p : Nat) (o : ARM64.Optab) : AsmM (Option (Array UInt32)) := do
  let pp ← getP p
  let diag {α} (msg : String) : AsmM α := throw s!"asmout: {msg}: {pp.as.name}"
  match case with
  | 0 => -- pseudo ops (asm7.go:3632-3633)
    return some #[]
  | 1 => -- op Rm,[Rn],Rd (asm7.go:3635-3643)
    let mut rt := pp.to.reg
    let mut r := pp.reg
    let rf := pp.from_.reg
    if pp.to.type == .NONE then rt := REGZERO
    if r == 0 then r := rt
    let o1 ← oprrr pp pp.as rt r rf
    return some #[o1]
  | 2 => -- add/sub $(uimm12|uimm24)[,R],R; cmp $(uimm12|uimm24),R (asm7.go:3645-3662)
    if pp.to.reg == REG_RSP && isADDSop pp.as then diag "illegal destination register"
    let mut o1 ← opirr pp pp.as
    let mut rt := pp.to.reg
    let mut r := pp.reg
    if pp.to.type == .NONE then
      if o1 &&& W.Sbit == 0 then diag "ineffective ZR destination"
      rt := REGZERO
    if r == 0 then r := rt
    let v ← aoRegoff p false
    o1 ← oaddi pp pp.as v rt r
    return some #[o1]
  | 3 => -- op R<<n[,R],R (shifted register) (asm7.go:3664-3685)
    let mut rt := pp.to.reg
    let mut r := pp.reg
    if pp.to.type == .NONE then rt := REGZERO
    if pp.as == .MVN || pp.as == .MVNW || isNEGop pp.as then
      r := REGZERO
    else if r == 0 then
      r := rt
    let mut o1 ← oprrr pp pp.as rt r 0
    let amount := (pp.from_.offset >>> 10) % 64
    let is64bit := o1 &&& ((1 : UInt32) <<< 31)
    if is64bit == 0 && amount ≥ 32 then diag "shift amount out of range 0 to 31"
    let shift := (pp.from_.offset >>> 22) % 4
    if (shift > 2 || shift < 0) && (isADDop pp.as || isADDWop pp.as || isNEGop pp.as) then
      diag "unsupported shift operator"
    o1 := o1 ||| Go.u32 pp.from_.offset
    return some #[o1]
  | 4 => -- mov $addcon, R; mov $recon, R; mov $racon, R; mov $addcon2, R (asm7.go:3687-3713)
    let rt := pp.to.reg
    let mut r := o.param
    if r == 0 then
      r := REGZERO
    else if r == REGFROM then
      r := pp.from_.reg
    if r == 0 then r := REGSP
    let mut v ← aoRegoff p false
    let pp ← getP p
    let mut a : As := .ADD
    if v < 0 then
      a := .SUB
      v := Go.i32 (-v)
    if (← optabSize o p) == 8 then
      let o1 ← oaddi pp a (aoAnd v 0xfff000) rt r
      let o2 ← oaddi pp a (aoAnd v 0x000fff) rt rt
      return some #[o1, o2]
    let o1 ← oaddi pp a v rt r
    return some #[o1]
  | 5 => -- b s; bl s (asm7.go:3715-3729)
    let mut o1 ← opbra pp pp.as
    match pp.to.sym with
    | none =>
      o1 := o1 ||| Go.u32 (← brdist p 0 26 2)
      return some #[o1]
    | some s =>
      aoAddRel { type := "R_CALLARM64", off := ← aoPc, siz := 4, sym := some s,
                 add := pp.to.offset }
      return some #[o1]
  | 6 => -- b ,O(R); bl ,O(R) (asm7.go:3731-3739)
    let mut o1 ← opbrr pp pp.as
    o1 := o1 ||| Go.u32 (aoAnd pp.to.reg 31) <<< 5
    if pp.as == .CALL then
      aoAddRel { type := "R_CALLIND", off := ← aoPc, siz := 0, sym := none, add := 0 }
    return some #[o1]
  | 7 => -- beq s (asm7.go:3741-3744)
    let mut o1 ← opbra pp pp.as
    o1 := o1 ||| Go.u32 ((← brdist p 0 19 2) <<< 5)
    return some #[o1]
  | 8 => -- lsl $c,[R],R -> ubfm $(W-1)-c,$(-c MOD (W-1)),Rn,Rd (asm7.go:3746-3780)
    let rt := pp.to.reg
    let mut rf := pp.reg
    if rf == 0 then rf := rt
    let v := pp.from_.offset
    let o1 ← match pp.as with
      | .ASR => opbfm pp .SBFM v 63 rf rt
      | .ASRW => opbfm pp .SBFMW v 31 rf rt
      | .LSL => opbfm pp .UBFM ((64 - v) % 64) (63 - v) rf rt
      | .LSLW => opbfm pp .UBFMW ((32 - v) % 32) (31 - v) rf rt
      | .LSR => opbfm pp .UBFM v 63 rf rt
      | .LSRW => opbfm pp .UBFMW v 31 rf rt
      | .ROR => opextr pp .EXTR v rf rf rt
      | .RORW => opextr pp .EXTRW v rf rf rt
      | _ => diag "bad shift $con"
    return some #[o1]
  | 9 => -- lsl Rm,[Rn],Rd -> lslv Rm, Rn, Rd (asm7.go:3782-3787)
    let rt := pp.to.reg
    let mut r := pp.reg
    let rf := pp.from_.reg
    if r == 0 then r := rt
    let o1 ← oprrr pp pp.as rt r rf
    return some #[o1]
  | 10 => -- brk/hvc/.../svc [$con] (asm7.go:3789-3794)
    let mut o1 ← opimm pp pp.as
    if pp.from_.type != .NONE then
      o1 := o1 ||| Go.u32 (aoAnd pp.from_.offset 0xffff <<< 5)
    return some #[o1]
  | 11 => -- dword (asm7.go:3796-3811)
    discard <| aoAclass p true
    let pp ← getP p
    let off := (← get).instoffset
    let mut o1 := Go.u32 off
    let mut o2 := Go.u32 (off >>> 32)
    if let some s := pp.to.sym then
      aoAddRel { type := "R_ADDR", off := ← aoPc, siz := 8, sym := some s, add := pp.to.offset }
      o2 := 0
      o1 := o2
    return some #[o1, o2]
  | 12 => -- movT $vcon, reg (asm7.go:3813-3823)
    let (num, os) ← omovlconst pp.as pp pp.from_ pp.to.reg (Array.replicate 5 0)
    if num == 0 then diag "invalid constant"
    return some #[os[0]!, os[1]!, os[2]!, os[3]!]
  | 13 => -- addop $vcon, [R], R (64 bit literal); cmp $lcon,R -> addop $lcon,R, ZR
    -- (asm7.go:3825-3866)
    if pp.reg == REGTMP then diag "cannot use REGTMP as source"
    if pp.to.reg == REG_RSP && isADDSop pp.as then diag "illegal destination register"
    let cls := pp.from_.cls
    let (num, os) ← if isADDWop pp.as then do
        if !cmp C_LCON.toNat cls.toNat then diag "illegal combination"
        omovlconst .MOVW pp pp.from_ REGTMP (Array.replicate 5 0)
      else
        omovlconst .MOVD pp pp.from_ REGTMP (Array.replicate 5 0)
    if num == 0 then diag "invalid constant"
    let mut rt := pp.to.reg
    let mut r := pp.reg
    let rf := REGTMP
    if pp.to.type == .NONE then rt := REGZERO
    if r == 0 then r := rt
    let o ← if pp.to.type != .NONE && (rt == REGSP || r == REGSP) then do
        let o ← opxrrr pp pp.as rt r rf false
        pure (o ||| W.LSL0_64)
      else
        oprrr pp pp.as rt r rf
    let os := os.set! num o
    return some #[os[0]!, os[1]!, os[2]!, os[3]!, os[4]!]
  | 14 => -- word (asm7.go:3868-3884)
    if (← aoAclass p true) == C_ADDR.toNat then diag "address constant needs DWORD"
    let mut o1 := Go.u32 (← get).instoffset
    if let some s := pp.to.sym then
      aoAddRel { type := "R_ADDR", off := ← aoPc, siz := 4, sym := some s, add := pp.to.offset }
      o1 := 0
    return some #[o1]
  | 15 => -- mul/mneg/umulh/umull r,[r,]r; madd/msub/fmadd/... Rm,Ra,Rn,Rd (asm7.go:3886-3897)
    let rt := pp.to.reg
    let mut r := pp.reg
    let rf := pp.from_.reg
    let mut ra := REGZERO
    if r == 0 then r := rt
    if aoFrom3Type pp == .REG then
      r := (← aoFrom3 pp).reg
      ra := pp.reg
      if ra == 0 then ra := REGZERO
    let o1 ← oprrrr pp pp.as rt r rf ra
    return some #[o1]
  | 16 => -- XremY R[,R],R -> XdivY; XmsubY (asm7.go:3899-3906)
    let rt := pp.to.reg
    let mut r := pp.reg
    let rf := pp.from_.reg
    if r == 0 then r := rt
    let o1 ← oprrr pp pp.as REGTMP r rf
    let mut o2 ← oprrrr pp .MSUBW rt REGTMP rf r
    o2 := o2 ||| (o1 &&& ((1 : UInt32) <<< 31))
    return some #[o1, o2]
  | 17 => -- op Rm,[Rn],Rd; default Rn=ZR (asm7.go:3908-3916)
    let mut rt := pp.to.reg
    let mut r := pp.reg
    let rf := pp.from_.reg
    if pp.to.type == .NONE then rt := REGZERO
    if r == 0 then r := REGZERO
    let o1 ← oprrr pp pp.as rt r rf
    return some #[o1]
  | 18 => -- csel cond,Rn,Rm,Rd; cinc/cinv/cneg cond,Rn,Rd; cset cond,Rd (asm7.go:3918-3938)
    let cond0 := pp.from_.offset
    if cond0 < SPOP_EQ || cond0 > SPOP_NV ||
        (cond0 == SPOP_AL || cond0 == SPOP_NV) && aoFrom3Type pp == .NONE then
      diag "invalid condition"
    let mut cond : Nat := (cond0 - SPOP_EQ).toNat
    let rt := pp.to.reg
    let mut r := pp.reg
    let mut rf := pp.reg
    if aoFrom3Type pp == .NONE then
      -- CINC/CINV/CNEG or CSET/CSETM
      if r == 0 then
        -- CSET/CSETM
        r := REGZERO
        rf := REGZERO
      cond := cond ^^^ 1
    else
      rf := (← aoFrom3 pp).reg -- CSEL
    let mut o1 ← oprrr pp pp.as rt r rf
    o1 := o1 ||| (cond &&& 15).toUInt32 <<< 12
    return some #[o1]
  | 19 => -- CCMN cond, (Rm|uimm5),Rn, uimm4 -> ccmn Rn,Rm,uimm4,cond (asm7.go:3940-3957)
    let nzcv := Go.u32 pp.to.offset
    let cond0 := pp.from_.offset
    if cond0 < SPOP_EQ || cond0 > SPOP_NV then diag "invalid condition"
    let cond : Nat := (cond0 - SPOP_EQ).toNat
    let f3 ← aoFrom3 pp
    if f3.type == .REG then
      let r := pp.reg
      let rf := f3.reg
      let mut o1 ← oprrr pp pp.as 0 r rf
      o1 := o1 ||| (((cond &&& 15).toUInt32 <<< 12) ||| nzcv)
      return some #[o1]
    else
      let rf := aoAnd f3.offset 0x1F
      let mut o1 ← opirr pp pp.as
      o1 := o1 ||| ((Go.u32 (aoAnd rf 31) <<< 16) ||| ((cond &&& 15).toUInt32 <<< 12) |||
        (Go.u32 (aoAnd pp.reg 31) <<< 5) ||| nzcv)
      return some #[o1]
  | 20 => -- movT R,O(R) -> strT (asm7.go:3959-3972)
    let mut v ← aoRegoff p true
    let pp ← getP p
    let sz ← aoMoveSz pp.as
    let mut rt := pp.to.reg
    let rf := pp.from_.reg
    if rt == 0 then rt := o.param
    if v < 0 || (← aoRem v sz) != 0 then
      -- unscaled 9-bit signed
      let o1 ← olsr9s pp (← opstr p pp.as) v rt rf
      return some #[o1]
    else
      v := Go.i32 (← offsetshift pp v o.a4)
      let o1 ← olsr12u pp (← opstr p pp.as) v rt rf
      return some #[o1]
  | 21 => -- movT O(R),R -> ldrT (asm7.go:3974-3987)
    let mut v ← aoRegoff p false
    let pp ← getP p
    let sz ← aoMoveSz pp.as
    let rt := pp.to.reg
    let mut rf := pp.from_.reg
    if rf == 0 then rf := o.param
    if v < 0 || (← aoRem v sz) != 0 then
      -- unscaled 9-bit signed
      let o1 ← olsr9s pp (← opldr pp pp.as) v rf rt
      return some #[o1]
    else
      v := Go.i32 (← offsetshift pp v o.a1)
      let o1 ← olsr12u pp (← opldr pp pp.as) v rf rt
      return some #[o1]
  | 22 => -- movT (R)O!,R; movT O(R)!, R -> ldrT (asm7.go:3989-4005)
    if pp.from_.reg != REGSP && pp.from_.reg == pp.to.reg then
      diag "constrained unpredictable behavior"
    let v := Go.i32 pp.from_.offset
    if v < -256 || v > 255 then diag "offset out of range [-256,255]"
    let mut o1 ← opldr pp pp.as
    if o.scond == C_XPOST.toNat then
      o1 := o1 ||| (1 : UInt32) <<< 10
    else
      o1 := o1 ||| (3 : UInt32) <<< 10
    o1 := o1 ||| (((Go.u32 v &&& 0x1FF) <<< 12) ||| (Go.u32 (aoAnd pp.from_.reg 31) <<< 5) |||
      Go.u32 (aoAnd pp.to.reg 31))
    return some #[o1]
  | 23 => -- movT R,(R)O!; movT O(R)!, R -> strT (asm7.go:4007-4023)
    if pp.to.reg != REGSP && pp.from_.reg == pp.to.reg then
      diag "constrained unpredictable behavior"
    let v := Go.i32 pp.to.offset
    if v < -256 || v > 255 then diag "offset out of range [-256,255]"
    let mut o1 ← opstr p pp.as
    if o.scond == C_XPOST.toNat then
      o1 := o1 ||| (1 : UInt32) <<< 10
    else
      o1 := o1 ||| (3 : UInt32) <<< 10
    o1 := o1 ||| (((Go.u32 v &&& 0x1FF) <<< 12) ||| (Go.u32 (aoAnd pp.to.reg 31) <<< 5) |||
      Go.u32 (aoAnd pp.from_.reg 31))
    return some #[o1]
  | 24 => -- mov/mvn Rs,Rd -> add $0,Rs,Rd or orr Rs,ZR,Rd (asm7.go:4025-4035)
    let rt := pp.to.reg
    let r := REGZERO
    let rf := pp.from_.reg
    if rt == REGSP || rf == REGSP then
      if pp.as == .MVN || pp.as == .MVNW then diag "illegal SP reference"
      let mut o1 ← opirr pp pp.as
      o1 := o1 ||| ((Go.u32 (aoAnd rf 31) <<< 5) ||| Go.u32 (aoAnd rt 31))
      return some #[o1]
    else
      let o1 ← oprrr pp pp.as rt r rf
      return some #[o1]
  | 25 => -- negX Rs, Rd -> subX Rs<<0, ZR, Rd (asm7.go:4037-4042)
    let rt := pp.to.reg
    let r := REGZERO
    let mut rf := pp.from_.reg
    if rf == 0 then rf := rt
    let o1 ← oprrr pp pp.as rt r rf
    return some #[o1]
  | 26 => -- op Vn, Vd; op Vn.<T>, Vd.<T> (asm7.go:4044-4068)
    let rt := pp.to.reg
    let rf := pp.from_.reg
    let af := (rf >>> 5) % 16
    let at_ := (rt >>> 5) % 16
    let cf ← aoAclass p false
    let sz : Int := match pp.as with
      | .AESD | .AESE | .AESIMC | .AESMC => ARNG_16B
      | .SHA1SU1 | .SHA256SU0 => ARNG_4S
      | .SHA512SU0 => ARNG_2D
      | _ => 0
    if cf == C_ARNG.toNat then
      if pp.as == .SHA1H then
        diag "invalid operands"
      else if af != sz || af != at_ then
        diag "invalid arrangement"
    let o1 ← oprrr pp pp.as rt rf 0
    return some #[o1]
  | 27 => -- op Rm<<n[,Rn],Rd (extended register) (asm7.go:4070-4091)
    if pp.to.reg == REG_RSP && isADDSop pp.as then diag "illegal destination register"
    let mut rt := pp.to.reg
    let mut r := pp.reg
    let rf := pp.from_.reg
    if pp.to.type == .NONE then rt := REGZERO
    if r == 0 then r := rt
    if aoAnd (pp.from_.reg - REG_R0) REG_EXT.toNat != 0 ||
        (pp.from_.reg ≥ REG_LSL && pp.from_.reg < REG_ARNG) then
      let amount := (pp.from_.reg >>> 5) % 8
      if amount > 4 then diag "shift amount out of range 0 to 4"
      let mut o1 ← opxrrr pp pp.as rt r 0 true
      o1 := o1 ||| (← encRegShiftOrExt p pp.from_ pp.from_.reg) -- includes reg, op, etc
      return some #[o1]
    else
      let o1 ← opxrrr pp pp.as rt r rf false
      return some #[o1]
  | 28 => -- logop $vcon, [R], R (64 bit literal) (asm7.go:4093-4126)
    if pp.reg == REGTMP then diag "cannot use REGTMP as source"
    let cls := pp.from_.cls
    let (num, os) ← if isANDWop pp.as then do
        if !cmp C_LCON.toNat cls.toNat then diag "illegal combination"
        omovlconst .MOVW pp pp.from_ REGTMP (Array.replicate 5 0)
      else
        omovlconst .MOVD pp pp.from_ REGTMP (Array.replicate 5 0)
    if num == 0 then diag "invalid constant"
    let mut rt := pp.to.reg
    let mut r := pp.reg
    let rf := REGTMP
    if pp.to.type == .NONE then rt := REGZERO
    if r == 0 then r := rt
    let o ← oprrr pp pp.as rt r rf
    let os := os.set! num o
    return some #[os[0]!, os[1]!, os[2]!, os[3]!, os[4]!]
  | 29 => -- op Rn, Rd (asm7.go:4128-4143)
    let fc ← aoAclass p false
    let tc ← aoAclass p true
    let pp ← getP p
    if (pp.as == .FMOVD || pp.as == .FMOVS) &&
        (fc == C_REG.toNat || fc == C_ZREG.toNat || tc == C_REG.toNat || tc == C_ZREG.toNat) then
      -- FMOV Rx, Fy or FMOV Fy, Rx
      let mut o1 := FPCVTI 0 0 0 0 6
      if pp.as == .FMOVD then o1 := o1 ||| ((1 : UInt32) <<< 31 ||| (1 : UInt32) <<< 22) -- 64-bit
      if fc == C_REG.toNat || fc == C_ZREG.toNat then o1 := o1 ||| (1 : UInt32) <<< 16 -- FMOV Rx, Fy
      o1 := o1 ||| (Go.u32 (aoAnd pp.from_.reg 31) <<< 5 ||| Go.u32 (aoAnd pp.to.reg 31))
      return some #[o1]
    else
      let o1 ← oprrr pp pp.as pp.to.reg pp.from_.reg 0
      return some #[o1]
  | 30 => -- movT R,L(R) -> strT (asm7.go:4145-4199)
    let s := movesize o.as
    if s < 0 then diag "unexpected long move"
    let mut rt := pp.to.reg
    let rf := pp.from_.reg
    if rt == 0 then rt := o.param
    let v ← aoRegoff p true
    if v ≥ -256 && v ≤ 256 then
      diag s!"bad type for offset {v} (should be 9 bit signed immediate store)"
    if v ≥ 0 && v ≤ 4095 && aoAnd v (2 ^ s.toNat - 1) == 0 then
      diag s!"bad type for offset {v} (should be 12 bit unsigned immediate store)"
    -- Handle smaller unaligned and negative offsets via addition or subtraction.
    if v ≥ -4095 && v ≤ 4095 then
      let o1 ← oaddi12 pp v REGTMP rt
      let o2 ← olsr12u pp (← opstr p pp.as) 0 REGTMP rf
      return some #[o1, o2]
    match aoSplit v s with
    | some (hi, lo) =>
      if pp.pool.isSome then diag s!"unused constant in pool ({v})"
      let o1 ← oaddi pp .ADD hi REGTMP rt
      let o2 ← olsr12u pp (← opstr p pp.as) lo REGTMP rf
      return some #[o1, o2]
    | none =>
      -- storeusepool:
      if pp.pool.isNone then diag "constant is not in pool"
      if rt == REGTMP || rf == REGTMP then diag "REGTMP used in large offset store"
      let o1 ← omovlit .MOVD p pp.to REGTMP
      let o2 ← opstrr pp pp.as rf rt REGTMP false
      return some #[o1, o2]
  | 31 => -- movT L(R), R -> ldrT (asm7.go:4201-4255)
    let s := movesize o.as
    if s < 0 then diag "unexpected long move"
    let rt := pp.to.reg
    let mut rf := pp.from_.reg
    if rf == 0 then rf := o.param
    let v ← aoRegoff p false
    if v ≥ -256 && v ≤ 256 then
      diag s!"bad type for offset {v} (should be 9 bit signed immediate load)"
    if v ≥ 0 && v ≤ 4095 && aoAnd v (2 ^ s.toNat - 1) == 0 then
      diag s!"bad type for offset {v} (should be 12 bit unsigned immediate load)"
    -- Handle smaller unaligned and negative offsets via addition or subtraction.
    if v ≥ -4095 && v ≤ 4095 then
      let o1 ← oaddi12 pp v REGTMP rf
      let o2 ← olsr12u pp (← opldr pp pp.as) 0 REGTMP rt
      return some #[o1, o2]
    match aoSplit v s with
    | some (hi, lo) =>
      if pp.pool.isSome then diag s!"unused constant in pool ({v})"
      let o1 ← oaddi pp .ADD hi REGTMP rf
      let o2 ← olsr12u pp (← opldr pp pp.as) lo REGTMP rt
      return some #[o1, o2]
    | none =>
      -- loadusepool:
      if pp.pool.isNone then diag "constant is not in pool"
      if rt == REGTMP || rf == REGTMP then diag "REGTMP used in large offset load"
      let o1 ← omovlit .MOVD p pp.from_ REGTMP
      let o2 ← opldrr pp pp.as rt rf REGTMP false
      return some #[o1, o2]
  | 32 => -- mov $con, R -> movz/movn (asm7.go:4257-4258)
    let o1 ← omovconst pp.as pp pp.from_ pp.to.reg
    return some #[o1]
  | 33 => -- movk $uimm16 << pos (asm7.go:4260-4279)
    let mut o1 ← opirr pp pp.as
    let d := pp.from_.offset
    if d == 0 then diag "zero shifts cannot be handled correctly"
    let s := movcon d
    if s < 0 || s ≥ 64 then diag "bad constant for MOVK"
    if o1 &&& W.S64 == 0 && s ≥ 32 then diag "illegal bit position"
    let du : Nat := (d % 18446744073709551616).toNat
    if (du >>> s.toNat) >>> 16 != 0 then diag "requires uimm16"
    let rt := pp.to.reg
    -- uint32 of the int64 OR = OR of the uint32 truncations
    o1 := o1 ||| (Go.u32 (aoAnd (d >>> s.toNat) 0xFFFF <<< 5) |||
      ((Go.u32 (s >>> 4) &&& 3) <<< 21) ||| Go.u32 (aoAnd rt 31))
    return some #[o1]
  | 34 => -- mov $lacon,R (asm7.go:4281-4288)
    let rt := pp.to.reg
    let mut r := pp.from_.reg
    let rf := REGTMP
    if r == 0 then r := o.param
    let o1 ← omovlit .MOVD p pp.from_ REGTMP
    let mut o2 ← opxrrr pp .ADD rt r rf false
    o2 := o2 ||| W.LSL0_64
    return some #[o1, o2]
  | 38 => -- clrex [$imm] (asm7.go:4350-4357)
    let mut o1 ← opimm pp pp.as
    if pp.to.type == .NONE then
      o1 := o1 ||| (0xF : UInt32) <<< 8
    else
      o1 := o1 ||| Go.u32 (aoAnd pp.to.offset 0xF <<< 8)
    return some #[o1]
  | 39 => -- cbz R, rel (asm7.go:4359-4363)
    let mut o1 ← opirr pp pp.as
    o1 := o1 ||| Go.u32 (aoAnd pp.from_.reg 31)
    o1 := o1 ||| Go.u32 ((← brdist p 0 19 2) <<< 5)
    return some #[o1]
  | 40 => -- tbz (asm7.go:4365-4374)
    let mut o1 ← opirr pp pp.as
    let v := Go.i32 pp.from_.offset
    if v < 0 || v > 63 then diag "illegal bit number"
    o1 := o1 ||| (((Go.u32 v &&& 0x20) <<< (31 - 5)) ||| ((Go.u32 v &&& 0x1F) <<< 19))
    o1 := o1 ||| Go.u32 ((← brdist p 0 14 2) <<< 5)
    o1 := o1 ||| Go.u32 (aoAnd pp.reg 31)
    return some #[o1]
  | 41 => -- eret, nop, others with no operands (asm7.go:4376-4377)
    let o1 ← op0 pp pp.as
    return some #[o1]
  | 42 => -- bfm R,r,s,R (asm7.go:4379-4380)
    let o1 ← opbfm pp pp.as pp.from_.offset (← aoFrom3 pp).offset pp.reg pp.to.reg
    return some #[o1]
  | 43 => -- bfm aliases (asm7.go:4382-4446)
    let rt := pp.to.reg
    let mut rf := pp.reg
    if rf == 0 then rf := rt
    let mut r := pp.from_.offset
    let s := (← aoFrom3 pp).offset
    let mut o1 : UInt32 := 0
    match pp.as with
    | .BFI =>
      if r != 0 then r := 64 - r
      o1 ← opbfm pp .BFM r (s - 1) rf rt
    | .BFIW =>
      if r != 0 then r := 32 - r
      o1 ← opbfm pp .BFMW r (s - 1) rf rt
    | .BFXIL => o1 ← opbfm pp .BFM r (r + s - 1) rf rt
    | .BFXILW => o1 ← opbfm pp .BFMW r (r + s - 1) rf rt
    | .SBFIZ =>
      if r != 0 then r := 64 - r
      o1 ← opbfm pp .SBFM r (s - 1) rf rt
    | .SBFIZW =>
      if r != 0 then r := 32 - r
      o1 ← opbfm pp .SBFMW r (s - 1) rf rt
    | .SBFX => o1 ← opbfm pp .SBFM r (r + s - 1) rf rt
    | .SBFXW => o1 ← opbfm pp .SBFMW r (r + s - 1) rf rt
    | .UBFIZ =>
      if r != 0 then r := 64 - r
      o1 ← opbfm pp .UBFM r (s - 1) rf rt
    | .UBFIZW =>
      if r != 0 then r := 32 - r
      o1 ← opbfm pp .UBFMW r (s - 1) rf rt
    | .UBFX => o1 ← opbfm pp .UBFM r (r + s - 1) rf rt
    | .UBFXW => o1 ← opbfm pp .UBFMW r (r + s - 1) rf rt
    | _ => diag "bad bfm alias"
    return some #[o1]
  | 44 => -- extr $b, Rn, Rm, Rd (asm7.go:4448-4449)
    let o1 ← opextr pp pp.as pp.from_.offset (← aoFrom3 pp).reg pp.reg pp.to.reg
    return some #[o1]
  | 45 => -- sxt/uxt[bhw] R,R; movT R,R -> sxtT R,R (asm7.go:4451-4494)
    let mut as := pp.as
    let rt := pp.to.reg
    let rf := pp.from_.reg
    if rf == REGZERO then as := .MOVWU -- clearer in disassembly
    let o1 ← match as with
      | .MOVB | .SXTB => opbfm pp .SBFM 0 7 rf rt
      | .MOVH | .SXTH => opbfm pp .SBFM 0 15 rf rt
      | .MOVW | .SXTW => opbfm pp .SBFM 0 31 rf rt
      | .MOVBU | .UXTB => opbfm pp .UBFM 0 7 rf rt
      | .MOVHU | .UXTH => opbfm pp .UBFM 0 15 rf rt
      | .MOVWU => oprrr pp as pp.to.reg REGZERO pp.from_.reg
      | .UXTW => opbfm pp .UBFM 0 31 rf rt
      | .SXTBW => opbfm pp .SBFMW 0 7 rf rt
      | .SXTHW => opbfm pp .SBFMW 0 15 rf rt
      | .UXTBW => opbfm pp .UBFMW 0 7 rf rt
      | .UXTHW => opbfm pp .UBFMW 0 15 rf rt
      | _ => throw s!"asmout: bad sxt {as.name}"
    return some #[o1]
  | _ => return none

end GoFV.Asm
