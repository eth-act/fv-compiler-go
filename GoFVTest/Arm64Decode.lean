import GoFV.Asm.Parse
import GoFV.Asm.Reg
import GoFV.Arm64.Exec
import Std.Data.HashMap

/-!
# `arm64-decode`: decoder round trip on the asm sections (issue #552)

`docs/plans/semantics3.md` §3 (a), (c). For every `gofv-prog` file under the given directories,
the asm section's text bytes are cut at the Progs' PCs and every Prog's words are decoded with
`GoFV.Arm64.decode`. A Prog **matches** when its words decode and executing them with
`GoFV.Arm64.exec` from a random state has the effect the Prog has in Go's assembly language
(`cmd/internal/obj/arm64` operand conventions: `OP from, reg, to` is `to = reg OP from`, `MADD`
`Rm, Ra, Rn, Rd` with `Ra` in `reg` and `Rn` in `RestArgs`, `LDP off(Rn), (Rt1, Rt2)`, `CASALD Rs, (Rn), Rt`, …): the destination registers,
flags, stores and the next PC agree with `progEffect`, every other register, `SP`, the flags
and the vector registers are unchanged, except `R27` (REGTMP, the assembler's scratch).
This checks the decoder and the instruction semantics against the Progs the assembler encoded,
including multi-word expansions (constants, large offsets, literal pools, `REM`), without
modelling the assembler's choices.

The text is placed at `BASE`; relocations are applied as the linker would (`R_CALLARM64`,
`R_ADDRARM64`, `R_ARM64_PCREL_LDST{8,16,32,64}`) with symbol `y<n>` at `symAddr n`, and the
memory outside the text is a fixed pseudo-random byte pattern. Pseudo-ops (`TEXT`, `FUNCDATA`,
`PCDATA`, …) must cover no bytes; `WORD`/`DWORD` (literal pools, jump tables) must be their
constant; the words after the last Prog must be zero (alignment padding, `UDF #0`).

usage: `arm64-decode [--words FILE] [--examples N] <dir|file>...`: prints per mismatch class
(opcode, optab entry, reason) the number of Progs and an example, then totals. `--words`
writes the distinct words of the text bytes with their counts (input of `arm64-cosim`).
Exit status 1 if a Prog does not match.
-/

open GoFV.Asm GoFV.Arm64
open GoFV.SSA.Sem (Flags)

namespace GoFVTest.Arm64Decode

def BASE : BitVec 64 := 0x10000000

/-- Where symbol `y<n>` is linked: within `BL`'s ±128 MiB of the text, 256-byte aligned. -/
def symAddr (n : Nat) : BitVec 64 := 0x14000000 + BitVec.ofNat 64 (n * 0x100)

/-- The background memory: a fixed byte pattern. -/
def pattern (a : BitVec 64) : BitVec 8 :=
  let x := a.toNat
  BitVec.ofNat 8 ((x * 2654435761 + x / 256 * 40503 + 17) / 4096)

/-! ## Registers in obj numbering (`GoFV.Asm.ARM64`, `cmd/internal/obj/arm64/a.out.go`) -/

open GoFV.Asm.ARM64 (REG_R0 REG_R27 REG_R31 REG_F0 REG_V0 REG_RSP REG_ARNG REG_EXT REG_LSL
  C_XPRE C_XPOST SPOP_EQ)

def gpIdx? (r : Int) : Option Nat :=
  if REG_R0 ≤ r && r ≤ REG_R31 then some (r - REG_R0).toNat else none

/-- A floating-point or vector register (`Fn`, `Vn`, `Vn.<T>`, `Vn.<T>[i]`): its number. -/
def fpIdx? (r : Int) : Option Nat :=
  if REG_F0 ≤ r && r < REG_V0 + 32 then some ((r - REG_F0).toNat % 32)
  else if REG_ARNG ≤ r && r < REG_ARNG + 1024 then some ((r - REG_R0).toNat % 32)
  else none

/-! ## Effects -/

/-- What a Prog does, from a given state. -/
structure Eff where
  /-- General registers written (index 0–30). -/
  x : List (Nat × BitVec 64) := []
  sp : Option (BitVec 64) := none
  v : List (Nat × BitVec 128) := []
  flags : Option Flags := none
  /-- Stores: address, size in bytes, value. -/
  stores : List (BitVec 64 × Nat × Nat) := []
  /-- The next PC if not the fall-through. -/
  pc : Option (BitVec 64) := none

/-- The context of a Prog's specification. -/
structure Ctx where
  s : MState
  p : Prog
  pcOf : Nat → Option Int
  autosize : Int
  extrasize : Int

abbrev Spec := Except String Eff

def Eff.wX (e : Eff) (r : Int) (val : BitVec 64) : Except String Eff :=
  if r == REG_R31 then pure e
  else if r == REG_RSP then pure { e with sp := some val }
  else match gpIdx? r with
    | some i => pure { e with x := (i, val) :: e.x }
    | none => throw s!"destination register {r}"

def Eff.wV (e : Eff) (r : Int) (val : BitVec 128) : Except String Eff :=
  match fpIdx? r with
  | some i => pure { e with v := (i, val) :: e.v }
  | none => throw s!"destination fp register {r}"

def Ctx.x (c : Ctx) (r : Int) : Except String (BitVec 64) :=
  if r == REG_RSP then pure c.s.sp
  else match gpIdx? r with
    | some i => pure (c.s.rX (BitVec.ofNat 5 i))
    | none => throw s!"register {r}"

def Ctx.v (c : Ctx) (r : Int) : Except String (BitVec 128) :=
  match fpIdx? r with
  | some i => pure (c.s.v (BitVec.ofNat 5 i))
  | none => throw s!"fp register {r}"

/-- Truncation to the datasize. -/
def trunc (sf : Bool) (x : BitVec 64) : BitVec 64 := if sf then x else x.setWidth 32 |>.setWidth 64

/-- An extended register `Rn.<ext><<amount` (`REG_EXT` range): bits 8–10 the extension, bits
5–7 the amount. -/
def extReg? (r : Int) : Option (Nat × Nat × Nat) :=
  let d := (r - REG_R0).toNat
  if r ≥ REG_EXT && r < REG_EXT + 4096 then some (d % 32, d / 256 % 8, d / 32 % 8)
  else none

/-- A source operand (register, shifted register, extended register, constant) at the datasize. -/
def Ctx.src (c : Ctx) (sf : Bool) (a : Addr) : Except String (BitVec 64) := do
  match a.type with
  | .REG =>
    match extReg? a.reg with
    | some (r, opt, amt) =>
      pure (trunc sf (extendReg (c.s.rX (BitVec.ofNat 5 r)) (BitVec.ofNat 3 opt) amt))
    | none => return trunc sf (← c.x a.reg)
  | .CONST => pure (trunc sf (BitVec.ofInt 64 a.offset))
  | .SHIFT =>
    let off := a.offset.toNat
    let rm := c.s.rX (BitVec.ofNat 5 (off / 65536 % 32))
    let k := shiftOf (BitVec.ofNat 2 (off / 4194304 % 4))
    let amt := off / 1024 % 64
    pure (sized sf fun _ e => GoFV.SSA.Sem.Arm64.Shift.apply k (e rm) amt)
  | _ => throw s!"source operand {a.type.name}"

/-- The condition of a `SPECIAL` operand (`SPOP_EQ` … `SPOP_NV`). -/
def condOfSpecial (a : Addr) : Except String (BitVec 4) :=
  if a.type == .SPECIAL && SPOP_EQ ≤ a.offset && a.offset < SPOP_EQ + 16 then
    pure (BitVec.ofInt 4 (a.offset - SPOP_EQ))
  else throw "condition operand"

/-- The address a memory operand denotes and the base register's write-back (`.W` = `C_XPRE`,
`.P` = `C_XPOST`). -/
def Ctx.mem (c : Ctx) (a : Addr) : Except String (BitVec 64 × Option (Int × BitVec 64)) := do
  if a.type != .MEM then throw s!"memory operand {a.type.name}"
  let off := BitVec.ofInt 64 a.offset
  match a.name with
  | .AUTO => pure (c.s.sp + BitVec.ofInt 64 (c.autosize + a.offset - c.extrasize), none)
  | .PARAM => pure (c.s.sp + BitVec.ofInt 64 (c.autosize + a.offset + 8), none)
  | .EXTERN | .STATIC =>
    match a.sym with
    | some n => pure (symAddr n + off, none)
    | none => throw "symbol-less extern"
  | .NONE =>
    let base ← c.x a.reg
    if a.index != 0 then
      let d := (a.index - REG_R0).toNat
      let idx ← if REG_EXT ≤ a.index && a.index < REG_EXT + 4096 then
          pure (extendReg (c.s.rX (BitVec.ofNat 5 (d % 32))) (BitVec.ofNat 3 (d / 256 % 8)) (d / 32 % 8))
        else if REG_LSL ≤ a.index && a.index < REG_LSL + 512 then
          pure (c.s.rX (BitVec.ofNat 5 (d % 32)) <<< (d / 32 % 8))
        else c.x a.index
      pure (base + idx, none)
    else if c.p.scond == C_XPRE.toNat then pure (base + off, some (a.reg, base + off))
    else if c.p.scond == C_XPOST.toNat then pure (base, some (a.reg, base + off))
    else pure (base + off, none)
  | n => throw s!"memory name {n.name}"

def Ctx.load (c : Ctx) (a : BitVec 64) (n : Nat) : BitVec 64 := (readMem c.s.mem a n).setWidth 64

/-- The branch target of a `BRANCH` operand. -/
def Ctx.target (c : Ctx) (a : Addr) : Except String (BitVec 64) := do
  match a.type, a.val, a.sym with
  | .BRANCH, .target id, _ =>
    match c.pcOf id with
    | some pc => pure (BASE + BitVec.ofInt 64 pc)
    | none => throw "branch target not in the list"
  | .BRANCH, _, some n => pure (symAddr n + BitVec.ofInt 64 a.offset)
  | _, _, _ => throw s!"branch operand {a.type.name}"

/-- `reg` of a three-operand Prog, defaulting to `to`. -/
def Ctx.rn (c : Ctx) : Int := if c.p.reg != 0 then c.p.reg else c.p.to.reg

def Ctx.rest (c : Ctx) (i : Nat) : Except String Addr :=
  match c.p.rest[i]? with
  | some (_, a) => pure a
  | none => throw "missing RestArgs operand"

/-! ## Integer operations by opcode -/

/-- `s` without its first `k` characters. -/
def dropS (s : String) (k : Nat) : String := String.ofList (s.toList.drop k)

/-- `s` without its last `k` characters. -/
def chopS (s : String) (k : Nat) : String := String.ofList (s.toList.take (s.length - k))

/-- The datasize of an opcode with an optional `W` suffix: `(base name, sf)`. -/
def baseOf (name : String) (ws : List String) : Option (String × Bool) :=
  if ws.contains name then some (name, true)
  else if name.endsWith "W" && ws.contains (chopS name 1) then some (chopS name 1, false)
  else none

def binNames : List String := ["ADD", "SUB", "AND", "ORR", "EOR", "BIC", "EON", "ORN", "ANDS",
  "BICS", "ADDS", "SUBS", "ADC", "ADCS", "SBC", "SBCS", "MUL", "MNEG", "UDIV", "SDIV", "REM",
  "UREM", "LSL", "LSR", "ASR", "ROR", "SMULH", "UMULH", "SMULL", "UMULL"]

/-- `x OP y` (`x` = `reg`, `y` = `from`) at the datasize, with the flags if the op sets them. -/
def binOp (op : String) (sf : Bool) (x y : BitVec 64) (cin : Bool) : BitVec 64 × Option Flags :=
  let nf (r : BitVec 64) := (r, (none : Option Flags))
  let wf (r : BitVec 64 × Flags) := (r.1, some r.2)
  match op with
  | "ADD" => nf (addSub sf false x y).1
  | "SUB" => nf (addSub sf true x y).1
  | "ADDS" => wf (addSub sf false x y)
  | "SUBS" => wf (addSub sf true x y)
  | "AND" => nf (logical sf 0 x y).1
  | "ORR" => nf (logical sf 1 x y).1
  | "EOR" => nf (logical sf 2 x y).1
  | "ANDS" => wf (logical sf 3 x y)
  | "BIC" => nf (logical sf 0 x (trunc sf (~~~y))).1
  | "ORN" => nf (logical sf 1 x (trunc sf (~~~y))).1
  | "EON" => nf (logical sf 2 x (trunc sf (~~~y))).1
  | "BICS" => wf (logical sf 3 x (trunc sf (~~~y)))
  | "ADC" | "ADCS" | "SBC" | "SBCS" =>
    let r := sizedF sf fun _ e =>
      GoFV.SSA.Sem.addWithCarry (e x) (if op.startsWith "S" then ~~~(e y) else e y) cin
    if op.endsWith "S" then wf r else nf r.1
  | "MUL" => nf (sized sf fun _ e => e x * e y)
  | "MNEG" => nf (sized sf fun _ e => -(e x * e y))
  | "UDIV" => nf (dp2Op sf 2 x y)
  | "SDIV" => nf (dp2Op sf 3 x y)
  | "REM" => nf (sized sf fun _ e => GoFV.SSA.Sem.Arm64.srem (e x) (e y))
  | "UREM" => nf (sized sf fun _ e => GoFV.SSA.Sem.Arm64.urem (e x) (e y))
  | "LSL" => nf (dp2Op sf 8 x y)
  | "LSR" => nf (dp2Op sf 9 x y)
  | "ASR" => nf (dp2Op sf 10 x y)
  | "ROR" => nf (dp2Op sf 11 x y)
  | "SMULH" => nf (GoFV.SSA.Sem.Arm64.smulh x y)
  | "UMULH" => nf (GoFV.SSA.Sem.Arm64.umulh x y)
  | "SMULL" => nf (GoFV.SSA.Sem.Arm64.smull x y)
  | _ => nf (GoFV.SSA.Sem.Arm64.umull x y)

/-- Loads and stores of the `MOV` family: bytes, sign extension, register file. -/
def movMem (name : String) : Option (Nat × Bool × Bool) :=
  match name with
  | "MOVD" => some (8, false, false) | "MOVW" => some (4, true, false)
  | "MOVWU" => some (4, false, false) | "MOVH" => some (2, true, false)
  | "MOVHU" => some (2, false, false) | "MOVB" => some (1, true, false)
  | "MOVBU" => some (1, false, false) | "FMOVD" => some (8, false, true)
  | "FMOVS" => some (4, false, true) | "FMOVQ" => some (16, false, true)
  | _ => none

def sextTo64 (n : Nat) (x : BitVec 64) : BitVec 64 := GoFV.SSA.Sem.Arm64.sext (8 * n) x

/-- Pair loads and stores: element bytes, sign extension, register file. -/
def pairOp (name : String) : Option (Bool × Nat × Bool × Bool) :=
  match name with
  | "LDP" => some (true, 8, false, false) | "STP" => some (false, 8, false, false)
  | "LDPW" => some (true, 4, false, false) | "STPW" => some (false, 4, false, false)
  | "LDPSW" => some (true, 4, true, false)
  | "FLDPD" => some (true, 8, false, true) | "FSTPD" => some (false, 8, false, true)
  | "FLDPS" => some (true, 4, false, true) | "FSTPS" => some (false, 4, false, true)
  | "FLDPQ" => some (true, 16, false, true) | "FSTPQ" => some (false, 16, false, true)
  | _ => none

def bcond (name : String) : Option Nat :=
  match name with
  | "BEQ" => some 0 | "BNE" => some 1 | "BCS" | "BHS" => some 2 | "BCC" | "BLO" => some 3
  | "BMI" => some 4 | "BPL" => some 5 | "BVS" => some 6 | "BVC" => some 7 | "BHI" => some 8
  | "BLS" => some 9 | "BGE" => some 10 | "BLT" => some 11 | "BGT" => some 12 | "BLE" => some 13
  | _ => none

/-- Atomic read-modify-writes `Rs, (Rn), Rt`: bytes and the combination. -/
def rmw (name : String) : Option (Nat × (BitVec 64 → BitVec 64 → BitVec 64)) :=
  let sz (s : String) : Nat := if s == "D" then 8 else if s == "W" then 4 else if s == "H" then 2 else 1
  let pre (p : String) : Option String := if name.startsWith p then some (dropS name p.length) else none
  match pre "LDADDAL", pre "SWPAL", pre "LDCLRAL", pre "LDORAL", pre "LDEORAL" with
  | some s, _, _, _, _ => some (sz s, fun old v => old + v)
  | _, some s, _, _, _ => some (sz s, fun _ v => v)
  | _, _, some s, _, _ => some (sz s, fun old v => old &&& ~~~v)
  | _, _, _, some s, _ => some (sz s, fun old v => old ||| v)
  | _, _, _, _, some s => some (sz s, fun old v => old ^^^ v)
  | _, _, _, _, _ => none

def suffixBytes (s : String) : Nat := if s == "" then 8 else if s == "W" then 4 else if s == "H" then 2 else 1

def maskN (n : Nat) (x : BitVec 64) : BitVec 64 := if n == 8 then x else x &&& BitVec.ofNat 64 (2 ^ (8 * n) - 1)

/-! ## Floating point by opcode -/

def fpType (name : String) : BitVec 2 := if name.endsWith "S" then 0 else 1

/-- The bits of an `FCONST` operand at single (`ftype` 0) or double precision. -/
def fconst (ftype : BitVec 2) (a : Addr) : Except String (BitVec 128) :=
  match a.val with
  | .float bits =>
    let d : BitVec 64 := BitVec.ofNat 64 bits.toNat
    if ftype = 0 then pure ((GoFV.IEEE.convert GoFV.IEEE.Fmt.b64 GoFV.IEEE.Fmt.b32 .rne d).setWidth 128)
    else pure (d.setWidth 128)
  | _ => throw "FCONST without a value"

/-- The effect of a Prog (in Go's operand conventions). -/
def progEffect (c : Ctx) : Spec := do
  let p := c.p
  let name := p.as.name
  let e : Eff := {}
  -- three-operand integer ops and their compare forms
  if let some (op, sf) := baseOf name binNames then
    if p.from_.type == .CONST && ["LSL", "LSR", "ASR", "ROR"].contains op then
      let x ← c.src sf { type := .REG, reg := c.rn }
      let (r, _) := binOp op sf x (trunc sf (BitVec.ofInt 64 p.from_.offset)) false
      return ← e.wX p.to.reg r
    let x ← c.src sf { type := .REG, reg := c.rn }
    let y ← c.src sf p.from_
    let (r, f) := binOp op sf x y c.s.nzcv.c
    let e ← e.wX p.to.reg r
    return { e with flags := f }
  if let some (op, sf) := baseOf name ["CMP", "CMN", "TST"] then
    let x ← c.src sf { type := .REG, reg := p.reg }
    let y ← c.src sf p.from_
    let op' := if op == "CMP" then "SUBS" else if op == "CMN" then "ADDS" else "ANDS"
    return { e with flags := (binOp op' sf x y false).2 }
  if let some (op, sf) := baseOf name ["NEG", "NEGS", "MVN", "NGC", "NGCS"] then
    let y ← c.src sf p.from_
    let op' := match op with
      | "NEG" => "SUB" | "NEGS" => "SUBS" | "MVN" => "ORN" | "NGC" => "SBC" | _ => "SBCS"
    let (r, f) := binOp op' sf 0 y c.s.nzcv.c
    let e ← e.wX p.to.reg r
    return { e with flags := f }
  if let some (op, sf) := baseOf name ["CLZ", "RBIT", "REV", "REV16", "REV32"] then
    let x ← c.x p.from_.reg
    let opc : BitVec 3 := match op with
      | "RBIT" => 0 | "REV16" => 1 | "REV32" => 2 | "REV" => if sf then 3 else 2 | _ => 4
    return ← e.wX p.to.reg (dp1Op sf opc x)
  if let some (op, sf) := baseOf name ["MADD", "MSUB"] then
    -- `asmout` case 15: `Rm` = from, `Ra` = reg, `Rn` = the RestArgs operand
    let m ← c.x p.from_.reg
    let a ← c.x p.reg
    let n ← c.x (← c.rest 0).reg
    return ← e.wX p.to.reg (dp3Op sf 0 (op == "MSUB") a n m)
  if let some (op, sf) := baseOf name ["UBFX", "SBFX", "UBFIZ", "SBFIZ", "BFI", "BFXIL"] then
    let lsb := p.from_.offset.toNat
    let width := (← c.rest 0).offset.toNat
    let k : Int64 := Int64.ofNat (lsb * 256 + width)
    let x ← c.x p.reg
    let d ← c.x p.to.reg
    let r := match op with
      | "UBFX" => GoFV.SSA.Sem.Arm64.ubfx k (trunc sf x)
      | "SBFX" => GoFV.SSA.Sem.Arm64.sbfx k (trunc sf x)
      | "UBFIZ" => GoFV.SSA.Sem.Arm64.ubfiz k x
      | "SBFIZ" => GoFV.SSA.Sem.Arm64.sbfiz k x
      | "BFI" => GoFV.SSA.Sem.Arm64.bfi k d x
      | _ => GoFV.SSA.Sem.Arm64.bfxil k d (trunc sf x)
    return ← e.wX p.to.reg (trunc sf r)
  if let some (_, sf) := baseOf name ["EXTR"] then
    let lsb := p.from_.offset.toNat
    -- `asmout` case 44: `Rn` (high half) = the RestArgs operand, `Rm` = reg
    let n ← c.x (← c.rest 0).reg
    let m ← c.x p.reg
    return ← e.wX p.to.reg (sized sf fun _ e => GoFV.SSA.Sem.Arm64.extr lsb (e n) (e m))
  if let some (op, sf) := baseOf name ["CSEL", "CSINC", "CSINV", "CSNEG"] then
    let cond ← condOfSpecial p.from_
    let n ← c.x p.reg
    let m ← c.x (← c.rest 0).reg
    let r := if c.s.holds cond then trunc sf n else
      let y := trunc sf m
      match op with
      | "CSINC" => trunc sf (y + 1) | "CSINV" => trunc sf (~~~y) | "CSNEG" => trunc sf (-y) | _ => y
    return ← e.wX p.to.reg r
  if let some (op, sf) := baseOf name ["CSET", "CSETM"] then
    let cond ← condOfSpecial p.from_
    let r : BitVec 64 := if c.s.holds cond then (if op == "CSET" then 1 else trunc sf (-1)) else 0
    return ← e.wX p.to.reg r
  -- moves, loads and stores
  if let some (n, signed, fp) := movMem name then
    match p.from_.type, p.to.type with
    | .MEM, _ =>
      let (a, wb) ← c.mem p.from_
      let e ← match wb with
        | some (r, b) => e.wX r b
        | none => pure e
      if fp then return ← e.wV p.to.reg ((readMem c.s.mem a n).setWidth 128)
      let raw := c.load a n
      return ← e.wX p.to.reg (if signed then sextTo64 n raw else raw)
    | _, .MEM =>
      let (a, wb) ← c.mem p.to
      let e ← match wb with
        | some (r, b) => e.wX r b
        | none => pure e
      let val : Nat ← if fp then pure ((← c.v p.from_.reg).toNat % 2 ^ (8 * n))
        else pure ((← c.x p.from_.reg).toNat % 2 ^ (8 * n))
      return { e with stores := (a, n, val) :: e.stores }
    | .REG, .REG =>
      match fpIdx? p.from_.reg, fpIdx? p.to.reg with
      | some _, some _ => return ← e.wV p.to.reg ((maskN n ((← c.v p.from_.reg).setWidth 64)).setWidth 128)
      | some _, none => return ← e.wX p.to.reg (maskN n ((← c.v p.from_.reg).setWidth 64))
      | none, some _ => return ← e.wV p.to.reg ((maskN n (← c.x p.from_.reg)).setWidth 128)
      | none, none =>
        let x ← c.x p.from_.reg
        return ← e.wX p.to.reg (if signed then sextTo64 n x else maskN n x)
    | .CONST, .REG =>
      let k := BitVec.ofInt 64 p.from_.offset
      return ← e.wX p.to.reg (maskN n k)
    | .FCONST, .REG => return ← e.wV p.to.reg (← fconst (if n == 4 then 0 else 1) p.from_)
    | .ADDR, .REG =>
      let (a, _) ← c.mem { p.from_ with type := .MEM }
      return ← e.wX p.to.reg a
    | t, u => throw s!"operands {t.name},{u.name}"
  if let some (ld, n, signed, fp) := pairOp name then
    let (memA, regs) := if ld then (p.from_, p.to) else (p.to, p.from_)
    if regs.type != .REGREG then throw s!"pair operand {regs.type.name}"
    let (a, wb) ← c.mem memA
    let e ← match wb with
      | some (r, b) => e.wX r b
      | none => pure e
    let r1 := regs.reg
    let r2 := regs.offset
    let nb := BitVec.ofNat 64 n
    if ld then
      if fp then
        let e ← e.wV r1 ((readMem c.s.mem a n).setWidth 128)
        return ← e.wV r2 ((readMem c.s.mem (a + nb) n).setWidth 128)
      let ext (x : BitVec 64) := if signed then sextTo64 n x else x
      let e ← e.wX r1 (ext (c.load a n))
      return ← e.wX r2 (ext (c.load (a + nb) n))
    else
      let val (r : Int) : Except String Nat :=
        if fp then return (← c.v r).toNat % 2 ^ (8 * n) else return (← c.x r).toNat % 2 ^ (8 * n)
      return { e with stores := (a, n, ← val r1) :: (a + nb, n, ← val r2) :: e.stores }
  -- atomics and ordered accesses
  if name.startsWith "LDAR" || name.startsWith "LDAXR" then
    let n := suffixBytes (if name.startsWith "LDAR" then (dropS name 4) else (dropS name 5))
    let (a, _) ← c.mem p.from_
    return ← e.wX p.to.reg (c.load a n)
  if name.startsWith "STLR" || name.startsWith "STLXR" then
    let n := suffixBytes (if name.startsWith "STLR" then (dropS name 4) else (dropS name 5))
    let (a, _) ← c.mem p.to
    let e ← if name.startsWith "STLXR" then e.wX p.regTo2 0 else pure e
    return { e with stores := (a, n, (← c.x p.from_.reg).toNat % 2 ^ (8 * n)) :: e.stores }
  if name.startsWith "CASAL" then
    let n := suffixBytes (dropS name 5)
    let (a, _) ← c.mem p.to
    let old := c.load a n
    let cmp := maskN n (← c.x p.from_.reg)
    let e ← e.wX p.from_.reg old
    if old == cmp then
      return { e with stores := [(a, n, (← c.x p.regTo2).toNat % 2 ^ (8 * n))] }
    return e
  if let some (n, f) := rmw name then
    let (a, _) ← c.mem p.to
    let old := c.load a n
    let nw := maskN n (f old (← c.x p.from_.reg))
    let e ← e.wX p.regTo2 old
    return { e with stores := [(a, n, nw.toNat)] }
  -- floating point
  let ft := fpType name
  match name with
  | "FADDD" | "FADDS" | "FSUBD" | "FSUBS" | "FMULD" | "FMULS" | "FDIVD" | "FDIVS"
  | "FMAXD" | "FMAXS" | "FMIND" | "FMINS" | "FNMULD" | "FNMULS" =>
    let opc : BitVec 4 := match chopS name 1 with
      | "FMUL" => 0 | "FDIV" => 1 | "FADD" => 2 | "FSUB" => 3 | "FMAX" => 4 | "FMIN" => 5
      | _ => 8
    return ← e.wV p.to.reg (fp2Op ft opc (← c.v c.rn) (← c.v p.from_.reg))
  | "FMADDD" | "FMADDS" | "FMSUBD" | "FMSUBS" | "FNMADDD" | "FNMADDS" | "FNMSUBD" | "FNMSUBS" =>
    let (o1, o0) := match chopS name 1 with
      | "FMADD" => (false, false) | "FMSUB" => (false, true) | "FNMADD" => (true, false)
      | _ => (true, true)
    return ← e.wV p.to.reg (fp3Op ft o1 o0 (← c.v p.reg) (← c.v (← c.rest 0).reg) (← c.v p.from_.reg))
  | "FNEGD" | "FNEGS" | "FABSD" | "FABSS" | "FSQRTD" | "FSQRTS" | "FRINTND" | "FRINTPD"
  | "FRINTMD" | "FRINTZD" | "FRINTAD" | "FRINTNS" | "FRINTPS" | "FRINTMS" | "FRINTZS"
  | "FRINTAS" =>
    let opc : BitVec 6 := match chopS name 1 with
      | "FABS" => 1 | "FNEG" => 2 | "FSQRT" => 3 | "FRINTN" => 8 | "FRINTP" => 9 | "FRINTM" => 10
      | "FRINTZ" => 11 | _ => 12
    return ← e.wV p.to.reg (fp1Op ft opc (← c.v p.from_.reg))
  | "FCVTSD" => return ← e.wV p.to.reg (fp1Op 0 5 (← c.v p.from_.reg))
  | "FCVTDS" => return ← e.wV p.to.reg (fp1Op 1 4 (← c.v p.from_.reg))
  | "FCMPD" | "FCMPS" | "FCMPED" | "FCMPES" =>
    let y ← if p.from_.type == .FCONST then pure 0 else c.v p.from_.reg
    return { e with flags := some (fcmpOp ft (← c.v p.reg) y) }
  | "FCSELD" | "FCSELS" =>
    let cond ← condOfSpecial p.from_
    let n ← c.v p.reg
    let m ← c.v (← c.rest 0).reg
    let r := if c.s.holds cond then n else m
    return ← e.wV p.to.reg (fpUn ft (fun _ a => a) r)
  | _ => pure ()
  -- conversions: FCVTZ{S,U}{D,S}[W], {S,U}CVTF[W]{D,S}
  if name.startsWith "FCVTZ" then
    let u := (dropS name 5).startsWith "U"
    let rest := (dropS name 6)
    let src : BitVec 2 := if rest.startsWith "S" then 0 else 1
    let w := rest.endsWith "W"
    let x ← c.v p.from_.reg
    let r : BitVec 64 := if src = 0
      then (GoFV.IEEE.toFixed GoFV.IEEE.Fmt.b32 (x.setWidth 32) u (if w then 32 else 64) .rz).setWidth 64
      else (GoFV.IEEE.toFixed GoFV.IEEE.Fmt.b64 (x.setWidth 64) u (if w then 32 else 64) .rz).setWidth 64
    return ← e.wX p.to.reg r
  if name.startsWith "SCVTF" || name.startsWith "UCVTF" then
    let u := name.startsWith "U"
    let rest := (dropS name 5)
    let w := rest.startsWith "W"
    let dst : BitVec 2 := if rest.endsWith "S" then 0 else 1
    let m := if w then 32 else 64
    let x := (← c.x p.from_.reg).setWidth m
    let r : BitVec 128 := if dst = 0
      then (GoFV.IEEE.fromFixed GoFV.IEEE.Fmt.b32 m x u .rne).setWidth 128
      else (GoFV.IEEE.fromFixed GoFV.IEEE.Fmt.b64 m x u .rne).setWidth 128
    return ← e.wV p.to.reg r
  -- branches
  if let some k := bcond name then
    let t ← c.target p.to
    return if c.s.holds (BitVec.ofNat 4 k) then { e with pc := some t } else e
  match name with
  | "JMP" =>
    if p.to.type == .BRANCH then return { e with pc := some (← c.target p.to) }
    return { e with pc := some (← c.x p.to.reg) }
  | "CBZ" | "CBNZ" | "CBZW" | "CBNZW" =>
    let sf := !name.endsWith "W"
    let z := trunc sf (← c.x p.from_.reg) == 0
    let t ← c.target p.to
    return if z == name.startsWith "CBZ" then { e with pc := some t } else e
  | "TBZ" | "TBNZ" =>
    let b := (← c.x p.reg).getLsbD p.from_.offset.toNat
    let t ← c.target p.to
    return if b == (name == "TBNZ") then { e with pc := some t } else e
  | "CALL" =>
    let t ← if p.to.type == .BRANCH then c.target p.to else c.x p.to.reg
    let e ← e.wX (REG_R0 + 30) (BASE + BitVec.ofInt 64 p.pc + 4)
    return { e with pc := some t }
  | "RET" =>
    let r := if p.to.type == .NONE then REG_R0 + 30 else p.to.reg
    return { e with pc := some (← c.x r) }
  | "NOP" | "HINT" | "DMB" | "PRFM" => return e
  | "VCNT" => return ← e.wV p.to.reg ((GoFV.SSA.Sem.Arm64.vcnt ((← c.v p.from_.reg).setWidth 64)).setWidth 128)
  | "VUADDLV" =>
    return ← e.wV p.to.reg ((GoFV.SSA.Sem.Arm64.vuaddlv ((← c.v p.from_.reg).setWidth 64)).setWidth 128)
  | _ => throw "opcode not specified"

/-! ## Relocations (as the linker applies them) -/

def getW (t : ByteArray) (o : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((t[o]!).toNat + (t[o+1]!).toNat * 256 + (t[o+2]!).toNat * 65536 +
    (t[o+3]!).toNat * 16777216)

def putW (t : ByteArray) (o : Nat) (w : BitVec 32) : ByteArray := Id.run do
  let mut t := t
  for j in [0:4] do t := t.set! (o + j) (w.toNat / 256 ^ j % 256).toUInt8
  t

def setBits (w : BitVec 32) (lo len : Nat) (v : Nat) : BitVec 32 :=
  let m : BitVec 32 := BitVec.ofNat 32 ((2 ^ len - 1) * 2 ^ lo)
  (w &&& ~~~m) ||| BitVec.ofNat 32 ((v % 2 ^ len) * 2 ^ lo)

/-- Patch the text with the relocations the decoder check understands. -/
def applyRelocs (text : ByteArray) (rs : Array Reloc) : ByteArray := Id.run do
  let mut t := text
  for r in rs do
    let o := r.off.toNat
    match r.sym with
    | none => pure ()
    | some n =>
      let target := symAddr n + BitVec.ofInt 64 r.add
      let pc := BASE + BitVec.ofNat 64 o
      let adrp (w : BitVec 32) : BitVec 32 :=
        let pages := ((target >>> 12) - (pc >>> 12)).toNat
        setBits (setBits w 29 2 pages) 5 19 (pages / 4)
      -- `RelocType(-32759)` is `R_WEAK | R_CALLARM64` (`weakenGlobalMapInitRelocs`): the linker
      -- patches it like `R_CALLARM64` when the target is live
      if (r.type == "R_CALLARM64" || r.type == "RelocType(-32759)") && o + 4 ≤ t.size then
        t := putW t o (setBits (getW t o) 0 26 ((target - pc) >>> 2).toNat)
      else if r.type == "R_ADDRARM64" && o + 8 ≤ t.size then
        t := putW t o (adrp (getW t o))
        t := putW t (o + 4) (setBits (getW t (o + 4)) 10 12 (target.toNat % 4096))
      else if r.type.startsWith "R_ARM64_PCREL_LDST" && o + 8 ≤ t.size then
        let sc := match dropS r.type 18 with
          | "8" => 0 | "16" => 1 | "32" => 2 | "64" => 3 | _ => 0
        t := putW t o (adrp (getW t o))
        t := putW t (o + 4) (setBits (getW t (o + 4)) 10 12 (target.toNat % 4096 / 2 ^ sc))
  t

/-! ## Random states -/

def mix (x : UInt64) : UInt64 :=
  let x := x ^^^ (x >>> 33)
  let x := x * 0xff51afd7ed558ccd
  let x := x ^^^ (x >>> 33)
  let x := x * 0xc4ceb9fe1a85ec53
  x ^^^ (x >>> 33)

def randState (seed : UInt64) (text : ByteArray) (pc : BitVec 64) : MState :=
  let r (k : Nat) : BitVec 64 := BitVec.ofNat 64 (mix (seed + k.toUInt64 * 0x9E3779B97F4A7C15)).toNat
  -- registers with small low bits half of the time, so shift amounts and bit numbers vary; never
  -- below 4096, so that accesses through them do not fault in the nil page
  let rx (k : Nat) : BitVec 64 := if (r (k + 1000)).getLsbD 0 then r k else 0x10000 + (r k &&& 0xFF)
  { x := fun i => rx i.toNat
    sp := 0x7FFF00000000 + (r 40 &&& 0xFFFF0)
    v := fun i => ((r (64 + 2 * i.toNat)).setWidth 128 <<< 64) ||| (r (65 + 2 * i.toNat)).setWidth 128
    nzcv := GoFV.SSA.Sem.Flags.ofNZCV ((r 41).toNat % 16)
    pc
    mem := fun a =>
      let d := a - BASE
      if d.toNat < text.size then BitVec.ofNat 8 (text[d.toNat]!).toNat else pattern a }

/-! ## Checking one Prog -/

/-- Compare the result of executing the words with the effect. -/
def checkEff (s0 s : MState) (e : Eff) (next : BitVec 64) : Option String := Id.run do
  for k in [0:31] do
    if k == (REG_R27 - REG_R0).toNat then continue
    let want := match e.x.find? (·.1 == k) with
      | some (_, v) => v
      | none => s0.x (BitVec.ofNat 5 k)
    if s.x (BitVec.ofNat 5 k) != want then return some s!"R{k}"
  if s.sp != e.sp.getD s0.sp then return some "RSP"
  for k in [0:32] do
    let want := match e.v.find? (·.1 == k) with
      | some (_, v) => v
      | none => s0.v (BitVec.ofNat 5 k)
    if s.v (BitVec.ofNat 5 k) != want then return some s!"V{k}"
  if s.nzcv != e.flags.getD s0.nzcv then return some "flags"
  for (a, n, val) in e.stores do
    if (readMem s.mem a n).toNat != val then return some "store"
  if s.pc != e.pc.getD next then return some "pc"
  none

structure Stats where
  progs : Nat := 0
  code : Nat := 0
  matched : Nat := 0
  classes : Std.HashMap String (Nat × String) := {}
  words : Std.HashMap UInt32 Nat := {}
  files : Nat := 0
  bad : Nat := 0

def Stats.fail (st : Stats) (cls ex : String) : Stats :=
  { st with classes := st.classes.alter cls fun e => some ((e.map (·.1)).getD 0 + 1, (e.map (·.2)).getD ex),
            bad := st.bad + 1 }

def pseudo : List String := ["TEXT", "FUNCDATA", "PCDATA", "NOP"]

def checkFile (path : System.FilePath) (st : Stats) (collect : Bool) : IO Stats := do
  let data ← IO.FS.readBinFile path
  match parseProgFile data with
  | .error e => return st.fail "parse error" s!"{path}: {e}"
  | .ok f =>
    let a := f.asm
    let text := a.text
    let mut st := { st with files := st.files + 1 }
    if collect then
      let mut ws := st.words
      for k in [0:text.size / 4] do
        ws := ws.alter (getW text (4 * k)).toNat.toUInt32 (some <| ·.getD 0 + 1)
      st := { st with words := ws }
    let linked := applyRelocs text a.relocs
    let pcs : Std.HashMap Nat Int := a.progs.foldl (fun m p => m.insert p.id p.pc) {}
    let autosize := match a.progs[0]? with
      | some p => if p.as == .TEXT then p.to.offset else 0
      | none => 0
    let pre := match f.prog0.progs.find? (·.as == .TEXT) with
      | some p => p.to.offset
      | none => 0
    -- `preprocess`: autosize = frame size + 8 (saved LR) + extrasize (`obj7.go`), and `span7`
    -- drops the packed extrasize from the asm section's TEXT
    let extrasize := if autosize == 0 then 0 else autosize - pre - 8
    let code : Code := fun pc =>
      let d := pc - BASE
      if d.toNat % 4 == 0 && d.toNat + 4 ≤ linked.size then some (getW linked d.toNat) else none
    let ps := a.progs
    let mut lastEnd : Nat := 0
    for i in [0:ps.size] do
      let p := ps[i]!
      let nextPc := if h : i + 1 < ps.size then ps[i+1].pc else
        -- the last Prog: up to the padding
        if p.as.name == "DWORD" then p.pc + 8 else if pseudo.contains p.as.name then p.pc else p.pc + 4
      let size := (nextPc - p.pc).toNat
      st := { st with progs := st.progs + 1 }
      let key := s!"{p.as.name} optab {p.optab}"
      if pseudo.contains p.as.name then
        if size != 0 then st := st.fail s!"{key}: pseudo-op with code" s!"{path} @{p.id}"
        continue
      if size == 0 then
        st := st.fail s!"{key}: no code" s!"{path} @{p.id}"
        continue
      st := { st with code := st.code + 1 }
      lastEnd := p.pc.toNat + size
      if p.as.name == "WORD" || p.as.name == "DWORD" then
        let n := if p.as.name == "WORD" then 4 else 8
        let v := (List.range n).foldl (fun acc j => acc + (text[p.pc.toNat + j]!).toNat * 256 ^ j) 0
        if size == n && v == p.to.offset.toNat % 2 ^ (8 * n) then st := { st with matched := st.matched + 1 }
        else st := st.fail s!"{key}: data word" s!"{path} @{p.id}"
        continue
      -- decode every word
      let mut undec := none
      for k in [0:size / 4] do
        if (decode (getW linked (p.pc.toNat + 4 * k))).isNone then
          undec := some (getW linked (p.pc.toNat + 4 * k))
      if let some w := undec then
        st := st.fail s!"{key}: undecoded word" s!"{path} @{p.id} {w.toHex}"
        continue
      -- execute from three random states and compare with the Prog's effect
      let pc0 := BASE + BitVec.ofInt 64 p.pc
      let next := pc0 + BitVec.ofNat 64 size
      let mut err : Option String := none
      for t in [0:3] do
        let s0 := randState (UInt64.ofNat (p.id * 7919 + t * 104729 + st.files)) linked pc0
        let c : Ctx := { s := s0, p, pcOf := pcs.get?, autosize, extrasize }
        match progEffect c with
        | .error why => err := some why; break
        | .ok e =>
          let steps := if e.pc.isSome then 1 else size / 4
          match run code steps s0 with
          | .error flt =>
            err := some (match flt with
              | .nilPage _ => "fault: nil page" | .undefined _ => "fault: undefined"
              | .noCode _ => "fault: no code"); break
          | .ok s =>
            if let some d := checkEff s0 s e next then
              err := some s!"differs in {d}"; break
      match err with
      | none => st := { st with matched := st.matched + 1 }
      | some why => st := st.fail s!"{key}: {why}" s!"{path} @{p.id}"
    -- padding after the last Prog
    let mut pad := true
    for k in [lastEnd:text.size] do
      if text[k]! != 0 then pad := false
    if !pad then st := st.fail "padding: nonzero bytes after the last Prog" s!"{path}"
    return st

def progFiles (p : System.FilePath) : IO (Array System.FilePath) := do
  if ← p.isDir then
    let fs ← p.walkDir
    return (fs.filter (·.extension == some "prog")).qsort (·.toString < ·.toString)
  else return #[p]

def main (args : List String) : IO UInt32 := do
  let rec opts : List String → Option String × List String
    | "--words" :: f :: rest => let (_, r) := opts rest; (some f, r)
    | rest => (none, rest)
  let (wordsOut, paths) := opts args
  if paths.isEmpty then
    IO.eprintln "usage: arm64-decode [--words FILE] <dir|file>..."
    return 2
  let mut st : Stats := {}
  for a in paths do
    for f in ← progFiles a do
      st ← checkFile f st wordsOut.isSome
  let rows := st.classes.toArray.qsort fun a b => a.2.1 > b.2.1 || (a.2.1 == b.2.1 && a.1 < b.1)
  for (k, (n, ex)) in rows do IO.println s!"{n} {k} (e.g. {ex})"
  IO.println s!"arm64-decode: {st.files} files, {st.progs} asm Progs, {st.code} with code, \
    {st.matched} match, {st.bad} do not ({rows.size} classes)"
  if let some out := wordsOut then
    let ws := st.words.toArray.qsort fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1)
    let mut s := ""
    for (w, n) in ws do
      s := s ++ s!"{(BitVec.ofNat 32 w.toNat).toHex} {n}\n"
    IO.FS.writeFile out s
  return if st.bad == 0 then 0 else 1

end GoFVTest.Arm64Decode

def main (args : List String) : IO UInt32 := GoFVTest.Arm64Decode.main args
