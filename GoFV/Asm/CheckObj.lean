import GoFV.Asm.CheckObjSym

variable [GoFV.SSA.Sem.Addrs]

/-!
# `checkObj`: the assembler validator (`docs/plans/proofs3.md` §2, row D2–D5)

`checkObj ps spills obj` checks the assembled function `obj` (text bytes, relocations, and the
assembler's Prog list as a hint for the PC of each Prog) against the P0 Prog list `ps` (genssa's
output, the list `runProg` runs on under `Link.byId`). It recomputes none of the assembler's
choices (`progedit`, `preprocess`, `span7`: classes, sizes, constant materialisation,
literal pools); it decodes the words and compares effects:

* **Layout.** Each P0 Prog owns the words from its PC to the PC of the next P0 Prog (`Tab.offs`);
  the hint's PCs only choose the cut, every word is checked. `TEXT` owns nothing: the prologue
  in front of the first body Prog is checked as a template (below), and `TEXT`'s offset is the
  prologue's end, so the skip `TEXT` steps to the body without machine steps.
* **Per Prog** (`checkProg`): a pseudo-op (`Prog.isSkip`) owns no words. Any other Prog's words
  are decoded (`GoFV.Arm64.decode`) and executed symbolically (`symInsn`; the word pairs of an
  `R_ADDRARM64` or `R_ARM64_PCREL_LDST*` relocation and the `BL` of an `R_CALLARM64` as the
  linker patches them, `symWords`), every word but the last falling through; the Prog's effect
  is computed symbolically from its operands (`progSym`). The two `Sym`s must agree on every
  general register but `X27` (the assembler's scratch) and `X30` (written only by calls), on
  every vector register, on `SP`, the flags and the stores in order, every machine load must be
  a load of the Prog, the Prog must not read `X27` or `X30`, and the control must agree: a
  branch to the offset of the target Prog, a call to the same symbol and addend, a return
  through the same register. The templates below write no vector register.
* **Prologue** (`checkPrologue`): the stack check (`stacksplit`: `MOVD 16(g), R16`, the compare
  of `SP` or `SP − (framesize − StackSmall)`, `BLS` to the morestack tail) when present, then the
  frame (`MOVD.W R30, -autosize(RSP)`; `MOVD R29, -8(RSP)`; `SUB $8, RSP, R29`, or the large-frame
  form through `R20`), compared with its specification (`frameSym`).
* **Epilogue**: a P0 `RET` of a framed function owns the epilogue, compared with `retSym` (a leaf
  restores `R29` from `SP`, others reload `R29` and `R30`; both pop the frame and return through
  `R30`).
* **Morestack tail** (`checkTail`): the register-argument spills of `FuncInfo.spills`, `MOVD R30,
  R3`, the call, the reloads and the jump back to the stack check.

Words after the tail (literal pools, jump tables, padding) are never executed by the checked
ranges.

The result `Tab` gives each P0 Prog's offset, the offset the last one falls through to, the
frame size and kind; `GoFV/Proof/Obj/` proves that a `runProg` step of an accepted Prog is matched
by `runMach` steps of the linked words.
-/

namespace GoFV.Asm.CheckObj

open GoFV.Arm64 GoFV.Arm64.ProgOp
open GoFV.Asm.ARM64 (REG_R0 REG_R31 REG_RSP REG_EXT REG_LSL C_XPRE C_XPOST)

/-! ## The P0 side -/

/-- Where a Prog goes after its effect. -/
inductive PCtl where
  | fall
  | jmp (id : Nat)
  | cond (c : BitVec 4) (id : Nat)
  | cbz (sf nz : Bool) (a : Ex) (id : Nat)
  | tbz (nz : Bool) (b : Nat) (a : Ex) (id : Nat)
  | reg (a : Ex)
  | call (n : Nat) (add : Int)
  /-- `CALL (Rn)`: to the register's value. -/
  | callReg (a : Ex)
  deriving DecidableEq, Repr, Inhabited

/-- A general register operand (`ProgCtx.x`): `RSP` is `SP`, `ZR` reads zero. -/
def xP (r : Int) : Except String Ex :=
  if r == REG_RSP then pure .sp
  else match gpIdx? r with
    | some 31 => pure (.k 0)
    | some i => pure (.x i)
    | none => throw s!"register {r}"

/-- A register write (`Eff.wX`). -/
def wP (σ : Sym) (r : Int) (v : Ex) : Except String Sym :=
  if r == REG_R31 then pure σ
  else if r == REG_RSP then pure { σ with sp := v }
  else match gpIdx? r with
    | some i => pure { σ with x := (i, v) :: σ.x }
    | none => throw s!"destination register {r}"

/-- A source operand at the datasize (`ProgCtx.src`) for an operation that reads it at that
width: the register is not truncated (the operation's `sized` does it), a constant is. -/
def srcP (sf : Bool) (a : Addr) : Except String Ex := do
  match a.type with
  | .REG =>
    match extReg? a.reg with
    | some (r, opt, amt) => pure (Ex.mkExt (BitVec.ofNat 3 opt) amt (if r = 31 then .k 0 else .x r))
    | none => xP a.reg
  | .CONST => pure (.k (trunc sf (BitVec.ofInt 64 a.offset)))
  | .SHIFT =>
    let off := a.offset.toNat
    let r := off / 65536 % 32
    pure (Ex.mkShift sf (BitVec.ofNat 2 (off / 4194304 % 4)) (off / 1024 % 64)
      (if r = 31 then .k 0 else .x r))
  | t => throw s!"source operand {t.name}"

/-- The address of a memory operand and the base register's write-back (`ProgCtx.mem`). -/
def memP (az ez : Int) (scond : Nat) (a : Addr) : Except String (Ex × Option (Int × Ex)) := do
  if a.type != .MEM && a.type != .ADDR then throw s!"memory operand {a.type.name}"
  let off := BitVec.ofInt 64 a.offset
  match a.name with
  | .AUTO => pure (Ex.mkAdd .sp (.k (BitVec.ofInt 64 (az + a.offset - ez))), none)
  | .PARAM => pure (Ex.mkAdd .sp (.k (BitVec.ofInt 64 (az + a.offset + 8))), none)
  | .EXTERN | .STATIC =>
    match a.sym with
    | some n => pure (Ex.mkAdd (.sym n) (.k off), none)
    | none => throw "symbol-less extern"
  | .NONE =>
    let base ← xP a.reg
    if a.index != 0 then
      let d := (a.index - REG_R0).toNat
      let rx (k : Nat) : Ex := if k = 31 then .k 0 else .x k
      let idx ← if REG_EXT ≤ a.index && a.index < REG_EXT + 4096 then
          pure (Ex.mkExt (BitVec.ofNat 3 (d / 256 % 8)) (d / 32 % 8) (rx (d % 32)))
        else if REG_LSL ≤ a.index && a.index < REG_LSL + 512 then
          pure (Ex.mkExt 3 (d / 32 % 8) (rx (d % 32)))
        else xP a.index
      pure (Ex.mkAdd base idx, none)
    else if scond == C_XPRE.toNat then pure (Ex.mkAdd base (.k off), some (a.reg, Ex.mkAdd base (.k off)))
    else if scond == C_XPOST.toNat then pure (base, some (a.reg, Ex.mkAdd base (.k off)))
    else pure (Ex.mkAdd base (.k off), none)
  | n => throw s!"memory name {n.name}"

/-- A branch target Prog. -/
def targetP (a : Addr) : Except String Nat :=
  match a.type, a.val with
  | .BRANCH, .target id => pure id
  | _, _ => throw "branch target"

/-- The bitfield move the assembler encodes a constant shift as (`LSL`/`LSR`/`ASR $k`). -/
def shiftBfm (op : String) (sf : Bool) (k : Nat) (x : Ex) : Except String Ex :=
  let w := if sf then 64 else 32
  if k = 0 || k ≥ w then throw s!"shift amount {k}" else
  match op with
  | "LSL" => pure (Ex.mkBfm sf 2 (BitVec.ofNat 6 ((w - k) % w)) (BitVec.ofNat 6 (w - 1 - k)) (.k 0) x)
  | "LSR" => pure (Ex.mkBfm sf 2 (BitVec.ofNat 6 k) (BitVec.ofNat 6 (w - 1)) (.k 0) x)
  | "ASR" => pure (Ex.mkBfm sf 0 (BitVec.ofNat 6 k) (BitVec.ofNat 6 (w - 1)) (.k 0) x)
  | _ => throw s!"constant {op}"

/-- The `RestArgs` operand `i`. -/
def restP (p : Prog) (i : Nat) : Except String Addr :=
  match p.rest[i]? with
  | some (_, a) => pure a
  | none => throw "missing RestArgs operand"

/-- `MUL`/`MNEG`/`MADD`/`MSUB` (and `W`), `UMULH`, `SMULH`: the data-processing (3 source) form
the assembler encodes them as (`MUL` is `MADD` with `ZR` as the addend). -/
def mulP (op : String) (sf : Bool) (p : Prog) : Except String (Sym × PCtl) := do
  let rn : Int := if p.reg != 0 then p.reg else p.to.reg
  let r ← match op with
    | "MADD" | "MSUB" => do
      let m ← xP p.from_.reg
      let a ← xP p.reg
      let n ← xP (← restP p 0).reg
      pure (Ex.mkDp3 sf 0 (op == "MSUB") a n m)
    | "UMULH" | "SMULH" =>
      if !sf then throw s!"{op}W" else do
      let x ← xP rn
      let y ← srcP true p.from_
      pure (Ex.mkDp3 true (if op == "UMULH" then 6 else 2) false (.k 0) x y)
    | _ => do
      let x ← xP rn
      let y ← srcP sf p.from_
      pure (Ex.mkDp3 sf 0 (op == "MNEG") (.k 0) x y)
  return (← wP {} p.to.reg r, .fall)

/-- `CLZ`/`RBIT`/`REV`/`REV16`/`REV32` (and `W`): data-processing (1 source). -/
def dp1P (op : String) (sf : Bool) (p : Prog) : Except String (Sym × PCtl) := do
  let opc : BitVec 3 := match op with
    | "RBIT" => 0 | "REV16" => 1 | "REV32" => 2 | "REV" => if sf then 3 else 2 | _ => 4
  let x ← xP p.from_.reg
  return (← wP {} p.to.reg (.dp1 sf opc x), .fall)

/-- `ROR` by a register, `UDIV`/`SDIV`, `REM`/`UREM`, `BIC`/`ORN`/`EON` and `MVN` (and `W`), as
the assembler encodes them: variable shifts and divisions as data-processing (2 source)
(`Ex.mkDp2`), `REM`/`UREM` as the division into `REGTMP` and `MSUB` (`asmout` case 16), `BIC`/
`ORN`/`EON` as the logical operation of the inverted operand (`Ex.mkInv`), `MVN` as `ORN` with
`ZR`. -/
def dp2P (op : String) (sf : Bool) (p : Prog) : Except String (Sym × PCtl) := do
  let rn : Int := if p.reg != 0 then p.reg else p.to.reg
  let r ← match op with
    | "MVN" => do
      let y ← srcP sf p.from_
      pure (Ex.mkLogical sf 1 (.k 0) (Ex.mkInv sf y))
    | "BIC" | "ORN" | "EON" => do
      let x ← xP rn
      let y ← srcP sf p.from_
      pure (Ex.mkLogical sf (if op == "BIC" then 0 else if op == "ORN" then 1 else 2) x
        (Ex.mkInv sf y))
    | "REM" | "UREM" => do
      let x ← xP rn
      let y ← srcP sf p.from_
      pure (Ex.mkDp3 sf 0 true x (Ex.mkDp2 sf (if op == "REM" then 3 else 2) x y) y)
    | _ => do
      if p.from_.type == .CONST then throw s!"{op} by a constant"
      let x ← xP rn
      let y ← srcP sf p.from_
      pure (Ex.mkDp2 sf (if op == "ROR" then 11 else if op == "UDIV" then 2 else 3) x y)
  return (← wP {} p.to.reg r, .fall)

/-- `CSEL`/`CSINC`/`CSINV`/`CSNEG` (and `W`): the conditional select on the flags before the
Prog; `CSET`/`CSETM` as the assembler encodes them, `CSINC`/`CSINV` of `ZR` on the inverted
condition (not `AL`/`NV`, whose inversion is not their negation). -/
def cselP (op : String) (sf : Bool) (p : Prog) : Except String (Sym × PCtl) := do
  let c ← condOfSpecial p.from_
  let r ← match op with
    | "CSET" | "CSETM" =>
      if c.toNat ≥ 14 then throw s!"{op} on AL/NV" else
      pure (Ex.csel sf (op == "CSETM") (op == "CSET") (c ^^^ 1) (.k 0) (.k 0))
    | _ => do
      let n ← xP p.reg
      let m ← xP (← restP p 0).reg
      pure (Ex.csel sf (op == "CSINV" || op == "CSNEG") (op == "CSINC" || op == "CSNEG") c n m)
  return (← wP {} p.to.reg r, .fall)

/-- The acquire loads `LDAR*` and the release stores `STLR*`: whether a load, and the bytes. -/
def exclOp (name : String) : Option (Bool × Nat) :=
  match name with
  | "LDAR" => some (true, 8) | "LDARW" => some (true, 4) | "LDARH" => some (true, 2)
  | "LDARB" => some (true, 1) | "STLR" => some (false, 8) | "STLRW" => some (false, 4)
  | "STLRH" => some (false, 2) | "STLRB" => some (false, 1)
  | _ => none

/-- An acquire load or release store (`exclOp`): a plain access of `n` bytes at the operand's
address. -/
def exclP (az ez : Int) (ld : Bool) (n : Nat) (p : Prog) : Except String (Sym × PCtl) := do
  if ld then
    if p.from_.type != .MEM then throw "acquire load operand"
    let (a, _) ← memP az ez p.scond p.from_
    return (← wP { loads := [(a, n)] } p.to.reg (.ld n a), .fall)
  if p.to.type != .MEM then throw "release store operand"
  let (a, _) ← memP az ez p.scond p.to
  return (({} : Sym).store a n (← xP p.from_.reg), .fall)

/-- A vector register operand (`ProgCtx.v`): its number. -/
def vP (r : Int) : Except String Nat :=
  match fpIdx? r with
  | some i => pure i
  | none => throw s!"fp register {r}"

/-- A vector register write (`Eff.wV`). -/
def wVP (σ : Sym) (r : Int) (v : VEx) : Except String Sym :=
  match fpIdx? r with
  | some i => pure (σ.wV i v)
  | none => throw s!"destination fp register {r}"

/-- The write-back of a memory operand (`memP`), on the empty effect. -/
def wbP (wb : Option (Int × Ex)) : Except String Sym :=
  match wb with
  | some (r, b) => wP {} r b
  | none => pure {}

/-- The format of an `n`-byte SIMD&FP access or move: 0 single (4 bytes), 1 double. -/
def fpFt (n : Nat) : BitVec 2 := if n == 4 then 0 else 1

/-- `FMOVS`/`FMOVD`/`FMOVQ` (`movMem`'s SIMD&FP forms, `n` bytes): loads (all address forms,
with write-back), stores, `S`/`D` moves between vector registers and from or to a general
register, constants. A store's value is `vStoreEx` of the vector register (its `S`/`D` part,
`Ex.vlo`, or the whole `Q` register, `Ex.vq`), a move to a general register reads the `S`/`D`
part, a vector move is `FMOV`'s `fp1Op` of opcode 0. `Q` register moves are not modelled. -/
def fmovP (az ez : Int) (n : Nat) (p : Prog) : Except String (Sym × PCtl) := do
  match p.from_.type, p.to.type with
  | .MEM, .REG =>
    let (a, wb) ← memP az ez p.scond p.from_
    let σ ← wbP wb
    return (← wVP { σ with loads := (a, n) :: σ.loads } p.to.reg (.ld n a), .fall)
  | .REG, .MEM =>
    let (a, wb) ← memP az ez p.scond p.to
    let σ ← wbP wb
    return (σ.store a n (vStoreEx n (← vP p.from_.reg)), .fall)
  | .REG, .REG =>
    if n == 16 then throw "FMOVQ between registers"
    match fpIdx? p.from_.reg, fpIdx? p.to.reg with
    | some r, some _ => return (← wVP {} p.to.reg (.fp1 (fpFt n) 0 (.v r)), .fall)
    | some r, none => return (← wP {} p.to.reg (.vlo (fpFt n) r), .fall)
    | none, some _ => return (← wVP {} p.to.reg (VEx.mkOfX (8 * n) (← xP p.from_.reg)), .fall)
    | none, none => throw "FMOV between general registers"
  | .FCONST, .REG => return (← wVP {} p.to.reg (.k (← fconst (fpFt n) p.from_)), .fall)
  | t, u => throw s!"{p.as.name} operands {t.name},{u.name}"

/-- `FLDPS`/`FLDPD`/`FLDPQ`, `FSTPS`/`FSTPD`/`FSTPQ` (`pairOp`'s SIMD&FP forms, `n` bytes each):
two loads, or two stores of `vStoreEx` of the registers (`Ex.vlo`, `Ex.vq`). -/
def fpairP (az ez : Int) (ld : Bool) (n : Nat) (p : Prog) : Except String (Sym × PCtl) := do
  let (memA, regs) := if ld then (p.from_, p.to) else (p.to, p.from_)
  if regs.type != .REGREG then throw s!"pair operand {regs.type.name}"
  let (a, wb) ← memP az ez p.scond memA
  let σ ← wbP wb
  let a2 := Ex.mkAdd a (.k (BitVec.ofNat 64 n))
  if ld then
    let σ ← wVP { σ with loads := (a2, n) :: (a, n) :: σ.loads } regs.reg (.ld n a)
    return (← wVP σ regs.offset (.ld n a2), .fall)
  return ((σ.store a n (vStoreEx n (← vP regs.reg))).store a2 n (vStoreEx n (← vP regs.offset)),
    .fall)

/-- A SIMD&FP data-processing opcode `progEffect` models by name, with the fields of its
encoding: the format `ft` (0 single, 1 double), the opcode, a conversion's signedness `u` and
integer width `m`. -/
inductive FpOp where
  | fp1 (ft : BitVec 2) (opc : BitVec 6)
  | fp2 (ft : BitVec 2) (opc : BitVec 4)
  | fp3 (ft : BitVec 2) (o1 o0 : Bool)
  | cmp (ft : BitVec 2)
  | csel (ft : BitVec 2)
  | cvtz (ft : BitVec 2) (u : Bool) (m : Nat)
  | cvtf (ft : BitVec 2) (u : Bool) (m : Nat)

/-- The SIMD&FP data-processing opcodes, as `progEffect` reads their names (`fpType`, its opcode
tables, the `FCVTZ*`/`*CVTF*` name parsing). -/
def fpOp? (name : String) : Option FpOp :=
  match name with
  | "FMULD" => some (.fp2 1 0) | "FMULS" => some (.fp2 0 0)
  | "FDIVD" => some (.fp2 1 1) | "FDIVS" => some (.fp2 0 1)
  | "FADDD" => some (.fp2 1 2) | "FADDS" => some (.fp2 0 2)
  | "FSUBD" => some (.fp2 1 3) | "FSUBS" => some (.fp2 0 3)
  | "FMAXD" => some (.fp2 1 4) | "FMAXS" => some (.fp2 0 4)
  | "FMIND" => some (.fp2 1 5) | "FMINS" => some (.fp2 0 5)
  | "FNMULD" => some (.fp2 1 8) | "FNMULS" => some (.fp2 0 8)
  | "FMADDD" => some (.fp3 1 false false) | "FMADDS" => some (.fp3 0 false false)
  | "FMSUBD" => some (.fp3 1 false true) | "FMSUBS" => some (.fp3 0 false true)
  | "FNMADDD" => some (.fp3 1 true false) | "FNMADDS" => some (.fp3 0 true false)
  | "FNMSUBD" => some (.fp3 1 true true) | "FNMSUBS" => some (.fp3 0 true true)
  | "FABSD" => some (.fp1 1 1) | "FABSS" => some (.fp1 0 1)
  | "FNEGD" => some (.fp1 1 2) | "FNEGS" => some (.fp1 0 2)
  | "FSQRTD" => some (.fp1 1 3) | "FSQRTS" => some (.fp1 0 3)
  | "FRINTND" => some (.fp1 1 8) | "FRINTNS" => some (.fp1 0 8)
  | "FRINTPD" => some (.fp1 1 9) | "FRINTPS" => some (.fp1 0 9)
  | "FRINTMD" => some (.fp1 1 10) | "FRINTMS" => some (.fp1 0 10)
  | "FRINTZD" => some (.fp1 1 11) | "FRINTZS" => some (.fp1 0 11)
  | "FRINTAD" => some (.fp1 1 12) | "FRINTAS" => some (.fp1 0 12)
  | "FCVTSD" => some (.fp1 0 5) | "FCVTDS" => some (.fp1 1 4)
  | "FCMPD" => some (.cmp 1) | "FCMPS" => some (.cmp 0)
  | "FCMPED" => some (.cmp 1) | "FCMPES" => some (.cmp 0)
  | "FCSELD" => some (.csel 1) | "FCSELS" => some (.csel 0)
  | "FCVTZSD" => some (.cvtz 1 false 64) | "FCVTZSS" => some (.cvtz 0 false 64)
  | "FCVTZUD" => some (.cvtz 1 true 64) | "FCVTZUS" => some (.cvtz 0 true 64)
  | "FCVTZSDW" => some (.cvtz 1 false 32) | "FCVTZSSW" => some (.cvtz 0 false 32)
  | "FCVTZUDW" => some (.cvtz 1 true 32) | "FCVTZUSW" => some (.cvtz 0 true 32)
  | "SCVTFD" => some (.cvtf 1 false 64) | "SCVTFS" => some (.cvtf 0 false 64)
  | "UCVTFD" => some (.cvtf 1 true 64) | "UCVTFS" => some (.cvtf 0 true 64)
  | "SCVTFWD" => some (.cvtf 1 false 32) | "SCVTFWS" => some (.cvtf 0 false 32)
  | "UCVTFWD" => some (.cvtf 1 true 32) | "UCVTFWS" => some (.cvtf 0 true 32)
  | _ => none

/-- The SIMD&FP data processing (`fpOp?`) in `progEffect`'s operand conventions: arithmetic
(`fp1Op`, `fp2Op`, `fp3Op`), `FCMP` (the flags; `$(0.0)` compares with zero), `FCSEL` (on the
flags before the Prog), and the conversions to (`Ex.fcvtz`) and from (`VEx.cvtf`) a general
register. -/
def fpP (k : FpOp) (p : Prog) : Except String (Sym × PCtl) := do
  match k with
  | .fp1 ft opc => return (← wVP {} p.to.reg (.fp1 ft opc (.v (← vP p.from_.reg))), .fall)
  | .fp2 ft opc =>
    let a ← vP (if p.reg != 0 then p.reg else p.to.reg)
    let b ← vP p.from_.reg
    return (← wVP {} p.to.reg (.fp2 ft opc (.v a) (.v b)), .fall)
  | .fp3 ft o1 o0 =>
    let a ← vP p.reg
    let n ← vP (← restP p 0).reg
    let m ← vP p.from_.reg
    return (← wVP {} p.to.reg (.fp3 ft o1 o0 (.v a) (.v n) (.v m)), .fall)
  | .cmp ft =>
    let m : VEx ← if p.from_.type == .FCONST then pure (.k 0) else do pure (.v (← vP p.from_.reg))
    let n ← vP p.reg
    return ({ fl := .fcmp ft (.v n) m }, .fall)
  | .csel ft =>
    let cond ← condOfSpecial p.from_
    let n ← vP p.reg
    let m ← vP (← restP p 0).reg
    return (← wVP {} p.to.reg (.fcsel ft cond (.v n) (.v m)), .fall)
  | .cvtz ft u m => return (← wP {} p.to.reg (.fcvtz ft u m (← vP p.from_.reg)), .fall)
  | .cvtf ft u m => return (← wVP {} p.to.reg (.cvtf ft m u (← xP p.from_.reg)), .fall)

/-- The symbolic effect of a P0 Prog with code (`progEffect`) and its control, for the opcodes
the validator models (`progSym` adds the opcode check of the control). `az`, `ez`: the frame
(`Link.autosize`, `Link.extrasize`). -/
def progSymCore (az ez : Int) (p : Prog) : Except String (Sym × PCtl) := do
  let name := p.as.name
  let σ : Sym := {}
  let rn : Int := if p.reg != 0 then p.reg else p.to.reg
  -- shifts (`binOp` of `LSL`/`LSR`/`ASR`): by a constant the bitfield move, by a register the
  -- variable shift
  if let some (op, sf) := baseOf name ["LSL", "LSR", "ASR"] then
    if p.from_.type == .CONST then
      if p.from_.offset < 0 then throw s!"{name} by a negative amount"
      let x ← xP rn
      return (← wP σ p.to.reg (← shiftBfm op sf p.from_.offset.toNat x), .fall)
    let x ← xP rn
    let y ← srcP sf p.from_
    let opc : BitVec 6 := if op == "LSL" then 8 else if op == "LSR" then 9 else 10
    return (← wP σ p.to.reg (Ex.mkDp2 sf opc x y), .fall)
  if let some (op, sf) := baseOf name ["ADD", "SUB", "AND", "ORR", "EOR", "ADDS", "SUBS", "ANDS"] then
    let x ← xP rn
    let y ← srcP sf p.from_
    let (r, f) : Ex × Option Fl := match op with
      | "ADD" => (Ex.mkAddSub sf false x y, none)
      | "SUB" => (Ex.mkAddSub sf true x y, none)
      | "ADDS" => (Ex.mkAddSub sf false x y, some (Fl.mkAddSub sf false x y))
      | "SUBS" => (Ex.mkAddSub sf true x y, some (Fl.mkAddSub sf true x y))
      | "AND" => (Ex.mkLogical sf 0 x y, none)
      | "ORR" => (Ex.mkLogical sf 1 x y, none)
      | "EOR" => (Ex.mkLogical sf 2 x y, none)
      | _ => (Ex.mkLogical sf 3 x y, some (Fl.mkAnds sf x y))
    let σ ← wP σ p.to.reg r
    return ({ σ with fl := f.getD σ.fl }, .fall)
  if let some (op, sf) := baseOf name ["CMP", "CMN", "TST"] then
    let x ← xP p.reg
    let y ← srcP sf p.from_
    let f := match op with
      | "CMP" => Fl.mkAddSub sf true x y
      | "CMN" => Fl.mkAddSub sf false x y
      | _ => Fl.mkAnds sf x y
    return ({ σ with fl := f }, .fall)
  if let some (_, sf) := baseOf name ["NEG"] then
    let y ← srcP sf p.from_
    return (← wP σ p.to.reg (Ex.mkAddSub sf true (.k 0) y), .fall)
  if let some (op, sf) := baseOf name ["UBFX", "SBFX", "UBFIZ"] then
    let lsb := p.from_.offset.toNat
    let width := (← match p.rest[0]? with
      | some (_, a) => pure a
      | none => throw "missing RestArgs operand").offset.toNat
    let w := if sf then 64 else 32
    if width = 0 || lsb + width > w then throw s!"{op} bounds"
    let x ← xP p.reg
    let r := match op with
      | "UBFX" => Ex.mkBfm sf 2 (BitVec.ofNat 6 lsb) (BitVec.ofNat 6 (lsb + width - 1)) (.k 0) x
      | "SBFX" => Ex.mkBfm sf 0 (BitVec.ofNat 6 lsb) (BitVec.ofNat 6 (lsb + width - 1)) (.k 0) x
      | _ => Ex.mkBfm sf 2 (BitVec.ofNat 6 ((w - lsb) % w)) (BitVec.ofNat 6 (width - 1)) (.k 0) x
    return (← wP σ p.to.reg r, .fall)
  if let some (n, signed, fp) := movMem name then
    if fp then return ← fmovP az ez n p
    match p.from_.type, p.to.type with
    | .MEM, .REG =>
      let (a, wb) ← memP az ez p.scond p.from_
      let σ ← match wb with
        | some (r, b) => wP σ r b
        | none => pure σ
      let σ := { σ with loads := (a, n) :: σ.loads }
      let raw : Ex := .ld n a
      return (← wP σ p.to.reg (if signed then Ex.mkSext (8 * n) raw else raw), .fall)
    | .REG, .MEM =>
      let (a, wb) ← memP az ez p.scond p.to
      let σ ← match wb with
        | some (r, b) => wP σ r b
        | none => pure σ
      return (σ.store a n (← xP p.from_.reg), .fall)
    | .REG, .REG =>
      let x ← xP p.from_.reg
      -- the forms `MOV*reg` is encoded as: `ORR` (`MOVD`, `MOVWU`) or a bitfield move
      let r := match n, signed with
        | 8, _ => x
        | 4, false => Ex.mkTrunc false x
        | n, true => Ex.mkBfm true 0 0 (BitVec.ofNat 6 (8 * n - 1)) (.k 0) x
        | n, false => Ex.mkBfm true 2 0 (BitVec.ofNat 6 (8 * n - 1)) (.k 0) x
      return (← wP σ p.to.reg r, .fall)
    | .CONST, .REG =>
      let k := BitVec.ofInt 64 p.from_.offset
      return (← wP σ p.to.reg (.k (maskN n k)), .fall)
    | .ADDR, .REG =>
      let (a, _) ← memP az ez p.scond p.from_
      return (← wP σ p.to.reg a, .fall)
    | t, u => throw s!"{name} operands {t.name},{u.name}"
  if let some (ld, n, signed, fp) := pairOp name then
    if fp then return ← fpairP az ez ld n p
    let (memA, regs) := if ld then (p.from_, p.to) else (p.to, p.from_)
    if regs.type != .REGREG then throw s!"pair operand {regs.type.name}"
    let (a, wb) ← memP az ez p.scond memA
    let σ ← match wb with
      | some (r, b) => wP σ r b
      | none => pure σ
    let a2 := Ex.mkAdd a (.k (BitVec.ofNat 64 n))
    if ld then
      let σ := { σ with loads := (a2, n) :: (a, n) :: σ.loads }
      let ext (v : Ex) : Ex := if signed then Ex.mkSext (8 * n) v else v
      let σ ← wP σ regs.reg (ext (.ld n a))
      return (← wP σ regs.offset (ext (.ld n a2)), .fall)
    return ((σ.store a n (← xP regs.reg)).store a2 n (← xP regs.offset), .fall)
  if let some c := bcond name then
    return (σ, .cond (BitVec.ofNat 4 c) (← targetP p.to))
  if let some (op, sf) := baseOf name ["MUL", "MNEG", "MADD", "MSUB", "UMULH", "SMULH"] then
    return ← mulP op sf p
  if let some (op, sf) := baseOf name ["CLZ", "RBIT", "REV", "REV16", "REV32"] then
    return ← dp1P op sf p
  if let some (op, sf) := baseOf name ["CSEL", "CSINC", "CSINV", "CSNEG", "CSET", "CSETM"] then
    return ← cselP op sf p
  if let some (ld, n) := exclOp name then
    return ← exclP az ez ld n p
  if let some (op, sf) := baseOf name ["ROR", "UDIV", "SDIV", "REM", "UREM", "BIC", "ORN", "EON",
      "MVN"] then
    return ← dp2P op sf p
  match name with
  | "HINT" => if p.from_.offset == 0 then return (σ, .fall) else throw "HINT"
  -- no effect on one core (`progEffect`'s `DMB`/`PRFM` arm): `DMB $k` and `PRFM 0(Rn), $k`
  | "DMB" => if p.from_.type == .CONST && p.to.type == .NONE then return (σ, .fall) else throw "DMB"
  | "PRFM" =>
    if p.from_.type == .MEM && p.from_.name == .NONE && p.from_.offset == 0 &&
        p.from_.index == 0 && p.to.type == .CONST then return (σ, .fall)
    else throw "PRFM"
  | "JMP" =>
    if p.to.type == .BRANCH then return (σ, .jmp (← targetP p.to))
    throw "JMP to a register"
  | "CBZ" | "CBNZ" | "CBZW" | "CBNZW" =>
    return (σ, .cbz (!endsS name "W") (!startsS name "CBZ") (← xP p.from_.reg) (← targetP p.to))
  | "TBZ" | "TBNZ" =>
    if p.from_.offset < 0 || p.from_.offset ≥ 64 then throw "TBZ bit"
    return (σ, .tbz (name == "TBNZ") p.from_.offset.toNat (← xP p.reg) (← targetP p.to))
  | "CALL" =>
    if p.to.type == .MEM && (p.to.name == .EXTERN || p.to.name == .STATIC) then
      match p.to.sym with
      | some n => return (σ, .call n p.to.offset)
      | none => throw "symbol-less call target"
    if p.to.type == .BRANCH then
      match p.to.val, p.to.sym with
      | .target _, _ => throw "call to a Prog"
      | _, some n => return (σ, .call n p.to.offset)
      | _, none => throw "call to a Prog"
    return (σ, .callReg (← xP p.to.reg))
  | "RET" =>
    let r := if p.to.type == .NONE then REG_R0 + 30 else p.to.reg
    return (σ, .reg (← xP r))
  | _ =>
    match fpOp? name with
    | some k => fpP k p
    | none => throw s!"opcode not modelled: {name}"

/-- Calls come from `CALL`, register jumps from `RET`. -/
def ctlOp (p : Prog) : PCtl → Except String Unit
  | .call .. | .callReg _ => if p.as == .CALL then pure () else throw "call control"
  | .reg _ => if p.as == .RET then pure () else throw "register jump control"
  | _ => pure ()

/-- `progSymCore`, its control checked against the opcode (`ctlOp`). -/
def progSym (az ez : Int) (p : Prog) : Except String (Sym × PCtl) :=
  match progSymCore az ez p with
  | .ok (σ, c) => match ctlOp p c with
    | .ok () => .ok (σ, c)
    | .error e => .error e
  | .error e => .error e

/-! ## The machine side -/

/-- The little-endian word at offset `o` of the text. -/
def wordAt (t : ByteArray) (o : Nat) : BitVec 32 :=
  BitVec.ofNat 32 ((t.get! o).toNat + (t.get! (o + 1)).toNat * 256 +
    (t.get! (o + 2)).toNat * 65536 + (t.get! (o + 3)).toNat * 16777216)

/-- `R_CALLARM64`, or the weak form `weakenGlobalMapInitRelocs` gives it. -/
def isCallReloc (ty : String) : Bool := ty == "R_CALLARM64" || ty == "RelocType(-32759)"

/-- The relocations that patch the word at offset `o`: a call's at `o`, a two-word relocation's
at `o` or `o − 4` (marker relocations of size 0 patch nothing). -/
def covering (rs : List Reloc) (o : Nat) : List Reloc :=
  rs.filter fun r => r.siz != 0 && (r.off == (o : Int) || (!isCallReloc r.type && r.off + 4 == (o : Int)))

/-- The relocation starting at offset `o`, if it is the only one patching its words. -/
def relocAt (rs : List Reloc) (o : Nat) : Option Reloc :=
  match covering rs o with
  | [r] => if r.off == (o : Int) then some r else none
  | _ => none

/-- `R_ARM64_PCREL_LDST<8|16|32|64>`: the access's `log2` size. -/
def ldstScale (ty : String) : Option Nat :=
  match ty with
  | "R_ARM64_PCREL_LDST8" => some 0 | "R_ARM64_PCREL_LDST16" => some 1
  | "R_ARM64_PCREL_LDST32" => some 2 | "R_ARM64_PCREL_LDST64" => some 3
  | _ => none

/-- A `B`/`BL` with a zero offset field (an `R_CALLARM64` target): whether it links. -/
def callLink? : Insn → Option Bool
  | .b link imm26 => if imm26 = 0 then some link else none
  | _ => none

/-- An `ADRP` with a zero offset field to a register: the register. -/
def adrpRd? : Insn → Option Reg
  | .adr page imm rd => if page ∧ imm = 0 ∧ rd ≠ 31 then some rd else none
  | _ => none

/-- `ADD rd2, rd, #0` (64-bit, no flags, unshifted): `rd2`. -/
def addLo? (rd : Reg) : Insn → Option Reg
  | .addSubImm sf sub setf sh imm12 rn rd2 =>
    if sf ∧ !sub ∧ !setf ∧ !sh ∧ imm12 = 0 ∧ rn = rd then some rd2 else none
  | _ => none

/-- A load/store `[rd, #0]` of `2^sc` bytes, integer or (`vec`) SIMD&FP `B`/`H`/`S`/`D` (no `Q`:
`opc` below 2): its `size`, `vec`, `opc` and `rt`. -/
def ldstLo? (rd : Reg) (sc : Nat) : Insn → Option (BitVec 2 × Bool × BitVec 2 × Reg)
  | .ldst size vec opc (.uimm imm12) rn rt =>
    if (!vec || decide (opc.toNat < 2)) ∧ imm12 = 0 ∧ rn = rd ∧ size.toNat = sc then
      some (size, vec, opc, rt)
    else none
  | _ => none

/-- The target of a relocation `r` against symbol `y`: `y + r.add`. -/
def relTgt (y : Nat) (r : Reloc) : Ex := Ex.mkAdd (.sym y) (.k (BitVec.ofInt 64 r.add))

/-! `symUnit` is split into small definitions without early returns, `let`s or `do` join points
(`symLdst`, `symPair2`, `symPairAt`, `symPair`, `symUnitRel`), so that the proofs about it
(`symUnit_inv`) reduce one small match at a time. -/

/-- The access of a relocated load/store at `a`: SIMD&FP (`symVAccess`) or integer (`symAccess`). -/
def symLdstAcc (σ : Sym) (vec : Bool) (size opc : BitVec 2) (rt : Nat) (a : Ex) :
    Except String Sym :=
  if vec then symVAccess σ size opc rt a else symAccess σ size opc rt a

/-- The access of an `R_ARM64_PCREL_LDST*` pair (`ADRP rd` then `i2`). -/
def symLdst (σ : Sym) (y : Nat) (r : Reloc) (rd : Reg) (i2 : Insn) :
    Except String (Sym × MCtl × Nat) :=
  match ldstScale r.type with
  | none => throw s!"relocation {r.type}"
  | some sc =>
    match ldstLo? rd sc i2 with
    | none => throw "PCREL_LDST: access"
    | some (size, vec, opc, rt) => do
      let σ2 ← symLdstAcc (σ.wX rd.toNat (.page (relTgt y r))) vec size opc rt.toNat (relTgt y r)
      pure (σ2, .fall, 2)

/-- The second word `i2` of a relocated pair (`ADRP rd` first). -/
def symPair2 (σ : Sym) (y : Nat) (r : Reloc) (rd : Reg) (i2 : Insn) :
    Except String (Sym × MCtl × Nat) :=
  if r.type == "R_ADDRARM64" then
    match addLo? rd i2 with
    | none => throw "R_ADDRARM64: not ADRP + ADD"
    | some rd2 => pure ((σ.wX rd.toNat (.page (relTgt y r))).wXsp rd2.toNat (relTgt y r), .fall, 2)
  else symLdst σ y r rd i2

/-- The second word `d` (decoded) of a relocated pair (`ADRP rd` first). The decoding is an
argument, not a `match` scrutinee, so that unfolding this does not expose `decode` to the
kernel. -/
def symPairAt (d : Option Insn) (σ : Sym) (y : Nat) (r : Reloc) (rd : Reg) :
    Except String (Sym × MCtl × Nat) :=
  match d with
  | none => throw "undecodable word"
  | some i2 => symPair2 σ y r rd i2

/-- A relocated pair at `o` (relocation `r` against `y`, first word `i`). -/
def symPair (t : ByteArray) (rs : List Reloc) (n o : Nat) (σ : Sym) (y : Nat) (r : Reloc)
    (i : Insn) : Except String (Sym × MCtl × Nat) :=
  if n = 0 || o + 8 > t.size then throw "relocated pair cut"
  else if covering rs (o + 4) != [r] then throw s!"word at {o + 4} patched by several relocations"
  else
    match adrpRd? i with
    | none => throw s!"relocation {r.type} not on ADRP"
    | some rd => symPairAt (decode (wordAt t (o + 4))) σ y r rd

/-- `symUnit` at a relocated word `i` (relocation `r`): a `BL`/`B` of `R_CALLARM64`, or the
relocated pair. -/
def symUnitRel (t : ByteArray) (rs : List Reloc) (n o : Nat) (σ : Sym) (i : Insn) (r : Reloc) :
    Except String (Sym × MCtl × Nat) :=
  match r.sym with
  | none => throw "relocation without symbol"
  | some y =>
    if isCallReloc r.type then
      match callLink? i with
      | none => throw "R_CALLARM64 not on a B or BL with a zero offset"
      | some link => pure (σ, if link then .call y r.add else .jmpSym y r.add, 1)
    else symPair t rs n o σ y r i

/-- The first unit of the words `[o, o + 4 (n + 1))` executed symbolically from `σ`: one word,
or the two words of a relocated pair (`R_ADDRARM64`: `ADRP` + `ADD`, the target in the `ADD`'s
destination, its page in the `ADRP`'s; `R_ARM64_PCREL_LDST*`: `ADRP` + load/store, the access
at the target), or a `BL`/`B` of `R_CALLARM64`, as linked (`symUnitRel`); the relocated fields
must be zero. The effect, the control and the number of words. -/
def symUnit (t : ByteArray) (rs : List Reloc) (n o : Nat) (σ : Sym) :
    Except String (Sym × MCtl × Nat) :=
  if o + 4 > t.size || o % 4 != 0 then throw s!"word at {o} past the text or unaligned"
  else
    let w := wordAt t o
    match decode w with
    | none => throw s!"undecodable word {w.toHex} at {o}"
    | some i =>
      match relocAt rs o with
      | none =>
        if !(covering rs o).isEmpty then throw s!"word at {o} patched by several relocations"
        else do
          let (σ, c) ← symInsn i o σ
          pure (σ, c, 1)
      | some r => symUnitRel t rs n o σ i r

/-- The words `[o, o + 4 n)` executed symbolically from `σ`, unit by unit (`symUnit`), every
unit but the last falling through. -/
def symWords (t : ByteArray) (rs : List Reloc) : Nat → Nat → Sym → Except String (Sym × MCtl)
  | 0, _, σ => pure (σ, .fall)
  | n + 1, o, σ => do
    let (σ, c, used) ← symUnit t rs n o σ
    if used = 2 then
      match n with
      | 0 => throw "relocated pair cut"
      | m + 1 =>
        if m = 0 then pure (σ, c)
        else if c != .fall then throw s!"branch before the last word at {o}"
        else symWords t rs m (o + 8) σ
    else if n = 0 then pure (σ, c)
    else if c != .fall then throw s!"branch before the last word at {o}"
    else symWords t rs n (o + 4) σ

/-! ## Comparing -/

/-- The registers compared: all general registers but `X27` (REGTMP) and `X30`. -/
def cmpRegs : List Nat := (List.range 31).filter fun r => r != 27 && r != 30

/-- Whether a value of a P0 effect reads `X27`, `X30` or no general register (`Ex.regsOK`,
`VEx.regsOK`). -/
def Sym.readsTmp (σ : Sym) : Bool :=
  let rd (e : Ex) := !e.regsOK
  σ.x.any (rd ·.2) || rd σ.sp || !σ.fl.regsOK ||
    σ.loads.any (rd ·.1) || (σ.stores.any fun (a, _, v) => rd a || rd v) ||
    σ.v.any (!·.2.regsOK)

/-- The machine effect `m` matches the Prog effect `p` (the module doc). -/
def sameEffect (m p : Sym) : Except String Unit := do
  if let some r := cmpRegs.find? (fun r => m.getX r != p.getX r) then
    throw s!"R{r}: machine {(m.getX r).str}, Prog {(p.getX r).str}"
  if let some r := (List.range 32).find? (fun r => m.getV r != p.getV r) then
    throw s!"V{r}: machine {(m.getV r).str}, Prog {(p.getV r).str}"
  if m.getX 30 != .x 30 || p.getX 30 != .x 30 then throw "R30 written"
  if m.sp != p.sp then throw "SP"
  if m.fl != p.fl then throw s!"flags: machine {repr m.fl}, Prog {repr p.fl}"
  if m.stores != p.stores then
    let f (l : List (Ex × Nat × Ex)) := l.map fun (a, n, v) => s!"[{a.str}]{n}={v.str}"
    throw s!"stores: machine {f m.stores}, Prog {f p.stores}"
  unless m.loads.all (p.loads.contains ·) do throw "a machine load the Prog does not perform"
  unless p.loads.all (m.loads.contains ·) do throw "a Prog load the machine does not perform"
  if p.readsTmp then throw "the Prog reads R27 or R30"

/-- The offset of a P0 Prog, by ID (`Tab.offs` aligned with the list). -/
def offOf (ids : List (Nat × Nat)) (id : Nat) : Option Nat := ids.lookup id

/-- The machine control `m` matches the Prog control `p` (branch offsets through `offs`). -/
def sameCtl (offs : List (Nat × Nat)) (m : MCtl) (p : PCtl) (_pr : Sym) : Except String Unit := do
  let tgt (id : Nat) (q : Int) : Except String Unit :=
    match offOf offs id with
    | some o => if (o : Int) == q then pure () else throw s!"branch to {q}, target Prog at {o}"
    | none => throw "branch target not a P0 Prog"
  let ctlReads (e : Ex) : Bool := !e.regsOK
  match m, p with
  | .fall, .fall => pure ()
  | .jmp q, .jmp id => tgt id q
  | .cond fl c q, .cond c' id =>
    if fl != .init then throw "condition on flags set by the words" else
    if c != c' then throw "condition" else tgt id q
  | .cbz sf nz a q, .cbz sf' nz' a' id =>
    if sf != sf' || nz != nz' || a != a' || ctlReads a' then throw "CBZ" else tgt id q
  | .tbz nz b a q, .tbz nz' b' a' id =>
    if nz != nz' || b != b' || a != a' || ctlReads a' then throw "TBZ" else tgt id q
  | .call n add, .call n' add' =>
    if n != n' || add != add' || add != 0 then throw "call target" else pure ()
  | .callReg a, .callReg a' => if a != a' || ctlReads a' then throw "call register" else pure ()
  | _, _ => throw s!"control: machine {repr m}, Prog {repr p}"

/-- One P0 Prog against its words `[o, e)`. -/
def checkProg (t : ByteArray) (rs : List Reloc) (offs : List (Nat × Nat)) (az ez : Int)
    (p : Prog) (o e : Nat) : Except String Unit := do
  if p.isSkip || p.as == .END then
    if o != e then throw s!"{p.as.name} owns words" else return
  if e ≤ o || (e - o) % 4 != 0 then throw s!"{p.as.name}: no words"
  let (pσ, pc) ← progSym az ez p
  let (mσ, mc) ← symWords t rs ((e - o) / 4) o {}
  sameEffect mσ pσ
  sameCtl offs mc pc pσ

/-! ## Prologue, epilogue, morestack tail -/

/-- The frame's specification after the prologue: `SP` lowered by `autosize`, the caller's `LR`
at `0(SP)` and `FP` at `-8(SP)`, `R29 = SP - 8`, no loads. The large-frame form also writes
`R20`. -/
def frameOK (az : Int) (σ : Sym) : Except String Unit := do
  let sp' := Ex.mkAdd .sp (.k (BitVec.ofInt 64 (-az)))
  let fp' := Ex.mkAdd .sp (.k (BitVec.ofInt 64 (-az - 8)))
  if σ.sp != sp' then throw "prologue: SP"
  if σ.getX 29 != fp' then throw "prologue: R29"
  if let some r := cmpRegs.find? (fun r => r != 29 && r != 20 && σ.getX r != .x r) then
    throw s!"prologue: R{r} written"
  if σ.getX 30 != .x 30 then throw "prologue: R30 written"
  let st := [(sp', 8, Ex.x 30), (fp', 8, Ex.x 29)]
  if σ.stores != st && σ.stores != st.reverse then throw "prologue: stores"
  if !σ.loads.isEmpty then throw "prologue: loads"
  if !σ.v.isEmpty then throw "prologue: V registers"

/-- The epilogue's specification: `R29` restored (a leaf recomputes it, `SP + autosize - 8`,
others reload it from `-8(SP)`), `R30` reloaded from `0(SP)` unless a leaf, `SP` raised by
`autosize`, no load but these reloads, a return through `R30`. -/
def retOK (az : Int) (leaf : Bool) (σ : Sym) (c back : MCtl) : Except String Unit := do
  if az == 0 then
    if σ != {} then throw "frameless epilogue: effect" else
    if c != back then throw "frameless epilogue: return" else return
  if σ.sp != Ex.mkAdd .sp (.k (BitVec.ofInt 64 az)) then throw "epilogue: SP"
  let fp := if leaf then Ex.mkAdd .sp (.k (BitVec.ofInt 64 (az - 8)))
    else .ld 8 (Ex.mkAdd .sp (.k (BitVec.ofInt 64 (-8))))
  let lr := if leaf then Ex.x 30 else .ld 8 .sp
  if σ.getX 29 != fp then throw "epilogue: R29"
  if σ.getX 30 != lr then throw "epilogue: R30"
  if let some r := cmpRegs.find? (fun r => r != 29 && σ.getX r != .x r) then
    throw s!"epilogue: R{r} written"
  if σ.fl != .init then throw "epilogue: flags"
  if !σ.stores.isEmpty then throw "epilogue: stores"
  if !σ.v.isEmpty then throw "epilogue: V registers"
  let reloads := [(Ex.mkAdd .sp (.k (BitVec.ofInt 64 (-8))), 8), (Ex.sp, 8)]
  unless σ.loads.all (reloads.contains ·) do throw "epilogue: loads"
  if c != back then throw "epilogue: return"

/-- The stack check: `[0, e)` ends in the `BLS` to the morestack tail (and, for big frames, a
`BLO` there before it); returns the tail's offset and the check's specification is met:
the limit `SP` (small frames) or `SP - (framesize - StackSmall)` compared unsigned with
`stackguard0` (`16(g)`), loaded by the only load; `SP` and `R30` unchanged. -/
def checkStackCheck (t : ByteArray) (rs : List Reloc) (az : Int) (o : Nat) (gOff : Nat) :
    Except String (Nat × Nat) := do
  let g : Ex := .ld 8 (Ex.mkAdd (.x 28) (.k (BitVec.ofNat 64 gOff)))
  let lim := if az ≤ 128 then Ex.sp else Ex.mkAdd .sp (.k (BitVec.ofInt 64 (-(az - 128))))
  -- small and medium frames: LDR, (SUB), CMP, BLS
  let n := if az ≤ 128 then 3 else 4
  if az > 4096 then throw "stack check of a huge frame"
  let (σ, c) ← symWords t rs n o {}
  match c with
  | .cond fl 9 q =>
    if fl != .addSub true true lim g then throw s!"stack check: flags {repr fl}" else
    if σ.stores != [] then throw "stack check: stores" else
    if !σ.v.isEmpty then throw "stack check: V registers" else
    if σ.sp != .sp then throw "stack check: SP" else
    if σ.getX 30 != .x 30 then throw "stack check: R30" else
    if σ.loads != [(Ex.mkAdd (.x 28) (.k (BitVec.ofNat 64 gOff)), 8)] then
      throw "stack check: loads" else
    if let some r := cmpRegs.find? (fun r => r != 16 && r != 17 && σ.getX r != .x r) then
      throw s!"stack check: R{r}"
    if q < 0 then throw "stack check: tail" else
    pure (o + 4 * n, q.toNat)
  | _ => throw "stack check: not a BLS"

/-- The number of words of the unit at `o` (`symUnit`): two for a relocated pair. -/
def unitLen (rs : List Reloc) (o : Nat) : Nat :=
  match relocAt rs o with
  | some r => if isCallReloc r.type then 1 else 2
  | none => 1

/-- The words `[o, e)` up to and including the first one whose control is not a fall-through
(searching at most `fuel` words): its offset after, the effect and the control. -/
def symUntil (t : ByteArray) (rs : List Reloc) : Nat → Nat → Sym → Except String (Nat × Sym × MCtl)
  | 0, _, _ => throw "no branch"
  | fuel + 1, o, σ => do
    let used := unitLen rs o
    let (σ', c) ← symWords t rs used o σ
    if c == .fall then symUntil t rs fuel (o + 4 * used) σ' else pure (o + 4 * used, σ', c)

/-- One register-argument spill of the morestack tail (`tailPlan`): general register `reg` (or
vector register `V reg` if `fp`: an `F` register's `S`/`D` part) stored in its `n` low bytes at
`off(SP)` (`SP` at the entry: the frame is not yet allocated), reloaded sign-extended if `sg` (a
vector register zero-extended to 128 bits). -/
structure TailSlot where
  reg : Nat
  n : Nat
  off : Nat
  sg : Bool
  fp : Bool
  deriving DecidableEq, Repr, Inhabited

/-- The slot's address, `off(SP)`. -/
def TailSlot.addr (s : TailSlot) : Ex := Ex.mkAdd .sp (.k (BitVec.ofNat 64 s.off))

/-- The slot's spill: the general register, or the `S`/`D` part of the vector register
(`vStoreEx`). -/
def TailSlot.store (s : TailSlot) : Ex × Nat × Ex :=
  (s.addr, s.n, if s.fp then vStoreEx s.n s.reg else .x s.reg)

/-- The slot's reload into a general register. -/
def TailSlot.reload (s : TailSlot) : Ex :=
  if s.sg then Ex.mkSext (8 * s.n) (.ld s.n s.addr) else .ld s.n s.addr

/-- The slot's reload into a vector register (`LDR S`/`D`: zero-extended). -/
def TailSlot.vreload (s : TailSlot) : VEx := .ld s.n s.addr

/-- The slot register `r` is reloaded from: its last spill (of a vector register if `fp`, else
of a general one). -/
def reloadOf (sl : List TailSlot) (fp : Bool) (r : Nat) : Option TailSlot :=
  sl.reverse.find? fun s => s.fp == fp && s.reg == r

/-- Whether the slots' byte ranges are pairwise disjoint. -/
def slotsApart : List TailSlot → Bool
  | [] => true
  | s :: ss => ss.all (fun s' => s.off + s.n ≤ s'.off || s'.off + s'.n ≤ s.off) && slotsApart ss

/-- The slots of one spill: a register (`MOVx`, `FMOVS`/`FMOVD`) or a pair (`STP`/`STPW`,
`FSTPS`/`FSTPD`) at `off(RSP)`, the frame not yet allocated. -/
def spillSlots (sp : Spill) : Except String (List TailSlot) := do
  let a := sp.addr
  let named := match a.name with
    | .NONE => true
    | _ => false
  if a.type != .MEM || !named || a.reg != REG_RSP || a.index != 0 || a.offset < 0 then
    throw "tail: spill address"
  let off := a.offset.toNat
  let regIdx := fun (fp : Bool) (r : Int) => if fp then fpIdx? r else gpIdx? r
  match movMem sp.spill.name, pairOp sp.spill.name with
  | some (n, _, fp), _ =>
    let some r := regIdx fp sp.reg | throw "tail: spill register"
    let some (n', sg, fp') := movMem sp.unspill.name | throw s!"tail: unspill {sp.unspill.name}"
    if n' != n || fp' != fp then throw "tail: unspill size"
    pure [⟨r, n, off, sg && !fp, fp⟩]
  | _, some (false, n, false, fp) =>
    let some r := regIdx fp sp.reg | throw "tail: spill register"
    let some r2 := regIdx fp sp.reg2 | throw "tail: spill register"
    pure [⟨r, n, off, false, fp⟩, ⟨r2, n, off + n, false, fp⟩]
  | _, _ => throw s!"tail: spill {sp.spill.name}"

/-- The slots of the spills, in order. -/
def tailSlots : List Spill → Except String (List TailSlot)
  | [] => pure []
  | sp :: rest => do
    let here ← spillSlots sp
    let more ← tailSlots rest
    pure (here ++ more)

/-- The morestack tail's spills (`FuncInfo.spills`) as slots, in order: argument registers
`R0`–`R15` (`1`–`8` bytes each) and `F0`–`F15` (`4` or `8` bytes), disjoint byte ranges. -/
def tailPlan (spills : List Spill) : Except String (List TailSlot) := do
  let sl ← tailSlots spills
  if sl.any (·.reg ≥ 16) then throw "tail: spill register"
  if sl.any (fun s => s.n == 0 || s.n > 8 || (s.fp && s.n != 4 && s.n != 8)) then
    throw "tail: spill size"
  if !slotsApart sl then throw "tail: spill slots overlap"
  pure sl

/-- The call of the morestack tail at `o` (`checkTail`): its symbol and addend. -/
def tailCall (t : ByteArray) (rs : List Reloc) (o : Nat) : Option (Nat × Int) :=
  match symUntil t rs ((t.size - o) / 4) o {} with
  | .ok (_, _, .call n add) => some (n, add)
  | _ => none

/-- The morestack tail at `o` (`stacksplit`): the spills of `FuncInfo.spills` at their entry
addresses (`tailPlan`), `MOVD R30, R3`, the call, the reloads and the jump back to the stack
check at `check`. Before the call `SP` is kept and nothing is loaded; after it `SP` and `R30`
are kept, nothing is stored, the only loads are of the slots, each general register is its
reload (or kept) and each reloaded vector register is its reload (the others are unconstrained:
the hook clobbers them). Returns the tail's end. -/
def checkTail (t : ByteArray) (rs : List Reloc) (spills : List Spill) (check o : Nat) :
    Except String Nat := do
  let sl ← tailPlan spills
  let budget := (t.size - o) / 4
  let (o1, σ1, c1) ← symUntil t rs budget o {}
  match c1 with
  | .call _ _ => pure ()
  | _ => throw "tail: no call"
  if σ1.stores != sl.map TailSlot.store then throw "tail: spills"
  if σ1.sp != .sp then throw "tail: SP before the call"
  if !σ1.loads.isEmpty then throw "tail: loads before the call"
  if let some r := cmpRegs.find? (fun r => σ1.getX r != if r == 3 then Ex.x 30 else Ex.x r) then
    throw s!"tail: R{r} before the call"
  let (o2, σ2, c2) ← symUntil t rs budget o1 {}
  if c2 != .jmp check then throw "tail: not a jump back to the stack check"
  if !σ2.stores.isEmpty then throw "tail: stores after the call"
  if σ2.sp != .sp then throw "tail: SP after the call"
  if σ2.getX 30 != .x 30 then throw "tail: R30 after the call"
  unless σ2.loads.all (fun x => sl.any fun s => s.addr == x.1 && s.n == x.2) do
    throw "tail: loads after the call"
  let want := fun r => ((reloadOf sl false r).map TailSlot.reload).getD (Ex.x r)
  if let some r := cmpRegs.find? (fun r => σ2.getX r != want r) then
    throw s!"tail: R{r} after the call: {(σ2.getX r).str}, want {(want r).str}"
  if let some r := (List.range 16).find? (fun r =>
      match reloadOf sl true r with
      | some q => σ2.getV r != q.vreload
      | none => false) then
    throw s!"tail: F{r} after the call: {(σ2.getV r).str}"
  pure o2

/-- The prologue `[0, body)` of a function with frame size `az`: nothing if frameless, else the
stack check (when the first word loads `stackguard0`, or `stackguard1` in a C function) and the
frame (`frameOK`). Returns the stack check's end and the morestack tail's offset. -/
def checkPrologue (t : ByteArray) (rs : List Reloc) (az : Int) (body : Nat) :
    Except String (Option (Nat × Nat × Nat)) := do
  if az == 0 then
    if body != 0 then throw "frameless function with a prologue"
    return none
  -- `MOVD 16(g), R16` (`24(g)` in a C function's prologue, `stackguard1`)
  let gOff? : Option Nat := match decode (wordAt t 0) with
    | some (.ldst 3 false 1 (.uimm 2) 28 16) => some 16
    | some (.ldst 3 false 1 (.uimm 3) 28 16) => some 24
    | _ => none
  let check ← match (if body ≥ 12 then gOff? else none) with
    | some gOff => do
      let (ce, tail) ← checkStackCheck t rs az 0 gOff
      pure (some (ce, tail, gOff))
    | none => pure none
  let fo := match check with
    | some (ce, _, _) => ce
    | none => 0
  if body ≤ fo || (body - fo) % 4 != 0 then throw "prologue: no frame words"
  let (σ, c) ← symWords t rs ((body - fo) / 4) fo {}
  if c != .fall then throw "prologue: branch"
  frameOK az σ
  return check

/-- One body Prog `p` against its words `[s, e)`: a P0 `RET` (without operand, or of a symbol)
against the epilogue (`retOK`), any other Prog by `checkProg`. -/
def checkOne (t : ByteArray) (rs : List Reloc) (offs : List (Nat × Nat)) (az ez : Int)
    (leaf : Bool) (p : Prog) (s e : Nat) : Except String Unit :=
  if p.as == .RET && (p.to.type == .NONE || p.to.sym.isSome) then
    if e ≤ s || (e - s) % 4 != 0 then throw s!"Prog {p.id} RET: no epilogue" else
    match symWords t rs ((e - s) / 4) s {} with
    | .error msg => throw s!"Prog {p.id} RET: {msg}"
    | .ok (σ, c) =>
      let back := match p.to.sym with
        | some y => MCtl.jmpSym y p.to.offset
        | none => .reg (if az == 0 || leaf then .x 30 else .ld 8 .sp)
      match retOK az leaf σ c back with
      | .ok () => pure ()
      | .error msg => throw s!"Prog {p.id} RET: {msg}"
  else
    match checkProg t rs offs az ez p s e with
    | .ok () => pure ()
    | .error msg => throw s!"Prog {p.id} {p.as.name}: {msg}"

/-- The body Progs in list order with their offsets (`ss`; the last one's words end at
`lastEnd`). -/
def checkBody (t : ByteArray) (rs : List Reloc) (offs : List (Nat × Nat)) (az ez : Int)
    (leaf : Bool) : List Prog → List Nat → Nat → Except String Unit
  | p :: ps, s :: ss, lastEnd => do
    checkOne t rs offs az ez leaf p s (ss.headD lastEnd)
    checkBody t rs offs az ez leaf ps ss lastEnd
  | _, _, _ => pure ()

/-- Each Prog's offset: its PC in the assembled list, or (no PC: `TEXT`, an `END` placeholder)
the next Prog's, `lastEnd` after the last. -/
def startsOf (lastEnd : Nat) : List (Option Nat) → List Nat
  | [] => []
  | o :: os => let rest := startsOf lastEnd os; o.getD (rest.headD lastEnd) :: rest

/-- What `checkObj` returns: the machine offset of each P0 Prog (aligned with the list; `TEXT`
at the body's start), the offset the last Prog falls through to, the frame, and the prologue's
stack check (its end and the morestack tail's offset) if any. -/
structure Tab where
  offs : Array Nat
  endOff : Nat
  autosize : Int
  extrasize : Int
  leaf : Bool
  /-- The stack check: its end, the morestack tail's offset, the `g` offset it reads. -/
  check : Option (Nat × Nat × Nat)
  deriving Repr, Inhabited

/-- The assembled function: text bytes, relocations, and the assembler's final Prog list (a hint
for the PCs; P0 IDs are kept by the assembler). -/
structure ObjIn where
  text : ByteArray
  relocs : Array Reloc
  progs : Array Prog

/-- A function without `CALL` (the assembler's `LEAF`). -/
def leafOf (ps : Array Prog) : Bool :=
  ps.all fun p => p.as != .CALL && p.as != .DUFFZERO && p.as != .DUFFCOPY

/-- The validator (module doc). -/
def checkObj (ps : Array Prog) (spills : Array Spill) (o : ObjIn) : Except String Tab := do
  let some text := ps[0]? | throw "empty Prog list"
  if text.as != .TEXT then throw "the list does not start with TEXT"
  let ids := ps.toList.map (·.id)
  unless ids.Nodup do throw "duplicate Prog IDs"
  unless ids.all (· < 2 ^ 32) do throw "Prog ID ≥ 2^32"
  if ps.size < 2 then throw "no body"
  let pcs : Std.HashMap Nat Int := o.progs.foldl (fun m p => m.insert p.id p.pc) {}
  let some t2 := o.progs.find? (·.id == text.id) | throw "no TEXT in the assembled list"
  -- `span7` leaves the frame size in `TEXT` (`autosize`); `extrasize` is what `preprocess`
  -- added to genssa's frame size besides the saved LR (`Link.extrasize`)
  let az := t2.to.offset % 2 ^ 32
  let ez := if az == 0 then 0 else az - text.to.offset - 8
  let leaf := leafOf ps
  let rs := o.relocs.toList
  let t := o.text
  -- the PCs of the body Progs (an `END` placeholder, which `Flushplist` drops, at the next
  -- Prog's PC; it has no meaning, so `runProg` never steps it)
  let mut pcsOpt : Array (Option Nat) := #[none]
  for h : k in [1:ps.size] do
    match pcs.get? ps[k].id with
    | some pc => if pc < 0 then throw "negative PC" else pcsOpt := pcsOpt.push (some pc.toNat)
    | none =>
      if ps[k].as == .END then pcsOpt := pcsOpt.push none
      else throw s!"P0 Prog {ps[k].id} ({ps[k].as.name}) not in the assembled list"
  let body := ((pcsOpt.toList.drop 1).findSome? id).getD 0
  let check ← checkPrologue t rs az body
  -- the end of the last Prog's words
  let firstPool := (o.progs.find? fun p => p.as == .WORD || p.as == .DWORD).map (·.pc.toNat)
  let rec trimZero : Nat → Nat
    | 0 => 0
    | n + 1 => if wordAt t (4 * n) == 0 then trimZero n else n + 1
  let codeEnd := match firstPool with
    | some q => q
    | none => 4 * trimZero (t.size / 4)
  let lastEnd := match check with
    | some (_, tail, _) => tail
    | none => codeEnd
  let starts := startsOf lastEnd pcsOpt.toList
  if starts.length != ps.size || starts.headD 0 != body then throw "internal: PC table"
  let offs := (ps.toList.zip starts).map fun (p, s) => (p.id, s)
  checkBody t rs offs az ez leaf (ps.toList.drop 1) (starts.drop 1) lastEnd
  if let some (_, tail, _) := check then
    let _ ← checkTail t rs spills.toList 0 tail
  return { offs := starts.toArray, endOff := lastEnd, autosize := az, extrasize := ez, leaf, check }

end GoFV.Asm.CheckObj
