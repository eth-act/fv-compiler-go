import GoFV.Asm.CheckObjSym

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
  `SP`, the flags and the stores in order, every machine load must be a load of the Prog, the
  Prog must not read `X27` or `X30`, and the control must agree: a branch to the offset of the
  target Prog, a call to the same symbol and addend, a return through the same register.
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

/-- The symbolic effect of a P0 Prog with code (`progEffect`) and its control, for the opcodes
the validator models. `az`, `ez`: the frame (`Link.autosize`, `Link.extrasize`). -/
def progSym (az ez : Int) (p : Prog) : Except String (Sym × PCtl) := do
  let name := p.as.name
  let σ : Sym := {}
  let rn : Int := if p.reg != 0 then p.reg else p.to.reg
  -- constant shifts (`binOp` of `LSL`/`LSR`/`ASR` with a constant)
  if let some (op, sf) := baseOf name ["LSL", "LSR", "ASR"] then
    if p.from_.type == .CONST then
      if p.from_.offset < 0 then throw s!"{name} by a negative amount"
      let x ← xP rn
      return (← wP σ p.to.reg (← shiftBfm op sf p.from_.offset.toNat x), .fall)
    throw s!"{name} by a register"
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
    if fp then throw s!"{name}: SIMD&FP"
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
    if fp then throw s!"{name}: SIMD&FP"
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
  match name with
  | "HINT" => if p.from_.offset == 0 then return (σ, .fall) else throw "HINT"
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
    throw "indirect CALL"
  | "RET" =>
    let r := if p.to.type == .NONE then REG_R0 + 30 else p.to.reg
    return (σ, .reg (← xP r))
  | _ => throw s!"opcode not modelled: {name}"

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

/-- The symbolic integer access of `ldst` at address `a` (no write-back). -/
def symAccess (σ : Sym) (size : BitVec 2) (opc : BitVec 2) (rt : Nat) (a : Ex) :
    Except String Sym := do
  let n := bytesOf size
  if size = 3 && opc = 2 then throw "PRFM"
  if opc != 0 then
    let (σ, v) ← σ.load a n
    pure (σ.wX rt (loadVal opc n v))
  else pure (σ.store a n (σ.rX rt))

/-- The words `[o, o + 4 n)` executed symbolically from `σ`, every word but the last falling
through; relocated words as linked: `BL` of `R_CALLARM64`, `ADRP` + `ADD` of `R_ADDRARM64`
(the target in the `ADD`'s destination, its page in the `ADRP`'s), `ADRP` + load/store of
`R_ARM64_PCREL_LDST*` (the access at the target). The relocated fields must be zero. -/
def symWords (t : ByteArray) (rs : List Reloc) : Nat → Nat → Sym → Except String (Sym × MCtl)
  | 0, _, σ => pure (σ, .fall)
  | n + 1, o, σ => do
    if o + 4 > t.size then throw s!"word at {o} past the text"
    let w := wordAt t o
    let some i := decode w | throw s!"undecodable word {w.toHex} at {o}"
    let step : Except String (Sym × MCtl × Nat) :=
      match relocAt rs o with
      | none => do
        if !(covering rs o).isEmpty then throw s!"word at {o} patched by several relocations"
        let (σ, c) ← symInsn i o σ
        pure (σ, c, 1)
      | some r => do
        let some y := r.sym | throw "relocation without symbol"
        let tgt := Ex.mkAdd (.sym y) (.k (BitVec.ofInt 64 r.add))
        if isCallReloc r.type then
          match i with
          | .b true 0 => pure (σ, .call y r.add, 1)
          | .b false 0 => pure (σ, .jmpSym y r.add, 1)
          | _ => throw "R_CALLARM64 not on a B or BL"
        else if n = 0 || o + 8 > t.size then throw "relocated pair cut"
        else if covering rs (o + 4) != [r] then throw s!"word at {o + 4} patched by several relocations"
        else match i, decode (wordAt t (o + 4)) with
          | .adr true 0 rd, some i2 =>
            let σ1 := σ.wX rd.toNat (.page tgt)
            if r.type == "R_ADDRARM64" then
              match i2 with
              | .addSubImm true false false false 0 rn rd2 =>
                if rn != rd then throw "R_ADDRARM64: ADD of another register" else
                pure (σ1.wXsp rd2.toNat tgt, .fall, 2)
              | _ => throw "R_ADDRARM64: not ADRP + ADD"
            else match ldstScale r.type, i2 with
              | some sc, .ldst size false opc (.uimm 0) rn rt =>
                if rn != rd then throw "PCREL_LDST: access through another register" else
                if size.toNat != sc then throw "PCREL_LDST: size" else do
                pure (← symAccess σ1 size opc rt.toNat tgt, .fall, 2)
              | _, _ => throw s!"relocation {r.type}"
          | _, _ => throw s!"relocation {r.type} not on ADRP"
    let (σ, c, used) ← step
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

/-- Whether any value of a P0 effect reads `X27` or `X30`. -/
def Sym.readsTmp (σ : Sym) : Bool :=
  let rd (e : Ex) := e.reads 27 || e.reads 30
  σ.x.any (rd ·.2) || rd σ.sp || σ.fl.reads 27 || σ.fl.reads 30 ||
    σ.loads.any (rd ·.1) || σ.stores.any fun (a, _, v) => rd a || rd v

/-- The machine effect `m` matches the Prog effect `p` (the module doc). -/
def sameEffect (m p : Sym) : Except String Unit := do
  for r in cmpRegs do
    if m.getX r != p.getX r then throw s!"R{r}: machine {(m.getX r).str}, Prog {(p.getX r).str}"
  if m.getX 30 != .x 30 || p.getX 30 != .x 30 then throw "R30 written"
  if m.sp != p.sp then throw "SP"
  if m.fl != p.fl then throw s!"flags: machine {repr m.fl}, Prog {repr p.fl}"
  if m.stores != p.stores then
    let f (l : List (Ex × Nat × Ex)) := l.map fun (a, n, v) => s!"[{a.str}]{n}={v.str}"
    throw s!"stores: machine {f m.stores}, Prog {f p.stores}"
  unless m.loads.all (p.loads.contains ·) do throw "a machine load the Prog does not perform"
  if p.readsTmp then throw "the Prog reads R27 or R30"

/-- The offset of a P0 Prog, by ID (`Tab.offs` aligned with the list). -/
def offOf (ids : List (Nat × Nat)) (id : Nat) : Option Nat := ids.lookup id

/-- The machine control `m` matches the Prog control `p` (branch offsets through `offs`). -/
def sameCtl (offs : List (Nat × Nat)) (m : MCtl) (p : PCtl) (pr : Sym) : Except String Unit := do
  let tgt (id : Nat) (q : Int) : Except String Unit :=
    match offOf offs id with
    | some o => if (o : Int) == q then pure () else throw s!"branch to {q}, target Prog at {o}"
    | none => throw "branch target not a P0 Prog"
  let ctlReads (e : Ex) : Bool := e.reads 27 || e.reads 30
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
  | .reg a, .reg a' => if a != .x 30 || a' != .x 30 then throw "return register" else
    if pr.getX 30 != .x 30 then throw "return after writing R30" else pure ()
  | .call n add, .call n' add' =>
    if n != n' || add != add' || add != 0 then throw "call target" else pure ()
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
at `0(SP)` and `FP` at `-8(SP)`, `R29 = SP - 8`. The large-frame form also writes `R20`. -/
def frameOK (az : Int) (σ : Sym) : Except String Unit := do
  let sp' := Ex.mkAdd .sp (.k (BitVec.ofInt 64 (-az)))
  let fp' := Ex.mkAdd .sp (.k (BitVec.ofInt 64 (-az - 8)))
  if σ.sp != sp' then throw "prologue: SP"
  if σ.getX 29 != fp' then throw "prologue: R29"
  for r in cmpRegs do
    if r != 29 && r != 20 && σ.getX r != .x r then throw s!"prologue: R{r} written"
  if σ.getX 30 != .x 30 then throw "prologue: R30 written"
  let st := [(sp', 8, Ex.x 30), (fp', 8, Ex.x 29)]
  if σ.stores != st && σ.stores != st.reverse then throw "prologue: stores"

/-- The epilogue's specification: `R29` restored (a leaf recomputes it, `SP + autosize - 8`,
others reload it from `-8(SP)`), `R30` reloaded from `0(SP)` unless a leaf, `SP` raised by
`autosize`, a return through `R30`. -/
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
  for r in cmpRegs do
    if r != 29 && σ.getX r != .x r then throw s!"epilogue: R{r} written"
  if σ.fl != .init then throw "epilogue: flags"
  if !σ.stores.isEmpty then throw "epilogue: stores"
  if c != back then throw "epilogue: return"

/-- The stack check: `[0, e)` ends in the `BLS` to the morestack tail (and, for big frames, a
`BLO` there before it); returns the tail's offset and the check's specification is met:
the limit `SP` (small frames) or `SP - (framesize - StackSmall)` compared unsigned with
`stackguard0` (`16(g)`). -/
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
    for r in cmpRegs do
      if r != 16 && r != 17 && σ.getX r != .x r then throw s!"stack check: R{r}"
    if q < 0 then throw "stack check: tail" else
    pure (o + 4 * n, q.toNat)
  | _ => throw "stack check: not a BLS"

/-- The words `[o, e)` up to and including the first one whose control is not a fall-through
(searching at most `fuel` words): its offset after, the effect and the control. -/
def symUntil (t : ByteArray) (rs : List Reloc) : Nat → Nat → Sym → Except String (Nat × Sym × MCtl)
  | 0, _, _ => throw "no branch"
  | fuel + 1, o, σ => do
    let used := match relocAt rs o with
      | some r => if isCallReloc r.type then 1 else 2
      | none => 1
    let (σ', c) ← symWords t rs used o σ
    if c == .fall then symUntil t rs fuel (o + 4 * used) σ' else pure (o + 4 * used, σ', c)

/-- The morestack tail at `o` (`stacksplit`): the spills of `FuncInfo.spills` at their entry
addresses (`SP + offset + 8`, the frame not yet allocated), `MOVD R30, R3`, the call, the
reloads and the jump back to the stack check at `check`. Returns the tail's end. -/
def checkTail (t : ByteArray) (rs : List Reloc) (spills : List Spill) (check o : Nat) :
    Except String Nat := do
  let mut st : List (Ex × Nat × Ex) := []
  let mut rl : List (Nat × Ex) := []
  for sp in spills do
    -- at entry: no frame yet
    let (a, wb) ← memP 0 0 0 sp.addr
    if wb.isSome then throw "tail: spill with write-back"
    let some r := gpIdx? sp.reg | throw "tail: spill register"
    match movMem sp.spill.name, pairOp sp.spill.name with
    | some (n, _, false), _ =>
      let some (n', sg, false) := movMem sp.unspill.name | throw s!"tail: unspill {sp.unspill.name}"
      if n' != n then throw "tail: unspill size"
      st := st ++ [(a, n, Ex.x r)]
      rl := (r, if sg then Ex.mkSext (8 * n) (.ld n a) else .ld n a) :: rl
    | _, some (false, n, false, false) =>
      let some r2 := gpIdx? sp.reg2 | throw "tail: spill register"
      let a2 := Ex.mkAdd a (.k (BitVec.ofNat 64 n))
      st := st ++ [(a, n, Ex.x r), (a2, n, Ex.x r2)]
      rl := (r2, Ex.ld n a2) :: (r, Ex.ld n a) :: rl
    | _, _ => throw s!"tail: spill {sp.spill.name}"
  let budget := (t.size - o) / 4
  let (o1, σ1, c1) ← symUntil t rs budget o {}
  match c1 with
  | .call _ _ => pure ()
  | _ => throw "tail: no call"
  if σ1.stores != st then throw "tail: spills"
  for r in cmpRegs do
    let want := if r == 3 then Ex.x 30 else Ex.x r
    if σ1.getX r != want then throw s!"tail: R{r} before the call"
  let (o2, σ2, c2) ← symUntil t rs budget o1 {}
  if c2 != .jmp check then throw "tail: not a jump back to the stack check"
  if !σ2.stores.isEmpty then throw "tail: stores after the call"
  for r in cmpRegs do
    let want := (rl.lookup r).getD (Ex.x r)
    if σ2.getX r != want then throw s!"tail: R{r} after the call: {(σ2.getX r).str}, want {want.str}"
  pure o2

/-- What `checkObj` returns: the machine offset of each P0 Prog (aligned with the list; `TEXT`
at the body's start), the offset the last Prog falls through to, the frame, and the prologue's
stack check (its end and the morestack tail's offset) if any. -/
structure Tab where
  offs : Array Nat
  endOff : Nat
  autosize : Int
  extrasize : Int
  leaf : Bool
  check : Option (Nat × Nat)
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
  -- prologue
  let mut check : Option (Nat × Nat) := none
  if az == 0 then
    if body != 0 then throw "frameless function with a prologue"
  else
    let mut fo := 0
    -- `MOVD 16(g), R16` (`24(g)` in a C function's prologue, `stackguard1`)
    let gOff? : Option Nat := match decode (wordAt t 0) with
      | some (.ldst 3 false 1 (.uimm 2) 28 16) => some 16
      | some (.ldst 3 false 1 (.uimm 3) 28 16) => some 24
      | _ => none
    if let some gOff := (if body ≥ 12 then gOff? else none) then
      let (ce, tail) ← checkStackCheck t rs az 0 gOff
      check := some (ce, tail)
      fo := ce
    if body ≤ fo || (body - fo) % 4 != 0 then throw "prologue: no frame words"
    let (σ, c) ← symWords t rs ((body - fo) / 4) fo {}
    if c != .fall then throw "prologue: branch"
    frameOK az σ
  -- the end of the last Prog's words
  let firstPool := (o.progs.find? fun p => p.as == .WORD || p.as == .DWORD).map (·.pc.toNat)
  let rec trimZero : Nat → Nat
    | 0 => 0
    | n + 1 => if wordAt t (4 * n) == 0 then trimZero n else n + 1
  let codeEnd := match firstPool with
    | some q => q
    | none => 4 * trimZero (t.size / 4)
  let lastEnd := match check with
    | some (_, tail) => tail
    | none => codeEnd
  let mut starts : Array Nat := Array.replicate ps.size lastEnd
  let mut nxt := lastEnd
  for h : j in [0:ps.size] do
    let k := ps.size - 1 - j
    if let some (some pc) := pcsOpt[k]? then nxt := pc
    starts := starts.set! k nxt
  let offs := (ps.toList.zip starts.toList).map fun (p, s) => (p.id, s)
  for h : k in [1:ps.size] do
    let p := ps[k]
    let s := starts[k]!
    let e := if k + 1 < ps.size then starts[k + 1]! else lastEnd
    if p.as == .RET && (p.to.type == .NONE || p.to.sym.isSome) then
      if e ≤ s || (e - s) % 4 != 0 then throw "RET: no epilogue"
      let (σ, c) ← symWords t rs ((e - s) / 4) s {}
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
  if let some (_, tail) := check then
    let _ ← checkTail t rs spills.toList 0 tail
  return { offs := starts, endOff := lastEnd, autosize := az, extrasize := ez, leaf, check }

end GoFV.Asm.CheckObj
