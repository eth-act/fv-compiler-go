import GoFV.Asm.Prog
import GoFV.Asm.Reg
import GoFV.SSA.Sem.RunMach

/-!
# `runProg`: the machine whose instructions are Progs (`docs/plans/semantics3.md` §7)

A Prog list (P0 after `genssa`, P1 after `progedit`, P2 the asm section after `span7`) runs on
the machine of §3 (`MState`: X0–X30, SP, V0–V31, NZCV, PC, flat byte memory) with each Prog's
meaning given directly in Go's assembly-language operand conventions (`cmd/internal/obj/arm64`:
`OP from, reg, to` is `to = reg OP from`, `MADD Rm, Ra, Rn, Rd` with `Ra` in `reg` and `Rn` in
`RestArgs`, `LDP off(Rn), (Rt1, Rt2)`, `CASALD Rs, (Rn), Rt`, …), without the encoder.

* `progEffect L p s`: what `p` does from `s` (`Eff`: registers written, `SP`, `V` registers,
  flags, loads, stores in order, the next PC if not the fall-through), or why it has no
  specified meaning (data words, opcodes outside the specified subset).
* `Eff.apply e s next`: the effect on the state; `progStep L p s`: the deterministic step (`R27`
  unchanged unless `p` writes it); `progSpec L p s s'`: the relational step, `R27` (REGTMP, the
  assembler's scratch) left free unless `p` names `R27` explicitly.
* `runProg H L ps ret`: run a Prog list with the runtime hooks `H` of `runMach`
  (`GoFV/SSA/Sem/RunMach.lean`), so the two compare directly.

**The PC model.** The PC is an address, as in `runMach`. The link layout `L : Link` places each
Prog (by ID) at `L.text + L.off id` and says where it falls through to (`L.next id`, the
address after the Prog); symbol `y<n>` is at `L.sym n`, and `L.autosize`/`L.extrasize` give the
frame of §5 for `NAME_AUTO`/`NAME_PARAM` operands. On P2, `off` is the Prog's `Pc` after
`span7` and `next` the `Pc` of its successor in the list (`Link.ofProgs ps (·.pc)`): zero-size
Progs share the address of the Prog after them. P0/P1 have no PCs; `Link.byId` places the Prog
with ID `n` at `text + 4 n` and lets each Prog fall through to its list successor. At a PC, the
Prog executed is the first Prog of the list that **occupies** that address (`progAt?`: placed
there, falling through elsewhere). Zero-size Progs (P2: `TEXT`, `PCDATA`, `FUNCDATA`, `NOP` =
`obj.ANOP`, which share the address of the Prog after them) occupy nothing and are never
executed, so a PC with only zero-size Progs of the list is a PC with no Prog, also when the list
is cut at them (a basic block). Under the ID layout every Prog occupies its own address and the
pseudo-ops are skips (`Prog.isSkip`: PC to the fall-through, nothing else).
Branch targets are Prog IDs (`L.off`), calls and jumps to symbols go to `L.sym` (P0/P1's static
call `CALL sym(SB)`, a `TYPE_MEM` operand, as the `CALL sym` `progedit` makes of it); a CALL
writes the fall-through address to `X30`. P0/P1's `RET` (without operand, or of a symbol: a tail
call) is unspecified (stuck):
it returns through the frame that only `preprocess` makes explicit, and its meaning, the
epilogue, is stated on the machine (`checkObj`, `docs/plans/proofs3.md` §7); P2's `RET (Rn)`
jumps to `Rn`.

A run (`runProg`) **returns** when the PC is `ret` (before any Prog there); at a PC with no
Prog — the target of a `CALL` leaving the list, a jump out of it, the end — it consults
`H.call` exactly like `runMach`; a load or store whose address is in the nil page is
`panicked .nilDeref` (the state before the Prog), like `runMach`'s `Fault.nilPage`; a Prog
without a specified meaning is `stuck`. Fuel counts Progs (skips included) and hook calls.

`GoFVTest/Arm64Decode.lean` (`arm64-decode`) checks `progStep` per Prog and `runProg` per basic
block against `GoFV.Arm64.step`/`runMach` on the words the assembler encoded (relocations
applied as the linker would).
-/

namespace GoFV.Arm64

open GoFV.Asm
open GoFV.SSA.Sem (Flags)
open GoFV.Asm.ARM64 (REG_R0 REG_R31 REG_F0 REG_V0 REG_RSP REG_ARNG REG_EXT REG_LSL C_XPRE C_XPOST
  SPOP_EQ)

/-! ## The link layout -/

/-- Where a Prog list and its symbols are (the PC model of the module doc). -/
structure Link where
  /-- The address of symbol `y<n>`. -/
  sym : Nat → BitVec 64
  /-- The text base. -/
  text : BitVec 64
  /-- The offset from `text` of the Prog with a given ID (its first word on P2). -/
  off : Nat → Option Int
  /-- The offset from `text` the Prog with a given ID falls through to. -/
  next : Nat → Option Int
  /-- The frame size (asm-section `TEXT` `to.offset`, §5). -/
  autosize : Int
  /-- `autosize - framesize - 8` when `autosize ≠ 0`, else 0 (§5). -/
  extrasize : Int

namespace Link

/-- The address of the Prog with ID `id`. -/
def addr (L : Link) (id : Nat) : Option (BitVec 64) :=
  (L.off id).map fun o => L.text + BitVec.ofInt 64 o

/-- The fall-through address of the Prog with ID `id`. -/
def nextAddr (L : Link) (id : Nat) : Option (BitVec 64) :=
  (L.next id).map fun o => L.text + BitVec.ofInt 64 o

/-- The fall-through offset of the Prog with ID `id` in `ps`: its successor's, `endOff` for the
last Prog. -/
def nextOff (off : Prog → Int) (endOff : Int) (id : Nat) : List Prog → Option Int
  | [] => none
  | [p] => if p.id = id then some endOff else none
  | p :: q :: r => if p.id = id then some (off q) else nextOff off endOff id (q :: r)

/-- The layout of a Prog list with offsets `off`, each Prog falling through to its successor
and the last one to `endOff`. P2: `off := (·.pc)`, `endOff` the end of the last Prog's code. -/
def ofProgs (sym : Nat → BitVec 64) (text : BitVec 64) (autosize extrasize : Int) (ps : List Prog)
    (off : Prog → Int) (endOff : Int) : Link where
  sym
  text
  off id := (ps.find? (·.id = id)).map off
  next id := nextOff off endOff id ps
  autosize
  extrasize

/-- The ID layout for P0/P1 (no PCs yet): the Prog with ID `n` at `text + 4 n`. -/
def byId (sym : Nat → BitVec 64) (text : BitVec 64) (autosize extrasize : Int) (ps : List Prog) :
    Link :=
  ofProgs sym text autosize extrasize ps (fun p => 4 * p.id)
    (4 * (ps.foldl (fun m p => max m p.id) 0 + 1))

end Link

/-! ## Operands (obj register numbering, `GoFV.Asm.ARM64`) -/

namespace ProgOp

def gpIdx? (r : Int) : Option Nat :=
  if REG_R0 ≤ r && r ≤ REG_R31 then some (r - REG_R0).toNat else none

/-- A floating-point or vector register (`Fn`, `Vn`, `Vn.<T>`, `Vn.<T>[i]`): its number. -/
def fpIdx? (r : Int) : Option Nat :=
  if REG_F0 ≤ r && r < REG_V0 + 32 then some ((r - REG_F0).toNat % 32)
  else if REG_ARNG ≤ r && r < REG_ARNG + 1024 then some ((r - REG_R0).toNat % 32)
  else none

/-- Truncation to the datasize. -/
def trunc (sf : Bool) (x : BitVec 64) : BitVec 64 := if sf then x else x.setWidth 32 |>.setWidth 64

/-- An extended register `Rn.<ext><<amount` (`REG_EXT` range): bits 8–10 the extension, bits
5–7 the amount. -/
def extReg? (r : Int) : Option (Nat × Nat × Nat) :=
  let d := (r - REG_R0).toNat
  if r ≥ REG_EXT && r < REG_EXT + 4096 then some (d % 32, d / 256 % 8, d / 32 % 8)
  else none

/-- The general register a register field names: `Rn`, or the register of `Rn.<ext>` /
`Rn<<k` (`REG_EXT`, `REG_LSL` ranges). -/
def gpField? (r : Int) : Option Nat :=
  match gpIdx? r with
  | some i => some i
  | none =>
    if (REG_LSL ≤ r && r < REG_LSL + 512) || (REG_EXT ≤ r && r < REG_EXT + 4096) then
      some ((r - REG_R0).toNat % 32)
    else none

/-- `s` begins with `p` (on the characters, so that the kernel and `decide` reduce it). -/
def startsS (s p : String) : Bool := p.toList.isPrefixOf s.toList

/-- `s` ends with `p`. -/
def endsS (s p : String) : Bool := p.toList.isSuffixOf s.toList

/-- `s` without its first `k` characters. -/
def dropS (s : String) (k : Nat) : String := String.ofList (s.toList.drop k)

/-- `s` without its last `k` characters. -/
def chopS (s : String) (k : Nat) : String := String.ofList (s.toList.take (s.length - k))

/-- The condition of a `SPECIAL` operand (`SPOP_EQ` … `SPOP_NV`). -/
def condOfSpecial (a : Addr) : Except String (BitVec 4) :=
  if a.type == .SPECIAL && SPOP_EQ ≤ a.offset && a.offset < SPOP_EQ + 16 then
    pure (BitVec.ofInt 4 (a.offset - SPOP_EQ))
  else throw "condition operand"

end ProgOp

open ProgOp

/-- Whether an operand names general register `k` (as a register, index, shifted or extended
register, or the second register of a pair). -/
def _root_.GoFV.Asm.Addr.namesX (a : Addr) (k : Nat) : Bool :=
  gpField? a.reg == some k || gpField? a.index == some k ||
    (a.type == .SHIFT && a.offset.toNat / 65536 % 32 == k) ||
    (a.type == .REGREG && gpField? a.offset == some k)

/-- Whether a Prog names general register `k` in any operand. -/
def _root_.GoFV.Asm.Prog.namesX (p : Prog) (k : Nat) : Bool :=
  p.from_.namesX k || p.to.namesX k || gpField? p.reg == some k || gpField? p.regTo2 == some k ||
    p.rest.any (·.2.namesX k)

/-- Pseudo-ops: no code, no effect (`TEXT`, `FUNCDATA`, `PCDATA`, `obj.ANOP` = `NOP`). -/
def _root_.GoFV.Asm.Prog.isSkip (p : Prog) : Bool :=
  match p.as with
  | .TEXT | .FUNCDATA | .PCDATA | .NOP => true
  | _ => false

/-! ## Effects -/

/-- What a Prog does, from a given state. Lists are latest first, except `stores` (in order). -/
structure Eff where
  /-- General registers written (index 0–30). -/
  x : List (Nat × BitVec 64) := []
  sp : Option (BitVec 64) := none
  v : List (Nat × BitVec 128) := []
  flags : Option Flags := none
  /-- Loads: address, size in bytes. -/
  loads : List (BitVec 64 × Nat) := []
  /-- Stores in order: address, size in bytes, value. -/
  stores : List (BitVec 64 × Nat × Nat) := []
  /-- The next PC if not the fall-through. -/
  pc : Option (BitVec 64) := none

/-- The context of a Prog's effect. -/
structure ProgCtx where
  L : Link
  s : MState
  p : Prog

namespace Eff

def wX (e : Eff) (r : Int) (val : BitVec 64) : Except String Eff :=
  if r == REG_R31 then pure e
  else if r == REG_RSP then pure { e with sp := some val }
  else match gpIdx? r with
    | some i => pure { e with x := (i, val) :: e.x }
    | none => throw s!"destination register {r}"

def wV (e : Eff) (r : Int) (val : BitVec 128) : Except String Eff :=
  match fpIdx? r with
  | some i => pure { e with v := (i, val) :: e.v }
  | none => throw s!"destination fp register {r}"

/-- Record a load of `n` bytes at `a`. -/
def ld (e : Eff) (a : BitVec 64) (n : Nat) : Eff := { e with loads := (a, n) :: e.loads }

/-- The first access in the nil page, if any (the machine checks each access's address). -/
def nilAccess? (e : Eff) : Option (BitVec 64) :=
  (e.loads.map (·.1) ++ e.stores.map (·.1)).find? nilPage

/-- The effect on a state, with `next` the fall-through address: registers (the latest write to
a register wins), `SP`, `V`, flags, the stores in order, the PC. Everything else, `R27`
included, is unchanged. -/
def apply (e : Eff) (s : MState) (next : BitVec 64) : MState :=
  let s := e.x.foldr (fun (i, val) s => s.wX (BitVec.ofNat 5 i) val) s
  let s := e.v.foldr (fun (i, val) s => s.wV (BitVec.ofNat 5 i) val) s
  { s with
    sp := e.sp.getD s.sp
    nzcv := e.flags.getD s.nzcv
    mem := e.stores.foldl (fun m (a, n, val) => writeMem m a n (BitVec.ofNat (8 * n) val)) s.mem
    pc := e.pc.getD next }

end Eff

namespace ProgCtx

def x (c : ProgCtx) (r : Int) : Except String (BitVec 64) :=
  if r == REG_RSP then pure c.s.sp
  else match gpIdx? r with
    | some i => pure (c.s.rX (BitVec.ofNat 5 i))
    | none => throw s!"register {r}"

def v (c : ProgCtx) (r : Int) : Except String (BitVec 128) :=
  match fpIdx? r with
  | some i => pure (c.s.v (BitVec.ofNat 5 i))
  | none => throw s!"fp register {r}"

/-- A source operand (register, shifted register, extended register, constant) at the datasize. -/
def src (c : ProgCtx) (sf : Bool) (a : Addr) : Except String (BitVec 64) := do
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

/-- The address a memory operand denotes and the base register's write-back (`.W` = `C_XPRE`,
`.P` = `C_XPOST`). `NAME_AUTO` at `SP + autosize + off - extrasize`, `NAME_PARAM` at
`SP + autosize + off + 8` (§5), symbols at `L.sym`. -/
def mem (c : ProgCtx) (a : Addr) : Except String (BitVec 64 × Option (Int × BitVec 64)) := do
  if a.type != .MEM then throw s!"memory operand {a.type.name}"
  let off := BitVec.ofInt 64 a.offset
  match a.name with
  | .AUTO => pure (c.s.sp + BitVec.ofInt 64 (c.L.autosize + a.offset - c.L.extrasize), none)
  | .PARAM => pure (c.s.sp + BitVec.ofInt 64 (c.L.autosize + a.offset + 8), none)
  | .EXTERN | .STATIC =>
    match a.sym with
    | some n => pure (c.L.sym n + off, none)
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

def load (c : ProgCtx) (a : BitVec 64) (n : Nat) : BitVec 64 := (readMem c.s.mem a n).setWidth 64

/-- The branch target of a `BRANCH` operand: a Prog by ID, or a symbol. -/
def target (c : ProgCtx) (a : Addr) : Except String (BitVec 64) := do
  match a.type, a.val, a.sym with
  | .BRANCH, .target id, _ =>
    match c.L.addr id with
    | some pc => pure pc
    | none => throw "branch target not in the list"
  | .BRANCH, _, some n => pure (c.L.sym n + BitVec.ofInt 64 a.offset)
  | _, _, _ => throw s!"branch operand {a.type.name}"

/-- The fall-through address (a CALL's return address). -/
def fall (c : ProgCtx) : Except String (BitVec 64) :=
  match c.L.nextAddr c.p.id with
  | some a => pure a
  | none => throw "no fall-through address"

/-- `reg` of a three-operand Prog, defaulting to `to`. -/
def rn (c : ProgCtx) : Int := if c.p.reg != 0 then c.p.reg else c.p.to.reg

def rest (c : ProgCtx) (i : Nat) : Except String Addr :=
  match c.p.rest[i]? with
  | some (_, a) => pure a
  | none => throw "missing RestArgs operand"

end ProgCtx

/-! ## Integer operations by opcode -/

namespace ProgOp

/-- The datasize of an opcode with an optional `W` suffix: `(base name, sf)`. -/
def baseOf (name : String) (ws : List String) : Option (String × Bool) :=
  if ws.contains name then some (name, true)
  else if endsS name "W" && ws.contains (chopS name 1) then some (chopS name 1, false)
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
      GoFV.SSA.Sem.addWithCarry (e x) (if startsS op "S" then ~~~(e y) else e y) cin
    if endsS op "S" then wf r else nf r.1
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
  let pre (p : String) : Option String := if startsS name p then some (dropS name p.length) else none
  match pre "LDADDAL", pre "SWPAL", pre "LDCLRAL", pre "LDORAL", pre "LDEORAL" with
  | some s, _, _, _, _ => some (sz s, fun old v => old + v)
  | _, some s, _, _, _ => some (sz s, fun _ v => v)
  | _, _, some s, _, _ => some (sz s, fun old v => old &&& ~~~v)
  | _, _, _, some s, _ => some (sz s, fun old v => old ||| v)
  | _, _, _, _, some s => some (sz s, fun old v => old ^^^ v)
  | _, _, _, _, _ => none

/-- The access size of an opcode suffix: none or `D` 8 bytes (`LDAR`, `CASALD`), `W` 4, `H` 2,
`B` 1. -/
def suffixBytes (s : String) : Nat :=
  if s == "" || s == "D" then 8 else if s == "W" then 4 else if s == "H" then 2 else 1

def maskN (n : Nat) (x : BitVec 64) : BitVec 64 := if n == 8 then x else x &&& BitVec.ofNat 64 (2 ^ (8 * n) - 1)

/-! ## Floating point by opcode -/

def fpType (name : String) : BitVec 2 := if endsS name "S" then 0 else 1

/-- The bits of an `FCONST` operand at single (`ftype` 0) or double precision. -/
def fconst (ftype : BitVec 2) (a : Addr) : Except String (BitVec 128) :=
  match a.val with
  | .float bits =>
    let d : BitVec 64 := BitVec.ofNat 64 bits.toNat
    if ftype = 0 then pure ((GoFV.IEEE.convert GoFV.IEEE.Fmt.b64 GoFV.IEEE.Fmt.b32 .rne d).setWidth 128)
    else pure (d.setWidth 128)
  | _ => throw "FCONST without a value"

end ProgOp

/-- The effect of a Prog with code (in Go's operand conventions), or why it has no specified
meaning. -/
def progEffect (c : ProgCtx) : Except String Eff := do
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
      let e := e.ld a n
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
      let e := (e.ld a n).ld (a + nb) n
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
  if startsS name "LDAR" || startsS name "LDAXR" then
    let n := suffixBytes (if startsS name "LDAR" then (dropS name 4) else (dropS name 5))
    let (a, _) ← c.mem p.from_
    return ← (e.ld a n).wX p.to.reg (c.load a n)
  if startsS name "STLR" || startsS name "STLXR" then
    let n := suffixBytes (if startsS name "STLR" then (dropS name 4) else (dropS name 5))
    let (a, _) ← c.mem p.to
    let e ← if startsS name "STLXR" then e.wX p.regTo2 0 else pure e
    return { e with stores := (a, n, (← c.x p.from_.reg).toNat % 2 ^ (8 * n)) :: e.stores }
  if startsS name "CASAL" then
    let n := suffixBytes (dropS name 5)
    let (a, _) ← c.mem p.to
    let old := c.load a n
    let cmp := maskN n (← c.x p.from_.reg)
    let e ← (e.ld a n).wX p.from_.reg old
    if old == cmp then
      return { e with stores := [(a, n, (← c.x p.regTo2).toNat % 2 ^ (8 * n))] }
    return e
  if let some (n, f) := rmw name then
    let (a, _) ← c.mem p.to
    let old := c.load a n
    let nw := maskN n (f old (← c.x p.from_.reg))
    let e ← (e.ld a n).wX p.regTo2 old
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
  if startsS name "FCVTZ" then
    let u := startsS (dropS name 5) "U"
    let rest := (dropS name 6)
    let src : BitVec 2 := if startsS rest "S" then 0 else 1
    let w := endsS rest "W"
    let x ← c.v p.from_.reg
    let r : BitVec 64 := if src = 0
      then (GoFV.IEEE.toFixed GoFV.IEEE.Fmt.b32 (x.setWidth 32) u (if w then 32 else 64) .rz).setWidth 64
      else (GoFV.IEEE.toFixed GoFV.IEEE.Fmt.b64 (x.setWidth 64) u (if w then 32 else 64) .rz).setWidth 64
    return ← e.wX p.to.reg r
  if startsS name "SCVTF" || startsS name "UCVTF" then
    let u := startsS name "U"
    let rest := (dropS name 5)
    let w := startsS rest "W"
    let dst : BitVec 2 := if endsS rest "S" then 0 else 1
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
    let sf := !endsS name "W"
    let z := trunc sf (← c.x p.from_.reg) == 0
    let t ← c.target p.to
    return if z == startsS name "CBZ" then { e with pc := some t } else e
  | "TBZ" | "TBNZ" =>
    let b := (← c.x p.reg).getLsbD p.from_.offset.toNat
    let t ← c.target p.to
    return if b == (name == "TBNZ") then { e with pc := some t } else e
  | "CALL" =>
    -- P0/P1 `CALL sym(SB)` (`TYPE_MEM`, `NAME_EXTERN`/`NAME_STATIC`, as `genssa` emits a static
    -- call) is the `CALL sym` (`TYPE_BRANCH`) that `progedit` rewrites it to
    let t ← if p.to.type == .BRANCH then c.target p.to
      else if p.to.type == .MEM && (p.to.name == .EXTERN || p.to.name == .STATIC) then
        match p.to.sym with
        | some n => pure (c.L.sym n + BitVec.ofInt 64 p.to.offset)
        | none => throw "symbol-less call target"
      else c.x p.to.reg
    let e ← e.wX (REG_R0 + 30) (← c.fall)
    return { e with pc := some t }
  | "RET" =>
    -- P0/P1's `RET` (no operand, as `genssa` emits it, or a symbol: a tail call) leaves a frame
    -- that only `preprocess` makes explicit: its meaning is the epilogue's, stated on the
    -- machine (`checkObj`'s epilogue, proofs3 §7). P2's `RET (Rn)` jumps to `Rn`.
    if p.to.type == .NONE || p.to.sym.isSome then throw "P0 RET: the epilogue's (machine level)"
    return { e with pc := some (← c.x p.to.reg) }
  | "NOP" | "HINT" | "DMB" | "PRFM" => return e
  | "VCNT" => return ← e.wV p.to.reg ((GoFV.SSA.Sem.Arm64.vcnt ((← c.v p.from_.reg).setWidth 64)).setWidth 128)
  | "VUADDLV" =>
    return ← e.wV p.to.reg ((GoFV.SSA.Sem.Arm64.vuaddlv ((← c.v p.from_.reg).setWidth 64)).setWidth 128)
  | _ => throw "opcode not specified"

/-! ## Steps -/

/-- Why a Prog step has no successor. -/
inductive ProgFault where
  /-- A load or store in the nil page. -/
  | nilPage (addr : BitVec 64)
  /-- No specified meaning (data word, opcode outside the subset, no fall-through address). -/
  | stuck (msg : String)

/-- One Prog, deterministically: skips go to the fall-through, other Progs apply their effect
(`R27` unchanged unless written). -/
def progStep (L : Link) (p : Prog) (s : MState) : Except ProgFault MState :=
  match L.nextAddr p.id with
  | none => .error (.stuck "no fall-through address")
  | some next =>
    if p.isSkip then .ok { s with pc := next }
    else match progEffect ⟨L, s, p⟩ with
      | .error msg => .error (.stuck msg)
      | .ok e =>
        match e.nilAccess? with
        | some a => .error (.nilPage a)
        | none => .ok (e.apply s next)

/-- `s` agrees with `t` everywhere except in `X27` when `tmpFree`. -/
structure AgreeTmp (tmpFree : Bool) (t s : MState) : Prop where
  x : ∀ k : Reg, (tmpFree = true → k ≠ 27) → s.x k = t.x k
  sp : s.sp = t.sp
  v : s.v = t.v
  nzcv : s.nzcv = t.nzcv
  pc : s.pc = t.pc
  mem : s.mem = t.mem

/-- The specification of one Prog (§7): a skip moves the PC to the fall-through; any other Prog
has its architectural effect with no access in the nil page, and leaves `R27` (REGTMP) free
unless it names `R27` explicitly. -/
def progSpec (L : Link) (p : Prog) (s s' : MState) : Prop :=
  ∃ next, L.nextAddr p.id = some next ∧
    if p.isSkip then s' = { s with pc := next }
    else ∃ e, progEffect ⟨L, s, p⟩ = .ok e ∧ e.nilAccess? = none ∧
      AgreeTmp (!p.namesX 27) (e.apply s next) s'

/-- The deterministic step meets the specification. -/
theorem progStep_spec {L : Link} {p : Prog} {s s' : MState} (h : progStep L p s = .ok s') :
    progSpec L p s s' := by
  unfold progStep at h
  cases hn : L.nextAddr p.id with
  | none => simp [hn] at h
  | some next =>
    simp only [hn] at h
    refine ⟨next, hn, ?_⟩
    cases hs : p.isSkip with
    | true =>
      simp only [hs, ↓reduceIte, Except.ok.injEq] at h ⊢
      exact h.symm
    | false =>
      simp only [hs, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases he : progEffect ⟨L, s, p⟩ with
      | error msg => simp [he] at h
      | ok e =>
        cases hnil : e.nilAccess? with
        | some a => simp [he, hnil] at h
        | none =>
          simp only [he, hnil, Except.ok.injEq] at h
          subst h
          exact ⟨e, rfl, hnil, fun _ _ => rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Whether a Prog occupies its address: it is placed and falls through elsewhere (on P2: it has
code). -/
def Link.occupies (L : Link) (p : Prog) : Bool :=
  match L.addr p.id, L.nextAddr p.id with
  | some a, some n => a != n
  | _, _ => false

/-- The Prog the PC is at: the first Prog of `ps` occupying that address. -/
def progAt? (L : Link) (ps : List Prog) (pc : BitVec 64) : Option Prog :=
  ps.find? fun p => L.addr p.id == some pc && L.occupies p

/-- `runProg H L ps ret fuel s`: run the Prog list `ps` laid out by `L` from `s` until the PC is
`ret`, with at most `fuel` steps (Progs and hook calls). -/
def runProg (H : Hooks) (L : Link) (ps : List Prog) (ret : BitVec 64) : Nat → MState → MOutcome
  | 0, _ => .outOfFuel
  | n + 1, s =>
    if s.pc = ret then .returned s
    else match progAt? L ps s.pc with
      | some p =>
        match progStep L p s with
        | .ok s' => runProg H L ps ret n s'
        | .error (.nilPage _) => .panicked .nilDeref s
        | .error (.stuck msg) => .stuck msg
      | none =>
        match H.call s with
        | some (.ret s') => runProg H L ps ret n s'
        | some (.panicked e s') => .panicked e s'
        | some (.stuck msg) => .stuck msg
        | none => .stuck s!"no Prog and no hook at {s.pc.toHex}"

/-! ## Witnesses -/

/-- A Prog with the given opcode and operands (ID `id`, no position). -/
def mkProg (id : Nat) (as : As) (from_ to : Addr) (reg : Int := 0) : Prog :=
  { id, pc := 4 * id, spadj := 0, isize := 4, optab := 0, pool := none, as, scond := 0, from_, reg,
    rest := #[], to, regTo2 := 0, mark := 0, pos := default }

/-- `MOVD $5, R0`. -/
def wMov : Prog := mkProg 0 .MOVD { type := .CONST, offset := 5 } { type := .REG, reg := REG_R0 }

/-- `RET (R30)`: P2's return (P0's `RET` without operand is the epilogue's, unspecified here). -/
def wRet : Prog := mkProg 1 .RET {} { type := .MEM, reg := REG_R0 + 30 }

/-- P0's `RET` without operand. -/
def wRet0 : Prog := mkProg 1 .RET {} {}

/-- `MOVD (R1), R2`. -/
def wLoad : Prog := mkProg 2 .MOVD { type := .MEM, reg := REG_R0 + 1 } { type := .REG, reg := REG_R0 + 2 }

/-- `CALL y7`. -/
def wCall : Prog := mkProg 3 .CALL {} { type := .BRANCH, sym := some 7 }

/-- `CALL y7(SB)`: P0's form of a static call (`TYPE_MEM`, `NAME_EXTERN`). -/
def wCallMem : Prog := mkProg 5 .CALL {} { type := .MEM, name := .EXTERN, sym := some 7 }

/-- `PCDATA` (a skip). -/
def wPcdata : Prog := mkProg 4 .PCDATA { type := .CONST } { type := .CONST }

/-- The ID layout of the witness Progs at `0x1000`, symbol `y<n>` at `0x8000 + 16 n`. -/
def wLink (ps : List Prog) : Link :=
  Link.byId (fun n => 0x8000 + BitVec.ofNat 64 (16 * n)) 0x1000 0 0 ps

/-- `progSpec` is satisfiable: `MOVD $5, R0` writes `X0` and falls through, `R27` free. -/
theorem progSpec_witness :
    progSpec (wLink [wMov, wRet]) wMov (MState.const 7 0x100000 0x1000)
      { MState.const 7 0x100000 0x1004 with x := fun i => if i = 0 then 5 else if i = 27 then 99 else 7 } := by
  refine ⟨0x1004, by decide, ?_⟩
  refine ⟨{ x := [(0, 5)] }, rfl, by decide, fun k hk => ?_, rfl, rfl, rfl, rfl, rfl⟩
  have hk : ¬k = 27#5 := hk (by decide +kernel)
  simp [Eff.apply, MState.wX, MState.const, hk]

/-- A skip moves the PC to the fall-through. -/
theorem progSpec_skip_witness :
    progSpec (wLink [wPcdata, wRet]) wPcdata (MState.const 7 0x100000 0x1010)
      (MState.const 7 0x100000 0x1004) :=
  ⟨0x1004, by decide, rfl⟩

/-- `MOVD $5, R0; RET` from `0x1000` with `X30 = 0x2000` returns there with `X0 = 5`. -/
theorem runProg_witness :
    (match runProg Hooks.none (wLink [wMov, wRet]) [wMov, wRet] 0x2000 3
        { MState.const 0x2000 0x100000 0x1000 with x := fun _ => 0x2000 } with
      | .returned s => s.x 0 == 5 && s.pc == 0x2000
      | _ => false) = true := by decide

/-- P0's `RET` without operand is stuck: its meaning is the epilogue's, on the machine. -/
theorem runProg_ret0_witness :
    (match runProg Hooks.none (wLink [wMov, wRet0]) [wMov, wRet0] 0x2000 3
        { MState.const 0x2000 0x100000 0x1000 with x := fun _ => 0x2000 } with
      | .stuck _ => true
      | _ => false) = true := by decide

/-- A load through `X1 = 8` is in the nil page: `panicked .nilDeref`. -/
theorem runProg_nil_witness :
    (match runProg Hooks.none (wLink [wLoad]) [wLoad] 0x2000 3 (MState.const 8 0x100000 0x1008) with
      | .panicked .nilDeref s => s.pc == 0x1008
      | _ => false) = true := by decide

/-- `CALL y7` leaves the list: the hook at `y7` returns to `X30`, the fall-through, where the run
returns. -/
theorem runProg_call_witness :
    (match runProg ⟨fun s => if s.pc = 0x8070 then some (.ret { s with pc := s.x 30 }) else none⟩
        (wLink [wCall, wRet]) [wCall, wRet] 0x1004 3 (MState.const 0 0x100000 0x100C) with
      | .returned s => s.pc == 0x1004 && s.x 30 == 0x1004
      | _ => false) = true := by decide

/-- P0's `CALL y7(SB)` goes to `y7` like `CALL y7`. -/
theorem runProg_callMem_witness :
    (match runProg ⟨fun s => if s.pc = 0x8070 then some (.ret { s with pc := s.x 30 }) else none⟩
        (wLink [wCallMem, wRet]) [wCallMem, wRet] 0x1004 3 (MState.const 0 0x100000 0x1014) with
      | .returned s => s.pc == 0x1004 && s.x 30 == 0x1004
      | _ => false) = true := by decide

end GoFV.Arm64
