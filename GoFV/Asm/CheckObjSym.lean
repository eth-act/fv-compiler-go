import GoFV.SSA.Sem.RunProg

/-!
# `checkObj`'s symbolic states (`docs/plans/proofs3.md` §2, row D4/D5; semantics3 §3 (c))

The assembler validator compares two descriptions of what one P0 Prog does: the Prog's own
effect (`progEffect`, in Go's operand conventions) and the effect of the machine words the
assembler encoded for it (`GoFV.Arm64.exec` of their decoded instructions). Both are computed
**symbolically**, as a `Sym`: the general registers written, `SP`, the flags, the loads and the
stores, each value an `Ex` over the state *before* the Prog. Equal `Sym`s (with `X27`, the
assembler's scratch, ignored) mean equal effects on every state.

`Ex`'s operations are the data operations `exec` and `progEffect` share (`addSub`, `logical`,
`Shift.apply` through `sized`, `extendReg`, `bitfieldMove`, `sext`, loads), so the two sides
meet syntactically. Smart constructors (`Ex.add`, `Ex.mkAddSub`, …) fold constants and pick
one form for the identities the encodings need (`ORR Rd, ZR, Rm` is `Rm`, `ADD`/`SUB` of a
constant is `+`, …); `Ex.eval` gives the meaning, which each smart constructor must preserve
(`docs/plans/proofs3.md` §7).

`symInsn` is the machine side: the symbolic `exec` of one decoded instruction at a known offset
of the function, with its control outcome (`MCtl`: fall through, branch to an offset, …).
Instructions it does not model are rejected with the instruction's form.
-/

namespace GoFV.Asm.CheckObj

open GoFV.Arm64
open GoFV.SSA.Sem (Flags addWithCarry logicFlags)
open GoFV.SSA.Sem.Arm64 (Shift sext)

/-! ## Values -/

/-- A 64-bit value, symbolically, over the state before a Prog (`eval`). -/
inductive Ex where
  /-- General register `X r` (`r ≤ 30`). -/
  | x (r : Nat)
  | sp
  | k (c : BitVec 64)
  /-- The linked address of symbol `y<n>`. -/
  | sym (n : Nat)
  /-- The `n` bytes at the address, zero-extended (the memory before the Prog). -/
  | ld (n : Nat) (a : Ex)
  | add (a b : Ex)
  /-- `(addSub sf sub a b).1` (not a 64-bit `ADD`, nor `SUB` of a constant: those are `add`). -/
  | addSub (sf sub : Bool) (a b : Ex)
  /-- `(logical sf opc a b).1`. -/
  | logical (sf : Bool) (opc : BitVec 2) (a b : Ex)
  /-- `sized sf (Shift.apply (shiftOf k) · amt)`, `amt ≠ 0`. -/
  | shift (sf : Bool) (k : BitVec 2) (amt : Nat) (a : Ex)
  /-- `extendReg a opt sh`. -/
  | ext (opt : BitVec 3) (sh : Nat) (a : Ex)
  /-- `bitfieldMove sf opc immr imms d a`. -/
  | bfm (sf : Bool) (opc : BitVec 2) (immr imms : BitVec 6) (d a : Ex)
  /-- `ProgOp.trunc false a`: the low 32 bits, zero-extended. -/
  | lo32 (a : Ex)
  /-- `sext n a`. -/
  | sext (n : Nat) (a : Ex)
  /-- `a &&& ~~~0xFFF` (`ADRP`'s page). -/
  | page (a : Ex)
  deriving DecidableEq, Repr, Inhabited

/-- What an `Ex` is evaluated against: the state before the Prog and the symbol addresses. -/
structure Ctx where
  s : MState
  sym : Nat → BitVec 64

namespace Ex

/-- The meaning of an `Ex`. -/
def eval (c : Ctx) : Ex → BitVec 64
  | .x r => c.s.x (BitVec.ofNat 5 r)
  | .sp => c.s.sp
  | .k v => v
  | .sym n => c.sym n
  | .ld n a => (readMem c.s.mem (eval c a) n).setWidth 64
  | .add a b => eval c a + eval c b
  | .addSub sf sub a b => (GoFV.Arm64.addSub sf sub (eval c a) (eval c b)).1
  | .logical sf opc a b => (GoFV.Arm64.logical sf opc (eval c a) (eval c b)).1
  | .shift sf kd amt a => sized sf fun _ e => Shift.apply (shiftOf kd) (e (eval c a)) amt
  | .ext opt sh a => extendReg (eval c a) opt sh
  | .bfm sf opc immr imms d a => bitfieldMove sf opc immr imms (eval c d) (eval c a)
  | .lo32 a => ProgOp.trunc false (eval c a)
  | .sext n a => GoFV.SSA.Sem.Arm64.sext n (eval c a)
  | .page a => eval c a &&& ~~~(0xFFF : BitVec 64)

/-- A short rendering for rejection messages. -/
def str : Ex → String
  | .x r => s!"R{r}"
  | .sp => "SP"
  | .k v => if v.toInt.natAbs < 4096 then toString v.toInt else v.toHex
  | .sym n => s!"y{n}"
  | .ld n a => s!"ld{n}({str a})"
  | .add a b => s!"({str a}+{str b})"
  | .addSub sf sub a b => s!"{if sub then "sub" else "add"}{if sf then "" else "W"}({str a},{str b})"
  | .logical sf opc a b => s!"log{opc.toNat}{if sf then "" else "W"}({str a},{str b})"
  | .shift sf kd amt a => s!"sh{kd.toNat}{if sf then "" else "W"}({str a},{amt})"
  | .ext opt sh a => s!"ext{opt.toNat}({str a},{sh})"
  | .bfm sf opc immr imms d a => s!"bfm{opc.toNat}{if sf then "" else "W"}({immr.toNat},{imms.toNat},{str d},{str a})"
  | .lo32 a => s!"lo32({str a})"
  | .sext n a => s!"sext{n}({str a})"
  | .page a => s!"page({str a})"

/-- Whether the value reads general register `r` of the state before the Prog. -/
def reads (r : Nat) : Ex → Bool
  | .x q => q == r
  | .sp | .k _ | .sym _ => false
  | .ld _ a | .shift _ _ _ a | .ext _ _ a | .lo32 a | .sext _ a | .page a => reads r a
  | .add a b | .addSub _ _ a b | .logical _ _ a b | .bfm _ _ _ _ a b => reads r a || reads r b

/-- Whether every register the value reads is one of `X0`–`X30` but `X27` (the assembler's
scratch) and `X30` (the link register): the registers a P0 state and its machine state agree on. -/
def regsOK : Ex → Bool
  | .x r => r < 31 && r != 27 && r != 30
  | .sp | .k _ | .sym _ => true
  | .ld _ a | .shift _ _ _ a | .ext _ _ a | .lo32 a | .sext _ a | .page a => regsOK a
  | .add a b | .addSub _ _ a b | .logical _ _ a b | .bfm _ _ _ _ a b => regsOK a && regsOK b

/-! ### Smart constructors (constant folding and the canonical forms) -/

/-- `a + b`, constants folded and collected on the right. -/
def mkAdd (a b : Ex) : Ex :=
  match a, b with
  | .k u, .k v => .k (u + v)
  | a, .k 0 => a
  | .add a (.k u), .k v => if u + v = 0 then a else .add a (.k (u + v))
  | .k 0, b => b
  | a, b => .add a b

/-- `ProgOp.trunc sf a`. -/
def mkTrunc (sf : Bool) (a : Ex) : Ex :=
  if sf then a else
  match a with
  | .k v => .k (ProgOp.trunc false v)
  | .lo32 b => .lo32 b
  | a => .lo32 a

/-- An operand of an operation at the datasize `sf`: at 32 bits the operation reads the low
half only, so a `lo32` around it is dropped. -/
def opnd (sf : Bool) (a : Ex) : Ex :=
  if sf then a else match a with
    | .lo32 b => b
    | a => a

/-- `(addSub sf sub a b).1`: 64-bit `ADD`, and `SUB` of a constant, as `+`. -/
def mkAddSub (sf sub : Bool) (a b : Ex) : Ex :=
  let a := opnd sf a
  let b := opnd sf b
  match a, b with
  | .k u, .k v => .k (GoFV.Arm64.addSub sf sub u v).1
  | a, b =>
    if sf then
      if !sub then mkAdd a b
      else match b with
        | .k y => mkAdd a (.k (-y))
        | b => .addSub sf sub a b
    else .addSub sf sub a b

/-- `(logical sf opc a b).1`; `ORR` with zero is the other operand at the datasize. -/
def mkLogical (sf : Bool) (opc : BitVec 2) (a b : Ex) : Ex :=
  let a := opnd sf a
  let b := opnd sf b
  match a, b with
  | .k u, .k v => .k (GoFV.Arm64.logical sf opc u v).1
  | .k 0, b => if opc = 1 then mkTrunc sf b else .logical sf opc (.k 0) b
  | a, b => .logical sf opc a b

/-- `sized sf (Shift.apply (shiftOf k) · amt)`; by zero, the operand at the datasize. -/
def mkShift (sf : Bool) (kd : BitVec 2) (amt : Nat) (a : Ex) : Ex :=
  match a with
  | .k v => .k (sized sf fun _ e => Shift.apply (shiftOf kd) (e v) amt)
  | a => if amt = 0 then mkTrunc sf a else .shift sf kd amt a

/-- `extendReg a opt sh`; `UXTX #0` is the operand. -/
def mkExt (opt : BitVec 3) (sh : Nat) (a : Ex) : Ex :=
  match a with
  | .k v => .k (extendReg v opt sh)
  | a => if opt = 3 && sh = 0 then a else .ext opt sh a

/-- `bitfieldMove sf opc immr imms d a`; the destination's old value only matters for `BFM`. -/
def mkBfm (sf : Bool) (opc : BitVec 2) (immr imms : BitVec 6) (d a : Ex) : Ex :=
  let d := if opc = 1 then d else .k 0
  match d, a with
  | .k u, .k v => .k (bitfieldMove sf opc immr imms u v)
  | d, a => .bfm sf opc immr imms d a

/-- `sext n a`. -/
def mkSext (n : Nat) (a : Ex) : Ex :=
  match a with
  | .k v => .k (GoFV.SSA.Sem.Arm64.sext n v)
  | a => .sext n a

end Ex

/-! ## Flags -/

/-- The flags, symbolically. -/
inductive Fl where
  /-- The flags before the Prog. -/
  | init
  /-- `(addSub sf sub a b).2`. -/
  | addSub (sf sub : Bool) (a b : Ex)
  /-- `(logical sf 3 a b).2` (`ANDS`). -/
  | ands (sf : Bool) (a b : Ex)
  deriving DecidableEq, Repr, Inhabited

namespace Fl

def eval (c : Ctx) : Fl → Flags
  | .init => c.s.nzcv
  | .addSub sf sub a b => (GoFV.Arm64.addSub sf sub (a.eval c) (b.eval c)).2
  | .ands sf a b => (GoFV.Arm64.logical sf 3 (a.eval c) (b.eval c)).2

def reads (r : Nat) : Fl → Bool
  | .init => false
  | .addSub _ _ a b | .ands _ a b => a.reads r || b.reads r

/-- `Ex.regsOK` of the operands. -/
def regsOK : Fl → Bool
  | .init => true
  | .addSub _ _ a b | .ands _ a b => a.regsOK && b.regsOK

/-- `SUBS` of a nonzero constant `y` sets the flags `ADDS` of `-y` does (`CMP $-c` is encoded
as `CMN $c`); the canonical form is the `ADDS`. -/
def mkAddSub (sf sub : Bool) (a b : Ex) : Fl :=
  let a := Ex.opnd sf a
  let b := Ex.opnd sf b
  match sub, b with
  | true, .k y =>
    let y' := ProgOp.trunc sf y
    if y' ≠ 0 ∧ y' ≠ ProgOp.trunc sf (BitVec.ofNat 64 (if sf then 2 ^ 63 else 2 ^ 31)) then
      .addSub sf false a (.k (ProgOp.trunc sf (-y)))
    else .addSub sf true a b
  | false, .k y => .addSub sf false a (.k (ProgOp.trunc sf y))
  | _, b => .addSub sf sub a b

/-- `(logical sf 3 a b).2`. -/
def mkAnds (sf : Bool) (a b : Ex) : Fl := .ands sf (Ex.opnd sf a) (Ex.opnd sf b)

end Fl

/-! ## Symbolic states -/

/-- The effect of a Prog (or of the words encoded for it) so far, over the state before it:
general registers written (latest first), `SP`, the flags, the loads (latest first) and the
stores (in order: address, bytes, value; the value's low `8 n` bits are stored). -/
structure Sym where
  x : List (Nat × Ex) := []
  sp : Ex := .sp
  fl : Fl := .init
  loads : List (Ex × Nat) := []
  stores : List (Ex × Nat × Ex) := []
  deriving DecidableEq, Repr, Inhabited

namespace Sym

/-- General register `r` (`r ≤ 30`). -/
def getX (σ : Sym) (r : Nat) : Ex := (σ.x.lookup r).getD (.x r)

/-- `rX`: register 31 reads zero. -/
def rX (σ : Sym) (r : Nat) : Ex := if r = 31 then .k 0 else σ.getX r

/-- `rXsp`: register 31 is `SP`. -/
def rXsp (σ : Sym) (r : Nat) : Ex := if r = 31 then σ.sp else σ.getX r

/-- `wX`: a write to register 31 is dropped. -/
def wX (σ : Sym) (r : Nat) (v : Ex) : Sym := if r = 31 then σ else { σ with x := (r, v) :: σ.x }

/-- `wXsp`: register 31 is `SP`. -/
def wXsp (σ : Sym) (r : Nat) (v : Ex) : Sym := if r = 31 then { σ with sp := v } else σ.wX r v

/-- A load of `n` bytes at `a`: its value, recorded. Loads after a store are not modelled (the
symbolic value reads the memory before the Prog). -/
def load (σ : Sym) (a : Ex) (n : Nat) : Except String (Sym × Ex) :=
  if σ.stores.isEmpty then pure ({ σ with loads := (a, n) :: σ.loads }, .ld n a)
  else throw "load after a store"

def store (σ : Sym) (a : Ex) (n : Nat) (v : Ex) : Sym := { σ with stores := σ.stores ++ [(a, n, v)] }

end Sym

/-! ## The machine side -/

/-- Where the words of a Prog go after the last one. Offsets are from the start of the text. -/
inductive MCtl where
  | fall
  /-- `B`. -/
  | jmp (q : Int)
  /-- `B.cond` on the flags `fl`. -/
  | cond (fl : Fl) (c : BitVec 4) (q : Int)
  /-- `CBZ`/`CBNZ`. -/
  | cbz (sf nz : Bool) (a : Ex) (q : Int)
  /-- `TBZ`/`TBNZ`. -/
  | tbz (nz : Bool) (b : Nat) (a : Ex) (q : Int)
  /-- `BR`/`RET` to a register's value. -/
  | reg (a : Ex)
  /-- `BL` with an `R_CALLARM64` relocation: to symbol `n` plus `add`, `X30` the next word. -/
  | call (n : Nat) (add : Int)
  /-- `B` with an `R_CALLARM64` relocation (a tail call): to symbol `n` plus `add`. -/
  | jmpSym (n : Nat) (add : Int)
  deriving DecidableEq, Repr, Inhabited

/-- The word offset of a PC-relative branch immediate (`pcRel`). -/
def relOff {k : Nat} (o : Nat) (imm : BitVec k) : Int := o + 4 * imm.toInt

/-- `accessBytes` of an integer access. -/
def bytesOf (size : BitVec 2) : Nat := 2 ^ size.toNat

/-- The value an integer load of `n` bytes with `opc` writes (`loadInto`). -/
def loadVal (opc : BitVec 2) (n : Nat) (v : Ex) : Ex :=
  match opc.toNat with
  | 2 => Ex.mkSext (8 * n) v
  | 3 => Ex.mkTrunc false (Ex.mkSext (8 * n) v)
  | _ => v

/-- The address and base write-back of an integer single-register access (`amode`). -/
def amodeSym (σ : Sym) (mode : AMode) (rn : Nat) (n : Nat) : Ex × Option Ex :=
  let base := σ.rXsp rn
  match mode with
  | .uimm imm12 => (Ex.mkAdd base (.k (BitVec.ofNat 64 (imm12.toNat * n))), none)
  | .simm imm9 idx =>
    let off : BitVec 64 := imm9.signExtend 64
    match idx with
    | .unscaled => (Ex.mkAdd base (.k off), none)
    | .post => (base, some (Ex.mkAdd base (.k off)))
    | .pre => (Ex.mkAdd base (.k off), some (Ex.mkAdd base (.k off)))
  | .reg rm option sc =>
    (Ex.mkAdd base (Ex.mkExt option (if sc then Nat.log2 n else 0) (σ.rX rm.toNat)), none)

/-- The symbolic integer single-register access of `ldst` at address `a` (no write-back). -/
def symAccess (σ : Sym) (size : BitVec 2) (opc : BitVec 2) (rt : Nat) (a : Ex) :
    Except String Sym := do
  let n := bytesOf size
  if size = 3 && opc = 2 then throw "PRFM"
  if opc != 0 then
    let (σ, v) ← σ.load a n
    pure (σ.wX rt (loadVal opc n v))
  else pure (σ.store a n (σ.rX rt))

/-- The symbolic `exec` of one instruction at offset `o` (a word whose fields no relocation
patches). -/
def symInsn (i : Insn) (o : Nat) (σ : Sym) : Except String (Sym × MCtl) :=
  match i with
  | .addSubImm sf sub setf sh imm12 rn rd =>
    let x := σ.rXsp rn.toNat
    let y : Ex := .k (imm12.setWidth 64 <<< (if sh then 12 else 0))
    let r := Ex.mkAddSub sf sub x y
    if setf then pure ({ σ.wX rd.toNat r with fl := Fl.mkAddSub sf sub x y }, .fall)
    else pure (σ.wXsp rd.toNat r, .fall)
  | .logImm sf opc n immr imms rn rd =>
    match decodeBitMasks (if sf then 64 else 32) n imms immr true with
    | none => throw "logical immediate"
    | some (w, _) =>
      let x := σ.rX rn.toNat
      let y : Ex := .k (w.setWidth 64)
      let r := Ex.mkLogical sf opc x y
      if opc = 3 then pure ({ σ.wX rd.toNat r with fl := Fl.mkAnds sf x y }, .fall)
      else pure (σ.wXsp rd.toNat r, .fall)
  | .movWide sf opc hw imm16 rd =>
    let sh := 16 * hw.toNat
    match opc.toNat with
    | 0 => pure (σ.wX rd.toNat (.k (sized sf fun _ e => ~~~(e (imm16.setWidth 64 <<< sh)))), .fall)
    | 2 => pure (σ.wX rd.toNat (.k (imm16.setWidth 64 <<< sh)), .fall)
    | _ =>
      match σ.rX rd.toNat with
      | .k old =>
        pure (σ.wX rd.toNat (.k (sized sf fun _ e =>
          e ((old &&& ~~~((0xFFFF : BitVec 64) <<< sh)) ||| (imm16.setWidth 64 <<< sh)))), .fall)
      | _ => throw "MOVK of a non-constant register"
  | .bitfield sf opc immr imms rn rd =>
    pure (σ.wX rd.toNat (Ex.mkBfm sf opc immr imms (σ.rX rd.toNat) (σ.rX rn.toNat)), .fall)
  | .b link imm26 => if link then throw "BL without relocation" else pure (σ, .jmp (relOff o imm26))
  | .bcond c imm19 => pure (σ, .cond σ.fl c (relOff o imm19))
  | .cbz sf nz imm19 rt => pure (σ, .cbz sf nz (σ.rX rt.toNat) (relOff o imm19))
  | .tbz nz b imm14 rt => pure (σ, .tbz nz b.toNat (σ.rX rt.toNat) (relOff o imm14))
  | .br kind rn =>
    if kind = .blr then throw "BLR" else pure (σ, .reg (σ.rX rn.toNat))
  | .nop | .barrier .. => pure (σ, .fall)
  | .logShift sf opc shift n rm imm6 rn rd =>
    let y := Ex.mkShift sf shift imm6.toNat (σ.rX rm.toNat)
    if n then throw "logical shifted register with inversion" else
    let x := σ.rX rn.toNat
    let r := Ex.mkLogical sf opc x y
    if opc = 3 then pure ({ σ.wX rd.toNat r with fl := Fl.mkAnds sf x y }, .fall)
    else pure (σ.wX rd.toNat r, .fall)
  | .addSubShift sf sub setf shift rm imm6 rn rd =>
    let y := Ex.mkShift sf shift imm6.toNat (σ.rX rm.toNat)
    let x := σ.rX rn.toNat
    let r := Ex.mkAddSub sf sub x y
    if setf then pure ({ σ.wX rd.toNat r with fl := Fl.mkAddSub sf sub x y }, .fall)
    else pure (σ.wX rd.toNat r, .fall)
  | .addSubExt sf sub setf rm option imm3 rn rd =>
    let y := Ex.mkExt option imm3.toNat (σ.rX rm.toNat)
    let x := σ.rXsp rn.toNat
    let r := Ex.mkAddSub sf sub x y
    if setf then pure ({ σ.wX rd.toNat r with fl := Fl.mkAddSub sf sub x y }, .fall)
    else pure (σ.wXsp rd.toNat r, .fall)
  | .ldst size vec opc mode rn rt => do
    if vec then throw "SIMD&FP load/store"
    let (a, wb) := amodeSym σ mode rn.toNat (bytesOf size)
    let σ ← symAccess σ size opc rt.toNat a
    let σ := match wb with
      | some b => σ.wXsp rn.toNat b
      | none => σ
    pure (σ, .fall)
  | .ldstPair opc vec mode ld imm7 rt2 rn rt => do
    if vec then throw "SIMD&FP pair"
    let n := if opc.getLsbD 1 then 8 else 4
    let base := σ.rXsp rn.toNat
    let off : BitVec 64 := imm7.signExtend 64 * BitVec.ofNat 64 n
    let a := if mode = 1 then base else Ex.mkAdd base (.k off)
    let a2 := Ex.mkAdd a (.k (BitVec.ofNat 64 n))
    let σ' ← if ld then do
        let lopc : BitVec 2 := if opc = 1 then 2 else 1
        let (σ1, v1) ← σ.load a n
        let (σ2, v2) ← σ1.load a2 n
        pure ((σ2.wX rt.toNat (loadVal lopc n v1)).wX rt2.toNat (loadVal lopc n v2))
      else pure ((σ.store a n (σ.rX rt.toNat)).store a2 n (σ.rX rt2.toNat))
    let σ' := if mode = 2 then σ' else σ'.wXsp rn.toNat (Ex.mkAdd base (.k off))
    pure (σ', .fall)
  | i => throw s!"instruction not modelled: {i.form}"

end GoFV.Asm.CheckObj
