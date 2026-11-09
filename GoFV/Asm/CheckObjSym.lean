import GoFV.SSA.Sem.RunProg

variable [GoFV.SSA.Sem.Addrs]

/-!
# `checkObj`'s symbolic states (`docs/plans/proofs3.md` §2, row D4/D5; semantics3 §3 (c))

The assembler validator compares two descriptions of what one P0 Prog does: the Prog's own
effect (`progEffect`, in Go's operand conventions) and the effect of the machine words the
assembler encoded for it (`GoFV.Arm64.exec` of their decoded instructions). Both are computed
**symbolically**, as a `Sym`: the general registers written, `SP`, the flags, the loads, the
stores and the vector registers written, each value an `Ex` (64 bits) or a `VEx` (128 bits) over
the state *before* the Prog. Equal `Sym`s (with `X27`, the assembler's scratch, ignored) mean
equal effects on every state.

`Ex`'s operations are the data operations `exec` and `progEffect` share (`addSub`, `logical`,
`Shift.apply` through `sized`, `extendReg`, `bitfieldMove`, `sext`, `dp2Op`, loads), so the two
sides meet syntactically. Smart constructors (`Ex.add`, `Ex.mkAddSub`, …) fold constants and pick
one form for the identities the encodings need (`ORR Rd, ZR, Rm` is `Rm`, `ADD`/`SUB` of a
constant is `+`, …); `Ex.eval` gives the meaning, and each smart constructor is proven to
preserve it (`GoFV/Proof/Obj/`).

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
  /-- `dp1Op sf opc a` (`CLZ`, `RBIT`, `REV`, …). -/
  | dp1 (sf : Bool) (opc : BitVec 3) (a : Ex)
  /-- `dp2Op sf opc a b` (`UDIV`, `SDIV`, `LSLV`, `LSRV`, `ASRV`, `RORV`). -/
  | dp2 (sf : Bool) (opc : BitVec 6) (a b : Ex)
  /-- `sized sf fun _ e => ~~~(e a)`: the inverted operand of `BIC`/`ORN`/`EON` (`logShift`
  with `n`). -/
  | inv (sf : Bool) (a : Ex)
  /-- `dp3Op sf op31 o0 a x y` (`MADD`/`MSUB`, `UMULH`, `SMULH`). -/
  | dp3 (sf : Bool) (op31 : BitVec 3) (o0 : Bool) (a x y : Ex)
  /-- `cselVal sf op op2 h a b`, `h` whether condition `c` holds on the flags before the Prog
  (`CSEL`, `CSINC`, `CSINV`, `CSNEG`). -/
  | csel (sf op op2 : Bool) (c : BitVec 4) (a b : Ex)
  /-- The low `S`/`D` part of vector register `V r` (`r < 32`) before the Prog, zero-extended:
  `ft = 0` the low 32 bits, else the low 64 (`FMOV` to a general register, an `S`/`D` store). -/
  | vlo (ft : BitVec 2) (r : Nat)
  /-- `FCVTZS`/`FCVTZU` (`u`) of the `S` (`ft = 0`) or `D` part of `V r` before the Prog into
  `m` bits, zero-extended (`exec`'s `fcvtInt` with `rmode` 3). -/
  | fcvtz (ft : BitVec 2) (u : Bool) (m : Nat) (r : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The value of a conditional select (`condSel`): `x` at the datasize if `h`, else `y`
inverted (`op`) and incremented (`op2`) at the datasize. -/
def cselVal (sf op op2 h : Bool) (x y : BitVec 64) : BitVec 64 :=
  if h then sized sf fun _ e => e x
  else sized sf fun _ e =>
    let y := e y
    let y := if op then ~~~y else y
    if op2 then y + 1 else y

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
  | .dp1 sf opc a => dp1Op sf opc (eval c a)
  | .dp2 sf opc a b => dp2Op sf opc (eval c a) (eval c b)
  | .inv sf a => sized sf fun _ e => ~~~(e (eval c a))
  | .dp3 sf op31 o0 a b d => dp3Op sf op31 o0 (eval c a) (eval c b) (eval c d)
  | .csel sf op op2 cc a b => cselVal sf op op2 ((condOf cc).holds c.s.nzcv) (eval c a) (eval c b)
  | .vlo ft r =>
    if ft = 0 then ((c.s.v (BitVec.ofNat 5 r)).setWidth 32).setWidth 64
    else (c.s.v (BitVec.ofNat 5 r)).setWidth 64
  | .fcvtz ft u m r =>
    if ft = 0 then
      (GoFV.IEEE.toFixed .b32 ((c.s.v (BitVec.ofNat 5 r)).setWidth 32) u m .rz).setWidth 64
    else (GoFV.IEEE.toFixed .b64 ((c.s.v (BitVec.ofNat 5 r)).setWidth 64) u m .rz).setWidth 64

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
  | .dp1 sf opc a => s!"dp1_{opc.toNat}{if sf then "" else "W"}({str a})"
  | .dp2 sf opc a b => s!"dp2_{opc.toNat}{if sf then "" else "W"}({str a},{str b})"
  | .inv sf a => s!"inv{if sf then "" else "W"}({str a})"
  | .dp3 sf op31 o0 a b d =>
    s!"dp3_{op31.toNat}{if o0 then "S" else "A"}{if sf then "" else "W"}({str a},{str b},{str d})"
  | .csel sf op op2 cc a b =>
    s!"csel{if op then "I" else ""}{if op2 then "+" else ""}{if sf then "" else "W"}_{cc.toNat}({str a},{str b})"
  | .vlo ft r => s!"vlo{ft.toNat}(V{r})"
  | .fcvtz ft u m r => s!"fcvtz{if u then "U" else "S"}{ft.toNat}_{m}(V{r})"

/-- Whether the value reads general register `r` of the state before the Prog. -/
def reads (r : Nat) : Ex → Bool
  | .x q => q == r
  | .sp | .k _ | .sym _ | .vlo .. | .fcvtz .. => false
  | .ld _ a | .shift _ _ _ a | .ext _ _ a | .lo32 a | .sext _ a | .page a | .dp1 _ _ a
  | .inv _ a => reads r a
  | .add a b | .addSub _ _ a b | .logical _ _ a b | .bfm _ _ _ _ a b | .csel _ _ _ _ a b
  | .dp2 _ _ a b => reads r a || reads r b
  | .dp3 _ _ _ a b d => reads r a || reads r b || reads r d

/-- Whether every register the value reads is one of `X0`–`X30` but `X27` (the assembler's
scratch) and `X30` (the link register), or a vector register: the registers a P0 state and its
machine state agree on. -/
def regsOK : Ex → Bool
  | .x r => r < 31 && r != 27 && r != 30
  | .sp | .k _ | .sym _ | .vlo .. | .fcvtz .. => true
  | .ld _ a | .shift _ _ _ a | .ext _ _ a | .lo32 a | .sext _ a | .page a | .dp1 _ _ a
  | .inv _ a => regsOK a
  | .add a b | .addSub _ _ a b | .logical _ _ a b | .bfm _ _ _ _ a b | .csel _ _ _ _ a b
  | .dp2 _ _ a b => regsOK a && regsOK b
  | .dp3 _ _ _ a b d => regsOK a && regsOK b && regsOK d

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

/-- An operand of a `MADD`-type operation at the datasize `sf`: `opnd`, and a constant
truncated to it. -/
def opndK (sf : Bool) (a : Ex) : Ex :=
  match opnd sf a with
  | .k v => .k (ProgOp.trunc sf v)
  | a => a

/-- `dp3Op sf op31 o0 a x y`; the `MADD`/`MSUB` form (`op31` 0) reads its operands at the
datasize. -/
def mkDp3 (sf : Bool) (op31 : BitVec 3) (o0 : Bool) (a x y : Ex) : Ex :=
  if op31 = 0 then .dp3 sf 0 o0 (opndK sf a) (opndK sf x) (opndK sf y) else .dp3 sf op31 o0 a x y

/-- `dp2Op sf opc a b`: the operands at the datasize (`opndK`). -/
def mkDp2 (sf : Bool) (opc : BitVec 6) (a b : Ex) : Ex := .dp2 sf opc (opndK sf a) (opndK sf b)

/-- `sized sf fun _ e => ~~~(e a)`: the operand at the datasize (`opnd`), a constant folded. -/
def mkInv (sf : Bool) (a : Ex) : Ex :=
  match opnd sf a with
  | .k v => .k (sized sf fun _ e => ~~~(e v))
  | a => .inv sf a

end Ex

/-! ## Vector values -/

/-- A 128-bit vector register value, symbolically, over the state before a Prog (`eval`). -/
inductive VEx where
  /-- Vector register `V r` (`r < 32`). -/
  | v (r : Nat)
  | k (c : BitVec 128)
  /-- The low `w` bits of a general value, zero-extended (`FMOV` from a general register). -/
  | ofX (w : Nat) (a : Ex)
  /-- The `n` bytes at the address, zero-extended (the memory before the Prog). -/
  | ld (n : Nat) (a : Ex)
  /-- `fp1Op ft opc a`. -/
  | fp1 (ft : BitVec 2) (opc : BitVec 6) (a : VEx)
  /-- `fp2Op ft opc a b` (`Rn`, `Rm` order). -/
  | fp2 (ft : BitVec 2) (opc : BitVec 4) (a b : VEx)
  /-- `fp3Op ft o1 o0 a n m`. -/
  | fp3 (ft : BitVec 2) (o1 o0 : Bool) (a n m : VEx)
  /-- `FCSEL`: `a` if condition `c` holds on the flags before the Prog, else `b`, at the
  format `ft`. -/
  | fcsel (ft : BitVec 2) (c : BitVec 4) (a b : VEx)
  /-- `SCVTF`/`UCVTF` (`u`) of the low `m` bits of a general value to the format `ft`. -/
  | cvtf (ft : BitVec 2) (m : Nat) (u : Bool) (a : Ex)
  deriving DecidableEq, Repr, Inhabited

namespace VEx

/-- The meaning of a `VEx`. -/
def eval (c : Ctx) : VEx → BitVec 128
  | .v r => c.s.v (BitVec.ofNat 5 r)
  | .k w => w
  | .ofX w a => ((a.eval c).setWidth w).setWidth 128
  | .ld n a => (readMem c.s.mem (a.eval c) n).setWidth 128
  | .fp1 ft opc a => fp1Op ft opc (eval c a)
  | .fp2 ft opc a b => fp2Op ft opc (eval c a) (eval c b)
  | .fp3 ft o1 o0 a n m => fp3Op ft o1 o0 (eval c a) (eval c n) (eval c m)
  | .fcsel ft cc a b =>
    fpUn ft (fun _ x => x) (if (condOf cc).holds c.s.nzcv then eval c a else eval c b)
  | .cvtf ft m u a =>
    if ft = 0 then (GoFV.IEEE.fromFixed .b32 m ((a.eval c).setWidth m) u .rne).setWidth 128
    else (GoFV.IEEE.fromFixed .b64 m ((a.eval c).setWidth m) u .rne).setWidth 128

/-- A short rendering for rejection messages. -/
def str : VEx → String
  | .v r => s!"V{r}"
  | .k w => w.toHex
  | .ofX w a => s!"ofX{w}({a.str})"
  | .ld n a => s!"vld{n}({a.str})"
  | .fp1 ft opc a => s!"fp1_{opc.toNat}_{ft.toNat}({str a})"
  | .fp2 ft opc a b => s!"fp2_{opc.toNat}_{ft.toNat}({str a},{str b})"
  | .fp3 ft o1 o0 a n m => s!"fp3_{o1}{o0}_{ft.toNat}({str a},{str n},{str m})"
  | .fcsel ft cc a b => s!"fcsel{ft.toNat}_{cc.toNat}({str a},{str b})"
  | .cvtf ft m u a => s!"cvtf{if u then "U" else "S"}{ft.toNat}_{m}({a.str})"

/-- Whether the value reads general register `r` of the state before the Prog (`Ex.reads` of
its `Ex` leaves). -/
def reads (r : Nat) : VEx → Bool
  | .v _ | .k _ => false
  | .ofX _ a | .ld _ a | .cvtf _ _ _ a => a.reads r
  | .fp1 _ _ a => reads r a
  | .fp2 _ _ a b | .fcsel _ _ a b => reads r a || reads r b
  | .fp3 _ _ _ a n m => reads r a || reads r n || reads r m

/-- `Ex.regsOK` of its `Ex` leaves. -/
def regsOK : VEx → Bool
  | .v _ | .k _ => true
  | .ofX _ a | .ld _ a | .cvtf _ _ _ a => a.regsOK
  | .fp1 _ _ a => regsOK a
  | .fp2 _ _ a b | .fcsel _ _ a b => regsOK a && regsOK b
  | .fp3 _ _ _ a n m => regsOK a && regsOK n && regsOK m

/-- `ofX w a`, a constant folded (`FMOV` from `ZR`, the encoding of the `FCONST` `0.0`, is the
constant `0`). -/
def mkOfX (w : Nat) (a : Ex) : VEx :=
  match a with
  | .k x => .k ((x.setWidth w).setWidth 128)
  | a => .ofX w a

end VEx

/-! ## Flags -/

/-- The flags, symbolically. -/
inductive Fl where
  /-- The flags before the Prog. -/
  | init
  /-- `(addSub sf sub a b).2`. -/
  | addSub (sf sub : Bool) (a b : Ex)
  /-- `(logical sf 3 a b).2` (`ANDS`). -/
  | ands (sf : Bool) (a b : Ex)
  /-- `fcmpOp ft a b` (`FCMP`; the zero form compares with `.k 0`). -/
  | fcmp (ft : BitVec 2) (a b : VEx)
  deriving DecidableEq, Repr, Inhabited

namespace Fl

def eval (c : Ctx) : Fl → Flags
  | .init => c.s.nzcv
  | .addSub sf sub a b => (GoFV.Arm64.addSub sf sub (a.eval c) (b.eval c)).2
  | .ands sf a b => (GoFV.Arm64.logical sf 3 (a.eval c) (b.eval c)).2
  | .fcmp ft a b => fcmpOp ft (a.eval c) (b.eval c)

def reads (r : Nat) : Fl → Bool
  | .init => false
  | .addSub _ _ a b | .ands _ a b => a.reads r || b.reads r
  | .fcmp _ a b => a.reads r || b.reads r

/-- `Ex.regsOK` of the operands. -/
def regsOK : Fl → Bool
  | .init => true
  | .addSub _ _ a b | .ands _ a b => a.regsOK && b.regsOK
  | .fcmp _ a b => a.regsOK && b.regsOK

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
general registers written (latest first), `SP`, the flags, the loads (latest first), the
stores (in order: address, bytes, value; the value's low `8 n` bits are stored) and the vector
registers written (latest first). -/
structure Sym where
  x : List (Nat × Ex) := []
  sp : Ex := .sp
  fl : Fl := .init
  loads : List (Ex × Nat) := []
  stores : List (Ex × Nat × Ex) := []
  v : List (Nat × VEx) := []
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

/-- Vector register `r` (`r < 32`). -/
def getV (σ : Sym) (r : Nat) : VEx := (σ.v.lookup r).getD (.v r)

/-- A write of vector register `r`. -/
def wV (σ : Sym) (r : Nat) (e : VEx) : Sym := { σ with v := (r, e) :: σ.v }

/-- `e`, a value reading `V r` before the Prog (`Ex.vlo`, `Ex.fcvtz`), while the effect has not
written `V r`. -/
def vEx (σ : Sym) (r : Nat) (e : Ex) : Except String Ex :=
  if (σ.v.lookup r).isNone then pure e else throw "V register read after write"

/-- The vector registers after the effect, over `c`: the latest write's value, else the
register before the Prog. -/
def evalV (σ : Sym) (c : Ctx) : Reg → BitVec 128 :=
  fun r => ((σ.v.lookup r.toNat).map (·.eval c)).getD (c.s.v r)

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
  /-- `BLR` to a register's value, `X30` the next word. -/
  | callReg (a : Ex)
  deriving DecidableEq, Repr, Inhabited

/-- Whether the control writes `X30` (a call). -/
def MCtl.links : MCtl → Bool
  | .call .. | .callReg _ => true
  | _ => false

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

/-- The symbolic `execExcl` (`LDAR*`/`LDAXR*`, and the ordered store `STLR*`; an exclusive
store, which writes its status register, is not modelled). -/
def symExcl (σ : Sym) (size : BitVec 2) (o2 ld : Bool) (rn rt : Reg) : Except String (Sym × MCtl) :=
  if ld then
    match σ.load (σ.rXsp rn.toNat) (bytesOf size) with
    | .ok (σ1, v) => pure (σ1.wX rt.toNat v, .fall)
    | .error e => throw e
  else if o2 then pure (σ.store (σ.rXsp rn.toNat) (bytesOf size) (σ.rX rt.toNat), .fall)
  else throw "store exclusive"

/-- The symbolic `condSel`: the condition on the flags before the Prog. -/
def symCsel (σ : Sym) (sf op op2 : Bool) (rm : Reg) (cond : BitVec 4) (rn rd : Reg) :
    Except String (Sym × MCtl) :=
  if σ.fl = .init then
    pure (σ.wX rd.toNat (.csel sf op op2 cond (σ.rX rn.toNat) (σ.rX rm.toNat)), .fall)
  else throw "conditional select on flags set by the words"

/-! ### SIMD&FP -/

/-- The format of an `S`/`D` store's value (`Ex.vlo`): 4 bytes the low 32 bits, 8 the low 64; a
store of another size (a `B`/`H` or `Q` register) is not modelled. -/
def vStoreFt (n : Nat) : Except String (BitVec 2) :=
  if n = 4 then pure 0 else if n = 8 then pure 1 else throw "SIMD&FP store of other than 4 or 8 bytes"

/-- The symbolic SIMD&FP single-register access of `ldst` at address `a` (no write-back): a load
writes `V rt` (`VEx.ld`), a store stores the low part of `V rt` before the Prog. -/
def symVAccess (σ : Sym) (size opc : BitVec 2) (rt : Nat) (a : Ex) : Except String Sym := do
  let n := accessBytes size true opc
  if opc.getLsbD 0 then
    let (σ, _) ← σ.load a n
    pure (σ.wV rt (.ld n a))
  else
    let ft ← vStoreFt n
    let v ← σ.vEx rt (.vlo ft rt)
    pure (σ.store a n v)

/-- The symbolic SIMD&FP `ldstPair` (`LDP`/`STP` of `S`, `D`, `Q`; `Q` stores not modelled). -/
def symVPair (σ : Sym) (opc mode : BitVec 2) (ld : Bool) (imm7 : BitVec 7) (rt2 rn rt : Reg) :
    Except String Sym := do
  let n := 4 * 2 ^ opc.toNat
  let base := σ.rXsp rn.toNat
  let off : BitVec 64 := imm7.signExtend 64 * BitVec.ofNat 64 n
  let a := if mode = 1 then base else Ex.mkAdd base (.k off)
  let a2 := Ex.mkAdd a (.k (BitVec.ofNat 64 n))
  let σ' ← if ld then do
      let (σ1, _) ← σ.load a n
      let (σ2, _) ← σ1.load a2 n
      pure ((σ2.wV rt.toNat (.ld n a)).wV rt2.toNat (.ld n a2))
    else do
      let ft ← vStoreFt n
      let v1 ← σ.vEx rt.toNat (.vlo ft rt.toNat)
      let v2 ← σ.vEx rt2.toNat (.vlo ft rt2.toNat)
      pure ((σ.store a n v1).store a2 n v2)
  pure (if mode = 2 then σ' else σ'.wXsp rn.toNat (Ex.mkAdd base (.k off)))

/-- The symbolic `FCSEL`: the condition on the flags before the Prog. -/
def symFcsel (σ : Sym) (ft : BitVec 2) (rm : Reg) (cond : BitVec 4) (rn rd : Reg) :
    Except String Sym :=
  if σ.fl = .init then
    pure (σ.wV rd.toNat (.fcsel ft cond (σ.getV rn.toNat) (σ.getV rm.toNat)))
  else throw "FCSEL on flags set by the words"

/-- The symbolic `fcvtInt` (`FMOV` between general and SIMD&FP registers, `SCVTF`/`UCVTF`,
`FCVTZS`/`FCVTZU`). -/
def symFcvt (σ : Sym) (sf : Bool) (ft rmode : BitVec 2) (opc : BitVec 3) (rn rd : Reg) :
    Except String Sym :=
  let m := if sf then 64 else 32
  match rmode.toNat, opc.toNat with
  | 0, 6 => do
    let e ← σ.vEx rn.toNat (.vlo ft rn.toNat)
    pure (σ.wX rd.toNat e)
  | 0, 7 =>
    pure (σ.wV rd.toNat
      (if ft = 0 then VEx.mkOfX 32 (σ.rX rn.toNat) else VEx.mkOfX 64 (σ.rX rn.toNat)))
  | 0, 2 => pure (σ.wV rd.toNat (.cvtf ft m false (σ.rX rn.toNat)))
  | 0, 3 => pure (σ.wV rd.toNat (.cvtf ft m true (σ.rX rn.toNat)))
  | 3, 0 => do
    let e ← σ.vEx rn.toNat (.fcvtz ft false m rn.toNat)
    pure (σ.wX rd.toNat e)
  | 3, 1 => do
    let e ← σ.vEx rn.toNat (.fcvtz ft true m rn.toNat)
    pure (σ.wX rd.toNat e)
  | _, _ => throw s!"instruction not modelled: {(Insn.fcvtInt sf ft rmode opc rn rd).form}"

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
    if kind = .blr then pure (σ, .callReg (σ.rX rn.toNat)) else pure (σ, .reg (σ.rX rn.toNat))
  | .condSel sf op op2 rm cond rn rd => symCsel σ sf op op2 rm cond rn rd
  | .dp1 sf opc rn rd => pure (σ.wX rd.toNat (.dp1 sf opc (σ.rX rn.toNat)), .fall)
  | .dp2 sf opc rm rn rd =>
    pure (σ.wX rd.toNat (Ex.mkDp2 sf opc (σ.rX rn.toNat) (σ.rX rm.toNat)), .fall)
  | .dp3 sf op31 o0 rm ra rn rd =>
    pure (σ.wX rd.toNat (Ex.mkDp3 sf op31 o0 (σ.rX ra.toNat) (σ.rX rn.toNat) (σ.rX rm.toNat)), .fall)
  | .ldstExcl size o2 ld _ _ rn rt => symExcl σ size o2 ld rn rt
  | .nop | .barrier .. => pure (σ, .fall)
  | .logShift sf opc shift n rm imm6 rn rd =>
    let y := Ex.mkShift sf shift imm6.toNat (σ.rX rm.toNat)
    let y := if n then Ex.mkInv sf y else y
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
  | .ldst size true opc mode rn rt => do
    let (a, wb) := amodeSym σ mode rn.toNat (accessBytes size true opc)
    let σ ← symVAccess σ size opc rt.toNat a
    let σ := match wb with
      | some b => σ.wXsp rn.toNat b
      | none => σ
    pure (σ, .fall)
  | .ldst size false opc mode rn rt => do
    let (a, wb) := amodeSym σ mode rn.toNat (bytesOf size)
    let σ ← symAccess σ size opc rt.toNat a
    let σ := match wb with
      | some b => σ.wXsp rn.toNat b
      | none => σ
    pure (σ, .fall)
  | .ldstPair opc true mode ld imm7 rt2 rn rt => do
    let σ ← symVPair σ opc mode ld imm7 rt2 rn rt
    pure (σ, .fall)
  | .ldstPair opc false mode ld imm7 rt2 rn rt => do
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
  | .fp1 ft opc rn rd => pure (σ.wV rd.toNat (.fp1 ft opc (σ.getV rn.toNat)), .fall)
  | .fp2 ft opc rm rn rd =>
    pure (σ.wV rd.toNat (.fp2 ft opc (σ.getV rn.toNat) (σ.getV rm.toNat)), .fall)
  | .fp3 ft o1 o0 rm ra rn rd =>
    pure (σ.wV rd.toNat
      (.fp3 ft o1 o0 (σ.getV ra.toNat) (σ.getV rn.toNat) (σ.getV rm.toNat)), .fall)
  | .fcmp ft rm rn zero _ =>
    pure ({ σ with fl := .fcmp ft (σ.getV rn.toNat) (if zero then .k 0 else σ.getV rm.toNat) },
      .fall)
  | .fmovImm ft imm8 rd => pure (σ.wV rd.toNat (.k (vfpExpandImm ft imm8)), .fall)
  | .fcsel ft rm cond rn rd => do
    let σ ← symFcsel σ ft rm cond rn rd
    pure (σ, .fall)
  | .fcvtInt sf ft rmode opc rn rd => do
    let σ ← symFcvt σ sf ft rmode opc rn rd
    pure (σ, .fall)
  | i => throw s!"instruction not modelled: {i.form}"

end GoFV.Asm.CheckObj
