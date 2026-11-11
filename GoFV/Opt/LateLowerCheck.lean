import GoFV.Opt.Lower
import GoFV.Opt.LowerCheck
import GoFV.Proof.CongL

variable [GoFV.SSA.Sem.Addrs]

/-!
# The checked `late lower` (`lateB`, issue #385)

`late lower` (`GoFV.Opt.lateLower`, `ARM64latelower.rules`) rewrites lowered values in place and
materializes immediates. `lateB tabs tabs' f g` accepts `g` (with tables `tabs'`) for `f` (with
tables `tabs`, agreeing with `tabs'` for `f`, `tabsAgreeL`) when `g` is `f` with

* some values rewritten in place (same ID and type; `rwOK`), each by one of
  - `(MOVDreg x) => (MOVDnop x)` (line 91; `arm64Op` has one arm for both: `rw91`),
  - `(MOVDconst [0]) => (ZERO)` (line 98; both the word 0: `rw98`),
  - `(SLLconst [1] x) => (ADD x x)` (line 103; `rw103`),
  - an extension of a producer whose register already holds it dropped to `MOVDreg`/`MOVDnop`
    (lines 35-87, then 91: `rwExt`): the producer (`prodSig`: a narrow load, indexed or not, or
    an extension) leaves the low `kP` bits sign- or zero-extended, and the extension (`extSig`)
    then changes nothing (`dropOK`, also on the producer's lowered shape, whose upper bits the
    register reading `Arm64.reg` zero-extends),
  - an immediate op made a register op of a new constant (lines 8-21: `rwImm`, `immOf`):
    `(OPconst [c] x) => (OP x (MOVDconst [c]))`;
* new values (an ID `f` does not use) that are `MOVDconst`s without arguments (`freshK`: at
  the 64-bit integer shape and `c` for the one an immediate rewrite reads), listed in a block of
  `g` before the values that read them (`freshBefore`);

and otherwise unchanged: the same values (up to positions and use counts) whose arguments are
values of `f`, the same blocks up to positions, predictions and the new constants in their value
lists, `runL`'s order (`Sem.schedule`) of each block of `g` that of `f` with the new constants
interleaved, and every `MOVDreg`/`MOVDnop` of `g` reads whether its argument sign-extends as in
`f` (`sxOK`). Then `g` runs as `f` (`GoFV.Proof.LateLowerL.lateLower_refinesL`). Sections where
any other rule fires (the copies of lines 29 and 32, line 95) are rejected.
-/

namespace GoFV.Opt.LateLowerCheck

open GoFV.SSA GoFV.SSA.Sem

/-! ## Extensions -/

/-- The producers and the extension their result register holds, `(signed, bits)`: the low
`bits` bits sign- or zero-extended (`Arm64.loadN`, `Arm64.loadIdx`, `Arm64.ext`). -/
def prodOps : List (Op × Bool × Nat) :=
  [(.ARM64MOVBload, true, 8), (.ARM64MOVBUload, false, 8), (.ARM64MOVHload, true, 16),
   (.ARM64MOVHUload, false, 16), (.ARM64MOVWload, true, 32), (.ARM64MOVWUload, false, 32),
   (.ARM64MOVBloadidx, true, 8), (.ARM64MOVBUloadidx, false, 8), (.ARM64MOVHloadidx, true, 16),
   (.ARM64MOVHUloadidx, false, 16), (.ARM64MOVHloadidx2, true, 16),
   (.ARM64MOVHUloadidx2, false, 16), (.ARM64MOVWloadidx, true, 32),
   (.ARM64MOVWUloadidx, false, 32), (.ARM64MOVWloadidx4, true, 32),
   (.ARM64MOVWUloadidx4, false, 32),
   (.ARM64MOVBreg, true, 8), (.ARM64MOVBUreg, false, 8), (.ARM64MOVHreg, true, 16),
   (.ARM64MOVHUreg, false, 16), (.ARM64MOVWreg, true, 32), (.ARM64MOVWUreg, false, 32)]

/-- The extension `prodOps` gives a producer. -/
def prodSig (o : Op) : Option (Bool × Nat) := (prodOps.find? (·.1 == o)).map (·.2)

/-- The extension ops, `(signed, bits)` (`Arm64.evalPure`: `op1 ty (ext signed bits)`). -/
def extOps : List (Op × Bool × Nat) :=
  [(.ARM64MOVBreg, true, 8), (.ARM64MOVBUreg, false, 8), (.ARM64MOVHreg, true, 16),
   (.ARM64MOVHUreg, false, 16), (.ARM64MOVWreg, true, 32), (.ARM64MOVWUreg, false, 32)]

/-- The extension `extOps` gives an op. -/
def extSig (o : Op) : Option (Bool × Nat) := (extOps.find? (·.1 == o)).map (·.2)

/-- An extension `(sE, kE)` of a producer `(sP, kP)` read at shape `t` changes nothing: at an
integer shape of `w` bits the register holds the low `w` bits zero-extended, so `w` keeps the
producer's bits (and, for a signed producer, the extension's); a signed producer's value is
unchanged by a signed extension of at least `kP` bits, an unsigned one's by an unsigned
extension of at least `kP` bits or a signed one of more. -/
def dropOK (sP : Bool) (kP : Nat) (sE : Bool) (kE : Nat) (t : Ty) : Bool :=
  (match t with
    | .int w => decide (kP ≤ w.bits) && (!sP || decide (kE ≤ w.bits))
    | _ => true) &&
  (if sP then sE && decide (kP ≤ kE) else if sE then decide (kP < kE) else decide (kP ≤ kE))

/-- The immediate ops and their register ops (`ARM64latelower.rules:8-21`). -/
def immOps : List (Op × Op) :=
  [(.ARM64ADDconst, .ARM64ADD), (.ARM64SUBconst, .ARM64SUB), (.ARM64ANDconst, .ARM64AND),
   (.ARM64ORconst, .ARM64OR), (.ARM64XORconst, .ARM64XOR), (.ARM64TSTconst, .ARM64TST),
   (.ARM64TSTWconst, .ARM64TSTW), (.ARM64CMPconst, .ARM64CMP), (.ARM64CMPWconst, .ARM64CMPW),
   (.ARM64CMNconst, .ARM64CMN), (.ARM64CMNWconst, .ARM64CMNW),
   (.ARM64ADDSconstflags, .ARM64ADDSflags)]

/-- The register op `immOps` gives an immediate op. -/
def immOf (o : Op) : Option Op := (immOps.find? (·.1 == o)).map (·.2)

/-! ## Values -/

/-- Value `a` is a value of `f`. -/
@[inline] def inF (f : Func) (a : ID) : Bool := (f.value? a).isSome

/-- The shape is the 64-bit integer one. -/
def isW64 : Option Ty → Bool
  | some (.int .w64) => true
  | _ => false

/-- `c` is a new constant of `g` with auxint `k` at the 64-bit integer shape (`tysG`: `g`'s
lowered shapes). -/
def freshK (tysG : Array Ty) (f g : Func) (c : ID) (k : Int64) : Bool :=
  !inF f c && isW64 tysG[c]? &&
    match g.value? c with
    | some w => w.op == .ARM64MOVDconst && w.args.isEmpty && w.auxInt == k
    | none => false

/-- Line 91. -/
def rw91 (f : Func) (u w : Value) : Bool :=
  u.op == .ARM64MOVDreg && w.op == .ARM64MOVDnop && w.args == u.args && u.args.all (inF f)

/-- Line 98. -/
def rw98 (u w : Value) : Bool :=
  u.op == .ARM64MOVDconst && u.auxInt == 0 && w.op == .ARM64ZERO && u.args.isEmpty &&
    w.args.isEmpty

/-- Line 103. -/
def rw103 (f : Func) (u w : Value) : Bool :=
  u.op == .ARM64SLLconst && u.auxInt == 1 && w.op == .ARM64ADD &&
    match u.args.toList with
    | [x] => w.args == #[x, x] && inF f x
    | _ => false

/-- Lines 35-87 (then 91): an extension of a producer whose register holds it (`tysF`: `f`'s
lowered shapes). -/
def rwExt (tysF : Array Ty) (f : Func) (u w : Value) : Bool :=
  (w.op == .ARM64MOVDreg || w.op == .ARM64MOVDnop) &&
    match u.args.toList with
    | [x] => w.args == #[x] &&
      match extSig u.op, (f.value? x).bind (prodSig ·.op) with
      | some (sE, kE), some (sP, kP) => dropOK sP kP sE kE (tysF[x]?.getD .other)
      | _, _ => false
    | _ => false

/-- Lines 8-21: an immediate op made the register op of a new constant. -/
def rwImm (tysG : Array Ty) (f g : Func) (u w : Value) : Bool :=
  (immOf u.op).any (· == w.op) &&
    match u.args.toList, w.args.toList with
    | [x], [x', c] => x' == x && inF f x && freshK tysG f g c u.auxInt
    | _, _ => false

/-- `w` is `late lower`'s rewrite of `u`. -/
def rwOK (tysF tysG : Array Ty) (f g : Func) (u w : Value) : Bool :=
  rw91 f u w || rw98 u w || rw103 f u w || rwExt tysF f u w || rwImm tysG f g u w

/-! ## Removed extensions (line 29) -/

/-- Value `a` of `f` is gone from `g`. -/
@[inline] def gone (f g : Func) (a : ID) : Bool := inF f a && !inF g a

/-- The condition ops (`CSET`s) of line 29. -/
def condOps : List Op :=
  [.ARM64Equal, .ARM64NotEqual, .ARM64LessThan, .ARM64LessThanU, .ARM64LessThanF,
   .ARM64LessEqual, .ARM64LessEqualU, .ARM64LessEqualF, .ARM64GreaterThan, .ARM64GreaterThanU,
   .ARM64GreaterThanF, .ARM64GreaterEqual, .ARM64GreaterEqualU, .ARM64GreaterEqualF]

/-- The shape is an integer one. -/
def isInt : Option Ty → Bool
  | some (.int _) => true
  | _ => false

/-- The shape is `bool`. -/
def isBool : Option Ty → Bool
  | some .bool => true
  | _ => false

/-- The first argument of value `a` of `f` (for a gone value: the `x` its users read in `g`). -/
def base (f : Func) (a : ID) : Option ID := (f.value? a).bind (·.args[0]?)

/-- Line 29, `(MOVBUreg x:(Equal|NotEqual|…|GreaterEqualF _)) => x`: `u` (gone from `g`) is the
`MOVBUreg`, at an integer shape, of a condition op `x` of `g` at the `bool` shape. -/
def rw29 (tysF : Array Ty) (f g : Func) (u : Value) : Bool :=
  u.op == .ARM64MOVBUreg && isInt tysF[u.id]? &&
    match u.args.toList with
    | [x] => inF g x && isBool tysF[x]? &&
      ((f.value? x).map fun v => condOps.contains v.op).getD false
    | _ => false

/-- The pure ops that read every argument as its register (`Arm64.op1`, `op2`, `opSh`, `add`,
`sub`, `addSh`, `subSh`, `addK`), where a `bool` reads as the integer 0 or 1. -/
def regOps : List Op :=
  [.ARM64ADD, .ARM64ADDconst, .ARM64SUB, .ARM64SUBconst, .ARM64MUL, .ARM64NEG, .ARM64MVN,
   .ARM64AND, .ARM64ANDconst, .ARM64OR, .ARM64ORconst, .ARM64XOR, .ARM64XORconst, .ARM64BIC,
   .ARM64EON, .ARM64ORN, .ARM64SLL, .ARM64SRL, .ARM64SRA, .ARM64SLLconst, .ARM64SRLconst,
   .ARM64SRAconst, .ARM64ADDshiftLL, .ARM64ADDshiftRL, .ARM64ADDshiftRA, .ARM64SUBshiftLL,
   .ARM64SUBshiftRL, .ARM64SUBshiftRA, .ARM64ANDshiftLL, .ARM64ANDshiftRL, .ARM64ANDshiftRA,
   .ARM64ORshiftLL, .ARM64ORshiftRL, .ARM64ORshiftRA, .ARM64XORshiftLL, .ARM64XORshiftRL,
   .ARM64XORshiftRA, .ARM64BICshiftLL, .ARM64BICshiftRL, .ARM64BICshiftRA, .ARM64MOVBreg,
   .ARM64MOVBUreg, .ARM64MOVHreg, .ARM64MOVHUreg, .ARM64MOVWreg, .ARM64MOVWUreg]

/-- The stores whose stored value (argument 1) is the low bytes of its register
(`Arm64.storeBytes`). -/
def stOps : List Op := [.ARM64MOVBstore, .ARM64MOVHstore, .ARM64MOVWstore, .ARM64MOVDstore]

/-- `u` reads its argument `j` as a register: a `regOps` op, a stored value, or a `Phi` at an
integer shape (it reads its argument at its shape, `Val.widen` zero-extends a `bool`). -/
def regPos (tysF : Array Ty) (u : Value) (j : Nat) : Bool :=
  regOps.contains u.op || (stOps.contains u.op && j == 1) ||
    (u.op == .Phi && isInt tysF[u.id]?)

/-- Argument `j` of `w` (`b`) is `u`'s (`a`), a value of both, or `u`'s is gone and `w` reads its
`x` instead, as a register. -/
def argOK (tysF : Array Ty) (f g : Func) (u : Value) (j : Nat) (a b : ID) : Bool :=
  (a == b && inF f a && inF g a) || (gone f g a && base f a == some b && regPos tysF u j)

/-- The arguments of `w` are `u`'s, up to gone ones (`argOK`). -/
def argsOK (tysF : Array Ty) (f g : Func) (u w : Value) : Bool :=
  w.args.size == u.args.size &&
    (List.range u.args.size).all fun j =>
      match u.args[j]?, w.args[j]? with
      | some a, some b => argOK tysF f g u j a b
      | _, _ => false

/-- Value `i` of `g` is `f`'s (with ID `i`, up to gone arguments), `f`'s rewritten, or a new
constant; a value of `f` gone from `g` is line 29's. -/
def valOK (tysF tysG : Array Ty) (f g : Func) (i : ID) : Bool :=
  match f.value? i, g.value? i with
  | none, none => true
  | none, some w => w.op == .ARM64MOVDconst && w.args.isEmpty && w.id == i
  | some u, none => u.id == i && rw29 tysF f g u
  | some u, some w =>
    u.id == i && w.id == u.id && w.type == u.type &&
      ((w.op == u.op && w.aux == u.aux && w.auxInt == u.auxInt && argsOK tysF f g u w) ||
        (u.op != .Phi && u.args.all (inF g) && rwOK tysF tysG f g u w))

/-- Whether the first argument of `v` sign-extends in `f` (`arm64Op`'s `MOVDreg`/`MOVDnop`). -/
def sxIn (f : Func) (v : Value) : Option Bool :=
  (v.args[0]?.bind f.value?).map (Arm64.signExtendsIn f.value?)

/-- Every `MOVDreg`/`MOVDnop` of `g` reads whether its argument sign-extends as in `f`. -/
def sxOK (f g : Func) : Bool :=
  g.valueTab.all fun
    | some w => !(w.op == .ARM64MOVDreg || w.op == .ARM64MOVDnop) || sxIn g w == sxIn f w
    | none => true

/-! ## Blocks -/

/-- The new constants a value of the order reads come before it (`seen`: the values before). -/
def freshBefore (f g : Func) : List ID → List ID → Bool
  | _, [] => true
  | seen, x :: xs =>
    ((g.value? x).map fun w => w.args.all fun a => inF f a || seen.contains a).getD true &&
      freshBefore f g (x :: seen) xs

/-- The values of `f` gone from `g` (line 29's `MOVBUreg`s). -/
def goneL (f g : Func) : List ID := (List.range f.valueTab.size).filter (gone f g)

/-- Along `f`'s order of a block (`gs`: `goneL`), a gone value is read (by a value of `g`, which
reads its `x`) only while `x` holds the value it was computed from, and not by a `Phi`. `W` is
the gone values whose `x` ran after them (from this block on: running `x` opens its gone
values, running one closes it); no reader reads one of `W`, and the block ends with `W` empty. -/
def winOK (f g : Func) (gs : List ID) : List ID → List ID → Bool
  | W, [] => W.isEmpty
  | W, y :: ys =>
    if inF g y then
      ((f.value? y).map fun u =>
          u.args.all fun a => !gone f g a || (u.op != .Phi && !W.contains a)).getD true &&
        winOK f g gs (W ++ gs.filter fun v => base f v == some y) ys
    else winOK f g gs (W.filter (· != y)) ys

/-- Block `b` of `g` is `f`'s up to position, prediction, the new constants of its values (values
of `g`) and the gone values of `f`'s, its controls are values of both, and its `runL` order is
`f`'s without the gone values and with the new constants interleaved, each before its readers;
the gone values are read while their `x` holds what they were computed from (`winOK`). -/
def blkOK (f g : Func) (gs : List ID) (b : ID) : Bool :=
  match f.block? b, g.block? b with
  | none, none => true
  | some fb, some gb =>
    decide ({ gb with values := fb.values, pos := fb.pos, likely := fb.likely } = fb) &&
      gb.values.toList.filter (inF f) == fb.values.toList.filter (inF g) &&
      fb.values.all (inF f) && gb.values.all (fun x => (g.value? x).isSome) &&
      fb.controls.all (fun c => inF f c && inF g c) &&
      match schedule f fb, schedule g gb with
      | some oS, some oT =>
        oT.toList.filter (inF f) == oS.toList.filter (inF g) && oS.all (inF f) &&
          oT.all (fun x => (g.value? x).isSome) && freshBefore f g [] oT.toList &&
          winOK f g gs [] oS.toList
      | _, _ => false
  | _, _ => false

/-! ## The validator -/

/-- `f`'s lowered shapes in `tabs` (`Ctx.makeL`'s, for a lowered `f`). -/
def shapesL (tabs : Tables) (f : Func) : Array Ty := f.valueTab.map (valueTy (typeShapesL tabs))

/-- **The `late lower` validator** (module doc). -/
def lateB (tabs tabs' : Tables) (f g : Func) : Bool :=
  LowerCheck.tabsAgreeL tabs tabs' f && f.lowered && g.lowered && g.entry == f.entry &&
    g.ownAux == f.ownAux && g.blockTab.size == f.blockTab.size &&
    (let tysF := shapesL tabs' f
     let tysG := shapesL tabs' g
     (List.range (max f.valueTab.size g.valueTab.size)).all (valOK tysF tysG f g)) &&
    (let gs := goneL f g
     (List.range f.blockTab.size).all (blkOK f g gs)) && sxOK f g

end GoFV.Opt.LateLowerCheck
