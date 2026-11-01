import GoFV.Opt.KnownBits
import GoFV.Opt.RewriteCheck
import GoFV.Opt.CSE

/-!
# known bits' checker

`knownBitsPass` is a translation validator: it runs `knownBitsWith`, which also returns the
final table `E` of `(value, known)` entries and the reachable blocks `R`, and keeps the result
only if the Bool checker `kbOK` accepts it, else returns the input
(`GoFV.Proof.KnownBits.knownBits_refines`).

The checker's lattice works on `BitVec 64` (`BB`): an entry claims the bits of `known` of the
value's 64-bit pattern (integers sign-extended from their width, booleans 0/1) to be those of
`value` (`ent` reads `E`, `value` masked by `known`).

`kbOK tabs f g E R`:
- `R` is closed: the entry is in `R`, and so is every successor a block of `R` can take (`First`:
  successor 0 only);
- `E` is a **post-fixpoint** of the transfer functions over `f` (`fixOK`): for every value of `f`,
  `E[x]` claims no more (`incl`) than its transfer (`tk` by the op's family `kind`, normalised at
  the shape of the value's type, `norm`; `(0, 0)` for other ops and atoms), a shift no more than
  each shift by an amount its amount's entry allows (`shiftOK`), a `Phi` no more than each
  argument on a live in-edge (`liveIn`: an edge from a block of `R`, of `First` blocks edge 0
  only). Fixpoint order and the cycle cut of `fold` do not matter: only the final table is checked;
- `g` is `f` but for values whose entry is fully known, which became `Copy c` of a constant `c`
  of `g` of that value at the value's shape (`repOK`); `g`'s blocks list `f`'s values first
  (new constants are appended to the entry), same atoms (`RewriteCheck.atomsOK`), kinds,
  successors, IDs and controls (`blocksOK`), and both are closed under arguments
  (`RewriteCheck.closedOK`).
-/

namespace GoFV.Opt

open GoFV.SSA

namespace KnownBits

/-- A lattice entry over 64 bits: `(value, known)`. -/
abbrev BB := BitVec 64 × BitVec 64

/-- The entry of `a` (`(0, 0)`: nothing known), its value masked by its known bits. -/
def ent (E : Array (Int64 × Int64)) (a : ID) : BB :=
  let r := E.getD a (0, 0)
  (r.1.toBitVec &&& r.2.toBitVec, r.2.toBitVec)

/-- The entry of argument `i` of `v`. -/
def argE (E : Array (Int64 × Int64)) (v : Value) (i : Nat) : BB := ent E (v.args[i]?.getD 0)

/-- The low `n ≤ 64` bits. -/
def lowMask (n : Nat) : BitVec 64 := ~~~(BitVec.allOnes 64 <<< n)

/-- Sign extension from the low `n` bits. -/
def sext (n : Nat) (x : BitVec 64) : BitVec 64 := (x.setWidth n).signExtend 64

/-- `fold`'s `finish` at the shape of the value's type: booleans keep bit 0, integers are
sign-extended from their width, unknown bits are cleared. -/
def norm (t : Sem.Ty) (r : BB) : BB :=
  match t with
  | .bool => (r.1 &&& 1 &&& (r.2 ||| ~~~1), r.2 ||| ~~~1)
  | .int w => (sext w.bits r.1 &&& sext w.bits r.2, sext w.bits r.2)
  | _ => (0, 0)

/-- `e` claims a subset of `r`'s known bits, with `r`'s values. -/
def incl (r e : BB) : Bool := (e.2 &&& ~~~r.2) == 0 && (r.1 &&& e.2) == (e.1 &&& e.2)

/-- A shift's direction. -/
inductive ShK where
  | lsh | rsh | rshu
  deriving DecidableEq

/-- The op families known bits has a transfer function for. -/
inductive KOp where
  | const (w : Sem.Width)
  | constBool
  | and (w : Sem.Width)
  | andB
  | or (w : Sem.Width)
  | orB
  | xor (w : Sem.Width)
  | com (w : Sem.Width)
  | not
  | copy
  | cvt
  | signExt (w w' : Sem.Width)
  | trunc (w w' : Sem.Width)
  | zeroExt (w w' : Sem.Width)
  | eq (w : Sem.Width)
  | eqB
  | neq (w : Sem.Width)
  | neqB
  | shift (s : ShK) (w a : Sem.Width)

/-- The family of an op. -/
def kind : Op → Option KOp
  | .Const8 => some (.const .w8) | .Const16 => some (.const .w16)
  | .Const32 => some (.const .w32) | .Const64 => some (.const .w64)
  | .ConstBool => some .constBool
  | .And8 => some (.and .w8) | .And16 => some (.and .w16) | .And32 => some (.and .w32)
  | .And64 => some (.and .w64) | .AndB => some .andB
  | .Or8 => some (.or .w8) | .Or16 => some (.or .w16) | .Or32 => some (.or .w32)
  | .Or64 => some (.or .w64) | .OrB => some .orB
  | .Xor8 => some (.xor .w8) | .Xor16 => some (.xor .w16) | .Xor32 => some (.xor .w32)
  | .Xor64 => some (.xor .w64)
  | .Com8 => some (.com .w8) | .Com16 => some (.com .w16) | .Com32 => some (.com .w32)
  | .Com64 => some (.com .w64) | .Not => some .not
  | .Copy => some .copy | .CvtBoolToUint8 => some .cvt
  | .SignExt8to16 => some (.signExt .w8 .w16) | .SignExt8to32 => some (.signExt .w8 .w32)
  | .SignExt8to64 => some (.signExt .w8 .w64) | .SignExt16to32 => some (.signExt .w16 .w32)
  | .SignExt16to64 => some (.signExt .w16 .w64) | .SignExt32to64 => some (.signExt .w32 .w64)
  | .Trunc16to8 => some (.trunc .w16 .w8) | .Trunc32to8 => some (.trunc .w32 .w8)
  | .Trunc32to16 => some (.trunc .w32 .w16) | .Trunc64to8 => some (.trunc .w64 .w8)
  | .Trunc64to16 => some (.trunc .w64 .w16) | .Trunc64to32 => some (.trunc .w64 .w32)
  | .ZeroExt8to16 => some (.zeroExt .w8 .w16) | .ZeroExt8to32 => some (.zeroExt .w8 .w32)
  | .ZeroExt8to64 => some (.zeroExt .w8 .w64) | .ZeroExt16to32 => some (.zeroExt .w16 .w32)
  | .ZeroExt16to64 => some (.zeroExt .w16 .w64) | .ZeroExt32to64 => some (.zeroExt .w32 .w64)
  | .Eq8 => some (.eq .w8) | .Eq16 => some (.eq .w16) | .Eq32 => some (.eq .w32)
  | .Eq64 => some (.eq .w64) | .EqB => some .eqB
  | .Neq8 => some (.neq .w8) | .Neq16 => some (.neq .w16) | .Neq32 => some (.neq .w32)
  | .Neq64 => some (.neq .w64) | .NeqB => some .neqB
  | .Lsh8x8 => some (.shift .lsh .w8 .w8) | .Lsh8x16 => some (.shift .lsh .w8 .w16)
  | .Lsh8x32 => some (.shift .lsh .w8 .w32) | .Lsh8x64 => some (.shift .lsh .w8 .w64)
  | .Lsh16x8 => some (.shift .lsh .w16 .w8) | .Lsh16x16 => some (.shift .lsh .w16 .w16)
  | .Lsh16x32 => some (.shift .lsh .w16 .w32) | .Lsh16x64 => some (.shift .lsh .w16 .w64)
  | .Lsh32x8 => some (.shift .lsh .w32 .w8) | .Lsh32x16 => some (.shift .lsh .w32 .w16)
  | .Lsh32x32 => some (.shift .lsh .w32 .w32) | .Lsh32x64 => some (.shift .lsh .w32 .w64)
  | .Lsh64x8 => some (.shift .lsh .w64 .w8) | .Lsh64x16 => some (.shift .lsh .w64 .w16)
  | .Lsh64x32 => some (.shift .lsh .w64 .w32) | .Lsh64x64 => some (.shift .lsh .w64 .w64)
  | .Rsh8x8 => some (.shift .rsh .w8 .w8) | .Rsh8x16 => some (.shift .rsh .w8 .w16)
  | .Rsh8x32 => some (.shift .rsh .w8 .w32) | .Rsh8x64 => some (.shift .rsh .w8 .w64)
  | .Rsh16x8 => some (.shift .rsh .w16 .w8) | .Rsh16x16 => some (.shift .rsh .w16 .w16)
  | .Rsh16x32 => some (.shift .rsh .w16 .w32) | .Rsh16x64 => some (.shift .rsh .w16 .w64)
  | .Rsh32x8 => some (.shift .rsh .w32 .w8) | .Rsh32x16 => some (.shift .rsh .w32 .w16)
  | .Rsh32x32 => some (.shift .rsh .w32 .w32) | .Rsh32x64 => some (.shift .rsh .w32 .w64)
  | .Rsh64x8 => some (.shift .rsh .w64 .w8) | .Rsh64x16 => some (.shift .rsh .w64 .w16)
  | .Rsh64x32 => some (.shift .rsh .w64 .w32) | .Rsh64x64 => some (.shift .rsh .w64 .w64)
  | .Rsh8Ux8 => some (.shift .rshu .w8 .w8) | .Rsh8Ux16 => some (.shift .rshu .w8 .w16)
  | .Rsh8Ux32 => some (.shift .rshu .w8 .w32) | .Rsh8Ux64 => some (.shift .rshu .w8 .w64)
  | .Rsh16Ux8 => some (.shift .rshu .w16 .w8) | .Rsh16Ux16 => some (.shift .rshu .w16 .w16)
  | .Rsh16Ux32 => some (.shift .rshu .w16 .w32) | .Rsh16Ux64 => some (.shift .rshu .w16 .w64)
  | .Rsh32Ux8 => some (.shift .rshu .w32 .w8) | .Rsh32Ux16 => some (.shift .rshu .w32 .w16)
  | .Rsh32Ux32 => some (.shift .rshu .w32 .w32) | .Rsh32Ux64 => some (.shift .rshu .w32 .w64)
  | .Rsh64Ux8 => some (.shift .rshu .w64 .w8) | .Rsh64Ux16 => some (.shift .rshu .w64 .w16)
  | .Rsh64Ux32 => some (.shift .rshu .w64 .w32) | .Rsh64Ux64 => some (.shift .rshu .w64 .w64)
  | _ => none

/-- The transfer function of a non-shift family on its arguments' entries (`fold`'s). -/
def tk : KOp → Int64 → BB → BB → BB
  | .const w, ai, _, _ => (sext w.bits ai.toBitVec, BitVec.allOnes 64)
  | .constBool, ai, _, _ => (if ai != 0 then 1 else 0, BitVec.allOnes 64)
  | .and _, _, (a, ak), (b, bk) | .andB, _, (a, ak), (b, bk) =>
    (a &&& b, (a &&& b) ||| (~~~a &&& ak) ||| (~~~b &&& bk))
  | .or _, _, (a, ak), (b, bk) | .orB, _, (a, ak), (b, bk) =>
    (a ||| b, a ||| b ||| (~~~a &&& ~~~b &&& (ak &&& bk)))
  | .xor _, _, (a, ak), (b, bk) => (a ^^^ b, ak &&& bk)
  | .com _, _, (a, ak), _ | .not, _, (a, ak), _ => (~~~a, ak)
  | .copy, _, r, _ | .cvt, _, r, _ | .signExt _ _, _, r, _ | .trunc _ _, _, r, _ => r
  | .zeroExt w _, _, (a, ak), _ => (a &&& lowMask w.bits, ak ||| ~~~lowMask w.bits)
  | .eq _, _, (a, ak), (b, bk) | .eqB, _, (a, ak), (b, bk) =>
    if (a ^^^ b) &&& ak &&& bk != 0 then (0, BitVec.allOnes 64)
    else if ak == BitVec.allOnes 64 && bk == BitVec.allOnes 64 then
      (if a == b then 1 else 0, BitVec.allOnes 64)
    else (0, ~~~1)
  | .neq _, _, (a, ak), (b, bk) | .neqB, _, (a, ak), (b, bk) =>
    if (a ^^^ b) &&& ak &&& bk != 0 then (1, BitVec.allOnes 64)
    else if ak == BitVec.allOnes 64 && bk == BitVec.allOnes 64 then
      (if a != b then 1 else 0, BitVec.allOnes 64)
    else (0, ~~~1)
  | .shift _ _ _, _, _, _ => (0, 0)

/-- A shift of a `w`-bit operand with entry `(a, ak)` by `m ≤ w` (Go's: by `w`, `0` or the sign
fill). -/
def doShift (s : ShK) (w : Sem.Width) (r : BB) (m : Nat) : BB :=
  match s with
  | .lsh => if m < w.bits then (r.1 <<< m, (r.2 <<< m) ||| lowMask m) else (0, BitVec.allOnes 64)
  | .rshu =>
    if m < w.bits then
      ((r.1 &&& lowMask w.bits) >>> m,
       ((r.2 ||| ~~~lowMask w.bits) >>> m) ||| ~~~(BitVec.allOnes 64 >>> m))
    else (0, BitVec.allOnes 64)
  | .rsh => (r.1.sshiftRight m, r.2.sshiftRight m)

/-- The effective amount `m ≤ w` of a shift (amount `min n w`) is possible for an `a`-bit amount
`n` with entry `(y, yk)`: `m < w` agrees with the known bits, `m = w` needs an unbounded shift
and an amount `≥ w` within the known bits. -/
def feasible (w a : Sem.Width) (bounded : Bool) (y yk : BitVec 64) (m : Nat) : Bool :=
  if m < w.bits then ((BitVec.ofNat 64 m ^^^ y) &&& yk &&& lowMask a.bits) == 0
  else !bounded && w.bits ≤ (((y &&& yk) ||| ~~~yk) &&& lowMask a.bits).toNat

/-- A shift's claim `e`: no more than the shift by each feasible amount. -/
def shiftOK (t : Sem.Ty) (s : ShK) (w a : Sem.Width) (bounded : Bool) (r y : BB) (e : BB) : Bool :=
  (List.range (w.bits + 1)).all fun m =>
    !feasible w a bounded y.1 y.2 m || incl (norm t (doShift s w r m)) e

/-- The run may enter block `b` along its edge `i`: the entry along edge 0 (how a run starts),
or an edge from a block of `R` that its terminator can take (`First`: successor 0 only). -/
def liveIn (f : Func) (R : Array Bool) (b : ID) (i : Nat) : Bool :=
  (b == f.entry && i == 0) ||
  match (f.block? b).bind (·.preds[i]?) with
  | some e => R.getD e.b false && match f.block? e.b with
    | some pb => pb.kind != .First || e.i == 0
    | none => false
  | none => false

/-- `R` holds the entry and is closed under the successors a terminator can take. -/
def reachOK (f : Func) (R : Array Bool) : Bool :=
  R.getD f.entry false &&
  f.blocks.all fun b =>
    !R.getD b false || match f.block? b with
      | some fb => (List.range fb.succs.size).all fun k =>
          (fb.kind == .First && k != 0) || R.getD fb.succs[k]!.b false
      | none => true

/-- The post-fixpoint condition at value `x`. -/
def fixOK (tabs : Tables) (f : Func) (R : Array Bool) (E : Array (Int64 × Int64)) (x : ID) :
    Bool :=
  match f.value? x with
  | none => true
  | some v =>
    let t := tabs.ty v.type
    let e := ent E x
    if v.op == .Phi then
      (List.range v.args.size).all fun i =>
        !liveIn f R v.block i || incl (norm t (ent E v.args[i]!)) e
    else if !RewriteCheck.termOp v.op then incl (norm t (0, 0)) e
    else match kind v.op with
      | some (.shift s w a) =>
        shiftOK t s w a (v.auxInt == 1) (argE E v 0) (argE E v 1) e
      | some k => incl (norm t (tk k v.auxInt (argE E v 0) (argE E v 1))) e
      | none => incl (norm t (0, 0)) e

/-- `c` is a constant of `g` whose value at shape `t` is the fully known entry value `val`. -/
def constOK (tabs : Tables) (g : Func) (t : Sem.Ty) (val : BitVec 64) (c : ID) : Bool :=
  match g.value? c with
  | some cv =>
    cv.args.isEmpty && cv.block == g.entry && CSE.tyEq (tabs.ty cv.type) t && cv.auxInt.toBitVec == val &&
    match cv.op, t with
    | .Const8, .int .w8 | .Const16, .int .w16 | .Const32, .int .w32 | .Const64, .int .w64
    | .ConstBool, .bool => true
    | _, _ => false
  | none => false

/-- Value `x` of `f` is unchanged in `g` (but for its use count), or became `Copy c` of a
constant of its fully known entry value. -/
def repOK (tabs : Tables) (f g : Func) (E : Array (Int64 × Int64)) (x : ID) : Bool :=
  match f.value? x, g.value? x with
  | none, _ => true
  | some _, none => false
  | some u, some w =>
    w.id == u.id && w.block == u.block &&
    ((w.op == u.op && w.type == u.type && w.auxInt == u.auxInt && w.aux == u.aux &&
      w.args == u.args) ||
     (w.op == .Copy && w.args.size == 1 && (ent E x).2 == BitVec.allOnes 64 &&
      CSE.tyEq (tabs.ty w.type) (tabs.ty u.type) &&
      constOK tabs g (tabs.ty u.type) (ent E x).1 (w.args[0]?.getD 0)))

/-- `g`'s blocks list `f`'s values first, with the same kinds, successors, IDs and controls. -/
def blocksOK (f g : Func) : Bool :=
  f.blocks.all fun b =>
    match f.block? b, g.block? b with
    | some fb, some gb =>
      fb.kind == gb.kind && fb.succs == gb.succs && fb.id == gb.id &&
      fb.controls == gb.controls && fb.values == gb.values.extract 0 fb.values.size
    | _, _ => false

/-- **The checker.** -/
def kbOK (tabs : Tables) (f g : Func) (E : Array (Int64 × Int64)) (R : Array Bool) : Bool :=
  RewriteCheck.atomsOK f g && RewriteCheck.closedOK f && RewriteCheck.closedOK g &&
  blocksOK f g && reachOK f R &&
  (List.range f.valueTab.size).all (fun x => fixOK tabs f R E x && repOK tabs f g E x)

end KnownBits

/-- known bits, validated: the result if it changed and `kbOK` accepts it, else the input. -/
def knownBitsChecked (tabs : Tables) (order : TypeOrder) (f : Func) : Except String Func := do
  let (g, E, R) ← knownBitsWith tabs order f
  return if g != f && KnownBits.kbOK tabs f g E R then g else f

/-- The `known bits` pass (validated). -/
def knownBitsPass : Pass := Pass.ofFunc fun env f => knownBitsChecked env.tables env.typeOrder f

end GoFV.Opt
