import GoFV.Opt.KnownBits
import GoFV.Opt.RewriteCheck
import GoFV.Opt.CSE

/-!
# known bits' checker

`knownBitsPass` is a translation validator: it runs `knownBitsWith`, which also returns the
final table `E` of `(value, known)` entries and the reachable blocks `R`, and keeps the result
only if the Bool checker `kbOK` accepts it, else returns the input
(`GoFV.Proof.KnownBits.knownBits_refines`).

`kbOK tabs f g E R`:
- `R` is closed: the entry is in `R`, and so is every successor a block of `R` can take (`First`:
  successor 0 only);
- `E` is a **post-fixpoint** of the transfer functions over `f` (`transfer`, read from `E`,
  normalised at the shape of the value's type, `norm`): for every value of `f`, `E[x]` claims no
  more than the transfer of its arguments' entries (`incl`), a `Phi` no more than each argument on
  a live in-edge (`liveIn`: an edge from a block of `R`, of `First` blocks edge 0 only).
  Fixpoint order and the cycle cut of `fold` do not matter: only the final table is checked;
- `g` is `f` but for values whose entry is fully known, which became `Copy c` of a constant `c`
  of `g` of that value at the value's shape (`repOK`); `g`'s blocks list `f`'s values first
  (new constants are appended to the entry), same kinds, successors and controls
  (`RewriteCheck.atomsOK`), and both are closed under arguments (`RewriteCheck.closedOK`).
-/

namespace GoFV.Opt

open GoFV.SSA

namespace KnownBits

/-- A lattice entry `(value, known)`. -/
abbrev KB := Int64 × Int64

/-- `fold`'s `finish` at the shape of the value's type: booleans keep bit 0, integers are
sign-extended from their width, unknown bits are cleared. -/
def norm (t : Sem.Ty) (r : KB) : KB :=
  match t with
  | .bool => (r.1 &&& 1 &&& (r.2 ||| ~~~1), r.2 ||| ~~~1)
  | .int .w8 => (r.1.toInt8.toInt64 &&& r.2.toInt8.toInt64, r.2.toInt8.toInt64)
  | .int .w16 => (r.1.toInt16.toInt64 &&& r.2.toInt16.toInt64, r.2.toInt16.toInt64)
  | .int .w32 => (r.1.toInt32.toInt64 &&& r.2.toInt32.toInt64, r.2.toInt32.toInt64)
  | _ => (r.1 &&& r.2, r.2)

/-- `γ(r) ⊆ γ(e)`: `e` knows a subset of `r`'s bits, with `r`'s values. -/
def incl (r e : KB) : Bool := (e.2 &&& ~~~r.2) == 0 && (r.1 &&& e.2) == (e.1 &&& e.2)

/-- The entry of `a` (`(0, 0)`: nothing known). -/
@[inline] def ent (E : Array KB) (a : ID) : KB := E.getD a (0, 0)

/-- The width in bits of the first operand of a shift or extension op. -/
def opWidth : Op → Int64
  | .ZeroExt8to16 | .ZeroExt8to32 | .ZeroExt8to64
  | .Lsh8x8 | .Lsh8x16 | .Lsh8x32 | .Lsh8x64
  | .Rsh8Ux8 | .Rsh8Ux16 | .Rsh8Ux32 | .Rsh8Ux64
  | .Rsh8x8 | .Rsh8x16 | .Rsh8x32 | .Rsh8x64 => 8
  | .ZeroExt16to32 | .ZeroExt16to64
  | .Lsh16x8 | .Lsh16x16 | .Lsh16x32 | .Lsh16x64
  | .Rsh16Ux8 | .Rsh16Ux16 | .Rsh16Ux32 | .Rsh16Ux64
  | .Rsh16x8 | .Rsh16x16 | .Rsh16x32 | .Rsh16x64 => 16
  | .ZeroExt32to64
  | .Lsh32x8 | .Lsh32x16 | .Lsh32x32 | .Lsh32x64
  | .Rsh32Ux8 | .Rsh32Ux16 | .Rsh32Ux32 | .Rsh32Ux64
  | .Rsh32x8 | .Rsh32x16 | .Rsh32x32 | .Rsh32x64 => 32
  | _ => 64

/-- The transfer function of a non-`Phi` value `x` (`fold`'s, before `finish`), reading its
arguments' entries from `E`. -/
def transfer (E : Array KB) (x : Value) : KB :=
  let arg (i : Nat) : KB := ent E x.args[i]!
  let shift (doShift : ShiftFn) : KB :=
    let (a, ak) := arg 0
    let (y, yk) := arg 1
    shiftResult doShift x.auxInt a ak (opWidth x.op) y yk
  match x.op with
  | .Const64 | .Const32 | .Const16 | .Const8 => (x.auxInt, -1)
  | .ConstBool => (if x.auxInt != 0 then 1 else 0, -1)
  | .And64 | .And32 | .And16 | .And8 | .AndB =>
    let (a, ak) := arg 0
    let (b, bk) := arg 1
    (a &&& b, (a &&& b) ||| (~~~a &&& ak) ||| (~~~b &&& bk))
  | .Or64 | .Or32 | .Or16 | .Or8 | .OrB =>
    let (a, ak) := arg 0
    let (b, bk) := arg 1
    (a ||| b, a ||| b ||| (~~~a &&& ~~~b &&& (ak &&& bk)))
  | .Xor64 | .Xor32 | .Xor16 | .Xor8 =>
    let (a, ak) := arg 0
    let (b, bk) := arg 1
    (a ^^^ b, ak &&& bk)
  | .Com64 | .Com32 | .Com16 | .Com8 | .Not =>
    let (a, ak) := arg 0
    (~~~a, ak)
  | .Copy | .CvtBoolToUint8
  | .SignExt8to16 | .SignExt8to32 | .SignExt8to64 | .SignExt16to32 | .SignExt16to64
  | .SignExt32to64
  | .Trunc64to32 | .Trunc64to16 | .Trunc64to8 | .Trunc32to16 | .Trunc32to8
  | .Trunc16to8 => arg 0
  | .Eq64 | .Eq32 | .Eq16 | .Eq8 | .EqB =>
    let (a, ak) := arg 0
    let (b, bk) := arg 1
    if (a ^^^ b) &&& ak &&& bk != 0 then (0, -1)
    else if ak == -1 && bk == -1 then (if a == b then 1 else 0, -1)
    else (0, -2)
  | .Neq64 | .Neq32 | .Neq16 | .Neq8 | .NeqB =>
    let (a, ak) := arg 0
    let (b, bk) := arg 1
    if (a ^^^ b) &&& ak &&& bk != 0 then (1, -1)
    else if ak == -1 && bk == -1 then (if a != b then 1 else 0, -1)
    else (0, -2)
  | .ZeroExt8to16 | .ZeroExt8to32 | .ZeroExt8to64 | .ZeroExt16to32 | .ZeroExt16to64
  | .ZeroExt32to64 =>
    let (a, k) := arg 0
    let mask := shl 1 (opWidth x.op) - 1
    (a &&& mask, k ||| ~~~mask)
  | .Lsh8x8 | .Lsh16x8 | .Lsh32x8 | .Lsh64x8
  | .Lsh8x16 | .Lsh16x16 | .Lsh32x16 | .Lsh64x16
  | .Lsh8x32 | .Lsh16x32 | .Lsh32x32 | .Lsh64x32
  | .Lsh8x64 | .Lsh16x64 | .Lsh32x64 | .Lsh64x64 => shift lshFn
  | .Rsh8Ux8 | .Rsh16Ux8 | .Rsh32Ux8 | .Rsh64Ux8
  | .Rsh8Ux16 | .Rsh16Ux16 | .Rsh32Ux16 | .Rsh64Ux16
  | .Rsh8Ux32 | .Rsh16Ux32 | .Rsh32Ux32 | .Rsh64Ux32
  | .Rsh8Ux64 | .Rsh16Ux64 | .Rsh32Ux64 | .Rsh64Ux64 => shift rshuFn
  | .Rsh8x8 | .Rsh16x8 | .Rsh32x8 | .Rsh64x8
  | .Rsh8x16 | .Rsh16x16 | .Rsh32x16 | .Rsh64x16
  | .Rsh8x32 | .Rsh16x32 | .Rsh32x32 | .Rsh64x32
  | .Rsh8x64 | .Rsh16x64 | .Rsh32x64 | .Rsh64x64 => shift rshFn
  | _ => (0, 0)

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
def fixOK (tabs : Tables) (f : Func) (R : Array Bool) (E : Array KB) (x : ID) : Bool :=
  match f.value? x with
  | none => true
  | some v =>
    let t := tabs.ty v.type
    if v.op == .Phi then
      (List.range v.args.size).all fun i =>
        !liveIn f R v.block i || incl (norm t (ent E v.args[i]!)) (ent E x)
    else if RewriteCheck.termOp v.op then incl (norm t (transfer E v)) (ent E x)
    else incl (norm t (0, 0)) (ent E x)

/-- `c` is a constant of `g` whose value at shape `t` is the fully known entry value `val`. -/
def constOK (tabs : Tables) (g : Func) (t : Sem.Ty) (val : Int64) (c : ID) : Bool :=
  match g.value? c with
  | some cv =>
    cv.args.isEmpty && CSE.tyEq (tabs.ty cv.type) t && cv.auxInt == val &&
    match cv.op, t with
    | .Const8, .int .w8 | .Const16, .int .w16 | .Const32, .int .w32 | .Const64, .int .w64
    | .ConstBool, .bool => true
    | _, _ => false
  | none => false

/-- Value `x` of `f` is unchanged in `g` (but for its use count), or became `Copy c` of a
constant of its fully known entry value. -/
def repOK (tabs : Tables) (f g : Func) (E : Array KB) (x : ID) : Bool :=
  match f.value? x, g.value? x with
  | none, _ => true
  | some _, none => false
  | some u, some w =>
    w.id == u.id && w.block == u.block &&
    ((w.op == u.op && w.type == u.type && w.auxInt == u.auxInt && w.aux == u.aux &&
      w.args == u.args) ||
     (w.op == .Copy && w.args.size == 1 && (ent E x).2 == -1 &&
      CSE.tyEq (tabs.ty w.type) (tabs.ty u.type) &&
      constOK tabs g (tabs.ty u.type) (ent E x).1 w.args[0]!))

/-- `g`'s block lists `f`'s values first, and the same controls. -/
def blocksOK (f g : Func) : Bool :=
  f.blocks.all fun b =>
    match f.block? b, g.block? b with
    | some fb, some gb => fb.controls == gb.controls && fb.values == gb.values.extract 0 fb.values.size
    | _, _ => false

/-- **The checker.** -/
def kbOK (tabs : Tables) (f g : Func) (E : Array KB) (R : Array Bool) : Bool :=
  RewriteCheck.atomsOK f g && RewriteCheck.closedOK f && RewriteCheck.closedOK g &&
  blocksOK f g && reachOK f R &&
  (List.range f.valueTab.size).all (fun x => fixOK tabs f R E x && repOK tabs f g E x)

end KnownBits

/-- known bits, validated: the result if `kbOK` accepts it, else the input. -/
def knownBitsChecked (tabs : Tables) (order : TypeOrder) (f : Func) : Except String Func := do
  let (g, E, R) ← knownBitsWith tabs order f
  return if KnownBits.kbOK tabs f g E R then g else f

/-- The `known bits` pass (validated). -/
def knownBitsPass : Pass := Pass.ofFunc fun env f => knownBitsChecked env.tables env.typeOrder f

end GoFV.Opt
