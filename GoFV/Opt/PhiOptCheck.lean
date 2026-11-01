import GoFV.Opt.PhiOpt
import GoFV.SSA.DomCert
import GoFV.SSA.Sem.Run

/-!
# phiopt's checker

`phioptPass` is a translation validator: it runs `phiopt` and keeps the result only if the
Bool checker `prel` accepts it, else returns the input (`GoFV.Proof.PhiOpt.phiopt_refines`).

`prel f g`: `g` has `f`'s control-flow graph, block kinds and controls, and `f`'s values with
their IDs and types; every value keeps its op, aux, auxint and arguments except *rewritten*
`Phi`s; `g`'s blocks may hold *new* values (no table entry in `f`): `Not`/`CvtBoolToUint8` of
an available value or of a new `Not`.

A rewritten `Phi` `v = Phi a₀ a₁` of block `b` is justified by **edge facts**
(`edgeFact f c fuel b i = some dᵢ`): entering `b` along its edge `i`, the control `c` of an
`If` holds `dᵢ`, because the run left that `If` through the successor named by `dᵢ` and then
went only through single-predecessor blocks that do not define `c`. Its new form must yield
`aᵢ`'s value whenever `c = dᵢ` (`formOK`): `Copy c`, `Not c` (constant arms), `OrB c n`,
`AndB c n` (one arm constant or `c`, the other `n`, available), or phioptint's
`ZeroExt8toN (CvtBoolToUint8 [Not] c)`/`Copy` of it (integer constant arms 0/1).
-/

namespace GoFV.Opt

open GoFV.SSA

namespace PhiOpt

/-- **Edge fact**: entering `x` along its edge `j`, value `c` holds `d` (the result), since the
edge comes from an `If` on `c` (`d`: through its first successor), or from a block with a single
predecessor that does not define `c` and that is entered with the fact. -/
def edgeFact (f : Func) (c : ID) : Nat → ID → Nat → Option Bool
  | 0, _, _ => none
  | fuel + 1, x, j =>
    match f.block? x with
    | none => none
    | some xb =>
      match xb.preds[j]? with
      | none => none
      | some e =>
        match f.block? e.b with
        | none => none
        | some y =>
          if y.kind == .If && y.controls[0]? == some c then some (e.i == 0)
          else if y.preds.size == 1 && !y.values.contains c then edgeFact f c fuel e.b 0
          else none

/-- `x` is listed in block `b`. -/
def listedIn (f : Func) (b x : ID) : Bool := ((f.block? b).map (·.values.contains x)).getD false

/-- `x` is a value of `f` placed in a listed block that strictly dominates `b` in the
certified dominator tree (so it is available on entry to `b`), and not listed in `b`. -/
def avail (f : Func) (b x : ID) : Bool :=
  match f.value? x with
  | some v => f.blocks.contains v.block && listedIn f v.block x &&
      (DomCert.make f).anc v.block b && v.block != b && !listedIn f b x
  | none => false

/-- `a` is a `ConstBool` of `f` holding `d`. -/
def constB (f : Func) (a : ID) (d : Bool) : Bool :=
  match f.value? a with
  | some u => u.op == .ConstBool && (u.auxInt != 0) == d
  | none => false

/-- The width of an integer shape. -/
def intW (tabs : Tables) (t : TypeRef) : Option Sem.Width :=
  match tabs.ty t with
  | .int w => some w
  | _ => none

/-- The integer constant op of a width. -/
def constOp : Sem.Width → Op
  | .w8 => .Const8 | .w16 => .Const16 | .w32 => .Const32 | .w64 => .Const64

/-- The op extending a byte to a width (`Copy` for one byte). -/
def extOp : Sem.Width → Op
  | .w8 => .Copy | .w16 => .ZeroExt8to16 | .w32 => .ZeroExt8to32 | .w64 => .ZeroExt8to64

/-- `a` is an integer constant of `f` of width `w` (op and type) holding `k`. -/
def constI (tabs : Tables) (f : Func) (a : ID) (w : Sem.Width) (k : Int64) : Bool :=
  match f.value? a with
  | some u => u.op == constOp w && intW tabs u.type == some w && u.auxInt == k
  | none => false

/-- `x` is a new value of `g` (no table entry in `f`) listed in block `b`. -/
def isNew (f g : Func) (b x : ID) : Bool := (f.value? x).isNone && listedIn g b x

/-- A new value of block `b` of `g`: a `Not` of an available value, or a `CvtBoolToUint8` of an
available value or of a new `Not` of `b`. -/
def newOK (f g : Func) (b x : ID) : Bool :=
  match g.value? x with
  | some nv =>
    nv.id == x && nv.args.size == 1 &&
    (if nv.op == .Not then avail f b nv.args[0]!
     else if nv.op == .CvtBoolToUint8 then
       avail f b nv.args[0]! ||
         (isNew f g b nv.args[0]! &&
           (g.value? nv.args[0]!).any fun u => u.op == .Not && u.args.size == 1 &&
             avail f b u.args[0]!)
     else false)
  | none => false

/-- The edge facts of `b`'s two edges for value `c`. -/
def facts (f : Func) (b c : ID) : Option (Bool × Bool) :=
  let fuel := f.blocks.size + 1
  match edgeFact f c fuel b 0, edgeFact f c fuel b 1 with
  | some d0, some d1 => some (d0, d1)
  | _, _ => none

/-- Arm `a` holds `d` when `c` holds `dc`: a `ConstBool` `d`, or `c` itself with `dc = d`. -/
def armB (f : Func) (c a : ID) (dc d : Bool) : Bool := (a == c && dc == d) || constB f a d

/-- A `bool` shape. -/
def isBoolTy (tabs : Tables) (t : TypeRef) : Bool :=
  match tabs.ty t with
  | .bool => true
  | _ => false

/-- The boolean form `gv` (control `c`) yields arm `a` when `c` holds `d`: `Copy c` (`a` holds
`d`), `Not c` (`a` holds `¬d`), `OrB c n` (`a` holds `true` if `d`, else `a = n`), `AndB c n`
(`a = n` if `d`, else `a` holds `false`); `n` available. -/
def armOK (f : Func) (b c : ID) (gv : Value) (a : ID) (d : Bool) : Bool :=
  if gv.op == .Copy then gv.args.size == 1 && armB f c a d d
  else if gv.op == .Not then gv.args.size == 1 && armB f c a d !d
  else if gv.op == .OrB then
    gv.args.size == 2 && avail f b gv.args[1]! &&
      (if d then armB f c a d true else a == gv.args[1]!)
  else if gv.op == .AndB then
    gv.args.size == 2 && avail f b gv.args[1]! &&
      (if d then a == gv.args[1]! else armB f c a d false)
  else false

/-- The boolean forms of a rewritten `Phi` (`fv`, with arms `a₀ a₁`, of `bool` shape) in block
`b` (`gv`: its value in `g`). -/
def boolForm (tabs : Tables) (f : Func) (b : ID) (fv : Value) (a0 a1 : ID) (gv : Value) : Bool :=
  isBoolTy tabs fv.type &&
  match gv.args[0]? with
  | none => false
  | some c =>
    avail f b c &&
    match facts f b c with
    | none => false
    | some (d0, d1) => armOK f b c gv a0 d0 && armOK f b c gv a1 d1

/-- phioptint's arms: `c` available, and arm `aᵢ` the integer constant `dᵢ ≠ neg` of width
`w`. -/
def intArms (tabs : Tables) (f : Func) (b : ID) (w : Sem.Width) (a0 a1 c : ID) (neg : Bool) :
    Bool :=
  avail f b c &&
  match facts f b c with
  | some (d0, d1) =>
    constI tabs f a0 w (if d0 != neg then 1 else 0) &&
      constI tabs f a1 w (if d1 != neg then 1 else 0)
  | none => false

/-- phioptint's form: `extOp w (CvtBoolToUint8 x)` with `x = c` or `x = Not c` (new values of
`b`), the `Phi` of width `w` with integer constant arms 0/1. -/
def intForm (tabs : Tables) (f g : Func) (b : ID) (fv gv : Value) (a0 a1 : ID) : Bool :=
  match intW tabs fv.type, gv.args[0]? with
  | some w, some cv =>
    gv.op == extOp w && gv.args.size == 1 && isNew f g b cv &&
    match g.value? cv with
    | some cvv =>
      cvv.op == .CvtBoolToUint8 && intW tabs cvv.type == some .w8 && cvv.args.size == 1 &&
      if isNew f g b cvv.args[0]! then
        match g.value? cvv.args[0]! with
        | some nv => nv.op == .Not && nv.args.size == 1 && intArms tabs f b w a0 a1 nv.args[0]! true
        | none => false
      else intArms tabs f b w a0 a1 cvv.args[0]! false
    | none => false
  | _, _ => false

/-- A rewritten `Phi` (`fv` in `f`, `gv` in `g`) in a block with two predecessors. -/
def rewriteOK (tabs : Tables) (f g : Func) (fv gv : Value) : Bool :=
  fv.op == .Phi && gv.op != .Phi && fv.args.size == 2 &&
  ((f.block? fv.block).map (·.preds.size == 2)).getD false &&
  let a0 := fv.args[0]!
  let a1 := fv.args[1]!
  boolForm tabs f fv.block fv a0 a1 gv || intForm tabs f g fv.block fv gv a0 a1

/-- Value `x` of `f` in `g`: same ID, type and block, and the same op, aux, auxint and arguments
or a rewritten `Phi`. -/
def valueOK (tabs : Tables) (f g : Func) (x : ID) : Bool :=
  match f.value? x with
  | none => true
  | some fv =>
    match g.value? x with
    | none => false
    | some gv =>
      gv.id == fv.id && gv.type == fv.type && gv.block == fv.block &&
      ((gv.op == fv.op && gv.aux == fv.aux && gv.auxInt == fv.auxInt && gv.args == fv.args) ||
        rewriteOK tabs f g fv gv)

/-- Block `bid`: same kind and controls; `f`'s values, and new values. -/
def blockOK (f g : Func) (bid : ID) : Bool :=
  match f.block? bid, g.block? bid with
  | some fb, some gb =>
    gb.kind == fb.kind && gb.controls == fb.controls &&
    fb.values.all (fun x => gb.values.contains x) &&
    gb.values.all (fun x => fb.values.contains x || ((f.value? x).isNone && newOK f g bid x))
  | _, _ => false

/-- **phiopt's output relation**, checked. -/
def prel (tabs : Tables) (f g : Func) : Bool :=
  DomCert.cfgView g == DomCert.cfgView f && g.ownAux == f.ownAux &&
  f.valueTab.size ≤ g.valueTab.size &&
  f.blocks.all (blockOK f g) &&
  (List.range f.valueTab.size).all (valueOK tabs f g)

end PhiOpt

/-- `phiopt`, validated by `PhiOpt.prel` (the input if the checker rejects the result). -/
def phioptChecked (tabs : Tables) (uint8 : TypeRef) (f : Func) : Except String Func := do
  let g ← phiopt tabs uint8 f
  return if PhiOpt.prel tabs f g then g else f

/-- The `phiopt` pass (validated). -/
def phioptPass : Pass := Pass.ofFunc fun env f => do
  let some u8 := env.typ? "UInt8" | throw "phiopt: no typ.UInt8"
  phioptChecked env.tables u8 f

end GoFV.Opt
