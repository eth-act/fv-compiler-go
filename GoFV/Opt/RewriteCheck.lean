import GoFV.Proof.Rules.AllSound
import GoFV.Rules.Run
import GoFV.Opt.CSE
import GoFV.Opt.TabsAgree
import GoFV.Opt.NilCheckRel
import GoFV.Opt.Checked
import GoFV.Opt.CopyRelCheck
import GoFV.Opt.MemCall
import GoFV.Opt.MemTy
import GoFV.Opt.ExpandCallsCheck
import GoFV.SSA.Sem.Image

variable [GoFV.SSA.Sem.Addrs]

/-!
# Validating a rewrite pass (`applyRewrite`) against its log (issue #113)

`applyRewrite` run with its log on (`RwState.log`) records every value rule it fires: the value,
the rule (index in the value's op row of the table) and the definitions it built. `validate`
replays the log on a map of definitions, starting from the input `f`:

* a rule event is checked as an instance of the rule on the current definitions (`ruleOK`):
  the pattern matches at the value (`matchPat`, with the commutative choices that make the rest
  hold), the pattern's checks (`Pat.cons`), the checker facts (`Pat.wf`) and the condition
  hold under `GoFV.Proof.Rules.evalE` with the oracle `oracle` (unmodelled expressions: `true`
  if boolean, the fields of the built nodes otherwise), the top op produces its value's shape
  (`topOK`: `natShape` for integer, float and boolean ops, a pointer op `ptrTop` whose
  arguments have the shapes `argShapeOk`
  asks for, `Pat.argsOK`, checked at every op node, or a constant composite `constTop`), every
  leaf has an integer, boolean or pointer shape, and the built definitions are those of
  `Rule.Sound`'s result denotation (`resDen`); `copy` results and `build` results in place or,
  for an `@b` result, with a fresh top of which `v` becomes a compatible copy (`blockTopOK`);
* a copy-argument replacement (`copyArg v i src`, copy elimination before a rule matches) is
  replayed on the definitions when `src` is reached from the old argument through `Copy`s of
  compatible shape (`copyReach`);
* the terminators of the blocks whose controls copy elimination followed or a block rule
  rewrote are replayed too (`BState`: kind, controls, successors swapped or not): a control
  replacement (`control b i c`) when `c` is reached from the old control through copies; a
  block-rule event (`blockRule b i ctrls`, issue #151) when the block has two successors and
  is an `If` on one boolean control and the rule's control rule (`BlockRule.ctrlRule`) fires at that control as
  a value rule (`ruleOK`) with the definitions the new controls `ctrls` determine (`ctrlDefs`;
  for the generic rules they are the control's own definition);
* a rule event outside the value's op row is a struct-load expansion (`structLoadOK`, issue
  #151: `rewriteStructLoad`, `Load <struct> p m` → `StructMake` of field `Load`s at `OffPtr`s);
* a rule event of a selection of a `Make` (`GoFV.Proof.Rules.makeSelShape`, issue #17, e.g.
  `(ITab (IMake itab _)) => itab` or the variadic `(StructSelect [i] x:(StructMake ___)) =>
  x.Args[i]`) is first checked per instance (`makeSelOK`, the selected value resolved through
  compatible copies and selections of `Make`s, `selRes`), else as a rule instance (`ruleOK`);
* a rule event of an unconditional selection of a `Load` with an `@b` result
  (`GoFV.Proof.Rules.loadSelShape`, issue #17, `dec.rules:132`, `:141`) is checked per instance
  only (`loadSelOK`);
* an event of a dropped rule (`dropShape`), a copy-argument replacement the copies do not
  justify, and (in `validate`, `lax`) a table rule's event that is not validated are skipped:
  the value keeps its definition;
* a phi elimination rejects;
* finally every value listed in the output `g` that `g` reads (`liveMarks`, `liveOK`), and every
  atom, has the replayed definition up to copies: each argument (and each control of `g`) is
  the replayed one or reached from it through `Copy`s of the same shape (`copyReach`), which is
  how copy elimination and `copySource`'s path compression rewrite arguments; every block of
  `g` has its replayed terminator (kind, successors in the replayed order, controls up to
  copies).

`Rule.Sound` of every rule of the table then gives that each definition of `g` refines the
input's as a term over the unchanged values (`GoFV.Proof.Term`).
-/

namespace GoFV.Opt.RewriteCheck

open GoFV.SSA GoFV.Rules GoFV.Proof.Rules

/-- Definitions by value ID. -/
abbrev Defs := Array (Option Value)

@[inline] def Defs.get? (M : Defs) (x : ID) : Option Value := (M[x]?).join

/-- Set the definition of `x` (growing the map if needed). -/
def Defs.put (M : Defs) (x : ID) (v : Value) : Defs :=
  let M := if x < M.size then M else M ++ Array.replicate (x + 1 - M.size) none
  M.set! x (some v)

/-- A pattern instance: the value at each position (path) of the pattern. -/
abbrev Inst := List (Path × ID)

def Inst.at (I : Inst) (p : Path) : ID := (I.lookup p).getD 0

/-- Swap the first two elements. -/
def swap01 {α : Type} : List α → List α
  | a :: b :: l => b :: a :: l
  | l => l

/-- The nodes of terms: ops evaluated by `evalPure`, and `Addr`/`ConstString`, which the
semantics evaluates from the tables alone (`GoFV.Proof.Rules.opVal`, issue #151); not roots,
phis or activation-dependent ops. `Invalid` is one (`poison`): sccp leaves its failed fold
temporaries as `Invalid` values. -/
def termOp (op : Op) : Bool :=
  !Sem.isRoot op && !(op matches .Phi | .InitMem | .Arg | .ArgIntReg | .ArgFloatReg | .PanicBounds |
    .StaticLECall | .StaticCall | .Store | .StoreWB | .Move | .MoveWB | .Zero | .ZeroWB |
    .VarDef | .VarLive | .KeepAlive | .WBend | .NilCheck | .SP | .LocalAddr |
    .GetClosurePtr | .GetCallerSP)

/-- The ops whose first two arguments commute (`GoFV.Proof.Rules.commOpsP1`): a `commute` node
is matched swapped only at these. -/
def commOps : List Op :=
  [.Add8, .Add16, .Add32, .Add64, .Add64carry, .And8, .And16, .And32, .And64, .AndB, .Eq8,
   .Eq16, .Eq32, .Eq64, .EqB, .Mul8, .Mul16, .Mul32, .Mul64, .Mul32uhilo, .Mul32uover,
   .Mul64uhilo, .Mul64uover, .Neq8, .Neq16, .Neq32, .Neq64, .NeqB, .Or8, .Or16, .Or32, .Or64,
   .OrB, .Xor8, .Xor16, .Xor32, .Xor64, .EqPtr, .NeqPtr, .Add32F, .Add64F, .Mul32F, .Mul64F,
   .Eq32F, .Eq64F, .Neq32F, .Neq64F]

mutual
/-- Match pattern `q` at value `w` (position `p`) in `M`. `sw`: the choices at commutative
nodes in preorder (`true`: first two arguments swapped, only at `commOps`), consumed. Every op
node is a term node (`termOp`): its value is its op's `evalPure`. -/
def matchPat (M : Defs) : Pat → Path → ID → List Bool → Option (Inst × List Bool)
  | .op o _ _ _ _ ar args comm, p, w, sw =>
    match M.get? w with
    | none => none
    | some x =>
      if x.op != o || !termOp o || x.args.size != args.length ||
          !(match ar with | .fixed | .exact _ => true | _ => false) then none
      else
        let (ids, sw) :=
          if comm then
            match sw with
            | c :: sw => (if c && commOps.contains o then swap01 x.args.toList else x.args.toList, sw)
            | [] => (x.args.toList, [])
          else (x.args.toList, sw)
        match matchPats M args p 0 ids sw with
        | none => none
        | some (I, sw) => some ((p, w) :: I, sw)
  | _, p, w, sw => some ([(p, w)], sw)
def matchPats (M : Defs) : List Pat → Path → Nat → List ID → List Bool → Option (Inst × List Bool)
  | [], _, _, [], sw => some ([], sw)
  | q :: qs, p, i, a :: as, sw =>
    match matchPat M q (i :: p) a sw with
    | none => none
    | some (I, sw) =>
      match matchPats M qs p (i + 1) as sw with
      | none => none
      | some (J, sw) => some (I ++ J, sw)
  | _, _, _, _, _ => none
end

mutual
/-- The number of commutative nodes of a pattern. -/
def Pat.commutes : Pat → Nat
  | .op _ _ _ _ _ _ args comm => (if comm then 1 else 0) + Pat.commutess args
  | _ => 0
def Pat.commutess : List Pat → Nat
  | [] => 0
  | q :: qs => Pat.commutes q + Pat.commutess qs
end

/-- All choice lists of length `n`. -/
def choices : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (choices n).flatMap fun l => [false :: l, true :: l]

/-- The static instance environment: node fields from the definitions, leaf values `poison`
(the checks never read them: `same` is checked by IDs, `sameOK`). -/
def env (tabs : Tables) (M : Defs) (I : Inst) : PEnv where
  leaf _ := .poison
  ty p := ((M.get? (I.at p)).map fun x => tabs.ty x.type).getD .other
  auxInt p := ((M.get? (I.at p)).map (·.auxInt)).getD 0
  aux p := ((M.get? (I.at p)).map (·.aux)).getD none

/-- The oracle of the validator: an unmodelled boolean expression is `true` (so the oracle is
`Oracle.BoolTyped`: every expression `exprTy` types `bool` gets a boolean), others `other`;
result fields come from the built nodes (`fields`: per result node, its expressions and the
built value). -/
def oracle (vtys : List GoTy) (tabs : Tables) (nodes : List (RNode × Value)) : Oracle where
  dv e := if exprTy [] e == .bool || exprTy vtys e == .bool then .bool true else .other
  ty e := ((nodes.find? fun (n, _) => match n.ty with
      | some te => te == e | none => false).map fun (_, u) => tabs.ty u.type).getD .other
  auxInt e := ((nodes.find? fun (n, _) => match n.auxInt with
      | some ae => ae == e | none => false).map (·.2.auxInt)).getD 0
  aux e := ((nodes.find? fun (n, _) => match n.aux with
      | some xe => xe == e | none => false).map (·.2.aux)).getD none
  val _ := .poison

/-- `DV.ty t = d`. -/
def dvTyEq (t : Sem.Ty) : DV → Bool
  | .ty t' => GoFV.Opt.CSE.tyEq t t'
  | _ => false

/-- `auxIntDV aty a = d`. -/
def dvAuxIntEq : DV → DV → Bool
  | .int a, .int b => a == b
  | .bool a, .bool b => a == b
  | .f64 a, .f64 b => a == b
  | .f32 a, .f32 b => a == b
  | .other, .other => true
  | _, _ => false

/-- The value bound to a value variable: its position. -/
def DV.pos? : DV → Option Path
  | .val _ p => p
  | _ => none

mutual
/-- `Pat.cons` on the static instance, with `same` by IDs. -/
def consOK (ev : Expr → DV) (σ : Nat → DV) (e : PEnv) (I : Inst) (p : Path) : Pat → Bool
  | .wild | .bind _ => true
  | .same x =>
    match σ x with
    | .val _ (some p') => I.at p' == I.at p
    | _ => false
  | .op o _ ty ai _ _ args _ =>
    (match ty with | .eq te => dvTyEq (e.ty p) (ev te) | _ => true) &&
    (match ai with | .eq ae => dvAuxIntEq (auxIntDV o.auxType (e.auxInt p)) (ev ae) | _ => true) &&
    conssOK ev σ e I p 0 args
def conssOK (ev : Expr → DV) (σ : Nat → DV) (e : PEnv) (I : Inst) (p : Path) (i : Nat) :
    List Pat → Bool
  | [] => true
  | q :: qs => consOK ev σ e I (i :: p) q && conssOK ev σ e I p (i + 1) qs
end

/-- `auxIntOk` as a test. -/
def auxIntOkB (aty : AuxType) (a : Int64) : Bool :=
  match aty with
  | .Bool => a == 0 || a == 1
  | .Float32 | .Float64 => !IEEE.isNaN .b64 (BitVec.ofInt 64 a.toInt)
  | _ => true

mutual
/-- `Pat.wf` on the instance. -/
def wfOK (e : PEnv) (p : Path) : Pat → Bool
  | .op o _ _ _ _ _ args _ => auxIntOkB o.auxType (e.auxInt p) && wfsOK e p 0 args
  | _ => true
def wfsOK (e : PEnv) (p : Path) (i : Nat) : List Pat → Bool
  | [] => true
  | q :: qs => wfOK e (i :: p) q && wfsOK e p (i + 1) qs
end

mutual
/-- The rule variables naming op nodes of the pattern (`x:(Op …)`). -/
def Pat.opNames : Pat → List Nat
  | .op _ name _ _ _ _ args _ => name.toList ++ Pat.opNamess args
  | _ => []
def Pat.opNamess : List Pat → List Nat
  | [] => []
  | q :: qs => Pat.opNames q ++ Pat.opNamess qs
end

mutual
/-- The variables of the `same x` leaves of the pattern. -/
def Pat.sames : Pat → List Nat
  | .same x => [x]
  | .op _ _ _ _ _ _ args _ => Pat.samess args
  | _ => []
def Pat.samess : List Pat → List Nat
  | [] => []
  | q :: qs => Pat.sames q ++ Pat.samess qs
end

/-- The top node is unnamed and `same x` only repeats a leaf variable (the term proof gives a
leaf and a named op node the values of different fuels, `GoFV.Proof.Term`). -/
def patOK (pat : Pat) : Bool :=
  (match pat with | .op _ none _ _ _ _ _ _ => true | _ => false) &&
  (Pat.sames pat).all fun x => !(Pat.opNames pat).contains x

/-- Comparisons (incl. pointer, interface, slice, float and memory comparisons), nil checks
(`IsNonNil`) and boolean ops: their result is a boolean (or `poison`). -/
def boolOp : Op → Bool
  | .Eq8 | .Neq8 | .Less8 | .Less8U | .Leq8 | .Leq8U | .Eq16 | .Neq16 | .Less16 | .Less16U
  | .Leq16 | .Leq16U | .Eq32 | .Neq32 | .Less32 | .Less32U | .Leq32 | .Leq32U | .Eq64 | .Neq64
  | .Less64 | .Less64U | .Leq64 | .Leq64U | .AndB | .OrB | .EqB | .NeqB | .Not | .ConstBool
  | .IsInBounds | .IsSliceInBounds | .EqPtr | .NeqPtr | .EqInter | .NeqInter | .EqSlice
  | .NeqSlice | .MemEq | .IsNonNil
  | .Eq32F | .Neq32F | .Less32F | .Leq32F | .Eq64F | .Neq64F | .Less64F | .Leq64F => true
  | _ => false

/-- Integer and float ops whose result is an integer of width `w` (or `poison`; a float is its
bits, `Sem/Float.lean`); `Ctz`/`BitLen`/`PopCount`/`Slicemask` produce their type's width. -/
def intOpWidth (op : Op) (w : Sem.Width) : Bool :=
  match op with
  | .Add8 | .Sub8 | .Mul8 | .And8 | .Or8 | .Xor8 | .Neg8 | .Com8 | .Div8 | .Div8u | .Mod8
  | .Mod8u | .Const8 | .BitRev8 | .RotateLeft8 | .Trunc16to8 | .Trunc32to8 | .Trunc64to8
  | .CvtBoolToUint8
  | .Lsh8x8 | .Rsh8x8 | .Rsh8Ux8 | .Lsh8x16 | .Rsh8x16 | .Rsh8Ux16 | .Lsh8x32 | .Rsh8x32
  | .Rsh8Ux32 | .Lsh8x64 | .Rsh8x64 | .Rsh8Ux64 => w == .w8
  | .Add16 | .Sub16 | .Mul16 | .And16 | .Or16 | .Xor16 | .Neg16 | .Com16 | .Div16 | .Div16u
  | .Mod16 | .Mod16u | .Const16 | .BitRev16 | .RotateLeft16 | .Bswap16 | .SignExt8to16
  | .ZeroExt8to16 | .Trunc32to16 | .Trunc64to16
  | .Lsh16x8 | .Rsh16x8 | .Rsh16Ux8 | .Lsh16x16 | .Rsh16x16 | .Rsh16Ux16 | .Lsh16x32
  | .Rsh16x32 | .Rsh16Ux32 | .Lsh16x64 | .Rsh16x64 | .Rsh16Ux64 => w == .w16
  | .Add32 | .Sub32 | .Mul32 | .And32 | .Or32 | .Xor32 | .Neg32 | .Com32 | .Div32 | .Div32u
  | .Mod32 | .Mod32u | .Const32 | .BitRev32 | .RotateLeft32 | .Bswap32 | .Hmul32
  | .Hmul32u | .SignExt8to32 | .ZeroExt8to32 | .SignExt16to32 | .ZeroExt16to32
  | .Trunc64to32
  | .Lsh32x8 | .Rsh32x8 | .Rsh32Ux8 | .Lsh32x16 | .Rsh32x16 | .Rsh32Ux16 | .Lsh32x32
  | .Rsh32x32 | .Rsh32Ux32 | .Lsh32x64 | .Rsh32x64 | .Rsh32Ux64 => w == .w32
  | .Add64 | .Sub64 | .Mul64 | .And64 | .Or64 | .Xor64 | .Neg64 | .Com64 | .Div64 | .Div64u
  | .Mod64 | .Mod64u | .Const64 | .BitRev64 | .RotateLeft64 | .Bswap64 | .Hmul64
  | .Hmul64u | .Avg64u | .Min64 | .Min64u | .Max64 | .Max64u | .SignExt8to64
  | .ZeroExt8to64 | .SignExt16to64 | .ZeroExt16to64 | .SignExt32to64 | .ZeroExt32to64
  | .Lsh64x8 | .Rsh64x8 | .Rsh64Ux8 | .Lsh64x16 | .Rsh64x16 | .Rsh64Ux16 | .Lsh64x32
  | .Rsh64x32 | .Rsh64Ux32 | .Lsh64x64 | .Rsh64x64 | .Rsh64Ux64 => w == .w64
  | .Add32F | .Sub32F | .Mul32F | .Div32F | .Neg32F | .Min32F | .Max32F | .Sqrt32 | .Round32F
  | .Cvt32to32F | .Cvt64to32F | .Cvt32Uto32F | .Cvt64Uto32F | .Cvt32Fto32 | .Cvt64Fto32
  | .Cvt32Fto32U | .Cvt64Fto32U | .Cvt64Fto32F | .Const32F => w == .w32
  | .Add64F | .Sub64F | .Mul64F | .Div64F | .Neg64F | .Min64F | .Max64F | .Sqrt | .Floor | .Ceil
  | .Trunc | .Round | .RoundToEven | .Abs | .Copysign | .FMA | .Round64F | .Cvt32to64F
  | .Cvt64to64F | .Cvt32Uto64F | .Cvt64Uto64F | .Cvt32Fto64 | .Cvt64Fto64 | .Cvt32Fto64U
  | .Cvt64Fto64U | .Cvt32Fto64F | .Const64F => w == .w64
  | .Ctz8 | .Ctz16 | .Ctz32 | .Ctz64 | .Ctz8NonZero | .Ctz16NonZero | .Ctz32NonZero
  | .Ctz64NonZero | .BitLen8 | .BitLen16 | .BitLen32 | .BitLen64 | .PopCount8 | .PopCount16
  | .PopCount32 | .PopCount64 | .Slicemask => true
  | _ => false

/-- `evalPure op ty …` always has shape `ty` (integer, float and boolean ops). -/
def natShape (op : Op) (ty : Sem.Ty) : Bool :=
  match ty with
  | .bool => boolOp op
  | .int w => intOpWidth op w
  | _ => false

/-- Pointer ops whose value has shape `ty` when their first argument has the shape
`argShapeOk` asks for (`OffPtr`, `AddPtr`, `PtrIndex` at a pointer shape, `Convert` between a
pointer and a 64-bit integer). -/
def ptrTop (op : Op) (ty : Sem.Ty) : Bool :=
  match op with
  | .OffPtr | .AddPtr | .PtrIndex => isPtrTy ty
  | .Convert => isPtrTy ty || isInt64Ty ty
  | _ => false

/-- Constant ops of a pointer or composite shape (`ConstNil`, `ConstSlice`, `ConstInterface`)
whose constant has the shape `ty`; their value depends on nothing but the op (an integer word or
a composite of them: no instance reads it, `Val.hasTyC`). -/
def constTop (op : Op) (ty : Sem.Ty) : Bool :=
  (op matches .ConstNil | .ConstSlice | .ConstInterface) &&
    (@Sem.evalPure Sem.Addrs.fixed op ty 0 none []).hasTyC ty

/-- The string shape (`Sem.tyOf` of a `STRING`). -/
def strTy : Sem.Ty := .str

/-- Table-evaluated ops (`GoFV.Proof.Rules.opVal`) at the shape of their value: `Addr` (a
pointer or `poison`) at a pointer shape, `ConstString` (a string or `poison`) at the string
shape. -/
def frameTop (op : Op) (ty : Sem.Ty) : Bool :=
  (op == .Addr && isPtrTy ty) || (op == .ConstString && GoFV.Opt.CSE.tyEq ty strTy)

/-- The top op of a match produces a value of its type's shape `ty` (`natShape`, `ptrTop` under
`Pat.argsOK`, `constTop`, `frameTop`). -/
def topOK (op : Op) (ty : Sem.Ty) : Bool :=
  natShape op ty || ptrTop op ty || constTop op ty || frameTop op ty

/-- The component a selection op reads (`Comp.select`, `Comp.selectAux`): `StringPtr`,
`SlicePtr`, `SlicePtrUnchecked`, `ITab`, `ComplexReal` 0; `StringLen`, `SliceLen`, `IData`,
`ComplexImag` 1; `SliceCap` 2; `StructSelect [i]`, `ArraySelect [i]` the auxint `i ≥ 0`. -/
def selIndex? (op : Op) (ai : Int64) : Option Nat :=
  match op with
  | .StringPtr | .SlicePtr | .SlicePtrUnchecked | .ITab | .ComplexReal => some 0
  | .StringLen | .SliceLen | .IData | .ComplexImag => some 1
  | .SliceCap => some 2
  | .StructSelect | .ArraySelect => if ai.toInt < 0 then none else some ai.toInt.toNat
  | _ => none

/-- A value of shape `f` has shape `ty`: `shapeSub`, or a 64-bit integer at a pointer shape (an
`.int .w64` value, or a pointer without a concrete address, has every pointer shape,
`Val.hasTy`; the interface's `uintptr` itab word read by an `ITab` typed `*uint8`, issue #17). -/
def compSub (f ty : Sem.Ty) : Bool :=
  shapeSub f ty || ((f matches .int .w64) && (ty matches .ptr _))

/-- Component `k` of a value of shape `argTy` has shape `ty`: the component's shape is `ty`'s
(`compSub`) or missing (the selection is `poison`), or the argument is a scalar (the
selection is `poison`). -/
def selShapeOK (k : Nat) (ty argTy : Sem.Ty) : Bool :=
  match argTy.asAgg with
  | .agg fs _ => match fs[k]? with
    | some (_, f) => compSub f ty
    | none => true
  | .int _ | .bool | .ptr _ => true
  | _ => false

/-- A selection op of shape `ty` (auxint `ai`) whose argument has shape `argTy` produces a value
of shape `ty` (issue #17: the dec rules' tops). -/
def selTop (op : Op) (ty : Sem.Ty) (ai : Int64) (argTy : Sem.Ty) : Bool :=
  match selIndex? op ai with
  | some k => selShapeOK k ty argTy
  | none => false

/-- Integer, boolean and pointer shapes. -/
def scalarTy : Sem.Ty → Bool
  | .int _ | .bool | .ptr _ => true
  | _ => false

/-- Shapes a `Load` decodes to a value of the shape: scalars, aggregates of scalars (strings,
slices, interfaces, complex numbers; issue #17) and the empty shape (zero-size types,
`generic.rules:1004`). -/
def loadShape (t : Sem.Ty) : Bool :=
  match t.asAgg with
  | .agg fs _ => fs.all (scalarTy ·.2)
  | .empty => true
  | t => scalarTy t

/-- A `Load` at a `loadShape`. -/
def loadTop (op : Op) (ty : Sem.Ty) : Bool := op == .Load && loadShape ty

/-- A value of shape `f` has shape `t`: `compSub`, or a pointer shape at the 64-bit integer shape
(a pointer without an integer form has both word shapes, `Val.hasTy`). -/
def armSub (f t : Sem.Ty) : Bool := compSub f t || (isPtrTy f && isInt64Ty t)

/-- A `CondSelect` whose arms' shapes are its own (`armSub`): its value is an arm or `poison`
(`branchelim`'s selects of a `uintptr` between two symbol addresses, `generic.rules:292–294`). -/
def condTop (op : Op) (e : PEnv) : Bool :=
  op == .CondSelect && armSub (e.ty [0]) (e.ty []) && armSub (e.ty [1]) (e.ty [])

/-- The top op of a match at the instance `e` produces a value of its type's shape: `topOK`, a
selection from its first argument (`selTop`), a `Load` (`loadTop`), or a `CondSelect`
(`condTop`). -/
def topAll (op : Op) (e : PEnv) : Bool :=
  topOK op (e.ty []) || selTop op (e.ty []) (e.auxInt []) (e.ty [0]) || loadTop op (e.ty []) ||
    condTop op e

/-- A `SliceMake` at a slice shape: retyping its value at the shape gives the value or `poison`
(`Val.ofSlice`; the components have their shapes, `Pat.argsOK`), so the matched value is
`poison` or the raw value, which then has the shape (`generic.rules:1053`). -/
def makeTop (op : Op) (ty : Sem.Ty) : Bool :=
  op == .SliceMake && GoFV.Proof.Rules.isSliceTy ty

mutual
/-- Every leaf of the pattern is a defined value. `Pat.typed` asks of the leaves that their
values have their type's shape: `Val.retype` produces a value of the shape at every shape
(`Val.retype_hasTy`, issue #108), aggregates (strings, slices, interfaces) included. -/
def leavesOK (M : Defs) (I : Inst) (p : Path) : Pat → Bool
  | .op _ _ _ _ _ _ args _ => leavessOK M I p 0 args
  | _ => (M.get? (I.at p)).isSome
def leavessOK (M : Defs) (I : Inst) (p : Path) (i : Nat) : List Pat → Bool
  | [] => true
  | q :: qs => leavesOK M I (i :: p) q && leavessOK M I p (i + 1) qs
end

/-- The value a result argument refers to (`none` for a Go-expression argument: not checked). -/
def argID (σ : Nat → DV) (I : Inst) (ids : List ID) : RArg → Option ID
  | .var x => (DV.pos? (σ x)).map I.at
  | .node j => ids[j]?
  | .expr _ => none

/-- Result node `n` was built as `u` (`nodeDen`'s fields; `topTy`: the shape of `v`'s type). -/
def nodeOK (tabs : Tables) (ev : Expr → DV) (or : Oracle) (σ : Nat → DV) (I : Inst)
    (ids : List ID) (topTy : Sem.Ty) (n : RNode) (u : Value) : Bool :=
  u.op == n.op && termOp n.op &&
  GoFV.Opt.CSE.tyEq (tabs.ty u.type) (match n.ty with
    | some te => match ev te with
      | .ty t => t
      | _ => or.ty te
    | none => topTy) &&
  u.auxInt == (match n.auxInt with
    | some ae => (toAuxIntD n.op.auxType (ev ae)).getD (or.auxInt ae)
    | none => 0) &&
  u.aux == (match n.aux with
    | some xe => or.aux xe
    | none => none) &&
  u.args.size == n.args.length &&
  (n.args.zip u.args.toList).all fun (a, w) => argID σ I ids a == some w

/-- A `Copy` of shape `s` of a value of shape `t` is the identity on it: the same shape, or two
pointer shapes (`Val.retype` at a pointer shape ignores the element size). -/
def copyCompat (s t : Sem.Ty) : Bool :=
  GoFV.Opt.CSE.tyEq s t || (s matches .ptr _ && t matches .ptr _)

/-- An `@b` result (`… => @x.Block (…)`, issue #17): node 0 is built fresh as `t` (in block
`b`, which the term denotations do not read) and `v` becomes `Copy t`, the identity on `t`'s
value (`copyCompat`). The copy has `t`'s type, as Go's `copyOf` gives it, which need not be `v`'s
type id (`(SlicePtr x:(Load <t> …)) => @x.Block (Load <t.Elem().PtrTo()> …)` at a selection typed
`*go.shape.uint16` builds a `*uint16`). -/
def blockTopOK (tabs : Tables) (M : Defs) (v u0 : Value) (us : List Value) (t : ID) : Bool :=
  t != v.id && (M.get? t).isNone && !((us.map (·.id)).drop 1).contains t &&
  u0.op == .Copy && u0.args == #[t] && u0.auxInt == 0 && u0.aux == none &&
  us.head?.any fun u => copyCompat (tabs.ty u0.type) (tabs.ty u.type)

/-- The built definitions are the result's (`resDen`): `copy` of a bound value, or a `build`
whose other nodes are fresh and whose node 0 is `v` (in place) or, for an `@b` result, fresh
with `v` a copy of it (`blockTopOK`). -/
def resultOK (tabs : Tables) (M : Defs) (ev : Expr → DV) (or : Oracle) (σ : Nat → DV)
    (I : Inst) (r : Rule) (v : Value) (defs : List Value) : Bool :=
  let topTy := tabs.ty v.type
  match r.result, r.block, defs with
  | .copy ce, none, [u] =>
    match DV.pos? (ev ce) with
    | some p => u.id == v.id && u.op == .Copy && u.args == #[I.at p] &&
        (M.get? (I.at p)).any (·.type == u.type) && I.at p != v.id && u.auxInt == 0 && u.aux == none
    | none => false
  | .build nodes, b, u0 :: us =>
    let ids := us.map (·.id)
    u0.id == v.id &&
    (match ids.head? with
      | some t => match b with
        | none => t == v.id
        | some _ => blockTopOK tabs M v u0 us t
      | none => false) &&
    us.length == nodes.length &&
    (ids.drop 1).all (fun x => (M.get? x).isNone) && (ids.drop 1).Nodup &&
    !(ids.drop 1).contains v.id &&
    (nodes.zip us).all fun (n, u) => nodeOK tabs ev or σ I ids topTy n u
  | _, _, _ => false

/-- The string aux bound to rule variable `x` (at the aux field of the pattern node
`Pat.auxPos x`), on the instance `e`. -/
def strOf (tabs : Tables) (e : PEnv) (pat : Pat) (x : Nat) : Option (GoStr × GoStr) :=
  (Pat.auxPos x [] pat).bind fun p => strAux? tabs (e.aux p)

/-- The frame helpers of a built node `u` of result node `n` (`GoFV.Proof.Rules.FrameOK`): an
aux `fe.StringData(x)` names the data symbol of the non-empty string aux bound to `x`, an
auxint `int64(len(x))` is the string's length, an aux `{x}` is the aux bound to `x`, an auxint
shift `a << b`/`a >> b` shifts by a nonnegative amount. -/
def frameNodeOK (tabs : Tables) (ev : GoFV.Rules.Expr → DV) (e : PEnv) (pat : Pat) (n : RNode)
    (u : Value) : Bool :=
  (match n.aux.bind strDataVar? with
    | some x => match strOf tabs e pat x with
      | some (s, d) => s.size != 0 && symName? tabs u.aux == some d
      | none => false
    | none => true) &&
  (match n.auxInt.bind lenVar? with
    | some x => match strOf tabs e pat x with
      | some (s, _) => u.auxInt == Int64.ofNat s.size
      | none => false
    | none => true) &&
  (match n.aux.bind auxVar? with
    | some x => match Pat.auxPos x [] pat with
      | some p => u.aux == e.aux p
      | none => false
    | none => true) &&
  (match n.auxInt.bind shiftAmt? with
    | some b => match ev b with
      | .int i => decide (0 ≤ i)
      | _ => false
    | none => true)

/-- The condition's conjuncts `x == ""` hold of the string aux bound to `x`, its conjuncts
`isSamePtr(x, y)` of leaves `x`, `y` match the same value, its conjuncts
`x.NumElem() == 1` have a type `x` of the shape of one field at offset 0 that fills it, its
conjuncts `x.Size() == 0` a type `x` of the empty shape, and the positions `same`
(`GoFV.Proof.Rules.sameLeaves`) match the same value (`GoFV.Proof.Rules.FrameOK`). -/
def condFrameOK (tabs : Tables) (ev : GoFV.Rules.Expr → DV) (e : PEnv) (I : Inst) (pat : Pat)
    (cond : Option GoFV.Rules.Expr) (same : List (Path × Path)) : Bool :=
  ((cond.map emptyStrVars).getD []).all (fun x => match strOf tabs e pat x with
    | some (s, _) => s.size == 0
    | none => false) &&
  ((cond.map samePtrVars).getD []).all (fun (x, y) =>
    match Pat.leafPos x [] pat, Pat.leafPos y [] pat with
    | some p, some q => I.at p == I.at q
    | _, _ => false) &&
  ((cond.map numElem1Vars).getD []).all (fun x => match ev (.var x) with
    | .ty (.agg [(0, f)] n) => f.size == n
    | _ => false) &&
  ((cond.map size0Vars).getD []).all (fun x => match ev (.var x) with
    | .ty .empty => true
    | _ => false) &&
  same.all fun (p, q) => I.at p == I.at q

/-- How `isNonNegative` (`rewrite.go`) decides an op whose value is an integer of width `w`. -/
inductive NNKind where
  /-- `Const<w>`: its constant, retyped to the node's type. -/
  | const (w : Sem.Width)
  /-- Nonnegative at every integer type (`Ctz*`, `BitLen*`: at most 64; `none`) or at `w`
  (`ZeroExt*to<w>`). -/
  | always (w : Option Sem.Width)
  /-- `Rsh<w>Ux64` by a positive `Const64`. -/
  | rshuC (w : Sem.Width)
  /-- Nonnegative when the first argument is (`Rsh<w>x*`, `SignExt*to<w>`). -/
  | arg0 (w : Sem.Width)
  /-- When an argument is (`And<w>`). -/
  | anyArg (w : Sem.Width)
  /-- When every argument is (`Or<w>`, `Xor<w>`, `Div<w>`, `Mod<w>`). -/
  | allArgs (w : Sem.Width)
  /-- A length or capacity (`StringLen`, `SliceLen`, `SliceCap`) of a string or slice shaped
  argument, at `int64`: `retype` gives values of these shapes `0 ≤ len ≤ cap`
  (`Val.hasTy_str`, `Val.hasTy_slice`). -/
  | len

/-- The ops `isNonNegative` looks through, by kind. -/
def nnTable : List (Op × NNKind) :=
  [(.Const64, .const .w64), (.Const32, .const .w32), (.Const16, .const .w16),
   (.Const8, .const .w8),
   (.ZeroExt8to64, .always (some .w64)), (.ZeroExt16to64, .always (some .w64)),
   (.ZeroExt32to64, .always (some .w64)), (.ZeroExt8to32, .always (some .w32)),
   (.ZeroExt16to32, .always (some .w32)), (.ZeroExt8to16, .always (some .w16)),
   (.Ctz64, .always none), (.Ctz32, .always none), (.Ctz16, .always none), (.Ctz8, .always none),
   (.Ctz64NonZero, .always none), (.Ctz32NonZero, .always none), (.Ctz16NonZero, .always none),
   (.Ctz8NonZero, .always none), (.BitLen64, .always none), (.BitLen32, .always none),
   (.BitLen16, .always none), (.BitLen8, .always none),
   (.Rsh64Ux64, .rshuC .w64), (.Rsh32Ux64, .rshuC .w32),
   (.Rsh64x64, .arg0 .w64), (.Rsh32x64, .arg0 .w32), (.Rsh8x64, .arg0 .w8),
   (.Rsh16x64, .arg0 .w16), (.Rsh32x32, .arg0 .w32), (.Rsh64x32, .arg0 .w64),
   (.SignExt32to64, .arg0 .w64), (.SignExt16to64, .arg0 .w64), (.SignExt8to64, .arg0 .w64),
   (.SignExt16to32, .arg0 .w32), (.SignExt8to32, .arg0 .w32),
   (.And64, .anyArg .w64), (.And32, .anyArg .w32), (.And16, .anyArg .w16), (.And8, .anyArg .w8),
   (.Mod64, .allArgs .w64), (.Mod32, .allArgs .w32), (.Mod16, .allArgs .w16),
   (.Mod8, .allArgs .w8), (.Div64, .allArgs .w64), (.Div32, .allArgs .w32),
   (.Div16, .allArgs .w16), (.Div8, .allArgs .w8), (.Or64, .allArgs .w64),
   (.Or32, .allArgs .w32), (.Or16, .allArgs .w16), (.Or8, .allArgs .w8),
   (.Xor64, .allArgs .w64), (.Xor32, .allArgs .w32), (.Xor16, .allArgs .w16),
   (.Xor8, .allArgs .w8), (.StringLen, .len), (.SliceLen, .len), (.SliceCap, .len)]

/-- The kind of `op` in `nnTable`. -/
def nonNegKind (op : Op) : Option NNKind := (nnTable.find? (·.1 == op)).map (·.2)

/-- `t` is the integer shape of width `w`. -/
def isIntW (t : Sem.Ty) (w : Sem.Width) : Bool :=
  match t with
  | .int w' => w' == w
  | _ => false

/-- `t` is the string or a slice shape. -/
def lenShape (t : Sem.Ty) : Bool :=
  match t with
  | .str | .slice _ => true
  | _ => false

/-- `isNonNegative(x)` (`rewrite.go`) on the definitions `D`, with `k` levels: every
evaluation of `x` as a term (`GoFV.Proof.Term.den`) is then a nonnegative integer or `poison`
(`GoFV.Proof.Pass.Rewrite.nonNegD_den`). Unlike Go it asks each node's type to have its op's
width (a narrower type would truncate the value). -/
def nonNegD (tabs : Tables) (D : ID → Option Value) : Nat → ID → Bool
  | 0, _ => false
  | k + 1, x =>
    match D x with
    | none => false
    | some v =>
      let ty := tabs.ty v.type
      termOp v.op && match nonNegKind v.op with
      | none => false
      | some (.const w) => ((Sem.Conv.const w v.auxInt).retypeC ty).nonNeg
      | some (.always w?) => match ty with
        | .int rw => w?.all (· == rw)
        | _ => false
      | some (.rshuC w) => isIntW ty w && match v.args[1]?.bind D with
        | some b => b.op == .Const64 && b.auxInt > 0 && isIntW (tabs.ty b.type) .w64
        | none => false
      | some (.arg0 w) => isIntW ty w && match v.args[0]? with
        | some a => nonNegD tabs D k a
        | none => false
      | some (.anyArg w) => isIntW ty w && v.args.any (nonNegD tabs D k)
      | some (.allArgs w) => isIntW ty w && v.args.all (nonNegD tabs D k)
      | some .len => isIntW ty .w64 && match v.args[0]?.bind D with
        | some a => lenShape (tabs.ty a.type)
        | none => false

/-- Levels `nonNegD` looks through. -/
def nnFuel : Nat := 16

/-- `Pat.nonNegOK` decided on the definitions `D` (those after the event): the leaf of each
`isNonNegative(x)` conjunct is `nonNegD`. -/
def nonNegOKD (tabs : Tables) (D : ID → Option Value) (I : Inst) (pat : Pat) :
    Option GoFV.Rules.Expr → Bool
  | some c => (nonNegVars c).all fun x => match Pat.leafPos x [] pat with
    | some p => nonNegD tabs D nnFuel (I.at p)
    | none => true
  | none => true

/-- The rule event `(v, r, defs)` is a sound instance of `r` on `M`. The definition at `v` is
`v`'s (its ID, which the result's nodes are compared with), and the matched values below the
top are not `v` (no cyclic match). -/
def ruleOK (tabs : Tables) (M : Defs) (r : Rule) (v : ID) (defs : List Value) : Bool :=
  Pat.arityOk r.pat && patOK r.pat &&
  match M.get? v with
  | none => false
  | some x =>
    termOp x.op && x.id == v &&
    (choices (Pat.commutes r.pat)).any fun sw =>
      match matchPat M r.pat [] v sw with
      | none => false
      | some (I, _) =>
        let e := env tabs M I
        let vtys := r.vars.map (·.ty)
        let σ := @sigmaT Sem.Addrs.fixed tabs e r.pat
        let nodes := match r.result, defs with
          | .build ns, _ :: us => ns.zip us
          | _, _ => []
        let or := oracle vtys tabs nodes
        let ev := evalE vtys σ or e (@Pat.denT Sem.Addrs.fixed tabs e [] r.pat)
        I.tail.all (·.2 != v) &&
        consOK ev σ e I [] r.pat && wfOK e [] r.pat &&
        (match r.cond with
          | some c => match ev c with | .bool true => true | _ => false
          | none => true) &&
        (match r.pat with
          | .op o _ _ _ _ _ _ _ => topAll o e || makeTop o (e.ty []) || GoFV.Proof.Rules.anyTop r
          | _ => false) &&
        Pat.argsOK e.ty [] r.pat &&
        leavesOK M I [] r.pat &&
        resultOK tabs M ev or σ I r x defs &&
        nodes.all (fun (n, u) => frameNodeOK tabs ev e r.pat n u) &&
        condFrameOK tabs ev e I r.pat r.cond (GoFV.Proof.Rules.sameLeaves r) &&
        nonNegOKD tabs (defs.foldl (fun M u => M.put u.id u) M).get? I r.pat r.cond

/-- `w` is `a`, or reached from `a` through at most `n` `Copy`s each compatible with its
argument (`copyCompat`: the identity on its argument's value). -/
def copyReach (tabs : Tables) (M : Defs) : Nat → ID → ID → Bool
  | 0, a, w => a == w
  | n + 1, a, w =>
    a == w ||
    match M.get? a with
    | some x =>
      x.op == .Copy && x.args.size == 1 &&
      (match M.get? x.args[0]! with
        | some y => copyCompat (tabs.ty x.type) (tabs.ty y.type)
        | none => false) &&
      copyReach tabs M n x.args[0]! w
    | none => false

/-- The replayed terminator of a block (issue #151): kind, controls, and whether its successors
are swapped relative to the input's. -/
structure BState where
  kind : BlockKind
  ctrls : Array ID
  swapped : Bool
  deriving Inhabited

/-- The replayed terminators of the blocks the log changed, latest first. -/
abbrev BMap := List (ID × BState)

/-- The terminator of `b` in the replay: the latest replayed one, else the input's. -/
def bstate (f : Func) (B : BMap) (b : ID) : Option BState :=
  match B.lookup b with
  | some st => some st
  | none => (f.block? b).map fun fb => { kind := fb.kind, ctrls := fb.controls, swapped := false }

/-- Two successors swapped (`Func.swapSuccessors`). -/
def swapS (s : Array Edge) : Array Edge := #[s[1]!, s[0]!]

/-- The definitions (`ruleOK`'s `defs`) that the control rule `cr` of a block rule makes of the
control `x` when the block's new controls are `nc` (`BlockRule.ctrlRule`): the in-place `build`
of a `Not` of the new control or of the constant, or the `copy` of the new control. -/
def ctrlDefs (cr : Rule) (x : Value) (nc : Array ID) : Option (List Value) :=
  match cr.result, nc.toList with
  | .build [n], [c] =>
    let u := { x with op := n.op, args := #[c], auxInt := 0, aux := none }
    some [u, u]
  | .build [n], [] =>
    let ai : Int64 := match n.auxInt with
      | some (.lit _ (.bool true)) => 1
      | _ => 0
    let u := { x with op := n.op, args := #[], auxInt := ai, aux := none }
    some [u, u]
  | .copy _, [c] => some [{ x with op := .Copy, args := #[c], auxInt := 0, aux := none }]
  | _, _ => none

/-- The boolean shape. -/
def isBool : Sem.Ty → Bool
  | .bool => true
  | _ => false

/-- A block-rule event (rule `br`, new controls `nc`) on the replayed terminator `st`: `st` is an
`If` on one control `c` of boolean shape, `br`'s control rule fires at `c` (`ruleOK`) with the
definitions `ctrlDefs` makes, and the new terminator has `br`'s kind (with one control for `If`,
none for `First`), the controls `nc` and the swap flag toggled by `br`'s swap. -/
def blockOK (tabs : Tables) (M : Defs) (br : BlockRule) (st : BState) (nc : Array ID) :
    Option (List Value × BState) :=
  match BlockRule.ctrlRule br, st.kind, st.ctrls.toList with
  | some cr, .If, [c] =>
    match M.get? c with
    | some x =>
      match ctrlDefs cr x nc with
      | some defs =>
        if isBool (tabs.ty x.type) && nc.size == (if br.newKind == .If then 1 else 0) &&
            ruleOK tabs M cr c defs then
          some (defs, { kind := br.newKind, ctrls := nc, swapped := st.swapped != br.swapSuccs })
        else none
      | none => none
    | none => none
  | _, _, _ => none

/-! ## Struct-load expansions (issue #151)

`(Load <t> _ _) && t.IsStruct() && … => rewriteStructLoad(v)` (`generic.rules:974`) turns
`Load <t> p m` into `StructMake` of `Load <tᵢ> (OffPtr [oᵢ] p) m`, one per field, built fresh;
the event logs `v`'s new definition, then each field's `OffPtr` and `Load`
(`GoFV.Rules.Interp.structLoadDefs`). As terms over the atoms this refines the `Load` for every
memory value: a valid read of the struct's bytes reads each field's bytes at its offset, whose
pointer stays inside the block's window (`Sem.Mem.read`). -/

mutual
/-- Every field of an aggregate shape lies inside it, recursively: `decode` of the shape reads
only its own bytes. -/
def layoutOK : Sem.Ty → Bool
  | .agg fs n => layoutsOK n fs
  | _ => true
/-- `layoutOK` of the fields of an aggregate of `n` bytes. -/
def layoutsOK (n : Nat) : List (Nat × Sem.Ty) → Bool
  | [] => true
  | (o, t) :: fs => decide (o + t.size ≤ n) && layoutOK t && layoutsOK n fs
end

/-- The fields of a struct-load expansion of `Load <agg fs n> ptr mem`: arguments `as` of the
`StructMake`, built values `ds` (per field its `OffPtr [o] ptr` and `Load <t> that mem`). -/
def slFieldsOK (tabs : Tables) (ptr mem : ID) : List (Nat × Sem.Ty) → List ID → List Value → Bool
  | [], [], [] => true
  | (o, t) :: fs, a :: as, op :: ld :: ds =>
    op.op == .OffPtr && op.args == #[ptr] && op.auxInt == Int64.ofNat o &&
    (tabs.ty op.type matches .ptr _) &&
    ld.op == .Load && ld.args == #[op.id, mem] && GoFV.Opt.CSE.tyEq (tabs.ty ld.type) t &&
    a == ld.id &&
    slFieldsOK tabs ptr mem fs as ds
  | _, _, _ => false

/-- The event `(v, defs)` is a struct-load expansion of the `Load` `v` of `M`: `defs` is `v`'s new
definition, a `StructMake` of the same type, then the fresh `OffPtr` and `Load` of each field of
the `Load`'s aggregate shape, whose layout is well formed with every offset inside it. -/
def structLoadOK (tabs : Tables) (M : Defs) (v : ID) (defs : List Value) : Bool :=
  match M.get? v, defs with
  | some x, x' :: ds =>
    match tabs.ty x.type, x.args.toList with
    | .agg fs n, [ptr, mem] =>
      x.op == .Load && x.id == v && x'.id == v && x'.op == .StructMake && x'.type == x.type &&
      layoutsOK n fs && fs.all (·.1 < n) &&
      (ds.map (·.id)).all (fun y => (M.get? y).isNone) && (ds.map (·.id)).Nodup &&
      slFieldsOK tabs ptr mem fs x'.args.toList ds
    | _, _ => false
  | _, _ => false

/-- A struct-load expansion rule: `(Load …) && … => rewriteStructLoad(v)`; each instance is
validated by `structLoadOK`. -/
def structLoadShapeOK (r : Rule) : Bool :=
  match r.pat, r.result, r.block with
  | .op .Load .., .copy (.call "rewriteStructLoad" [.rsv .v] _), none => true
  | _, _, _ => false

/-! ## Selections of a `Make` (issue #17)

A rule `(Sel (Make …)) => …` with a copy result (`GoFV.Proof.Rules.makeSelShape`: `(ITab (IMake
itab _)) => itab`, `(StringLen (StringMake _ len)) => len`, the variadic `(StructSelect [i]
x:(StructMake ___)) => x.Args[i]` of `dec.rules:106`/`generic.rules:973`, …) makes the selection
`v` a `Copy` of the selected argument. Each such event is first validated per instance
(`makeSelOK`); the variadic ones have no `Rule.Sound` form and only this check. Component `k`
of a `Make` retyped at an aggregate shape is argument `k` retyped at the field's shape, so only
the selected argument matters: it is kept when its shape is the field's and the selection's
(`shapeSub`), or when all three are word shapes (`wordVal`, `wordTy`: the two word shapes have
the same values and retype alike, §3.2, #290; e.g. the interface's `uintptr` itab word read by a
pointer-typed `ITab`, or a pointer-typed itab `Phi` in an `IMake`); without a field `k` the
selection is `poison`. -/

/-- A 64-bit integer or pointer shape: the word shapes, which have the same values and retype
alike (`Val.hasTy_ptr_eq_i64`, `Val.retype_ptr_eq_i64`). -/
def wordTy : Sem.Ty → Bool
  | .int .w64 | .ptr _ => true
  | _ => false

/-- `a` is a value of `M` of a word shape (`wordTy`): its denotation has both word shapes, so
`retype` at either keeps it. -/
def wordVal (tabs : Tables) (M : Defs) (a : ID) : Bool :=
  (M.get? a).any fun w => wordTy (tabs.ty w.type)

/-- `copyReach`, or first a `Copy` at a word shape of a value of a word shape (`wordVal`: the
identity on its argument's value) and then `copyReach` from its argument: the `Copy <uintptr>` of
an `Addr <*uint8>` a phi elimination leaves (issue #17), whose shapes `copyCompat` does not
relate. -/
def copyReachW (tabs : Tables) (M : Defs) (n : Nat) (a w : ID) : Bool :=
  copyReach tabs M n a w ||
    match M.get? a with
    | some x => x.op == .Copy && x.args.size == 1 && wordTy (tabs.ty x.type) &&
        wordVal tabs M x.args[0]! && copyReach tabs M n x.args[0]! w
    | none => false

/-- `y` is a `Make` whose component `k` is its argument `a` (defined as `w`) at the shape the
selection `x` keeps: where `y`'s shape has a component `k`, `a`'s shape is that component's and
`x`'s (`shapeSub`), or all three are word shapes (`wordTy`). -/
def selArgOK (tabs : Tables) (M : Defs) (x y w : Value) (k : Nat) (a : ID) : Bool :=
  makeOp y.op &&
    match fieldShape? (tabs.ty y.type) k with
    | some fk =>
      (shapeSub (tabs.ty w.type) fk && shapeSub (tabs.ty w.type) (tabs.ty x.type)) ||
      (wordTy (tabs.ty w.type) && wordTy fk && wordTy (tabs.ty x.type))
    | none => true

/-- The argument the selection `x` reads: `x` selects component `k` (`selIndex?`) of `s`, the
resolver `r` takes `s` to a `Make` whose argument `k` is a defined value `a`, at a shape the
selection keeps (`selArgOK`). -/
def selArg (tabs : Tables) (M : Defs) (r : ID → ID) (x : Value) : Option ID :=
  match x.args.toList, selIndex? x.op x.auxInt with
  | [s], some k =>
    match M.get? (r s) with
    | some y =>
      match y.args[k]? with
      | some a =>
        match M.get? a with
        | some w => if selArgOK tabs M x y w k a then some a else none
        | none => none
      | none => none
    | none => none
  | _, _ => none

/-- `a` resolved within `n` steps through copies compatible with their argument (`copyCompat`)
and selections of a `Make`'s argument (`selArg`): a value whose denotation refines `a`'s (a
selection of a `Make` the replay kept, issue #17: `(StructSelect [0] (StructSelect [1] x))` of
`x = StructMake _ (StructMake p)` whose dropped inner `Make` Go made a copy of `p`). -/
def selRes (tabs : Tables) (M : Defs) : Nat → ID → ID
  | 0, a => a
  | n + 1, a =>
    match M.get? a with
    | some x =>
      if x.op == .Copy && x.args.size == 1 &&
          (M.get? x.args[0]!).any (fun y => copyCompat (tabs.ty x.type) (tabs.ty y.type)) then
        selRes tabs M n x.args[0]!
      else
        match selArg tabs M (selRes tabs M n) x with
        | some b => selRes tabs M n b
        | none => a
    | none => a

/-- Steps `makeSelOK` resolves a selection's argument through. -/
def selFuel : Nat := 8

/-- The event `(v, defs)` selects an argument of a `Make`: `v`'s selection reads `a` (`selArg`,
its argument resolved by `selRes`), and `defs` is `v` as `Copy a` at `a`'s type (`copyOf`). -/
def makeSelOK (tabs : Tables) (M : Defs) (v : ID) (defs : List Value) : Bool :=
  match M.get? v, defs with
  | some x, [u] =>
    match selArg tabs M (selRes tabs M selFuel) x with
    | some a =>
      match M.get? a with
      | some w => u.id == v && u.op == .Copy && u.args == #[a] && u.type == w.type
      | none => false
    | none => false
  | _, _ => false

/-! ## Selections of a `Load` without a condition (issue #17)

`(StructSelect [i] x:(Load <t> ptr mem)) => @x.Block (Load <v.Type> (OffPtr <v.Type.PtrTo()>
[t.FieldOff(int(i))] ptr) mem)` (`dec.rules:141`) and its `ArraySelect` form (`:132`,
`[t.Elem().Size()*i]`; `GoFV.Proof.Rules.loadSelShape`) read component `k` of a `Load` as a
`Load` of `v`'s type at an offset. Nothing in the rule ties `v`'s type to the field's, so each
instance is validated (`loadSelOK`), and only so: the `Load`'s shape is `agg fs n` with every
field inside it (`layoutsOK`) at an offset below `n`, field `k` is `(o, t)`, `v` becomes `Copy` of
a fresh `Load` of shape `t` (compatible with `v`'s, `copyCompat`) on a fresh pointer-shaped
`OffPtr [o]` of the `Load`'s pointer, from its memory. -/

/-- The event `(v, [u0, top, off])` reads component `k` of the `Load` that `v` selects from as a
`Load` at field `k`'s offset (above). -/
def loadSelOK (tabs : Tables) (M : Defs) (v : ID) (defs : List Value) : Bool :=
  match M.get? v, defs with
  | some x, [u0, top, off] =>
    match x.args.toList, selIndex? x.op x.auxInt with
    | [s], some k =>
      match M.get? s with
      | some y =>
        match tabs.ty y.type, y.args.toList with
        | .agg fs n, [p, m] =>
          match fs[k]? with
          | some (o, t) =>
            y.op == .Load && layoutsOK n fs && fs.all (·.1 < n) &&
            u0.id == v && u0.op == .Copy && u0.args == #[top.id] && u0.type == x.type &&
            u0.auxInt == 0 && u0.aux == none &&
            (M.get? top.id).isNone && (M.get? off.id).isNone && top.id != off.id &&
            top.op == .Load && top.args == #[off.id, m] && GoFV.Opt.CSE.tyEq (tabs.ty top.type) t &&
            copyCompat (tabs.ty x.type) (tabs.ty top.type) &&
            off.op == .OffPtr && off.args == #[p] && off.auxInt == Int64.ofNat o &&
            (tabs.ty off.type matches .ptr _)
          | none => false
        | _, _ => false
      | none => false
    | _, _ => false
  | _, _ => false

/-! ## An `IMake` of a `StructMake` (issue #69)

`(IMake _typ (StructMake ___)) => imakeOfStructMake(v)` (`generic.rules:981`, `dec.rules:102`;
`GoFV.Proof.Rules.imsShape`) makes `v` a copy of a fresh `IMake _typ a`, `a` the struct's first
field of non-zero size (`Interp.tryRule` logs the fresh value after `v`). Under the semantics an
interface's data word read at its pointer shape from a struct value is `poison` (`Val.retype`
keeps an aggregate only at an aggregate shape), so any field refines it; each instance is
validated (`imsOK`), and only so: the `StructMake` has an aggregate shape, `v`'s shape is an
interface's (two fields, the second a word, `imsTy`), and the fresh `IMake` has `v`'s type, its
first argument and an argument of the `StructMake`. -/

/-- An interface shape: two fields, the second (the data word) a pointer or a 64-bit integer. -/
def imsTy : Sem.Ty → Bool
  | .agg [_, (_, t)] _ => isPtrTy t || isInt64Ty t
  | _ => false

/-- The event `(v, [u0, w])` puts a struct into an interface as one of its fields (above). -/
def imsOK (tabs : Tables) (M : Defs) (v : ID) (defs : List Value) : Bool :=
  match M.get? v, defs with
  | some x, [u0, w] =>
    match x.args.toList, w.args.toList with
    | [t, s], [t', a] =>
      match M.get? s with
      | some y =>
        x.op == .IMake && y.op == .StructMake && (tabs.ty y.type matches .agg ..) &&
          imsTy (tabs.ty x.type) &&
          u0.id == v && u0.op == .Copy && u0.args == #[w.id] && u0.type == x.type &&
          u0.auxInt == 0 && u0.aux == none &&
          (M.get? w.id).isNone && w.op == .IMake && w.type == x.type && t' == t &&
          y.args.contains a && (M.get? a).isSome
      | none => false
    | _, _ => false
  | _, _ => false

/-! ## Comparisons of symbol addresses (issue #69)

`(EqPtr (Addr {x} _) (Addr {y} _)) => (ConstBool [x == y])` (`generic.rules:1648`) and its
`NeqPtr` form (`:1651`; `GoFV.Proof.Rules.addrCmpShape`) compare two symbols' auxes, which the
denotation does not model (the oracle answers `x == y`). The semantics gives an `Addr` the
pointer to offset 0 of the global block named by its symbol (`GoFV.Proof.Rules.addrVal`), so two
such pointers are equal iff the names are: each instance is validated (`addrCmpOK`), and only so,
by those names. -/

/-- The global block name an `Addr` aux points to (`GoFV.Proof.Rules.addrVal`). -/
def addrName? (tabs : Tables) (ax : Option AuxRef) : Option String :=
  match ax.bind tabs.aux? with
  | some { kind := .sym name .., .. } => some name.toStringLossy
  | _ => none

/-- The global block an `Addr` operand of an address comparison points to. -/
def addrSymOf (tabs : Tables) (M : Defs) (a : ID) : Option String :=
  match M.get? a with
  | some x => if x.op == .Addr then addrName? tabs x.aux else none
  | none => none

/-- The event `(v, [u0, u])` folds the comparison `v` of two symbol addresses: `u` is `v` as
`ConstBool` of whether the names are equal (`NeqPtr`: differ). The interpreter logs `v`'s new
definition twice for an in-place result (`Interp.tryRule`): `u0` is at `v` too. -/
def addrCmpOK (tabs : Tables) (M : Defs) (v : ID) (defs : List Value) : Bool :=
  match M.get? v, defs with
  | some x, [u0, u] =>
    match x.args.toList with
    | [a, b] =>
      match addrSymOf tabs M a, addrSymOf tabs M b with
      | some na, some nb =>
        (x.op == .EqPtr || x.op == .NeqPtr) && u0.id == v &&
          u.id == v && u.op == .ConstBool && u.args.isEmpty && u.type == x.type &&
          u.auxInt == (if (na == nb) != (x.op == .NeqPtr) then 1 else 0)
      | _, _ => false
    | _ => false
  | _, _ => false

/-- Replay the log on the definitions `M` and the terminators `B`, starting from `f`'s; `none`
if an event is not validated. An event of a dropped rule (`dropShape`) and a copy-argument
replacement the copies of `M` do not justify are skipped: `M` keeps its definition, and
`finalOK` accepts the output only where that value is no longer read (issue #17). A selection of
a `Make` (`makeSelOK`) is accepted from any rule; a selection of a `Load` (`loadSelOK`), an
`IMake` of a `StructMake` (`imsOK`) and a comparison of symbol addresses (`addrCmpOK`) only per
instance. With `lax` (`validate`), an event of a table
rule that is not validated is skipped the same way (keeping a definition is always sound;
`finalOK` decides): a selection of a dropped `Make` whose argument Go's `copyOf` retyped, issue
#17. The `ld` layer replays strictly, to take only validated events. -/
def replay (tabs : Tables) (t : Interp.Table) (f : Func) (lax : Bool) :
    Defs → BMap → List RwEvent → Option (Defs × BMap)
  | M, B, [] => some (M, B)
  | M, B, .rule v i _ defs :: evs =>
    match M.get? v with
    | none => none
    | some x =>
      match (t.values[x.op.ctorIdx]?).bind (·[i]?) with
      | none =>
        if structLoadOK tabs M v defs.toList then
          replay tabs t f lax (defs.foldl (fun M u => M.put u.id u) M) B evs
        else none
      | some cr =>
        if makeSelOK tabs M v defs.toList then
          replay tabs t f lax (defs.foldl (fun M u => M.put u.id u) M) B evs
        else if dropShape cr.rule then replay tabs t f lax M B evs
        else if loadSelShape cr.rule then
          if loadSelOK tabs M v defs.toList then
            replay tabs t f lax (defs.foldl (fun M u => M.put u.id u) M) B evs
          else none
        else if imsShape cr.rule then
          if imsOK tabs M v defs.toList then
            replay tabs t f lax (defs.foldl (fun M u => M.put u.id u) M) B evs
          else none
        else if addrCmpShape cr.rule then
          if addrCmpOK tabs M v defs.toList then
            replay tabs t f lax (defs.foldl (fun M u => M.put u.id u) M) B evs
          else none
        else if ruleOK tabs M cr.rule v defs.toList then
          replay tabs t f lax (defs.foldl (fun M u => M.put u.id u) M) B evs
        else if lax then replay tabs t f lax M B evs else none
  | M, B, .copyArg v i src :: evs =>
    match M.get? v with
    | none => none
    | some x =>
      if h : i < x.args.size then
        if copyReachW tabs M M.size x.args[i] src then
          replay tabs t f lax (M.put v { x with args := x.args.set i src }) B evs
        else replay tabs t f lax M B evs
      else none
  | M, B, .control b i c :: evs =>
    match bstate f B b with
    | none => none
    | some st =>
      if h : i < st.ctrls.size then
        if copyReach tabs M M.size st.ctrls[i] c then
          replay tabs t f lax M ((b, { st with ctrls := st.ctrls.set i c }) :: B) evs
        else none
      else none
  | _, _, .phielim .. :: _ => none
  | _, _, .snap .. :: _ => none
  | M, B, .blockRule b i nc _ :: evs =>
    match bstate f B b with
    | none => none
    | some st =>
      if ((f.block? b).map (·.succs.size)) != some 2 then none else
      match (t.blocks[st.kind.ctorIdx]?).bind (·[i]?) with
      | none => none
      | some br =>
        match blockOK tabs M br st nc with
        | none => none
        | some (defs, st') =>
          replay tabs t f lax (defs.foldl (fun M u => M.put u.id u) M) ((b, st') :: B) evs

/-- A value that is not a term node: phis, roots and frame-dependent values (`termOp`). -/
@[inline] def isAtom (x : Value) : Bool := !termOp x.op

/-- The atoms listed in block `b`. -/
def atomsOf (h : Func) (b : Block) : List ID :=
  b.values.toList.filter fun x => match h.value? x with
    | some v => isAtom v
    | none => false

/-- Atoms whose evaluation neither panics nor changes memory, which the rewrite pass may delete
when they are dead. -/
def dropAtom (op : Op) : Bool :=
  op matches .Phi | .Arg | .ArgIntReg | .ArgFloatReg | .SP | .LocalAddr | .GetClosurePtr |
    .GetCallerSP

/-- `f` and `g` have the same blocks, the atoms of `g` are atoms of `f` with the same fields and
block, the atoms only `f` has are droppable (`dropAtom`), and each block evaluates its roots in
the same order (`Sem.schedule`). The terminators are `finalOK`'s. -/
def atomsOK (f g : Func) : Bool :=
  f.entry == g.entry && f.blocks == g.blocks && f.ownAux == g.ownAux &&
  f.blocks.all fun b =>
    match f.block? b, g.block? b with
    | some fb, some gb =>
      fb.id == gb.id &&
      let af := atomsOf f fb
      let ag := atomsOf g gb
      ag.all (fun x => af.contains x && match f.value? x, g.value? x with
        | some u, some w => u.op == w.op && u.type == w.type && u.auxInt == w.auxInt &&
            u.aux == w.aux && u.args.size == w.args.size && u.block == w.block && u.id == w.id
        | _, _ => false) &&
      af.all (fun x => ag.contains x || (f.value? x).any (dropAtom ·.op)) &&
      match Sem.schedule f fb, Sem.schedule g gb with
      | some of, some og =>
        of.toList.filter (fun x => (f.value? x).any (Sem.isRoot ·.op)) ==
          og.toList.filter (fun x => (g.value? x).any (Sem.isRoot ·.op))
      | _, _ => false
    | _, _ => false

/-- `x` is a root of `h` (`GoFV.Proof.AtomSim.rootP`). -/
def rootB (h : Func) (x : ID) : Bool := (h.value? x).any (Sem.isRoot ·.op)

/-- The atom `w` of `g` has the fields of the atom `u` of `f` but the arguments and, for a
`Store`, the aux. -/
def atomFieldsOK (u w : Value) : Bool :=
  u.op == w.op && u.type == w.type && u.auxInt == w.auxInt && (u.aux == w.aux || u.op == .Store) &&
    u.args.size == w.args.size && u.block == w.block && u.id == w.id

/-- `atomsOK` with changed and dropped memory roots (`GoFV.Proof.AtomSim.AtomsX`; memcombine's
combined stores, issue #35, and the forwarding layer's dropped identity writes, issue #151): the
same entry, blocks and own aux; every atom of `g` is an atom of `f` with the same fields but the
arguments and, for a `Store`, the aux; each block evaluates the roots both functions have in
the same order (`Sem.schedule`), and a root of `f` that is no root of `g` is a `Store` or a
`Zero` (which never panic), or with `calls` a `StaticLECall` (the forwarding layer's folded
`runtime.ifaceeq`/`efaceeq` calls, which return under their contract, `Sem.Env.IfaceEq`). -/
def atomsXOK (f g : Func) (calls : Bool := false) : Bool :=
  f.entry == g.entry && f.blocks == g.blocks && f.ownAux == g.ownAux &&
  f.blocks.all fun b =>
    match f.block? b, g.block? b with
    | some fb, some gb =>
      fb.id == gb.id &&
      (atomsOf g gb).all (fun x => (atomsOf f fb).contains x && match f.value? x, g.value? x with
        | some u, some w => atomFieldsOK u w
        | _, _ => false) &&
      match Sem.schedule f fb, Sem.schedule g gb with
      | some of, some og =>
        of.toList.filter (fun x => rootB f x && rootB g x) == og.toList.filter (rootB g) &&
          of.toList.all fun x =>
            !rootB f x || rootB g x || (f.value? x).any fun u => u.op == .Store || u.op == .Zero ||
              (calls && u.op == .StaticLECall)
      | _, _ => false
    | _, _ => false

/-- Marks of the values listed in `h`: `x` is in the values of its own block, a block of `h`. -/
def listedMarks (h : Func) : Array Bool :=
  h.blocks.foldl (init := Array.replicate h.valueTab.size false) fun L b =>
    match h.block? b with
    | some hb => hb.values.foldl (init := L) fun L x =>
        if (h.value? x).any (·.block == b) then L.set! x true else L
    | none => L

/-- The arguments of the values in the blocks of `h` and the controls of its blocks are listed
(`listedMarks`): the terms over listed values only reach listed values. -/
def closedOK (h : Func) : Bool :=
  let L := listedMarks h
  h.blocks.all fun b =>
    match h.block? b with
    | some hb =>
      hb.controls.all (fun c => L[c]? == some true) &&
      hb.values.all fun x => (h.value? x).all fun u => u.args.all fun a => L[a]? == some true
    | none => true

/-! ### Values the output reads

`finalOK` compares the replayed definition of a listed value only where the output reads it: the
controls of `h`'s blocks, the arguments of its listed atoms, and the arguments of its listed terms
that are read themselves. A term read only by unread terms is dead (a dropped `Make` the replay
kept, still an argument of an unread `StructMake`, issue #17). `liveMarks` computes the marks
(untrusted, a worklist), `liveOK` checks that they are closed under these rules. -/

/-- The listed terms' arguments by ID, the roots (controls and the listed atoms' arguments), and
the number of arguments of listed values. -/
def liveInit (h : Func) : Array (Option (Array ID)) × List ID × Nat :=
  h.blocks.toList.foldl (init := (Array.replicate h.valueTab.size none, [], 0)) fun (T, R, n) b =>
    match h.block? b with
    | some hb =>
      hb.values.toList.foldl (init := (T, hb.controls.toList ++ R, n)) fun (T, R, n) x =>
        match h.value? x with
        | some u =>
          if termOp u.op then (T.set! x (some u.args), R, n + u.args.size)
          else (T, u.args.toList ++ R, n + u.args.size)
        | none => (T, R, n)
    | none => (T, R, n)

/-- The worklist of `liveMarks`: mark each popped value once, pushing a listed term's
arguments. -/
def liveGo (T : Array (Option (Array ID))) : Nat → List ID → Array Bool → Array Bool
  | 0, _, L => L
  | _ + 1, [], L => L
  | n + 1, x :: xs, L =>
    if L[x]? == some true then liveGo T n xs L
    else
      match T[x]? with
      | some (some as) => liveGo T n (as.toList ++ xs) (L.set! x true)
      | _ => liveGo T n xs (L.set! x true)

/-- Marks of the values `h` reads (`liveOK` checks them). -/
def liveMarks (h : Func) : Array Bool :=
  let (T, R, n) := liveInit h
  liveGo T (R.length + n + 1) R (Array.replicate h.valueTab.size false)

/-- The marks `L` hold the controls of `h`'s blocks, the arguments of its listed atoms, and the
arguments of its marked listed terms. -/
def liveOK (h : Func) (L : Array Bool) : Bool :=
  h.blocks.all fun b =>
    match h.block? b with
    | some hb =>
      hb.controls.all (fun c => L[c]? == some true) &&
      hb.values.all fun x => (h.value? x).all fun u =>
        (termOp u.op && L[x]? != some true) || u.args.all fun a => L[a]? == some true
    | none => true

/-- Every value listed in `g` has its replayed definition, up to copies in its arguments, or is a
term that `g` does not read (`liveMarks`, closed by `liveOK`; the replay kept the input's
definition of a dropped rule's value or of an event it skipped, issue #17), and every block of `g`
its replayed terminator (`bstate`): the kind, the successors (swapped if the replay swapped them,
then from two), the controls up to copies. -/
def finalOK (tabs : Tables) (f g : Func) (M : Defs) (B : BMap) : Bool :=
  let n := M.size
  let L := liveMarks g
  liveOK g L &&
  g.blocks.all fun b =>
    match bstate f B b, f.block? b, g.block? b with
    | some st, some fb, some gb =>
      gb.kind == st.kind &&
      (if st.swapped then fb.succs.size == 2 && gb.succs == swapS fb.succs
       else gb.succs == fb.succs) &&
      gb.controls.size == st.ctrls.size &&
      (st.ctrls.toList.zip gb.controls.toList).all (fun (c, c') => copyReach tabs M n c c') &&
      gb.values.all fun x =>
        match M.get? x, g.value? x with
        | some m, some u =>
          (u.id == x && m.id == x && u.op == m.op && u.type == m.type && u.auxInt == m.auxInt &&
            u.aux == m.aux && u.args.size == m.args.size &&
            (m.args.toList.zip u.args.toList).all fun (a, a') => copyReachW tabs M n a a') ||
          (termOp u.op && L[x]? != some true)
        | _, _ => false
    | _, _, _ => false

/-- **The validator**: `g` (the result of the rewrite pass with table `t` on `f`, which logged
`log`) is related to `f` as the theorems need. -/
def validate (tabs : Tables) (t : Interp.Table) (f g : Func) (log : Array RwEvent) : Bool :=
  atomsOK f g && closedOK f && closedOK g &&
  match replay tabs t f true f.valueTab [] log.toList with
  | some (M, B) => finalOK tabs f g M B
  | none => false

/-! ## Nil-check eliminations (issue #151)

A rule of the table's `nilChecks` row, `(NilCheck x:(Op …) _) => x`, turns a root (a nil check)
into a term (`Copy x`). The validator takes these events out of the log: `nilPre` applies them to
the input (`NilCheck p mem` → `Copy p`, as `v.reset(OpCopy)`), the checked pass relates input
and `nilPre` by nilcheckelim's checker (`NilCheck.nrel`: `p` is a `safePtr` seed, so the check
cannot panic, and the other roots keep their order), and `validate` relates `nilPre` and the
output with the remaining events. The row also holds `(IsNonNil (Op …)) => (ConstBool [true])`
with `Op` an `Addr` or `LocalAddr` (tried on an `IsNonNil` after its row), which `nilPre`
applies alike (`IsNonNil p` → `ConstBool [1]`) and `nrel` justifies by `NilCheck.nnSeed`. -/

/-- A nil-check elimination `(NilCheck x:(Op …) _) => x` whose pointer op nilcheckelim's
checker can justify by itself (`NilCheck.safePtr true`: `Addr`, `LocalAddr`, `NilCheck`, `GetG`,
`OffPtr` or `Convert` of such a pointer, the `SelectN [0]` of a malloc-family call, a dictionary
`Arg`). -/
def nilElimOK (r : Rule) : Bool :=
  match r.pat, r.result with
  | .op .NilCheck none _ _ _ .fixed [.op o (some x) _ _ _ _ _ _, _] _, .copy (.var y) =>
    x == y &&
      (o matches .Addr | .LocalAddr | .NilCheck | .GetG | .OffPtr | .Convert | .SelectN | .Arg)
  | .op .IsNonNil none _ _ _ .fixed [.op o _ _ _ _ _ _ _] _, .build [n] =>
    (o matches .Addr | .LocalAddr) && n.op == .ConstBool && n.ty.isNone && n.aux.isNone &&
      n.args.isEmpty && (n.auxInt matches some (.lit .bool (.bool true)))
  | _, _ => false

/-- The nil check (or `IsNonNil`) `v` of `f` that event `ev` eliminates, if it is a `nilChecks`
rule event (`nilElimOK`). -/
def nilEvent? (t : Interp.Table) (f : Func) : RwEvent → Option ID
  | .rule v i _ _ =>
    match f.value? v with
    | some x =>
      if x.op == .NilCheck || x.op == .IsNonNil then
        let n := ((t.values[x.op.ctorIdx]?).map (·.size)).getD 0
        if n ≤ i then
          match t.nilChecks[i - n]? with
          | some cr => if nilElimOK cr.rule then some v else none
          | none => none
        else none
      else none
    | none => none
  | _ => none

/-- `v.reset(OpCopy)` with its pointer argument: the nil check `v` of `f` becomes `Copy p`, its
other arguments lose a use; an `IsNonNil` `v` becomes `ConstBool [1]` (`v.reset(OpConstBool)`),
its argument loses a use. -/
def nilCopy (f : Func) (v : ID) : Func :=
  match f.value? v with
  | some x =>
    if x.op == .NilCheck && 0 < x.args.size then
      let f := (x.args.extract 1 x.args.size).foldl (fun f a => f.modV a fun u => { u with uses := u.uses - 1 }) f
      f.modV v fun u => { u with op := .Copy, auxInt := 0, aux := none, args := #[x.args[0]!] }
    else if x.op == .IsNonNil then
      let f := x.args.foldl (fun f a => f.modV a fun u => { u with uses := u.uses - 1 }) f
      f.modV v fun u => { u with op := .ConstBool, auxInt := 1, aux := none, args := #[] }
    else f
  | none => f

/-- The nil check `v` of `f` checks a pointer nilcheckelim's checker takes as non-nil by itself
(`NilCheck.safePtr true`); the `IsNonNil` `v` tests an `NilCheck.nnSeed`. -/
def nilSafe (tabs : Tables) (f : Func) (v : ID) : Bool :=
  match f.value? v with
  | some x =>
    match x.args[0]? with
    | some p =>
      if x.op == .IsNonNil then NilCheck.nnSeed tabs f p
      else NilCheck.safePtr true tabs f f.valueTab.size p
    | none => false
  | none => false

/-- One event of `nilPre`: a nil-check elimination of `f` is applied (with `sel` only one of a
`nilSafe` check), any other event kept, but for the copy-argument replacements of the eliminated
check logged before it (the check becomes `Copy` of its pointer in `f`, which reaches the
replaced argument through copies). -/
def nilStep (t : Interp.Table) (tabs : Tables) (sel : Bool) (f : Func) (p : Func × Array RwEvent)
    (ev : RwEvent) : Func × Array RwEvent :=
  match nilEvent? t f ev with
  | some v =>
    if sel && !nilSafe tabs f v then (p.1, p.2.push ev)
    else (nilCopy p.1 v, p.2.filter fun | .copyArg w _ _ => w != v | _ => true)
  | none => (p.1, p.2.push ev)

/-- The input with the log's nil-check eliminations applied (with `sel` only those of `nilSafe`
checks), and the remaining events. -/
def nilPre (t : Interp.Table) (tabs : Tables) (sel : Bool) (f : Func) (log : Array RwEvent) :
    Func × Array RwEvent :=
  log.foldl (nilStep t tabs sel f) (f, #[])

/-! ## Load-of-Store forwarding (issue #151)

A rule of the table's `loads` row, `(Load p1 (Store {t2} p2 x _)) && isSamePtr(p1, p2) && … => x`
and its forms through up to three more `Store`s at disjoint addresses (`fwdShapeOK`), replaces a
`Load` (a term) by `Copy x` of the value a `Store` (a root) wrote at the same address. The
validator takes these events out of the log like nil-check eliminations: `fwdPre` applies them
to the input, `fwdRel` relates the input and that function (each replaced `Load` reads, through
`Store`s at disjoint addresses, a `Store` of `x` at a pointer that evaluates like the `Load`'s,
at a shape a write and a read give back unchanged: `fwdOK`; every other value unchanged; ranks
that order each listed non-`Phi` value after its arguments: `fwdRank`, `fwdRankOK`), and
`validate` relates that function and the output with the remaining events. -/

/-- Pointer shapes, whatever their element size (only `PtrIndex` reads it). -/
def isPtrTy : Sem.Ty → Bool
  | .ptr _ => true
  | _ => false

/-- `x` is a value of `f` of pointer shape. -/
def ptrVal (tabs : Tables) (f : Func) (x : ID) : Bool :=
  (f.value? x).any fun u => isPtrTy (tabs.ty u.type)

/-- The length and capacity arguments of `v` if it is a `SliceLen`/`SliceCap` of a `SliceMake`
of slice shape. -/
def sliceMakeLC? (tabs : Tables) (f : Func) (v : Value) : Option (ID × ID) :=
  if (v.op == .SliceLen || v.op == .SliceCap) && v.args.size == 1 then
    match f.value? v.args[0]! with
    | some m =>
      if m.op == .SliceMake && m.args.size == 3 &&
          (match tabs.ty m.type with | .slice _ => true | _ => false) then
        some (m.args[1]!, m.args[2]!)
      else none
    | none => none
  else none

/-- The length (`len`) or capacity of a `SliceMake` of slice shape with length `l` and capacity
`c`, whatever its pointer: `Val.retype` at a slice shape checks only `Val.sliceOK`, which does
not read the pointer. -/
def sliceComp (l c : Sem.Val) (len : Bool) : Sem.Val :=
  if Sem.Val.sliceOK [.poison, l.retypeI64, c.retypeI64] then
    if len then l.retypeI64 else c.retypeI64
  else .poison

omit [GoFV.SSA.Sem.Addrs] in
/-- `sliceComp` of values without frame pointers agrees under any two instances. -/
theorem sliceComp_agree {A B : Sem.Addrs} {l c : Sem.Val} (hl : l.lowB = true) (hc : c.lowB = true)
    (len : Bool) : @sliceComp A l c len = @sliceComp B l c len := by
  simp only [sliceComp, Sem.Val.retypeI64_agree (A := A) (B := B) hl,
    Sem.Val.retypeI64_agree (A := A) (B := B) hc]

/-- The value of `a` if it is a constant term of `f` at most `k` deep: a term node (`termOp`)
whose arguments are constant terms, evaluated as the semantics evaluates it (`Rules.opVal` at its
value's shape, retyped), e.g. `Mul64 (StringLen (ConstString {s})) (Const64 [1])`, which value
rules fold to a `Const64` only later in the log; or a `SliceLen`/`SliceCap` of a `SliceMake` of
slice shape whose length and capacity are constant terms (`sliceMakeLC?`, `sliceComp`; its
pointer need not be constant), e.g. the size `Mul64 (SliceLen (SliceMake p (Sub64 (Const64 [8])
(Const64 [0])) …)) (Const64 [1])` of a `memmove` call of `copy(a[i:j], …)`. It evaluates at
`Addrs.fixed` (`Rules.opValC`, `Val.retypeC`) on values without frame pointers whose integers an
op reads as pointers lie below `2^62`, where every instance gives the same value
(`docs/plans/proofs3.md` §8, item 6); any other term is no constant. -/
def termConst (tabs : Tables) (f : Func) : Nat → ID → Option Sem.Val
  | 0, _ => none
  | k + 1, a =>
    match f.value? a with
    | some v =>
      if (sliceMakeLC? tabs f v).isSome then
        match k with
        | 0 => none
        | j + 1 =>
          match sliceMakeLC? tabs f v with
          | some (l, c) =>
            match termConst tabs f j l, termConst tabs f j c with
            | some lv, some cv =>
              if lv.lowB && cv.lowB then
                let s := @sliceComp Sem.Addrs.fixed lv cv (v.op == .SliceLen)
                if s.lowB then some (s.retypeC (tabs.ty v.type)) else none
              else none
            | _, _ => none
          | none => none
      else if termOp v.op then
        (v.args.toList.mapM (termConst tabs f k)).bind fun cs =>
          (GoFV.Proof.Rules.opValC tabs v.op (tabs.ty v.type) v.auxInt v.aux cs).map
            (·.retypeC (tabs.ty v.type))
      else none
    | none => none

/-- A constant index: a constant term (`termConst`, at most four deep) of the 64-bit integer
shape, its value; e.g. `Div64 (Sub64 (Const64 [32]) (Const64 [1])) (Const64 [32])`, which value
rules fold to a `Const64` only later in the log. -/
def constIdx? (tabs : Tables) (f : Func) (i : ID) : Option (BitVec 64) :=
  match termConst tabs f 4 i with
  | some (.int .w64 k) => some k
  | _ => none

/-- A pointer-shaped value that reads as its argument's pointer word: a `Convert` (to a pointer
type, the identity on the word, `Sem.PtrOps.convert`) or an `ITab` of an `IMake` (the `IMake`'s
first argument, retyped as the interface's first field and then as a pointer; the fixed loads
`generic.rules:2252`–`:2258`). -/
def wordStep? (tabs : Tables) (f : Func) (u : Value) : Option ID :=
  if !isPtrTy (tabs.ty u.type) then none
  else if u.op == .Convert && u.args.size == 2 then some u.args[0]!
  else if u.op == .ITab && u.args.size == 1 then
    match f.value? u.args[0]! with
    | some m => if m.op == .IMake && m.args.size == 2 then some m.args[0]! else none
    | none => none
  else none

/-- One step of `ptrBase`: an `OffPtr` or `Copy` of pointer shape on a pointer-shaped argument,
or a `PtrIndex` of element size `e` (its pointer shape) by a constant index `k` (`constIdx?`),
its argument and its offset (`k * e`); or a `wordStep?`, at offset `0`. -/
def ptrStep? (tabs : Tables) (f : Func) (a : ID) : Option (ID × BitVec 64) :=
  match f.value? a with
  | some u =>
    if (u.op == .OffPtr || u.op == .Copy) && u.args.size == 1 && isPtrTy (tabs.ty u.type) &&
        ptrVal tabs f u.args[0]! then
      some (u.args[0]!, if u.op == .OffPtr then BitVec.ofInt 64 u.auxInt.toInt else 0)
    else if u.op == .PtrIndex && u.args.size == 2 && ptrVal tabs f u.args[0]! then
      match tabs.ty u.type, constIdx? tabs f u.args[1]! with
      | .ptr (some e), some k => some (u.args[0]!, k * BitVec.ofNat 64 e)
      | _, _ => none
    else (wordStep? tabs f u).map (·, 0)
  | none => none

/-- Pointer `a` as a base and a constant offset: through at most `n` `OffPtr`s and `Copy`s
(`ptrStep?`; `isSamePtr`'s `OffPtr` chains, copies that copy elimination looks through). -/
def ptrBase (tabs : Tables) (f : Func) : Nat → ID → ID × BitVec 64
  | 0, a => (a, 0)
  | n + 1, a =>
    match ptrStep? tabs f a with
    | some (c, o) => ((ptrBase tabs f n c).1, (ptrBase tabs f n c).2 + o)
    | none => (a, 0)

/-- Terms that evaluate equally: the same value, or term nodes with the same op, shape and
fields whose arguments evaluate equally (at most `n` deep). -/
def termEqB (tabs : Tables) (f : Func) : Nat → ID → ID → Bool
  | 0, a, b => a == b
  | n + 1, a, b =>
    a == b ||
    match f.value? a, f.value? b with
    | some u, some w =>
      termOp u.op && u.op == w.op && GoFV.Opt.CSE.tyEq (tabs.ty u.type) (tabs.ty w.type) &&
        u.auxInt == w.auxInt && u.aux == w.aux && u.args.size == w.args.size &&
        (u.args.toList.zip w.args.toList).all fun (c, d) => termEqB tabs f n c d
    | _, _ => false

/-- Index values equal: `termEqB`. -/
def idxSame (tabs : Tables) (f : Func) (i j : ID) : Bool := termEqB tabs f 4 i j

/-- The allocation base pointer `a` points to at offset 0, where it is known statically: a
pointer-shaped `LocalAddr`'s frame variable (in activation 0, where the atom simulation runs:
`Sem.frameVal`, `AtomSim.MemAtoms`) or a word-shaped `Addr`'s global (`Sem.addrVal`; at
`uintptr` its word, which reads back as the pointer, `Ptr.word_asPtrWord`). -/
def baseBlk? (tabs : Tables) (f : Func) (a : ID) : Option Sem.Blk :=
  match f.value? a with
  | some u =>
    if u.op == .LocalAddr && isPtrTy (tabs.ty u.type) then u.aux.map (Sem.frameBlk tabs 0)
    else if u.op == .Addr && wordTy (tabs.ty u.type) then
      match u.aux.bind tabs.aux? with
      | some { kind := .sym name .., .. } => some (.global name.toStringLossy)
      | _ => none
    else none
  | none => none

/-- Base pointers equal where both are pointers: the same value, the start of one allocation
(`baseBlk?`), or `AddPtr`/`PtrIndex` nodes of one pointer shape on such pointers (`ptrBase`, the
same offset) by equal indices (`idxSame`). -/
def baseSameB (tabs : Tables) (f : Func) : Nat → ID → ID → Bool
  | 0, a, b => a == b
  | n + 1, a, b =>
    a == b ||
    (match baseBlk? tabs f a, baseBlk? tabs f b with
     | some x, some y => x == y
     | _, _ => false) ||
    match f.value? a, f.value? b with
    | some u, some w =>
      (u.op == .AddPtr || u.op == .PtrIndex) && u.op == w.op && u.args.size == 2 &&
        w.args.size == 2 && GoFV.Opt.CSE.tyEq (tabs.ty u.type) (tabs.ty w.type) &&
        u.auxInt == w.auxInt && u.aux == w.aux &&
        ptrVal tabs f u.args[0]! && ptrVal tabs f w.args[0]! &&
        (ptrBase tabs f 8 u.args[0]!).2 == (ptrBase tabs f 8 w.args[0]!).2 &&
        baseSameB tabs f n (ptrBase tabs f 8 u.args[0]!).1 (ptrBase tabs f 8 w.args[0]!).1 &&
        idxSame tabs f u.args[1]! w.args[1]! && isPtrTy (tabs.ty u.type)
    | _, _ => false

/-- Pointers equal where both are pointers (`isSamePtr`): equal bases (`baseSameB`) at the same
offset (`ptrBase`). -/
def samePtrB (tabs : Tables) (f : Func) (a b : ID) : Bool :=
  (ptrBase tabs f 8 a).2 == (ptrBase tabs f 8 b).2 &&
    baseSameB tabs f 8 (ptrBase tabs f 8 a).1 (ptrBase tabs f 8 b).1

/-- Offsets `o` (`n` bytes) and `o'` (`k` bytes) from one base address disjoint byte ranges,
modulo `2^64`: `o'` at least `n` above `o` and wrapping at most onto `o`, or the other way. -/
def offSep (o : BitVec 64) (n : Nat) (o' : BitVec 64) (k : Nat) : Bool :=
  (decide (n ≤ (o' - o).toNat) && decide ((o' - o).toNat + k ≤ 2 ^ 64)) ||
  (decide (k ≤ (o - o').toNat) && decide ((o - o').toNat + n ≤ 2 ^ 64))

/-- Pointer `a` is an argument's word moved by at most `n` pointer steps: an `Arg` or
`ArgIntReg`, or an `OffPtr`, `Copy`, `AddPtr`, `PtrIndex` or `NilCheck` of such a pointer (its
first argument). A function's arguments hold no pointer into a frame temporary
(`Sem.InitAvoids`), and none of these steps changes the block a pointer points into. -/
def argPtrB (tabs : Tables) (f : Func) : Nat → ID → Bool
  | 0, _ => false
  | n + 1, a =>
    match f.value? a with
    | some u =>
      u.op == .Arg || u.op == .ArgIntReg ||
      (((u.op == .OffPtr || u.op == .Copy) && u.args.size == 1 ||
          (u.op == .AddPtr || u.op == .PtrIndex || u.op == .NilCheck) && u.args.size == 2) &&
        argPtrB tabs f n u.args[0]!)
    | none => false

/-- A frame temporary (`Sem.Blk.temp`: a `PAUTO` whose address is never converted to an
integer, `Sem.frameBlk`). -/
def tempBlk : Sem.Blk → Bool
  | .temp _ _ => true
  | _ => false

/-- Pointer `a`'s base (`ptrBase`) is the start of a frame temporary (`baseBlk?`). -/
def tempBaseB (tabs : Tables) (f : Func) (a : ID) : Bool :=
  (baseBlk? tabs f (ptrBase tabs f 8 a).1).any tempBlk

/-- Pointer `a` (`n` bytes) and pointer `b` (`k` bytes) address disjoint bytes where both are
pointers (`disjoint`): equal bases (`baseSameB`) at separate offsets (`offSep`), bases in
different allocations (`baseBlk?`), or one in a frame temporary (`tempBaseB`) and the other an
argument's pointer (`argPtrB`). -/
def disjointB (tabs : Tables) (f : Func) (a : ID) (n : Nat) (b : ID) (k : Nat) : Bool :=
  (offSep (ptrBase tabs f 8 a).2 n (ptrBase tabs f 8 b).2 k &&
    baseSameB tabs f 8 (ptrBase tabs f 8 a).1 (ptrBase tabs f 8 b).1) ||
  (match baseBlk? tabs f (ptrBase tabs f 8 a).1, baseBlk? tabs f (ptrBase tabs f 8 b).1 with
   | some x, some y => x != y
   | _, _ => false) ||
  (tempBaseB tabs f a && argPtrB tabs f 8 b) || (argPtrB tabs f 8 a && tempBaseB tabs f b)

mutual
/-- A shape a `Store` writes and a `Load` reads back unchanged (`Sem.encode`,
`Sem.decodeLoad`): `scalarTy`, a string or slice, or a non-empty aggregate of `fwdFields`
(nested structs, strings and slices as fields; a `poison` store decodes as `poison`). -/
def fwdTy : Sem.Ty → Bool
  | .int _ | .bool | .ptr _ | .str | .slice _ => true
  | .agg fs n => n != 0 && fwdFields n 0 fs
  | _ => false
/-- Fields of `fwdTy` shapes at increasing offsets from `lo` that do not overlap and end inside
`n` bytes. -/
def fwdFields (n lo : Nat) : List (Nat × Sem.Ty) → Bool
  | [] => true
  | (o, t) :: fs => fwdTy t && decide (lo ≤ o) && decide (o + t.size ≤ n) &&
      fwdFields n (o + t.size) fs
end

mutual
/-- A shape with its pointers' and slices' element sizes dropped, through aggregates' fields:
shapes with equal `fwdErase` write, read and retype alike (`copyCompatibleType`). -/
def fwdErase : Sem.Ty → Sem.Ty
  | .ptr _ => .ptr none
  | .slice _ => .slice none
  | .agg fs n => .agg (fwdEraseFields fs) n
  | t => t
/-- `fwdErase` of every field. -/
def fwdEraseFields : List (Nat × Sem.Ty) → List (Nat × Sem.Ty)
  | [] => []
  | (o, t) :: fs => (o, fwdErase t) :: fwdEraseFields fs
end

/-- Shapes `fwdTy` that write, read and retype alike: equal up to element sizes (`fwdErase`). -/
def fwdTyEq (t s : Sem.Ty) : Bool := fwdTy t && Sem.Ty.beq (fwdErase t) (fwdErase s)

/-- A `Store` at type shape `s` writes a value of shape `t` (`fwdTy`) as a write at `t` does:
`fwdTyEq`, or a pointer stored as a 64-bit integer (`Sem.encode` writes a pointer's bytes at
both). -/
def fwdStoreTy (t s : Sem.Ty) : Bool :=
  fwdTyEq t s || (isPtrTy t && s matches .int .w64)

/-- The value `a` a `Store` writes stands for `x`: `x` is reached from `a` through compatible
copies (`copyReach`; copy elimination ran before the rule matched `x`), and `a` has a shape
`fwdTyEq` to the read's `t`. -/
def storedOK (tabs : Tables) (f : Func) (t : Sem.Ty) (a x : ID) : Bool :=
  copyReach tabs f.valueTab f.valueTab.size a x &&
    match f.value? a with
    | some av => fwdTyEq t (tabs.ty av.type)
    | none => false

/-- Memory `m` of `f`, read at pointer `p` at shape `t`, holds `x`: through at most `d` `Copy`s
and `Store`s at pointers disjoint from the read (`disjointB`), a `Store` of a value standing for
`x` (`storedOK`) at a pointer equal to `p` (`samePtrB`) at a type of shape `t` (`fwdStoreTy`),
and `x` of shape `t` (`fwdTyEq`). -/
def fwdChain (tabs : Tables) (f : Func) (p : ID) (t : Sem.Ty) (x : ID) : Nat → ID → Bool
  | 0, _ => false
  | d + 1, m =>
    match f.value? m, f.value? x with
    | some s, some xv =>
      (s.op == .Copy && s.args.size == 1 && fwdChain tabs f p t x d s.args[0]!) ||
      ((s.op == .Store || s.op == .StoreWB) && s.args.size == 3 &&
       ((storedOK tabs f t s.args[1]! x && samePtrB tabs f p s.args[0]! &&
           fwdStoreTy t (Sem.auxTy tabs s.aux) && fwdTyEq t (tabs.ty xv.type)) ||
        (disjointB tabs f p t.size s.args[0]! (Sem.auxTy tabs s.aux).size &&
           fwdChain tabs f p t x d s.args[2]!)))
    | _, _ => false

/-- The `Load` `u` of `f` reads back the value `x` (`fwdChain` through at most eight `Copy`s and
`Store`s). -/
def fwdOK (tabs : Tables) (f : Func) (u : Value) (x : ID) : Bool :=
  u.op == .Load && u.args.size == 2 && fwdChain tabs f u.args[0]! (tabs.ty u.type) x 8 u.args[1]!

/-- The value the memory `m` of `f` stores at a pointer equal to `p` (`samePtrB`): through at
most `d` `Copy`s and `Store`s at other pointers, the first `Store` at `p` (the candidate `x` of
`fwdConstOK`; `fwdChain` checks it). -/
def fwdStored (tabs : Tables) (f : Func) (p : ID) : Nat → ID → Option ID
  | 0, _ => none
  | d + 1, m =>
    match f.value? m with
    | some s =>
      if s.op == .Copy && s.args.size == 1 then fwdStored tabs f p d s.args[0]!
      else if (s.op == .Store || s.op == .StoreWB) && s.args.size == 3 then
        if samePtrB tabs f p s.args[0]! then some s.args[1]! else fwdStored tabs f p d s.args[2]!
      else none
    | none => none

/-- `Const64` and `Const64F`: both denote the 64-bit integer of their auxint (a float is its bits). -/
def const64Op (op : Op) : Bool := op == .Const64 || op == .Const64F

/-- The `Load` `u` of `f` becomes the constant `w` (`generic.rules:830`, `:832`: a `Const64F` read
back from a `Store` of a `Const64` of its bits, and the other way): `fwdOK` reading back a
`const64Op` value `x` (the first `Store` at the Load's pointer, `fwdStored`) of the auxint of the
argument-less `const64Op` `w`, at a shape `fwdTyEq` to the Load's. -/
def fwdConstOK (tabs : Tables) (f : Func) (u w : Value) : Bool :=
  u.op == .Load && u.args.size == 2 && const64Op w.op && w.args.size == 0 &&
  match fwdStored tabs f u.args[0]! 8 u.args[1]! with
  | some x =>
    (match f.value? x with
     | some xv => const64Op xv.op && xv.auxInt == w.auxInt && fwdTyEq (tabs.ty u.type) (tabs.ty xv.type)
     | none => false) &&
    fwdOK tabs f u x
  | none => false

mutual
/-- A value whose bytes are `0` or `poison` at every shape: `0`, `false`, `poison`, the empty
value, or a composite of such (e.g. the empty string `ConstString {""}`, `ConstSlice`,
`ConstInterface`; a nil pointer is the word `0`, #290). -/
def zeroVal : Sem.Val → Bool
  | .poison | .bool false | .empty => true
  | .int _ c => c == 0
  | .agg vs => zeroVals vs
  | _ => false
def zeroVals : List Sem.Val → Bool
  | [] => true
  | v :: vs => zeroVal v && zeroVals vs
end

/-- Component `ps` (outermost first) of a composite value, `poison` where there is none. -/
def valPath : List Nat → Sem.Val → Sem.Val
  | [], v => v
  | i :: ps, .agg vs => valPath ps (vs.getD i .poison)
  | _ :: _, _ => .poison

/-- Component `ps` of `x`'s value is a `zeroVal`, at most `k` deep: a constant term
(`termConst`) whose component is one, a selection (`ECCheck.selIdx?`) of an argument whose
component `i :: ps` is, a `Copy` of an argument whose component `ps` is, or a composite built by
a make op (`ECCheck.isMake`) whose argument `i` has a zero component `ps'` (`ps = i :: ps'`) or
all of whose arguments are zero (`ps = []`). E.g. `SliceLen (SliceMake p (Const64 [0]) c)`,
`ITab (StructSelect [0] (StructMake (ConstInterface) x))`. -/
def zeroAt (tabs : Tables) (f : Func) : Nat → List Nat → ID → Bool
  | 0, _, _ => false
  | k + 1, ps, x =>
    (match termConst tabs f 4 x with
     | some c => zeroVal (valPath ps c)
     | none => false) ||
    match f.value? x with
    | some v =>
      match ECCheck.selIdx? v with
      | some i => v.args.size == 1 && zeroAt tabs f k (i :: ps) v.args[0]!
      | none =>
        (v.op == .Copy && v.args.size == 1 && zeroAt tabs f k ps v.args[0]!) ||
        (ECCheck.isMake v.op &&
          match ps with
          | [] => v.args.toList.all (zeroAt tabs f k [])
          | i :: ps' => decide (i < v.args.size) && zeroAt tabs f k ps' v.args[i]!)
    | none => false

/-- A term whose value is zero (`zeroAt`, ten deep): `Const64 [0]`, `ConstBool [0]`, `ConstNil`,
`ConstString {""}`, `SliceLen (ConstSlice)`, a selection of a zero field of a `StructMake`, … -/
def zeroConst (tabs : Tables) (f : Func) (x : ID) : Bool := zeroAt tabs f 10 [] x

/-- A size-specialised malloc call that asks for zeroed memory (issue #69; `ssagen.newObject`:
`mallocgc*SC*(size, typ, true)`, `Sem.AllocReq`): a call other than `newobject`, of four
arguments and of a type whose first two components are a pointer and a memory, with one ABI
result and parameters of the shapes `uintptr`, any, `bool`, whose size argument is a positive
`Const64` and whose `needzero` argument is `ConstBool [1]`. -/
def freshSC (tabs : Tables) (f : Func) (cv : Value) : Bool :=
  cv.aux.bind tabs.callee? != some "runtime.newobject" && cv.args.size == 4 &&
  (match tabs.ty cv.type with
   | .tuple (.ptr _ :: .mem :: _) => true
   | _ => false) &&
  ((((Sem.callABI? tabs cv.aux).map (·.params.toList)).getD []).filter (·.out)).length == 1 &&
  (match ((((Sem.callABI? tabs cv.aux).map (·.params.toList)).getD []).filter
      (!·.out)).map (tabs.ty ·.type) with
   | [.int .w64, _, .bool] => true
   | _ => false) &&
  match f.value? cv.args[0]!, f.value? cv.args[2]! with
  | some s, some z =>
    s.op == .Const64 && s.args.size == 0 && decide (0 < s.auxInt.toInt) &&
      (tabs.ty s.type matches .int .w64) &&
      z.op == .ConstBool && z.args.size == 0 && z.auxInt == 1 && (tabs.ty z.type matches .bool)
  | _, _ => false

/-- A `runtime.newobject(typ)` call (issue #69): of two arguments (the type descriptor and the
memory) and of a type whose first two components are a pointer and a memory, with one ABI result
and one pointer-shaped parameter, whose type argument is an `Addr` of a symbol
(`WBCheck.symName?`). That the symbol is a read-only one whose type descriptor has a positive
size is `fwdRoOK`'s. -/
def freshNew (tabs : Tables) (f : Func) (cv : Value) : Bool :=
  cv.aux.bind tabs.callee? == some "runtime.newobject" && cv.args.size == 2 &&
  (match tabs.ty cv.type with
   | .tuple (.ptr _ :: .mem :: _) => true
   | _ => false) &&
  ((((Sem.callABI? tabs cv.aux).map (·.params.toList)).getD []).filter (·.out)).length == 1 &&
  (match ((((Sem.callABI? tabs cv.aux).map (·.params.toList)).getD []).filter
      (!·.out)).map (tabs.ty ·.type) with
   | [.ptr _] => true
   | _ => false) &&
  (f.value? cv.args[0]!).any fun a => a.op == .Addr && (WBCheck.symName? tabs a.aux).isSome

/-- A malloc call that returns a fresh zeroed block: a malloc-family `StaticLECall`
(`NilCheck.mallocCall`) that is `freshSC` or `freshNew`. Under `Sem.Env.AllocZero` (and, for
`newobject`, `fwdRoOK`) its first result points to a heap block that is all zero in its
memory. -/
def freshCall (tabs : Tables) (f : Func) (c : ID) : Bool :=
  NilCheck.mallocCall tabs f c &&
  match f.value? c with
  | some cv => freshSC tabs f cv || freshNew tabs f cv
  | none => false

/-- The size and pointer-bytes words of a type descriptor whose bytes are `a`'s
(`Sem.Runtime.typeInfo` of a pointer to its start). -/
def roTypeInfo? (a : Sem.Alloc) : Option (Nat × Nat) :=
  if 16 ≤ a.data.size then
    match Sem.bytesNat? (a.data.extract 0 8), Sem.bytesNat? (a.data.extract 8 16) with
    | some s, some pb => some (s, pb)
    | _, _ => none
  else none

/-- The type argument of the `freshNew` call `c` of `f` is an `Addr` of a read-only symbol of
`ro` whose type descriptor has a positive size (`roTypeInfo?`). -/
def newSymOK (tabs : Tables) (ro : List (String × Sem.Alloc)) (f : Func) (c : ID) : Bool :=
  (f.value? c).any fun cv => (f.value? cv.args[0]!).any fun a =>
    (WBCheck.symName? tabs a.aux).any fun n =>
      ro.any fun e => e.1 == n && (roTypeInfo? e.2).any (0 < ·.1)

/-- The read-only symbol `aux` names in `tabs`, with its allocation in the global image
(`Sem.globalImage`): an `SRODATA` symbol with exported bytes (`Sem.rodataBytes?`,
`Sem.rodataAlloc`), or a type descriptor (`typeinfo` set, `Sem.typeDescAlloc`: the size and
pointer-bytes words `newobject` reads, issue #69). -/
def roSym? (tabs : Tables) (aux : Option AuxRef) : Option (String × Sem.Alloc) :=
  match aux.bind tabs.aux? with
  | some { kind := .sym name _ kind size _ ti itab data relocs rt, .. } =>
    match kind, Sem.rodataBytes? data ti itab, ti with
    | "SRODATA", some d, _ => some (name.toStringLossy, Sem.rodataAlloc d size relocs)
    | _, _, some t => some (name.toStringLossy, Sem.typeDescAlloc tabs t rt)
    | _, _, _ => none
  | _ => none

/-- The read-only data symbols `f`'s `Addr`s name in `tabs`, with their allocations: the
symbols the precondition `RoImage` of the rewrite passes pins for their input. -/
def roSyms (tabs : Tables) (f : Func) : List (String × Sem.Alloc) :=
  f.valueTab.toList.filterMap fun o => o.bind fun v =>
    if v.op == .Addr then roSym? tabs v.aux else none

/-- The forwarding layer's read-only condition on `f` (issue #69): if `f` has `freshNew` calls,
their type arguments pass `newSymOK` against the read-only symbols `ro` of the precondition
(`Sem.RoImage`), and `f` passes `WBCheck.memTyOK` (so every memory a run of `f` holds keeps
them). -/
def fwdRoOK (tabs : Tables) (ro : List (String × Sem.Alloc)) (f : Func) : Bool :=
  let ns := (List.range f.valueTab.size).filter fun c =>
    NilCheck.mallocCall tabs f c && (f.value? c).any (freshNew tabs f)
  ns.isEmpty || (WBCheck.memTyOK tabs f && ns.all (newSymOK tabs ro f))

/-- Memory `m` of `f` holds zero bytes at the `n` bytes at pointer `p` where they can be read:
through at most `d` `Copy`s, `Store`s at pointers disjoint from them (`disjointB`) and `VarDef`s
of a variable that is not a `PAUTO` (`Tables.varDefPoisons`: the identity on memory, so
`generic.rules:2159`'s `Zero` over `VarDef (Zero …)` drops), a
`Zero [k] q _` with `p` at offset `o` of `q` (`ptrBase`, `baseSameB`) and `o + n ≤ k`, or the
memory `SelectN [1] c` of a call `c` that returns a fresh zeroed block (`freshCall`) with `p`
in its first result `SelectN [0] c` (`ptrBase`, of pointer shape). -/
def zeroChain (tabs : Tables) (f : Func) (p : ID) (n : Nat) : Nat → ID → Bool
  | 0, _ => false
  | d + 1, m =>
    match f.value? m with
    | some s =>
      (s.op == .Copy && s.args.size == 1 && zeroChain tabs f p n d s.args[0]!) ||
      ((s.op == .Store || s.op == .StoreWB) && s.args.size == 3 &&
        disjointB tabs f p n s.args[0]! (Sem.auxTy tabs s.aux).size &&
        zeroChain tabs f p n d s.args[2]!) ||
      (s.op == .Zero && s.args.size == 2 &&
        decide (((ptrBase tabs f 8 p).2 - (ptrBase tabs f 8 s.args[0]!).2).toNat + n ≤
          s.auxInt.toInt.toNat) &&
        baseSameB tabs f 8 (ptrBase tabs f 8 p).1 (ptrBase tabs f 8 s.args[0]!).1) ||
      (s.op == .SelectN && s.auxInt == 1 && s.args.size == 1 && freshCall tabs f s.args[0]! &&
        ptrVal tabs f (ptrBase tabs f 8 p).1 &&
        match f.value? (ptrBase tabs f 8 p).1 with
        | some q => q.op == .SelectN && q.auxInt == 0 && q.args.size == 1 &&
            q.args[0]! == s.args[0]!
        | none => false) ||
      (s.op == .VarDef && s.args.size == 1 && s.aux.any (fun x => !tabs.varDefPoisons x) &&
        zeroChain tabs f p n d s.args[0]!)
    | none => false

/-- The zero constant a `Load` of shape `t` reading zero bytes becomes (`generic.rules:882`–`:902`):
`ConstBool` at `bool`, `Const8`/`Const16`/`Const32`/`Const64` at the integer widths. -/
def zeroLdOp (t : Sem.Ty) (op : Op) : Bool :=
  match t with
  | .bool => op == .ConstBool
  | .int .w8 => op == .Const8
  | .int .w16 => op == .Const16
  | .int .w32 => op == .Const32
  | .int .w64 => op == .Const64
  | _ => false

/-- The `Load` `u` of `f` reads zero bytes and becomes the zero constant `w`
(`generic.rules:882`–`:902`, `(Load <t1> (OffPtr [o] p1) (Zero [n] p2 _)) && isSamePtr(p1, p2) &&
n >= o + size => (Const* [0])`): `w` an argument-less `zeroLdOp` of `u`'s shape and auxint 0, and
the Load's memory holds zeros at its pointer for its shape's size (`zeroChain`, eight deep). -/
def fwdZeroOK (tabs : Tables) (f : Func) (u w : Value) : Bool :=
  u.op == .Load && u.args.size == 2 && zeroLdOp (tabs.ty u.type) w.op && w.args.size == 0 &&
    w.auxInt == 0 && zeroChain tabs f u.args[0]! (tabs.ty u.type).size 8 u.args[1]!

/-- Whether pointers `a` and `b` of `f` are equal wherever both read as pointers, if the
validator can tell: from one base (`baseSameB` of their `ptrBase`s) they are iff their offsets
are; from the starts of two different known allocations (`baseBlk?`: frame variables of
`LocalAddr`s, globals of `Addr`s) they are not. -/
def ptrCmp? (tabs : Tables) (f : Func) (a b : ID) : Option Bool :=
  let pa := ptrBase tabs f 8 a
  let pb := ptrBase tabs f 8 b
  if baseSameB tabs f 8 pa.1 pb.1 then some (pa.2 == pb.2)
  else
    match baseBlk? tabs f pa.1, baseBlk? tabs f pb.1 with
    | some x, some y => if x != y then some false else none
    | _, _ => none

/-- The pointer comparison `u` of `f` (`EqPtr`/`NeqPtr`) becomes the constant `w`
(`generic.rules:1649`–`:1676`: `LocalAddr`s, `Addr`s and `OffPtr`s of them, `isSamePtr` bases):
an argument-less `ConstBool` whose value is the comparison `ptrCmp?` tells. -/
def ptrCmpOK (tabs : Tables) (f : Func) (u w : Value) : Bool :=
  (u.op == .EqPtr || u.op == .NeqPtr) && u.args.size == 2 && w.op == .ConstBool &&
    w.args.size == 0 &&
    match ptrCmp? tabs f u.args[0]! u.args[1]! with
    | some e => (w.auxInt != 0) == (e != (u.op == .NeqPtr))
    | none => false

/-- `y` is listed in `g` (`Proof.listedDefs`): a value of a block of `g` that lists it. -/
def listedB (g : Func) (y : ID) : Bool :=
  (g.value? y).any fun v => g.blocks.contains v.block && (g.block? v.block).any (·.values.contains y)

/-- `w` is `a`, or reached from `a` through at most `n` `Copy`s listed in `g` (`listedB`): a
memory one of them holds is the one `w` holds (`retype` keeps only memories as memories). -/
def memCopyReach (g : Func) : Nat → ID → ID → Bool
  | 0, a, w => a == w
  | n + 1, a, w =>
    a == w ||
    (listedB g a &&
      match g.value? a with
      | some x => x.op == .Copy && x.args.size == 1 && memCopyReach g n x.args[0]! w
      | none => false)

/-- The memory `w` of `g` holds what the memory `a` of `f` does: `w` is reached from `a` through
compatible copies of `f` (`copyReach`: copy elimination ran before the rule matched), or through
copies of `g` (`memCopyReach`: the writes between were dropped in the same layer, issue #69). -/
def memReach (tabs : Tables) (f g : Func) (a w : ID) : Bool :=
  copyReach tabs f.valueTab f.valueTab.size a w || memCopyReach g g.valueTab.size a w

/-- The shapes a `Load` and a `Store` at the same shape write back as a refinement of the bytes
read: a narrow integer or a `bool` (`decodeInt` of bytes that are not all concrete, and `decode`
of a byte other than `0` or `1` at `bool`, are `poison`, whose encoding is `poison` bytes;
concrete bytes encode back to themselves). Not the word shapes: a stored pointer reloads as its
address word, whose bytes do not refine its fragments. -/
def wbTy : Sem.Ty → Bool
  | .int .w8 | .int .w16 | .int .w32 | .bool => true
  | _ => false

/-- The `Store` `u` of `f` writes back what a `Load` of its own memory read at an equal pointer
(`generic.rules:919`, `(Store {t1} p1 (Load <t2> p2 mem) mem) && isSamePtr(p1, p2) && t2.Size()
== t1.Size() => mem`): its value a `Load` of `u`'s memory argument (the same ID) at a pointer
equal to `u`'s (`samePtrB`), the `Load`'s shape `u`'s, a `wbTy` one. -/
def writeBackOK (tabs : Tables) (f : Func) (u : Value) : Bool :=
  wbTy (Sem.auxTy tabs u.aux) &&
  match f.value? u.args[1]! with
  | some ld => ld.op == .Load && ld.args.size == 2 && ld.args[1]! == u.args[2]! &&
      Sem.Ty.beq (tabs.ty ld.type) (Sem.auxTy tabs u.aux) && samePtrB tabs f u.args[0]! ld.args[0]!
  | none => false

/-- The memory root `u` of `f` becomes `w` in `g`, a `Copy` of its memory (`memReach` from `u`'s
memory argument), as its write changes no byte (`generic.rules:1005`, `:943`, `:948`, `:954`,
`:961`, `:2158`, `:2159`, `:1352`, `:1357`, `:1362`): a `Store` of zero bytes (of a zero-sized
type), a `Store` of a `zeroConst` into zero bytes (`zeroChain` through at most eight `Copy`s,
`Store`s and non-poisoning `VarDef`s), a `Zero` of a `Zero` of the same size at an equal pointer
(`samePtrB`, reached through copies of `f`), or a `Zero` of zero bytes (`zeroChain`; `:2159`'s
`Zero` over `VarDef (Zero …)`); or as it writes back the bytes a `Load`
read there, or `poison` (`writeBackOK`, `:919`). -/
def dropOK (tabs : Tables) (f g : Func) (u w : Value) : Bool :=
  w.op == .Copy && w.args.size == 1 &&
  ((u.op == .Store && u.args.size == 3 &&
    memReach tabs f g u.args[2]! w.args[0]! &&
    ((Sem.auxTy tabs u.aux).size == 0 ||
      (zeroConst tabs f u.args[1]! &&
        zeroChain tabs f u.args[0]! (Sem.auxTy tabs u.aux).size 8 u.args[2]!))) ||
   (u.op == .Zero && u.args.size == 2 &&
    ((copyReach tabs f.valueTab f.valueTab.size u.args[1]! w.args[0]! &&
      match f.value? w.args[0]! with
      | some z => z.op == .Zero && z.args.size == 2 && z.auxInt == u.auxInt &&
          samePtrB tabs f u.args[0]! z.args[0]!
      | none => false) ||
     (memReach tabs f g u.args[1]! w.args[0]! &&
      zeroChain tabs f u.args[0]! u.auxInt.toInt.toNat 8 u.args[1]!))) ||
   (u.op == .Store && u.args.size == 3 && memReach tabs f g u.args[2]! w.args[0]! &&
    writeBackOK tabs f u))

/-- The inner `Move` `im` of a changed `Move` source (`moveSrcOK`): of `u`'s size, its
destination equal to `u`'s source (`samePtrB`), its source reaching `w`'s through compatible
copies and disjoint from its destination (`disjointB`); under a `VarDef` of the frame variable
`B` (`some B`), its source in a known allocation other than `B` (`baseBlk?`) or, for a frame
temporary `B`, an argument's pointer (`argPtrB`). -/
def moveInnerOK (tabs : Tables) (f : Func) (u w im : Value) (B : Option Sem.Blk) : Bool :=
  im.op == .Move && im.args.size == 3 && im.auxInt == u.auxInt &&
  samePtrB tabs f u.args[1]! im.args[0]! &&
  copyReach tabs f.valueTab f.valueTab.size im.args[1]! w.args[1]! &&
  disjointB tabs f im.args[1]! u.auxInt.toInt.toNat im.args[0]! u.auxInt.toInt.toNat &&
  match B with
  | none => true
  | some b => (baseBlk? tabs f (ptrBase tabs f 8 im.args[1]!).1).any (· != b) ||
      (tempBlk b && argPtrB tabs f 8 im.args[1]!)

/-- The `Move` `u` of `f` becomes the `Move` `w` that reads its bytes where the `Move` below its
memory copied them from (`generic.rules:2146`, `:2155`): `w` is `u` with another source, its
destination and memory reached from `u`'s through compatible copies (`copyReach`), and `w`'s
memory is a `Move` `moveInnerOK` accepts, or a `VarDef` (of activation 0's frame variable, as
`Sem.frameBlk`) of one. -/
def moveSrcOK (tabs : Tables) (f : Func) (u w : Value) : Bool :=
  u.op == .Move && w.op == .Move && u.args.size == 3 && w.args.size == 3 &&
  w.auxInt == u.auxInt && w.aux == u.aux &&
  copyReach tabs f.valueTab f.valueTab.size u.args[0]! w.args[0]! &&
  copyReach tabs f.valueTab f.valueTab.size u.args[2]! w.args[2]! &&
  match f.value? w.args[2]! with
  | some mv =>
    moveInnerOK tabs f u w mv none ||
    (mv.op == .VarDef && mv.args.size == 1 &&
      match mv.aux, f.value? mv.args[0]! with
      | some n, some im => moveInnerOK tabs f u w im (some (Sem.frameBlk tabs 0 n))
      | _, _ => false)
  | none => false

/-- What a `Load` of shape `t` reads at offset `o` of the read-only symbol `n` from its
allocation `a` alone, retyped (`fixedOK`), at `Addrs.fixed` (`Mem.loadC`, `Val.retypeC`): if the
allocation and the value hold no frame pointer, so that every instance reads it alike. -/
def fixedSrc (n : String) (a : Sem.Alloc) (t : Sem.Ty) (o : BitVec 64) : Option Sem.Val :=
  let m := ({} : Sem.Mem).set (.global n) a
  if m.lowB then
    let v := m.loadC t ((⟨.global n, 0⟩ : Sem.Ptr).add o)
    if v.lowB then some (v.retypeC t) else none
  else none

/-- `a` is `poison`, or the integer or pointer `b` (`fixedOK`). -/
def fixedEq : Sem.Val → Sem.Val → Bool
  | .poison, _ => true
  | .int w x, .int w' y => if h : w = w' then (h ▸ x) == y else false
  | .ptr p, .ptr q => p == q
  | _, _ => false

/-- The value `w` a fixed load (`generic.rules:2251`, `:2255`, `rewriteFixedLoad`, issue #69)
gives the `Load` `u` of `f`: the Load's pointer is an `Addr` of a read-only symbol `n` of `ro`
(`baseBlk?`) at a constant offset (`ptrBase`), and the read at that offset from the symbol's
allocation alone (`fixedSrc`) is `poison` or `w`'s value (`fixedEq`); `w` is an argument-less
`Const64`, `Const32` or `Const8`, or an `Addr` (whose value ignores its argument,
`Rules.opVal_addr`). `f` passes `WBCheck.memTyOK`, so the memory the Load reads holds the symbols
`ro` (`LoadFwd.FwdQ`). -/
def fixedOK (tabs : Tables) (ro : List (String × Sem.Alloc)) (f : Func) (u w : Value) : Bool :=
  u.op == .Load && u.args.size == 2 &&
  (w.op == .Addr || ((w.op == .Const64 || w.op == .Const32 || w.op == .Const8) && w.args.size == 0)) &&
  (match baseBlk? tabs f (ptrBase tabs f 8 u.args[0]!).1 with
   | some (.global n) =>
     ro.any fun e => e.1 == n &&
       match fixedSrc n e.2 (tabs.ty u.type) (ptrBase tabs f 8 u.args[0]!).2,
           GoFV.Proof.Rules.opValC tabs w.op (tabs.ty u.type) w.auxInt w.aux [] with
       | some s, some r => fixedEq s (r.retypeC (tabs.ty u.type))
       | _, _ => false
   | _ => false) &&
  WBCheck.memTyOK tabs f

/-- A call of `runtime.growslice` or `runtime.growsliceNoAlias` (whose contract returns a slice of
the requested length, `Sem.Env.GrowLen`): a `StaticLECall` with six arguments (`oldPtr`,
`newLen`, `oldCap`, `num`, `et`, the memory) of a type `(slice, …)`, its second ABI parameter of
the 64-bit integer shape and its one ABI result a slice. -/
def growV (tabs : Tables) (cv : Value) : Bool :=
  cv.op == .StaticLECall && cv.args.size == 6 &&
    ((cv.aux.bind tabs.callee?).any fun n =>
      n == "runtime.growslice" || n == "runtime.growsliceNoAlias") &&
    (tabs.ty cv.type matches .tuple (.slice _ :: _)) &&
    (match (((Sem.callABI? tabs cv.aux).map (·.params.toList)).getD []).filter (·.out) with
     | [o] => (tabs.ty o.type matches .slice _)
     | _ => false) &&
    (match ((((Sem.callABI? tabs cv.aux).map (·.params.toList)).getD []).filter (!·.out))[1]? with
     | some p => (tabs.ty p.type matches .int .w64)
     | none => false)

/-- The length of the slice a `growslice` call returns becomes its length argument
(`generic.rules:2128`, there a `Const64`): `u` is `SliceLen (SelectN [0] c)` of the 64-bit
integer shape, the `SelectN` of a slice shape, `c` a call `growV` accepts, and `w` is `Copy x` of
`c`'s second argument `x`. -/
def growOK (tabs : Tables) (f : Func) (u w : Value) : Bool :=
  u.op == .SliceLen && u.args.size == 1 && (tabs.ty u.type matches .int .w64) &&
  w.op == .Copy && w.args.size == 1 &&
  match f.value? u.args[0]! with
  | some s =>
    s.op == .SelectN && s.auxInt == 0 && s.args.size == 1 && (tabs.ty s.type matches .slice _) &&
      (f.value? s.args[0]!).any fun cv => growV tabs cv && cv.args[1]! == w.args[0]!
  | none => false

/-- A post-`expand calls` call of `runtime.growslice` or `runtime.growsliceNoAlias`
(`generic.rules:2131`): a `StaticCall` with six arguments (the register pieces of `oldPtr`,
`newLen`, `oldCap`, `num`, `et`, then the memory) of a type `(_, int, …)`, its first two ABI
parameters in one register each, the second of the 64-bit integer shape, and its one ABI result
a slice in registers. -/
def growPV (tabs : Tables) (cv : Value) : Bool :=
  cv.op == .StaticCall && cv.args.size == 6 &&
    ((cv.aux.bind tabs.callee?).any fun n =>
      n == "runtime.growslice" || n == "runtime.growsliceNoAlias") &&
    (tabs.ty cv.type matches .tuple (_ :: .int .w64 :: _)) &&
    (match (((Sem.callABI? tabs cv.aux).map (·.params.toList)).getD []).filter (·.out) with
     | [o] => (tabs.ty o.type matches .slice _) && !o.regs.isEmpty
     | _ => false) &&
    (match (((Sem.callABI? tabs cv.aux).map (·.params.toList)).getD []).filter (!·.out) with
     | i0 :: i1 :: _ => i0.regs.size == 1 && i1.regs.size == 1 && (tabs.ty i1.type matches .int .w64)
     | _ => false)

/-- The length register of a post-`expand calls` `growslice` call becomes its length argument
(`generic.rules:2131`, `(SelectN [1] (StaticCall {sym} _ newLen:(Const64) _ _ _ _)) => newLen`):
`u` is `SelectN [1] c` of the 64-bit integer shape, `c` a call `growPV` accepts, and `w` is
`Copy x` of `c`'s second argument `x`, of the 64-bit integer shape (any value: the layer's input
may still hold the `Const64`'s unfolded form, e.g. an `Add64` the same pass folds). -/
def growPOK (tabs : Tables) (f : Func) (u w : Value) : Bool :=
  u.op == .SelectN && u.auxInt == 1 && u.args.size == 1 && (tabs.ty u.type matches .int .w64) &&
  w.op == .Copy && w.args.size == 1 &&
  (f.value? u.args[0]!).any (fun cv => growPV tabs cv && cv.args[1]! == w.args[0]!) &&
  (f.value? w.args[0]!).any fun x => (tabs.ty x.type matches .int .w64)

/-! ### Folded `runtime.ifaceeq`/`efaceeq` calls (`generic.rules:2279`, `:2287`, `:1343`)

`(StaticLECall {f} itab x y mem) && isSameCall(f, "runtime.ifaceeq") &&
isDirectAndComparableIface(itab) => (MakeResult (EqPtr x y) mem)` (and `efaceeq` with
`isDirectAndComparableType`) turns the call root into a term; the `SelectN`s of its result
become the `EqPtr` and the memory by `(SelectN [n] m:(MakeResult ___)) => m.Args[n]`. The
validator accepts the fold of a call whose descriptor is, statically, the start of a symbol of
the precondition's list (`eqPass`: the symbols of the pass's and the frontend's tables whose type
the export marks direct-interface and comparable), under whose contract (`Sem.Env.IfaceEq`) the
call returns `x == y` and its memory;
the selections are checked per instance (`selMROK`). -/

/-- An interface shape whose first word (the itab or type word) has a word shape (`wordTy`): two
fields, as `Sem.Ty.ofType` lays out an `INTER`. -/
def ifaceTy : Sem.Ty → Bool
  | .agg [(_, t0), _] _ => wordTy t0
  | _ => false

mutual
/-- The aux of the `Addr` whose global's start the word `a` of `f` holds, statically (at most `n`
deep): an `Addr`, a `Copy` of such a word, or the `ITab` of such an interface (`eqDescI`), each of
a word shape (`wordTy`). -/
def eqDescW (tabs : Tables) (f : Func) : Nat → ID → Option AuxRef
  | 0, _ => none
  | n + 1, a =>
    match f.value? a with
    | some u =>
      if !wordTy (tabs.ty u.type) then none
      else if u.op == .Addr then u.aux
      else if u.op == .Copy && u.args.size == 1 then eqDescW tabs f n u.args[0]!
      else if u.op == .ITab && u.args.size == 1 then eqDescI tabs f n u.args[0]!
      else none
    | none => none
/-- `eqDescW` of the first word of the interface `a` of `f`: an `IMake` of such a word or a `Copy`
of such an interface, each of an interface shape (`ifaceTy`). -/
def eqDescI (tabs : Tables) (f : Func) : Nat → ID → Option AuxRef
  | 0, _ => none
  | n + 1, a =>
    match f.value? a with
    | some u =>
      if !ifaceTy (tabs.ty u.type) then none
      else if u.op == .IMake && u.args.size == 2 then eqDescW tabs f n u.args[0]!
      else if u.op == .Copy && u.args.size == 1 then eqDescI tabs f n u.args[0]!
      else none
    | none => none
end

/-- The name of the symbol aux `ax` defines. -/
def eqSymName? (tabs : Tables) (ax : AuxRef) : Option String :=
  match tabs.aux? ax with
  | some { kind := .sym name .., .. } => some name.toStringLossy
  | _ => none

/-- Aux `ax` is an itab symbol (`itab`, `ifaceeq`'s descriptor) or a type descriptor symbol
(`efaceeq`'s) whose type the export marks direct-interface and comparable
(`Rules.isDirectAndComparableIface`/`…Type`: `types.IsDirectIface`, `types.IsComparable`). -/
def eqSymOK (tabs : Tables) (itab : Bool) (ax : AuxRef) : Bool :=
  match tabs.aux? ax with
  | some { kind := .sym _ _ _ _ _ ti ii _ _ _, .. } =>
    (if itab then ii else ti).any fun t =>
      (tabs.type? t).any fun d => d.flags.direct && d.flags.comparable
  | _ => false

/-- The symbols of `tabs` (its `.sym` auxes) whose type the export marks direct-interface and
comparable (`eqSymOK`): its itab symbols if `itab`, else its type descriptor symbols. -/
def eqSymsOf (tabs : Tables) (itab : Bool) : List String :=
  (List.range tabs.auxes.size).filterMap fun n =>
    if eqSymOK tabs itab n then eqSymName? tabs n else none

/-- The descriptor symbols of `tabs` the precondition `Sem.Env.IfaceEq` may name: its itab
symbols (`runtime.ifaceeq`'s descriptors) and its type symbols (`runtime.efaceeq`'s) whose types
are direct-interface and comparable. It does not depend on a function's calls, so a pass that
resolves a new descriptor chain or takes a symbol from the frontend keeps the list. -/
def eqSyms (tabs : Tables) : List String × List String :=
  (eqSymsOf tabs true, eqSymsOf tabs false)

/-- The descriptor symbols the precondition of the rewrite passes on tables `tabs` with the
frontend tables `fe` names: `eqSyms` of both (passes take new symbols from the frontend, as for
the read-only symbols, `roPass`). -/
def eqPass (tabs fe : Tables) : List String × List String :=
  ((eqSyms tabs).1 ++ (eqSyms fe).1, (eqSyms tabs).2 ++ (eqSyms fe).2)

/-- A call of `runtime.ifaceeq` or `runtime.efaceeq`: a `StaticLECall` with four arguments (the
descriptor, the two data words, the memory) of type `(bool, mem)`, its ABI's parameters three
words (`wordTy`) and its one result a register-assigned `bool` (`encodeResults` stores
nothing). -/
def eqCallSig (tabs : Tables) (cv : Value) : Bool :=
  cv.op == .StaticLECall && cv.args.size == 4 &&
    ((cv.aux.bind tabs.callee?).any fun n => n == "runtime.ifaceeq" || n == "runtime.efaceeq") &&
    (tabs.ty cv.type matches .tuple [.bool, .mem]) &&
    (match (((Sem.callABI? tabs cv.aux).map (·.params.toList)).getD []).filter (·.out) with
     | [o] => (tabs.ty o.type matches .bool) && !o.regs.isEmpty
     | _ => false) &&
    (match (((Sem.callABI? tabs cv.aux).map (·.params.toList)).getD []).filter (!·.out) with
     | [p0, p1, p2] => wordTy (tabs.ty p0.type) && wordTy (tabs.ty p1.type) &&
         wordTy (tabs.ty p2.type)
     | _ => false)

/-- The symbols of the list `eq` (`eqPass`) the descriptor of the call `cv` may name: the itab
symbols for `runtime.ifaceeq`, the type symbols for `runtime.efaceeq`. -/
def eqList (tabs : Tables) (eq : List String × List String) (cv : Value) : List String :=
  if cv.aux.bind tabs.callee? == some "runtime.ifaceeq" then eq.1 else eq.2

/-- A call (`eqCallSig`) whose descriptor holds the start of a symbol of its list (`eqDescW`,
`eqList`). -/
def eqCallV (tabs : Tables) (eq : List String × List String) (f : Func) (cv : Value) : Bool :=
  eqCallSig tabs cv &&
    ((eqDescW tabs f 8 cv.args[0]!).bind (eqSymName? tabs)).any (eqList tabs eq cv).contains

/-- The call `u` of `f` (`eqCallV`) becomes `w = MakeResult q m` in `g` (`generic.rules:2279`,
`:2287`): `m` its memory argument and `q` a listed `EqPtr x y` of `bool` shape of its data
arguments, each reached through compatible copies of `f` (`copyReach`). -/
def eqCallOK (tabs : Tables) (eq : List String × List String) (f g : Func) (u w : Value) : Bool :=
  eqCallV tabs eq f u && w.op == .MakeResult && w.args.size == 2 &&
    copyReach tabs f.valueTab f.valueTab.size u.args[3]! w.args[1]! && listedB g w.args[0]! &&
    match g.value? w.args[0]! with
    | some q => q.op == .EqPtr && q.args.size == 2 && (tabs.ty q.type matches .bool) &&
        copyReach tabs f.valueTab f.valueTab.size u.args[1]! q.args[0]! &&
        copyReach tabs f.valueTab f.valueTab.size u.args[2]! q.args[1]!
    | none => false

/-- The selection `u = SelectN [i] m` of `f` of a `MakeResult` `m` becomes `w = Copy a` of its
argument `a` (`generic.rules:1343`): `m`'s type a tuple of one component per argument, the
`i`-th `u`'s type. -/
def selMROK (tabs : Tables) (f : Func) (u w : Value) : Bool :=
  u.op == .SelectN && u.args.size == 1 && decide (0 ≤ u.auxInt.toInt) &&
    w.op == .Copy && w.args.size == 1 &&
    match f.value? u.args[0]! with
    | some m =>
      m.op == .MakeResult && decide (u.auxInt.toInt.toNat < m.args.size) &&
        w.args[0]! == m.args[u.auxInt.toInt.toNat]! &&
        match tabs.ty m.type with
        | .tuple ts => ts.length == m.args.size &&
            (ts[u.auxInt.toInt.toNat]?).any (Sem.Ty.beq · (tabs.ty u.type))
        | _ => false
    | none => false

/-- The value `a` of `f` is a call `g` folds (`eqCallOK`). -/
def dcB (tabs : Tables) (eq : List String × List String) (f g : Func) (a : ID) : Bool :=
  match f.value? a, g.value? a with
  | some u, some w => eqCallOK tabs eq f g u w
  | _, _ => false

/-- The calls `g` folds (`dcB`) are read only by a `SelectN [0]` or `[1]` of them, and are no
control. -/
def dcUsesOK (tabs : Tables) (eq : List String × List String) (f g : Func) : Bool :=
  f.valueTab.all (fun o => o.all fun u =>
    (u.op == .SelectN && u.args.size == 1 && (u.auxInt == 0 || u.auxInt == 1)) ||
      u.args.all fun a => !dcB tabs eq f g a) &&
  f.blocks.all fun b => (f.block? b).all fun fb => fb.controls.all fun c => !dcB tabs eq f g c

/-- The new definition `w` in `g` of the `Load` `u` of `f`: `Copy x` of the value `x` it reads
back (`fwdOK`), a constant of the bits it reads back (`fwdConstOK`), or the value of a fixed load
from the read-only symbols `ro` (`fixedOK`); or of the memory root `u`, a `Copy` of its memory
(`dropOK`), or a `Move` from another source (`moveSrcOK`); or of the `SliceLen` `u` of a
`growslice` result, a `Copy` of its length argument (`growOK`); or of a folded `ifaceeq`/`efaceeq`
call `u` with a descriptor symbol of `eq` (`eqCallOK`) or a selection of a `MakeResult`
(`selMROK`); or of the length register `u` of a post-`expand calls` `growslice` call, a `Copy`
of its length argument (`growPOK`); or of a `Load` `u` reading zero bytes, the zero constant
(`fwdZeroOK`); or of a pointer comparison `u`, its constant (`ptrCmpOK`). -/
def fwdNewOK (tabs : Tables) (ro : List (String × Sem.Alloc)) (eq : List String × List String)
    (f g : Func) (u w : Value) : Bool :=
  (w.op == .Copy && w.args.size == 1 && fwdOK tabs f u (w.args[0]?.getD 0)) || fwdConstOK tabs f u w ||
    dropOK tabs f g u w || moveSrcOK tabs f u w || fixedOK tabs ro f u w || growOK tabs f u w ||
    eqCallOK tabs eq f g u w || selMROK tabs f u w || growPOK tabs f u w || fwdZeroOK tabs f u w ||
    ptrCmpOK tabs f u w

/-- The `Load` `u` of `f` reads, at offset `o` (`offp`'s auxint), the bytes a `Move [n] dst src
mem` copied (`generic.rules:827`): its memory is the `Move`, its pointer `dst + o` (`ptrBase`,
`baseSameB`), `0 ≤ o` and the read (of positive size) inside the `n` bytes; `top` is
`Load <u.Type> offp mem` and `offp` the pointer-shaped `OffPtr [o] src`. -/
def fwdMoveOK (tabs : Tables) (f : Func) (u top offp : Value) : Bool :=
  u.op == .Load && u.args.size == 2 && top.op == .Load && top.type == u.type &&
  top.args.size == 2 && offp.op == .OffPtr && offp.args.size == 1 &&
  isPtrTy (tabs.ty offp.type) && decide (0 ≤ offp.auxInt.toInt) &&
  decide (0 < (tabs.ty u.type).size) &&
  match f.value? u.args[1]! with
  | some mv =>
    mv.op == .Move && mv.args.size == 3 && top.args[1]! == mv.args[2]! &&
    offp.args[0]! == mv.args[1]! &&
    decide (offp.auxInt.toInt.toNat + (tabs.ty u.type).size ≤ mv.auxInt.toInt.toNat) &&
    (ptrBase tabs f 8 u.args[0]!).2 ==
      (ptrBase tabs f 8 mv.args[0]!).2 + BitVec.ofInt 64 offp.auxInt.toInt &&
    baseSameB tabs f 8 (ptrBase tabs f 8 u.args[0]!).1 (ptrBase tabs f 8 mv.args[0]!).1
  | none => false

/-- Memory `m` of `f` reaches memory `e` through at most `d` `Copy`s and `Store`s at pointers
disjoint from the `n` bytes at pointer `p` (`disjointB`): those bytes read the same in both. -/
def sepChain (tabs : Tables) (f : Func) (p : ID) (n : Nat) (e : ID) : Nat → ID → Bool
  | 0, m => m == e
  | d + 1, m =>
    m == e ||
    match f.value? m with
    | some s =>
      (s.op == .Copy && s.args.size == 1 && sepChain tabs f p n e d s.args[0]!) ||
      ((s.op == .Store || s.op == .StoreWB) && s.args.size == 3 &&
        disjointB tabs f p n s.args[0]! (Sem.auxTy tabs s.aux).size &&
        sepChain tabs f p n e d s.args[2]!)
    | none => false

/-- The `Load` `u` of `f` reads, through `Store`s disjoint from it (`sepChain`, eight deep), the
bytes at offset `o` (`offp`'s auxint) of the pointer `q` of a `Zero` `z` (`generic.rules:842`,
`:851`, `:862`, `:875`): its pointer is `q + o` (`ptrBase`, `baseSameB`), `0 ≤ o`, its shape of
positive size; `top` is `Load <u.Type> offp z` and `offp` the pointer-shaped `OffPtr [o] q`. -/
def fwdSepOK (tabs : Tables) (f : Func) (u top offp : Value) : Bool :=
  u.op == .Load && u.args.size == 2 && top.op == .Load && top.type == u.type &&
  top.args.size == 2 && offp.op == .OffPtr && offp.args.size == 1 &&
  isPtrTy (tabs.ty offp.type) && decide (0 ≤ offp.auxInt.toInt) &&
  decide (0 < (tabs.ty u.type).size) &&
  sepChain tabs f u.args[0]! (tabs.ty u.type).size top.args[1]! 8 u.args[1]! &&
  match f.value? top.args[1]! with
  | some z =>
    z.op == .Zero && z.args.size == 2 && offp.args[0]! == z.args[0]! &&
    (ptrBase tabs f 8 u.args[0]!).2 ==
      (ptrBase tabs f 8 z.args[0]!).2 + BitVec.ofInt 64 offp.auxInt.toInt &&
    baseSameB tabs f 8 (ptrBase tabs f 8 u.args[0]!).1 (ptrBase tabs f 8 z.args[0]!).1
  | none => false

/-- The new definition `w` of the `Load` `u` of `f` in `g`: `Copy y` of the listed `Load` `y` of
`g` through the listed `OffPtr` that `fwdMoveOK` (of the `Move`'s source) or `fwdSepOK` (of the
`Zero`'s pointer) accepts. -/
def fwdMoveRep (tabs : Tables) (f g : Func) (u w : Value) : Bool :=
  w.op == .Copy && w.args.size == 1 && listedB g w.args[0]! &&
  match g.value? w.args[0]! with
  | some top =>
    top.args.size == 2 && listedB g top.args[0]! &&
    match g.value? top.args[0]! with
    | some offp => fwdMoveOK tabs f u top offp || fwdSepOK tabs f u top offp
    | none => false
  | none => false

/-- One pass of `fwdRank`, in ID order: each listed non-`Phi` value one above its arguments. -/
def rankPass (f : Func) (L : Array Bool) (rk : Array Nat) : Array Nat :=
  (List.range f.valueTab.size).foldl (init := rk) fun rk z =>
    if L[z]? == some true then
      match f.value? z with
      | some u =>
        if u.op == .Phi then rk
        else rk.set! z (u.args.foldl (fun m a => max m (rk[a]?.getD 0 + 1)) 0)
      | none => rk
    else rk

/-- `rankPass` until nothing changes (at most `n` passes). -/
def rankIter (f : Func) (L : Array Bool) : Nat → Array Nat → Array Nat
  | 0, rk => rk
  | n + 1, rk =>
    let rk' := rankPass f L rk
    if rk' == rk then rk else rankIter f L n rk'

/-- Ranks of the listed values (`fwdRankOK` checks them): the depth of their non-`Phi` arguments. -/
def fwdRank (f : Func) : Array Nat :=
  rankIter f (listedMarks f) (f.valueTab.size + 1) (Array.replicate f.valueTab.size 0)

/-- Every listed non-`Phi` value of `f` ranks above its arguments. -/
def fwdRankOK (f : Func) (rk : Array Nat) : Bool :=
  let L := listedMarks f
  (List.range f.valueTab.size).all fun z =>
    L[z]? != some true ||
    match f.value? z with
    | some u => u.op == .Phi || u.args.all fun a => rk[a]?.getD 0 < rk[z]?.getD 0
    | none => true

/-- Value `x` of `f` is unchanged in `g` (but for its use count), or a `Load` got a new definition
`fwdNewOK` (with the read-only symbols `ro` and the descriptor symbols `eq`) or `fwdMoveRep`
accepts. -/
def fwdRepOK (tabs : Tables) (ro : List (String × Sem.Alloc)) (eq : List String × List String)
    (f g : Func) (x : ID) : Bool :=
  match f.value? x, g.value? x with
  | none, _ => true
  | some _, none => false
  | some u, some w =>
    w.id == u.id && w.block == u.block && w.type == u.type &&
    ((w.op == u.op && w.auxInt == u.auxInt && w.aux == u.aux && w.args == u.args) ||
     fwdNewOK tabs ro eq f g u w || fwdMoveRep tabs f g u w)

/-- `g`'s blocks are `f`'s, but for values appended to their lists (the fresh values of a
forwarding through a `Move` or to a `Zero`, `fwdMoveRep`). -/
def blocksExtOK (f g : Func) : Bool :=
  g.blocks == f.blocks && f.blocks.all fun b =>
    match f.block? b, g.block? b with
    | some fb, some gb => gb == { fb with values := gb.values } && fb.values.all (gb.values.contains ·)
    | _, _ => false

/-- `g` is `f` with Loads forwarded (fixed loads from the read-only symbols `ro`), identity
writes dropped and `ifaceeq`/`efaceeq` calls with descriptor symbols of `eq` folded: the same
blocks (`blocksExtOK`) and atoms but the dropped roots (`atomsXOK`, which may drop calls), every
value as `fwdRepOK` says, the folded calls read only by selections (`dcUsesOK`), ranks ordering
`f`'s listed values after their arguments. -/
def fwdRel (tabs : Tables) (ro : List (String × Sem.Alloc)) (eq : List String × List String)
    (f g : Func) : Bool :=
  atomsXOK f g true && closedOK f && closedOK g && blocksExtOK f g &&
  fwdRankOK f (fwdRank f) && (List.range f.valueTab.size).all (fwdRepOK tabs ro eq f g ·) &&
  dcUsesOK tabs eq f g

/-- The variable a chain of at most `n` `Store`s binds as a stored value is `y`. -/
def storesBind (y : Nat) : Nat → Pat → Bool
  | n + 1, .op .Store none _ _ _ .fixed [_, v, m] _ =>
    (match v with | .bind z => z == y | _ => false) || storesBind y n m
  | _, _ => false

/-- The pattern binds the rule variable `y` at its top: `y` or `y:(Op …)`. -/
def patBinds (y : Nat) : Pat → Bool
  | .bind z => z == y
  | .op _ (some z) .. => z == y
  | _ => false

/-- `(Addr {s} _)` or `(Convert (Addr {s} _) _)`. -/
def addrConvPat : Pat → Bool
  | .op .Addr none _ _ _ .fixed [_] _ => true
  | .op .Convert none _ _ _ .fixed [.op .Addr none _ _ _ .fixed [_] _, .wild] _ => true
  | _ => false

/-- The pointer patterns of the fixed loads (`generic.rules:2251`–`:2258`): an `addrConvPat`,
possibly in `(ITab (IMake _ _))`, possibly in an `OffPtr`. -/
def fixedPtrPat (p : Pat) : Bool :=
  let inner : Pat → Bool := fun
    | .op .ITab none _ _ _ .fixed [.op .IMake none _ _ _ .fixed [a, .wild] _] _ => addrConvPat a
    | q => addrConvPat q
  match p with
  | .op .OffPtr none _ _ _ .fixed [q] _ => inner q
  | q => inner q

/-- A Load-of-Store forwarding rule: `(Load _ m) => x` with `x` stored by one of the up to four
`Store`s of the chain `m` (`generic.rules:800`, `:806`, `:813`, `:821`),
`(Load _ (Store _ (Const64 [x]) _)) => (Const64F [x'])` and its converse (`:830`, `:832`), or
`(Load (OffPtr [o] _) (Move _ src mem)) => @move.Block (Load (OffPtr [o] src) mem)` (`:827`) and
`(Load (OffPtr [o] _) (Store _ _ … mem:(Zero _ q _))) => @mem.Block (Load (OffPtr [o] q) mem)`
through one to four `Store`s (`:842`, `:851`, `:862`, `:875`); or
a dropped identity write `(Store _ _ mem) => mem`, `(Zero _ mem) => mem` (`:1005`, `:943`,
`:948`, `:954`, `:961`, `:2158`) and the write-back `(Store _ (Load _ mem) mem) => mem` (`:919`,
`writeBackOK`); or a changed `Move` source `(Move dst tmp m:(Move tmp' src _))
=> (Move dst src m)` and its form through a `VarDef` (`:2146`, `:2155`); the validator checks
each instance by `fwdNewOK`, `fwdMoveOK` or `fwdSepOK`, the `isSamePtr`/`disjoint` conditions
included; or a
fixed load `(Load p _) && isFixedLoad(v, s, off) => rewriteFixedLoad(v, s, sb, off)` whose
pointer `p` is `(Addr {s} _)`, through `Convert`, `ITab (IMake …)` and an `OffPtr [off]`
(`fixedPtrPat`; `generic.rules:2251`–`:2258`; `fixedOK`, which follows them by `wordStep?`); or
the length of a `growslice` result `(SliceLen (SelectN [0] (StaticLECall _ newLen:(Const64) …)))
=> newLen` (`:2128`; `growOK`) and its post-`expand calls` form `(SelectN [1] (StaticCall _
newLen:(Const64) …)) => newLen` (`:2131`; `growPOK`); or a folded `ifaceeq`/`efaceeq` call
`(StaticLECall {f} d x y mem) && … => (MakeResult (EqPtr x y) mem)` (`:2279`, `:2287`;
`eqCallOK`) or a selection of a `MakeResult` `(SelectN [n] m:(MakeResult ___)) => m.Args[n]`
(`:1343`; `selMROK`); or a `Load` of a `Zero` folded to a zero constant `(Load (OffPtr [o] p1)
(Zero [n] p2 _)) && isSamePtr(p1, p2) && n >= o + size => (Const* [0])` (`:882`–`:902`;
`fwdZeroOK`); or a pointer comparison folded to a constant `(EqPtr x y) => (ConstBool [c])`
(and `NeqPtr`; `:1649`–`:1676`, `ptrCmpOK`). -/
def fwdShapeOK (r : Rule) : Bool :=
  match r.pat, r.result, r.block with
  | .op .Load none _ _ _ .fixed [_, m] _, .copy (.var y), none => storesBind y 4 m
  | .op .Load none _ _ _ .fixed [p, .wild] _, .copy (.call "rewriteFixedLoad" _ _), none =>
    fixedPtrPat p
  | .op .Load none _ _ _ .fixed [_, .op .Store none _ _ _ .fixed [_, .op o none _ _ _ .fixed [] _, _] _]
      _, .build [n], none => const64Op o && const64Op n.op && n.args.isEmpty
  | .op .Load none _ _ _ .fixed [.op .OffPtr .., .op .Move ..] _, .build [n0, n1], some _ =>
    n0.op == .Load && n1.op == .OffPtr
  | .op .Load none _ _ _ .fixed [.op .OffPtr .., .op .Store ..] _, .build [n0, n1], some _ =>
    n0.op == .Load && n1.op == .OffPtr
  | .op .Load none _ _ _ .fixed [.op .OffPtr .., .op .Zero ..] _, .build [n], none =>
    (n.op == .ConstBool || n.op == .Const8 || n.op == .Const16 || n.op == .Const32 ||
      n.op == .Const64) && n.args.isEmpty
  | .op .Store none _ _ _ .fixed [_, .op .Load none _ _ _ .fixed [_, .bind z] _, .same z'] _,
      .copy (.var y), none => z == y && z' == y
  | .op .Store none _ _ _ .fixed [_, _, m] _, .copy (.var y), none => patBinds y m
  | .op .Zero none _ _ _ .fixed [_, m] _, .copy (.var y), none => patBinds y m
  | .op .Move none _ _ _ .fixed [_, _, .op .Move ..] _, .build [n], none => n.op == .Move
  | .op .Move none _ _ _ .fixed [_, _, .op .VarDef _ _ _ _ .fixed [.op .Move ..] _] _, .build [n],
      none => n.op == .Move
  | .op .SliceLen none _ _ _ .fixed
      [.op .SelectN none _ _ _ .fixed [.op .StaticLECall none _ _ _ _ (_ :: .op .Const64 (some y) .. :: _) _] _] _,
      .copy (.var z), none => y == z
  | .op .StaticLECall none _ _ _ (.exact 4) [_, _, _, _] _, .build [n0, n1], none =>
    n0.op == .MakeResult && n1.op == .EqPtr
  | .op .SelectN none _ _ _ .fixed [.op .MakeResult ..] _, .copy _, none => true
  | .op .SelectN none _ _ _ .fixed
      [.op .StaticCall none _ _ _ _ (_ :: .op .Const64 (some y) .. :: _) _] _, .copy (.var z),
      none => y == z
  | .op .EqPtr none _ _ _ .fixed [_, _] _, .build [n], none => n.op == .ConstBool && n.args.isEmpty
  | .op .NeqPtr none _ _ _ .fixed [_, _] _, .build [n], none => n.op == .ConstBool && n.args.isEmpty
  | _, _, _ => false

/-- The `Load` `v` of `f` that event `ev` forwards (or the `Store`/`Zero` it drops, the `Move`
whose source it changes, the `SliceLen` of a `growslice` result, the call it folds, the
`SelectN` of a `MakeResult` or the pointer comparison it folds), its new definition (a `Copy`, a
constant, an `Addr`, a `Move` or a `MakeResult`) and the fresh values to put in first (`:827`:
the `OffPtr`, then the `Load`; a folded call: its `EqPtr`, logged after the call's definition
twice, `Interp.tryRule`), if it is a `loads` rule event (`fwdShapeOK`; tried on a `Store` after
its `structStores`, `Interp.rewriteValue`). -/
def fwdEvent? (t : Interp.Table) (f : Func) : RwEvent → Option (ID × Value × List Value)
  | .rule v i _ defs =>
    match f.value? v with
    | some u =>
      if u.op == .Load || u.op == .Store || u.op == .Zero || u.op == .Move || u.op == .SliceLen ||
          u.op == .StaticLECall || u.op == .SelectN || u.op == .EqPtr || u.op == .NeqPtr then
        let n := ((t.values[u.op.ctorIdx]?).map (·.size)).getD 0 +
          if u.op == .Store then t.structStores.size else 0
        if n ≤ i then
          match t.loads[i - n]?, defs.toList with
          | some cr, [w, top, offp] =>
            if fwdShapeOK cr.rule && w.op == .MakeResult && offp.op == .EqPtr then
              some (v, w, [offp])
            else if fwdShapeOK cr.rule && w.op == .Copy && w.args.size == 1 && top.op == .Load then
              some (v, w, [offp, top])
            else none
          | some cr, w :: _ =>
            if fwdShapeOK cr.rule &&
                ((w.op == .Copy && w.args.size == 1) || const64Op w.op || w.op == .Move ||
                  w.op == .Addr || w.op == .Const32 || w.op == .Const8 || w.op == .Const16 ||
                  w.op == .ConstBool) then
              some (v, w, [])
            else none
          | _, _ => none
        else none
      else none
    | none => none
  | _ => none

/-- Put the logged fresh value `u` into `f`: at its ID (taken off the free list, as the pass
allocated it), listed last in its block, its arguments gaining a use. -/
def ssPut (f : Func) (u : Value) : Func :=
  let f := { f with valueTab := Func.tabPut f.valueTab u.id { u with uses := 0 },
                    freeValues := f.freeValues.erase u.id, vidLast := max f.vidLast u.id }
  let f := f.modB u.block fun b => { b with values := b.values.push u.id }
  u.args.foldl Func.incUses f

/-- `v.reset(OpCopy); v.AddArg(x)` (or `v.reset(OpConst64F); v.AuxInt = …`): the `Load` (or
dropped `Store`/`Zero`) `v` of `f` gets the definition `w`, its arguments lose a use, `w`'s gain
one. -/
def fwdCopy (f : Func) (v : ID) (w : Value) : Func :=
  match f.value? v with
  | some u =>
    let f := u.args.foldl (fun f a => f.modV a fun z => { z with uses := z.uses - 1 }) f
    let f := w.args.foldl (fun f a => f.modV a fun z => { z with uses := z.uses + 1 }) f
    f.modV v fun z => { z with op := w.op, auxInt := w.auxInt, aux := w.aux, args := w.args }
  | none => f

/-- The forwarding of the `Load` `u` of `f` to `w` with the fresh values `ds` (`fwdEvent?`) is
one the validator accepts in `f` alone: `fwdNewOK` (with `f` for the output, so a dropped write
whose memory was dropped in the same layer is not selected; fixed loads from the read-only
symbols `ro`, folds of calls with descriptor symbols of `eq`), `fwdMoveOK` or `fwdSepOK` of the
fresh `[offp, top]` with `w` a `Copy` of `top`, or `eqCallOK` with the fresh `EqPtr` put in. -/
def fwdEvOK (tabs : Tables) (ro : List (String × Sem.Alloc)) (eq : List String × List String)
    (f : Func) (u w : Value) : List Value → Bool
  | [] => fwdNewOK tabs ro eq f f u w
  | [q] => eqCallOK tabs eq f (ssPut f q) u w
  | [offp, top] =>
    w.args == #[top.id] && top.args[0]! == offp.id &&
      (fwdMoveOK tabs f u top offp || fwdSepOK tabs f u top offp)
  | _ => false

/-- One event of `fwdPre`: a forwarding of `f` is applied (with `sel` only one `fwdEvOK` holds of
in `f` and not at a value of `late`; its fresh values put in first), any other event kept, but for
the copy-argument replacements of the forwarded `Load` logged before it (copy elimination on the
`Load`'s arguments, which the forwarding validated in `f` replaces). -/
def fwdStep (t : Interp.Table) (tabs : Tables) (ro : List (String × Sem.Alloc))
    (eq : List String × List String) (sel : Bool) (late : List ID) (f : Func)
    (p : Func × Array RwEvent) (ev : RwEvent) : Func × Array RwEvent :=
  match fwdEvent? t f ev with
  | some (v, w, ds) =>
    if sel && (late.contains v || !(f.value? v).any (fwdEvOK tabs ro eq f · w ds)) then
      (p.1, p.2.push ev)
    else (fwdCopy (ds.foldl ssPut p.1) v w, p.2.filter fun | .copyArg z _ _ => z != v | _ => true)
  | none => (p.1, p.2.push ev)

/-- The input with the log's Load-of-Store forwardings applied (with `sel` only those `fwdEvOK`
holds of, with `f`'s read-only symbols and the descriptor symbols of `tabs`, and none at a value
of `late`), and the remaining events. -/
def fwdPre (t : Interp.Table) (tabs : Tables) (sel : Bool) (late : List ID) (f : Func)
    (log : Array RwEvent) : Func × Array RwEvent :=
  log.foldl (fwdStep t tabs (if sel then roSyms tabs f else [])
    (if sel then eqSyms tabs else ([], [])) sel late f) (f, #[])

/-! ## Struct-store splits (issues #151, #17)

`(Store _ (StructMake ___) _) => rewriteStructStore(v)` (`generic.rules:975`, `dec.rules:123`)
replaces the root `v = Store {T} dst (StructMake a₁ … aₙ) mem` by a chain of fresh field stores
`sᵢ = Store {Tᵢ} (OffPtr [oᵢ] dst) aᵢ sᵢ₋₁` (`s₀ = mem`), and `v` becomes `Copy sₙ`. The
decompose rules of a `Store` of a builtin `Make` (`dec.rules:23 :35 :51 :72 :93 :129`, e.g.
`(Store dst (StringMake ptr len) mem) => (Store {int} (OffPtr [8] dst) len (Store {*uint8} dst
ptr mem))`) split it in place: `v` becomes the chain's last store, the first one at `dst`
itself. The roots change, so the validator takes these events out of the log, as the
forwardings: `ssPre` applies them to the input (the logged fresh values put in, then
`v.copyOf(sₙ)` or `v` redefined as logged), `ssRel` relates the input to that function, and
`validate` the output to it with the other events. -/

/-- A struct-store split rule: `(Store …) => rewriteStructStore(v)`, or a `Store` rule with a
built result in `v`'s block (an in-place split); each instance is validated by `ssRel`. -/
def structStoreShapeOK (r : Rule) : Bool :=
  match r.pat, r.result, r.block with
  | .op .Store .., .copy (.call "rewriteStructStore" [.rsv .v] _), none => true
  | .op .Store .., .build _, none => true
  | _, _, _ => false

/-- The `Store` `v` of `f` that event `ev` splits, its logged definition `w` (a `Copy` of the
chain's last store, or that store itself) and the fresh values (`Interp.structStoreDefs`, or the
built ones), if it is a `structStores` rule event (`structStoreShapeOK`). -/
def ssEvent? (t : Interp.Table) (f : Func) : RwEvent → Option (ID × Value × List Value)
  | .rule v i _ defs =>
    match f.value? v with
    | some u =>
      if u.op == .Store then
        let n := ((t.values[u.op.ctorIdx]?).map (·.size)).getD 0
        if n ≤ i then
          match t.structStores[i - n]?, defs.toList with
          | some cr, w :: ds =>
            if structStoreShapeOK cr.rule &&
                ((w.op == .Copy && w.args.size == 1) ||
                  (w.op == .Store && w.id == v && w.args.size == 3)) then
              some (v, w, ds.filter (·.id != v))
            else none
          | _, _ => none
        else none
      else none
    | none => none
  | _ => none

/-- The split of the `Store` `v` with its logged definition `w`: the fresh values `ds` put in,
then `v.copyOf(x)` for a `Copy` of `x`, else `v` redefined as `w` (its arguments losing a use,
`w`'s gaining one; the built values `ds`, logged parents first, put in children first). -/
def ssApply (f : Func) (v : ID) (w : Value) (ds : List Value) : Func :=
  match f.value? v with
  | some u =>
    if u.op == .Store then
      if w.op == .Copy then (ds.foldl ssPut f).copyOf v w.args[0]!
      else
        let f := u.args.foldl (fun f a => f.modV a fun z => { z with uses := z.uses - 1 }) f
        let f := w.args.foldl Func.incUses (ds.reverse.foldl ssPut f)
        f.modV v fun z => { z with op := w.op, auxInt := w.auxInt, aux := w.aux, args := w.args }
    else f
  | none => f

/-- The events `evs` replace argument `i` of `v` (copy elimination). -/
def copyArgOf (evs : Array RwEvent) (v : ID) (i : Nat) : Bool :=
  evs.any fun | .copyArg y j _ => y == v && j == i | _ => false

/-- The first store of a split's logged chain: of its stores (`w` itself when in place, the fresh
values `ds`), the one whose memory is none of them. -/
def ssFirst (v : ID) (w : Value) (ds : List Value) : Option ID :=
  let sts := (if w.op == .Store then w :: ds else ds).filter (·.op == .Store)
  let ids := v :: sts.map (·.id)
  (sts.find? fun s => !ids.contains (s.args[2]?.getD 0)).map (·.id)

/-- The value `a` of `f` stands for through at most `n` `Copy`s each compatible with its
argument (`copyReach` reaches it). -/
def copyEnd (tabs : Tables) (M : Defs) : Nat → ID → ID
  | 0, a => a
  | n + 1, a =>
    match M.get? a with
    | some x =>
      if x.op == .Copy && x.args.size == 1 &&
          (match M.get? x.args[0]! with
            | some y => copyCompat (tabs.ty x.type) (tabs.ty y.type)
            | none => false) then copyEnd tabs M n x.args[0]!
      else a
    | none => a

/-- The `Make` ops: `StructMake`, `StringMake`, `SliceMake`, `IMake`, `ComplexMake`,
`ArrayMake1` (`Comp.make`: the aggregate of the arguments). -/
def ssMakeOp : Op → Bool
  | .StructMake | .StringMake | .SliceMake | .IMake | .ComplexMake | .ArrayMake1 => true
  | _ => false

/-- The stores `sts` of a split's logged chain in chain order from the store `s`: each next one
the store on the previous one (at most `n`). -/
def ssOrder (sts : List Value) : Nat → ID → List Value
  | 0, _ => []
  | n + 1, s =>
    match sts.find? (·.id == s) with
    | some u =>
      u :: match sts.find? (fun x => x.args[2]? == some s) with
        | some nx => ssOrder sts n nx.id
        | none => []
    | none => []

/-- The fields whose logged store does not store the `Make`'s argument `as[k]` of `f` up to copies
(a value rule rewrote the argument, and copy elimination replaced it, before the split, but the
layers apply the rule later; or a layer applied a later replacement of the argument): per such
field its store, the argument and the logged stored value. The chain's stores of the split of
`v` with its logged definition `w` and fresh values `ds`. -/
def ssStoredFixes (tabs : Tables) (f : Func) (v : ID) (w : Value) (ds : List Value)
    (as : Array ID) : List (ID × ID × ID) :=
  let sts := (if w.op == .Store then w :: ds else ds).filter (·.op == .Store)
  match ssFirst v w ds with
  | some s0 =>
    (ssOrder sts sts.length s0).zipIdx.filterMap fun (u, k) =>
      match as[k]?, u.args[1]? with
      | some a, some b =>
        if a != b && !copyReach tabs f.valueTab f.valueTab.size a b then some (u.id, a, b)
        else none
      | _, _ => none
  | none => []

/-- One event of `ssPre`: a split of a `Store` of `f` whose stored value is, up to copies in `f`, a
`Make` (`ssMakeOp`) is applied, any other event kept (a split of
a fresh field store of an earlier split, a nested struct, or a second split of a `Store` this
layer split in place, `(Store dst (ArrayMake1 (StructMake …)) mem)`, is left to a later layer),
but for the copy-argument replacements of the split `Store` logged before it (copy elimination on
its arguments, which the split validated in `f` through copies replaces). A replacement of its
memory gave the chain's first store the copy's source (another split `Store`'s last store, in any
block, or the memory a split without fields stands for): that store starts from the `Store`'s
memory in `f` instead, and the replacements move to it, for `validate` to replay. A split of a
`Store` of a `Load` (the struct-load layer has not expanded it yet) is left to a later layer as
well. A field store whose stored value is not the `Make`'s argument up to copies
(`ssStoredFixes`) stores the argument, and a replacement of it by the logged value follows, for
`validate` to replay (none if the logged value is a copy of the argument). -/
def ssStep (t : Interp.Table) (tabs : Tables) (f : Func) (p : Func × Array RwEvent)
    (ev : RwEvent) : Func × Array RwEvent :=
  match ssEvent? t f ev with
  | some (v, w, ds) =>
    match f.value? v,
        ((f.value? v).bind (·.args[1]?)).bind fun a => f.value? (copyEnd tabs f.valueTab f.valueTab.size a) with
    | some fv, some smv =>
      if !(ssMakeOp smv.op && (p.1.value? v).any fun u => u.op == fv.op && u.args == fv.args)
      then (p.1, p.2.push ev)
      else
      let s0m : Option (ID × ID) :=
        if copyArgOf p.2 v 2 then (ssFirst v w ds).bind fun s0 => fv.args[2]?.map (s0, ·) else none
      let fixM := fun (u : Value) => match s0m with
        | some (s0, m) => if u.id == s0 then { u with args := u.args.set! 2 m } else u
        | none => u
      let w := fixM w
      let ds := ds.map fixM
      let fixes := ssStoredFixes tabs f v w ds smv.args
      let fixS := fun (u : Value) => match fixes.find? (·.1 == u.id) with
        | some (_, a, _) => { u with args := u.args.set! 1 a }
        | none => u
      let rest := p.2.filterMap fun
        | .copyArg y i src =>
          if y != v then some (.copyArg y i src)
          else match s0m with
            | some (s0, _) => if i == 2 then some (.copyArg s0 2 src) else none
            | none => none
        | e => some e
      (ssApply p.1 v (fixS w) (ds.map fixS),
        rest ++ (fixes.filterMap fun (s, a, b) =>
          if copyReach tabs f.valueTab f.valueTab.size b a then none else some (.copyArg s 1 b)).toArray)
    | _, _ => (p.1, p.2.push ev)
  | none => (p.1, p.2.push ev)

/-- The input with the log's struct-store splits of its `Store`s applied, and the remaining
events. -/
def ssPre (t : Interp.Table) (tabs : Tables) (f : Func) (log : Array RwEvent) :
    Func × Array RwEvent :=
  log.foldl (ssStep t tabs f) (f, #[])

/-- `gv` is `fv` but for its use count. -/
def ssSame (fv gv : Value) : Bool :=
  gv.id == fv.id && gv.op == fv.op && gv.aux == fv.aux && gv.auxInt == fv.auxInt &&
    gv.type == fv.type && gv.block == fv.block && gv.args == fv.args

/-- The last `n` memory roots of `g` ending in `m`, walked back through their memory argument:
the pairs `(pointer argument, store)`, first first, and the memory before them. -/
def ssWalk (g : Func) : Nat → ID → List (ID × ID) × ID
  | 0, m => ([], m)
  | k + 1, m =>
    match g.value? m with
    | some s =>
      let r := ssWalk g k (s.args[2]?.getD 0)
      (r.1 ++ [(s.args[0]?.getD 0, m)], r.2)
    | none => ([], m)

/-- The pointer `p` of a split's field at offset `o` of `dst` (in block `b`): a fresh `OffPtr`
(pointer shape) of `dst` (up to copies) by `o`, or, at offset `0`, a value of `f` that `dst`
reaches through copies. -/
def ssPtrOK (tabs : Tables) (f g : Func) (b dst p : ID) (o : Nat) : Bool :=
  match f.value? p, g.value? p with
  | none, some ov =>
    ov.id == p && ov.op == .OffPtr && ov.block == b &&
      ov.args.size == 1 && copyReach tabs f.valueTab f.valueTab.size dst ov.args[0]! &&
      ov.auxInt == Int64.ofNat o && isPtrTy (tabs.ty ov.type)
  | some _, _ => o == 0 && copyReach tabs f.valueTab f.valueTab.size dst p
  | none, none => false

/-- A `Make` argument of shape `s` fits its field's shape `t`: the same shape, or two word shapes
(`wordTy`: a 64-bit integer or a pointer). The two word shapes have the same values
(`Val.hasTy_ptr_eq_i64`, #290), so a register of one keeps its value at the other: a pointer in
a pointer field of another element type, or in a `uintptr` field (an interface's itab word of a
pointer type: a `*uint8` itab, a `Phi` of them), a `uintptr` in a pointer field. -/
def ssFieldOK (s t : Sem.Ty) : Bool :=
  Sem.Ty.beq s t || (wordTy s && wordTy t)

/-- Field `k` of the split of `x` (block `b`, pointer `dst`, fields `fs`, `Make` arguments `as`,
chain `ps` from memory `m0`): the `Make` argument has the field's shape; the pair `(p, s)` is a
fresh (not in `f`; or `x` itself, last) memory-typed `Store` of that argument (up to copies in
`f`) at the field's shape on the previous store of the chain (`m0` for the first), at the field's
pointer (`ssPtrOK`), in `b`. -/
def ssLink (tabs : Tables) (f g : Func) (b dst x : ID) (fs : List (Nat × Sem.Ty)) (as : Array ID)
    (ps : List (ID × ID)) (m0 : ID) (k : Nat) : Bool :=
  match fs[k]?, as[k]?, ps[k]? with
  | some (o, t), some a, some (p, s) =>
    let prev := if k = 0 then m0 else (ps[k - 1]?.map (·.2)).getD 0
    match f.value? a, g.value? s with
    | some av, some sv =>
      ssFieldOK (tabs.ty av.type) t &&
      ((f.value? s).isNone || (s == x && k + 1 == ps.length)) && sv.id == s && sv.op == .Store &&
      sv.block == b && Sem.Ty.beq (tabs.ty sv.type) .mem &&
      sv.args.size == 3 && sv.args[0]! == p && sv.args[2]! == prev &&
      copyReach tabs f.valueTab f.valueTab.size a sv.args[1]! &&
      Sem.Ty.beq (Sem.auxTy tabs sv.aux) t &&
      ssPtrOK tabs f g b dst p o
    | _, _ => false
  | _, _, _ => false

/-- Value `x` of `f` is a split `Store` in `g`: in `f` a `Store` listed in its block at an
aggregate shape `agg fs n` (a string or slice by its layout `Ty.asAgg`; every field inside it,
`layoutsOK`, at an offset below `n`) of a
`Make` (`ssMakeOp`, up to copies, `copyEnd`) of that shape; in `g` `Copy` of the last store of
the chain (`ssWalk`), or (in place) that last store itself, each field linked (`ssLink`), from a
memory the `Store`'s memory reaches through copies (`ssStep` rebases the chain there). The
chain's pairs. -/
def ssSplit? (tabs : Tables) (f g : Func) (x : ID) : Option (List (ID × ID)) :=
  match f.value? x, g.value? x with
  | some fv, some gv =>
    match fv.args.toList, (Sem.auxTy tabs fv.aux).asAgg with
    | [dst, sm, mem], .agg fs n =>
      match f.value? (copyEnd tabs f.valueTab f.valueTab.size sm) with
      | some smv =>
        let copy := gv.op == .Copy
        let last := if copy then gv.args[0]?.getD 0 else x
        let r := ssWalk g fs.length last
        if fv.op == .Store && ((f.block? fv.block).any fun b => b.values.contains x) &&
            ssMakeOp smv.op && Sem.Ty.beq (tabs.ty smv.type).asAgg (.agg fs n) &&
            layoutsOK n fs && fs.all (·.1 < n) && smv.args.size == fs.length &&
            gv.id == x && gv.type == fv.type && gv.block == fv.block &&
            (if copy then gv.args.size == 1 && gv.aux == none && gv.auxInt == 0
             else gv.op == .Store && 0 < fs.length) &&
            r.1.length == fs.length && last == (r.1.getLast?.map (·.2)).getD r.2 &&
            copyReach tabs f.valueTab f.valueTab.size mem r.2 &&
            (List.range fs.length).all (ssLink tabs f g fv.block dst x fs smv.args r.1 r.2) then
          some r.1
        else none
      | none => none
    | _, _ => none
  | _, _ => none

/-- The roots `l` of `f` with each split `Store` (`S`) replaced by its chain's stores. -/
def ssRoots (S : Array (Option (List (ID × ID)))) (l : List ID) : List ID :=
  l.flatMap fun x => match S[x]?.join with
    | some ps => ps.map (·.2)
    | none => [x]

/-- Block `bid` of `g` has `f`'s kind and controls, `f`'s values then fresh values (not in `f`,
in `news`) of `bid`, and its schedule runs `f`'s roots with the splits' chains in their place
(`ssRoots`). -/
def ssBlockOK (f g : Func) (news : List ID) (S : Array (Option (List (ID × ID)))) (bid : ID) :
    Bool :=
  match f.block? bid, g.block? bid with
  | some fb, some gb =>
    gb.kind == fb.kind && gb.controls == fb.controls && fb.values.size ≤ gb.values.size &&
    gb.values.extract 0 fb.values.size == fb.values &&
    (gb.values.extract fb.values.size gb.values.size).all
      (fun x => (f.value? x).isNone && news.contains x && (g.value? x).any (·.block == bid)) &&
    match Sem.schedule f fb with
    | none => true
    | some oS =>
      match Sem.schedule g gb with
      | some oT => oT.toList.filter (CSE.rootNode g) == ssRoots S (oS.toList.filter (CSE.rootNode f))
      | none => false
  | _, _ => false

/-- **The split relation**: `g` is `f` with `Store`s split (`ssSplit?`): the same control-flow
graph, own aux and blocks (`ssBlockOK`); every value of `f` kept but for its use count, or split;
the chains' fresh values listed in their split's block, and the only values `f` lacks. -/
def ssRel (tabs : Tables) (f g : Func) : Bool :=
  let S : Array (Option (List (ID × ID))) := (Array.range f.valueTab.size).map (ssSplit? tabs f g)
  let news := S.toList.flatMap fun s => (s.getD []).flatMap fun (p, m) => [p, m]
  DomCert.cfgView g == DomCert.cfgView f && g.ownAux == f.ownAux &&
    f.valueTab.size ≤ g.valueTab.size &&
    (List.range f.valueTab.size).all (fun x => match f.value? x, g.value? x with
      | none, _ => true
      | some fv, some gv => ssSame fv gv || (S[x]?.join).isSome
      | some _, none => false) &&
    (List.range g.valueTab.size).all (fun x =>
      (f.value? x).isSome || (g.value? x).isNone || news.contains x) &&
    (List.range f.valueTab.size).all (fun x => match S[x]?.join, f.value? x with
      | some ps, some fv => (g.block? fv.block).any fun gb =>
          ps.all fun (p, m) => ((f.value? p).isSome || gb.values.contains p) &&
            ((f.value? m).isSome || gb.values.contains m)
      | _, _ => true) &&
    f.blocks.all (ssBlockOK f g news S)

/-! ## Segments (issue #151)

`generic.rules:1833`/`:1844`/`:1857` replace `Store`s over a `Zero` that they tile by the same
`Store`s over the `Zero`'s memory (`(Store op1 d1 (Store op2 d2 (Zero [n] p mem)))` becomes
`(Store op1 d1 (Store op2 d2 mem))`), `:1638`/`:1730` replace `SelectN [0]` of a call to
`runtime.memclrNoHeapPointers`/`runtime.memmove` (its only use) by `Zero`/`Move`, and `:1743`
replaces a `Move` from a read-only symbol whose bytes are zero by a `Zero`. Each rewrites
a *segment* of a block: the rule's value `x` (the anchor) is redefined in place, the values it
clobbers (`D`: the inner `Store`s and the `Zero`, or the call) are gone, and fresh values (`N`:
the new inner `Store`s) are put in. Only the anchor's memory agrees with the source's, so the
validator takes these events out of the log as the struct-store splits: `segPre` applies them,
`segRel` relates the input to that function, and `validate` the output to it with the other
events. -/

/-- A segment rule: a `Store`, `SelectN` or `Move` rule with a built result in `v`'s block; each
instance is validated by `segRel`. -/
def segShapeOK (r : Rule) : Bool :=
  match r.pat, r.result, r.block with
  | .op .Store .., .build _, none => true
  | .op .SelectN .., .build _, none => true
  | .op .Move .., .build _, none => true
  | _, _, _ => false

/-- The value `v` of `f` that event `ev` rewrites as a segment, its logged definition and the
fresh values (logged parents first), if it is a `segs` rule event (`segShapeOK`) of a rule on
`v`'s op in `f` (an event of a value the pass redefined earlier indexes another op's row). -/
def segEvent? (t : Interp.Table) (f : Func) : RwEvent → Option (ID × Value × List Value)
  | .rule v i _ defs =>
    match f.value? v with
    | some u =>
      let n := t.segBase u.op
      if n ≤ i then
        match t.segs[i - n]?, defs.toList with
        | some cr, w :: ds =>
          if segShapeOK cr.rule && w.id == v &&
              (match cr.rule.pat with | .op o .. => o == u.op | _ => false) then
            some (v, w, ds.filter (·.id != v))
          else none
        | _, _ => none
      else none
    | none => none
  | _ => none

/-- The last argument of `w` (the memory of a memory op or call). -/
def lastArg (w : Value) : ID := w.args.back?.getD 0

/-- The memory a segment's new chain starts from: from `m` down the last arguments of the fresh
values `ds`, the first value that is not one of them. -/
def segBottom (ds : List Value) : Nat → ID → ID
  | 0, m => m
  | k + 1, m =>
    match ds.find? (·.id == m) with
    | some d => segBottom ds k (lastArg d)
    | none => m

/-- The values of `f` from `m` down the last arguments, up to the memory `m0` (excluded; at most
`k`). -/
def segChainF (f : Func) (m0 : ID) : Nat → ID → List ID
  | 0, _ => []
  | k + 1, m =>
    if m == m0 then []
    else match f.value? m with
      | some s => m :: segChainF f m0 k (lastArg s)
      | none => []

/-- The values the segment rewrite of `u` into `w` with the fresh values `ds` drops: the call of
a `SelectN`, else the chain below the anchor's memory, down to the new chain's start. -/
def segDrops (f : Func) (u w : Value) (ds : List Value) : List ID :=
  segChainF f (segBottom ds 8 (lastArg w)) 8
    (if u.op == .SelectN then u.args[0]?.getD 0 else lastArg u)

/-- Drop the value `d` of `f`: its arguments lose a use, it leaves its block's list and is freed. -/
def segFree (f : Func) (d : ID) : Func :=
  match f.value? d with
  | some dv =>
    let f := dv.args.foldl (fun f a => f.modV a fun z => { z with uses := z.uses - 1 }) f
    (f.modB dv.block fun b => { b with values := b.values.filter (· != d) }).freeValue d
  | none => f

/-- The segment rewrite of `v` into `w` with the fresh values `ds`: `v`'s arguments lose a use,
the fresh values are put in (children first), `w`'s arguments gain a use, `v` is redefined and
the dropped values `D` are freed. -/
def segApply (f : Func) (v : ID) (w : Value) (ds : List Value) (D : List ID) : Func :=
  match f.value? v with
  | some u =>
    let f := u.args.foldl (fun f a => f.modV a fun z => { z with uses := z.uses - 1 }) f
    let f := w.args.foldl Func.incUses (ds.reverse.foldl ssPut f)
    let f := f.modV v fun z => { z with op := w.op, auxInt := w.auxInt, aux := w.aux, args := w.args }
    D.foldl segFree f
  | none => f

/-- One event of `segPre`: a segment rewrite of a value of `f` (not of `late`) is applied, any other
event kept, but for the copy-argument replacements of its anchor and dropped values logged before
it. -/
def segStep (t : Interp.Table) (f : Func) (late : List ID) (p : Func × Array RwEvent)
    (ev : RwEvent) : Func × Array RwEvent :=
  match segEvent? t f ev with
  | some (v, w, ds) =>
    match f.value? v with
    | some u =>
      if late.contains v then (p.1, p.2.push ev) else
      let D := segDrops f u w ds
      (segApply p.1 v w ds D,
        p.2.filter fun | .copyArg y _ _ => y != v && !D.contains y | _ => true)
    | none => (p.1, p.2.push ev)
  | none => (p.1, p.2.push ev)

/-- The values of `f` from `m` down the last arguments (at most `k`). -/
def segMemChain (f : Func) : Nat → ID → List ID
  | 0, _ => []
  | k + 1, m =>
    match f.value? m with
    | some s => m :: segMemChain f k (lastArg s)
    | none => []

/-- The values of `f` on the memory chain (`segMemChain`, 8 deep) below the anchor of the
segment event `ev`. -/
def segEvChain (t : Interp.Table) (f : Func) (ev : RwEvent) : Option (ID × List ID) :=
  (segEvent? t f ev).bind fun (x, _, _) =>
    (f.value? x).map fun u => (x, segMemChain f 8 (lastArg u))

/-- The anchors of the log's segment events whose memory chain in `f` has the anchor of an
earlier one: the pass matched the later rule on the earlier one's result (a `Move` of stores over
a `Move` it had turned into stores), which the first segment layer (`.seg true`) leaves to the
second. -/
def segLate (t : Interp.Table) (f : Func) (log : Array RwEvent) : List ID :=
  (log.foldl (init := (([] : List ID), ([] : List ID))) fun acc ev =>
    match segEvChain t f ev with
    | some (x, ch) => (x :: acc.1, if ch.any acc.1.contains then x :: acc.2 else acc.2)
    | none => acc).2

/-- The values of `f` that a rule event rewrites after a segment event whose memory chain in `f`
has them, or after another rule event (no forwarding) at them: the pass matched the segment's rule
with those values as they were (a dead zero `Store` the pass dropped only after it matched a `Move`
of the stores), or the later rule on the value the earlier one redefined (a zero `Store` dropped
after its split in place, `generic.rules:997`), so the selective forwarding layers leave their
forwardings to the later ones. -/
def fwdLate (t : Interp.Table) (f : Func) (log : Array RwEvent) : List ID :=
  (log.foldl (init := (([] : List ID), ([] : List ID), ([] : List ID))) fun acc ev =>
    match segEvChain t f ev with
    | some (x, ch) => (ch ++ acc.1, x :: acc.2.1, acc.2.2)
    | none =>
      match ev with
      | .rule v _ _ _ =>
        if acc.1.contains v || acc.2.1.contains v then (acc.1, acc.2.1, v :: acc.2.2)
        else if (fwdEvent? t f ev).isSome then acc
        else (acc.1, v :: acc.2.1, acc.2.2)
      | _ => acc).2.2

/-- The input with the log's segment rewrites applied (with `sel` none of `segLate`), and the
remaining events. -/
def segPre (t : Interp.Table) (sel : Bool) (f : Func) (log : Array RwEvent) :
    Func × Array RwEvent :=
  log.foldl (segStep t f (if sel then segLate t f log else [])) (f, #[])

/-- The values of `g` from `m` down the last arguments while they are no values of `f` (a
segment's fresh values), first first, and the value below them (at most `k`). -/
def freshChain (f g : Func) : Nat → ID → List ID × ID
  | 0, m => ([], m)
  | k + 1, m =>
    match f.value? m, g.value? m with
    | none, some s => let r := freshChain f g k (lastArg s); (m :: r.1, r.2)
    | _, _ => ([], m)

/-- `k` `Store`s of `f` from `m` down their memory arguments, first first, and the memory below
them. -/
def storesF (f : Func) : Nat → ID → Option (List ID × ID)
  | 0, m => some ([], m)
  | k + 1, m =>
    match f.value? m with
    | some s =>
      if s.op == .Store && s.args.size == 3 then
        (storesF f k s.args[2]!).map fun r => (m :: r.1, r.2)
      else none
    | none => none

/-- `k` `Store`s of `f` from `m` down their memory arguments through copies (`copyEnd`: a struct-
store split leaves a `Copy` of its chain's last store between two stores), first first, and the
memory below them. -/
def storesC (tabs : Tables) (f : Func) : Nat → ID → Option (List ID × ID)
  | 0, m => some ([], m)
  | k + 1, m =>
    match f.value? m with
    | some s =>
      if s.op == .Store && s.args.size == 3 then
        (storesC tabs f k (copyEnd tabs f.valueTab f.valueTab.size s.args[2]!)).map
          fun r => (m :: r.1, r.2)
      else none
    | none => none

/-- The `Store`s `ss` of `f` (last first) tile `[o, n)` of the pointer `p`: each at an `OffPtr` of
`p` (up to copies) by the offset where the previous one ends (`o` for the first), of pointer
shape (an integer-typed `OffPtr` would hold the address word, which need not read back as the
pointer, `Ptr.convertible`), of positive size, the last ending at `n`. -/
def segTiles (tabs : Tables) (f : Func) (p : ID) : Nat → List Value → Nat → Bool
  | o, [], n => o == n
  | o, s :: ss, n =>
    let sz := (Sem.auxTy tabs s.aux).size
    decide (0 < sz) && s.args.size == 3 &&
    (match f.value? s.args[0]! with
     | some op =>
       op.op == .OffPtr && op.args.size == 1 && op.auxInt.toInt == (o : Int) &&
         isPtrTy (tabs.ty op.type) &&
         copyEnd tabs f.valueTab f.valueTab.size op.args[0]! ==
           copyEnd tabs f.valueTab f.valueTab.size p
     | none => false) &&
    segTiles tabs f p (o + sz) ss n

/-- The `Store` `s` of `f` became the `Store` `s'` of `g` with the same type, aux, pointer and value
(its memory aside), both in block `b`. -/
def segStoreSame (b : ID) (s s' : Value) : Bool :=
  s.op == .Store && s'.op == .Store && s.args.size == 3 && s'.args.size == 3 &&
    s'.aux == s.aux && s'.type == s.type && s'.args[0]! == s.args[0]! &&
    s'.args[1]! == s.args[1]! && s.block == b && s'.block == b

/-- A chain segment at the `Store` `x` (`f`'s `fv`, `g`'s `gv`; `generic.rules:1833` family): in `f`
`k ≥ 2` `Store`s from `x` over a `Zero [n] p mem` of `x`'s block, in `g` the same `Store`s (fresh
but `x`) over `mem`, at `OffPtr`s of `p` tiling `[0, n)`. The dropped values (the inner `Store`s
of `f` and the `Zero`) and the fresh ones (dependency order). -/
def chainSeg? (tabs : Tables) (f g : Func) (x : ID) (fv gv : Value) : Option (List ID × List ID) :=
  let (ns, m0) := freshChain f g 4 (lastArg gv)
  match storesF f (ns.length + 1) x with
  | some (fs, z) =>
    match f.value? z with
    | some zv =>
      if fv.op == .Store && gv.op == .Store && zv.op == .Zero && zv.args.size == 2 &&
          zv.args[1]! == m0 && zv.block == fv.block && decide (0 ≤ zv.auxInt.toInt) &&
          1 ≤ ns.length &&
          (fs.zip (x :: ns)).all (fun (a, b) => match f.value? a, g.value? b with
            | some sa, some sb => segStoreSame fv.block sa sb
            | _, _ => false) &&
          segTiles tabs f zv.args[0]! 0 (fs.filterMap f.value?).reverse zv.auxInt.toInt.toNat then
        some (fs.tail ++ [z], ns.reverse)
      else none
    | none => none
  | none => none

/-- `a` is a constant term of `f` (`termConst`, at most 6 deep: `Mul64 (SliceLen (SliceMake _
(Sub64 (Const64 _) _) _)) _`) whose value is the 64-bit integer `n ≥ 0`. -/
def constSize (tabs : Tables) (f : Func) (a : ID) (n : Int64) : Bool :=
  decide (0 ≤ n.toInt) &&
    match termConst tabs f 6 a with
    | some (.int .w64 x) => x == BitVec.ofInt 64 n.toInt
    | _ => false

/-- `a` is a value of `f` of pointer shape. -/
def ptrArgB (tabs : Tables) (f : Func) (a : ID) : Bool :=
  (f.value? a).any fun av => isPtrTy (tabs.ty av.type)

/-- A call segment at `x` (`generic.rules:1638`, `:1730`): in `f` `SelectN [0]` of a call `c` of
its block to `runtime.memclrNoHeapPointers` (pointer `p`, a size `n` that is a constant term,
`constSize`) or `runtime.memmove`
(`dst`, `src`, size) whose arguments reach the callee as they are (`MemCall.simpleCall`), in `g`
`Zero [n] p mem` or `Move [n] dst src mem`. The call is dropped, no value is fresh. -/
def callSeg? (tabs : Tables) (f g : Func) (fv gv : Value) : Option (List ID × List ID) :=
  match fv.op, fv.args.toList with
  | .SelectN, [c] =>
    match f.value? c with
    | some cv =>
      if fv.auxInt == 0 && cv.block == fv.block then
        match cv.args.toList with
        | [p, n, m] =>
          if MemCall.simpleCall tabs cv 2 &&
              MemCall.calleeIs tabs cv "runtime.memclrNoHeapPointers" &&
              gv.op == .Zero && gv.args == #[p, m] && constSize tabs f n gv.auxInt &&
              ptrArgB tabs f p then some ([c], [])
          else none
        | [d, s, n, m] =>
          if MemCall.simpleCall tabs cv 3 && MemCall.calleeIs tabs cv "runtime.memmove" &&
              gv.op == .Move && gv.args == #[d, s, m] && constSize tabs f n gv.auxInt &&
              ptrArgB tabs f d && ptrArgB tabs f s then some ([c], [])
          else none
        | _ => none
      else none
    | none => none
  | _, _ => none

/-- A read-only segment at `x` (`generic.rules:1743`): in `f` `Move [n] dst src mem` from an
`Addr` of a symbol (`src`), in `g` `Zero [n] dst mem`. Nothing is dropped or fresh; that the
symbol is a read-only one of the precondition with zero bytes is `roSegsOK`'s. -/
def roSeg? (tabs : Tables) (f : Func) (fv gv : Value) : Option (List ID × List ID) :=
  match fv.op, fv.args.toList with
  | .Move, [d, s, m] =>
    if gv.op == .Zero && gv.args == #[d, m] && gv.auxInt == fv.auxInt &&
        (f.value? s).any (fun sv => sv.op == .Addr && (WBCheck.symName? tabs sv.aux).isSome) then
      some ([], [])
    else none
  | _, _ => none

/-- Values `a` and `b` of `f` hold the same pointer: they reach the same value through copies, or
`LocalAddr`s of the same variable at the same type (`isSamePtr`; their memory arguments differ). -/
def samePtr (tabs : Tables) (f : Func) (a b : ID) : Bool :=
  let ca := copyEnd tabs f.valueTab f.valueTab.size a
  let cb := copyEnd tabs f.valueTab f.valueTab.size b
  ca == cb ||
    match f.value? ca, f.value? cb with
    | some va, some vb => va.op == .LocalAddr && vb.op == .LocalAddr && va.aux.isSome &&
        va.aux == vb.aux && va.type == vb.type
    | _, _ => false

/-- The element size of a constant-index pointer step: `1` for an `AddPtr`, the element size of
a `PtrIndex`'s pointer shape. -/
def idxScale (tabs : Tables) (v : Value) : Option Nat :=
  if v.op == .AddPtr then some 1
  else match tabs.ty v.type with
    | .ptr (some e) => some e
    | _ => none

/-- The offset of the pointer `a` of `f` from `p`: `0` if `a` equals `p` (`samePtr`), else
through at most `k` `OffPtr`s, and `AddPtr`s and `PtrIndex`es by a constant index (`constIdx?`,
times `idxScale`), of pointer shape the sum of their offsets down to a value equal to `p` (the
segment layer's input may still hold the `PtrIndex`/`AddPtr` that value rules fold to `OffPtr`s
before the `Move` rule matches). -/
def offFrom (tabs : Tables) (f : Func) (p : ID) : Nat → ID → Option Int
  | 0, a => if samePtr tabs f a p then some 0 else none
  | k + 1, a =>
    if samePtr tabs f a p then some 0 else
    match f.value? a with
    | some v =>
      if v.op == .OffPtr && v.args.size == 1 && isPtrTy (tabs.ty v.type) then
        (offFrom tabs f p k v.args[0]!).map (v.auxInt.toInt + ·)
      else if (v.op == .AddPtr || v.op == .PtrIndex) && v.args.size == 2 &&
          isPtrTy (tabs.ty v.type) then
        match constIdx? tabs f v.args[1]!, idxScale tabs v with
        | some kk, some e => (offFrom tabs f p k v.args[0]!).map ((kk * BitVec.ofNat 64 e).toInt + ·)
        | _, _ => none
      else none
    | none => none

/-- One store of a move segment: the `Store` `sa` of `f` at a pointer `o` bytes past `p`
(`offFrom`: through `OffPtr`s to a value equal to `p` up to copies or the same variable) with
`0 ≤ o` and `o + size ≤ n` (positive size) became the `Store` `sb` of `g` (block `b`) with the
same aux, type and value, at a fresh `OffPtr [o]` of `dst` (pointer shape). The pass folds nested
`OffPtr`s (`generic.rules:964`) before it matches the `Move`; `sa` may be in another block (the
`Move` reads its memory through its register). -/
def moveStoreOK (tabs : Tables) (f g : Func) (p dst : ID) (n : Int64) (b : ID) (sa sb : Value) :
    Bool :=
  let sz := (Sem.auxTy tabs sa.aux).size
  sa.op == .Store && sb.op == .Store && sa.args.size == 3 && sb.args.size == 3 &&
    sb.aux == sa.aux && sb.type == sa.type && sb.args[1]! == sa.args[1]! &&
    sb.block == b && decide (0 < sz) && (f.value? sb.args[0]!).isNone &&
    match g.value? sb.args[0]!, offFrom tabs f p 4 sa.args[0]! with
    | some q', some o =>
      q'.op == .OffPtr && q'.args == #[dst] && q'.auxInt.toInt == o &&
        isPtrTy (tabs.ty q'.type) && decide (0 ≤ o) && decide (o + sz ≤ n.toInt)
    | _, _ => false

/-- The memory `m` of `f`, or the memory under it if it is a `VarDef`. -/
def underVarDef (f : Func) (m : ID) : ID :=
  match f.value? m with
  | some mv => if mv.op == .VarDef && mv.args.size == 1 then mv.args[0]! else m
  | none => m

/-- A move segment at the `Move` `x` (`generic.rules:1978` family; `f`'s `fv`, `g`'s `gv`): in `f`
`Move [n] dst p mem` whose memory is, up to copies (`mc`), (a `VarDef` of) `k ≥ 1` `Store`s
(`storesC`: through copies) over, up to copies, a `Zero [n] p' _` (`p'` equal to `p`, the
stores' pointers offsets of `p`), in `g` the same `Store`s (`moveStoreOK`) at fresh `OffPtr`s of
`dst`, the anchor
the first, over a fresh `Zero [n] dst mc` (of the `Zero`'s type).
Nothing is dropped; the fresh values in dependency order: the `OffPtr`s, the `Zero`, the stores
below the anchor bottom first. -/
def moveSeg? (tabs : Tables) (f g : Func) (x : ID) (fv gv : Value) : Option (List ID × List ID) :=
  match fv.op, fv.args.toList with
  | .Move, [d, p, m] =>
    let mc := copyEnd tabs f.valueTab f.valueTab.size m
    let (ns, m0) := freshChain f g 5 (lastArg gv)
    match ns.getLast?, storesC tabs f ns.length (underVarDef f mc) with
    | some z', some (fs, z1) =>
      let z := copyEnd tabs f.valueTab f.valueTab.size z1
      match f.value? z, g.value? z' with
      | some zv, some zv' =>
        let n := fv.auxInt
        let gs := x :: ns.dropLast
        if gv.op == .Store && m0 == mc && decide (0 ≤ n.toInt) && zv.op == .Zero &&
            zv.args.size == 2 && zv.auxInt == n && samePtr tabs f zv.args[0]! p &&
            zv'.op == .Zero && zv'.args == #[d, mc] && zv'.auxInt == n && zv'.type == zv.type &&
            (fs.zip gs).all (fun (a, b) => match f.value? a, g.value? b with
              | some sa, some sb => moveStoreOK tabs f g p d n fv.block sa sb
              | _, _ => false) then
          some ([], (gs.filterMap fun b => (g.value? b).map (·.args[0]!)) ++ ns.reverse)
        else none
      | _, _ => none
    | _, _ => none
  | _, _ => none

/-- A zero segment at the `Move` `x` (`generic.rules:1740`, `:1742`; `f`'s `fv`, `g`'s `gv`): in
`f` `Move [n] dst p mem` whose memory is, up to copies (`mc`), (a `VarDef` of) a `Zero [n] p' _`
(up to copies; `p'` equal to `p`, `samePtr`), in `g` `Zero [n] dst mc`: the `Move` copies the
zeros (or the bytes of the `VarDef`'s poisoned block, which zeros refine). Nothing is dropped or
fresh. -/
def zeroSeg? (tabs : Tables) (f : Func) (fv gv : Value) : Option (List ID × List ID) :=
  match fv.op, fv.args.toList with
  | .Move, [d, p, m] =>
    let mc := copyEnd tabs f.valueTab f.valueTab.size m
    match f.value? (copyEnd tabs f.valueTab f.valueTab.size (underVarDef f mc)) with
    | some zv =>
      if gv.op == .Zero && gv.args == #[d, mc] && gv.auxInt == fv.auxInt &&
          decide (0 ≤ fv.auxInt.toInt) && zv.op == .Zero && zv.args.size == 2 &&
          zv.auxInt == fv.auxInt && samePtr tabs f zv.args[0]! p then some ([], [])
      else none
    | none => none
  | _, _ => none

/-- `(offset, size)` pieces tile `[lo, n)`: consecutive, non-empty, in increasing order. -/
def tilesB : Nat → Nat → List (Nat × Nat) → Bool
  | lo, n, [] => lo == n
  | lo, n, (o, s) :: ws => o == lo && decide (0 < s) && tilesB (lo + s) n ws

/-- The `(offset, size)` of the `Store`s `gs` of `g`: their `OffPtr`'s auxint, their type's
size. -/
def storeShapes (tabs : Tables) (g : Func) (gs : List ID) : List (Nat × Nat) :=
  gs.filterMap fun b => (g.value? b).bind fun sb =>
    (g.value? sb.args[0]!).map fun q => (q.auxInt.toInt.toNat, (Sem.auxTy tabs sb.aux).size)

/-- A tile segment at the `Move` `x` (`generic.rules:1871`, `:1887`, `:1908`, `:1925`; `f`'s
`fv`, `g`'s `gv`): in `f` `Move [n] dst p mem` whose memory is, up to copies (`mc`), (a `VarDef`
of) `k ≥ 1` `Store`s (`storesC`: through copies) at pointers `o` bytes past `p` that tile `[0, n)`
bottom first (`tilesB` of the target's stores), in `g` the same `Store`s (`moveStoreOK`) at fresh
`OffPtr`s of `dst`, the anchor the first, the last over `mc`: the `Move` copies exactly the
stores' bytes. Nothing is dropped; the fresh values in dependency order: the `OffPtr`s, the
stores below the anchor bottom first. -/
def tileSeg? (tabs : Tables) (f g : Func) (x : ID) (fv gv : Value) : Option (List ID × List ID) :=
  match fv.op, fv.args.toList with
  | .Move, [d, p, m] =>
    let mc := copyEnd tabs f.valueTab f.valueTab.size m
    let (ns, m0) := freshChain f g 5 (lastArg gv)
    match storesC tabs f (ns.length + 1) (underVarDef f mc) with
    | some (fs, _) =>
      let n := fv.auxInt
      let gs := x :: ns
      if gv.op == .Store && m0 == mc && decide (0 ≤ n.toInt) &&
          (fs.zip gs).all (fun (a, b) => match f.value? a, g.value? b with
            | some sa, some sb => moveStoreOK tabs f g p d n fv.block sa sb
            | _, _ => false) &&
          tilesB 0 n.toInt.toNat (storeShapes tabs g gs.reverse) then
        some ([], (gs.filterMap fun b => (g.value? b).map (·.args[0]!)) ++ ns.reverse)
      else none
    | none => none
  | _, _ => none

/-- `a` is an argument of `s` in `f`, or an argument of one of its arguments, … (`k` levels),
through values that are no `Phi`s. -/
def argReach (f : Func) : Nat → ID → ID → Bool
  | 0, _, _ => false
  | k + 1, s, a => (f.value? s).any fun sv => sv.op != .Phi &&
      (sv.args.contains a || sv.args.any fun b => argReach f k b a)

/-- Value `x` of `f` is a segment's anchor in `g` (`chainSeg?`, `callSeg?`, `zeroSeg?`, `roSeg?`,
`moveSeg?` or `tileSeg?`): listed in its block, a `Store`, `SelectN` or `Move` redefined in place (its ID, block
and type kept); its dropped values are listed in that block, its fresh values in that block of
`g`; the anchor is a root of `g`, and so is each fresh value but `OffPtr`s of arguments of roots
of `f` of the segment (a dropped root, or the anchor); each argument of the fresh values and of
the anchor is an earlier one of them, or reached from a root of `f` of the segment through the
arguments (`argReach`) and not dropped. The dropped and fresh values. -/
def segOK (tabs : Tables) (f g : Func) (x : ID) : Option (List ID × List ID) :=
  match f.value? x, g.value? x with
  | some fv, some gv =>
    let listed (z : ID) : Bool := (f.block? fv.block).any (·.values.contains z)
    if !ssSame fv gv && gv.id == x && gv.block == fv.block && gv.type == fv.type &&
        (fv.op == .Store || fv.op == .SelectN || fv.op == .Move) && f.blocks.contains fv.block &&
        listed x then
      match (((((chainSeg? tabs f g x fv gv).orElse fun _ => callSeg? tabs f g fv gv).orElse
          fun _ => zeroSeg? tabs f fv gv).orElse fun _ => roSeg? tabs f fv gv).orElse
          fun _ => moveSeg? tabs f g x fv gv).orElse fun _ => tileSeg? tabs f g x fv gv with
      | some (D, N) =>
        let L := N ++ [x]
        let ext (a : ID) : Bool := !D.contains a && !L.contains a &&
          (D ++ [x]).any fun s => CSE.rootNode f s && argReach f 8 s a
        let argOf (a : ID) : Bool :=
          (D ++ [x]).any fun s => CSE.rootNode f s && (f.value? s).any (·.args.contains a)
        if D.all listed && D.all (CSE.rootNode f) &&
            N.all (fun n => (f.value? n).isNone && (g.block? fv.block).any (·.values.contains n) &&
              (g.value? n).any (·.block == fv.block)) &&
            CSE.rootNode g x &&
            N.all (fun n => CSE.rootNode g n ||
              (g.value? n).any fun v => v.op == .OffPtr && v.args.all argOf) &&
            (List.range L.length).all (fun i => (g.value? (L.getD i 0)).all fun v =>
              v.args.all fun a => (L.take i).contains a || ext a) then some (D, N)
        else none
      | none => none
    else none
  | _, _ => none

/-- The segments of `f` in `g` by anchor (`segOK`). -/
def segArr (tabs : Tables) (f g : Func) : Array (Option (List ID × List ID)) :=
  (Array.range f.valueTab.size).map (segOK tabs f g)

/-- The anchors with their segments (dropped and fresh values). -/
def segList (A : Array (Option (List ID × List ID))) : List (ID × List ID × List ID) :=
  (List.range A.size).filterMap fun x => (A[x]?.join).map (x, ·)

/-- The anchor of the (first) segment of `segs` that drops `z`. -/
def segOwner (segs : List (ID × List ID × List ID)) (z : ID) : Option ID :=
  (segs.find? fun s => s.2.1.contains z).map (·.1)

/-- The segment of `segs` value `z` is a root of: its own if it is an anchor, else its owner's. -/
def segOf (segs : List (ID × List ID × List ID)) (z : ID) : Option ID :=
  if segs.any (·.1 == z) then some z else segOwner segs z

/-- The roots of `g` that the segment of anchor `x` puts in: its fresh values and the anchor. -/
def segNew (g : Func) (segs : List (ID × List ID × List ID)) (x : ID) : List ID :=
  ((segs.find? (·.1 == x)).map fun s => (s.2.2 ++ [x]).filter (CSE.rootNode g)).getD []

/-- The roots `L` of `f` with each segment's roots (its dropped roots and its anchor) replaced,
at the last of them, by its fresh roots and its anchor in `g` (`segNew`). -/
def segRoots (g : Func) (segs : List (ID × List ID × List ID)) : List ID → List ID
  | [] => []
  | r :: L =>
    match segOf segs r with
    | some x =>
      (if L.any (fun z => segOf segs z == some x) then [] else segNew g segs x) ++ segRoots g segs L
    | none => r :: segRoots g segs L

/-- Block `bid` of `g` has `f`'s kind and controls, `f`'s values but the dropped ones, then fresh
values (in `news`) of `bid`; its schedule runs `f`'s roots with each segment's in its place
(`segRoots`). -/
def segBlockOK (f g : Func) (segs : List (ID × List ID × List ID)) (news : List ID) (bid : ID) :
    Bool :=
  match f.block? bid, g.block? bid with
  | some fb, some gb =>
    let kept := fb.values.filter fun z => (segOwner segs z).isNone
    gb.kind == fb.kind && gb.controls == fb.controls && kept.size ≤ gb.values.size &&
    gb.values.extract 0 kept.size == kept &&
    (gb.values.extract kept.size gb.values.size).all
      (fun x => (f.value? x).isNone && news.contains x && (g.value? x).any (·.block == bid)) &&
    match Sem.schedule f fb with
    | none => true
    | some oS =>
      match Sem.schedule g gb with
      | some oT =>
        oT.toList.filter (CSE.rootNode g) == segRoots g segs (oS.toList.filter (CSE.rootNode f))
      | none => false
  | _, _ => false

/-- **The segment relation**: `g` is `f` with segments rewritten (`segOK`): the same control-flow
graph, own aux and blocks (`segBlockOK`); every value of `f` kept but for its use count, an
anchor, or dropped (gone in `g`, in one segment, used by no listed value or control of `f` but
its segment's); the fresh values the only values `f` lacks. -/
def segRel (tabs : Tables) (f g : Func) : Bool :=
  let segs := segList (segArr tabs f g)
  let drops := segs.flatMap (·.2.1)
  let news := segs.flatMap (·.2.2)
  DomCert.cfgView g == DomCert.cfgView f && g.ownAux == f.ownAux &&
    f.valueTab.size ≤ g.valueTab.size && decide drops.Nodup && decide news.Nodup &&
    segs.all (fun s => (segOwner segs s.1).isNone) &&
    (List.range f.valueTab.size).all (fun x => match f.value? x, g.value? x with
      | none, _ => true
      | some fv, some gv => ssSame fv gv || (segOK tabs f g x).isSome
      | some _, none => (segOwner segs x).isSome) &&
    drops.all (fun d => (g.value? d).isNone) &&
    (List.range g.valueTab.size).all (fun x =>
      (f.value? x).isSome || (g.value? x).isNone || news.contains x) &&
    f.blocks.all (fun b => match f.block? b with
      | some fb =>
        fb.controls.all (fun c => (segOwner segs c).isNone) &&
        fb.values.all fun z => (f.value? z).all fun zv => zv.args.all fun a =>
          match segOwner segs a with
          | some x => z == x || segOwner segs z == some x
          | none => true
      | none => false) &&
    f.blocks.all (segBlockOK f g segs news)

/-- Every read-only data symbol defined in `tabs`, with its allocation. With `tabs` the export
file's frontend tables this covers every symbol a pass can introduce (passes take new symbols
from the frontend), so the verified pipeline pins these, not only its input's (`pipelineRo`). -/
def roAll (tabs : Tables) : List (String × Sem.Alloc) :=
  (List.range tabs.auxes.size).filterMap fun n => roSym? tabs (some n)

/-- The read-only `go:string.…` data symbols of the string auxes in `tabs`, with the allocation
`Rules.stringData` gives them when a pass materialises one (`fe.StringData`, e.g. for a
`ConstString`, `generic.rules:1022`): `SRODATA`, the string's bytes, no relocations. Empty strings
have no data symbol. -/
def roStrs (tabs : Tables) : List (String × Sem.Alloc) :=
  tabs.auxes.toList.filterMap fun d? => d?.bind fun d =>
    match d.kind with
    | .str t dn => if t.bytes.size == 0 then none
                   else some (dn.toStringLossy, Sem.rodataAlloc t.bytes t.bytes.size #[])
    | _ => none

/-- The read-only symbols the rewrite passes' precondition pins (`Pass.Rewrite.RwPre`) for the
input `f` in `tabs` with the frontend tables `fe`: those `f`'s `Addr`s name and every one the
frontend defines (`roAll`), so a fixed load from a symbol a pass took from the frontend (the
dictionary a first fixed load's `Addr` names, `reflect.TypeFor[T]`, issue #69) reads pinned
bytes. -/
def roPass (tabs fe : Tables) (f : Func) : List (String × Sem.Alloc) := roSyms tabs f ++ roAll fe

/-- The source of the `Move` `fv` of `f` is an `Addr` of a symbol of `ro` whose bytes are zero. -/
def roSrcOK (tabs : Tables) (ro : List (String × Sem.Alloc)) (f : Func) (fv : Value) : Bool :=
  match fv.args.toList with
  | [_, s, _] => (f.value? s).any fun sv => (WBCheck.symName? tabs sv.aux).any fun n =>
      ro.any fun e => e.1 == n && e.2.data.all (· == .b 0)
  | _ => false

/-- The read-only segments (`roSeg?`; the anchors that are `Move`s of `f` and `Zero`s of `g` but
the zero segments, `zeroSeg?`) copy from symbols of
`ro` whose bytes are zero, and `f` passes `WBCheck.memTyOK` (so every memory a run of `f` holds
has the symbols of `ro`, `GoFV.Proof.MemInv`). -/
def roSegsOK (tabs : Tables) (ro : List (String × Sem.Alloc)) (f g : Func) : Bool :=
  let movs := (segList (segArr tabs f g)).filter fun s =>
    match f.value? s.1, g.value? s.1 with
    | some fv, some gv => fv.op == .Move && gv.op == .Zero && (zeroSeg? tabs f fv gv).isNone
    | _, _ => false
  movs.isEmpty ||
    (WBCheck.memTyOK tabs f && movs.all fun s => (f.value? s.1).all (roSrcOK tabs ro f))

/-! ## Selections of `Phi`s of `SliceMake`s as a layer (issue #69)

`generic.rules:1049`/`:1050` (`(SliceLen (Phi (SliceMake _ x _) (SliceMake _ x _))) => x`, the
capacity likewise) match through a `Phi`, which `validate` treats as an atom: the `Phi`'s
value is the `SliceMake` of the edge it was entered along, whose length is `x`'s value then.
Their events are taken out of the log (`psPre`: the selection becomes `Copy x`), and the layer
is related to its input by `psRel`, whose simulation (`GoFV.Proof.PhiSel.ps_refines`) keeps the
fact that the selection of the `Phi` refines `x` while the `Phi`'s block dominates: `x` is
defined in a strict dominator of the `Phi`'s block, so it is not redefined in between. -/

/-- A `phiSels` rule: a `SliceLen`/`SliceCap` of a `Phi` with a copy result. -/
def psShapeOK (r : Rule) : Bool :=
  match r.pat, r.result, r.block with
  | .op o none _ _ _ _ [.op .Phi _ _ _ _ _ _ _] _, .copy _, none => o == .SliceLen || o == .SliceCap
  | _, _, _ => false

/-- The component a selection of `psOK` reads: `SliceLen` 1, `SliceCap` 2. -/
def psSel : Op → Option Nat
  | .SliceLen => some 1
  | .SliceCap => some 2
  | _ => none

/-- The value a `SliceMake` component `c` of `f` stands for: `x` if `c` is `Sub64 x z` with `z` a
`Const64 [0]` (the length `j - 0` of a slice `s[0:j]` before `generic.rules` simplifies it),
else `c`. -/
def psBase (f : Func) (c : ID) : ID :=
  match f.value? c with
  | some cv =>
    match cv.op, cv.args[0]?, cv.args[1]? with
    | .Sub64, some x, some z =>
      if (f.value? z).any (fun zv => zv.op == .Const64 && zv.auxInt == 0) then x else c
    | _, _, _ => c
  | none => c

/-- The `SliceMake` component `c` of `f` holds the value of `x`: it is `x`, or `Sub64 x z` of the
`int64` shape with `z` a `Const64 [0]` of the `int64` shape. -/
def psComp (tabs : Tables) (f : Func) (c x : ID) : Bool :=
  c == x || (f.value? c).any fun cv =>
    cv.op == .Sub64 && cv.args.size == 2 && cv.args[0]? == some x &&
      isInt64Ty (tabs.ty cv.type) &&
      (cv.args[1]?.bind f.value?).any fun zv =>
        zv.op == .Const64 && zv.auxInt == 0 && isInt64Ty (tabs.ty zv.type)

/-- The value `x` a `psOK` selection `v` of `f` becomes a copy of: what component `k` of the
first `SliceMake` of its `Phi` stands for (`psBase`). -/
def psSrc (f : Func) (v : ID) : Option ID := do
  let u ← f.value? v
  let k ← psSel u.op
  let p ← u.args[0]?
  let pv ← f.value? p
  let m ← pv.args[0]?
  let mv ← f.value? m
  let c ← mv.args[k]?
  return psBase f c

/-- The value `v` of `f` that event `ev` turns into a copy, and the copied value (`psSrc`), if
it is a `phiSels` rule event (`psShapeOK`) of a rule on `v`'s op in `f`. -/
def psEvent? (t : Interp.Table) (f : Func) : RwEvent → Option (ID × ID)
  | .rule v i _ _ =>
    match f.value? v with
    | some u =>
      let n := t.psBase u.op
      if n ≤ i then
        match t.phiSels[i - n]?, psSrc f v with
        | some cr, some x =>
          if psShapeOK cr.rule && (match cr.rule.pat with | .op o .. => o == u.op | _ => false) then
            some (v, x)
          else none
        | _, _ => none
      else none
    | none => none
  | _ => none

/-- One event of `psPre`: a selection of `f` becomes a copy (`Func.copyOf`), any other event
kept, but for the copy-argument replacements of the selection logged before it. -/
def psStep (t : Interp.Table) (f : Func) (p : Func × Array RwEvent) (ev : RwEvent) :
    Func × Array RwEvent :=
  match psEvent? t f ev with
  | some (v, x) => (p.1.copyOf v x, p.2.filter fun | .copyArg y _ _ => y != v | _ => true)
  | none => (p.1, p.2.push ev)

/-- The input with the log's `phiSels` events applied, and the remaining events. -/
def psPre (t : Interp.Table) (f : Func) (log : Array RwEvent) : Func × Array RwEvent :=
  log.foldl (psStep t f) (f, #[])

/-- The value `v` of `f`, `SliceLen`/`SliceCap` (component `k`, `psSel`) of a `Phi` `p`, is
`Copy x` in `g`: every argument of `p` is a `SliceMake` whose argument `k` holds `x`'s value
(`psComp`), `p` and those `SliceMake`s have slice shapes, `v` (in `f` and `g`) and `x` the
`int64` shape, `p` is listed in its block, which is not the entry block, and `x` is defined in a
strict dominator of `p`'s block. -/
def psOK (tabs : Tables) (f g : Func) (v : ID) : Bool :=
  match f.value? v, g.value? v with
  | some u, some w =>
    match psSel u.op, u.args[0]?, w.args[0]? with
    | some k, some p, some x =>
      u.args.size == 1 && w.args.size == 1 && w.op == .Copy && w.id == u.id &&
        w.block == u.block && isInt64Ty (tabs.ty u.type) && isInt64Ty (tabs.ty w.type) &&
        match f.value? p, f.value? x with
        | some pv, some xv =>
          pv.op == .Phi && pv.id == p && pv.block != f.entry && f.blocks.contains pv.block &&
            (f.block? pv.block).any (·.values.contains p) && isSliceTy (tabs.ty pv.type) &&
            isInt64Ty (tabs.ty xv.type) && xv.block != pv.block &&
            (DomCert.make f).anc xv.block pv.block &&
            pv.args.all fun m => (f.value? m).any fun mv =>
              mv.op == .SliceMake && mv.args.size == 3 &&
                (mv.args[k]?).any (psComp tabs f · x) && isSliceTy (tabs.ty mv.type)
        | _, _ => false
    | _, _, _ => false
  | _, _ => false

/-- **The `Phi`-selection relation**: `g` is `f` with selections turned copies (`psOK`): the same
control-flow graph, own aux, value IDs and blocks (kinds, controls, value lists and schedules);
every other value kept but for its use count. -/
def psRel (tabs : Tables) (f g : Func) : Bool :=
  DomCert.cfgView g == DomCert.cfgView f && g.ownAux == f.ownAux &&
    g.valueTab.size == f.valueTab.size &&
    (List.range f.valueTab.size).all (fun z => match f.value? z, g.value? z with
      | none, none => true
      | some fv, some gv => ssSame fv gv || psOK tabs f g z
      | _, _ => false) &&
    f.blocks.all fun b => match f.block? b, g.block? b with
      | some fb, some gb =>
        gb.kind == fb.kind && gb.controls == fb.controls && gb.values == fb.values &&
          Sem.schedule g gb == Sem.schedule f fb
      | _, _ => false

/-! ## Struct-load expansions as a layer (issue #151)

A struct-store split of a `Store` of a `Load` that `generic.rules:974` expanded stores the
expansion's fresh field `Load`s: the split layer needs the expansion applied first. `slPre`
applies the log's expansions that `structLoadOK` validates on the layer's input (the `Load`
becomes the `StructMake`, the fresh `OffPtr`s and `Load`s are put in), and the layer is related
to its input by `validate` with those events alone. -/

/-- A struct-load expansion's logged values on the `Load` `v`'s arguments in `f`: when copy
elimination replaced the `Load`'s pointer (argument 0) or memory (argument 1) before the expansion
(in `prior`), the fresh `OffPtr`s (`Load`s) took the copy's source; they take the `Load`'s argument
instead (`slMove` moves the replacements to them). -/
def slRebase (f : Func) (v : ID) (prior : Array RwEvent) (defs : List Value) : List Value :=
  match f.value? v, defs with
  | some u, x' :: ds =>
    let p0 := copyArgOf prior v 0
    let p1 := copyArgOf prior v 1
    x' :: ds.map fun d =>
      if p0 && d.op == .OffPtr && d.args.size == 1 then { d with args := #[u.args[0]?.getD 0] }
      else if p1 && d.op == .Load && d.args.size == 2 then
        { d with args := d.args.set! 1 (u.args[1]?.getD 0) }
      else d
  | _, _ => defs

/-- The events `evs` after the expansion of `v` with the fresh values `ds`: the replacements of
`v`'s pointer (memory) moved to each fresh `OffPtr` (`Load`), `v`'s others dropped. -/
def slMove (v : ID) (ds : List Value) (evs : Array RwEvent) : Array RwEvent :=
  evs.foldl (fun acc e => match e with
    | .copyArg y i src =>
      if y != v then acc.push e
      else if i == 0 then
        ds.foldl (fun a d => if d.op == .OffPtr then a.push (.copyArg d.id 0 src) else a) acc
      else if i == 1 then
        ds.foldl (fun a d => if d.op == .Load then a.push (.copyArg d.id 1 src) else a) acc
      else acc
    | e => acc.push e) #[]

/-- The `Load` `v` of `f` that event `ev` expands (a `structLoads` rule event, `structLoadShapeOK`)
and the logged definitions rebased on its arguments (`slRebase`, after the events `prior`), if
`structLoadOK` validates them on `f`'s definitions. -/
def slEvent? (t : Interp.Table) (tabs : Tables) (f : Func) (prior : Array RwEvent) :
    RwEvent → Option (ID × List Value)
  | .rule v i _ defs =>
    match f.value? v with
    | some u =>
      let n := ((t.values[u.op.ctorIdx]?).map (·.size)).getD 0
      let ds := slRebase f v prior defs.toList
      if u.op == .Load && n + t.loads.size ≤ i &&
          (t.structLoads[i - n - t.loads.size]?).any (structLoadShapeOK ·.rule) &&
          structLoadOK tabs f.valueTab v ds then some (v, ds)
      else none
    | none => none
  | _ => none

/-- The expansion of the `Load` `v`: its arguments lose a use, the fresh values put in, and `v`
redefined as the logged `StructMake` (or, for an `@b` result, the logged `Copy` with its type),
whose arguments gain a use. -/
def slApply (f : Func) (v : ID) : List Value → Func
  | [] => f
  | x' :: ds =>
    match f.value? v with
    | some u =>
      let f := u.args.foldl (fun f a => f.modV a fun w => { w with uses := w.uses - 1 }) f
      let f := x'.args.foldl Func.incUses (ds.foldl ssPut f)
      f.modV v fun w =>
        { w with op := x'.op, type := x'.type, auxInt := x'.auxInt, aux := x'.aux, args := x'.args }
    | none => f

/-- A rule event with the definitions `ds` instead of the logged ones. -/
def evWithDefs : RwEvent → List Value → RwEvent
  | .rule v i b _, ds => .rule v i b ds.toArray
  | e, _ => e

/-- One event of `slPre` (state: the function, the kept events, the applied expansions): an
expansion of `f` is applied and taken (as rebased), any other event kept, the copy-argument
replacements of the expanded `Load` logged before it moved (`slMove`). -/
def slStep (t : Interp.Table) (tabs : Tables) (f : Func)
    (p : Func × Array RwEvent × Array RwEvent) (ev : RwEvent) :
    Func × Array RwEvent × Array RwEvent :=
  match slEvent? t tabs f p.2.1 ev with
  | some (v, ds) => (slApply p.1 v ds, slMove v ds.tail p.2.1, p.2.2.push (evWithDefs ev ds))
  | none => (p.1, p.2.1.push ev, p.2.2)

/-- `slStep` over the log of the layer's input `f`. -/
def slRun (t : Interp.Table) (tabs : Tables) (f : Func) (log : Array RwEvent) :
    Func × Array RwEvent × Array RwEvent :=
  log.foldl (slStep t tabs f) (f, #[], #[])

/-- The input with the log's validated struct-load expansions applied, and the remaining events. -/
def slPre (t : Interp.Table) (tabs : Tables) (f : Func) (log : Array RwEvent) :
    Func × Array RwEvent :=
  let r := slRun t tabs f log
  (r.1, r.2.1)

/-- The expansions `slPre` applies, as rebased. -/
def slTaken (t : Interp.Table) (tabs : Tables) (f : Func) (log : Array RwEvent) : Array RwEvent :=
  (slRun t tabs f log).2.2

/-! ## Value-rule `Load` expansions as a layer (issue #17)

The decompose rules expand a `Load` of a builtin composite by a value rule
(`(Load <t> ptr mem) && t.IsString() => (StringMake (Load …) (Load … (OffPtr …)))`), and a
`Store` of that value is then split in place: as for the struct-load expansions, the split layer
needs the expansion applied first. `ldPre` takes, in log order, the value-rule events on `Load`s
and on one-argument values of a `Load` or a `Make` (the extractors `dec.rules:132`–`:162`,
`(StringPtr x:(Load <t> ptr mem)) => @x.Block (Load …)`, which the rewrite logs before the
`Load`'s own expansion, which would turn their argument into a `Make` they no longer match; the
selections `(SlicePtr (SliceMake ptr _ _)) => ptr`, whose results a split stores), and the
copy-argument replacements of a `Load`'s argument or by a `Load` (copy elimination before such a
rule: `(SliceLen (StructSelect [i] (Load …)))` reads the field `Load` the selection became), each
if the replay validates it on the definitions of the events taken before (`v` redefined as logged,
the fresh values put in: `slApply`; an argument replaced: `Func.setArg`). The layer is related to
its input by `validate` with the taken events; the events it supersedes (replacements of the
same argument, or of an argument of a redefined value, logged before) are dropped. -/

/-- `u` is a `Load` or has one argument, a `Load` or a `Make` (`ssMakeOp`) of `M`. -/
def ldTarget (M : Defs) (u : Value) : Bool :=
  u.op == .Load ||
    (u.args.size == 1 && (u.args[0]?.bind M.get?).any fun w => w.op == .Load || ssMakeOp w.op)

/-- The state of `ldPre`: the layer's function, the definitions the taken events replay to from
the input's, the taken events and the remaining ones. -/
structure LdSt where
  g : Func
  M : Defs
  taken : Array RwEvent
  rest : Array RwEvent

/-- One event of `ldPre` (input `f`): a value-rule event on an `ldTarget` of the definitions so
far, or a copy-argument replacement of a `Load`'s argument or by a `Load` at a value no event left
in the log redefines before it (the replacement is of the redefined value's argument), that the
replay validates on them is applied and taken (not an event the replay skips: of a dropped rule,
`dropShape`, or a replacement the copies do not justify); any other event kept, but for the
copy-argument replacements a taken event supersedes. -/
def ldStep (t : Interp.Table) (tabs : Tables) (f : Func) (s : LdSt) (ev : RwEvent) : LdSt :=
  let keep := { s with rest := s.rest.push ev }
  match ev with
  | .rule v i _ defs =>
    match s.M.get? v with
    | some u =>
      if ldTarget s.M u && i < ((t.values[u.op.ctorIdx]?).map (·.size)).getD 0 &&
          !(((t.values[u.op.ctorIdx]?).bind (·[i]?)).any (dropShape ·.rule)) then
        match replay tabs t f false s.M [] [ev] with
        | some (M', _) =>
          let ds := match defs.toList with | w :: ds => w :: (ds.filter (·.id != v)).reverse | [] => []
          { g := slApply s.g v ds, M := M', taken := s.taken.push ev
            rest := s.rest.filter fun | .copyArg y _ _ => y != v | _ => true }
        | none => keep
      else keep
    | none => keep
  | .copyArg v i src =>
    match s.M.get? v, s.M.get? src with
    | some u, some w =>
      if (u.op == .Load || w.op == .Load) &&
          (u.args[i]?).any (copyReachW tabs s.M s.M.size · src) &&
          !s.rest.any (fun | .rule y _ _ _ => y == v | _ => false) then
        match replay tabs t f false s.M [] [ev] with
        | some (M', _) =>
          { g := s.g.setArg v i src, M := M', taken := s.taken.push ev
            rest := s.rest.filter fun | .copyArg y j _ => !(y == v && j == i) | _ => true }
        | none => keep
      else keep
    | _, _ => keep
  | _ => keep

/-- `ldStep` over the log of the layer's input `f`. -/
def ldRun (t : Interp.Table) (tabs : Tables) (f : Func) (log : Array RwEvent) : LdSt :=
  log.foldl (ldStep t tabs f) { g := f, M := f.valueTab, taken := #[], rest := #[] }

/-- The input with the log's validated value-rule `Load` expansions (and the copy-argument
replacements they need) applied, and the remaining events. -/
def ldPre (t : Interp.Table) (tabs : Tables) (f : Func) (log : Array RwEvent) :
    Func × Array RwEvent :=
  let s := ldRun t tabs f log
  (s.g, s.rest)

/-- The events `ldPre` applies. -/
def ldTaken (t : Interp.Table) (tabs : Tables) (f : Func) (log : Array RwEvent) : Array RwEvent :=
  (ldRun t tabs f log).taken

end GoFV.Opt.RewriteCheck

/-! ## sccp's checker (issue #32), shared with the constant-`Phi` layer (issue #69)

The Bool checker of `GoFV.Opt.sccpChecked` (`GoFV/Opt/SccpCheck.lean`, which documents it): a
certificate of constant cells (`Lat`), executable edges and blocks, and `sccpOK`, which relates
a function to one with some values turned constants of their claimed value. It is here, not in
`SccpCheck`, because the constant-`Phi` layer of the rewrite validator (`RewriteCheck.pcRel`)
uses it, and `SccpCheck` imports this module. -/

namespace GoFV.Opt.Sccp

open GoFV.SSA GoFV.Rules

/-- `lattice`: `top`, `constant` (the value `lt.val`, with its `Op` and `AuxInt`, which never
change during the pass) or `bottom`. -/
inductive Lat where
  | top
  | const (v : ID) (op : Op) (auxInt : Int64)
  | bottom
  deriving Inhabited, Repr

/-- `isConst(v)`. -/
def isConst : Op → Bool
  | .Const64 | .Const32 | .Const16 | .Const8 | .ConstBool | .Const32F | .Const64F => true
  | _ => false

/-- An integer or boolean value: `some` of it, else `none`. -/
def scalar? : Sem.Val → Option Sem.Val
  | .int w x => some (.int w x)
  | .bool b => some (.bool b)
  | _ => none

/-- Equality of integer and boolean values (`false` for any other value). -/
def scalarEq : Sem.Val → Sem.Val → Bool
  | .int w x, .int w' x' => w == w' && x.toNat == x'.toNat
  | .bool b, .bool b' => b == b'
  | _, _ => false

/-- The value of a constant op at shape `t`, at `Addrs.fixed` (`Val.retypeC`), if it holds no
frame pointer (then every instance gives it), else `poison` (no scalar, so no claim). -/
def constVal (op : Op) (t : Sem.Ty) (ai : Int64) : Sem.Val :=
  let v := @Sem.evalPure Sem.Addrs.fixed op t ai none []
  if v.lowB then v.retypeC t else .poison

/-- The constant `x`'s cell claims: its constant op's value at `x`'s type, if an integer or
boolean. -/
def cval (tabs : Tables) (f : Func) (C : Array (Option Lat)) (x : ID) : Option Sem.Val :=
  match C[x]?.join, f.value? x with
  | some (.const _ op ai), some v =>
    if isConst op then scalar? (constVal op (tabs.ty v.type) ai) else none
  | _, _ => none

/-- `⟨b, i⟩` is an executable edge. -/
def live (vis : Array Edge) (b : ID) (i : Nat) : Bool := vis.contains ⟨b, i⟩

/-- The terminator of `pb` may take its successor `k`. -/
def feasible (tabs : Tables) (f : Func) (C : Array (Option Lat)) (pb : Block) (k : Nat) : Bool :=
  match pb.kind with
  | .Plain | .First => k == 0
  | .If =>
    match pb.controls[0]?.bind (cval tabs f C) with
    | some (.bool t) => k == if t then 0 else 1
    | _ => true
  | .JumpTable =>
    match pb.controls[0]?.bind (cval tabs f C) with
    | some (.int _ x) => k == x.toNat
    | _ => true
  | _ => true

/-- The executable part is closed under the successors a terminator can take. -/
def reachOK (tabs : Tables) (f : Func) (C : Array (Option Lat)) (vis : Array Edge)
    (R : Array Bool) : Bool :=
  R.getD f.entry false && live vis f.entry 0 &&
  f.blocks.all fun p =>
    !R.getD p false || match f.block? p with
      | some pb => (List.range pb.succs.size).all fun k =>
          !feasible tabs f C pb k ||
            (live vis pb.succs[k]!.b pb.succs[k]!.i && R.getD pb.succs[k]!.b false)
      | none => true

/-- The post-fixpoint condition at value `x`. -/
def fixOK (tabs : Tables) (f : Func) (C : Array (Option Lat)) (vis : Array Edge) (x : ID) :
    Bool :=
  match cval tabs f C x, f.value? x with
  | some c, some v =>
    let t := tabs.ty v.type
    if v.op == .Phi then
      (List.range v.args.size).all fun i =>
        !live vis v.block i || match cval tabs f C v.args[i]! with
          | some c' => scalarEq (c'.retypeC t) c
          | none => false
    else
      RewriteCheck.termOp v.op &&
      match v.args.toList.mapM (cval tabs f C) with
      | some cs => match GoFV.Proof.Rules.opValC tabs v.op t v.auxInt v.aux cs with
        | some r => scalarEq (r.retypeC t) c
        | none => false
      | none => false
  | _, _ => true

/-- Value `x` of `f` is unchanged in `g` (but for its use count), or became a constant term of
its claimed value. -/
def repOK (tabs : Tables) (f g : Func) (C : Array (Option Lat)) (x : ID) : Bool :=
  match f.value? x, g.value? x with
  | none, _ => true
  | some _, none => false
  | some u, some w =>
    w.id == u.id && w.block == u.block &&
    ((w.op == u.op && w.type == u.type && w.auxInt == u.auxInt && w.aux == u.aux &&
      w.args == u.args) ||
     (RewriteCheck.termOp w.op && w.args.isEmpty && w.type == u.type &&
      match cval tabs f C x, GoFV.Proof.Rules.opValC tabs w.op (tabs.ty w.type) w.auxInt w.aux [] with
      | some c, some r => scalarEq (r.retypeC (tabs.ty w.type)) c
      | _, _ => false))

/-- The successor an `If` or `JumpTable` takes on the constant control `c`. -/
def pickIdx : BlockKind → Option Sem.Val → Option Nat
  | .If, some (.bool t) => some (if t then 0 else 1)
  | .JumpTable, some (.int _ x) => some x.toNat
  | _, _ => none

/-- An `If` or `JumpTable` with a constant control became, in `h`, a `First` block (no
controls) whose successor 0 is the one the constant picks, with the same successors. -/
def firstOK (tabs : Tables) (f : Func) (C : Array (Option Lat)) (fb hb : Block) : Bool :=
  hb.kind == .First && hb.controls.isEmpty && fb.succs.all (hb.succs.contains ·) &&
  match pickIdx fb.kind (fb.controls[0]?.bind (cval tabs f C)) with
  | some k => (fb.succs[k]?).isSome && hb.succs[0]? == fb.succs[k]?
  | none => false

/-- `h`'s blocks list `f`'s values first, with the same IDs, and the same kinds, successors and
controls, or an `If`/`JumpTable` turned `First` (`firstOK`). -/
def blocksOK (tabs : Tables) (f h : Func) (C : Array (Option Lat)) : Bool :=
  f.blocks.all fun b =>
    match f.block? b, h.block? b with
    | some fb, some hb =>
      fb.id == hb.id && fb.values == hb.values.extract 0 fb.values.size &&
      ((fb.kind == hb.kind && fb.succs == hb.succs && fb.controls == hb.controls) ||
        firstOK tabs f C fb hb)
    | _, _ => false

/-- **The checker** (`f` to the intermediate `h`). -/
def sccpOK (tabs : Tables) (f h : Func) (C : Array (Option Lat)) (vis : Array Edge)
    (R : Array Bool) : Bool :=
  RewriteCheck.atomsOK f h && RewriteCheck.closedOK f && RewriteCheck.closedOK h &&
  blocksOK tabs f h C && reachOK tabs f C vis R &&
  (List.range f.valueTab.size).all (fun x => fixOK tabs f C vis x && repOK tabs f h C x)

end GoFV.Opt.Sccp

namespace GoFV.Opt.RewriteCheck

open GoFV.SSA GoFV.Rules GoFV.Proof.Rules

/-! ## Constant `Phi`s as a layer (issue #69)

`generic.rules:782`–`:785` (`(Phi (Const64 [c]) (Const64 [c])) => (Const64 [c])`, the narrower
widths likewise) match a `Phi`, which `validate` treats as an atom: its value is the argument of
the edge it was entered along. They are `phiSels` rules, logged after a snapshot (`tryRule`'s
`snap`), so each is the first event of its segment and its `Phi`'s arguments are the constants in
the layer's input. `pcPre` turns the `Phi` into the logged constant, and the layer is related to
its input by sccp's checker (`pcRel`): `Sccp.sccpOK` with the certificate `pcCells` (the turned
`Phi`s and their constant arguments claim their constants, every edge and block is executable),
whose simulation (`GoFV.Proof.Sccp`) keeps the fact that a register with a constant cell holds
`poison` or the constant. -/

/-- A `phiSels` rule that turns a `Phi` into a constant op built in place, without arguments. -/
def pcShapeOK (r : Rule) : Bool :=
  match r.pat, r.result, r.block with
  | .op .Phi .., .build [n], none => Sccp.isConst n.op && n.args.isEmpty && n.ty.isNone
  | _, _, _ => false

/-- The `Phi` `v` of `f` that event `ev` turns into a constant, and its logged definition, if it
is a `phiSels` rule event of a constant-`Phi` rule (`pcShapeOK`). -/
def pcEvent? (t : Interp.Table) (f : Func) : RwEvent → Option (ID × Value)
  | .rule v i _ defs =>
    match f.value? v, defs[0]? with
    | some u, some d =>
      let n := t.psBase u.op
      if u.op == .Phi && n ≤ i && d.id == v then
        match t.phiSels[i - n]? with
        | some cr => if pcShapeOK cr.rule then some (v, d) else none
        | none => none
      else none
    | _, _ => none
  | _ => none

/-- The value `v` of `f` becomes the constant `d` (`v.reset(op)`, `v.AuxInt = d.AuxInt`). -/
def pcApply (f : Func) (v : ID) (d : Value) : Func :=
  (f.resetValue v d.op).modV v fun x => { x with auxInt := d.auxInt }

/-- One event of `pcPre`: a constant-`Phi` event applied, any other event kept. -/
def pcStep (t : Interp.Table) (f : Func) (p : Func × Array RwEvent) (ev : RwEvent) :
    Func × Array RwEvent :=
  match pcEvent? t f ev with
  | some (v, d) => (pcApply p.1 v d, p.2)
  | none => (p.1, p.2.push ev)

/-- The input with the log's constant-`Phi` events applied, and the remaining events. -/
def pcPre (t : Interp.Table) (f : Func) (log : Array RwEvent) : Func × Array RwEvent :=
  log.foldl (pcStep t f) (f, #[])

/-- The certificate of a constant-`Phi` layer from `f` to `g`: each `Phi` of `f` that is a
constant in `g` claims that constant, each constant argument of such a `Phi` its own. -/
def pcCells (f g : Func) : Array (Option Sccp.Lat) := Id.run do
  let mut C : Array (Option Sccp.Lat) := Array.replicate f.valueTab.size none
  for x in [0:f.valueTab.size] do
    match f.value? x, g.value? x with
    | some u, some w =>
      if u.op == .Phi && Sccp.isConst w.op then
        C := C.set! x (some (.const x w.op w.auxInt))
        for a in u.args do
          if let some av := f.value? a then
            if Sccp.isConst av.op then C := C.set! a (some (.const a av.op av.auxInt))
    | _, _ => pure ()
  return C

/-- Every edge of `f` and the entry's edge 0 (sccp's start). -/
def pcVis (f : Func) : Array Edge :=
  f.blocks.foldl (init := #[⟨f.entry, 0⟩]) fun acc b =>
    match f.block? b with
    | some fb => acc ++ fb.succs
    | none => acc

/-- **The constant-`Phi` relation**: sccp's checker accepts `g` against `f` with every edge and
block executable and the certificate `pcCells`. -/
def pcRel (tabs : Tables) (f g : Func) : Bool :=
  Sccp.sccpOK tabs f g (pcCells f g) (pcVis f) (Array.replicate f.blockTab.size true)

/-! ## `Phi`s of `Not`s as a layer (issue #69)

`generic.rules:1068` (`(Phi <t> nx:(Not x) ny:(Not y)) && nx.Uses == 1 && ny.Uses == 1 =>
(Not (Phi <t> x y))`) turns a `Phi` into the `Not` of a fresh `Phi` of the `Not`s' arguments; the
target has a `Phi` atom the source lacks, which `validate` does not relate. It is a `phiSels`
rule, logged after a snapshot, so each instance is the first event of its segment. `pnPre` puts
the fresh `Phi` in and redefines the `Phi` as the logged `Not`, and the layer is related to its
input by `pnRel`, whose simulation (`GoFV.Proof.PhiNot.pn_refines`) keeps, from the `Phi`'s
block entry until the target evaluates the `Not`, the fact that the source's `Phi` is refined by
the `Not` of the fresh `Phi`: entered along edge `j`, the source's `Phi` takes the register of
its argument `Not x_j`, which lemma (D) re-evaluates from `x_j`'s register, and the fresh `Phi`
takes `x_j`'s. -/

/-- A `phiSels` rule that turns a `Phi` into a `Not` of a fresh `Phi`. -/
def pnShapeOK (r : Rule) : Bool :=
  match r.pat, r.result, r.block with
  | .op .Phi .., .build [n, q], none => n.op == .Not && q.op == .Phi
  | _, _, _ => false

/-- The `Phi` `v` of `f` that event `ev` turns into a `Not`, its logged definition (the result's
root, built at `v`: `defs` is `[v, root, fresh Phi]`) and the logged fresh `Phi`, if it is a
`phiSels` rule event of a `pnShapeOK` rule. -/
def pnEvent? (t : Interp.Table) (f : Func) : RwEvent → Option (ID × Value × Value)
  | .rule v i _ defs =>
    match f.value? v, defs[1]?, defs[2]? with
    | some u, some d, some q =>
      let n := t.psBase u.op
      if u.op == .Phi && n ≤ i && d.id == v && q.id != v then
        match t.phiSels[i - n]? with
        | some cr => if pnShapeOK cr.rule then some (v, d, q) else none
        | none => none
      else none
    | _, _, _ => none
  | _ => none

/-- The `Phi` `v` of `f` becomes the logged `Not` `d` of the fresh `Phi` `q`, which is put in
first (`v.reset(OpNot)`, `v0 := b.NewValue0(OpPhi)`, `v0.AddArg2(x, y)`, `v.AddArg(v0)`). -/
def pnApply (f : Func) (v : ID) (d q : Value) : Func := fwdCopy (ssPut f q) v d

/-- One event of `pnPre`: a `Phi`-of-`Not`s event applied, any other event kept. -/
def pnStep (t : Interp.Table) (f : Func) (p : Func × Array RwEvent) (ev : RwEvent) :
    Func × Array RwEvent :=
  match pnEvent? t f ev with
  | some (v, d, q) => (pnApply p.1 v d q, p.2)
  | none => (p.1, p.2.push ev)

/-- The input with the log's `Phi`-of-`Not`s events applied, and the remaining events. -/
def pnPre (t : Interp.Table) (f : Func) (log : Array RwEvent) : Func × Array RwEvent :=
  log.foldl (pnStep t f) (f, #[])

/-- The `Phi` `v` of `f` (of a `bool` shape, in a block other than the entry) is `Not p` in `g`
(same type and block): `p` is not a value of `f`, and in `g` a `Phi` of `v`'s type listed in
`v`'s block whose argument `j` is the argument `x_j` of `v`'s argument `j`, a `Not`, both of a
`bool` shape. -/
def pnOK (tabs : Tables) (f g : Func) (v : ID) : Bool :=
  match f.value? v, g.value? v with
  | some u, some w =>
    match w.args[0]? with
    | some p =>
      u.op == .Phi && w.op == .Not && w.args.size == 1 && w.id == v && w.block == u.block &&
        w.type == u.type && (tabs.ty u.type matches .bool) && u.block != f.entry &&
        (f.value? p).isNone && (g.block? u.block).any (·.values.contains p) &&
        (g.value? p).any fun pv =>
          pv.op == .Phi && pv.id == p && pv.block == u.block && pv.type == u.type &&
            pv.args.size == u.args.size &&
            (pv.args.toList.zip u.args.toList).all fun (c, a) =>
              (f.value? a).any fun av =>
                av.op == .Not && av.args.size == 1 && av.args[0]? == some c &&
                  (tabs.ty av.type matches .bool) &&
                  (f.value? c).any fun cv => (tabs.ty cv.type matches .bool)
    | none => false
  | _, _ => false

/-- `z` is the fresh `Phi` of a `pnOK` value listed in `z`'s block of `g`. -/
def pnFresh (tabs : Tables) (f g : Func) (z : ID) : Bool :=
  match g.value? z with
  | some zv => (g.block? zv.block).any fun gb => gb.values.any fun v =>
      pnOK tabs f g v && (g.value? v).any (·.args[0]? == some z)
  | none => false

/-- **The `Phi`-of-`Not`s relation**: `g` is `f` with `Phi`s turned `Not`s of fresh `Phi`s
(`pnOK`): the same control-flow graph and own aux; every other value of `f` kept but for its use
count, every value `f` lacks such a fresh `Phi`; per block the same kind and controls, the
source's values in the same order with only fresh `Phi`s added, and the source's schedule the
target's without the turned `Phi`s. -/
def pnRel (tabs : Tables) (f g : Func) : Bool :=
  DomCert.cfgView g == DomCert.cfgView f && g.ownAux == f.ownAux &&
    decide (f.valueTab.size ≤ g.valueTab.size) &&
    (List.range g.valueTab.size).all (fun z => match f.value? z, g.value? z with
      | none, none => true
      | some fv, some gv => ssSame fv gv || pnOK tabs f g z
      | none, some _ => pnFresh tabs f g z
      | some _, none => false) &&
    f.blocks.all fun b => match f.block? b, g.block? b with
      | some fb, some gb =>
        gb.kind == fb.kind && gb.controls == fb.controls &&
          gb.values.toList.filter (fun z => (f.value? z).isSome) == fb.values.toList &&
          gb.values.all (fun z => (f.value? z).isSome || pnFresh tabs f g z) &&
          (match Sem.schedule f fb, Sem.schedule g gb with
            | some of, some og => og.toList.filter (fun z => !pnOK tabs f g z) == of.toList
            | _, _ => false)
      | _, _ => false

/-! ## Layers (issue #151)

The log's nil-check eliminations, Load-of-Store forwardings, struct-load expansions,
struct-store splits and segment rewrites are taken out of the log and applied to the input in
layers, each related to its input by its own relation, before `validate` relates the last
layer's function and the output with the remaining events. A selective layer (`sel`) applies
only the events its relation holds of in its input; a later layer of the same kind applies the
rest. Each kind needs another first: a struct-store split's pointer may be an eliminated nil check
and its stored values forwarded `Load`s or an expanded `Load`, a split may split a field store of
another (nested structs), a forwarded `Load` may read a field `Store` of a split, an eliminated nil
check's pointer may be a forwarded `Load`, and a segment's `Store`s may be a split's field stores. -/

/-- A layer: nil-check eliminations (`nilPre`), Load-of-Store forwardings (`fwdPre`; selective ones
leave the rewrites `fwdLate` names), struct-load expansions (`slPre`), struct-store splits
(`ssPre`), value-rule `Load` expansions (`ldPre`), segment rewrites (`segPre`; selective ones leave
those `segLate` names), selections of `Phi`s of `SliceMake`s (`psPre`), constant `Phi`s
(`pcPre`), `Phi`s of `Not`s (`pnPre`). -/
inductive Layer where
  | nil (sel : Bool)
  | fwd (sel : Bool)
  | sl
  | ss
  | ld
  | seg (sel : Bool)
  | ps
  | pc
  | pn

/-- The input with the layer's events of the log applied, and the remaining events. -/
def Layer.pre (t : Interp.Table) (tabs : Tables) : Layer → Func → Array RwEvent →
    Func × Array RwEvent
  | .nil sel => nilPre t tabs sel
  | .fwd sel => fun f log => fwdPre t tabs sel (if sel then fwdLate t f log else []) f log
  | .sl => slPre t tabs
  | .ss => ssPre t tabs
  | .ld => ldPre t tabs
  | .seg sel => segPre t sel
  | .ps => psPre t
  | .pc => pcPre t
  | .pn => pnPre t

/-- The layers of `RewriteCheck.accepts`, in order (a second struct-load layer and a second split
layer for nested structs; the value-rule `Load` expansions and selections of `Make`s and `Load`s
before the splits, which store their results; a struct-load layer after the first split layer
for `Load`s whose memory a split rebased, before the splits of their expansions; a second segment
layer for segments over another's result; selective forwarding rounds after the segments for
forwardings through `Move`s whose sources earlier forwardings changed). A constant `Phi` and a
`Phi` of `Not`s are the first event of their segment, so their layers come first. -/
def layers : List Layer :=
  [.pc, .pn, .ps, .nil true, .fwd true, .sl, .sl, .ld, .ss, .sl, .ss, .ss, .seg true, .seg false,
   .fwd true, .fwd true, .fwd true, .fwd true, .sl, .ss, .fwd false, .nil false]

/-- The layers of the decompose builtin rewrite step (issue #17): its value-rule `Load`
expansions, then its splits (twice, for nested structs). -/
def decLayers : List Layer := [.ld, .ss, .ss]

/-! ## Phi eliminations (issue #69)

`applyRewrite` runs `phielimValue` on every value: a `Phi` whose arguments are all one value `w`
or the `Phi` itself becomes `Copy w`. Its arguments usually became equal through the rewrites
before (`StructSelect` of `StructMake` became copies of the selected argument, then the copies
were eliminated), so the elimination is not a fact about the input. The event
(`RwEvent.phielim v def pre`) logs the function `pre` just before the elimination. `accepts`
splits the log at these events (`segsOK`): each segment is validated (layers and `validate`)
against `pre` without the values reset to `Invalid` (`dropInvalid`; `applyRewrite`'s cleanup
frees them at the end), `pre` and the function with the `Phi` turned copy (`phiElim`) are
related by copyelim's relation (`CopyCheck.copyOK`), and the next segment starts from the
latter. The log is split likewise before every `Phi` selection (`RwEvent.snap pre`): the
selection becomes a copy in the `ps` layer of the next segment, which starts from `pre`, so a
rule logged before it matches the selection, not the copy; and before the nil-check eliminations
of `IsNonNil`s and `Convert`s, the fixed loads (`Interp.snapRule`) and the forwardings of `Load`s
not in the pass's input (`Interp.builtLoad`), whose matched values earlier rewrites built (the
layers of the next segment find them in `pre`). -/

/-- `h` without the `Invalid` values listed in its blocks. -/
def dropInvalid (h : Func) : Func :=
  h.blocks.foldl (init := h) fun h b =>
    h.modB b fun x => { x with values := x.values.filter fun y => (h.value? y).all (·.op != .Invalid) }

/-- `phielimValue`'s edit: the `Phi` `v` of `h` becomes `Copy w`. -/
def phiElim (h : Func) (v w : ID) : Func :=
  (h.modV v fun y => { y with op := .Copy }).setArgs1 v w

/-- The event is no segment boundary: no phi elimination, no snapshot. -/
def notPhiElim : RwEvent → Bool
  | .phielim .. | .snap .. => false
  | _ => true

/-- No segment boundary in the log. -/
def noPhiElim (log : Array RwEvent) : Bool := log.all notPhiElim

end GoFV.Opt.RewriteCheck

namespace GoFV.Opt

/-- The nil-check eliminations of a layer, applied to `f` (`f'`), are nilcheckelim's
(`NilCheck.nrel true` in the result's tables `tabs`: each pointer is a `safePtr true` seed, the
other roots keep their order), `f'` passes `check`, and `f`'s dictionary parameters are those of
the pass's input `f0` in the pass's tables (the precondition `Sem.DictArgs` is stated there). -/
def RewriteCheck.nilOK (env : PassEnv) (tabs : GoFV.SSA.Tables) (f0 f f' : GoFV.SSA.Func) : Bool :=
  NilCheck.nrel true tabs f f' && checkOK { tabs := tabs, typs := env.typs } f' &&
    NilCheck.dictParams tabs f == NilCheck.dictParams env.tables f0

/-- The layer `L` relates `f` (a layer's input with the log `log`, from the pass's input `f0`)
and `f'`: `nilOK`, `fwdRel` (with the precondition's read-only symbols, `roPass`, and descriptor
symbols, `eqPass`), `validate` with the expansions it applied (`slTaken`, `ldTaken`), `ssRel`,
`segRel` with its read-only segments' symbols among the precondition's (`roSegsOK`, `roPass`),
`psRel`, `pcRel` or `pnRel`, and `f'` passes `check`. -/
def RewriteCheck.layerOK (env : PassEnv) (t : GoFV.Rules.Interp.Table) (tabs : GoFV.SSA.Tables)
    (f0 : GoFV.SSA.Func) :
    RewriteCheck.Layer → GoFV.SSA.Func → Array GoFV.Rules.RwEvent → GoFV.SSA.Func → Bool
  | .nil _, f, _, f' => RewriteCheck.nilOK env tabs f0 f f'
  | .fwd _, f, _, f' =>
    RewriteCheck.fwdRel tabs (RewriteCheck.roPass env.tables env.frontend f0)
        (RewriteCheck.eqPass env.tables env.frontend) f f' &&
      RewriteCheck.fwdRoOK tabs (RewriteCheck.roPass env.tables env.frontend f0) f &&
      checkOK { tabs := tabs, typs := env.typs } f'
  | .sl, f, log, f' =>
    RewriteCheck.validate tabs t f f' (RewriteCheck.slTaken t tabs f log) &&
      checkOK { tabs := tabs, typs := env.typs } f'
  | .ss, f, _, f' => RewriteCheck.ssRel tabs f f' && checkOK { tabs := tabs, typs := env.typs } f'
  | .seg _, f, _, f' =>
    RewriteCheck.segRel tabs f f' &&
      RewriteCheck.roSegsOK tabs (RewriteCheck.roPass env.tables env.frontend f0) f f' &&
      checkOK { tabs := tabs, typs := env.typs } f'
  | .ps, f, _, f' =>
    RewriteCheck.psRel tabs f f' && checkOK { tabs := tabs, typs := env.typs } f'
  | .pc, f, _, f' =>
    RewriteCheck.pcRel tabs f f' && checkOK { tabs := tabs, typs := env.typs } f'
  | .pn, f, _, f' =>
    RewriteCheck.pnRel tabs f f' && checkOK { tabs := tabs, typs := env.typs } f'
  | .ld, f, log, f' =>
    RewriteCheck.validate tabs t f f' (RewriteCheck.ldTaken t tabs f log) &&
      checkOK { tabs := tabs, typs := env.typs } f'

/-- Two log events of the same kind at the same value (block) and index (rule, argument, source):
a layer that takes no event leaves every event in place. -/
def RewriteCheck.evSame : GoFV.Rules.RwEvent → GoFV.Rules.RwEvent → Bool
  | .rule v i _ _, .rule v' i' _ _ => v == v' && i == i'
  | .copyArg v i s, .copyArg v' i' s' => v == v' && i == i' && s == s'
  | .control b i c, .control b' i' c' => b == b' && i == i' && c == c'
  | .phielim v _ _, .phielim v' _ _ => v == v'
  | .blockRule b i _ _, .blockRule b' i' _ _ => b == b' && i == i'
  | .snap _, .snap _ => true
  | _, _ => false

/-- The logs `a` and `b` have the same events (`evSame`) in the same order. -/
def RewriteCheck.sameLog : List GoFV.Rules.RwEvent → List GoFV.Rules.RwEvent → Bool
  | [], [] => true
  | x :: xs, y :: ys => RewriteCheck.evSame x y && RewriteCheck.sameLog xs ys
  | _, _ => false

/-- The layers `Ls` take their events out of the log, each a step `layerOK` accepts (a layer
that leaves the log as it is, `sameLog`, is skipped; a struct-load expansion whose `Load`'s
memory copy elimination replaced keeps the log's size), and `validate` accepts `out` against the
last function and the remaining events. -/
def RewriteCheck.layersOK (env : PassEnv) (t : GoFV.Rules.Interp.Table) (f0 : GoFV.SSA.Func)
    (out : PassOut) : List RewriteCheck.Layer → GoFV.SSA.Func → Array GoFV.Rules.RwEvent → Bool
  | [], f, log => RewriteCheck.validate out.tables t f out.func log
  | L :: Ls, f, log =>
    match L.pre t out.tables f log with
    | (f', log') =>
      if RewriteCheck.sameLog log'.toList log.toList then RewriteCheck.layersOK env t f0 out Ls f log
      else RewriteCheck.layerOK env t out.tables f0 L f log f' &&
        RewriteCheck.layersOK env t f0 out Ls f' log'

/-- The segments of the log between its phi eliminations and snapshots (`seg`: the events of the
current one, from `f`): `layersOK` accepts each against the function logged at the event ending
it (without `Invalid` values, `h`), which passes `check`; at a phi elimination `h` is related by
copyelim's relation to `h` with the `Phi` turned copy (`h'`, which passes `check`), where the
next segment starts, at a snapshot the next segment starts from `h`; the last segment ends at
`out`. -/
def RewriteCheck.segsOK (env : PassEnv) (t : GoFV.Rules.Interp.Table) (f0 : GoFV.SSA.Func)
    (out : PassOut) : GoFV.SSA.Func → Array GoFV.Rules.RwEvent → List GoFV.Rules.RwEvent → Bool
  | f, seg, [] => RewriteCheck.layersOK env t f0 out RewriteCheck.layers f seg
  | f, seg, .phielim v d pre :: evs =>
    let ce : GoFV.SSA.CheckEnv := { tabs := out.tables, typs := env.typs }
    let h := RewriteCheck.dropInvalid pre
    let h' := RewriteCheck.phiElim h v d.args[0]!
    RewriteCheck.layersOK env t f0 { out with func := h } RewriteCheck.layers f seg &&
      checkOK ce h && CopyCheck.copyOK out.tables h h' && checkOK ce h' &&
      RewriteCheck.segsOK env t f0 out h' #[] evs
  | f, seg, .snap pre :: evs =>
    let h := RewriteCheck.dropInvalid pre
    RewriteCheck.layersOK env t f0 { out with func := h } RewriteCheck.layers f seg &&
      checkOK { tabs := out.tables, typs := env.typs } h &&
      RewriteCheck.segsOK env t f0 out h #[] evs
  | f, seg, ev :: evs => RewriteCheck.segsOK env t f0 out f (seg.push ev) evs

/-- `checkedRewrite` keeps the rewrite result `out` of `f` (input environment `env`, rewrite
log `log`): `f` cannot tell the result's tables from the input's (`tabsAgree`: rules create
types such as `ConstNil <v.Type.Elem().PtrTo()>` and symbols such as `fe.StringData(s)`, but no
definitions the input looks up), and `RewriteCheck.segsOK` accepts it in the result's tables:
between phi eliminations, `RewriteCheck.layersOK` through the `RewriteCheck.layers`. -/
def RewriteCheck.accepts (env : PassEnv) (t : GoFV.Rules.Interp.Table)
    (f : GoFV.SSA.Func) (out : PassOut) (log : Array GoFV.Rules.RwEvent) : Bool :=
  tabsAgree env.tables out.tables f && RewriteCheck.segsOK env t f out f #[] log.toList

/-- `applyRewrite` with the table `t` and its log; the result if `RewriteCheck.accepts` it. -/
def checkedRun (t : GoFV.Rules.Interp.Table) (env : PassEnv) (f : GoFV.SSA.Func) :
    Except String (Option PassOut) := do
  let (out, _, log) ← GoFV.Rules.rewriteRun t true true env f
  return if RewriteCheck.accepts env t f out log then some out else none

/-- The tables `checkedRewrite` tries in order: `t`, then (a `Phi` selection, segment rewrite,
Load-of-Store forwarding, struct-store split or nil-check elimination the validator cannot
relate, issues #69, #151) `t` without its `Phi` selections (`phiSels`), then also without its
segment rules (`segs`), then also without its forwardings (`loads`), then also without its
struct-store splits (`structStores`), then also without its nil-check eliminations
(`nilChecks`), each only if it removes rules. -/
def checkedTiers (t : GoFV.Rules.Interp.Table) : List GoFV.Rules.Interp.Table :=
  let tp := { t with phiSels := #[] }
  let t₀ := { tp with segs := #[] }
  let t₁ := { t₀ with loads := #[] }
  let t₂ := { t₁ with structStores := #[] }
  let t₃ := { t₂ with nilChecks := #[] }
  t :: ((if t.phiSels.isEmpty then [] else [tp]) ++ (if t.segs.isEmpty then [] else [t₀]) ++
    (if t.loads.isEmpty then [] else [t₁]) ++ (if t.structStores.isEmpty then [] else [t₂]) ++
    (if t.nilChecks.isEmpty then [] else [t₃]))

/-- The first of the tables whose run `checkedRun` accepts, and its result. -/
def checkedFirst (env : PassEnv) (f : GoFV.SSA.Func) :
    List GoFV.Rules.Interp.Table → Except String (Option PassOut)
  | [] => pure none
  | T :: Ts => do
    match ← checkedRun T env f with
    | some out => pure (some out)
    | none => checkedFirst env f Ts

/-- The validated rewrite pass: `applyRewrite` with the first table of `checkedTiers t` whose
result (with the pass's extended tables) `RewriteCheck.accepts`, else the input. -/
def checkedRewrite (t : GoFV.Rules.Interp.Table) : Pass := fun env f => do
  match ← checkedFirst env f (checkedTiers t) with
  | some out => return out
  | none => return { func := f, tables := env.tables }

end GoFV.Opt
