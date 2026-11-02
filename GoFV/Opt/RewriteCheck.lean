import GoFV.Proof.Rules.AllSound
import GoFV.Rules.Run
import GoFV.Opt.CSE
import GoFV.Opt.TabsAgree
import GoFV.Opt.NilCheckRel
import GoFV.Opt.Checked
import GoFV.Opt.CopyRelCheck
import GoFV.Opt.MemCall
import GoFV.Opt.MemTy
import GoFV.SSA.Sem.Image

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
  x.Args[i]`) is first checked per instance (`makeSelOK`), else as a rule instance (`ruleOK`);
* a rule event of an unconditional selection of a `Load` with an `@b` result
  (`GoFV.Proof.Rules.loadSelShape`, issue #17, `dec.rules:132`, `:141`) is checked per instance
  only (`loadSelOK`);
* a phi elimination rejects;
* finally every value listed in the output `g` has the replayed definition up to copies:
  each argument (and each control of `g`) is the replayed one or reached from it through
  `Copy`s of the same shape (`copyReach`), which is how copy elimination and `copySource`'s
  path compression rewrite arguments; every block of `g` has its replayed terminator (kind,
  successors in the replayed order, controls up to copies).

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
whose constant has the shape `ty`; their value depends on nothing but the op. -/
def constTop (op : Op) (ty : Sem.Ty) : Bool :=
  (op matches .ConstNil | .ConstSlice | .ConstInterface) &&
    (Sem.evalPure op ty 0 none []).hasTy ty

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

/-- Shapes a `Load` decodes to a value of the shape: scalars and aggregates of scalars (strings,
slices, interfaces, complex numbers; issue #17). -/
def loadShape (t : Sem.Ty) : Bool :=
  match t.asAgg with
  | .agg fs _ => fs.all (scalarTy ·.2)
  | t => scalarTy t

/-- A `Load` at a `loadShape`. -/
def loadTop (op : Op) (ty : Sem.Ty) : Bool := op == .Load && loadShape ty

/-- The top op of a match at the instance `e` produces a value of its type's shape: `topOK`, a
selection from its first argument (`selTop`), or a `Load` (`loadTop`). -/
def topAll (op : Op) (e : PEnv) : Bool :=
  topOK op (e.ty []) || selTop op (e.ty []) (e.auxInt []) (e.ty [0]) || loadTop op (e.ty [])

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

/-- The value a result argument refers to. -/
def argID (σ : Nat → DV) (I : Inst) (ids : List ID) : RArg → Option ID
  | .var x => (DV.pos? (σ x)).map I.at
  | .node j => ids[j]?

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
`x.NumElem() == 1` have a type `x` of the shape of one field at offset 0 that fills it, and the
positions `same` (`GoFV.Proof.Rules.sameLeaves`) match the same value
(`GoFV.Proof.Rules.FrameOK`). -/
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
      | some (.const w) => ((Sem.Conv.const w v.auxInt).retype ty).nonNeg
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
        let σ := sigmaT tabs e r.pat
        let nodes := match r.result, defs with
          | .build ns, _ :: us => ns.zip us
          | _, _ => []
        let or := oracle vtys tabs nodes
        let ev := evalE vtys σ or e (Pat.denT tabs e [] r.pat)
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
(`shapeSub`), or when it is a 64-bit integer word (`intWord`: a 64-bit integer or a pointer
without a concrete address, which every word shape keeps, §3.3; e.g. the interface's `uintptr`
itab word read by a pointer-typed `ITab`, or an itab `Addr {go:itab.…}` typed `*uint8`); without
a field `k` the selection is `poison`. -/

/-- A 64-bit integer or pointer shape: `retype` at it keeps a 64-bit integer and a pointer
without a concrete address. -/
def wordTy : Sem.Ty → Bool
  | .int .w64 | .ptr _ => true
  | _ => false

/-- `a` denotes a 64-bit integer word in `M`, within `n` steps: a 64-bit integer, a pointer
without a concrete address, or `poison` (`Val.hasTy _ (.int .w64)`). It has the 64-bit integer
shape, is an `Addr` (a global), or is a `Convert`/`Copy` at a word shape of such a value
(`Convert` integer → pointer is the identity). -/
def intWord (tabs : Tables) (M : Defs) : Nat → ID → Bool
  | 0, _ => false
  | n + 1, a =>
    match M.get? a with
    | some w =>
      (tabs.ty w.type matches .int .w64) || w.op == .Addr ||
        ((w.op == .Convert || w.op == .Copy) && wordTy (tabs.ty w.type) &&
          match w.args[0]? with
          | some x => intWord tabs M n x
          | none => false)
    | none => false

/-- `copyReach`, or first a `Copy` at a word shape of a 64-bit integer word (`intWord`: the
identity on its argument's value) and then `copyReach` from its argument: the `Copy <uintptr>` of
an `Addr <*uint8>` a phi elimination leaves (issue #17), whose shapes `copyCompat` does not
relate. -/
def copyReachW (tabs : Tables) (M : Defs) (n : Nat) (a w : ID) : Bool :=
  copyReach tabs M n a w ||
    match M.get? a with
    | some x => x.op == .Copy && x.args.size == 1 && wordTy (tabs.ty x.type) &&
        intWord tabs M 4 x.args[0]! && copyReach tabs M n x.args[0]! w
    | none => false

/-- The event `(v, defs)` selects an argument of a `Make`: `v` is a selection of component `k`
(`selIndex?`) of `s` in `M`, `s` a `Make` whose argument `k` is a defined value `a`, `defs` is
`v` as `Copy a` at `a`'s type (`copyOf`), and where the `Make`'s shape has a component `k`, `a`'s
shape is that component's and `v`'s (`shapeSub`), or `a` is a 64-bit integer word (`intWord`)
and both are word shapes (`wordTy`). -/
def makeSelOK (tabs : Tables) (M : Defs) (v : ID) (defs : List Value) : Bool :=
  match M.get? v, defs with
  | some x, [u] =>
    match x.args.toList, selIndex? x.op x.auxInt with
    | [s], some k =>
      match M.get? s with
      | some y =>
        match y.args[k]? with
        | some a =>
          match M.get? a with
          | some w =>
            makeOp y.op && u.id == v && u.op == .Copy && u.args == #[a] && u.type == w.type &&
            (match fieldShape? (tabs.ty y.type) k with
              | some fk =>
                (shapeSub (tabs.ty w.type) fk && shapeSub (tabs.ty w.type) (tabs.ty x.type)) ||
                (intWord tabs M 4 a && wordTy fk && wordTy (tabs.ty x.type))
              | none => true)
          | none => false
        | none => false
      | none => false
    | _, _ => false
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

/-- Replay the log on the definitions `M` and the terminators `B`, starting from `f`'s; `none`
if an event is not validated. An event of a dropped rule (`dropShape`) and a copy-argument
replacement the copies of `M` do not justify are skipped: `M` keeps its definition, and
`finalOK` accepts the output only where that value is no longer read (issue #17). A selection of
a `Make` (`makeSelOK`) is accepted from any rule. -/
def replay (tabs : Tables) (t : Interp.Table) (f : Func) :
    Defs → BMap → List RwEvent → Option (Defs × BMap)
  | M, B, [] => some (M, B)
  | M, B, .rule v i _ defs :: evs =>
    match M.get? v with
    | none => none
    | some x =>
      match (t.values[x.op.ctorIdx]?).bind (·[i]?) with
      | none =>
        if structLoadOK tabs M v defs.toList then
          replay tabs t f (defs.foldl (fun M u => M.put u.id u) M) B evs
        else none
      | some cr =>
        if makeSelOK tabs M v defs.toList then
          replay tabs t f (defs.foldl (fun M u => M.put u.id u) M) B evs
        else if dropShape cr.rule then replay tabs t f M B evs
        else if loadSelShape cr.rule then
          if loadSelOK tabs M v defs.toList then
            replay tabs t f (defs.foldl (fun M u => M.put u.id u) M) B evs
          else none
        else if ruleOK tabs M cr.rule v defs.toList then
          replay tabs t f (defs.foldl (fun M u => M.put u.id u) M) B evs
        else none
  | M, B, .copyArg v i src :: evs =>
    match M.get? v with
    | none => none
    | some x =>
      if h : i < x.args.size then
        if copyReachW tabs M M.size x.args[i] src then
          replay tabs t f (M.put v { x with args := x.args.set i src }) B evs
        else replay tabs t f M B evs
      else none
  | M, B, .control b i c :: evs =>
    match bstate f B b with
    | none => none
    | some st =>
      if h : i < st.ctrls.size then
        if copyReach tabs M M.size st.ctrls[i] c then
          replay tabs t f M ((b, { st with ctrls := st.ctrls.set i c }) :: B) evs
        else none
      else none
  | _, _, .phielim .. :: _ => none
  | _, _, .snap .. :: _ => none
  | M, B, .blockRule b i nc :: evs =>
    match bstate f B b with
    | none => none
    | some st =>
      if ((f.block? b).map (·.succs.size)) != some 2 then none else
      match (t.blocks[st.kind.ctorIdx]?).bind (·[i]?) with
      | none => none
      | some br =>
        match blockOK tabs M br st nc with
        | none => none
        | some (defs, st') => replay tabs t f (defs.foldl (fun M u => M.put u.id u) M) ((b, st') :: B) evs

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
`Zero` (which never panic). -/
def atomsXOK (f g : Func) : Bool :=
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
            !rootB f x || rootB g x || (f.value? x).any fun u => u.op == .Store || u.op == .Zero
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

/-- `x` is read in `h`: a control of a block of `h`, or an argument of a value listed in one. -/
def readIn (h : Func) (x : ID) : Bool :=
  h.blocks.any fun b => (h.block? b).any fun hb =>
    hb.controls.contains x || hb.values.any fun y => (h.value? y).any fun u => u.args.contains x

/-- Every value listed in `g` has its replayed definition, up to copies in its arguments, or is a
term that nothing in `g` reads (`readIn`; the replay kept the input's definition of a dropped
rule's value, issue #17), and every block of `g` its replayed terminator (`bstate`): the kind,
the successors (swapped if the replay swapped them, then from two), the controls up to copies. -/
def finalOK (tabs : Tables) (f g : Func) (M : Defs) (B : BMap) : Bool :=
  let n := M.size
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
          (termOp u.op && !readIn g x)
        | _, _ => false
    | _, _, _ => false

/-- **The validator**: `g` (the result of the rewrite pass with table `t` on `f`, which logged
`log`) is related to `f` as the theorems need. -/
def validate (tabs : Tables) (t : Interp.Table) (f g : Func) (log : Array RwEvent) : Bool :=
  atomsOK f g && closedOK f && closedOK g &&
  match replay tabs t f f.valueTab [] log.toList with
  | some (M, B) => finalOK tabs f g M B
  | none => false

/-! ## Nil-check eliminations (issue #151)

A rule of the table's `nilChecks` row, `(NilCheck x:(Op …) _) => x`, turns a root (a nil check)
into a term (`Copy x`). The validator takes these events out of the log: `nilPre` applies them to
the input (`NilCheck p mem` → `Copy p`, as `v.reset(OpCopy)`), the checked pass relates input
and `nilPre` by nilcheckelim's checker (`NilCheck.nrel`: `p` is a `safePtr` seed, so the check
cannot panic, and the other roots keep their order), and `validate` relates `nilPre` and the
output with the remaining events. -/

/-- A nil-check elimination `(NilCheck x:(Op …) _) => x` whose pointer op nilcheckelim's
checker can justify by itself (`NilCheck.safePtr true`: `Addr`, `LocalAddr`, `NilCheck`, `GetG`,
`OffPtr` of such a pointer, the `SelectN [0]` of a malloc-family call, a dictionary `Arg`). -/
def nilElimOK (r : Rule) : Bool :=
  match r.pat, r.result with
  | .op .NilCheck none _ _ _ .fixed [.op o (some x) _ _ _ _ _ _, _] _, .copy (.var y) =>
    x == y && (o matches .Addr | .LocalAddr | .NilCheck | .GetG | .OffPtr | .SelectN | .Arg)
  | _, _ => false

/-- The nil check `v` of `f` that event `ev` eliminates, if it is a `nilChecks` rule event
(`nilElimOK`). -/
def nilEvent? (t : Interp.Table) (f : Func) : RwEvent → Option ID
  | .rule v i _ _ =>
    match f.value? v with
    | some x =>
      if x.op == .NilCheck then
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
other arguments lose a use. -/
def nilCopy (f : Func) (v : ID) : Func :=
  match f.value? v with
  | some x =>
    if x.op == .NilCheck && 0 < x.args.size then
      let f := (x.args.extract 1 x.args.size).foldl (fun f a => f.modV a fun u => { u with uses := u.uses - 1 }) f
      f.modV v fun u => { u with op := .Copy, auxInt := 0, aux := none, args := #[x.args[0]!] }
    else f
  | none => f

/-- The nil check `v` of `f` checks a pointer nilcheckelim's checker takes as non-nil by itself
(`NilCheck.safePtr true`). -/
def nilSafe (tabs : Tables) (f : Func) (v : ID) : Bool :=
  match f.value? v with
  | some x =>
    match x.args[0]? with
    | some p => NilCheck.safePtr true tabs f f.valueTab.size p
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

/-- The value of `a` if it is a constant term of `f` at most `k` deep: a term node (`termOp`)
whose arguments are constant terms, evaluated as the semantics evaluates it (`Rules.opVal` at its
value's shape, retyped), e.g. `Mul64 (StringLen (ConstString {s})) (Const64 [1])`, which value
rules fold to a `Const64` only later in the log. -/
def termConst (tabs : Tables) (f : Func) : Nat → ID → Option Sem.Val
  | 0, _ => none
  | k + 1, a =>
    match f.value? a with
    | some v =>
      if termOp v.op then
        (v.args.toList.mapM (termConst tabs f k)).map fun cs =>
          (GoFV.Proof.Rules.opVal tabs v.op (tabs.ty v.type) v.auxInt v.aux cs).retype
            (tabs.ty v.type)
      else none
    | none => none

/-- A constant index: a constant term (`termConst`, at most four deep) of the 64-bit integer
shape, its value; e.g. `Div64 (Sub64 (Const64 [32]) (Const64 [1])) (Const64 [32])`, which value
rules fold to a `Const64` only later in the log. -/
def constIdx? (tabs : Tables) (f : Func) (i : ID) : Option (BitVec 64) :=
  match termConst tabs f 4 i with
  | some (.int .w64 k) => some k
  | _ => none

/-- One step of `ptrBase`: an `OffPtr` or `Copy` of pointer shape on a pointer-shaped argument,
or a `PtrIndex` of element size `e` (its pointer shape) by a constant index `k` (`constIdx?`),
its argument and its offset (`k * e`). -/
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
    else none
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
`Sem.frameVal`, `AtomSim.MemAtoms`) or a pointer-shaped `Addr`'s global (`Sem.addrVal`). -/
def baseBlk? (tabs : Tables) (f : Func) (a : ID) : Option Sem.Blk :=
  match f.value? a with
  | some u =>
    if u.op == .LocalAddr && isPtrTy (tabs.ty u.type) then u.aux.map (Sem.frameBlk tabs 0)
    else if u.op == .Addr && isPtrTy (tabs.ty u.type) then
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

/-- Pointer `a` (`n` bytes) and pointer `b` (`k` bytes) address disjoint bytes where both are
pointers (`disjoint`): equal bases (`baseSameB`) at separate offsets (`offSep`), or bases in
different allocations (`baseBlk?`). -/
def disjointB (tabs : Tables) (f : Func) (a : ID) (n : Nat) (b : ID) (k : Nat) : Bool :=
  (offSep (ptrBase tabs f 8 a).2 n (ptrBase tabs f 8 b).2 k &&
    baseSameB tabs f 8 (ptrBase tabs f 8 a).1 (ptrBase tabs f 8 b).1) ||
  match baseBlk? tabs f (ptrBase tabs f 8 a).1, baseBlk? tabs f (ptrBase tabs f 8 b).1 with
  | some x, some y => x != y
  | _, _ => false

/-- Fields of `scalarTy` shapes at increasing offsets from `lo` that do not overlap and end
inside `n` bytes. -/
def fwdFields (n lo : Nat) : List (Nat × Sem.Ty) → Bool
  | [] => true
  | (o, t) :: fs => scalarTy t && decide (lo ≤ o) && decide (o + t.size ≤ n) &&
      fwdFields n (o + t.size) fs

/-- A non-empty aggregate of `fwdFields` (strings, slices, interfaces, flat structs; strings
and slices by their aggregate layout `Ty.asAgg`). -/
def fwdAgg (t : Sem.Ty) : Bool :=
  match t.asAgg with
  | .agg fs n => n != 0 && fwdFields n 0 fs
  | _ => false

/-- A shape a `Store` writes and a `Load` reads back unchanged (`Sem.encode`,
`Sem.decodeLoad`): `scalarTy`, or `fwdAgg` (which decodes `poison` from a `poison` store). -/
def fwdTy (t : Sem.Ty) : Bool := scalarTy t || fwdAgg t

/-- `scalarTy` shapes that write, read and retype alike: equal up to pointers' element sizes
(`copyCompatibleType`). -/
def fwdScalarEq : Sem.Ty → Sem.Ty → Bool
  | .int w, .int w' => w == w'
  | .bool, .bool => true
  | .ptr _, .ptr _ => true
  | _, _ => false

/-- Fields at equal offsets of `fwdScalarEq` shapes. -/
def fwdFieldsEq : List (Nat × Sem.Ty) → List (Nat × Sem.Ty) → Bool
  | [], [] => true
  | (o, t) :: fs, (o', t') :: fs' => o == o' && fwdScalarEq t t' && fwdFieldsEq fs fs'
  | _, _ => false

/-- `fwdAgg` aggregates of one size with `fwdFieldsEq` fields. -/
def fwdAggEq : Sem.Ty → Sem.Ty → Bool
  | .agg fs n, .agg fs' n' => n == n' && fwdAgg (.agg fs n) && fwdFieldsEq fs fs'
  | .str, .str | .slice _, .slice _ => true
  | _, _ => false

/-- Shapes `fwdTy` that write, read and retype alike: `fwdScalarEq` or `fwdAggEq`. -/
def fwdTyEq (t s : Sem.Ty) : Bool := fwdScalarEq t s || fwdAggEq t s

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

/-- A constant term (`termConst`) whose value is a zero integer, `false` or `poison`
(`isConstZero` but for pointers, floats and composites; whose bytes are `0` or `poison` at every
shape; a `ConstNil` is a pointer, whose bytes are fragments): `Const64 [0]`, `ConstBool [0]`,
`SliceLen (ConstSlice)`, … -/
def zeroConst (tabs : Tables) (f : Func) (x : ID) : Bool :=
  match termConst tabs f 4 x with
  | some .poison | some (.bool false) => true
  | some (.int _ c) => c == 0
  | _ => false

/-- Memory `m` of `f` holds zero bytes at the `n` bytes at pointer `p`: through at most `d`
`Copy`s and `Store`s at pointers disjoint from them (`disjointB`), a `Zero [k] q _` with `p` at
offset `o` of `q` (`ptrBase`, `baseSameB`) and `o + n ≤ k`. -/
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
        baseSameB tabs f 8 (ptrBase tabs f 8 p).1 (ptrBase tabs f 8 s.args[0]!).1)
    | none => false

/-- The memory root `u` of `f` becomes `w`, a `Copy` of its memory (reached from `u`'s memory
argument through compatible copies, `copyReach`: copy elimination ran before the rule matched),
as its write changes no byte (`generic.rules:1005`, `:943`, `:948`, `:954`, `:961`, `:2158`): a
`Store` of zero bytes (of a zero-sized type), a `Store` of a `zeroConst` into bytes a `Zero`
cleared (`zeroChain` through at most eight `Copy`s and `Store`s), or a `Zero` of a `Zero` of the
same size at an equal pointer (`samePtrB`). -/
def dropOK (tabs : Tables) (f : Func) (u w : Value) : Bool :=
  w.op == .Copy && w.args.size == 1 &&
  ((u.op == .Store && u.args.size == 3 &&
    copyReach tabs f.valueTab f.valueTab.size u.args[2]! w.args[0]! &&
    ((Sem.auxTy tabs u.aux).size == 0 ||
      (zeroConst tabs f u.args[1]! &&
        zeroChain tabs f u.args[0]! (Sem.auxTy tabs u.aux).size 8 u.args[2]!))) ||
   (u.op == .Zero && u.args.size == 2 &&
    copyReach tabs f.valueTab f.valueTab.size u.args[1]! w.args[0]! &&
    match f.value? w.args[0]! with
    | some z => z.op == .Zero && z.args.size == 2 && z.auxInt == u.auxInt &&
        samePtrB tabs f u.args[0]! z.args[0]!
    | none => false))

/-- The inner `Move` `im` of a changed `Move` source (`moveSrcOK`): of `u`'s size, its
destination equal to `u`'s source (`samePtrB`), its source reaching `w`'s through compatible
copies and disjoint from its destination (`disjointB`); under a `VarDef` of the frame variable
`B` (`some B`), its source in a known allocation other than `B` (`baseBlk?`). -/
def moveInnerOK (tabs : Tables) (f : Func) (u w im : Value) (B : Option Sem.Blk) : Bool :=
  im.op == .Move && im.args.size == 3 && im.auxInt == u.auxInt &&
  samePtrB tabs f u.args[1]! im.args[0]! &&
  copyReach tabs f.valueTab f.valueTab.size im.args[1]! w.args[1]! &&
  disjointB tabs f im.args[1]! u.auxInt.toInt.toNat im.args[0]! u.auxInt.toInt.toNat &&
  match B with
  | none => true
  | some b => (baseBlk? tabs f (ptrBase tabs f 8 im.args[1]!).1).any (· != b)

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

/-- The new definition `w` of the `Load` `u` of `f`: `Copy x` of the value `x` it reads back
(`fwdOK`), or a constant of the bits it reads back (`fwdConstOK`); or of the memory root `u`, a
`Copy` of its memory (`dropOK`), or a `Move` from another source (`moveSrcOK`). -/
def fwdNewOK (tabs : Tables) (f : Func) (u w : Value) : Bool :=
  (w.op == .Copy && w.args.size == 1 && fwdOK tabs f u (w.args[0]?.getD 0)) || fwdConstOK tabs f u w ||
    dropOK tabs f u w || moveSrcOK tabs f u w

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

/-- `y` is listed in `g` (`Proof.listedDefs`): a value of a block of `g` that lists it. -/
def listedB (g : Func) (y : ID) : Bool :=
  (g.value? y).any fun v => g.blocks.contains v.block && (g.block? v.block).any (·.values.contains y)

/-- The new definition `w` of the `Load` `u` of `f` in `g`: `Copy y` of the listed `Load` `y` of
`g` through the listed `OffPtr` of the `Move`'s source that `fwdMoveOK` accepts. -/
def fwdMoveRep (tabs : Tables) (f g : Func) (u w : Value) : Bool :=
  w.op == .Copy && w.args.size == 1 && listedB g w.args[0]! &&
  match g.value? w.args[0]! with
  | some top =>
    top.args.size == 2 && listedB g top.args[0]! &&
    match g.value? top.args[0]! with
    | some offp => fwdMoveOK tabs f u top offp
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
`fwdNewOK` or `fwdMoveRep` accepts. -/
def fwdRepOK (tabs : Tables) (f g : Func) (x : ID) : Bool :=
  match f.value? x, g.value? x with
  | none, _ => true
  | some _, none => false
  | some u, some w =>
    w.id == u.id && w.block == u.block && w.type == u.type &&
    ((w.op == u.op && w.auxInt == u.auxInt && w.aux == u.aux && w.args == u.args) ||
     fwdNewOK tabs f u w || fwdMoveRep tabs f g u w)

/-- `g`'s blocks are `f`'s, but for values appended to their lists (the fresh values of a
forwarding through a `Move`, `fwdMoveRep`). -/
def blocksExtOK (f g : Func) : Bool :=
  g.blocks == f.blocks && f.blocks.all fun b =>
    match f.block? b, g.block? b with
    | some fb, some gb => gb == { fb with values := gb.values } && fb.values.all (gb.values.contains ·)
    | _, _ => false

/-- `g` is `f` with Loads forwarded and identity writes dropped: the same blocks (`blocksExtOK`)
and atoms but the dropped roots (`atomsXOK`), every value as `fwdRepOK` says, ranks ordering
`f`'s listed values after their arguments. -/
def fwdRel (tabs : Tables) (f g : Func) : Bool :=
  atomsXOK f g && closedOK f && closedOK g && blocksExtOK f g &&
  fwdRankOK f (fwdRank f) && (List.range f.valueTab.size).all (fwdRepOK tabs f g ·)

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

/-- A Load-of-Store forwarding rule: `(Load _ m) => x` with `x` stored by one of the up to four
`Store`s of the chain `m` (`generic.rules:800`, `:806`, `:813`, `:821`),
`(Load _ (Store _ (Const64 [x]) _)) => (Const64F [x'])` and its converse (`:830`, `:832`), or
`(Load (OffPtr [o] _) (Move _ src mem)) => @move.Block (Load (OffPtr [o] src) mem)` (`:827`); or
a dropped identity write `(Store _ _ mem) => mem`, `(Zero _ mem) => mem` (`:1005`, `:943`,
`:948`, `:954`, `:961`, `:2158`); or a changed `Move` source `(Move dst tmp m:(Move tmp' src _))
=> (Move dst src m)` and its form through a `VarDef` (`:2146`, `:2155`); the validator checks
each instance by `fwdNewOK` or `fwdMoveOK`, the `isSamePtr`/`disjoint` conditions included. -/
def fwdShapeOK (r : Rule) : Bool :=
  match r.pat, r.result, r.block with
  | .op .Load none _ _ _ .fixed [_, m] _, .copy (.var y), none => storesBind y 4 m
  | .op .Load none _ _ _ .fixed [_, .op .Store none _ _ _ .fixed [_, .op o none _ _ _ .fixed [] _, _] _]
      _, .build [n], none => const64Op o && const64Op n.op && n.args.isEmpty
  | .op .Load none _ _ _ .fixed [.op .OffPtr .., .op .Move ..] _, .build [n0, n1], some _ =>
    n0.op == .Load && n1.op == .OffPtr
  | .op .Store none _ _ _ .fixed [_, _, m] _, .copy (.var y), none => patBinds y m
  | .op .Zero none _ _ _ .fixed [_, m] _, .copy (.var y), none => patBinds y m
  | .op .Move none _ _ _ .fixed [_, _, .op .Move ..] _, .build [n], none => n.op == .Move
  | .op .Move none _ _ _ .fixed [_, _, .op .VarDef _ _ _ _ .fixed [.op .Move ..] _] _, .build [n],
      none => n.op == .Move
  | _, _, _ => false

/-- The `Load` `v` of `f` that event `ev` forwards (or the `Store`/`Zero` it drops, or the `Move`
whose source it changes), its new definition (a `Copy`, a constant or a `Move`) and the fresh
values to put in first (`:827`: the `OffPtr`, then the `Load`), if it is a `loads` rule event
(`fwdShapeOK`; tried on a `Store` after its `structStores`, `Interp.rewriteValue`). -/
def fwdEvent? (t : Interp.Table) (f : Func) : RwEvent → Option (ID × Value × List Value)
  | .rule v i _ defs =>
    match f.value? v with
    | some u =>
      if u.op == .Load || u.op == .Store || u.op == .Zero || u.op == .Move then
        let n := ((t.values[u.op.ctorIdx]?).map (·.size)).getD 0 +
          if u.op == .Store then t.structStores.size else 0
        if n ≤ i then
          match t.loads[i - n]?, defs.toList with
          | some cr, [w, top, offp] =>
            if fwdShapeOK cr.rule && w.op == .Copy && w.args.size == 1 && top.op == .Load then
              some (v, w, [offp, top])
            else none
          | some cr, w :: _ =>
            if fwdShapeOK cr.rule &&
                ((w.op == .Copy && w.args.size == 1) || const64Op w.op || w.op == .Move) then
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
one the validator accepts in `f`: `fwdNewOK`, or `fwdMoveOK` of the fresh `[offp, top]` with `w`
a `Copy` of `top`. -/
def fwdEvOK (tabs : Tables) (f : Func) (u w : Value) : List Value → Bool
  | [] => fwdNewOK tabs f u w
  | [offp, top] =>
    w.args == #[top.id] && top.args[0]! == offp.id && fwdMoveOK tabs f u top offp
  | _ => false

/-- One event of `fwdPre`: a forwarding of `f` is applied (with `sel` only one `fwdEvOK` holds of
in `f`; its fresh values put in first), any other event kept, but for the copy-argument
replacements of the forwarded `Load` logged before it (copy elimination on the `Load`'s
arguments, which the forwarding validated in `f` replaces). -/
def fwdStep (t : Interp.Table) (tabs : Tables) (sel : Bool) (f : Func) (p : Func × Array RwEvent)
    (ev : RwEvent) : Func × Array RwEvent :=
  match fwdEvent? t f ev with
  | some (v, w, ds) =>
    if sel && !(f.value? v).any (fwdEvOK tabs f · w ds) then (p.1, p.2.push ev)
    else (fwdCopy (ds.foldl ssPut p.1) v w, p.2.filter fun | .copyArg z _ _ => z != v | _ => true)
  | none => (p.1, p.2.push ev)

/-- The input with the log's Load-of-Store forwardings applied (with `sel` only those `fwdEvOK`
holds of), and the remaining events. -/
def fwdPre (t : Interp.Table) (tabs : Tables) (sel : Bool) (f : Func) (log : Array RwEvent) :
    Func × Array RwEvent :=
  log.foldl (fwdStep t tabs sel f) (f, #[])

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

/-- One event of `ssPre`: a split of a `Store` of `f` is applied, any other event kept (a split of
a fresh field store of an earlier split, a nested struct, is left to a later layer), but for the
copy-argument replacements of the split `Store` logged before it (copy elimination on its
arguments, which the split validated in `f` through copies replaces). -/
def ssStep (t : Interp.Table) (f : Func) (p : Func × Array RwEvent) (ev : RwEvent) :
    Func × Array RwEvent :=
  match ssEvent? t f ev with
  | some (v, w, ds) => (ssApply p.1 v w ds, p.2.filter fun | .copyArg y _ _ => y != v | _ => true)
  | none => (p.1, p.2.push ev)

/-- The input with the log's struct-store splits of its `Store`s applied, and the remaining
events. -/
def ssPre (t : Interp.Table) (f : Func) (log : Array RwEvent) : Func × Array RwEvent :=
  log.foldl (ssStep t f) (f, #[])

/-- `gv` is `fv` but for its use count. -/
def ssSame (fv gv : Value) : Bool :=
  gv.id == fv.id && gv.op == fv.op && gv.aux == fv.aux && gv.auxInt == fv.auxInt &&
    gv.type == fv.type && gv.block == fv.block && gv.args == fv.args

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

/-- The `Make` argument `a` of `f` (shape `s`) fits its field's shape `t`: the same shape, both
pointer shapes (a pointer keeps its value at every pointer shape), or, in a `uintptr` field (an
interface's itab word), a pointer that is, up to copies, a pointer to a symbol (`Addr`: it has no
concrete address) or a `Convert` at a word shape (`wordTy`) of a 64-bit integer (integer →
pointer is the identity), which keep their value at the 64-bit integer shape. -/
def ssFieldOK (tabs : Tables) (f : Func) (a : ID) (s t : Sem.Ty) : Bool :=
  Sem.Ty.beq s t || (s matches .ptr _ && t matches .ptr _) ||
  (Sem.Ty.beq t (.int .w64) && s matches .ptr _ &&
    (f.value? (copyEnd tabs f.valueTab f.valueTab.size a)).any fun w =>
      w.op == .Addr ||
        (w.op == .Convert && wordTy (tabs.ty w.type) &&
          (w.args[0]?.bind f.value?).any fun x => tabs.ty x.type matches .int .w64))

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
      ssFieldOK tabs f a (tabs.ty av.type) t &&
      ((f.value? s).isNone || (s == x && k + 1 == ps.length)) && sv.id == s && sv.op == .Store &&
      sv.block == b && Sem.Ty.beq (tabs.ty sv.type) .mem &&
      sv.args.size == 3 && sv.args[0]! == p && sv.args[2]! == prev &&
      copyReach tabs f.valueTab f.valueTab.size a sv.args[1]! &&
      Sem.Ty.beq (Sem.auxTy tabs sv.aux) t &&
      ssPtrOK tabs f g b dst p o
    | _, _ => false
  | _, _, _ => false

/-- The memory `m0` a split's chain starts from is the split `Store`'s memory `mem` (in block
`b`): `mem` reaches it through copies in `f`, or `mem` stands through copies for another split
`Store` of `b` with fields (in `g` its `Copy` of `m0`, the last store of its chain). -/
def ssStart (tabs : Tables) (f g : Func) (b mem m0 : ID) : Bool :=
  copyReach tabs f.valueTab f.valueTab.size mem m0 ||
  let y := copyEnd tabs f.valueTab f.valueTab.size mem
  match f.value? y, g.value? y with
  | some yv, some gy =>
    yv.op == .Store && yv.block == b && gy.op == .Copy && gy.args == #[m0] &&
      ((Sem.auxTy tabs yv.aux).asAgg matches .agg (_ :: _) _)
  | _, _ => false

/-- The `Make` ops: `StructMake`, `StringMake`, `SliceMake`, `IMake`, `ComplexMake`,
`ArrayMake1` (`Comp.make`: the aggregate of the arguments). -/
def ssMakeOp : Op → Bool
  | .StructMake | .StringMake | .SliceMake | .IMake | .ComplexMake | .ArrayMake1 => true
  | _ => false

/-- Value `x` of `f` is a split `Store` in `g`: in `f` a `Store` listed in its block at an
aggregate shape `agg fs n` (a string or slice by its layout `Ty.asAgg`; every field inside it,
`layoutsOK`, at an offset below `n`) of a
`Make` (`ssMakeOp`, up to copies, `copyEnd`) of that shape; in `g` `Copy` of the last store of
the chain (`ssWalk`), or (in place) that last store itself, each field linked (`ssLink`), from
the `Store`'s memory (`ssStart`). The chain's pairs. -/
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
            ssStart tabs f g fv.block mem r.2 &&
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

/-- One event of `segPre`: a segment rewrite of a value of `f` is applied, any other event kept,
but for the copy-argument replacements of its anchor and dropped values logged before it. -/
def segStep (t : Interp.Table) (f : Func) (p : Func × Array RwEvent) (ev : RwEvent) :
    Func × Array RwEvent :=
  match segEvent? t f ev with
  | some (v, w, ds) =>
    match f.value? v with
    | some u =>
      let D := segDrops f u w ds
      (segApply p.1 v w ds D,
        p.2.filter fun | .copyArg y _ _ => y != v && !D.contains y | _ => true)
    | none => (p.1, p.2.push ev)
  | none => (p.1, p.2.push ev)

/-- The input with the log's segment rewrites applied, and the remaining events. -/
def segPre (t : Interp.Table) (f : Func) (log : Array RwEvent) : Func × Array RwEvent :=
  log.foldl (segStep t f) (f, #[])

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

/-- `a` is a constant term of `f` (`termConst`, at most 4 deep) whose value is the 64-bit
integer `n ≥ 0`. -/
def constSize (tabs : Tables) (f : Func) (a : ID) (n : Int64) : Bool :=
  decide (0 ≤ n.toInt) &&
    match termConst tabs f 4 a with
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

/-- Value `x` of `f` is a segment's anchor in `g` (`chainSeg?`, `callSeg?` or `roSeg?`): listed in
its block, a `Store`, `SelectN` or `Move` redefined in place (its ID, block and type kept); its
dropped values are listed in that block, its fresh values in that block of `g`; the fresh values
and the anchor are roots of `g`, each of their arguments an earlier one of them, or an argument of
a root of `f` of the segment (a dropped root, or the anchor) that is not dropped. The dropped and
fresh values. -/
def segOK (tabs : Tables) (f g : Func) (x : ID) : Option (List ID × List ID) :=
  match f.value? x, g.value? x with
  | some fv, some gv =>
    let listed (z : ID) : Bool := (f.block? fv.block).any (·.values.contains z)
    if !ssSame fv gv && gv.id == x && gv.block == fv.block && gv.type == fv.type &&
        (fv.op == .Store || fv.op == .SelectN || fv.op == .Move) && f.blocks.contains fv.block &&
        listed x then
      match ((chainSeg? tabs f g x fv gv).orElse fun _ => callSeg? tabs f g fv gv).orElse
          fun _ => roSeg? tabs f fv gv with
      | some (D, N) =>
        let L := N ++ [x]
        let ext (a : ID) : Bool := !D.contains a && !L.contains a &&
          (D ++ [x]).any fun s => CSE.rootNode f s && (f.value? s).any (·.args.contains a)
        if D.all listed && D.all (CSE.rootNode f) &&
            N.all (fun n => (f.value? n).isNone && (g.block? fv.block).any (·.values.contains n) &&
              (g.value? n).any (·.block == fv.block)) &&
            L.all (CSE.rootNode g) &&
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

/-- The read-only data symbol `aux` names in `tabs` (`SRODATA` with exported bytes,
`Sem.rodataBytes?`), with its allocation in the global image (`Sem.rodataAlloc`). -/
def roSym? (tabs : Tables) (aux : Option AuxRef) : Option (String × Sem.Alloc) :=
  match aux.bind tabs.aux? with
  | some { kind := .sym name _ "SRODATA" size _ ti itab data relocs _, .. } =>
    (Sem.rodataBytes? data ti itab).map fun d => (name.toStringLossy, Sem.rodataAlloc d size relocs)
  | _ => none

/-- The read-only data symbols `f`'s `Addr`s name in `tabs`, with their allocations: the
symbols the precondition `RoImage` of the rewrite passes pins for their input. -/
def roSyms (tabs : Tables) (f : Func) : List (String × Sem.Alloc) :=
  f.valueTab.toList.filterMap fun o => o.bind fun v =>
    if v.op == .Addr then roSym? tabs v.aux else none

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

/-- The source of the `Move` `fv` of `f` is an `Addr` of a symbol of `ro` whose bytes are zero. -/
def roSrcOK (tabs : Tables) (ro : List (String × Sem.Alloc)) (f : Func) (fv : Value) : Bool :=
  match fv.args.toList with
  | [_, s, _] => (f.value? s).any fun sv => (WBCheck.symName? tabs sv.aux).any fun n =>
      ro.any fun e => e.1 == n && e.2.data.all (· == .b 0)
  | _ => false

/-- The read-only segments (`roSeg?`; the anchors that are `Move`s of `f`) copy from symbols of
`ro` whose bytes are zero, and `f` passes `WBCheck.memTyOK` (so every memory a run of `f` holds
has the symbols of `ro`, `GoFV.Proof.MemInv`). -/
def roSegsOK (tabs : Tables) (ro : List (String × Sem.Alloc)) (f g : Func) : Bool :=
  let movs := (segList (segArr tabs f g)).filter fun s => (f.value? s.1).any (·.op == .Move)
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

/-- The `Load` `v` of `f` that event `ev` expands (a `structLoads` rule event, `structLoadShapeOK`)
and the logged definitions, if `structLoadOK` validates them on `f`'s definitions. -/
def slEvent? (t : Interp.Table) (tabs : Tables) (f : Func) : RwEvent → Option (ID × List Value)
  | .rule v i _ defs =>
    match f.value? v with
    | some u =>
      let n := ((t.values[u.op.ctorIdx]?).map (·.size)).getD 0
      if u.op == .Load && n + t.loads.size ≤ i &&
          (t.structLoads[i - n - t.loads.size]?).any (structLoadShapeOK ·.rule) &&
          structLoadOK tabs f.valueTab v defs.toList then some (v, defs.toList)
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

/-- One event of `slPre`: an expansion of `f` is applied, any other event kept, but for the
copy-argument replacements of the expanded `Load` logged before it. -/
def slStep (t : Interp.Table) (tabs : Tables) (f : Func) (p : Func × Array RwEvent)
    (ev : RwEvent) : Func × Array RwEvent :=
  match slEvent? t tabs f ev with
  | some (v, ds) => (slApply p.1 v ds, p.2.filter fun | .copyArg w _ _ => w != v | _ => true)
  | none => (p.1, p.2.push ev)

/-- The input with the log's validated struct-load expansions applied, and the remaining events. -/
def slPre (t : Interp.Table) (tabs : Tables) (f : Func) (log : Array RwEvent) :
    Func × Array RwEvent :=
  log.foldl (slStep t tabs f) (f, #[])

/-- The expansions `slPre` applies. -/
def slTaken (t : Interp.Table) (tabs : Tables) (f : Func) (log : Array RwEvent) : Array RwEvent :=
  log.filter fun ev => (slEvent? t tabs f ev).isSome

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
far, or a copy-argument replacement of a `Load`'s argument or by a `Load`, that the replay
validates on them is applied and taken (not an event the replay skips: of a dropped rule,
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
        match replay tabs t f s.M [] [ev] with
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
          (u.args[i]?).any (copyReachW tabs s.M s.M.size · src) then
        match replay tabs t f s.M [] [ev] with
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

/-- A layer: nil-check eliminations (`nilPre`), Load-of-Store forwardings (`fwdPre`), struct-load
expansions (`slPre`), struct-store splits (`ssPre`), value-rule `Load` expansions (`ldPre`),
segment rewrites (`segPre`), selections of `Phi`s of `SliceMake`s (`psPre`). -/
inductive Layer where
  | nil (sel : Bool)
  | fwd (sel : Bool)
  | sl
  | ss
  | ld
  | seg
  | ps

/-- The input with the layer's events of the log applied, and the remaining events. -/
def Layer.pre (t : Interp.Table) (tabs : Tables) : Layer → Func → Array RwEvent →
    Func × Array RwEvent
  | .nil sel => nilPre t tabs sel
  | .fwd sel => fwdPre t tabs sel
  | .sl => slPre t tabs
  | .ss => ssPre t
  | .ld => ldPre t tabs
  | .seg => segPre t
  | .ps => psPre t

/-- The layers of `RewriteCheck.accepts`, in order (a second split layer for nested structs). -/
def layers : List Layer :=
  [.ps, .nil true, .fwd true, .sl, .ss, .ss, .seg, .fwd false, .nil false]

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
rule logged before it matches the selection, not the copy. -/

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
and `f'`: `nilOK`, `fwdRel`, `validate` with the expansions it applied (`slTaken`, `ldTaken`),
`ssRel`, or `segRel` with its read-only segments' symbols among `f0`'s (`roSegsOK`, `roSyms`), and
`f'` passes `check`. -/
def RewriteCheck.layerOK (env : PassEnv) (t : GoFV.Rules.Interp.Table) (tabs : GoFV.SSA.Tables)
    (f0 : GoFV.SSA.Func) :
    RewriteCheck.Layer → GoFV.SSA.Func → Array GoFV.Rules.RwEvent → GoFV.SSA.Func → Bool
  | .nil _, f, _, f' => RewriteCheck.nilOK env tabs f0 f f'
  | .fwd _, f, _, f' =>
    RewriteCheck.fwdRel tabs f f' && checkOK { tabs := tabs, typs := env.typs } f'
  | .sl, f, log, f' =>
    RewriteCheck.validate tabs t f f' (RewriteCheck.slTaken t tabs f log) &&
      checkOK { tabs := tabs, typs := env.typs } f'
  | .ss, f, _, f' => RewriteCheck.ssRel tabs f f' && checkOK { tabs := tabs, typs := env.typs } f'
  | .seg, f, _, f' =>
    RewriteCheck.segRel tabs f f' &&
      RewriteCheck.roSegsOK tabs (RewriteCheck.roSyms env.tables f0) f f' &&
      checkOK { tabs := tabs, typs := env.typs } f'
  | .ps, f, _, f' =>
    RewriteCheck.psRel tabs f f' && checkOK { tabs := tabs, typs := env.typs } f'
  | .ld, f, log, f' =>
    RewriteCheck.validate tabs t f f' (RewriteCheck.ldTaken t tabs f log) &&
      checkOK { tabs := tabs, typs := env.typs } f'

/-- The layers `Ls` take their events out of the log, each a step `layerOK` accepts (a layer
without events is skipped), and `validate` accepts `out` against the last function and the
remaining events. -/
def RewriteCheck.layersOK (env : PassEnv) (t : GoFV.Rules.Interp.Table) (f0 : GoFV.SSA.Func)
    (out : PassOut) : List RewriteCheck.Layer → GoFV.SSA.Func → Array GoFV.Rules.RwEvent → Bool
  | [], f, log => RewriteCheck.validate out.tables t f out.func log
  | L :: Ls, f, log =>
    match L.pre t out.tables f log with
    | (f', log') =>
      if log'.size == log.size then RewriteCheck.layersOK env t f0 out Ls f log
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
