import GoFV.Proof.Rules.Block
import GoFV.Rules.Run
import GoFV.Opt.CSE
import GoFV.Opt.TabsAgree
import GoFV.Opt.NilCheckRel
import GoFV.Opt.Checked

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
  (`topOK`: `natShape`, a pointer op `ptrTop` whose arguments have the shapes `argShapeOk`
  asks for, `Pat.argsOK`, checked at every op node, or a constant composite `constTop`), every
  leaf has an integer, boolean or pointer shape, and the built definitions are those of
  `Rule.Sound`'s result denotation (`resDen`); only in-place `build` and `copy` results;
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
   .OrB, .Xor8, .Xor16, .Xor32, .Xor64, .EqPtr, .NeqPtr]

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

/-- Comparisons (incl. pointer comparisons) and boolean ops: their result is a boolean (or
`poison`). -/
def boolOp : Op → Bool
  | .Eq8 | .Neq8 | .Less8 | .Less8U | .Leq8 | .Leq8U | .Eq16 | .Neq16 | .Less16 | .Less16U
  | .Leq16 | .Leq16U | .Eq32 | .Neq32 | .Less32 | .Less32U | .Leq32 | .Leq32U | .Eq64 | .Neq64
  | .Less64 | .Less64U | .Leq64 | .Leq64U | .AndB | .OrB | .EqB | .NeqB | .Not | .ConstBool
  | .IsInBounds | .IsSliceInBounds | .EqPtr | .NeqPtr => true
  | _ => false

/-- Integer ops whose result is an integer of width `w` (or `poison`); `Ctz`/`BitLen`/`PopCount`/
`Slicemask` produce their type's width. -/
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
  | .Ctz8 | .Ctz16 | .Ctz32 | .Ctz64 | .Ctz8NonZero | .Ctz16NonZero | .Ctz32NonZero
  | .Ctz64NonZero | .BitLen8 | .BitLen16 | .BitLen32 | .BitLen64 | .PopCount8 | .PopCount16
  | .PopCount32 | .PopCount64 | .Slicemask => true
  | _ => false

/-- `evalPure op ty …` always has shape `ty` (P1 integer and boolean ops). -/
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
def strTy : Sem.Ty := .agg [(0, .ptr (some 1)), (8, .int .w64)] 16

/-- Table-evaluated ops (`GoFV.Proof.Rules.opVal`) at the shape of their value: `Addr` (a
pointer or `poison`) at a pointer shape, `ConstString` (a string or `poison`) at the string
shape. -/
def frameTop (op : Op) (ty : Sem.Ty) : Bool :=
  (op == .Addr && isPtrTy ty) || (op == .ConstString && GoFV.Opt.CSE.tyEq ty strTy)

/-- The top op of a match produces a value of its type's shape `ty` (`natShape`, `ptrTop` under
`Pat.argsOK`, `constTop`, `frameTop`). -/
def topOK (op : Op) (ty : Sem.Ty) : Bool :=
  natShape op ty || ptrTop op ty || constTop op ty || frameTop op ty

mutual
/-- Every leaf of the pattern has an integer, boolean, pointer or memory shape. `Pat.typed` asks of the
leaves that their values have their type's shape: `Val.retype` at a shape always produces a
value of that shape (`Val.retype_hasTy`, issue #108). -/
def leavesOK (tabs : Tables) (M : Defs) (I : Inst) (p : Path) : Pat → Bool
  | .op _ _ _ _ _ _ args _ => leavessOK tabs M I p 0 args
  | _ =>
    match M.get? (I.at p) with
    | some x => (match tabs.ty x.type with | .int _ | .bool | .ptr _ | .mem => true | _ => false)
    | none => false
def leavessOK (tabs : Tables) (M : Defs) (I : Inst) (p : Path) (i : Nat) : List Pat → Bool
  | [] => true
  | q :: qs => leavesOK tabs M I (i :: p) q && leavessOK tabs M I p (i + 1) qs
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

/-- The built definitions are the result's (`resDen`): `copy` of a bound value, or an in-place
`build` whose node 0 is `v` and whose other nodes are fresh. -/
def resultOK (tabs : Tables) (M : Defs) (ev : Expr → DV) (or : Oracle) (σ : Nat → DV)
    (I : Inst) (r : Rule) (v : Value) (defs : List Value) : Bool :=
  let topTy := tabs.ty v.type
  match r.result, r.block, defs with
  | .copy ce, none, [u] =>
    match DV.pos? (ev ce) with
    | some p => u.id == v.id && u.op == .Copy && u.args == #[I.at p] &&
        (M.get? (I.at p)).any (·.type == u.type) && I.at p != v.id && u.auxInt == 0 && u.aux == none
    | none => false
  | .build nodes, none, u0 :: us =>
    let ids := us.map (·.id)
    u0.id == v.id && ids.head? == some v.id && us.length == nodes.length &&
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
auxint `int64(len(x))` is the string's length. -/
def frameNodeOK (tabs : Tables) (e : PEnv) (pat : Pat) (n : RNode) (u : Value) : Bool :=
  (match n.aux.bind strDataVar? with
    | some x => match strOf tabs e pat x with
      | some (s, d) => s.size != 0 && symName? tabs u.aux == some d
      | none => false
    | none => true) &&
  (match n.auxInt.bind lenVar? with
    | some x => match strOf tabs e pat x with
      | some (s, _) => u.auxInt == Int64.ofNat s.size
      | none => false
    | none => true)

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
          | .op o _ _ _ _ _ _ _ => topOK o (e.ty [])
          | _ => false) &&
        Pat.argsOK e.ty [] r.pat &&
        leavesOK tabs M I [] r.pat &&
        resultOK tabs M ev or σ I r x defs &&
        nodes.all fun (n, u) => frameNodeOK tabs e r.pat n u

/-- A `Copy` of shape `s` of a value of shape `t` is the identity on it: the same shape, or two
pointer shapes (`Val.retype` at a pointer shape ignores the element size). -/
def copyCompat (s t : Sem.Ty) : Bool :=
  GoFV.Opt.CSE.tyEq s t || (s matches .ptr _ && t matches .ptr _)

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

/-- Replay the log on the definitions `M` and the terminators `B`, starting from `f`'s; `none`
if an event is not validated. -/
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
        if ruleOK tabs M cr.rule v defs.toList then
          replay tabs t f (defs.foldl (fun M u => M.put u.id u) M) B evs
        else none
  | M, B, .copyArg v i src :: evs =>
    match M.get? v with
    | none => none
    | some x =>
      if h : i < x.args.size then
        if copyReach tabs M M.size x.args[i] src then
          replay tabs t f (M.put v { x with args := x.args.set i src }) B evs
        else none
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

/-- Every value listed in `g` has its replayed definition, up to copies in its arguments, and
every block of `g` its replayed terminator (`bstate`): the kind, the successors (swapped if the
replay swapped them, then from two), the controls up to copies. -/
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
          u.id == x && m.id == x && u.op == m.op && u.type == m.type && u.auxInt == m.auxInt &&
          u.aux == m.aux && u.args.size == m.args.size &&
          (m.args.toList.zip u.args.toList).all fun (a, a') => copyReach tabs M n a a'
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
checker justifies by itself (`NilCheck.safePtr`: `Addr`, `LocalAddr`, `NilCheck`). -/
def nilElimOK (r : Rule) : Bool :=
  match r.pat, r.result with
  | .op .NilCheck none _ _ _ .fixed [.op o (some x) _ _ _ _ _ _, _] _, .copy (.var y) =>
    x == y && (o matches .Addr | .LocalAddr | .NilCheck)
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

/-- One event of `nilPre`: a nil-check elimination of `f` is applied, any other event kept. -/
def nilStep (t : Interp.Table) (f : Func) (p : Func × Array RwEvent) (ev : RwEvent) :
    Func × Array RwEvent :=
  match nilEvent? t f ev with
  | some v => (nilCopy p.1 v, p.2)
  | none => (p.1, p.2.push ev)

/-- The input with the log's nil-check eliminations applied, and the remaining events. -/
def nilPre (t : Interp.Table) (f : Func) (log : Array RwEvent) : Func × Array RwEvent :=
  log.foldl (nilStep t f) (f, #[])

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

/-- One step of `ptrBase`: an `OffPtr` or `Copy` of pointer shape on a pointer-shaped argument,
its argument and its offset. -/
def ptrStep? (tabs : Tables) (f : Func) (a : ID) : Option (ID × BitVec 64) :=
  match f.value? a with
  | some u =>
    if (u.op == .OffPtr || u.op == .Copy) && u.args.size == 1 && isPtrTy (tabs.ty u.type) &&
        ptrVal tabs f u.args[0]! then
      some (u.args[0]!, if u.op == .OffPtr then BitVec.ofInt 64 u.auxInt.toInt else 0)
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
`LocalAddr`'s frame variable (in activation 0, where the atom simulation runs: `Sem.frameVal`,
`AtomSim.MemAtoms`) or an `Addr`'s global (`Sem.addrVal`). -/
def baseBlk? (tabs : Tables) (f : Func) (a : ID) : Option Sem.Blk :=
  match f.value? a with
  | some u =>
    if u.op == .LocalAddr then u.aux.map (Sem.frameBlk tabs 0)
    else if u.op == .Addr then
      match u.aux.bind tabs.aux? with
      | some { kind := .sym name .., .. } => some (.global name.toStringLossy)
      | _ => none
    else none
  | none => none

/-- Base pointers equal where both are pointers: the same value, the start of one allocation
(`baseBlk?`), or `AddPtr`/`PtrIndex` nodes of one shape on such pointers (`ptrBase`, the same
offset) by equal indices (`idxSame`). -/
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
        idxSame tabs f u.args[1]! w.args[1]!
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

/-- A shape a `Store` writes and a `Load` reads back unchanged (`Sem.encode`, `Sem.decode`): an
integer, a boolean or a pointer. -/
def fwdTy : Sem.Ty → Bool
  | .int _ | .bool | .ptr _ => true
  | _ => false

/-- Shapes `fwdTy` that write, read and retype alike: equal up to pointers' element sizes
(`copyCompatibleType`). -/
def fwdTyEq : Sem.Ty → Sem.Ty → Bool
  | .int w, .int w' => w == w'
  | .bool, .bool => true
  | .ptr _, .ptr _ => true
  | _, _ => false

/-- A `Store` at type shape `s` writes a value of shape `t` (`fwdTy`) as a write at `t` does:
`fwdTyEq`, or a pointer stored as a 64-bit integer (`Sem.encode` writes a pointer's bytes at
both). -/
def fwdStoreTy (t s : Sem.Ty) : Bool :=
  fwdTyEq t s || (isPtrTy t && s matches .int .w64)

/-- Memory `m` of `f`, read at pointer `p` at shape `t`, holds `x`: through at most `d` `Copy`s
and `Store`s at pointers disjoint from the read (`disjointB`), a `Store` of `x` at a pointer equal
to `p` (`samePtrB`) at a type of shape `t` (`fwdStoreTy`), and `x` of shape `t` (`fwdTyEq`). -/
def fwdChain (tabs : Tables) (f : Func) (p : ID) (t : Sem.Ty) (x : ID) : Nat → ID → Bool
  | 0, _ => false
  | d + 1, m =>
    match f.value? m, f.value? x with
    | some s, some xv =>
      (s.op == .Copy && s.args.size == 1 && fwdChain tabs f p t x d s.args[0]!) ||
      ((s.op == .Store || s.op == .StoreWB) && s.args.size == 3 &&
       ((s.args[1]! == x && samePtrB tabs f p s.args[0]! && fwdStoreTy t (Sem.auxTy tabs s.aux) &&
           fwdTyEq t (tabs.ty xv.type)) ||
        (disjointB tabs f p t.size s.args[0]! (Sem.auxTy tabs s.aux).size &&
           fwdChain tabs f p t x d s.args[2]!)))
    | _, _ => false

/-- The `Load` `u` of `f` reads back the value `x` (`fwdChain` through at most eight `Copy`s and
`Store`s). -/
def fwdOK (tabs : Tables) (f : Func) (u : Value) (x : ID) : Bool :=
  u.op == .Load && u.args.size == 2 && fwdChain tabs f u.args[0]! (tabs.ty u.type) x 8 u.args[1]!

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

/-- Value `x` of `f` is unchanged in `g` (but for its use count), or a `Load` became `Copy` of
the value it reads back (`fwdOK`). -/
def fwdRepOK (tabs : Tables) (f g : Func) (x : ID) : Bool :=
  match f.value? x, g.value? x with
  | none, _ => true
  | some _, none => false
  | some u, some w =>
    w.id == u.id && w.block == u.block && w.type == u.type &&
    ((w.op == u.op && w.auxInt == u.auxInt && w.aux == u.aux && w.args == u.args) ||
     (w.op == .Copy && w.args.size == 1 && fwdOK tabs f u (w.args[0]?.getD 0)))

/-- `g` is `f` with Loads forwarded: the same blocks and atoms, every value as `fwdRepOK`
says, ranks ordering `f`'s listed values after their arguments. -/
def fwdRel (tabs : Tables) (f g : Func) : Bool :=
  atomsOK f g && closedOK f && closedOK g && g.blocks == f.blocks && g.blockTab == f.blockTab &&
  fwdRankOK f (fwdRank f) && (List.range f.valueTab.size).all (fwdRepOK tabs f g ·)

/-- The variable a chain of at most `n` `Store`s binds as a stored value is `y`. -/
def storesBind (y : Nat) : Nat → Pat → Bool
  | n + 1, .op .Store none _ _ _ .fixed [_, v, m] _ =>
    (match v with | .bind z => z == y | _ => false) || storesBind y n m
  | _, _ => false

/-- A Load-of-Store forwarding rule: `(Load _ m) => x` with `x` stored by one of the up to four
`Store`s of the chain `m` (`generic.rules:800`, `:806`, `:813`, `:821`; the validator checks each
instance by `fwdOK`, the `isSamePtr`/`disjoint` conditions included). -/
def fwdShapeOK (r : Rule) : Bool :=
  match r.pat, r.result, r.block with
  | .op .Load none _ _ _ .fixed [_, m] _, .copy (.var y), none => storesBind y 4 m
  | _, _, _ => false

/-- The `Load` `v` of `f` that event `ev` forwards and the value it becomes a copy of, if it is a
`loads` rule event (`fwdShapeOK`) with a `Copy` result. -/
def fwdEvent? (t : Interp.Table) (f : Func) : RwEvent → Option (ID × ID)
  | .rule v i _ defs =>
    match f.value? v with
    | some u =>
      if u.op == .Load then
        let n := ((t.values[u.op.ctorIdx]?).map (·.size)).getD 0
        if n ≤ i then
          match t.loads[i - n]?, defs.toList with
          | some cr, [w] =>
            if fwdShapeOK cr.rule && w.op == .Copy && w.args.size == 1 then some (v, w.args[0]!)
            else none
          | _, _ => none
        else none
      else none
    | none => none
  | _ => none

/-- `v.reset(OpCopy); v.AddArg(x)`: the `Load` `v` of `f` becomes `Copy x`, its arguments lose
a use, `x` gains one. -/
def fwdCopy (f : Func) (v x : ID) : Func :=
  match f.value? v with
  | some u =>
    if u.op == .Load then
      let f := u.args.foldl (fun f a => f.modV a fun w => { w with uses := w.uses - 1 }) f
      let f := f.modV x fun w => { w with uses := w.uses + 1 }
      f.modV v fun w => { w with op := .Copy, auxInt := 0, aux := none, args := #[x] }
    else f
  | none => f

/-- One event of `fwdPre`: a forwarding of `f` is applied, any other event kept, but for the
copy-argument replacements of the forwarded `Load` logged before it (copy elimination on the
`Load`'s arguments, which the forwarding validated in `f` replaces). -/
def fwdStep (t : Interp.Table) (f : Func) (p : Func × Array RwEvent) (ev : RwEvent) :
    Func × Array RwEvent :=
  match fwdEvent? t f ev with
  | some (v, x) => (fwdCopy p.1 v x, p.2.filter fun | .copyArg w _ _ => w != v | _ => true)
  | none => (p.1, p.2.push ev)

/-- The input with the log's Load-of-Store forwardings applied, and the remaining events. -/
def fwdPre (t : Interp.Table) (f : Func) (log : Array RwEvent) : Func × Array RwEvent :=
  log.foldl (fwdStep t f) (f, #[])

end GoFV.Opt.RewriteCheck

namespace GoFV.Opt

/-- The nil-check eliminations of the log, applied to `f` (`f'`, `RewriteCheck.nilPre`), are
nilcheckelim's (`NilCheck.nrel` in the result's tables `tabs`: each pointer is a `safePtr` seed,
the other roots keep their order), and `f'` passes `check`. -/
def RewriteCheck.nilOK (env : PassEnv) (tabs : GoFV.SSA.Tables) (f f' : GoFV.SSA.Func) : Bool :=
  NilCheck.nrel tabs f f' && checkOK { tabs := tabs, typs := env.typs } f'

/-- `RewriteCheck.validate` accepts `out` against `f` and the log, or, when the log forwards
Loads of Stores (`fwdPre`, issue #151), `f` with these forwardings applied is related to `f` by
`fwdRel`, passes `check`, and `validate` accepts `out` against it and the remaining events. -/
def RewriteCheck.fwdAccepts (env : PassEnv) (t : GoFV.Rules.Interp.Table)
    (f : GoFV.SSA.Func) (out : PassOut) (log : Array GoFV.Rules.RwEvent) : Bool :=
  match RewriteCheck.fwdPre t f log with
  | (f', log') =>
    if log'.size == log.size then RewriteCheck.validate out.tables t f out.func log
    else RewriteCheck.fwdRel out.tables f f' && checkOK { tabs := out.tables, typs := env.typs } f' &&
      RewriteCheck.validate out.tables t f' out.func log'

/-- `checkedRewrite` keeps the rewrite result `out` of `f` (input environment `env`, rewrite
log `log`): `f` cannot tell the result's tables from the input's (`tabsAgree`: rules create
types such as `ConstNil <v.Type.Elem().PtrTo()>` and symbols such as `fe.StringData(s)`, but no
definitions the input looks up), and `RewriteCheck.fwdAccepts` accepts it in the result's
tables, against `f` and the log, or, when the log eliminates nil checks (`nilPre`, issue #151),
against `f` with these eliminations applied (`nilOK`) and the remaining events. -/
def RewriteCheck.accepts (env : PassEnv) (t : GoFV.Rules.Interp.Table)
    (f : GoFV.SSA.Func) (out : PassOut) (log : Array GoFV.Rules.RwEvent) : Bool :=
  tabsAgree env.tables out.tables f &&
  match RewriteCheck.nilPre t f log with
  | (f', log') =>
    if log'.size == log.size then RewriteCheck.fwdAccepts env t f out log
    else RewriteCheck.nilOK env out.tables f f' && RewriteCheck.fwdAccepts env t f' out log'

/-- `applyRewrite` with the table `t` and its log; the result if `RewriteCheck.accepts` it. -/
def checkedRun (t : GoFV.Rules.Interp.Table) (env : PassEnv) (f : GoFV.SSA.Func) :
    Except String (Option PassOut) := do
  let (out, _, log) ← GoFV.Rules.rewriteRun t true true env f
  return if RewriteCheck.accepts env t f out log then some out else none

/-- The validated rewrite pass: `applyRewrite` with the table `t` and its log, the result with
the pass's extended tables if `RewriteCheck.accepts` it; else (a Load-of-Store forwarding the
validator cannot relate, issue #151) the same without the table's forwardings (`loads`), if
accepted; else the input. -/
def checkedRewrite (t : GoFV.Rules.Interp.Table) : Pass := fun env f => do
  match ← checkedRun t env f with
  | some out => return out
  | none =>
    if t.loads.isEmpty then return { func := f, tables := env.tables } else
    match ← checkedRun { t with loads := #[] } env f with
    | some out => return out
    | none => return { func := f, tables := env.tables }

end GoFV.Opt
