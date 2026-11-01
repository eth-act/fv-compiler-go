import GoFV.Proof.Rules.Den
import GoFV.Rules.Run
import GoFV.Opt.CSE

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
  (`natShape`), every leaf that is a pure value too, and the built definitions are those of
  `Rule.Sound`'s result denotation (`resDen`); only in-place `build` and `copy` results;
* a copy-argument replacement (`copyArg v i src`, copy elimination before a rule matches) is
  replayed on the definitions when `src` is reached from the old argument through `Copy`s of
  compatible shape (`copyReach`);
* a phi elimination or block rule rejects;
* finally every value listed in the output `g` has the replayed definition up to copies:
  each argument (and each control of `g`) is the replayed one or reached from it through
  `Copy`s of the same shape (`copyReach`), which is how copy elimination and `copySource`'s
  path compression rewrite arguments.

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

/-- Ops evaluated by `evalPure` (not roots, phis or frame-dependent ops): the nodes of terms. -/
def termOp (op : Op) : Bool :=
  !Sem.isRoot op && !(op matches .Phi | .InitMem | .Arg | .ArgIntReg | .PanicBounds |
    .StaticLECall | .StaticCall | .Store | .StoreWB | .Move | .MoveWB | .Zero | .ZeroWB |
    .VarDef | .VarLive | .KeepAlive | .WBend | .NilCheck | .SP | .LocalAddr | .Addr |
    .ConstString | .GetClosurePtr | .GetCallerSP | .Invalid)

/-- The ops whose first two arguments commute (`GoFV.Proof.Rules.commOpsP1`): a `commute` node
is matched swapped only at these. -/
def commOps : List Op :=
  [.Add8, .Add16, .Add32, .Add64, .Add64carry, .And8, .And16, .And32, .And64, .AndB, .Eq8,
   .Eq16, .Eq32, .Eq64, .EqB, .Mul8, .Mul16, .Mul32, .Mul64, .Mul32uhilo, .Mul32uover,
   .Mul64uhilo, .Mul64uover, .Neq8, .Neq16, .Neq32, .Neq64, .NeqB, .Or8, .Or16, .Or32, .Or64,
   .OrB, .Xor8, .Xor16, .Xor32, .Xor64]

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

/-- The oracle of the validator: an unmodelled boolean expression is `true`, others `other`;
result fields come from the built nodes (`fields`: per result node, its expressions and the
built value). -/
def oracle (vtys : List GoTy) (tabs : Tables) (nodes : List (RNode × Value)) : Oracle where
  dv e := if exprTy vtys e == .bool then .bool true else .other
  ty e := ((nodes.find? fun (n, _) => match n.ty with
      | some te => reprStr te == reprStr e | none => false).map fun (_, u) => tabs.ty u.type).getD .other
  auxInt e := ((nodes.find? fun (n, _) => match n.auxInt with
      | some ae => reprStr ae == reprStr e | none => false).map (·.2.auxInt)).getD 0
  aux e := ((nodes.find? fun (n, _) => match n.aux with
      | some xe => reprStr xe == reprStr e | none => false).map (·.2.aux)).getD none
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

/-- Comparisons and boolean ops: their result is a boolean (or `poison`). -/
def boolOp : Op → Bool
  | .Eq8 | .Neq8 | .Less8 | .Less8U | .Leq8 | .Leq8U | .Eq16 | .Neq16 | .Less16 | .Less16U
  | .Leq16 | .Leq16U | .Eq32 | .Neq32 | .Less32 | .Less32U | .Leq32 | .Leq32U | .Eq64 | .Neq64
  | .Less64 | .Less64U | .Leq64 | .Leq64U | .AndB | .OrB | .EqB | .NeqB | .Not | .ConstBool
  | .IsInBounds | .IsSliceInBounds => true
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

mutual
/-- Every leaf of the pattern has a sized shape (not `.other`): registers have their type's shape
(`Val.retype` shapes every result; issue #108), which `Pat.typed` asks of the leaves. -/
def leavesOK (tabs : Tables) (M : Defs) (I : Inst) (p : Path) : Pat → Bool
  | .op _ _ _ _ _ _ args _ => leavessOK tabs M I p 0 args
  | _ =>
    match M.get? (I.at p) with
    | some x => !(tabs.ty x.type matches .other)
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

/-- The rule event `(v, r, defs)` is a sound instance of `r` on `M`. The matched values below
the top are not `v` (no cyclic match). -/
def ruleOK (tabs : Tables) (M : Defs) (r : Rule) (v : ID) (defs : List Value) : Bool :=
  Pat.arityOk r.pat && patOK r.pat &&
  match M.get? v with
  | none => false
  | some x =>
    termOp x.op &&
    (choices (Pat.commutes r.pat)).any fun sw =>
      match matchPat M r.pat [] v sw with
      | none => false
      | some (I, _) =>
        let e := env tabs M I
        let vtys := r.vars.map (·.ty)
        let σ := sigma e r.pat
        let nodes := match r.result, defs with
          | .build ns, _ :: us => ns.zip us
          | _, _ => []
        let or := oracle vtys tabs nodes
        let ev := evalE vtys σ or e (Pat.den e [] r.pat)
        I.tail.all (·.2 != v) &&
        consOK ev σ e I [] r.pat && wfOK e [] r.pat &&
        (match r.cond with
          | some c => match ev c with | .bool true => true | _ => false
          | none => true) &&
        (match r.pat with
          | .op o _ _ _ _ _ _ _ => natShape o (e.ty [])
          | _ => false) &&
        leavesOK tabs M I [] r.pat &&
        resultOK tabs M ev or σ I r x defs

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

/-- Replay the log on the definitions of `f`; `none` if an event is not validated. -/
def replay (tabs : Tables) (t : Interp.Table) : Defs → List RwEvent → Option Defs
  | M, [] => some M
  | M, .rule v i _ defs :: evs =>
    match M.get? v with
    | none => none
    | some x =>
      match (t.values[x.op.ctorIdx]?).bind (·[i]?) with
      | none => none
      | some cr =>
        if ruleOK tabs M cr.rule v defs.toList then
          replay tabs t (defs.foldl (fun M u => M.put u.id u) M) evs
        else none
  | M, .copyArg v i src :: evs =>
    match M.get? v with
    | none => none
    | some x =>
      if h : i < x.args.size then
        if copyReach tabs M M.size x.args[i] src then
          replay tabs t (M.put v { x with args := x.args.set i src }) evs
        else none
      else none
  | M, .control .. :: evs => replay tabs t M evs
  | _, .phielim .. :: _ => none
  | _, .blockRule .. :: _ => none

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
  op matches .Phi | .Arg | .ArgIntReg | .SP | .LocalAddr | .Addr | .ConstString |
    .GetClosurePtr | .GetCallerSP

/-- `f` and `g` have the same blocks and terminators, the atoms of `g` are atoms of `f` with the
same fields and block, the atoms only `f` has are droppable (`dropAtom`), and each block
evaluates its roots in the same order (`Sem.schedule`). -/
def atomsOK (f g : Func) : Bool :=
  f.entry == g.entry && f.blocks == g.blocks && f.ownAux == g.ownAux &&
  f.blocks.all fun b =>
    match f.block? b, g.block? b with
    | some fb, some gb =>
      fb.id == gb.id && fb.kind == gb.kind && fb.succs == gb.succs &&
      fb.controls.size == gb.controls.size &&
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
every control of `g` is reached from `f`'s through copies. -/
def finalOK (tabs : Tables) (f g : Func) (M : Defs) : Bool :=
  let n := M.size
  g.blocks.all fun b =>
    match f.block? b, g.block? b with
    | some fb, some gb =>
      (fb.controls.toList.zip gb.controls.toList).all (fun (c, c') => copyReach tabs M n c c') &&
      gb.values.all fun x =>
        match M.get? x, g.value? x with
        | some m, some u =>
          u.id == x && m.id == x && u.op == m.op && u.type == m.type && u.auxInt == m.auxInt &&
          u.aux == m.aux && u.args.size == m.args.size &&
          (m.args.toList.zip u.args.toList).all fun (a, a') => copyReach tabs M n a a'
        | _, _ => false
    | _, _ => false

/-- **The validator**: `g` (the result of the rewrite pass with table `t` on `f`, which logged
`log`) is related to `f` as the theorems need. -/
def validate (tabs : Tables) (t : Interp.Table) (f g : Func) (log : Array RwEvent) : Bool :=
  atomsOK f g && closedOK f && closedOK g &&
  match replay tabs t f.valueTab log.toList with
  | some M => finalOK tabs f g M
  | none => false

end GoFV.Opt.RewriteCheck

namespace GoFV.Opt

/-- The validated rewrite pass: `applyRewrite` with the table `t` and its log; the result if
`RewriteCheck.validate` accepts it, else the input. The tables are the input's (the validated
rules create no definitions). -/
def checkedRewrite (t : GoFV.Rules.Interp.Table) : Pass := fun env f => do
  let (out, _, log) ← GoFV.Rules.rewriteRun t true true env f
  if RewriteCheck.validate env.tables t f out.func log then
    return { out with tables := env.tables }
  else return { func := f, tables := env.tables }

end GoFV.Opt
