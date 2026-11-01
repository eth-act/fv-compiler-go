import GoFV.Opt.ExpandCalls
import GoFV.Opt.Checked
import GoFV.SSA.Sem.TyEq
import GoFV.SSA.DomCert
import GoFV.Proof.ABIBuild

/-!
# The checker of `expand calls` (`ECCheck.ecCheck`, issue #28)

`ecCheck tabs f g` relates the input `f` of `expand calls` to its output `g` (both read in the
output tables `tabs`) as the conversion simulation `GoFV.Proof.EC.CvRel` needs it: the same
CFG, own aux, block kinds and controls; every value of `f` listed in the same block of `g`; the
same non-pure schedule sequence; every argument of a source node reaching it in `g`; new values
(IDs `f` does not define) pure, frame values or argument pieces, with new arguments in their
block or the entry block; and per source value one of these classes:

* **identity**: the same op, type, auxint, aux and arguments, none of them a converted value;
* **Arg**: an incoming parameter becomes a Make-tree (`StructMake`, `ArrayMake1`, `SliceMake`,
  `StringMake`, `IMake`, zero-sized parts `Empty`) of new values whose leaves read the
  parameter at the leaf offsets (`ArgIntReg {name+off}`, `Arg {name} [off]`, `ArgFloatReg` for
  opaque leaves);
* **call**: `StaticLECall`/`ClosureLECall`/`InterLECall` become `StaticCall`/`ClosureCall`/
  `InterCall` with the same leading arguments and memory and, per input parameter, its
  register pieces computed by selector chains (`SlicePtr`, `StructSelect [i]`, …) of the Go
  argument; the call's type is the register types of its results (`regShapeOK`);
* **select**: a call result `SelectN [i] c` becomes a Make-tree over `SelectN [firstReg + j] c`;
  the call's memory `SelectN [#outs] c` becomes `SelectN [#pieces] c`;
* **result**: a `MakeResult` becomes the register pieces of the results (selector chains).

Fragment (`v1`): every ABI parameter of the converted calls and of the function's results is
register-assigned with as many registers as its shape has leaves (no stack-assigned arguments
or results, no complex numbers; `regParamsOK`).

Structural recursion and `List` operations only: the checker runs compiled and in the kernel.
-/

namespace GoFV.Opt.ECCheck

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof.ABI

/-! ## Shapes and paths -/

/-- The ops that build a composite of their arguments (`Comp.make`). -/
def isMake : Op → Bool
  | .StructMake | .ArrayMake1 | .SliceMake | .StringMake | .IMake => true
  | _ => false

/-- The component a selector picks (`Comp.select`, `Comp.selectAux`). -/
def selIdx? (w : Value) : Option Nat :=
  match w.op with
  | .SlicePtr | .StringPtr | .ITab => some 0
  | .SliceLen | .StringLen | .IData => some 1
  | .SliceCap => some 2
  | .StructSelect | .ArraySelect => if w.auxInt.toInt < 0 then none else some w.auxInt.toInt.toNat
  | _ => none

mutual
/-- The paths from a value of shape `t` to its register leaves, in `leaves t` order: per step
the field index and the field's shape. -/
def leafPaths : Ty → List (List (Nat × Ty))
  | .agg fs _ => leafPathsFields 0 fs
  | .empty => []
  | .blob _ => []
  | _ => [[]]
/-- `leafPaths` of fields `i, i+1, …`. -/
def leafPathsFields : Nat → List (Nat × Ty) → List (List (Nat × Ty))
  | _, [] => []
  | i, (_, t) :: fs => (leafPaths t).map ((i, t) :: ·) ++ leafPathsFields (i + 1) fs
end

/-- A register of shape `rt` holds a piece of shape `lt` without loss: `lt`-retyping undoes
`rt`-retyping on values of shape `lt` (the same shape, pointers to other element sizes, or an
interface's type word in an `unsafe.Pointer` register). -/
def regShapeOK (rt lt : Ty) : Bool :=
  Ty.beq rt lt ||
    match rt, lt with
    | .ptr _, .ptr _ => true
    | .ptr _, .int .w64 => true
    | _, _ => false

/-- The shape of a value's type in `g` (`Ctx.tys`). -/
@[inline] def shapeOf (sh : Array Ty) (g : Func) (x : ID) : Ty := valueTy sh (g.value? x)

/-- An ID that `f` does not define. -/
@[inline] def isNewB (f : Func) (x : ID) : Bool := (f.value? x).isNone

/-! ## Make-trees and selector chains -/

/-- The leaves (in `leaves t` order) of the Make-tree of shape `t` rooted at `x` in `g`: every
node's type has the node's shape; a composite node is a Make op with one argument per field; a
zero-sized node is `Empty`; an atom is a leaf. Nodes below the root are new (`nw`). -/
def mkTree (sh : Array Ty) (g : Func) (nw : ID → Bool) : Nat → ID → Ty → Option (List ID)
  | 0, _, _ => none
  | n + 1, x, t =>
    match g.value? x with
    | none => none
    | some w =>
      if !Ty.beq (valueTy sh (some w)) t then none else
      match t with
      | .agg fs _ =>
        if isMake w.op && w.args.size == fs.length then
          ((fs.zip w.args.toList).mapM fun (ft, a) =>
            if nw a then mkTree sh g nw n a ft.2 else none).map List.flatten
        else none
      | .empty => if w.op == .Empty then some [] else none
      | t => if atom t then some [x] else none

/-- Node `p` of `g` computes the component of `a` at the reversed path `rp` by selectors (new
values whose types have the shapes along the path). -/
def chainOK (sh : Array Ty) (g : Func) (nw : ID → Bool) : List (Nat × Ty) → ID → ID → Bool
  | [], p, a => p == a
  | (k, s) :: rp, p, a =>
    nw p &&
      match g.value? p with
      | some w =>
        selIdx? w == some k && Ty.beq (valueTy sh (some w)) s && w.args.size == 1 &&
          chainOK sh g nw rp w.args[0]! a
      | none => false

/-! ## ABI parameters -/

/-- The input and the result assignments of an ABI. -/
def insOf (abi : CallABI) : List ABIParam := abi.params.toList.filter (!·.out)
def outsOf (abi : CallABI) : List ABIParam := abi.params.toList.filter (·.out)

/-- The `v1` fragment: every parameter register-assigned, a well-formed shape with as many
leaves as registers. -/
def regParamsOK (tabs : Tables) (ps : List ABIParam) : Bool :=
  ps.all fun p => !p.regs.isEmpty && wf (tabs.ty p.type) && (leaves (tabs.ty p.type)).length == p.regs.size

/-- The leaf shapes of the parameters, in register order. -/
def leafTys (tabs : Tables) (ps : List ABIParam) : List Ty :=
  ps.flatMap fun p => (leaves (tabs.ty p.type)).map (·.2)

/-- `t` is a tuple of the shapes `ts` and memory. -/
def tupleOf (ts : List Ty) (t : Ty) : Bool :=
  match t with
  | .tuple us => us.length == ts.length + 1 && (ts.zip us).all (fun (a, b) => Ty.beq b a) &&
      match us.getLast? with
      | some .mem => true
      | _ => false
  | _ => false

/-- `t` is the register tuple of the pieces of shapes `lts` and memory (`regShapeOK`). -/
def regTupleOf (lts : List Ty) (t : Ty) : Bool :=
  match t with
  | .tuple us => us.length == lts.length + 1 && (lts.zip us).all (fun (lt, rt) => regShapeOK rt lt) &&
      match us.getLast? with
      | some .mem => true
      | _ => false
  | _ => false

/-- The pieces `pcs` of `g` are, parameter by parameter, the selector chains of the source
values `as` (each of the parameter's shape in `f`). -/
def piecesOK (tabs : Tables) (sh : Array Ty) (f g : Func) : List ABIParam → List ID → List ID → Bool
  | [], [], [] => true
  | p :: ps, a :: as, pcs =>
    let t := tabs.ty p.type
    let paths := leafPaths t
    Ty.beq (shapeOf sh f a) t && paths.length ≤ pcs.length &&
      (paths.zip (pcs.take paths.length)).all (fun (π, q) => chainOK sh g (isNewB f) π.reverse q a) &&
      piecesOK tabs sh f g ps as (pcs.drop paths.length)
  | _, _, _ => false

/-- The post-`expand calls` op of a call op and its number of leading arguments. -/
def callOpMap : Op → Option (Op × Nat)
  | .StaticLECall => some (.StaticCall, 0)
  | .ClosureLECall => some (.ClosureCall, 2)
  | .InterLECall => some (.InterCall, 1)
  | _ => none

/-- The result assignments of a call value's aux (none if it has no ABI). -/
def callOuts (tabs : Tables) (aux : Option AuxRef) : List ABIParam :=
  ((callABI? tabs aux).map outsOf).getD []

/-- The function's own result assignments. -/
def ownOuts (tabs : Tables) (f : Func) : List ABIParam :=
  (abiParams tabs f).toList.filter (·.out)

/-- `x` is a value `expand calls` converts (a call or a `MakeResult`). -/
def converted (f : Func) (x : ID) : Bool :=
  match f.value? x with
  | some u => (callOpMap u.op).isSome || u.op == .MakeResult
  | none => false

/-! ## The classes of source values -/

/-- **call**: `u` (in `f`) and `w` (in `g`) at the same ID. -/
def callOK (tabs : Tables) (sh : Array Ty) (f g : Func) (u w : Value) : Bool :=
  match callOpMap u.op, callABI? tabs u.aux with
  | some (op, k), some abi =>
    let ins := insOf abi
    let outs := outsOf abi
    let n := u.args.size
    w.op == op && w.aux == u.aux && 0 < n && k + 1 ≤ n &&
      regParamsOK tabs abi.params.toList &&
      w.args.size ≥ k + 1 &&
      (w.args.extract 0 k).toList == (u.args.extract 0 k).toList &&
      w.args[w.args.size - 1]! == u.args[n - 1]! &&
      (u.args.extract 0 (n - 1)).toList.all (fun a => !converted f a) &&
      piecesOK tabs sh f g ins (u.args.extract k (n - 1)).toList
        (w.args.extract k (w.args.size - 1)).toList &&
      tupleOf (outs.map (tabs.ty ·.type)) (valueTy sh (some u)) &&
      regTupleOf (leafTys tabs outs) (valueTy sh (some w))
  | _, _ => false

/-- The leaves `ls` of the Make-tree of a call result `SelectN [i] c` are `SelectN [first + j] c`. -/
def selLeavesOK (g : Func) (c : ID) (first : Nat) : Nat → List ID → Bool
  | _, [] => true
  | j, l :: ls =>
    (match g.value? l with
     | some w => w.op == .SelectN && w.args.toList == [c] && w.auxInt.toInt == ((first + j : Nat) : Int)
     | none => false) && selLeavesOK g c first (j + 1) ls

/-- The leaves `ls` of the Make-tree of a parameter `Arg {n} [off]` of shape `t` read the
parameter at the leaves' offsets. -/
def argLeavesOK (tabs : Tables) (g : Func) (n : AuxRef) (off : Int) :
    List (Nat × Ty) → List ID → Bool
  | [], [] => true
  | (o, lt) :: os, l :: ls =>
    (match g.value? l with
     | some w =>
       match w.op with
       | .ArgIntReg =>
         match w.aux.bind tabs.aux? with
         | some { kind := .nameOff n' off', .. } => n' == n && off' == off + o
         | _ => false
       | .Arg => w.aux == some n && w.auxInt.toInt == off + o
       | .ArgFloatReg => match lt with
         | .opaque _ => true
         | _ => false
       | _ => false
     | none => false) && argLeavesOK tabs g n off os ls
  | _, _ => false

/-- The input parameters' names of `g`'s ABI (`Ctx.params`). -/
def paramNames (tabs : Tables) (g : Func) : List (Option AuxRef) :=
  ((abiParams tabs g).toList.filter (!·.out)).map (·.name)

/-- **Arg**. -/
def argOK (tabs : Tables) (sh : Array Ty) (f g : Func) (x : ID) (u : Value) : Bool :=
  match u.aux with
  | some n =>
    let t := shapeOf sh f x
    wf t && (paramNames tabs g).contains (some n) &&
      match mkTree sh g (isNewB f) (tabs.types.size + 1) x t with
      | some ls => argLeavesOK tabs g n u.auxInt.toInt (leaves t) ls
      | none => false
  | none => false

/-- **select**: `u = SelectN [i] c` of a converted call `c`. -/
def selectOK (tabs : Tables) (sh : Array Ty) (f g : Func) (x : ID) (u w : Value) : Bool :=
  match u.args.toList with
  | [c] =>
    match f.value? c with
    | some cu =>
      (callOpMap cu.op).isSome && u.auxInt.toInt ≥ 0 &&
      let outs := callOuts tabs cu.aux
      let i := u.auxInt.toInt.toNat
      if i == outs.length then
        -- the call's memory
        w.op == .SelectN && w.args.toList == [c] && w.type == u.type &&
          w.auxInt.toInt == ((leafTys tabs outs).length : Int)
      else
        match outs[i]? with
        | some p =>
          let t := tabs.ty p.type
          let first := (leafTys tabs (outs.take i)).length
          Ty.beq (shapeOf sh f x) t &&
            match mkTree sh g (isNewB f) (tabs.types.size + 1) x t with
            | some ls => ls.length == (leaves t).length && selLeavesOK g c first 0 ls
            | none => false
        | none => false
    | none => false
  | _ => false

/-- **result**: a `MakeResult` of the function's results. -/
def resultOK (tabs : Tables) (sh : Array Ty) (f g : Func) (u w : Value) : Bool :=
  let outs := ownOuts tabs f
  let n := u.args.size
  w.op == .MakeResult && n == outs.length + 1 && w.args.size ≥ 1 &&
    w.args[w.args.size - 1]! == u.args[n - 1]! &&
    !converted f u.args[n - 1]! &&
    piecesOK tabs sh f g outs (u.args.extract 0 (n - 1)).toList
      (w.args.extract 0 (w.args.size - 1)).toList &&
    tupleOf (outs.map (tabs.ty ·.type)) (valueTy sh (some u)) &&
    regTupleOf (leafTys tabs outs) (valueTy sh (some w))

/-- **identity**. -/
def identOK (f : Func) (u w : Value) : Bool :=
  w.op == u.op && w.type == u.type && w.auxInt == u.auxInt && w.aux == u.aux && w.args == u.args &&
    u.args.all (fun a => !converted f a)

/-- The class check of non-`Phi` source value `x`. -/
def valueOK (tabs : Tables) (sh : Array Ty) (f g : Func) (x : ID) : Bool :=
  match f.value? x, g.value? x with
  | some u, some w =>
    if (callOpMap u.op).isSome then callOK tabs sh f g u w
    else if u.op == .MakeResult then resultOK tabs sh f g u w
    else if u.op == .SelectN && u.args.size == 1 && converted f u.args[0]! then
      selectOK tabs sh f g x u w
    else if u.op == .Arg && !identOK f u w then argOK tabs sh f g x u
    else identOK f u w
  | _, _ => false

/-! ## Blocks -/

/-- `y` depends on `a` through arguments that are nodes of `gb` (`Order.Dep`). -/
def depB (g : Func) (node : ID → Bool) : Nat → ID → ID → Bool
  | 0, _, _ => false
  | n + 1, a, y =>
    node y &&
      match g.value? y with
      | some w => w.args.any fun z => node z && (z == a || depB g node n a z)
      | none => false

/-- A new value evaluates in every frame (`NewEval`): pure ops, frame values, and the pieces of
the function's parameters. -/
def newEvalB (tabs : Tables) (g : Func) (w : Value) : Bool :=
  match w.op with
  | .ArgIntReg =>
    match w.aux.bind tabs.aux? with
    | some { kind := .nameOff n _, .. } => (paramNames tabs g).contains (some n)
    | _ => false
  | .Arg => match w.aux with
    | some n => (paramNames tabs g).contains (some n)
    | none => false
  | .SP | .SB | .LocalAddr | .OffPtr | .SelectN | .Empty | .ArgFloatReg
  | .StructMake | .ArrayMake1 | .SliceMake | .StringMake | .IMake
  | .SlicePtr | .SliceLen | .SliceCap | .StringPtr | .StringLen | .ITab | .IData
  | .StructSelect | .ArraySelect => true
  | _ => false

/-- The checks of block `bid`. -/
def blockOK (tabs : Tables) (sh : Array Ty) (f g : Func) (bid : ID) : Bool :=
  match f.block? bid, g.block? bid with
  | some fb, some gb =>
    let nodeF : ID → Bool := fun x => fb.values.contains x &&
      match f.value? x with
      | some u => u.op != .Phi
      | none => false
    let nodeG : ID → Bool := fun x => gb.values.contains x &&
      match g.value? x with
      | some w => w.op != .Phi
      | none => false
    let fuel := gb.values.size + 1
    gb.kind == fb.kind && gb.controls == fb.controls &&
    fb.values.all (fun x => gb.values.contains x) &&
    gb.values.all (fun x => fb.values.contains x || isNewB f x) &&
    -- Phis: unchanged, unconverted
    gb.values.all (fun x => match g.value? x with
      | some w => w.op != .Phi || (fb.values.contains x && f.value? x == some w)
      | none => true) &&
    fb.values.all (fun x => match f.value? x with
      | some u => u.op != .Phi ||
          (g.value? x == some u && !converted f x && u.args.all (fun a => !converted f a))
      | none => true) &&
    -- the same non-pure sequence
    (match schedule f fb, schedule g gb with
      | some of, some og => of.toList.filter (npOf f fb) == og.toList.filter (npOf f fb)
      | _, _ => false) &&
    -- every argument of a source node reaches it in `g`
    fb.values.all (fun y => !nodeF y ||
      match f.value? y with
      | some u => u.args.all fun a => !nodeF a || (nodeG a && depB g nodeG fuel a y)
      | none => false) &&
    -- per value
    fb.values.all (fun x => match f.value? x with
      | some u => u.op == .Phi || valueOK tabs sh f g x
      | none => false) &&
    -- controls of non-`Ret` blocks are unconverted
    (fb.kind == .Ret || fb.controls.all (fun c => !converted f c)) &&
    -- new values
    gb.values.all (fun z => !isNewB f z ||
      match g.value? z with
      | some w => w.op != .Phi && newEvalB tabs g w &&
          w.args.all (fun a => !isNewB f a || gb.values.contains a || (valsOf g g.entry).contains a)
      | none => false)
  | _, _ => false

/-- **The checker**: `g` is `f` after `expand calls`, both read in `tabs`. -/
def ecCheck (tabs : Tables) (f g : Func) : Bool :=
  let sh := typeShapes tabs
  let outs := ownOuts tabs f
  DomCert.cfgView g == DomCert.cfgView f && g.ownAux == f.ownAux &&
    regParamsOK tabs outs &&
    ((leafTys tabs outs).length != outs.length || outs.all (fun p => atom (tabs.ty p.type))) &&
    f.blocks.all (blockOK tabs sh f g)

end GoFV.Opt.ECCheck
