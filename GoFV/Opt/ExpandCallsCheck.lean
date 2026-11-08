import GoFV.Opt.ExpandCalls
import GoFV.Opt.Checked
import GoFV.SSA.Sem.TyEq
import GoFV.SSA.DomCert
import GoFV.Proof.ABIBuild
import GoFV.Opt.TabsAgree
import GoFV.Opt.MemTy
import Std.Data.HashMap.Lemmas

variable [GoFV.SSA.Sem.Addrs]

/-!
# The checker of `expand calls` (`ECCheck.ecCheck`, issue #28)

`ecCheck tabs f g` relates the input `f` of `expand calls` to its output `g` (both read in the
output tables `tabs`) as the conversion simulation `GoFV.Proof.EC.CvRel` needs it: the same
CFG, own aux, block kinds and controls; every value of `f` listed in the same block of `g`; the
same non-pure schedule sequence; every argument of a source node reaching it in `g`; new values
(IDs `f` does not define) pure, frame values or argument pieces, with new arguments in their
block, the entry block or a strict dominator (`placedSDom`); and per source value one of these
classes:

* **identity**: the same op, type, auxint, aux and arguments, none of them a converted value;
* **Arg**: an incoming parameter becomes a Make-tree (`StructMake`, `ArrayMake1`, `SliceMake`,
  `StringMake`, `IMake`, zero-sized parts `Empty`) of new values whose leaves read the
  parameter at the leaf offsets (`ArgIntReg`/`ArgFloatReg {name+off}`, `Arg {name} [off]`);
* **call**: `StaticLECall`/`ClosureLECall`/`InterLECall` become `StaticCall`/`ClosureCall`/
  `InterCall` with the same leading arguments and, per input parameter, its register pieces
  computed by selector chains (`SlicePtr`, `StructSelect [i]`, …) of the Go argument, or for a
  stack-assigned one a chain of new `Store`s of those pieces into its slots of the
  outgoing-arguments area on the call's memory (`stackOK`), the leading ones possibly copied
  by a chain of new `Move`s, one per wide argument `Dereference src mem`, from `src` into its
  slot (`moveOK`; a `Move` above another reads a frame variable, `localSrcOK`); the call's
  type is the register types of its register-assigned results (`regShapeOK`);
* **select**: a register-assigned call result `SelectN [i] c` becomes a Make-tree over
  `SelectN [firstReg + j] c`, a stack-assigned one a Make-tree of `Load`s of its leaf slots
  `OffPtr [off + o] SP` from the call's memory (`stkLeavesOK`); the call's memory
  `SelectN [#outs] c` becomes `SelectN [#pieces] c`;
* **result**: a `MakeResult` becomes the register pieces of the results (selector chains).

Fragment: the function's own results are register-assigned with as many registers as their
shapes have leaves (`regParamsOK`); a converted call's parameters are register-assigned likewise
or stack-assigned in disjoint slots inside the outgoing-arguments area (`insOK`, `outsOK`); no
complex numbers.

Structural recursion and `List` operations only: the checker runs compiled and in the kernel.
-/

namespace GoFV.Opt.ECCheck

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof.ABI

/-! ## Shapes and paths -/

/-- The ops that build a composite of their arguments (`Comp.make`). -/
def isMake : Op → Bool
  | .StructMake | .ArrayMake1 | .SliceMake | .StringMake | .IMake | .ComplexMake => true
  | _ => false

/-- The component a selector picks (`Comp.select`, `Comp.selectAux`). -/
def selIdx? (w : Value) : Option Nat :=
  match w.op with
  | .SlicePtr | .StringPtr | .ITab | .ComplexReal => some 0
  | .SliceLen | .StringLen | .IData | .ComplexImag => some 1
  | .SliceCap => some 2
  | .StructSelect | .ArraySelect => if w.auxInt.toInt < 0 then none else some w.auxInt.toInt.toNat
  | _ => none

mutual
/-- The paths from a value of shape `t` to its register leaves, in `leaves t` order: per step
the field index and the field's shape. -/
def leafPaths : Ty → List (List (Nat × Ty))
  | .agg fs _ => leafPathsFields 0 fs
  | .str => [[(0, .ptr (some 1))], [(1, .int .w64)]]
  | .slice e => [[(0, .ptr e)], [(1, .int .w64)], [(2, .int .w64)]]
  | .empty => []
  | .blob _ => []
  | _ => [[]]
/-- `leafPaths` of fields `i, i+1, …`. -/
def leafPathsFields : Nat → List (Nat × Ty) → List (List (Nat × Ty))
  | _, [] => []
  | i, (_, t) :: fs => (leafPaths t).map ((i, t) :: ·) ++ leafPathsFields (i + 1) fs
end

mutual
/-- A shape with every pointer's element size forgotten: values, `retype`, `encode` and `decode`
do not depend on it. -/
def erase : Ty → Ty
  | .ptr _ => .ptr none
  | .agg fs n => .agg (eraseFields fs) n
  | .slice _ => .slice none
  | .tuple ts => .tuple (eraseList ts)
  | t => t
def eraseFields : List (Nat × Ty) → List (Nat × Ty)
  | [] => []
  | (o, t) :: fs => (o, erase t) :: eraseFields fs
def eraseList : List Ty → List Ty
  | [] => []
  | t :: ts => erase t :: eraseList ts
end

/-- Equal shapes up to pointers' element sizes. -/
def eqE (s t : Ty) : Bool := Ty.beq (erase s) (erase t)

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
      if !eqE (valueTy sh (some w)) t then none else
      match t.asAgg with
      | .agg fs _ =>
        if isMake w.op && w.args.size == fs.length then
          ((fs.zip w.args.toList).mapM fun (e : (Nat × Ty) × ID) =>
            if nw e.2 then mkTree sh g nw n e.2 e.1.2 else none).map List.flatten
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
        selIdx? w == some k && eqE (valueTy sh (some w)) s && w.args.size == 1 &&
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

/-- The leaf shapes of the register-assigned parameters, in register order (a stack-assigned
parameter has no register pieces). -/
def leafTys (tabs : Tables) (ps : List ABIParam) : List Ty :=
  ps.flatMap fun p => if p.regs.isEmpty then [] else (leaves (tabs.ty p.type)).map (·.2)

/-- `t` is a tuple of the shapes `ts` and memory. -/
def tupleOf (ts : List Ty) (t : Ty) : Bool :=
  match t with
  | .tuple us => us.length == ts.length + 1 && (ts.zip us).all (fun (a, b) => eqE b a) &&
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

/-- A shape a register piece may have: an integer, a boolean or a pointer. -/
def scalarTy : Ty → Bool
  | .int _ | .bool | .ptr _ => true
  | _ => false

/-- Some register piece of leaf shape `lt` (in `lts`) stands where `goResults`' Go-typed path
expects a result of a shape `t` (in `ts`) that is no scalar: no value without `poison` has both
shapes (a register holds a scalar, `regShapeOK`), so that path is not taken. -/
def preMismatch : List Ty → List Ty → Bool
  | lt :: lts, t :: ts => (scalarTy lt && !scalarTy t) || preMismatch lts ts
  | _, _ => false

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

/-- `x` is a value the pass invalidated (an argument it no longer uses: `OpInvalid` in `g`; its
conversion is `poison`). -/
def invalidated (g : Func) (x : ID) : Bool :=
  match g.value? x with
  | some w => w.op == .Invalid
  | none => false

/-- `x` is a call result the pass stored to memory leaf by leaf (`rewriteWideSelectToStores`: a
`Store` of a result that is not SSA-able): the source's `SelectN` of a converted call whose node
in `g` is a `SelectN` that no value uses any more (its conversion is `poison`, `wideStoreOK`). -/
def wideSel (f g : Func) (x : ID) : Bool :=
  match f.value? x, g.value? x with
  | some u, some w => u.op == .SelectN && u.args.size == 1 && converted f u.args[0]! &&
      w.op == .SelectN && w.uses == 0
  | _, _ => false

/-- `x`'s conversion is not the identity. -/
def special (f g : Func) (x : ID) : Bool := converted f x || invalidated g x || wideSel f g x

/-- An interface shape: a type word and a pointer-shaped data word. -/
def ifaceShape : Ty → Bool
  | .agg [_, (_, .ptr _)] _ => true
  | _ => false

/-- `IMake` data shortcut (`decomposeAsNecessary`, `expand_calls.go:397`): the data-word piece
`q` of an interface argument `a` (interface-shaped in `g`) whose node in `g` is `IMake tab d` is
not `IData a` but `d` itself (`d` a pointer: the same word) or, when `d` is a one-field
`StructMake`/`ArrayMake1`, its sized part (the source's data word is then `poison`: the
interface shape's data word is a pointer, not an aggregate). -/
def imakeData (sh : Array Ty) (g : Func) (π : List (Nat × Ty)) (q a : ID) : Bool :=
  match π, g.value? a with
  | [(1, _)], some aw =>
    aw.op == .IMake && aw.args.size == 2 && ifaceShape (shapeOf sh g a) &&
      let d := aw.args[1]!
      (d == q && (match shapeOf sh g q with
        | .ptr _ => true
        | _ => false)) ||
      (match g.value? d, shapeOf sh g d with
        | some dw, .agg _ _ => dw.op == .StructMake || dw.op == .ArrayMake1
        | _, _ => false)
  | _, _ => false

/-- An argument of shape `s` passed to a parameter of shape `t` that differs: an `unsafe.Pointer`
(pointer-shaped) argument of a `uintptr` (64-bit integer) parameter, whose register piece is the
pointer itself (the callee reads its word as an integer, `decodeArgs`; the pre-`expand calls`
call retypes it alike, `retypeResults`). -/
def castOK : Ty → Ty → Bool
  | .ptr _, .int .w64 => true
  | _, _ => false

/-- The pieces `pcs` of `g` are, parameter by parameter, the selector chains of the source
values `as` (each of the parameter's shape in `f`, or with `cast` a pointer of a 64-bit integer
parameter, `castOK`), or `IMake` data shortcuts. -/
def piecesOK (tabs : Tables) (sh : Array Ty) (f g : Func) (cast : Bool) :
    List ABIParam → List ID → List ID → Bool
  | [], [], [] => true
  | p :: ps, a :: as, pcs =>
    let t := tabs.ty p.type
    let paths := leafPaths t
    (eqE (shapeOf sh f a) t || cast && castOK (shapeOf sh f a) t) && paths.length ≤ pcs.length &&
      (paths.isEmpty || !special f g a) &&
      (paths.zip (pcs.take paths.length)).all (fun (π, q) =>
        chainOK sh g (isNewB f) π.reverse q a || imakeData sh g π q a) &&
      piecesOK tabs sh f g cast ps as (pcs.drop paths.length)
  | _, _, _ => false

/-! ## Stack-assigned arguments -/

/-- The input parameters with their arguments assigned to registers (`reg = true`) or to the
stack (`reg = false`). -/
def argPairs (reg : Bool) (ps : List ABIParam) (as : List ID) : List (ABIParam × ID) :=
  (ps.zip as).filter fun e => !e.1.regs.isEmpty == reg

mutual
/-- A shape a stack-assigned parameter may have: a well-formed one (`wf`), or one with byte blobs
(arrays) inside, whose bytes a `Move` copies (`moveOK`; `storeArgsOK` needs `wf`). -/
def movTy : Ty → Bool
  | .agg fs n => movFields fs n 0
  | .int _ | .bool | .ptr _ | .opaque _ | .empty | .str | .slice _ | .blob _ => true
  | _ => false
/-- `movTy` of fields in order, disjoint, within the size (as `wfFields`). -/
def movFields : List (Nat × Ty) → Nat → Nat → Bool
  | [], n, start => start ≤ n
  | (o, t) :: fs, n, start => start ≤ o && movTy t && movFields fs n (o + t.size)
end

/-- The input parameters' shapes: a register-assigned one well-formed with as many registers as
leaves, a stack-assigned one `movTy` at a non-negative offset. -/
def insOK (tabs : Tables) (ps : List ABIParam) : Bool :=
  ps.all fun p =>
    if p.regs.isEmpty then movTy (tabs.ty p.type) && decide (0 ≤ p.offset)
    else wf (tabs.ty p.type) && (leaves (tabs.ty p.type)).length == p.regs.size

/-- The stack slots of the parameters `ps` are disjoint, in increasing offset order. -/
def slotsSorted (tabs : Tables) : List ABIParam → Bool
  | p :: q :: ps => decide (p.offset + (tabs.ty p.type).size ≤ q.offset) && slotsSorted tabs (q :: ps)
  | _ => true

/-- The leaf slots (offset in the outgoing-arguments area, shape) of stack parameters `ps`. -/
def leafSlots (tabs : Tables) (ps : List ABIParam) : List (Int × Ty) :=
  ps.flatMap fun p => (leaves (tabs.ty p.type)).map fun (o, lt) => (p.offset + o, lt)

/-- The chain of `Store`s from `z` down to the memory `b`, bottom first: new (`nw`) `Store`
nodes, each on the memory of the one below. -/
def storeChain (g : Func) (nw : ID → Bool) : Nat → ID → ID → Option (List ID)
  | 0, _, _ => none
  | n + 1, z, b =>
    if z == b then some [] else
    match g.value? z with
    | some w =>
      if nw z && w.op == .Store && w.args.size == 3 then
        (storeChain g nw n w.args[2]! b).map (· ++ [z])
      else none
    | none => none

/-- The value a `Store` writes. -/
def storeVal (g : Func) (z : ID) : ID := ((g.value? z).map (·.args[1]!)).getD z

/-- `q` is new `OffPtr [off]` of an `SP` (`OffPtr` pointer-shaped, `SP` a pointer or a
`uintptr`): the address `off` in the outgoing-arguments area. -/
def spOffOK (sh : Array Ty) (g : Func) (nw : ID → Bool) (q : ID) (off : Int) : Bool :=
  nw q && decide (0 ≤ off) && decide (off < 2 ^ 24) &&
    match g.value? q with
    | some w =>
      w.op == .OffPtr && w.auxInt.toInt == off && w.args.size == 1 &&
        (match shapeOf sh g q with
         | .ptr _ => true
         | _ => false) &&
        let s := w.args[0]!
        (match g.value? s with
         | some sw => sw.op == .SP
         | none => false) &&
        (match shapeOf sh g s with
         | .ptr _ | .int .w64 => true
         | _ => false)
    | none => false

/-- The `Store`s `zs` write the leaf slots: per store, the slot's shape at its offset; a store
is a memory. -/
def storesOK (tabs : Tables) (sh : Array Ty) (g : Func) (nw : ID → Bool) :
    List (Int × Ty) → List ID → Bool
  | [], [] => true
  | (off, lt) :: ss, z :: zs =>
    (match g.value? z with
     | some w => eqE (auxTy tabs w.aux) lt && spOffOK sh g nw w.args[0]! off &&
         (match shapeOf sh g z with
          | .mem => true
          | _ => false)
     | none => false) && storesOK tabs sh g nw ss zs
  | _, _ => false

/-- The `SP` under the address of `Store` (or `Move`) `z`. -/
def storeSP (g : Func) (z : ID) : ID :=
  ((g.value? z).bind fun w => (g.value? w.args[0]!).map (·.args[0]!)).getD z

/-- The bottom of the chain of new (`nw`) `Store`s from `z`: the first value below that is not
one. -/
def storeBottom (g : Func) (nw : ID → Bool) : Nat → ID → ID
  | 0, z => z
  | n + 1, z =>
    match g.value? z with
    | some w => if nw z && w.op == .Store && w.args.size == 3 then storeBottom g nw n w.args[2]! else z
    | none => z

/-- The chain of `Move`s from `z` down to the memory `b`, bottom first: new (`nw`) `Move`
nodes, each on the memory of the one below. -/
def moveChain (g : Func) (nw : ID → Bool) : Nat → ID → ID → Option (List ID)
  | 0, _, _ => none
  | n + 1, z, b =>
    if z == b then some [] else
    match g.value? z with
    | some w =>
      if nw z && w.op == .Move && w.args.size == 3 then
        (moveChain g nw n w.args[2]! b).map (· ++ [z])
      else none
    | none => none

/-- The copies of the wide stack arguments of call `u` (in `f`; `w` in `g`), bottom first: the
chain of new `Move`s from the bottom of the target's chain of stores down to the source call's
memory (none if there is no such chain). -/
def callMoves (f g : Func) (u w : Value) : List ID :=
  let b := storeBottom g (isNewB f) (g.valueTab.size + 1) w.args[w.args.size - 1]!
  (moveChain g (isNewB f) (g.valueTab.size + 1) b u.args[u.args.size - 1]!).getD []

/-- The memory the stores of call `u`'s stack arguments start from: its top `Move`, or else the
source call's memory. -/
def callBase (f g : Func) (u w : Value) : ID :=
  (callMoves f g u w).getLast?.getD u.args[u.args.size - 1]!

/-- The `Store`s of the stack arguments of call `u` (in `f`; `w` in `g`): the chain from the
target's memory argument down to `callBase` (empty if they are the same). -/
def callStores (f g : Func) (u w : Value) : Option (List ID) :=
  storeChain g (isNewB f) (g.valueTab.size + 1) w.args[w.args.size - 1]! (callBase f g u w)

/-- The stack parameters `sp` (with their arguments) of call `u`, of well-formed shapes, are
written by the `Store`s `zs` (in leaf order, parameter by parameter, bottom of the chain first):
selector chains of the Go arguments (`piecesOK`; a piece the source defines is one of the call's
arguments) at their slots. -/
def storeArgsOK (tabs : Tables) (sh : Array Ty) (f g : Func) (u : Value)
    (sp : List (ABIParam × ID)) (zs : List ID) : Bool :=
  storesOK tabs sh g (isNewB f) (leafSlots tabs (sp.map (·.1))) zs &&
    piecesOK tabs sh f g false (sp.map (·.1)) (sp.map (·.2)) (zs.map (storeVal g)) &&
    (zs.map (storeVal g)).all (fun q => isNewB f q || u.args.contains q) &&
    sp.all (fun e => wf (tabs.ty e.1.type))

/-- A shape a `Move` of a wide argument copies: not zero-sized `Empty`. -/
def moveTy : Ty → Bool
  | .empty => false
  | _ => true

/-- **The copy of a wide stack argument** `a` (parameter `p` of call `u`) by the `Move` `z`
(`Move {T} [n] (OffPtr [off] SP) src mem`): `a` is `Dereference src mem` of the call's memory
`mem`, of `p`'s shape, and `z` copies `p`'s size into `p`'s slot; `src` is a source value
the pass keeps. -/
def moveOK (tabs : Tables) (sh : Array Ty) (f g : Func) (u : Value) (p : ABIParam) (a z : ID) :
    Bool :=
  let t := tabs.ty p.type
  match g.value? z, f.value? a with
  | some mw, some au =>
    mw.args.size == 3 && spOffOK sh g (isNewB f) mw.args[0]! p.offset &&
      mw.auxInt.toInt == (t.size : Int) &&
      (match shapeOf sh g z with
       | .mem => true
       | _ => false) &&
      au.op == .Dereference && au.args.size == 2 && au.args[0]! == mw.args[1]! &&
      au.args[1]! == u.args[u.args.size - 1]! &&
      eqE (shapeOf sh f a) t && moveTy t && !isNewB f mw.args[1]! && !special f g mw.args[1]!
  | _, _ => false

/-- The memory and the source of `Move` `z`. -/
def moveMem (g : Func) (z : ID) : ID := ((g.value? z).map (·.args[2]!)).getD z
def moveSrc (g : Func) (z : ID) : ID := ((g.value? z).map (·.args[1]!)).getD z

/-- The source of `Move` `z` is a pointer-shaped `LocalAddr`: a frame variable, outside the
outgoing-arguments area that the `Move`s below `z` wrote. -/
def localSrcOK (sh : Array Ty) (g : Func) (z : ID) : Bool :=
  match g.value? (moveSrc g z) with
  | some sw => sw.op == .LocalAddr && sw.aux.isSome &&
      (match shapeOf sh g (moveSrc g z) with
       | .ptr _ => true
       | _ => false)
  | none => false

/-- The stack arguments of call `u`: the `Store`s of `storeArgsOK`, below them for the leading
stack parameters their `Move`s (`moveOK`, one per parameter, bottom first; a `Move` above
another reads a frame variable, `localSrcOK`); the slots are disjoint. -/
def stackOK (tabs : Tables) (sh : Array Ty) (f g : Func) (u w : Value) (ins : List ABIParam)
    (as : List ID) : Bool :=
  let sp := argPairs false ins as
  let ms := callMoves f g u w
  slotsSorted tabs (sp.map (·.1)) && decide (ms.length ≤ sp.length) &&
  ((sp.take ms.length).zip ms).all (fun e => moveOK tabs sh f g u e.1.1 e.1.2 e.2) &&
  ms.all (fun z => moveMem g z == u.args[u.args.size - 1]! || localSrcOK sh g z) &&
  match callStores f g u w with
  | some zs => storeArgsOK tabs sh f g u (sp.drop ms.length) zs
  | none => false

/-! ## Stack-assigned results -/

/-- The result parameters' shapes: a register-assigned one well-formed with as many registers as
leaves, a stack-assigned one (any shape: the call writes its encoding into its slot, and the
source reads it back by its address, `SelectNAddr`, or by `selectOK`'s leaf loads, which need
`wf`) a slot inside the outgoing-arguments area's window; the stack slots disjoint, in
increasing offset order. -/
def outsOK (tabs : Tables) (ps : List ABIParam) : Bool :=
  ps.all (fun p =>
    (if p.regs.isEmpty then decide (0 ≤ p.offset) && decide (p.offset + (tabs.ty p.type).size < 2 ^ 24)
     else wf (tabs.ty p.type) && (leaves (tabs.ty p.type)).length == p.regs.size)) &&
    slotsSorted tabs (ps.filter (·.regs.isEmpty))

/-- Value `m` of `g` is the memory of call `c` with `k` register pieces: `SelectN [k] c` of shape
`mem`. -/
def memSelOK (sh : Array Ty) (g : Func) (c : ID) (k : Nat) (m : ID) : Bool :=
  match g.value? m with
  | some mw => mw.op == .SelectN && mw.args.toList == [c] && mw.auxInt.toInt == (k : Int) &&
      (match shapeOf sh g m with
       | .mem => true
       | _ => false)
  | none => false

/-- The leaves `ls` of the Make-tree of a stack-assigned call result at offset `off` read their
leaf slots (leaf offsets and shapes `os`) from the call's memory: `Load (OffPtr [off + o] SP) m`
with `m` the call `c`'s memory (`k` register pieces). -/
def stkLeavesOK (sh : Array Ty) (g : Func) (nw : ID → Bool) (c : ID) (k : Nat) (off : Int) :
    List (Nat × Ty) → List ID → Bool
  | [], [] => true
  | (o, _) :: os, l :: ls =>
    (match g.value? l with
     | some w => w.op == .Load && w.args.size == 2 && spOffOK sh g nw w.args[0]! (off + o) &&
         memSelOK sh g c k w.args[1]!
     | none => false) && stkLeavesOK sh g nw c k off os ls
  | _, _ => false

/-! ## Wide call results stored to memory -/

/-- The address of the leaf at offset `o` of a wide store at `p`: `p` itself (offset 0) or a new
pointer-shaped `OffPtr [o] p`. -/
def wideAddrOK (sh : Array Ty) (g : Func) (nw : ID → Bool) (p : ID) (o : Nat) (a : ID) : Bool :=
  (o == 0 && a == p) ||
    (nw a && match g.value? a with
      | some aw => aw.op == .OffPtr && aw.auxInt.toInt == (o : Int) && aw.args.toList == [p] &&
          (match shapeOf sh g a with
           | .ptr _ => true
           | _ => false)
      | none => false)

/-- The value of a leaf store of a wide store: the new register piece `SelectN [k] c` of the
leaf's shape. -/
def wideValOK (sh : Array Ty) (g : Func) (nw : ID → Bool) (c : ID) (k : Nat) (lt : Ty) (q : ID) :
    Bool :=
  nw q && match g.value? q with
    | some qw => qw.op == .SelectN && qw.args.toList == [c] && qw.auxInt.toInt == (k : Int) &&
        eqE (shapeOf sh g q) lt
    | none => false

/-- The `Store`s `zs` (bottom of the chain first) of a wide store of call `c`'s result (first
register piece `first`) at `p`: per leaf `(o, lt)` (the `j`-th), a `Store {lt}` of shape `mem` of
`SelectN [first + j] c` at `p + o`. -/
def wideLeavesOK (tabs : Tables) (sh : Array Ty) (g : Func) (nw : ID → Bool) (p c : ID)
    (first : Nat) : Nat → List (Nat × Ty) → List ID → Bool
  | _, [], [] => true
  | j, (o, lt) :: ls, z :: zs =>
    (match g.value? z with
     | some zw => decide (0 < lt.size) && eqE (auxTy tabs zw.aux) lt &&
         (match shapeOf sh g z with
          | .mem => true
          | _ => false) &&
         wideAddrOK sh g nw p o zw.args[0]! && wideValOK sh g nw c (first + j) lt zw.args[1]!
     | none => false) && wideLeavesOK tabs sh g nw p c first (j + 1) ls zs
  | _, _, _ => false

/-- The chain of `Store`s that replaced the source's `Store` `u` (its node `w` in `g` a `Copy` of
the chain's top) down to `u`'s memory; none for other values. -/
def wideChain (f g : Func) (u w : Value) : Option (List ID) :=
  if u.op == .Store && w.op == .Copy && u.args.size == 3 && w.args.size == 1 then
    storeChain g (isNewB f) (g.valueTab.size + 1) w.args[0]! u.args[2]!
  else none

/-! ## Stack-assigned own results -/

/-- `p` is a new pointer-shaped `LocalAddr {n}` (`expand calls` addresses result `n`'s frame
slot by one per result). -/
def localAddrOK (sh : Array Ty) (g : Func) (nw : ID → Bool) (n : AuxRef) (p : ID) : Bool :=
  nw p && match g.value? p with
    | some pw => pw.op == .LocalAddr && pw.aux == some n &&
        (match shapeOf sh g p with
         | .ptr _ => true
         | _ => false)
    | none => false

/-- The base of the address `a` of the leaf at offset `o` of a result's slot: `a` itself at
offset 0, else the pointer `a` offsets (`wideAddrOK`). -/
def resBase (g : Func) (o : Nat) (a : ID) : ID :=
  if o == 0 then a else ((g.value? a).map (·.args[0]!)).getD a

/-- The leaf slots of the stack-assigned results `ps`: per result (its name) and leaf. -/
def resSlots (tabs : Tables) (ps : List ABIParam) : List (AuxRef × Nat × Ty) :=
  ps.flatMap fun p => match p.name with
    | some n => (leaves (tabs.ty p.type)).map fun (o, lt) => (n, o, lt)
    | none => []

/-- The `Store`s `zs` (bottom of the chain first) write the leaf slots `ss`: per slot `(n, o, lt)`
(`lt` not empty) a `Store {lt}` of shape `mem` at `LocalAddr {n}` plus `o` (`wideAddrOK`). -/
def resStoresOK (tabs : Tables) (sh : Array Ty) (g : Func) (nw : ID → Bool) :
    List (AuxRef × Nat × Ty) → List ID → Bool
  | [], [] => true
  | (n, o, lt) :: ss, z :: zs =>
    (match g.value? z with
     | some w => decide (0 < lt.size) && eqE (auxTy tabs w.aux) lt &&
         localAddrOK sh g nw n (resBase g o w.args[0]!) &&
         wideAddrOK sh g nw (resBase g o w.args[0]!) o w.args[0]! &&
         (match shapeOf sh g z with
          | .mem => true
          | _ => false)
     | none => false) && resStoresOK tabs sh g nw ss zs
  | _, _ => false

/-- The `Store`s of the stack-assigned results of `MakeResult` `u` (in `f`; `w` in `g`): the
chain from the target's memory argument down to the source's (empty if they are the same). -/
def resStores (f g : Func) (u w : Value) : Option (List ID) :=
  storeChain g (isNewB f) (g.valueTab.size + 1) w.args[w.args.size - 1]! u.args[u.args.size - 1]!

/-- **A self-move**: the argument `a` of `MakeResult` `u` for the stack-assigned result `p` is
`Dereference (LocalAddr {n}) mem` of `p`'s own slot `n` (a pointer-shaped `LocalAddr`) on `u`'s
memory, of `p`'s shape (not zero-sized, `moveTy`), and the pass invalidated it
(`rewriteFuncResults` skips it: the slot already holds the result, so no store). -/
def selfMoveOK (tabs : Tables) (sh : Array Ty) (f g : Func) (u : Value) (e : ABIParam × ID) :
    Bool :=
  invalidated g e.2 && moveTy (tabs.ty e.1.type) && moveTy (shapeOf sh f e.2) &&
  match e.1.name, f.value? e.2 with
  | some n, some au =>
    au.op == .Dereference && au.args.size == 2 && au.args[1]! == u.args[u.args.size - 1]! &&
      eqE (shapeOf sh f e.2) (tabs.ty e.1.type) &&
      (match shapeOf sh f au.args[0]! with
       | .ptr _ => true
       | _ => false) &&
      match f.value? au.args[0]! with
      | some pu => pu.op == .LocalAddr && pu.aux == some n
      | none => false
  | _, _ => false

/-- Per result of `MakeResult` `u` (with arguments `as`), whether it is a stack-assigned
self-move (`selfMoveOK`). -/
def selfMoves (tabs : Tables) (sh : Array Ty) (f g : Func) (u : Value) (ps : List ABIParam)
    (as : List ID) : List Bool :=
  (ps.zip as).map fun e => e.1.regs.isEmpty && selfMoveOK tabs sh f g u e

/-- The frame variables of `f` in `tabs` (`Ctx.locals`). -/
def localsOf (tabs : Tables) (f : Func) : Array (AuxRef × Nat × Option Nat) :=
  frameLocals tabs (((abiParams tabs f).filter (!·.out)).map (·.name))

/-- The frame slot of the stack-assigned own result `p`: a `movTy` shape (byte blobs allowed:
a result that is only ever a self-move is read back as bytes; a stored one needs `wf`,
`resultOK`) inside the frame blocks' window, a name that is a `Blk.local` (`forgeable`),
allocated by the frame (`locals`) with at least `p`'s size wherever it is listed. -/
def resSlotOK (tabs : Tables) (locals : Array (AuxRef × Nat × Option Nat)) (p : ABIParam) : Bool :=
  let t := tabs.ty p.type
  movTy t && decide (t.size < 2 ^ 24) &&
    match p.name with
    | some n => tabs.forgeable n && locals.any (·.1 == n) &&
        locals.all (fun e => e.1 != n || decide (t.size ≤ e.2.1))
    | none => false

/-- No name occurs twice. -/
def namesDistinct : List (Option AuxRef) → Bool
  | [] => true
  | n :: ns => !ns.contains n && namesDistinct ns

/-- **The function's own results**: register-assigned with as many registers as their shapes
have leaves (`regParamsOK`), or, with stack-assigned ones, each register-assigned one so and
each stack-assigned one in its frame slot (`resSlotOK`, distinct names), fewer or more register
pieces than results or a scalar piece where a result is no scalar (`preMismatch`: `goResults`
then reads the slots), and memories only in memory ops (`WBCheck.memTyOK`: the source run's
memories keep the slots, `EC.EcQ`). -/
def ownOutsOK (tabs : Tables) (f : Func) : Bool :=
  let outs := ownOuts tabs f
  regParamsOK tabs outs ||
    (outs.all (fun p => if p.regs.isEmpty then resSlotOK tabs (localsOf tabs f) p
        else wf (tabs.ty p.type) && (leaves (tabs.ty p.type)).length == p.regs.size) &&
      namesDistinct ((outs.filter (·.regs.isEmpty)).map (·.name)) &&
      ((leafTys tabs outs).length != outs.length ||
        preMismatch (leafTys tabs outs) (outs.map (tabs.ty ·.type))) &&
      WBCheck.memTyOK tabs f)

/-! ## The classes of source values -/

/-- **call**: `u` (in `f`) and `w` (in `g`) at the same ID. -/
def callOK (tabs : Tables) (sh : Array Ty) (f g : Func) (u w : Value) : Bool :=
  match callOpMap u.op, callABI? tabs u.aux with
  | some (op, k), some abi =>
    let ins := insOf abi
    let outs := outsOf abi
    let n := u.args.size
    let as := (u.args.extract k (n - 1)).toList
    let rp := argPairs true ins as
    w.op == op && w.aux == u.aux && 0 < n && k + 1 ≤ n &&
      outsOK tabs outs && insOK tabs ins && ins.length == as.length &&
      w.args.size ≥ k + 1 &&
      (w.args.extract 0 k).toList == (u.args.extract 0 k).toList &&
      stackOK tabs sh f g u w ins as &&
      (u.args.extract 0 k).toList.all (fun a => !special f g a) && !special f g u.args[n - 1]! &&
      piecesOK tabs sh f g true (rp.map (·.1)) (rp.map (·.2)) (w.args.extract k (w.args.size - 1)).toList &&
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
       | .ArgIntReg | .ArgFloatReg =>
         match w.aux.bind tabs.aux? with
         | some { kind := .nameOff n' off', .. } => n' == n && off' == off + o
         | _ => false
       | .Arg => w.aux == some n && w.auxInt.toInt == off + o
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
          eqE (shapeOf sh f x) t &&
            match mkTree sh g (isNewB f) (tabs.types.size + 1) x t with
            | some ls => ls.length == (leaves t).length &&
                if p.regs.isEmpty then
                  wf t && stkLeavesOK sh g (isNewB f) c (leafTys tabs outs).length p.offset (leaves t) ls
                else selLeavesOK g c first 0 ls
            | none => false
        | none => false
    | none => false
  | _ => false

/-- The result `i` of the call `c` of `f` is stack-assigned: its assignment if so. -/
def stackOut? (tabs : Tables) (f : Func) (c : ID) (i : Int64) : Option ABIParam :=
  match f.value? c with
  | some cu =>
    if (callOpMap cu.op).isSome && decide (0 ≤ i.toInt) then
      match (callOuts tabs cu.aux)[i.toInt.toNat]? with
      | some p => if p.regs.isEmpty then some p else none
      | none => none
    else none
  | none => none

/-- `u` is the address `SelectNAddr [i] c` of a stack-assigned result of a converted call `c`. -/
def selAddr (tabs : Tables) (f : Func) (u : Value) : Bool :=
  u.op == .SelectNAddr && u.args.size == 1 && (stackOut? tabs f u.args[0]! u.auxInt).isSome

/-- **result address**: `u = SelectNAddr [i] c` (`selAddr`) became `Copy q` of the same type
(`rewriteSelectOrArg`'s `offsetFrom(SP, OffsetOfResult)`), `q` a new `OffPtr [off] SP` at the
result's slot (`spOffOK`) of an `SP` of shape `uintptr`: both evaluate to the slot's address
word (`Ptr.word`). -/
def selAddrOK (tabs : Tables) (sh : Array Ty) (f g : Func) (u w : Value) : Bool :=
  match stackOut? tabs f u.args[0]! u.auxInt with
  | some p =>
    w.op == .Copy && w.type == u.type && w.args.size == 1 &&
      spOffOK sh g (isNewB f) w.args[0]! p.offset &&
      (match g.value? w.args[0]! with
       | some qw => (match shapeOf sh g qw.args[0]! with
           | .int .w64 => true
           | _ => false)
       | none => false)
  | none => false

/-- **result**: a `MakeResult` of the function's results becomes the register pieces of its
register-assigned results (selector chains) on a chain of new `Store`s of the leaves of its
stored stack-assigned results into their frame slots (`resStoresOK`; well-formed shapes, the
stored values selector chains of the results, or an `IMake` result's data operand) on the
source's memory; a self-moved stack-assigned result (`selfMoveOK`) is stored by nothing. -/
def resultOK (tabs : Tables) (sh : Array Ty) (f g : Func) (u w : Value) : Bool :=
  let outs := ownOuts tabs f
  let n := u.args.size
  let as := (u.args.extract 0 (n - 1)).toList
  let rp := argPairs true outs as
  let sp := (argPairs false outs as).filter fun e => !selfMoveOK tabs sh f g u e
  w.op == .MakeResult && n == outs.length + 1 && w.args.size ≥ 1 &&
    !special f g u.args[n - 1]! &&
    piecesOK tabs sh f g false (rp.map (·.1)) (rp.map (·.2))
      (w.args.extract 0 (w.args.size - 1)).toList &&
    sp.all (fun e => wf (tabs.ty e.1.type)) &&
    (match resStores f g u w with
     | some zs =>
       resStoresOK tabs sh g (isNewB f) (resSlots tabs (sp.map (·.1))) zs &&
         piecesOK tabs sh f g false (sp.map (·.1)) (sp.map (·.2)) (zs.map (storeVal g))
     | none => false) &&
    tupleOf (outs.map (tabs.ty ·.type)) (valueTy sh (some u)) &&
    regTupleOf (leafTys tabs outs) (valueTy sh (some w))

/-- **wide store**: a `Store {T} p x mem` of a wide call result `x = SelectN [i] c` (`wideSel`)
became a `Copy` of a chain of new leaf `Store`s on `mem` (`wideLeavesOK`): `x`'s result is
register-assigned with a well-formed shape `T`, `p` and `mem` keep their conversions. -/
def wideStoreOK (tabs : Tables) (sh : Array Ty) (f g : Func) (u w : Value) : Bool :=
  w.type == u.type && (match valueTy sh (some u) with
    | .mem => true
    | _ => false) &&
  wideSel f g u.args[1]! && !special f g u.args[0]! && !special f g u.args[2]! &&
  match wideChain f g u w, f.value? u.args[1]! with
  | some zs, some xu =>
    match f.value? xu.args[0]! with
    | some cu =>
      let outs := callOuts tabs cu.aux
      let i := xu.auxInt.toInt.toNat
      (callOpMap cu.op).isSome && decide (0 ≤ xu.auxInt.toInt) &&
      match outs[i]? with
      | some pp =>
        let t := tabs.ty pp.type
        !pp.regs.isEmpty && wf t && eqE (auxTy tabs u.aux) t && eqE (shapeOf sh f u.args[1]!) t &&
          wideLeavesOK tabs sh g (isNewB f) u.args[0]! xu.args[0]! (leafTys tabs (outs.take i)).length
            0 (leaves t) zs
      | none => false
    | none => false
  | _, _ => false

/-- Two `Phi`s that evaluate alike (`EC.PhiSame`): the same op, arguments and type. -/
def sameV (u w : Value) : Bool := w.op == u.op && w.args == u.args && w.type == u.type

/-- **identity**. -/
def identOK (f g : Func) (u w : Value) : Bool :=
  (w.op == u.op || (u.op == .Dereference && w.op == .Load)) && w.type == u.type &&
    w.auxInt == u.auxInt && w.aux == u.aux && w.args == u.args &&
    u.args.all (fun a => !special f g a)

/-- The pre-`expand calls` tail calls, outside the semantics' phases: their evaluation is
`stuck`, so no source register ever holds one. -/
def tailOp : Op → Bool
  | .TailLECall | .TailLECallInter => true
  | _ => false

/-- `a` is a tail call of `f`. -/
def isTail (f : Func) (a : ID) : Bool :=
  match f.value? a with
  | some u => tailOp u.op
  | none => false

/-- The class check of non-`Phi` source value `x`. A tail call (stuck in the source) and a value
reading one (never evaluated by the source) are accepted with any target node. -/
def valueOK (tabs : Tables) (sh : Array Ty) (f g : Func) (x : ID) : Bool :=
  match f.value? x, g.value? x with
  | some u, some w =>
    if (callOpMap u.op).isSome then callOK tabs sh f g u w
    else if u.op == .MakeResult then resultOK tabs sh f g u w
    else if tailOp u.op || u.args.any (isTail f) then true
    else if wideSel f g x then true
    else if u.op == .SelectN && u.args.size == 1 && converted f u.args[0]! then
      selectOK tabs sh f g x u w
    else if u.op == .Store && w.op == .Copy then wideStoreOK tabs sh f g u w
    else if w.op == .Invalid then Sem.prio u.op == 0 && u.op != .Phi
    else if selAddr tabs f u then selAddrOK tabs sh f g u w
    else if u.op == .Arg && !identOK f g u w then argOK tabs sh f g x u
    else identOK f g u w
  | _, _ => false

/-! ## Blocks -/

/-- `y` depends on `a` through arguments that are nodes of `gb` (`Order.Dep`), searching
through new nodes (`nw`) only. -/
def depB (g : Func) (node nw : ID → Bool) : Nat → ID → ID → Bool
  | 0, _, _ => false
  | n + 1, a, y =>
    node y &&
      match g.value? y with
      | some w => w.args.any fun z => node z && (z == a || (nw z && depB g node nw n a z))
      | none => false

/-! `depB` searches every path back from `y`, which is exponential in a block whose values share
arguments (a `--check --verified` run spent 90 min on `cmd/compile/internal/walk.maplit`).
`depBFast` (`@[csimp] depB_eq_depBFast`) is the same search with a table of failures: `M[z]? =
some m` records `depB m a z = false`, so `z` is skipped with any fuel `≤ m` (`depB_mono`). -/

theorem depB_mono {g : Func} {node nw : ID → Bool} {a : ID} :
    ∀ {n : Nat} {y : ID}, depB g node nw n a y = true → depB g node nw (n + 1) a y = true
  | 0, _, h => by simp [depB] at h
  | n + 1, y, h => by
    rw [depB] at h ⊢
    simp only [Bool.and_eq_true] at h ⊢
    refine ⟨h.1, ?_⟩
    revert h
    cases g.value? y with
    | none => simp
    | some w =>
      simp only [Array.any_eq_true, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq]
      rintro ⟨-, i, hi, hz, hd⟩
      exact ⟨i, hi, hz, hd.imp id fun h => ⟨h.1, depB_mono h.2⟩⟩

theorem depB_mono_le {g : Func} {node nw : ID → Bool} {a z : ID} {n m : Nat} (hnm : n ≤ m)
    (h : depB g node nw n a z = true) : depB g node nw m a z = true := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact depB_mono ih

theorem depB_false_le {g : Func} {node nw : ID → Bool} {a z : ID} {n m : Nat} (hnm : n ≤ m)
    (h : depB g node nw m a z = false) : depB g node nw n a z = false := by
  cases hd : depB g node nw n a z
  · rfl
  · exact absurd (depB_mono_le hnm hd) (by simp [h])

/-- The failure table's invariant. -/
def DepMemoOK (g : Func) (node nw : ID → Bool) (a : ID) (M : Std.HashMap ID Nat) : Prop :=
  ∀ z m, M[z]? = some m → depB g node nw m a z = false

/-- `zs.any` of `depB`'s argument test at fuel `n`, `rec` the search one level down. -/
def depBArgs (node nw : ID → Bool) (a : ID) (n : Nat)
    (rec : ID → Std.HashMap ID Nat → Bool × Std.HashMap ID Nat) :
    List ID → Std.HashMap ID Nat → Bool × Std.HashMap ID Nat
  | [], M => (false, M)
  | z :: zs, M =>
    if node z && z == a then (true, M)
    else if node z && nw z && !(M[z]?.any (n ≤ ·)) then
      let r := rec z M
      if r.1 then (true, r.2) else depBArgs node nw a n rec zs r.2
    else depBArgs node nw a n rec zs M

/-- `depB` with the failure table `M`. -/
def depBMemo (g : Func) (node nw : ID → Bool) (a : ID) :
    Nat → ID → Std.HashMap ID Nat → Bool × Std.HashMap ID Nat
  | 0, _, M => (false, M)
  | n + 1, y, M =>
    if node y then
      match g.value? y with
      | some w =>
        let r := depBArgs node nw a n (depBMemo g node nw a n) w.args.toList M
        (r.1, if r.1 then r.2 else r.2.insert y (n + 1))
      | none => (false, M)
    else (false, M)

def depBFast (g : Func) (node nw : ID → Bool) (n : Nat) (a y : ID) : Bool :=
  (depBMemo g node nw a n y {}).1

theorem depBArgs_spec {g : Func} {node nw : ID → Bool} {a : ID} {n : Nat}
    {rec : ID → Std.HashMap ID Nat → Bool × Std.HashMap ID Nat}
    (hrec : ∀ z M, DepMemoOK g node nw a M →
      (rec z M).1 = depB g node nw n a z ∧ DepMemoOK g node nw a (rec z M).2) :
    ∀ (zs : List ID) (M : Std.HashMap ID Nat), DepMemoOK g node nw a M →
      (depBArgs node nw a n rec zs M).1 =
          zs.any (fun z => node z && (z == a || (nw z && depB g node nw n a z))) ∧
        DepMemoOK g node nw a (depBArgs node nw a n rec zs M).2
  | [], M, hM => ⟨rfl, hM⟩
  | z :: zs, M, hM => by
    have ih := depBArgs_spec hrec zs
    unfold depBArgs
    by_cases h1 : (node z && z == a) = true
    · simp only [h1, ↓reduceIte, List.any_cons]
      simp only [Bool.and_eq_true, beq_iff_eq] at h1
      obtain ⟨hz, rfl⟩ := h1
      simp [hz, hM]
    · simp only [h1, Bool.false_eq_true, ↓reduceIte, List.any_cons]
      by_cases h2 : (node z && nw z && !(M[z]?.any (n ≤ ·))) = true
      · simp only [h2, ↓reduceIte]
        obtain ⟨hr1, hr2⟩ := hrec z M hM
        cases hr : (rec z M).1
        · simp only [Bool.false_eq_true, ↓reduceIte]
          obtain ⟨i1, i2⟩ := ih _ hr2
          refine ⟨?_, i2⟩
          rw [i1, ← hr1, hr]
          simp only [Bool.and_eq_true, beq_iff_eq] at h1
          cases hz : node z <;> simp_all
        · simp only [↓reduceIte]
          refine ⟨?_, hr2⟩
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at h2
          rw [← hr1, hr]; simp [h2.1.1, h2.1.2]
      · simp only [h2, Bool.false_eq_true, ↓reduceIte]
        obtain ⟨i1, i2⟩ := ih M hM
        refine ⟨?_, i2⟩
        rw [i1]
        have hf : (node z && (z == a || (nw z && depB g node nw n a z))) = false := by
          cases hz : node z
          · rfl
          · cases hza : (z == a)
            · cases hn : nw z
              · rfl
              · cases hm : M[z]? with
                | none => simp [hz, hn, hm] at h2
                | some m =>
                  have hle : n ≤ m := by simpa [hz, hn, hm] using h2
                  simp [depB_false_le hle (hM z m hm)]
            · simp [hz, hza] at h1
        simp [hf]

theorem depBMemo_spec {g : Func} {node nw : ID → Bool} {a : ID} :
    ∀ (n : Nat) (y : ID) (M : Std.HashMap ID Nat), DepMemoOK g node nw a M →
      (depBMemo g node nw a n y M).1 = depB g node nw n a y ∧
        DepMemoOK g node nw a (depBMemo g node nw a n y M).2
  | 0, _, M, hM => ⟨rfl, hM⟩
  | n + 1, y, M, hM => by
    unfold depBMemo
    rw [depB]
    cases hy : node y
    · exact ⟨rfl, hM⟩
    · simp only [↓reduceIte, Bool.true_and]
      cases hw : g.value? y with
      | none => exact ⟨rfl, hM⟩
      | some w =>
        obtain ⟨h1, h2⟩ := depBArgs_spec (fun z M hM => depBMemo_spec n z M hM) w.args.toList M hM
        refine ⟨by rw [h1, Array.any_toList], ?_⟩
        dsimp only
        split
        · exact h2
        · rename_i hf
          intro z m hz
          rw [Std.HashMap.getElem?_insert] at hz
          split at hz
          · rename_i hzy
            have : y = z := by simpa using hzy
            subst this
            cases hz
            rw [depB, hy, hw, Bool.true_and]
            dsimp only
            rw [← Array.any_toList, ← h1]
            simpa using hf
          · exact h2 z m hz

@[csimp] theorem depB_eq_depBFast : @depB = @depBFast := by
  funext g node nw n a y
  exact ((depBMemo_spec n y {} (fun z m h => by simp at h)).1).symm

/-- Source mode of `imkArgOK` (`aw` the `IMake` node of `a` in `g`): `a` is the same
interface-shaped `IMake` in `f`, its data operand `d` is unconverted, a pointer or an aggregate
in both, and when `a` is a value of `fb`, `x` depends on it in `g` (`EC.Held`: the source
register of `a` holds its evaluation when `x` is evaluated; outside `fb`, `a` is placed in a
strict dominator). -/
def imkSrcOK (sh : Array Ty) (f g : Func) (fb : Block) (node : ID → Bool) (fuel : Nat)
    (aw : Value) (a x : ID) : Bool :=
  match f.value? a with
  | some au =>
    au.op == .IMake && au.args.size == 2 && au.args[1]! == aw.args[1]! &&
      ifaceShape (shapeOf sh f a) && !special f g aw.args[1]! &&
      (match shapeOf sh f aw.args[1]!, shapeOf sh g aw.args[1]! with
       | .ptr _, .ptr _ => true
       | .agg _ _, .agg _ _ => true
       | _, _ => false) &&
      (!fb.values.contains a || depB g node (fun _ => true) fuel a x)
  | none => false

/-- `z` is a non-`Phi` value of `g` listed in its block, a strict dominator of block `bid`
(`anc`: the ancestor test of `g`'s dominator certificate, `DomCert.Cert.anc`). Its target
register holds its evaluation in block `bid` (lemma (D), `Avail.DInv`). -/
def placedSDom (g : Func) (anc : ID → ID → Bool) (bid z : ID) : Bool :=
  match g.value? z with
  | some w =>
    w.op != .Phi && w.block != bid && g.blocks.contains w.block &&
      (match g.block? w.block with
       | some b => b.values.contains z
       | none => false) &&
      anc w.block bid
  | none => false

/-- Target mode of `imkArgOK`: `a` is interface-shaped in `g`, and `a` and its data operand are
placed in strict dominators of `x`'s block `bid` or `x` depends on them in `g` (their target
registers hold their evaluations). The placement test comes first: a failing `depB` search
explores every path. -/
def imkTgtOK (sh : Array Ty) (g : Func) (anc : ID → ID → Bool) (bid : ID) (node : ID → Bool)
    (fuel : Nat) (aw : Value) (a x : ID) : Bool :=
  ifaceShape (shapeOf sh g a) &&
    (placedSDom g anc bid a || depB g node (fun _ => true) fuel a x) &&
    (placedSDom g anc bid aw.args[1]! || depB g node (fun _ => true) fuel aw.args[1]! x)

/-- An argument `a` of a converted value `x` of block `fb` whose node in `g` is an `IMake` (whose
data word the `IMake` shortcut may pass directly; `EC.ec_imake`) in source or target mode. -/
def imkArgOK (sh : Array Ty) (f g : Func) (anc : ID → ID → Bool) (fb : Block) (node : ID → Bool)
    (fuel : Nat) (a x : ID) : Bool :=
  match g.value? a with
  | some aw => aw.op != .IMake || (aw.args.size == 2 &&
      (imkSrcOK sh f g fb node fuel aw a x || imkTgtOK sh g anc fb.id node fuel aw a x))
  | none => true

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
  | .SP | .GetCallerSP | .SB | .LocalAddr | .OffPtr | .SelectN | .Empty | .ArgFloatReg
  | .StructMake | .ArrayMake1 | .SliceMake | .StringMake | .IMake | .ComplexMake
  | .ComplexReal | .ComplexImag
  | .SlicePtr | .SliceLen | .SliceCap | .StringPtr | .StringLen | .ITab | .IData
  | .StructSelect | .ArraySelect | .Load => true
  | _ => false

/-- The memory argument of value `x` of `f`. -/
def callMem (f : Func) (x : ID) : ID := ((f.value? x).map fun u => u.args[u.args.size - 1]!).getD x

/-- The `Move`s of the wide stack arguments of value `x` of `f` (`callMoves`; none unless `x` is
a call). -/
def stackMoves (f g : Func) (x : ID) : List ID :=
  match f.value? x, g.value? x with
  | some u, some w => if (callOpMap u.op).isSome then callMoves f g u w else []
  | _, _ => []

/-- The stack-argument `Store`s of value `x` of `f` (`callStores`; none unless `x` is a call),
and its `Move`s (`stackMoves`). -/
def stackStores (f g : Func) (x : ID) : List ID :=
  (match f.value? x, g.value? x with
   | some u, some w => if (callOpMap u.op).isSome then (callStores f g u w).getD [] else []
   | _, _ => []) ++ stackMoves f g x

/-- `a` may be the `Dereference` that a `Move` of call `y`'s wide stack arguments copies
(`moveOK`): `y` has a `Move` and `a` is a `Dereference`. The target does not read `a`. -/
def moveArgB (f g : Func) (y a : ID) : Bool :=
  !(stackMoves f g y).isEmpty && ((f.value? a).map (·.op == .Dereference)).getD false

/-- `a` is pure in `f` and its arguments that are nodes of the block (`nodeF`) reach `y` in `g`
(`Order.Feeds.through`). -/
def throughB (f g : Func) (nodeF nodeG : ID → Bool) (fuel : Nat) (a y : ID) : Bool :=
  match f.value? a with
  | some au => Sem.prio au.op == 0 &&
      au.args.all fun b => !nodeF b || (nodeG b && depB g nodeG (fun _ => true) fuel b y)
  | none => false

/-- `a` occurs in `l`, and `y` after its first occurrence. -/
def beforeB : List ID → ID → ID → Bool
  | [], _, _ => false
  | z :: l, a, y => if z == a then l.contains y else beforeB l a y

/-- The leaf `Store`s that replaced the source's `Store` `x` (`wideChain`); none for other
values and for a `Store` reading a tail call (`valueOK` accepts it without `wideStoreOK`). -/
def wideStores (f g : Func) (x : ID) : List ID :=
  match f.value? x, g.value? x with
  | some u, some w => if u.args.any (isTail f) then [] else (wideChain f g u w).getD []
  | _, _ => []

/-- The result `Store`s of value `x` of `f` (`resStores`); none unless `x` is a `MakeResult`. -/
def ownStores (f g : Func) (x : ID) : List ID :=
  match f.value? x, g.value? x with
  | some u, some w => if u.op == .MakeResult then (resStores f g u w).getD [] else []
  | _, _ => []

/-- The address argument of value `x` of `f`. -/
def addrArg (f : Func) (x : ID) : ID := ((f.value? x).map (·.args[0]!)).getD x

/-- The `LocalAddr`s that the self-moves of value `x` of `f` read (`selfMoveOK`); none unless `x`
is a `MakeResult`. -/
def selfAddrs (tabs : Tables) (sh : Array Ty) (f g : Func) (x : ID) : List ID :=
  match f.value? x with
  | some u =>
    if u.op == .MakeResult then
      (((argPairs false (ownOuts tabs f) (u.args.extract 0 (u.args.size - 1)).toList).filter
        (selfMoveOK tabs sh f g u)).map fun e => addrArg f e.2)
    else []
  | none => []

/-- The leaves of the Make-tree of a stack-assigned call result `x` of `f` (`SelectN [i] c`; the
`Load`s of `stkLeavesOK`); none for other values. -/
def stackLoads (tabs : Tables) (sh : Array Ty) (f g : Func) (x : ID) : List ID :=
  match f.value? x with
  | some u =>
    match u.args.toList with
    | [c] =>
      match f.value? c with
      | some cu =>
        if u.op == .SelectN && (callOpMap cu.op).isSome && decide (0 ≤ u.auxInt.toInt) then
          match (callOuts tabs cu.aux)[u.auxInt.toInt.toNat]? with
          | some p =>
            if p.regs.isEmpty then
              (mkTree sh g (isNewB f) (tabs.types.size + 1) x (tabs.ty p.type)).getD []
            else []
          | none => []
        else []
      | none => []
    | _ => []
  | none => []

/-- The address's `SP` and the memory a `Load` `l` reads. -/
def loadSP (g : Func) (l : ID) : ID :=
  ((g.value? l).bind fun w => (g.value? w.args[0]!).map (·.args[0]!)).getD l
def loadMem (g : Func) (l : ID) : ID := ((g.value? l).map (·.args[1]!)).getD l

/-- `x` is a source `SelectNAddr` that became a `Copy` (`selAddrOK`: of the slot's
`OffPtr [off] SP`): its target node no longer reads the call, so `g`'s schedule may place it
before the call; the target evaluates it from the frame alone (**frame-determined**). -/
def frameDet (f g : Func) (x : ID) : Bool :=
  match f.value? x, g.value? x with
  | some u, some w => u.op == .SelectNAddr && w.op == .Copy
  | _, _ => false

/-- The `SP` under the address that the target's `Copy` of a result address `x` of `f`
(`selAddrOK`) reads; none for other values. -/
def addrSP (tabs : Tables) (f g : Func) (x : ID) : List ID :=
  match f.value? x, g.value? x with
  | some u, some w => if selAddr tabs f u && w.op == .Copy then [loadSP g x] else []
  | _, _ => []

/-- `c` occurs in `l`, and no node with `np` comes before its first occurrence. -/
def noNpUntil (np : ID → Bool) : List ID → ID → Bool
  | [], _ => false
  | y :: l, c => y == c || (!np y && noNpUntil np l c)

/-- `z` occurs in `l`, then `c` after it, and no node with `np` lies strictly between the first `z`
and the first `c` after it. -/
def gapOK (np : ID → Bool) : List ID → ID → ID → Bool
  | [], _, _ => false
  | y :: l, z, c => if y == z then noNpUntil np l c else gapOK np l z c

/-- `z` occurs in `l`, and no node with `np` comes after its first occurrence. -/
def noNpAfter (np : ID → Bool) : List ID → ID → Bool
  | [], _ => false
  | y :: l, z => if y == z then l.all (fun x => !np x) else noNpAfter np l z

/-- New value `z` runs only when the source reaches a tail call `x` of block `fb` (`TailLECall*`,
`stuck` in the source): in `g`'s schedule of `gb` no source non-pure node lies between `z` and
`x` (the `Move`s and `Store`s of a tail call's stack arguments). -/
def tailAnchoredB (f g : Func) (fb gb : Block) (z : ID) : Bool :=
  match schedule g gb with
  | some og => fb.values.any fun x =>
      isTail f x && !invalidated g x && gapOK (npOf f fb) og.toList z x
  | none => false

/-- The checks of block `bid` (`anc`: the ancestor test of `g`'s dominator certificate). -/
def blockOK (tabs : Tables) (sh : Array Ty) (anc : ID → ID → Bool) (f g : Func) (bid : ID) : Bool :=
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
      | some w => w.op != .Phi || (fb.values.contains x &&
          match f.value? x with
          | some u => sameV u w
          | none => false)
      | none => true) &&
    fb.values.all (fun x => match f.value? x with
      | some u => u.op != .Phi ||
          ((match g.value? x with
            | some w => sameV u w
            | none => false) && !special f g x && u.args.all (fun a => !special f g a))
      | none => true) &&
    -- the same non-pure sequence
    (match schedule f fb, schedule g gb with
      | some of, some og => of.toList.filter (npOf f fb) == og.toList.filter (npOf f fb)
      | _, _ => false) &&
    -- every argument of a source node reaches it in `g` (but those of a value the pass
    -- invalidated or made frame-determined, and the `Dereference` a call's `Move` copies, whose
    -- own arguments reach it); a wide call result (dead in `g`) is pure and its arguments reach
    -- it instead (`Order.Feeds.through`)
    fb.values.all (fun y => !nodeF y || invalidated g y || frameDet f g y ||
      match f.value? y with
      | some u => u.args.all fun a => (!nodeF a || wideSel f g a || (nodeG a &&
          (depB g nodeG (isNewB f) fuel a y || depB g nodeG (fun _ => true) fuel a y)) ||
          (moveArgB f g y a && throughB f g nodeF nodeG fuel a y) ||
          (invalidated g a && throughB f g nodeF nodeG fuel a y)) &&
          (!wideSel f g a || throughB f g nodeF nodeG fuel a y)
      | none => false) &&
    -- a frame-determined value is read in `gb` only by source non-pure nodes that read it in the
    -- source too (the source evaluates it before them; `Order.transfer_rank_ex`)
    gb.values.all (fun b => match g.value? b with
      | some w => w.op == .Phi || w.args.all (fun a => !frameDet f g a ||
          (npOf f fb b && match f.value? b with
            | some ub => ub.args.contains a
            | none => false))
      | none => true) &&
    -- no node of `gb` reads an invalidated value
    gb.values.all (fun z => match g.value? z with
      | some w => w.op == .Phi || w.args.all (fun a => !invalidated g a)
      | none => true) &&
    -- per value
    fb.values.all (fun x => match f.value? x with
      | some u => u.op == .Phi || valueOK tabs sh f g x
      | none => false) &&
    -- the `IMake` arguments of converted values
    fb.values.all (fun x => !converted f x || match f.value? x with
      | some u => u.args.all fun a => imkArgOK sh f g anc fb nodeG fuel a x
      | none => true) &&
    -- controls of non-`Ret` blocks are unconverted
    ((fb.kind != .If && fb.kind != .JumpTable) || fb.controls.all (fun c => !special f g c)) &&
    -- a `Ret` returns a `MakeResult`
    (fb.kind != .Ret || match fb.controls[0]? with
      | some c => (match f.value? c with
        | some u => u.op == .MakeResult
        | none => false)
      | none => false) &&
    -- stack-argument stores and moves: values of the block, no source non-pure node between one
    -- and its call in `g`'s schedule (a store runs only when the source reaches the call); a
    -- source `SP` under its address and the call's source memory reach it (their target
    -- registers hold their evaluations, refine the source's); the `Dereference` a move copies is
    -- a value of the block (the source evaluates it before the call) before the call in `g`'s
    -- schedule (its target register is set); the source of a move above another (a frame
    -- variable) is held in the target: placed in a strict dominator or reaching the move
    (match schedule g gb with
     | some og => fb.values.all fun x => (stackStores f g x).all (fun z =>
         gb.values.contains z && gapOK (npOf f fb) og.toList z x &&
         (isNewB f (storeSP g z) || placedSDom g anc fb.id (storeSP g z) ||
           depB g nodeG (fun _ => true) fuel (storeSP g z) z) &&
         (!gb.values.contains (callMem f x) || !nodeG (callMem f x) ||
           depB g nodeG (fun _ => true) fuel (callMem f x) z)) &&
         (match f.value? x with
          | some u => u.args.all fun a => !moveArgB f g x a ||
              (fb.values.contains a && beforeB og.toList a x)
          | none => true) &&
         (stackMoves f g x).all fun z => moveMem g z == callMem f x ||
           placedSDom g anc fb.id (moveSrc g z) || depB g nodeG (fun _ => true) fuel (moveSrc g z) z
     | none => false) &&
    -- wide stores: the leaf stores are values of the block, with no source non-pure node between
    -- one and the source store in `g`'s schedule; the store's source address and memory reach
    -- them; a wide result of the block is before the store in `g`'s schedule (its source
    -- register holds its evaluation; its arguments reach the store by the reach condition)
    (match schedule g gb with
     | some og => fb.values.all fun x => (wideStores f g x).all (fun z =>
         gb.values.contains z && gapOK (npOf f fb) og.toList z x &&
         (!nodeG (addrArg f x) || depB g nodeG (fun _ => true) fuel (addrArg f x) z) &&
         (!nodeG (callMem f x) || depB g nodeG (fun _ => true) fuel (callMem f x) z)) &&
         match f.value? x with
         | some u => u.args.all fun a => !wideSel f g a || !fb.values.contains a ||
             beforeB og.toList a x
         | none => true
     | none => false) &&
    -- stack-result loads: the `SP` under the address and the call's memory are held (new,
    -- placed in a strict dominator, or the result depends on them); so is the `SP` under a
    -- result address
    fb.values.all (fun x => (stackLoads tabs sh f g x).all (fun l =>
      (isNewB f (loadSP g l) || placedSDom g anc fb.id (loadSP g l) ||
        depB g nodeG (fun _ => true) fuel (loadSP g l) x) &&
      (isNewB f (loadMem g l) || placedSDom g anc fb.id (loadMem g l) ||
        depB g nodeG (fun _ => true) fuel (loadMem g l) x)) &&
      (addrSP tabs f g x).all fun s =>
        isNewB f s || placedSDom g anc fb.id s || depB g nodeG (fun _ => true) fuel s x) &&
    -- result stores (of the `Ret` control): values of the block, with no source non-pure node
    -- after one in `g`'s schedule (a store runs only when the source completes the block); the
    -- source memory reaches them; the `LocalAddr` of a self-move, if a value of the block, is
    -- before the `MakeResult` in `g`'s schedule (its source register holds its evaluation). An
    -- invalidated argument may follow its reader: its conversion is `poison` and no target node
    -- reads it (`ecFront` leaves it out)
    (match schedule g gb with
     | some og => fb.values.all fun x => (ownStores f g x).all (fun z =>
         gb.values.contains z && noNpAfter (npOf f fb) og.toList z &&
         fb.kind == .Ret && fb.controls[0]? == some x &&
         (!nodeG (callMem f x) || depB g nodeG (fun _ => true) fuel (callMem f x) z)) &&
         (selfAddrs tabs sh f g x).all fun p => !fb.values.contains p ||
           (!invalidated g p && beforeB og.toList p x)
     | none => false) &&
    -- new values; their new arguments are values of the block, of the entry block, or placed
    -- in a strict dominator
    let sts := fb.values.toList.flatMap (stackStores f g)
    let wsts := fb.values.toList.flatMap (wideStores f g)
    let rsts := fb.values.toList.flatMap (ownStores f g)
    gb.values.all (fun z => match g.value? z with | some w => (!isNewB f z || (w.op != .Phi && (newEvalB tabs g w || sts.contains z || wsts.contains z || rsts.contains z || tailAnchoredB f g fb gb z))) && w.args.all (fun a => !isNewB f a || gb.values.contains a || (valsOf g g.entry).contains a || placedSDom g anc fb.id a) | none => !isNewB f z)
  | _, _ => false

/-- **The checker**: `g` is `f` after `expand calls`, both read in `tabs`. -/
def ecCheck (tabs : Tables) (f g : Func) : Bool :=
  let sh := typeShapes tabs
  let dc := DomCert.make g
  DomCert.cfgView g == DomCert.cfgView f && g.ownAux == f.ownAux &&
    ownOutsOK tabs f &&
    f.blocks.all (blockOK tabs sh dc.anc f g)

end GoFV.Opt.ECCheck

namespace GoFV.Opt

/-- **The fragment of `expandCalls_refines`**: the pass's output is accepted by `ecCheck` (read
in the output tables) and the input runs the same in the output tables (`tabsAgree`). `lake exe
expand-calls-probe` counts it on the corpus. -/
def expandCallsFrag (penv : PassEnv) (f : SSA.Func) : Bool :=
  match expandCallsPass penv f with
  | .ok out => tabsAgree penv.tables out.tables f && ECCheck.ecCheck out.tables f out.func
  | .error _ => true

end GoFV.Opt
