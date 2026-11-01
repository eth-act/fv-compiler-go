import GoFV.Opt.Sccp
import GoFV.Opt.KnownBitsCheck

/-!
# sccp's checker

`sccpChecked` is a translation validator: it runs sccp's analysis and `replaceConst` (with
`latticeCells` in insertion order, as `sccpPass`) and keeps the result only if the Bool checker
`sccpOK` accepts it, else returns the input (`GoFV.Proof.Sccp.sccp_refines`).

The certificate is the final lattice `C` (`latticeCells`), the executable edges `vis`
(`visited`: `⟨b, i⟩` is the edge into `b` at its predecessor index `i`) and blocks `R`
(`visitedBlock`). A constant cell of `x` claims that `x`'s value is `poison` or the constant
`cval x` (its constant op evaluated at `x`'s type, an integer or boolean). `sccpOK tabs f g C vis R`:
- the executable part is closed (`reachOK`): the entry and its edge 0 are executable, and every
  successor an executable block can take (by its kind and, for `If`/`JumpTable`, the value of a
  constant control) is an executable edge into an executable block;
- the claims are a **post-fixpoint** (`fixOK`): a constant non-`Phi` value is a term node whose
  arguments are all constant and which evaluates (`evalPure`, the semantics) on their constants
  to its own constant; a constant `Phi` has, on each executable in-edge, a constant argument with
  that constant. Folds are checked by evaluation, so no rewrite rule is trusted;
- `g` is `f` but for values that became constants of their claimed value (`repOK`), new values
  only appended to blocks (the fold temporaries in the entry, `Const` or `Invalid` terms), the
  same blocks, kinds, successors and controls (`KnownBits.blocksOK`, `RewriteCheck.atomsOK`), and
  both are closed under arguments. Edges `replaceConst` removes (`rewireSuccessor`) change the
  successors, so such outputs are rejected.
-/

namespace GoFV.Opt

open GoFV.SSA GoFV.Rules

namespace Sccp

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

/-- The value of a constant op at shape `t`. -/
def constVal (op : Op) (t : Sem.Ty) (ai : Int64) : Sem.Val :=
  (Sem.evalPure op t ai none []).retype t

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
          | some c' => scalarEq (c'.retype t) c
          | none => false
    else
      RewriteCheck.termOp v.op &&
      match v.args.toList.mapM (cval tabs f C) with
      | some cs => scalarEq ((Sem.evalPure v.op t v.auxInt v.aux cs).retype t) c
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
      match cval tabs f C x with
      | some c => scalarEq ((Sem.evalPure w.op (tabs.ty w.type) w.auxInt w.aux []).retype
          (tabs.ty w.type)) c
      | none => false))

/-- **The checker.** -/
def sccpOK (tabs : Tables) (f g : Func) (C : Array (Option Lat)) (vis : Array Edge)
    (R : Array Bool) : Bool :=
  RewriteCheck.atomsOK f g && RewriteCheck.closedOK f && RewriteCheck.closedOK g &&
  KnownBits.blocksOK f g && reachOK tabs f C vis R &&
  (List.range f.valueTab.size).all (fun x => fixOK tabs f C vis x && repOK tabs f g C x)

end Sccp

/-- sccp, validated: `replaceConst` in insertion order, the result if it changed and `sccpOK`
accepts it, else the input; the input's tables (the checked output creates no definitions). -/
def sccpChecked : Pass := fun env f => do
  let rw ← RwEnv.ofPassEnv env
  let a ← Sccp.analyze rw env.tables f
  let g := Sccp.replace a a.keys
  let ok := g != f && Sccp.sccpOK env.tables f g a.cells a.visited a.visitedBlock
  return { func := if ok then g else f, tables := env.tables }

end GoFV.Opt
