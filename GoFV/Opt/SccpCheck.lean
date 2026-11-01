import GoFV.Opt.Sccp
import GoFV.Opt.KnownBitsCheck
import GoFV.SSA.Check
import GoFV.Opt.CopyRelCheck
import GoFV.Proof.Pass.DeadEdgeVal

/-!
# sccp's checker

`sccpChecked` is a translation validator: it runs sccp's analysis and `replaceConst` (with
`latticeCells` in insertion order, as `sccpPass`) and keeps the result `g` only if the Bool
checkers accept it, else returns the input (`GoFV.Proof.Sccp.sccp_refines`). The proof goes
through two intermediate functions, built by `replaceConst` with other rewirings:
- `h` (`rewireFirst`): an `If` or `JumpTable` it would rewire becomes a `First` block whose
  successor 0 is the one its constant picks (no edge removed; `h` passes `check` with
  `firstAny`, as such a `First` block keeps all successors of a `JumpTable`);
- `k` (`rewireWith (removeEdgeG false)`): the edges are removed as in `g`, but the target's
  `Phi`s only lose arguments, where `removeEdge` may turn a `Phi` into a `Copy`
  (`phielimValue`).

`k` is `h` with the edges no run takes removed (`deadOK`, deadcode's `DeadRel`), and `g` is
`k` (often equal) with some `Phi`s turned copies (`copyOK`, copyelim's `CopyRel`).

The certificate is the final lattice `C` (`latticeCells`), the executable edges `vis`
(`visited`: `⟨b, i⟩` is the edge into `b` at its predecessor index `i`) and blocks `R`
(`visitedBlock`). A constant cell of `x` claims that `x`'s value is `poison` or the constant
`cval x` (its constant op evaluated at `x`'s type, an integer or boolean).

`sccpOK tabs f h C vis R`:
- the executable part is closed (`reachOK`): the entry and its edge 0 are executable, and every
  successor an executable block can take (by its kind and, for `If`/`JumpTable`, the value of a
  constant control) is an executable edge into an executable block;
- the claims are a **post-fixpoint** (`fixOK`): a constant non-`Phi` value is a term node whose
  arguments are all constant and which evaluates (`Rules.opVal`, the semantics) on their constants
  to its own constant; a constant `Phi` has, on each executable in-edge, a constant argument with
  that constant. Folds are checked by evaluation, so no rewrite rule is trusted;
- `h` is `f` but for values that became constants of their claimed value (`repOK`), new values
  only appended to blocks (the fold temporaries in the entry, `Const` or `Invalid` terms), the
  same atoms (`RewriteCheck.atomsOK`), and blocks with the same kinds, successors and controls
  or an `If`/`JumpTable` with a constant control turned `First` towards the successor it picks
  (`blocksOK`); both are closed under arguments.

`deadOK h k`: `k` keeps `h`'s blocks, values and the edges a run can take (successor 0 of a
`First` block), possibly at other predecessor indices with the `Phi` arguments following them
(`DeadRel`).

`CopyCheck.copyOK tabs k g` (`GoFV/Opt/CopyRelCheck.lean`): `g` is `k` with some `Phi`s turned
copies (copyelim's `CopyRel`). Only checked, with `check k`, when `k ≠ g`.
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
      | some cs => scalarEq ((GoFV.Proof.Rules.opVal tabs v.op t v.auxInt v.aux cs).retype t) c
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
      | some c => scalarEq ((GoFV.Proof.Rules.opVal tabs w.op (tabs.ty w.type) w.auxInt w.aux []).retype
          (tabs.ty w.type)) c
      | none => false))

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

/-- `rewireSuccessor` without removing an edge: an `If` or `JumpTable` on constant `ai` becomes
a `First` block whose successor 0 is the one `rewireSuccessor` keeps. -/
def rewireFirst (f : Func) (b : ID) (ai : Int64) : Func × Bool :=
  let blk := f.getB b
  let first (f : Func) : Func :=
    (f.modB b fun x => { x with kind := .First, likely := .unknown }).resetControls b
  match blk.kind with
  | .If => (first (if ai.toInt.toNat == 0 then f.swapSuccessorsByIdx b 0 1 else f), true)
  | .JumpTable =>
    let idx := ai.toInt
    if idx < 0 || idx ≥ blk.succs.size then (f, false) else
    (first (f.swapSuccessorsByIdx b 0 idx.toNat), true)
  | _ => (f, false)

/-- `rewireSuccessor` where the target's `Phi`s only lose arguments (no `phielimValue`). -/
def rewireKeep : Func → ID → Int64 → Func × Bool :=
  rewireWith (GoFV.Proof.Dead.removeEdgeG false)

/-- The kept `Phi`s of `g`'s block `c` read along `iT` what `h`'s read along `iS`. -/
def phiArgsOK (h g : Func) (c : ID) (iS iT : Nat) : Bool :=
  match g.block? c with
  | some gc => gc.values.all fun x =>
      match g.value? x with
      | some gv => gv.op != .Phi || match h.value? x with
        | some hv => gv.args[iT]? == hv.args[iS]?
        | none => false
      | none => true
  | none => true

/-- `g`'s value `x` (listed in a block) is `h`'s: same type, a `Phi` iff it was one, otherwise
the same op, aux and arguments. -/
def valueOK (h g : Func) (x : ID) : Bool :=
  match g.value? x with
  | some gv => match h.value? x with
    | some hv => gv.type == hv.type && (gv.op == .Phi) == (hv.op == .Phi) &&
        (gv.op == .Phi || (gv.op == hv.op && gv.aux == hv.aux && gv.auxInt == hv.auxInt &&
          gv.args == hv.args))
    | none => false
  | none => true

/-- `g`'s block `b` keeps `h`'s (`DeadRel`). -/
def deadBlockOK (h g : Func) (hb gb : Block) : Bool :=
  (gb.kind == hb.kind || (hb.kind == .First && gb.kind == .Plain)) &&
  gb.controls == hb.controls && gb.values.all (hb.values.contains ·) &&
  (List.range hb.succs.size).all (fun k => (hb.kind == .First && k != 0) ||
    match hb.succs[k]?, gb.succs[k]? with
    | some e, some e' => e'.b == e.b && g.blocks.contains e.b && phiArgsOK h g e.b e.i e'.i
    | _, _ => false) &&
  gb.values.all (valueOK h g) &&
  hb.values.all (fun x => gb.values.contains x ||
    (h.value? x).all fun hv => !(hv.op.call || hv.op == .NilCheck))

/-- **`g` is `h` with the edges no run takes removed** (`DeadRel h g (· ∈ g.blocks)`). -/
def deadOK (h g : Func) : Bool :=
  g.entry == h.entry && g.ownAux == h.ownAux && g.valueTab.size == h.valueTab.size &&
  g.blocks.contains h.entry &&
  (List.range g.valueTab.size).all (fun x => match g.value? x, h.value? x with
    | some gv, some hv => gv.block == hv.block
    | _, _ => true) &&
  g.blocks.all fun b =>
    match g.block? b, h.block? b with
    | some gb, some hb => h.blocks.contains b && deadBlockOK h g hb gb
    | none, _ => true
    | some _, none => false

end Sccp

/-- sccp, validated: `replaceConst` in insertion order, the result `g` if it changed and the
checkers accept it (`sccpOK` from the input to the intermediate `h`, which passes `check` with
`firstAny`, `deadOK` from `h` to the intermediate `k`, and `k = g` or `copyOK` from `k`, which
passes `check`, to `g`), else the input; the input's tables (the checked output creates no
definitions). -/
def sccpChecked : Pass := fun env f => do
  let rw ← RwEnv.ofPassEnv env
  let a ← Sccp.analyze rw env.tables f
  let g := Sccp.replace a a.keys
  let h := Sccp.replace a a.keys Sccp.rewireFirst
  let k := Sccp.replace a a.keys Sccp.rewireKeep
  let ce : CheckEnv := { tabs := env.tables, typs := env.typs }
  let ok := g != f && Sccp.sccpOK env.tables f h a.cells a.visited a.visitedBlock &&
    Sccp.deadOK h k && (check { ce with firstAny := true } h).toBool &&
    (k == g || ((check ce k).toBool && CopyCheck.copyOK env.tables k g))
  return { func := if ok then g else f, tables := env.tables }

end GoFV.Opt
