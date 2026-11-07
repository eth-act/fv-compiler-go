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

`sccpOK tabs f h C vis R` (defined in `GoFV/Opt/RewriteCheck.lean`, whose constant-`Phi` layer
uses it too):
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
