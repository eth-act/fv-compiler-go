import GoFV.Opt.Fuse.If
import GoFV.Opt.Fuse.ComparisonsCheck
import GoFV.Opt.SpecSafe

/-!
# fuseBlockIf, checked

`IfC.Site.relB f g R` validates one `fuseBlockIf` rewrite of `f` into `g` at the site `s`
(`siteOf`, Go's choice of the two sides): the `If` block `b` (control `c`) has two sides, each
an edge into the join block `ss` (at predecessor index `j0`/`j1`) or a speculation-safe `Plain`
arm whose successor is `ss`.

- `ss`'s `Phi`s read the same argument along both sides, a value outside `X` (below);
- in `g`, `b` is `Plain` without controls, continuing along side 1; one edge is gone (`rmT`,
  `rmJ`): `b`'s edge 0, or, when side 0's arm has `b` as its only predecessor (`unlinked`), the
  arm's edge into `ss` (the arm's values move to `b`, the arm keeps no values, edges or
  controls); the predecessor `rmJ` of `rmT` and the `Phi` arguments `rmJ` are swap-removed
  (`rmE`, `phiRm`), and `b`'s edge 1 becomes its edge 0 (`pmap`); every other listed block keeps
  its values, kind and controls, with successors renumbered by `rmE` and predecessors by
  `predsOf`;
- the values `R` (`resetOf`: `Invalid` in `g`, not in `f`) are reset to `OpInvalid` with no
  arguments; in `f` each is a `Phi` or pure (`resetOK`); every other value keeps what the
  semantics reads (the `Phi`s of `rmT` with their arguments renumbered); every value keeps its
  block, but a moved arm value is `b`'s (`blkOK`);
- no value of `g` outside `X` reads, and no control of `g` is, a value of `X` (the reset values
  and the arms' values);
- every checked block of `g` has a schedule.

No `check` of `g` (issue #147): well-formedness and use dominance of `g` follow from the
relation (`GoFV.Proof.FuseIf.Setup.wg`, `useDom_g`). The soundness proof is
`GoFV.Proof.FuseIf.fuseBlockIfChecked_refines`.
-/

namespace GoFV.Opt.Fuse

open GoFV.SSA

namespace IfC

/-- A `fuseBlockIf` site: the `If` block, its control and successor edges, the arms (`none`:
the side enters `ss` directly) and the predecessor indices of `ss` along the two sides. -/
structure Site where
  b : ID
  c : ID
  e0 : Edge
  e1 : Edge
  arm0 : Option ID
  arm1 : Option ID
  ss : ID
  j0 : Nat
  j1 : Nat
  deriving Inhabited

/-- The site `fuseBlockIf tv f b` rewrites (Go's choice of sides, `fuse.go:68-110`); two edges
into the same block are two direct sides. -/
def siteOf (tv : TypeView) (f : Func) (b : ID) : Option Site :=
  match f.block? b with
  | none => none
  | some B =>
    if B.kind != .If then none else
    match B.succs[0]?, B.succs[1]?, B.controls[0]? with
    | some e0, some e1, some c =>
      if e0.b == e1.b then some ⟨b, c, e0, e1, none, none, e0.b, e0.i, e1.i⟩ else
      let plainEmpty (s : ID) : Bool := (f.getB s).kind == .Plain && isEmpty tv f s
      let (a0, ss0, i0) :=
        if !plainEmpty e0.b then (none, e0.b, e0.i)
        else let e := (f.getB e0.b).succs[0]!; (some e0.b, e.b, e.i)
      let (a1, ss1, i1) :=
        if !plainEmpty e1.b then (none, e1.b, e1.i)
        else let e := (f.getB e1.b).succs[0]!; (some e1.b, e.b, e.i)
      if ss0 == ss1 then some ⟨b, c, e0, e1, a0, a1, ss0, i0, i1⟩
      else if a0 == some ss1 then some ⟨b, c, e0, e1, none, a1, ss1, e0.i, i1⟩
      else if a1 == some ss0 then some ⟨b, c, e0, e1, a0, none, ss0, i0, e1.i⟩
      else none
    | _, _, _ => none

namespace Site

variable (s : Site) (f g : Func)

/-- Side 0's arm has `b` as its only predecessor: Go unlinks it (`fuse.go:131`). -/
def unlinked : Bool :=
  match s.arm0 with
  | some a => ((f.block? a).map (·.preds)) == some #[⟨s.b, 0⟩]
  | none => false

/-- The block that loses a predecessor: `ss` (side 0 direct or its arm unlinked), else the arm. -/
def rmT : ID :=
  match s.arm0 with
  | some a => if s.unlinked f then s.ss else a
  | none => s.ss

/-- The predecessor index of `rmT` that is removed. -/
def rmJ : Nat :=
  match s.arm0 with
  | some _ => if s.unlinked f then s.j0 else s.e0.i
  | none => s.j0

/-- The last predecessor index of `rmT` in `f`. -/
def last : Nat := (((f.block? (s.rmT f)).map (·.preds.size)).getD 0) - 1

/-- Predecessor index `i` of `rmT` after the swap-removal of `rmJ`. -/
def rmI (i : Nat) : Nat := if i == s.last f then s.rmJ f else i

/-- An edge after the swap-removal: the edge into `rmT` at the last index moves to `rmJ`. -/
def rmE (e : Edge) : Edge :=
  if e.b == s.rmT f && e.i == s.last f then ⟨s.rmT f, s.rmJ f⟩ else e

/-- `x` is a value of an arm. -/
def armVal (x : ID) : Bool :=
  s.arm0.any (fun a => (valsOf f a).contains x) || s.arm1.any (fun a => (valsOf f a).contains x)

/-- The values the two functions may disagree on: the reset values and the arms' values. -/
def inX (R : List ID) (x : ID) : Bool := R.contains x || s.armVal f x

/-- The arm along edge `e`: speculation-safe `Plain` block, successor `ss` at `j`. -/
def armOK (a : ID) (e : Edge) (j : Nat) : Bool :=
  e.b == a && a != s.b && a != s.ss &&
  match f.block? a with
  | some A => A.kind == .Plain && A.succs == #[⟨s.ss, j⟩] &&
      A.values.all fun x => match f.value? x with
        | some v => specSafeOp v.op
        | none => false
  | none => false

/-- Side `k`: an arm, or the edge enters `ss` at `j`. -/
def sideOK (a? : Option ID) (e : Edge) (j : Nat) : Bool :=
  match a? with
  | some a => s.armOK f a e j
  | none => e == ⟨s.ss, j⟩

/-- The `Phi`s of `ss` read the same argument along both sides, outside `X`. -/
def phisOK (R : List ID) : Bool :=
  (valsOf f s.ss).all fun x => match f.value? x with
    | some v => v.op != .Phi ||
        (match v.args[s.j0]?, v.args[s.j1]? with
          | some a, some a' => a == a' && !s.inX f R a
          | _, _ => false)
    | none => false

/-- The shape of `f` around the site. -/
def shapeOK (R : List ID) : Bool :=
  f.blocks.contains s.b && f.blocks.contains s.ss && s.ss != s.b && s.j0 != s.j1 &&
  (match f.block? s.b with
    | some B => B.kind == .If && B.controls == #[s.c] && B.succs == #[s.e0, s.e1]
    | none => false) &&
  (match f.block? s.ss with
    | some P => s.j0 < P.preds.size && s.j1 < P.preds.size
    | none => false) &&
  s.sideOK f s.arm0 s.e0 s.j0 && s.sideOK f s.arm1 s.e1 s.j1 && s.phisOK f R

/-- `x` is `Invalid` without arguments in `g` (it evaluates in every frame). -/
def invalidIn (x : ID) : Bool :=
  match g.value? x with
  | some v => v.id == x && v.op == .Invalid && v.args.isEmpty
  | none => false

/-- `b`'s edge 1 becomes its edge 0 (`b.removeSucc(0)` moves it). -/
def pmap (e : Edge) : Edge := if e == ⟨s.b, 1⟩ then ⟨s.b, 0⟩ else e

/-- The predecessors of block `bid` in `g`, from its predecessors `ps` in `f`. -/
def predsOf (bid : ID) (ps : Array Edge) : Array Edge :=
  (if bid == s.rmT f then Cmp.swapRemove ps (s.rmJ f) else ps).map s.pmap

/-- `x` is a value of an unlinked arm (it moves to `b`). -/
def moved (x : ID) : Bool := s.unlinked f && s.arm0.any fun a => (valsOf f a).contains x

/-- Value `x` keeps its block, a moved one becomes `b`'s. -/
def blkOK (x : ID) : Bool :=
  match f.value? x, g.value? x with
  | some fv, some gv => gv.block == if s.moved f x then s.b else fv.block
  | _, _ => true

/-- An unlinked arm in `g`: its ID, no values, edges or controls. -/
def goneOK (bid : ID) : Bool :=
  match f.block? bid, g.block? bid with
  | some fb, some gb =>
    gb.id == fb.id && gb.values.isEmpty && gb.succs.isEmpty && gb.preds.isEmpty &&
      gb.controls.isEmpty
  | _, _ => false

/-- A reset value: `Invalid` without arguments in `g`; a `Phi` or pure in `f`. -/
def resetOK (r : ID) : Bool :=
  match f.value? r, g.value? r with
  | some u, some v =>
    u.id == r && v.id == r && v.op == .Invalid && v.args.isEmpty &&
      (u.op == .Phi || Sem.prio u.op == 0)
  | _, _ => false

/-- The reset values: `Invalid` in `g`, not in `f`. -/
def resetOf : List ID :=
  (List.range f.valueTab.size).filter fun x => match f.value? x, g.value? x with
    | some u, some v => u.op != .Invalid && v.op == .Invalid
    | _, _ => false

/-- The arguments of a `Phi` of `rmT` after the swap-removal of `rmJ`. -/
def phiRm (fa ga : Array ID) : Bool :=
  ga.size + 1 == fa.size &&
    (List.range fa.size).all fun i => i == s.rmJ f || ga[s.rmI f i]? == fa[i]?

/-- Value `x` (not reset): unchanged in what the semantics reads (a `Phi` of `rmT`: its
arguments swap-removed), reading nothing of `X`. -/
def valueOK (R : List ID) (x : ID) : Bool :=
  R.contains x ||
  match f.value? x, g.value? x with
  | some fv, some gv =>
    gv.id == fv.id && gv.type == fv.type && gv.aux == fv.aux && gv.auxInt == fv.auxInt &&
      gv.op == fv.op && gv.args.all (fun a => !s.inX f R a) &&
      if fv.op == .Phi && (valsOf f (s.rmT f)).contains x then s.phiRm f fv.args gv.args
      else gv.args == fv.args
  | none, none => true
  | _, _ => false

/-- Block `bid` of `g`: `b` is `Plain` along side 1 with its values (and an unlinked arm's); an
unlinked arm keeps nothing (`goneOK`); every other block keeps its values, kind and controls,
with successors renumbered; every block but the arm has its predecessors renumbered
(`predsOf`), its controls outside `X` and a schedule. -/
def blockOK (R : List ID) (bid : ID) : Bool :=
  (s.unlinked f && s.arm0 == some bid && goneOK f g bid) ||
  match f.block? bid, g.block? bid with
  | some fb, some gb =>
    gb.id == fb.id && gb.preds == s.predsOf f bid fb.preds &&
      gb.controls.all (fun c => !s.inX f R c) && (Sem.schedule g gb).isSome &&
      if bid == s.b then
        gb.kind == .Plain && gb.controls.isEmpty && gb.succs == #[s.rmE f s.e1] &&
          gb.values == fb.values ++ (if s.unlinked f then (s.arm0.map (valsOf f)).getD #[] else #[])
      else
        gb.values == fb.values && gb.kind == fb.kind && gb.controls == fb.controls &&
          gb.succs == fb.succs.map (s.rmE f)
  | _, _ => false

/-- **One `fuseBlockIf` rewrite** at site `s` with reset values `R`, checked (module doc). -/
def relB (R : List ID) : Bool :=
  s.shapeOK f R && g.entry == f.entry && g.ownAux == f.ownAux &&
    g.valueTab.size == f.valueTab.size && g.blocks == f.blocks &&
    R.all (resetOK f g) &&
    (!s.unlinked f || s.arm0.all fun a => (valsOf f a).all (invalidIn g)) &&
    (List.range f.valueTab.size).all (s.valueOK f g R) &&
    (List.range f.valueTab.size).all (s.blkOK f g) &&
    f.blocks.all (s.blockOK f g R)

end Site

/-- **A checked `fuseBlockIf` step** at `b`: `g` is the rewrite at `siteOf tv f b`. -/
def stepOK (tv : TypeView) (f g : Func) (b : ID) : Bool :=
  match siteOf tv f b with
  | some s => s.relB f g (Site.resetOf f g)
  | none => false

end IfC

/-- **`fuseBlockIf`, checked**: the rewrite is kept only if `IfC.stepOK` accepts it. -/
def fuseBlockIfChecked (tv : TypeView) (f : Func) (b : ID) : Except String (Func × Bool) := do
  let (g, ch) ← fuseBlockIf tv f b
  if ch && IfC.stepOK tv f g b then return (g, true) else return (f, false)

end GoFV.Opt.Fuse
