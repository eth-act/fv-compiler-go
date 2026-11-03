import GoFV.Proof.Pass.MoveLCheck
import GoFV.SSA.Sem.RunSched
import GoFV.SSA.DomCert

/-!
# The flagalloc validator `flagAllocB` (issue #385)

`flagalloc` (`GoFV.Opt.flagalloc`) keeps the CFG and each block's values in order, appends pure
recomputations (`copyFlags`) of flag generators and of the tuples they select from, redirects
flags arguments and controls to them, and drops replaced generators left without uses.
`flagAllocB tabs f g` checks that `g` is such a rewrite of `f`;
`GoFV.Proof.FlagAllocL.refinesSched_of_flagAlloc` proves that it then refines `f` under `runSched`.

* **Kept values** (`keptB`): listed in the same block of `f` and `g`. A kept non-`Phi` value
  has `f`'s op, type, aux, auxint and first-argument sign extension, and arguments related
  pairwise (`argRel`): equal and kept, or a clone of the original argument evaluated earlier in
  the block. A `Phi` is `f`'s with kept arguments.
* **Clones**: values of `g`'s block not in `f`'s, each with an original (`cert`, untrusted) of the
  same op (`cloneOp`: a pure op that never panics nor gets stuck on defined arguments), type,
  aux, auxint and related arguments, that is available where the clone runs: evaluated earlier in
  the block by `f`, or placed in a strict dominator of the block.
* **Removed values**: values of `f`'s block not in `g`'s; pure (`cloneOp`).
* **Order** (`walkB`): `f`'s and `g`'s `b.Values` orders (`schedOrder`; `g`'s must be one) agree
  on the kept values; every value `f` evaluates has no argument it evaluates later or itself
  (`f`'s order is a schedule). Controls are related like arguments (a redirected one only for an
  arm64 kind).
-/

namespace GoFV.Proof.FlagAllocL

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Proof GoFV.Proof.MoveL

/-- **Clone ops**: `Select0`/`Select1`, and the arm64 ops `Arm64.evalPure` evaluates (non-root,
outside `arm64Op`). Their lowered evaluation is `.ok` on any argument list and reads nothing but
the op, shape, aux, auxint and arguments. -/
def cloneOp (op : Op) : Bool :=
  op == .Select0 || op == .Select1 || (!op.generic && !actOp op && !isRoot op)

/-- `x` is a `Phi` of `f`. -/
def isPhiIn (f : Func) (x : ID) : Bool := ((f.value? x).map (·.op == .Phi)).getD false

/-- `x` is listed in block `b` of `f`. -/
def listedIn (f : Func) (b x : ID) : Bool := ((f.block? b).map (·.values.contains x)).getD false

/-- `x` is kept: a value of `f` and `g` in the same block, listed in it in both. -/
def keptB (f g : Func) (x : ID) : Bool :=
  match f.value? x, g.value? x with
  | some fv, some gv => fv.block == gv.block && listedIn f fv.block x && listedIn g gv.block x
  | _, _ => false

/-- Lists related pairwise by `p`. -/
def args2 (p : ID → ID → Bool) : List ID → List ID → Bool
  | [], [] => true
  | a :: as, b :: bs => p a b && args2 p as bs
  | _, _ => false

/-- Argument (or control) `ga` of `g` stands for `fa` of `f`: equal and kept, or `ga` is a clone
of `fa` evaluated earlier in the block (`C`: the block's clones so far with their originals). -/
def argRel (f g : Func) (C : List (ID × ID)) (ga fa : ID) : Bool :=
  (ga == fa && keptB f g ga) || C.contains (ga, fa)

/-- A kept non-`Phi` value: `f`'s op, type, aux, auxint, sign extension, related arguments. -/
def keptOK (f g : Func) (C : List (ID × ID)) (x : ID) : Bool :=
  match f.value? x, g.value? x with
  | some fv, some gv =>
    gv.op == fv.op && gv.type == fv.type && gv.aux == fv.aux && gv.auxInt == fv.auxInt &&
      sxOf g gv == sxOf f fv && args2 (argRel f g C) gv.args.toList fv.args.toList
  | _, _ => false

/-- `o` of `f` is available in block `b` after `f` evaluated `P` there: in `P`, or placed in a
strict dominator of `b`. -/
def availB (dc : Cert) (f : Func) (b : ID) (P : List ID) (o : ID) (ov : Value) : Bool :=
  P.contains o ||
    (ov.block != b && dc.anc ov.block b && f.blocks.contains ov.block && listedIn f ov.block o)

/-- Clone `x` of `g` of the original `o` of `f`, available in `b` after `P`. -/
def cloneOK (dc : Cert) (f g : Func) (b : ID) (P : List ID) (C : List (ID × ID)) (x o : ID) :
    Bool :=
  match f.value? o, g.value? x with
  | some ov, some gv =>
    cloneOp gv.op && gv.op == ov.op && gv.type == ov.type && gv.aux == ov.aux &&
      gv.auxInt == ov.auxInt && args2 (argRel f g C) gv.args.toList ov.args.toList &&
      availB dc f b P o ov
  | _, _ => false

/-- `f` evaluates `z` with the rest `L` of its order (`z` first): no argument of `z` is in `L`. -/
def topoOK (f : Func) (L : List ID) (z : ID) : Bool :=
  match f.value? z with
  | some fv => fv.args.all fun a => !L.contains a
  | none => false

/-- A removed value: pure. -/
def remOK (f : Func) (z : ID) : Bool := ((f.value? z).map (cloneOp ·.op)).getD false

/-- The controls of `gb` stand for those of `fb`; redirected ones only for an arm64 kind. -/
def ctrlsOK (f g : Func) (fb gb : Block) (C : List (ID × ID)) : Bool :=
  args2 (argRel f g C) gb.controls.toList fb.controls.toList &&
    (gb.controls == fb.controls || fb.kind.isArm64)

/-- **The order walk** of block `b`: `f`'s order `LF` and `g`'s `LG`, `f` having evaluated `P`,
`g` the clones `C`. A value of `f` not in `g`'s block is removed, one of `g` not in `f`'s a
clone; a kept value is the next of both. -/
def walkB (dc : Cert) (f g : Func) (cert : Array (Option ID)) (b : ID) (fb gb : Block) :
    List ID → List ID → List ID → List (ID × ID) → Bool
  | z :: LF, LG, P, C =>
    if !gb.values.contains z then
      remOK f z && topoOK f (z :: LF) z && walkB dc f g cert b fb gb LF LG (z :: P) C
    else
      match LG with
      | [] => false
      | x :: LG' =>
        if fb.values.contains x then
          x == z && keptOK f g C x && topoOK f (z :: LF) z &&
            walkB dc f g cert b fb gb LF LG' (z :: P) C
        else
          match cert.getD x none with
          | some o => cloneOK dc f g b P C x o && walkB dc f g cert b fb gb (z :: LF) LG' P ((x, o) :: C)
          | none => false
  | [], x :: LG', P, C =>
    !fb.values.contains x &&
      match cert.getD x none with
      | some o => cloneOK dc f g b P C x o && walkB dc f g cert b fb gb [] LG' P ((x, o) :: C)
      | none => false
  | [], [], _, C => ctrlsOK f g fb gb C
termination_by LF LG => LF.length + LG.length

/-- The `Phi`s of `fb` and `gb`: the same list, each `f`'s value with kept arguments. -/
def phisOK (f g : Func) (fb gb : Block) : Bool :=
  let ps := fb.values.filter (isPhiIn f)
  ps == gb.values.filter (isPhiIn g) &&
    ps.all fun x => match f.value? x, g.value? x with
      | some fv, some gv =>
        gv.op == fv.op && gv.type == fv.type && gv.aux == fv.aux && gv.auxInt == fv.auxInt &&
          gv.args == fv.args && gv.block == fv.block && fv.args.all (keptB f g)
      | _, _ => false

/-- Block `b`: same kind, `auxInt`, edges, `Phi`s; `g`'s order is a schedule; the walk. -/
def blockB (tabs : Tables) (dc : Cert) (f g : Func) (cert : Array (Option ID)) (b : ID) : Bool :=
  match f.block? b, g.block? b with
  | some fb, some gb =>
    gb.kind == fb.kind && gb.auxInt == fb.auxInt && gb.succs == fb.succs &&
      gb.preds == fb.preds && phisOK f g fb gb &&
      let LF := fb.values.filter (!isPhiIn f ·)
      let LG := gb.values.filter (!isPhiIn g ·)
      let oF := schedOrder f (Ctx.makeL tabs f).tys fb
      schedOrder g (Ctx.makeL tabs g).tys gb == some LG && (oF == none || oF == some LF) &&
        walkB dc f g cert b fb gb LF.toList LG.toList [] []
  | _, _ => false

/-- **The validator** with the clone originals `cert`. -/
def flagAllocWith (tabs : Tables) (cert : Array (Option ID)) (f g : Func) : Bool :=
  g.entry == f.entry && g.blocks == f.blocks && g.ownAux == f.ownAux && g.lowered == f.lowered &&
    let dc := make f
    f.blocks.all (blockB tabs dc f g cert)

/-! ## The certificate (untrusted) -/

/-- An original for each clone of `g` (in block order): a placed value of `f` in the block or a
dominator with the clone's op, type, aux, auxint and arguments (clone arguments read as their
originals); one in the block first. -/
def origCert (f g : Func) : Array (Option ID) := Id.run do
  let dc := make f
  let mut cert : Array (Option ID) := Array.replicate g.valueTab.size none
  for b in f.blocks do
    let (some fb, some gb) := (f.block? b, g.block? b) | continue
    for x in gb.values do
      if fb.values.contains x then continue
      let some gv := g.value? x | continue
      let args := gv.args.map fun a => (cert.getD a none).getD a
      let ok (v : Value) : Bool :=
        v.op == gv.op && v.type == gv.type && v.aux == gv.aux && v.auxInt == gv.auxInt &&
          v.args == args && listedIn f v.block v.id
      let cands := f.valueTab.filterMap fun o => o.bind fun v => if ok v then some v else none
      let pick := (cands.find? (·.block == b)).orElse fun _ =>
        cands.find? fun v => dc.anc v.block b
      if let some v := pick then cert := cert.set! x (some v.id)
  return cert

/-- **The flagalloc validator.** -/
def flagAllocB (tabs : Tables) (f g : Func) : Bool := flagAllocWith tabs (origCert f g) f g

end GoFV.Proof.FlagAllocL
