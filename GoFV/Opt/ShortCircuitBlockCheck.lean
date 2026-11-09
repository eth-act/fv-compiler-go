import GoFV.Opt.ShortCircuitBlock
import GoFV.Opt.Checked
import GoFV.SSA.Sem.TyEq

variable [GoFV.SSA.Sem.Addrs]

/-!
# `shortcircuitBlock`, checked (issue #16)

`scOK f g s` validates one `shortcircuitBlock` rewrite of `f` into `g` at the site `s`
(`siteOf f b`) without running `check` on `g`. The rewrite redirects the edge `p → b` (index
`cidx` of `b`'s predecessors) to `t` (the successor of `b` along `te`). A source run that takes
`p → b → t` is matched by a target run that takes `p → t`; every other step of a source run is
matched block by block.

**Before the rewrite** (`preOK`): `b` is an `If` block whose control is a chain of `Copy`/`Not`
values of `b` (`chainOf`) over the `Phi` `ctl` of `b`; `ctl`'s argument along `cidx` is a
`ConstBool` without arguments, and the boolean the chain then computes selects `te`; every other
value of `b` is a `Phi` (the *other phis* `vs`); `b` has two predecessors if there are other
phis.

**Facts.** The registers of `b`'s values (`bvals`) and of values not listed in `f` may differ
between the two runs (the set `Δ` of the proof); every other register is equal. For the other
phis `v`, a *fact* `(v, w)` says that the target register `w` holds the source's `v`. Each
checked block has facts after its `Phi`s (`pin`) and at its end (`out`), one optional register
per other phi; every other block has the default facts `dflt` (`w = v` for an other phi that the
rewrite moved out of `b` into another block, none otherwise). The facts of an edge are those of
its source block, except on the redirected edge, where the source has evaluated `b` along `cidx`
(`einX`: `v` holds its argument along `cidx`).

**Checked blocks** (`K`): the blocks `applySite` changes: `b`, `t`, `p`, the plan's blocks
(`region`) and the block of `b`'s last predecessor. For each, along each incoming edge of
`g` (the source's edge index `srcIdx`: `b`'s last predecessor took index `cidx`; the redirected
edge comes from `b` along `te`), `blockOK` checks that

- every `Phi` of `g` listed in the block in `f` too reads the register related (`trans`) to
  the source's argument; a source `Phi` missing from the block is one of `b`'s values, or one of
  `b`'s values that became a `Copy` of the related register or `Invalid`;
- each fact after the `Phi`s holds: the register is a new `Phi` (a *carrier*) reading the
  register holding `v` along the edge, or a register the block's `Phi`s do not write that holds
  `v` along the edge (`b`'s other phis: their argument, of `v`'s type);
- every non-`Phi` of the source block is a non-`Phi` of the target block with the same op,
  type, aux, auxint and related arguments (`argRel`); the target's other non-`Phi`s are `Copy`
  carriers of a fact or `Invalid` without arguments; the target's schedule lists the source's
  non-`Phi`s in the source schedule's order (`schedOK`);
- types compared by shape (`tyEq`: the shapes `tabs` gives them);
- the controls are related, the kind is equal, the successors are equal up to the
  redirection and `srcIdx`; the facts at the end hold.

**Everywhere else** (`frameOK`, `scanOK`, `exitOK`, `regionOK`): the other blocks and the values
`f` lists in them are unchanged (but for use counts), and read none of `b`'s values but the
moved phis with default facts; an edge from a checked block to another block carries the default
facts; a plan block is entered only from `b`, the plan's blocks, or along the redirected edge;
the tables keep their sizes (no rewrite on the corpus grows them).

**Well-formedness and use dominance of `g`** (the invariant `WFDom` of the fuse loop), without a
check of the whole of `g` (issue #147): each block of `K` passes the per-block loops of
`wfCheck` and keeps the indices of its edges to blocks outside `K` (`wfKOK`); each use in a
block of `K` (`domKOK`, `useOK`) is the source's use of the same register outside `b`'s values,
or reads a register defined in the use's block, a moved phi where the source reads it, or a
`Phi` argument of `b` (from `p`, or from `b`'s remaining predecessors at a block every path to
which passes `b`: `dsOK`); a path that passed `b` leaves the plan's blocks only through the
block a moved phi moved to (`closeOK`).

The soundness proof is `GoFV.Proof.ShortCirc.shortcircuitBlockChecked_refines`; `WF` and
`UseDom` of `g`: `GoFV/Proof/Pass/ShortCircPres.lean`, `ShortCircUseDom.lean`.
-/

namespace GoFV.Opt.ShortCircuit

open GoFV.SSA GoFV.Opt.Fuse

/-- `x` is a `Phi` of `h`. -/
def isPhiIn (h : Func) (x : ID) : Bool := (h.value? x).any (·.op == .Phi)

/-- `x` is listed in the block its table entry names. -/
def listedIn (h : Func) (x : ID) : Bool :=
  match h.value? x with
  | some v => (valsOf h v.block).contains x
  | none => false

/-- Two value table entries alike but for the use count. -/
def sameEntry : Option Value → Option Value → Bool
  | some x, some y => { x with uses := 0 } == { y with uses := 0 }
  | none, none => true
  | _, _ => false

theorem sameEntry_refl (o : Option Value) : sameEntry o o = true := by
  cases o <;> simp [sameEntry]

/-- `a` and `b` have the same size and agree at every index outside `skip`, by `eq` (`eq` holds
on equal entries). Compiled, entries that are the same object are neither compared nor passed to
`skip`, and nothing is allocated. -/
def tabEqBy {α : Type} (eq : Option α → Option α → Bool)
    (heq : ∀ o, eq o o = true) (a b : Array (Option α)) (skip : Nat → Bool) : Bool :=
  a.size == b.size &&
    Nat.all a.size fun i _ =>
      withPtrEq a[i]! b[i]! (fun _ => skip i || eq a[i]! b[i]!)
        (fun h => by rw [h, heq, Bool.or_true])

/-- `p i a[i]` at every index `i` of `a`. -/
def allIdx {α : Type} (a : Array α) (p : Nat → α → Bool) : Bool :=
  (List.range a.size).all fun i => (a[i]?).all (p i)

/-- The `Copy`/`Not` chain of `b` (`B`) from `x` down to `ctl`: its values, top first, and
whether it negates. -/
def chainOf (f : Func) (B : Block) (ctl : ID) : Nat → ID → Option (List ID × Bool)
  | 0, _ => none
  | fuel + 1, x =>
    if x == ctl then some ([], false) else
    match f.value? x with
    | some v =>
      if B.values.contains x && (v.op == .Copy || v.op == .Not) && v.args.size == 1 then
        (chainOf f B ctl fuel v.args[0]!).map fun (l, par) =>
          (x :: l, if v.op == .Not then !par else par)
      else none
    | none => none

/-- The plan's blocks, in the order their facts are computed. -/
def Plan.region : Plan → Array ID
  | .merge t m visited => #[t] ++ visited ++ #[m]
  | .uIntoT t visited => visited ++ #[t]
  | .tIntoU t u => #[t, u]
  | .tExits t u => #[t, u]
  | .uExits t u => #[u, t]

/-- Push `x` unless present. -/
def addU (K : Array ID) (x : ID) : Array ID := if K.contains x then K else K.push x

/-- Facts: per other phi of `b`, the target register holding it. -/
abbrev Facts := Array (Option ID)

/-- The per-block facts of the checked blocks: block, facts after the `Phi`s, facts at the end. -/
abbrev FactTab := Array (ID × Facts × Facts)

/-- What the checker derives from the site and the two functions. -/
structure Info where
  /-- The type tables (shapes of types). -/
  tabs : Tables
  s : Site
  /-- `b`'s values in `f`. -/
  bvals : Array ID
  /-- `b`'s other phis in `f`. -/
  vs : Array ID
  /-- `b`'s last predecessor index in `f`. -/
  last : Nat
  /-- The index of the redirected edge among `t`'s predecessors in `g`. -/
  tn : Nat
  region : Array ID
  /-- The checked blocks: `b`, the region, `t`, `p`, the block of `b`'s last predecessor. -/
  K : Array ID
  dflt : Facts
  /-- Blocks of `K` every path to which in `g` passes `b` (`dsOK` checks it). -/
  dS : Array ID
  deriving Inhabited

namespace Info

variable (I : Info) (f g : Func)

/-- `t`. -/
def t : ID := I.s.te.b

/-- The shape of a type as the semantics computes it (`Sem.typeShapes`). -/
def shapeOf (t : TypeRef) : Sem.Ty := if t < I.tabs.types.size then I.tabs.ty t else .other

/-- Two types of the same shape. -/
def tyEq (t1 t2 : TypeRef) : Bool := t1 == t2 || Sem.Ty.beq (I.shapeOf t1) (I.shapeOf t2)

/-- The fact of `F` for other phi `v`. -/
def look (F : Facts) (v : ID) : Option ID :=
  (I.vs.findIdx? (· == v)).bind fun i => F[i]?.join

/-- The target register holding the source's register `a` under facts `F` (`a` outside `b`'s
values: itself). -/
def trans (F : Facts) (a : ID) : Option ID :=
  if I.vs.contains a then I.look F a else if I.bvals.contains a then none else some a

/-- The source's predecessor index for the target's predecessor `iT` of `B`. -/
def srcIdx (B iT : Nat) : Nat :=
  if B == I.s.b && iT == I.s.cidx && I.s.cidx != I.last then I.last else iT

/-- The redirected edge `p → t`. -/
def redir (B iT : Nat) : Bool := B == I.t && iT == I.tn

/-- The facts of block `B` (default unless checked). -/
def factsOf (T : FactTab) (B : ID) : Facts × Facts :=
  if I.K.contains B then
    match T.find? (·.1 == B) with
    | some (_, pin, out) => (pin, out)
    | none => (I.dflt, I.dflt)
  else (I.dflt, I.dflt)

/-- The facts at the end of block `B`. -/
def outOf (T : FactTab) (B : ID) : Facts := (I.factsOf T B).2

/-- The facts of the redirected edge: the source evaluated `b` along `cidx`. -/
def einX (T : FactTab) : Facts :=
  I.vs.map fun v =>
    match (f.getV v).args[I.s.cidx]? with
    | some a => if I.tyEq (f.getV a).type (f.getV v).type then I.trans (I.outOf T I.s.p) a else none
    | none => none

/-- The source's edge index and the facts of the target's edge `iT` into `B` (`gB` in `g`). -/
def edgeIn (T : FactTab) (B : ID) (gB : Block) (iT : Nat) : Nat × Facts :=
  if I.redir B iT then (I.s.te.i, I.einX f T)
  else (I.srcIdx B iT, match gB.preds[iT]? with
    | some e => I.outOf T e.b
    | none => I.dflt)

/-! ## The per-block check -/

section Block

variable (fB gB : Block) (pin out : Facts)

/-- The source register a target non-`Phi` of the block stands for: itself (unless `Invalid`), or
the other phi whose end fact it carries. -/
def home (x : ID) : Option ID :=
  if fB.values.contains x && !isPhiIn f x then some x
  else if (g.getV x).op == .Invalid then none
  else if fB.values.contains x then some x
  else I.vs.find? fun v => I.look out v == some x

/-- Register `a` is equal in both after the `Phi`s (outside `b`'s values, or a `Phi` of the
block in both). -/
def idPost (a : ID) : Bool :=
  !I.bvals.contains a ||
    (isPhiIn f a && isPhiIn g a && fB.values.contains a && gB.values.contains a)

/-- After the `Phi`s, target register `w` holds the source's `a`. -/
def pinRel (w a : ID) : Bool :=
  (w == a && I.idPost f g fB gB a) || (I.vs.contains a && I.look pin a == some w)

/-- The non-`Phi`s of a block. -/
def nodesOf (h : Func) (B : Block) : Array ID := B.values.filter (!isPhiIn h ·)

/-- A target argument `w` read by a non-`Phi` where the source reads `a`. -/
def argRel (w a : ID) : Bool :=
  if (nodesOf g gB).contains w then I.home f g fB out w == some a
  else !(nodesOf f fB).contains a && I.pinRel f g fB gB pin w a

/-- The `Phi`s along target edge `iT` (source edge `iS`, edge facts `E`), and the facts after
them. `inR`: the block is a plan block (its edge facts hold defined source registers). -/
def phisOK (iT iS : Nat) (E : Facts) (inR : Bool) : Bool :=
  let rel (w a : ID) : Bool := I.trans E a == some w
  let srcArg (v : ID) : Option ID := (f.getV v).args[iS]?
  gB.values.all (fun z => !isPhiIn g z ||
    if fB.values.contains z then
      isPhiIn f z && I.tyEq (g.getV z).type (f.getV z).type &&
        match (g.getV z).args[iT]?, srcArg z with
        | some w, some a => rel w a
        | _, _ => false
    else I.vs.any fun v => I.look pin v == some z) &&
  fB.values.all (fun y => !isPhiIn f y ||
    if gB.values.contains y then
      isPhiIn g y ||
        (I.bvals.contains y &&
          (((g.getV y).op == .Invalid && (g.getV y).args.isEmpty) ||
           ((g.getV y).op == .Copy && I.tyEq (g.getV y).type (f.getV y).type &&
             (g.getV y).args.size == 1 &&
             match (g.getV y).args[0]?, srcArg y with
             | some w, some a => rel w a && !gB.values.contains w
             | _, _ => false)))
    else I.bvals.contains y) &&
  I.vs.all fun v => match I.look pin v with
    | none => true
    | some w =>
      let src (w' : ID) : Bool :=
        if fB.values.contains v then
          match srcArg v with
          | some a => rel w' a
          | none => false
        else I.look E v == some w'
      if gB.values.contains w then
        isPhiIn g w && !fB.values.contains w && I.tyEq (g.getV w).type (f.getV v).type &&
          (inR || fB.values.contains v) &&
          match (g.getV w).args[iT]? with
          | some a' => src a'
          | none => false
      else
        src w && (!fB.values.contains v ||
          match srcArg v with
          | some a => I.tyEq (f.getV a).type (f.getV v).type
          | none => false)

/-- A source non-`Phi` `x` of the block: the same op, type, aux, auxint, related arguments. -/
def sameNode (x : ID) : Bool :=
  (g.getV x).op == (f.getV x).op && (g.getV x).type == (f.getV x).type &&
    (g.getV x).aux == (f.getV x).aux && (g.getV x).auxInt == (f.getV x).auxInt &&
    (g.getV x).args.size == (f.getV x).args.size &&
    ((g.getV x).args.zip (f.getV x).args).all fun p => I.argRel f g fB gB pin out p.1 p.2

/-- A new non-`Phi` `x` (a carrier of an end fact): a `Copy` of the register holding its other
phi, in a plan block or `b` (`inRb`). -/
def carrierOK (inRb : Bool) (x : ID) : Bool :=
  match I.home f g fB out x with
  | some v =>
    inRb && (g.getV x).op == .Copy && I.tyEq (g.getV x).type (f.getV v).type &&
      (g.getV x).args.size == 1 &&
      match (g.getV x).args[0]? with
      | some w =>
        if (nodesOf g gB).contains w then I.home f g fB out w == some v
        else I.look pin v == some w
      | none => false
  | none => false

/-- A target non-`Phi` `x` of the block. -/
def nodeOK (inRb : Bool) (x : ID) : Bool :=
  if fB.values.contains x && !isPhiIn f x then I.sameNode f g fB gB pin out x
  else if (g.getV x).op == .Invalid then
    (g.getV x).args.isEmpty && (!fB.values.contains x || I.bvals.contains x)
  else if fB.values.contains x then I.bvals.contains x && (g.getV x).op == .Copy
  else I.carrierOK f g fB gB pin out inRb x

/-- The non-`Phi`s of the block (see the module doc). `inRb`: a plan block or `b`. -/
def nodesOK (inRb : Bool) : Bool :=
  (nodesOf f fB).all (fun y => (nodesOf g gB).contains y && I.home f g fB out y == some y) &&
  (nodesOf g gB).all (I.nodeOK f g fB gB pin out inRb)

/-- Along `l`, every `root` comes after (by `pos`) every value before it (`m`: the largest `pos`
so far). -/
def schedScan (pos : ID → Nat) (root : ID → Bool) : Option Nat → List ID → Bool
  | _, [] => true
  | m, r :: rest =>
    (!root r || m.all (· < pos r)) && schedScan pos root (some (max (m.getD 0) (pos r))) rest

/-- Two lists of schedule nodes alike. -/
def sameSNodes : List Sem.SNode → List Sem.SNode → Bool
  | [], [] => true
  | x :: xs, y :: ys => x.id == y.id && x.args == y.args && x.prio == y.prio && sameSNodes xs ys
  | _, _ => false

/-- Every source non-`Phi` the target's schedule lists before a source root (a non-pure
non-`Phi`), the source's schedule lists before it too: if the source panics at a root, the
target has evaluated only values the source evaluated. Blocks whose schedule nodes are
unchanged have the same schedule; the schedules (tables of the size of the largest value ID)
are computed only for the others. -/
def schedOK : Bool :=
  sameSNodes (Sem.schedNodes g gB).toList (Sem.schedNodes f fB).toList ||
  match Sem.schedule f fB, Sem.schedule g gB with
  | some oS, some oT =>
    schedScan (oS.toList.idxOf ·) (fun r => Sem.prio (f.getV r).op != 0) none
      (oT.toList.filter ((nodesOf f fB).contains ·))
  | _, _ => false

/-- The facts at the end of the block. -/
def outOK : Bool :=
  I.vs.all fun v => match I.look out v with
    | none => true
    | some w =>
      if (nodesOf g gB).contains w then I.home f g fB out w == some v
      else I.look pin v == some w

/-- Successor `k`: the same edge up to `srcIdx`, or the redirected edge. -/
def succOK (B : ID) : Bool :=
  gB.succs.size == fB.succs.size &&
  (List.range gB.succs.size).all fun k =>
    match gB.succs[k]?, fB.succs[k]? with
    | some e', some e =>
      (B == I.s.p && k == I.s.pi && e' == ⟨I.t, I.tn⟩ && e == ⟨I.s.b, I.s.cidx⟩) ||
        (e'.b == e.b && e.i == I.srcIdx e.b e'.i && !I.redir e'.b e'.i)
    | _, _ => false

/-- Every target value of the block is listed there in `f`, or is one of `b`'s values, or is not
listed in `f`. -/
def newOK : Bool :=
  gB.values.all fun x => fB.values.contains x || I.bvals.contains x || !listedIn f x

end Block

/-- **The check of a checked block** `B` (see the module doc). `b` left without predecessors is
never entered. -/
def blockOK (T : FactTab) (B : ID) : Bool :=
  !g.blocks.contains B ||
  match f.block? B, g.block? B with
  | some fB, some gB =>
    fB.id == B && gB.id == B &&
    ((gB.preds.isEmpty && B == I.s.b) ||
      let (pin, out) := I.factsOf T B
      let inR := I.region.contains B
      gB.kind == fB.kind && gB.controls.size == fB.controls.size &&
      (inR || B == I.s.b || (pin == I.dflt && out == I.dflt)) &&
      I.newOK f fB gB && I.nodesOK f g fB gB pin out (inR || B == I.s.b) &&
      schedOK f g fB gB && I.outOK f g fB gB pin out && I.succOK fB gB B &&
      (gB.controls.zip fB.controls).all (fun (c', c) => I.argRel f g fB gB pin out c' c) &&
      (List.range (max 1 gB.preds.size)).all fun iT =>
        (I.redir B iT || fB.preds[(I.edgeIn f T B gB iT).1]? == gB.preds[iT]?) &&
          I.phisOK f g fB gB pin iT (I.edgeIn f T B gB iT).1 (I.edgeIn f T B gB iT).2 inR)
  | _, _ => false

/-! ## Computing the facts (untrusted: `blockOK` checks them) -/

/-- The facts of checked block `B`, from the end facts `outK` of the other blocks (`none`:
not known yet, ignored); `none` if no incoming edge is known yet. -/
def computeFacts (outK : ID → Option Facts) (B : ID) : Option (Facts × Facts) :=
  if !(I.region.contains B || B == I.s.b) then some (I.dflt, I.dflt) else
  match f.block? B, g.block? B with
  | some fB, some gB =>
    let einX : Option Facts := (outK I.s.p).map fun Op => I.vs.map fun v =>
      match (f.getV v).args[I.s.cidx]? with
      | some a => if I.tyEq (f.getV a).type (f.getV v).type then I.trans Op a else none
      | none => none
    -- the known incoming edges: target index, source index, facts
    let edges : List (Nat × Nat × Facts) := (List.range gB.preds.size).filterMap fun iT =>
      if I.redir B iT then einX.map ((iT, I.s.te.i, ·))
      else (match gB.preds[iT]? with
        | some e => outK e.b
        | none => some I.dflt).map ((iT, I.srcIdx B iT, ·))
    let pin : Facts := I.vs.map fun v =>
      -- the target register along edge `(iS, E)` holding `v` after the `Phi`s
      let along (iS : Nat) (E : Facts) : Option ID :=
        if fB.values.contains v then
          match (f.getV v).args[iS]? with
          | some a => if I.tyEq (f.getV a).type (f.getV v).type then I.trans E a else none
          | none => none
        else I.look E v
      let carrier := gB.values.find? fun z =>
        isPhiIn g z && !fB.values.contains z && I.tyEq (g.getV z).type (f.getV v).type &&
          edges.all fun (iT, iS, E) =>
            match (g.getV z).args[iT]?, along iS E with
            | some a, some w => a == w
            | _, _ => false
      match carrier with
      | some z => some z
      | none =>
        match edges with
        | (_, iS, E) :: rest =>
          match along iS E with
          | some w =>
            if !gB.values.contains w && rest.all (fun (_, iS', E') => along iS' E' == some w)
            then some w else none
          | none => none
        | [] => none
    let out : Facts := (I.vs.zip pin).map fun (v, w?) =>
      match w? with
      | none => none
      | some w =>
        let copy := gB.values.find? fun x =>
          !isPhiIn g x && !fB.values.contains x && (g.getV x).op == .Copy &&
            (g.getV x).args == #[w] && I.tyEq (g.getV x).type (f.getV v).type
        match copy with
        | some x => some x
        | none => some w
    if edges.isEmpty && !gB.preds.isEmpty then none else some (pin, out)
  | _, _ => some (I.dflt, I.dflt)

/-- The fact table: rounds of `computeFacts` over `K` from nothing known (optimistic: unknown
edges are ignored, so facts along cycles of the plan's blocks are found), `K.size + 2` rounds;
blocks still unknown get no facts. -/
def factTab : FactTab := Id.run do
  let mut T : Array (ID × Option (Facts × Facts)) := #[]
  for _ in [0:I.K.size + 2] do
    let outK (B : ID) : Option Facts :=
      if I.region.contains B || B == I.s.b then
        ((T.find? (·.1 == B)).bind (·.2)).map (·.2)
      else some I.dflt
    T := I.K.map fun B => (B, I.computeFacts f g outK B)
  let none' : Facts := I.vs.map fun _ => none
  return T.map fun (B, o) => (B, o.getD (none', none'))

/-! ## The global checks -/

/-- Before the rewrite (see the module doc). -/
def preOK : Bool :=
  match f.block? I.s.b with
  | none => false
  | some B =>
    f.blocks.contains I.s.b &&
    B.id == I.s.b && B.values == I.bvals && B.kind == .If && I.s.p != I.s.b && I.t != I.s.b &&
    B.preds[I.s.cidx]? == some ⟨I.s.p, I.s.pi⟩ && I.last + 1 == B.preds.size &&
    I.vs == I.bvals.filter (fun x => x != I.s.ctl && isPhiIn f x) &&
    (I.vs.isEmpty || B.preds.size == 2) &&
    match B.controls[0]?, f.value? I.s.ctl with
    | some top, some cv =>
      B.controls.size == 1 && cv.op == .Phi && B.values.contains I.s.ctl &&
      match chainOf f B I.s.ctl (B.values.size + 1) top, cv.args[I.s.cidx]? with
      | some (chain, par), some c =>
        (match f.value? c with
         | some cc => cc.op == .ConstBool && cc.args.isEmpty &&
             B.succs[if (cc.auxInt != 0) ^^ par then 0 else 1]? == some I.s.te
         | none => false) &&
        B.values.all (fun x => x == I.s.ctl || chain.contains x || isPhiIn f x)
      | _, _ => false
    | _, _ => false

/-- The redirected edge in `g`. -/
def redirOK : Bool :=
  (f.getB I.t).preds.size == I.tn && (g.getB I.t).preds.size == I.tn + 1 &&
    (g.getB I.t).preds[I.tn]? == some ⟨I.s.p, I.s.pi⟩

/-- A plan block is entered only from `b`, the plan's blocks or along the redirected edge. -/
def regionOK : Bool :=
  I.region.all fun r =>
    r != I.s.b && r != g.entry && I.K.contains r &&
      (g.getB r).preds.all fun e =>
        I.region.contains e.b || e.b == I.s.b || (r == I.t && e == ⟨I.s.p, I.s.pi⟩)

/-- Blocks outside `K` and the values listed outside `K` in `f` are unchanged (but for use
counts). -/
def frameOK : Bool :=
  tabEqBy (fun a b => decide (a = b)) (fun _ => by simp) f.blockTab g.blockTab
      (I.K.contains ·) &&
    tabEqBy sameEntry sameEntry_refl f.valueTab g.valueTab
      (fun x => I.K.contains (f.getV x).block || (f.value? x).isNone)

/-- A register blocks outside `K` may read: not one of `b`'s values, or a moved phi with its
default fact. -/
def freeArg (a : ID) : Bool :=
  !I.bvals.contains a || (I.vs.contains a && I.look I.dflt a == some a)

/-- Blocks outside `K` read only `freeArg` registers (the tables read without allocating). -/
def scanOK : Bool :=
  g.blocks.all fun B =>
    I.K.contains B ||
      (g.blockTab.getD B none).all fun gB =>
        gB.controls.all I.freeArg &&
          gB.values.all fun x => (g.valueTab.getD x none).all fun v => v.args.all I.freeArg

/-- An edge from a checked block to another block carries the default facts. -/
def exitOK (T : FactTab) : Bool :=
  I.K.all fun B =>
    let out := I.outOf T B
    (g.getB B).succs.all fun e =>
      I.K.contains e.b || I.vs.all fun v =>
        I.look I.dflt v == none || I.look out v == I.look I.dflt v

/-! ## Well-formedness and use dominance of `g`, checked locally

`g` is well formed and its uses are dominated on paths (`WFDom`, the invariant of the fuse
loop) without a check of the whole of `g`: the blocks outside `K` are those of `f` (`frameOK`),
so only the blocks of `K` are checked. -/

/-- Predecessor `i` of block `B` (edge `e`) is crosslinked in `g`. -/
def predLinkOK (B : ID) (i : Nat) (e : Edge) : Bool :=
  (g.block? e.b).any fun P => P.succs[e.i]? == some ⟨B, i⟩

/-- Successor `j` of block `B` (edge `e`) is crosslinked in `g`. -/
def succLinkOK (B : ID) (j : Nat) (e : Edge) : Bool :=
  (g.block? e.b).any fun C => C.preds[e.i]? == some ⟨B, j⟩

/-- Block `B` of `K` is well formed in `g`: the per-block loops of `wfCheck` (edges crosslinked
and ending at blocks `B` has an edge with in `f`, or at `p`/`t` (the redirected edge); values in
the table with their ID and per-op shape, listed once; the entry has no predecessors), and an
edge of `f` from or to a block outside `K` keeps its index. -/
def wfKOK (B : ID) : Bool :=
  match f.block? B, g.block? B with
  | some fB, some gB =>
    (B != g.entry || gB.preds.isEmpty) &&
    allIdx gB.preds (fun i e => predLinkOK g B i e &&
      (fB.preds[i]? == some e || e.b == I.s.p || fB.preds.any (·.b == e.b))) &&
    allIdx gB.succs (fun j e => succLinkOK g B j e &&
      (fB.succs[j]? == some e || e.b == I.t || fB.succs.any (·.b == e.b))) &&
    allIdx fB.preds (fun i e => I.K.contains e.b || gB.preds[i]? == some e) &&
    allIdx fB.succs (fun j e => I.K.contains e.b || gB.succs[j]? == some e) &&
    gB.values.all (fun x => (g.value? x).any fun v => v.id == x && WFCheck.valueOK gB v) &&
    (gB.values == fB.values || decide gB.values.toList.Nodup)
  | none, none => true
  | _, _ => false

/-- Register `w` is the argument along `f`'s edge from `P` of one of `b`'s `Phi`s in `f`: it is
defined on every path to `P` (and outside `b`). -/
def availAt (P w : ID) : Bool :=
  !I.bvals.contains w &&
    let fb := f.getB I.s.b
    I.bvals.any fun z => isPhiIn f z &&
      (List.range fb.preds.size).any fun j =>
        (fb.preds[j]?.map (·.b)) == some P && (f.getV z).args[j]? == some w

/-- Every block of `dS` is `b` or is entered only from blocks of `dS`: every path to it in `g`
passes `b`. -/
def dsOK : Bool :=
  I.dS.all fun Y => Y == I.s.b || (Y != g.entry && (g.getB Y).preds.all (I.dS.contains ·.b))

/-- A path of `g` leaves `b` and its redirected edge into the plan's blocks, and leaves those
only through the block a moved phi (default fact) moved to. -/
def closeOK : Bool :=
  I.vs.all fun v => I.look I.dflt v != some v ||
    let M := (g.getV v).block
    I.region.contains M && I.region.contains I.t &&
      (M == I.t || (g.getB M).preds.any fun e => e.b == I.s.b || e.b == I.t) &&
      (g.getB I.s.b).succs.all (I.region.contains ·.b) &&
      I.region.all fun r => r == M || (g.getB r).succs.all (I.region.contains ·.b)

/-- A use in `g` of register `w` that must be defined on every path to block `P` (`a?`: the
source's register at the same place, if the use is one of `f`'s; `rd`: along the redirected
edge): the source's own register outside `b`'s values; or a listed register defined in `P`, a
moved phi read where the source reads it (outside `b` and the plan's blocks), a `Phi` argument of
`b` along an edge from `P`, or (`P` in `dS`) one along every edge into `b`. -/
def useOK (P w : ID) (a? : Option ID) (rd : Bool) : Bool :=
  (a? == some w && !I.bvals.contains w) ||
  (listedIn g w &&
    (DomCert.blockOf g w == P ||
      (a? == some w && !rd && I.freeArg w && P != I.s.b && !I.region.contains P) ||
      I.availAt f P w ||
      (I.dS.contains P && !(g.getB I.s.b).preds.isEmpty &&
        (g.getB I.s.b).preds.all fun e => I.availAt f e.b w)))

/-- The source's argument at the place of argument `iT` of a target `Phi` of block `B` (`fx?`:
the source value, if listed in the source block `fB`), along the target edge `e`: the
source's edge from the same block (or, along the redirected edge, from `b`). -/
def phiSrc (fB : Block) (fx? : Option Value) (B iT : Nat) (e : Edge) : Option ID :=
  fx?.bind fun fv =>
    if fv.op != .Phi then none
    else if I.redir B iT then
      if (fB.preds[I.s.te.i]?.map (·.b)) == some I.s.b then fv.args[I.s.te.i]? else none
    else if fB.preds[I.srcIdx B iT]? == some e then fv.args[I.srcIdx B iT]? else none

/-- The source's argument `k` of a non-`Phi` (`fx?` as for `phiSrc`). -/
def nodeSrc (fx? : Option Value) (k : Nat) : Option ID :=
  fx?.bind fun fv => if fv.op == .Phi then none else fv.args[k]?

/-- The uses of block `B` of `K` in `g` (`useOK`): arguments of its values (of a `Phi` on the
paths to the predecessor), controls. -/
def domKOK (B : ID) : Bool :=
  let fB := f.getB B
  let gB := g.getB B
  let same := gB.values == fB.values
  (gB.values.all fun x =>
    let gx := g.getV x
    let fx? : Option Value := if same || fB.values.contains x then f.value? x else none
    if gx.op == .Phi then
      allIdx gB.preds fun iT e => (gx.args[iT]?).all fun w =>
        I.useOK f g e.b w (I.phiSrc fB fx? B iT e) (I.redir B iT)
    else
      allIdx gx.args fun k w => I.useOK f g B w (nodeSrc fx? k) false) &&
  allIdx gB.controls fun k c => I.useOK f g B c fB.controls[k]? false

end Info

/-- The largest set of blocks of `K` and `b` whose members other than `b` are entered (in `g`)
only from members (loops of the plan's blocks included): from all of them, drop the others by
rounds (untrusted: `dsOK` checks the result). -/
def domSet (g : Func) (b : ID) (K : Array ID) : Array ID := Id.run do
  let mut S := addU K b
  for _ in [0:K.size + 1] do
    S := S.filter fun Y => Y == b || (Y != g.entry && (g.getB Y).preds.all (S.contains ·.b))
  return S

/-- The checker's view of a rewrite at site `s`. -/
def infoOf (tabs : Tables) (f g : Func) (s : Site) : Info :=
  let B := f.getB s.b
  let bvals := B.values
  let vs := bvals.filter fun x => x != s.ctl && isPhiIn f x
  let region := (s.plan.map Plan.region).getD #[]
  let t := s.te.b
  -- the blocks `applySite` changes: `b`, `t`, `p`, the plan's blocks, and the block of `b`'s
  -- last predecessor (`removePred` moves its edge); `frameOK` checks that nothing else changed
  let K := addU (addU (addU (region.foldl addU #[s.b]) t) s.p)
    ((B.preds[B.preds.size - 1]?.map (·.b)).getD s.b)
  let dflt : Facts := vs.map fun v =>
    let gv := g.getV v
    if gv.block != s.b && listedIn g v && gv.op != .Invalid then some v else none
  { tabs, s, bvals, vs, last := B.preds.size - 1, tn := (f.getB t).preds.size, region, K, dflt,
    dS := domSet g s.b K }

/-- **One `shortcircuitBlock` rewrite at site `s`, checked** (see the module doc). -/
def scOK (tabs : Tables) (f g : Func) (s : Site) : Bool :=
  let I := infoOf tabs f g s
  let T := I.factTab f g
  I.preOK f && withPtrEq g.blocks f.blocks (fun _ => g.blocks == f.blocks)
      (fun h => by rw [h]; exact beq_self_eq_true _) &&
    g.entry == f.entry && g.ownAux == f.ownAux &&
    g.valueTab.size == f.valueTab.size && g.blockTab.size == f.blockTab.size &&
    I.K.contains s.b && I.K.contains I.t && I.K.contains s.p &&
    I.redirOK f g && I.regionOK g && I.frameOK f g && I.K.all (I.blockOK f g T) &&
    I.exitOK g T && I.scanOK g && I.K.all (I.wfKOK f g) && I.dsOK g && I.closeOK g &&
    I.K.all (I.domKOK f g)

/-- **`shortcircuitBlock`, checked**: the rewrite if `scOK` accepts it, else `f` unchanged. -/
def shortcircuitBlockChecked (tabs : Tables) (f : Func) (b : ID) : Func × Bool :=
  match siteOf f b with
  | none => (f, false)
  | some s =>
    let g := applySite f s
    if scOK tabs f g s then (g, true) else (f, false)

end GoFV.Opt.ShortCircuit
