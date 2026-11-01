import GoFV.Opt.ProveCheck.Decide
import GoFV.Opt.Prove.Pass
import GoFV.SSA.DomCert

/-!
# prove's validator: assumptions, per-rewrite checks, the checked pass (issue #24)

`proveChecked` runs the ported `prove` (`GoFV.Opt.Prove.prove`), undoes every rewrite the
validator does not re-derive on the input `f` (`revert`), and returns the result only if the
relation `proveRel` (what the theorem needs) holds between `f` and it; otherwise `f`.

* **Assumptions** (`asmOf`): the path facts of every dominator-tree block — the control `c` of
  an `If` block `p` holds `.bool (k == 0)` in the blocks dominated by `p`'s `k`-th successor
  when that successor has `p` as its only predecessor — and range invariants of `Phi`s
  (candidates: induction variables counting up, `Phi`s of bounded values), kept only if they
  hold on every incoming edge. `factsOK`/`invOK` re-check them in `proveRel`. Relations
  `z - y ≤ c` (signed, for `y ≥ 0`) between a `Phi` `z` and a value `y` of a strict ancestor of
  `z`'s block, in the blocks `z`'s block dominates (candidates: each argument of `z` as `y + c`),
  kept only if they hold on every edge into `z`'s block; `relsOK` re-checks them.
* **Value rewrites** (`valueOK`): the bounded-shift mark (amount below the width), signed →
  unsigned `Rsh` (nonnegative value), `Div`/`Mod` (both nonnegative), `Ctz` → `CtzNonZero`
  (nonzero argument), `Slicemask` → `-1` (positive argument), `Mul` → `And` (both arguments
  0 or 1), each from the ranges of the arguments at the value's block (`rng`).
* **Branch removal** (`branchOK`): an `If` turned `First` keeps the successor its control is
  decided to take (`decides`).
* **Constant-folded arguments** (`foldOK`, `argsOK`): an argument replaced by a constant listed in
  the output, of the argument's shape, whose value the argument is decided to have — a boolean
  by `decides`, an integer by a one-point range when the argument is never a pointer word
  (`intOnly`: a range-table node or a side of a comparison fact). A `Phi`'s argument is read
  under its predecessor's facts (`argAsm`). Folds combine with the value rewrites (`defOK`).

Nothing here is trusted: `GoFV.Proof.ProveCheck` proves `proveRel` sound.
-/

namespace GoFV.Opt.ProveCheck

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck

/-- Depth bound of the range analysis and of `Not` nesting. -/
def rngFuel : Nat := 4

/-- The block `x` is listed in (its own block, if `x` is among its values). -/
def placed? (f : Func) (x : ID) : Option ID :=
  match f.value? x with
  | some v => if (f.block? v.block).any (·.values.contains x) then some v.block else none
  | none => none

/-! ## Assumptions -/

/-- The path fact a block `s` gets from its only predecessor, an `If` with two distinct
successor blocks. -/
def edgeFact (f : Func) (s : ID) : Option (ID × Bool) :=
  match f.block? s with
  | none => none
  | some sb =>
    match sb.preds.toList with
    | [⟨p, k⟩] =>
      match f.block? p with
      | some pb =>
        if pb.kind == .If && pb.succs.size == 2 &&
            (pb.succs[0]?.map (·.b)) != (pb.succs[1]?.map (·.b)) then
          match pb.controls.toList with
          | [c] => some (c, k == 0)
          | _ => none
        else none
      | none => none
    | _ => none

/-- The facts of block `b`. -/
@[inline] def factsAt (F : Array (List (ID × Bool))) (b : ID) : List (ID × Bool) := F[b]?.getD []

/-- A fact usable in tree block `p`: a term placed in a strict ancestor, not listed in `p`. -/
def factOK (f : Func) (C : DomCert.Cert) (p : ID) (pb : Block) (c : ID) : Bool :=
  !pb.values.contains c &&
  match placed? f c, f.value? c with
  | some e, some cv => e != p && C.anc e p && termOp cv.op && f.blocks.contains e
  | _, _ => false

/-- The path facts of every tree block, parents first: the parent's plus the block's own edge
fact, if usable. -/
def factsOf (f : Func) (C : DomCert.Cert) : Array (List (ID × Bool)) := Id.run do
  let tree := f.blocks.filterMap fun b => (C.depthOf b).map (·, b)
  let maxD := tree.foldl (fun m (d, _) => max m d) 0
  let mut F : Array (List (ID × Bool)) := Array.replicate f.blockTab.size []
  for d in [0:maxD + 1] do
    for (d', b) in tree do
      if d' != d then continue
      let up := if b == f.entry then [] else factsAt F (C.up b)
      let own := match edgeFact f b, f.block? b with
        | some (c, v), some bb => if factOK f C b bb c then [(c, v)] else []
        | _, _ => []
      F := F.set! b (own ++ up)
  return F

/-- The own fact of edge `k` of block `pb` (its control's value along that edge). -/
def ownFact (pb : Block) (k : Nat) : List (ID × Bool) :=
  if pb.kind == .If then
    match pb.controls.toList with
    | [c] => [(c, k == 0)]
    | _ => []
  else []

/-- The path facts are justified: the entry has none; every tree block's facts are usable
there (`factOK`) and include its parent's; along every edge of a tree block `p` the target is a
tree block of `f` whose facts are `p`'s or `p`'s own branch on that edge. -/
def factsOK (f : Func) (C : DomCert.Cert) (F : Array (List (ID × Bool))) : Bool :=
  factsAt F f.entry == [] && f.blocks.contains f.entry && C.inTree f.entry &&
  f.blocks.all fun p =>
    !C.inTree p ||
    match f.block? p with
    | none => false
    | some pb =>
      (factsAt F p).all (fun (c, _) => factOK f C p pb c) &&
      (p == f.entry || f.blocks.contains (C.up p) &&
        (factsAt F (C.up p)).all (fun fact => (factsAt F p).contains fact)) &&
      (List.range pb.succs.size).all fun k =>
        match pb.succs[k]? with
        | none => false
        | some e =>
          f.blocks.contains e.b && C.inTree e.b &&
          (factsAt F e.b).all fun fact => (factsAt F p).contains fact || (ownFact pb k).contains fact

/-- The incoming edges of `Phi` `z` from tree blocks: the argument and the edge's facts. -/
def phiEdges (f : Func) (C : DomCert.Cert) (F : Array (List (ID × Bool))) (z : ID) :
    List (ID × List (ID × Bool)) :=
  match placed? f z, f.value? z with
  | some h, some zv =>
    match f.block? h with
    | some hb =>
      (List.range hb.preds.size).filterMap fun i =>
        match (hb.preds[i]? : Option Edge), zv.args[i]? with
        | some e, some a =>
          if !C.inTree e.b then none else
          match f.block? e.b with
          | some pb => some (a, ownFact pb e.i ++ factsAt F e.b)
          | none => none
        | _, _ => none
    | none => []
  | _, _ => []

/-- `r` contains `ra` (or `ra` is empty). -/
def Rng.sub (ra r : Rng) : Bool :=
  ra.empty || (r.ulo ≤ ra.ulo && ra.uhi ≤ r.uhi && r.slo ≤ ra.slo && ra.shi ≤ r.shi)

/-- The invariants `es` hold on every incoming edge of their `Phi`s, assuming `inv`. -/
def invOK (f : Func) (tabs : Tables) (C : DomCert.Cert) (F : Array (List (ID × Bool)))
    (inv : List (ID × Width × Rng)) (es : List (ID × Width × Rng)) : Bool :=
  es.all fun (z, w, r) =>
    (f.value? z).any (fun zv => zv.op == .Phi && intAt tabs zv w) &&
    (phiEdges f C F z).all fun (a, fs) =>
      (f.value? a).any (intAt tabs · w) &&
      (rng f.value? tabs { facts := fs, inv } rngFuel w a).sub r

/-- Candidate invariants: a `Phi` of shape `int w` with an argument `Add (z, Const d)`, `d > 0`
(counting up from its other arguments' minimum); a `Phi` whose arguments have known ranges
(their hull). -/
def invCands (f : Func) (tabs : Tables) (C : DomCert.Cert) (F : Array (List (ID × Bool))) :
    List (ID × Width × Rng) := Id.run do
  let mut out : List (ID × Width × Rng) := []
  for b in f.blocks do
    if !C.inTree b then continue
    let some bb := f.block? b | continue
    for z in bb.values do
      let some zv := f.value? z | continue
      if zv.op != .Phi then continue
      let some w := (tabs.ty zv.type).width? | continue
      let n := w.bits
      let top := Rng.top n
      let edges := phiEdges f C F z
      let isUp (a : ID) : Bool :=
        match f.value? a with
        | some av =>
          (av.op == .Add64 || av.op == .Add32 || av.op == .Add16 || av.op == .Add8) &&
          match av.args.toList with
          | [x, y] =>
            let pos (c : ID) := (f.value? c).any fun cv =>
              (cv.op == .Const64 || cv.op == .Const32 || cv.op == .Const16 || cv.op == .Const8) &&
              cv.auxInt > 0
            (x == z && pos y) || (y == z && pos x)
          | _ => false
        | none => false
      let others := edges.filter fun (a, _) => !isUp a
      let rs := others.map fun (a, fs) => rng f.value? tabs { facts := fs } rngFuel w a
      if rs.isEmpty then continue
      let hull := rs.foldl (fun h r =>
        ⟨min h.ulo r.ulo, max h.uhi r.uhi, min h.slo r.slo, max h.shi r.shi⟩)
        ⟨2 ^ n, 0, 2 ^ n, -2 ^ n⟩
      if others.length < edges.length then
        if hull.slo > top.slo then out := (z, w, Rng.ofS n hull.slo top.shi) :: out
      else if hull != top then out := (z, w, hull) :: out
  return out

/-- Drop invariants that fail until the rest hold. -/
def invFix (f : Func) (tabs : Tables) (C : DomCert.Cert) (F : Array (List (ID × Bool))) :
    Nat → List (ID × Width × Rng) → List (ID × Width × Rng)
  | 0, _ => []
  | fuel + 1, inv =>
    let keep := inv.filter fun e => invOK f tabs C F inv [e]
    if keep.length == inv.length then inv else invFix f tabs C F fuel keep

/-! ## Relations between a `Phi` and a value of a strict ancestor -/

/-- The relations of block `b`. -/
@[inline] def relsAt (RB : Array (List (ID × ID × Width × Int))) (b : ID) :
    List (ID × ID × Width × Int) := RB[b]?.getD []

/-- Relation `(z, y, w, c)` is usable in block `b`: `z` is a `Phi` of shape `int w`, `y` is
placed in a strict ancestor of `b`. -/
def relHere (f : Func) (tabs : Tables) (C : DomCert.Cert) (b : ID)
    (r : ID × ID × Width × Int) : Bool :=
  (f.value? r.1).any (fun zv => zv.op == .Phi && intAt tabs zv r.2.2.1) &&
  match placed? f r.2.1 with
  | some e => e != b && C.anc e b && f.blocks.contains e
  | none => false

/-- The assumptions along successor `k` of block `p` (`pb`) for a relation to `y` at width `w`:
`p`'s facts and the branch taken, `p`'s relations, and `y` nonnegative. -/
def edgeAsm (F : Array (List (ID × Bool))) (inv : List (ID × Width × Rng))
    (RB : Array (List (ID × ID × Width × Int))) (p : ID) (pb : Block) (k : Nat) (y : ID)
    (w : Width) : Asm :=
  { facts := ownFact pb k ++ factsAt F p, inv := (y, w, Rng.nonneg w.bits) :: inv,
    rels := relsAt RB p }

/-- Relation `r` of the successor `e` (block `eb`) of block `p` (`pb`, successor `k`) holds after
`eb`'s `Phi`s: `p` has it and its `Phi` is not `eb`'s, or its `Phi` is `eb`'s and takes an
argument whose difference to `y` is decided under the assumptions along the edge
(`edgeAsm`). -/
def relEdgeOK (f : Func) (tabs : Tables) (F : Array (List (ID × Bool)))
    (inv : List (ID × Width × Rng)) (RB : Array (List (ID × ID × Width × Int))) (p : ID)
    (pb : Block) (k : Nat) (e : Edge) (eb : Block) (r : ID × ID × Width × Int) : Bool :=
  let (z, y, w, c) := r
  if eb.values.contains z then
    (f.value? z).any fun zv =>
      match zv.args[e.i]? with
      | some a =>
        (f.value? a).any (intAt tabs · w) &&
          diffDecides f.value? tabs (edgeAsm F inv RB p pb k y w) linFuel a y w c
      | none => false
  else (relsAt RB p).contains r

/-- The relations hold: each block's are usable there and include its parent's, and along every
edge of a tree block the successor's hold after its `Phi`s (`relEdgeOK`). -/
def relsOK (f : Func) (tabs : Tables) (C : DomCert.Cert) (F : Array (List (ID × Bool)))
    (inv : List (ID × Width × Rng)) (RB : Array (List (ID × ID × Width × Int))) : Bool :=
  f.blocks.all fun p =>
    !C.inTree p ||
    match f.block? p with
    | none => false
    | some pb =>
      (relsAt RB p).all (relHere f tabs C p) &&
      (p == f.entry || (relsAt RB (C.up p)).all fun r => (relsAt RB p).contains r) &&
      (List.range pb.succs.size).all fun k =>
        match pb.succs[k]? with
        | none => false
        | some e =>
          match f.block? e.b with
          | none => false
          | some eb => (relsAt RB e.b).all (relEdgeOK f tabs F inv RB p pb k e eb)

/-- A candidate relation and its `Phi`'s block. -/
abbrev RelC := (ID × ID × Width × Int) × ID

/-- Each candidate in the tree blocks its `Phi`'s block is an ancestor of. -/
def relsBlocks (f : Func) (C : DomCert.Cert) (R : List RelC) : Array (List RelC) := Id.run do
  let mut RB : Array (List RelC) := Array.replicate f.blockTab.size []
  for b in f.blocks do
    if !C.inTree b then continue
    RB := RB.set! b (R.filter fun (_, h) => C.anc h b)
  return RB

/-- Candidate relations: a `Phi` `z` of shape `int w` and each argument as `y + c` (`addConst`),
or `y`, for `y` placed in a strict ancestor of `z`'s block and not a constant. -/
def relCands (f : Func) (tabs : Tables) (C : DomCert.Cert) : List RelC := Id.run do
  let mut out : List RelC := []
  for b in f.blocks do
    if !C.inTree b then continue
    let some bb := f.block? b | continue
    for z in bb.values do
      let some zv := f.value? z | continue
      if zv.op != .Phi then continue
      let some w := (tabs.ty zv.type).width? | continue
      for a in zv.args do
        let a := canon f.value? tabs a
        let (y, c) := (addConst f.value? w a).getD (a, 0)
        let y := canon f.value? tabs y
        if (f.value? y).any (fun yv => termOp yv.op && yv.args.isEmpty) then continue
        let r := (z, y, w, c)
        if relHere f tabs C b r && !out.any (·.1 == r) then out := (r, b) :: out
  return out

/-- The candidates that fail along some edge into a block that has them: into their `Phi`'s
block by `relEdgeOK`, elsewhere unless the source block has them. -/
def relFails (f : Func) (tabs : Tables) (C : DomCert.Cert) (F : Array (List (ID × Bool)))
    (inv : List (ID × Width × Rng)) (RBH : Array (List RelC))
    (RB : Array (List (ID × ID × Width × Int))) : List (ID × ID × Width × Int) := Id.run do
  let mut bad : List (ID × ID × Width × Int) := []
  for p in f.blocks do
    if !C.inTree p then continue
    let some pb := f.block? p | continue
    for k in [0:pb.succs.size] do
      let some e := pb.succs[k]? | continue
      let some eb := f.block? e.b | continue
      for (r, h) in RBH[e.b]?.getD [] do
        if bad.contains r then continue
        let ok := if h == e.b then relEdgeOK f tabs F inv RB p pb k e eb r else C.anc h p
        if !ok then bad := r :: bad
  return bad

/-- Drop candidates that fail until the rest hold; their table per block. -/
def relFix (f : Func) (tabs : Tables) (C : DomCert.Cert) (F : Array (List (ID × Bool)))
    (inv : List (ID × Width × Rng)) : Nat → List RelC → Array (List (ID × ID × Width × Int))
  | 0, _ => Array.replicate f.blockTab.size []
  | fuel + 1, R =>
    let RBH := relsBlocks f C R
    let RB := RBH.map (·.map (·.1))
    let bad := relFails f tabs C F inv RBH RB
    if bad.isEmpty then RB else relFix f tabs C F inv fuel (R.filter fun (r, _) => !bad.contains r)

/-- The assumptions of `f`: the dominator certificate, per block path facts, `Phi` invariants,
per block relations. -/
def asmOf (f : Func) (tabs : Tables) :
    DomCert.Cert × Array (List (ID × Bool)) × List (ID × Width × Rng) ×
      Array (List (ID × ID × Width × Int)) :=
  let C := DomCert.make f
  let F := factsOf f C
  let F := if factsOK f C F then F else Array.replicate f.blockTab.size []
  let cands := invCands f tabs C F
  let inv := invFix f tabs C F (cands.length + 1) cands
  let rc := relCands f tabs C
  let RB := if rc.isEmpty then Array.replicate f.blockTab.size []
    else relFix f tabs C F inv (rc.length + 1) rc
  (C, F, inv, if relsOK f tabs C F inv RB then RB else Array.replicate f.blockTab.size [])

/-! ## Per-rewrite checks -/

/-- Shift ops: value width, amount width, kind (`0` `Lsh`, `1` `Rsh`, `2` `RshU`). -/
def shTab : List (Op × Width × Width × Nat) :=
  [(.Lsh8x8, .w8, .w8, 0), (.Lsh8x16, .w8, .w16, 0), (.Lsh8x32, .w8, .w32, 0),
   (.Lsh8x64, .w8, .w64, 0), (.Lsh16x8, .w16, .w8, 0), (.Lsh16x16, .w16, .w16, 0),
   (.Lsh16x32, .w16, .w32, 0), (.Lsh16x64, .w16, .w64, 0), (.Lsh32x8, .w32, .w8, 0),
   (.Lsh32x16, .w32, .w16, 0), (.Lsh32x32, .w32, .w32, 0), (.Lsh32x64, .w32, .w64, 0),
   (.Lsh64x8, .w64, .w8, 0), (.Lsh64x16, .w64, .w16, 0), (.Lsh64x32, .w64, .w32, 0),
   (.Lsh64x64, .w64, .w64, 0),
   (.Rsh8x8, .w8, .w8, 1), (.Rsh8x16, .w8, .w16, 1), (.Rsh8x32, .w8, .w32, 1),
   (.Rsh8x64, .w8, .w64, 1), (.Rsh16x8, .w16, .w8, 1), (.Rsh16x16, .w16, .w16, 1),
   (.Rsh16x32, .w16, .w32, 1), (.Rsh16x64, .w16, .w64, 1), (.Rsh32x8, .w32, .w8, 1),
   (.Rsh32x16, .w32, .w16, 1), (.Rsh32x32, .w32, .w32, 1), (.Rsh32x64, .w32, .w64, 1),
   (.Rsh64x8, .w64, .w8, 1), (.Rsh64x16, .w64, .w16, 1), (.Rsh64x32, .w64, .w32, 1),
   (.Rsh64x64, .w64, .w64, 1),
   (.Rsh8Ux8, .w8, .w8, 2), (.Rsh8Ux16, .w8, .w16, 2), (.Rsh8Ux32, .w8, .w32, 2),
   (.Rsh8Ux64, .w8, .w64, 2), (.Rsh16Ux8, .w16, .w8, 2), (.Rsh16Ux16, .w16, .w16, 2),
   (.Rsh16Ux32, .w16, .w32, 2), (.Rsh16Ux64, .w16, .w64, 2), (.Rsh32Ux8, .w32, .w8, 2),
   (.Rsh32Ux16, .w32, .w16, 2), (.Rsh32Ux32, .w32, .w32, 2), (.Rsh32Ux64, .w32, .w64, 2),
   (.Rsh64Ux8, .w64, .w8, 2), (.Rsh64Ux16, .w64, .w16, 2), (.Rsh64Ux32, .w64, .w32, 2),
   (.Rsh64Ux64, .w64, .w64, 2)]

/-- Rewrites of one op into another, with the width of the arguments: kind `0` signed →
unsigned `Div`/`Mod` (both arguments nonnegative), `1` `Ctz` → `CtzNonZero` (argument
nonzero), `2` `Mul` → `And` (both arguments 0 or 1). -/
def opTab : List ((Op × Op) × Width × Nat) :=
  [((.Div8, .Div8u), .w8, 0), ((.Div16, .Div16u), .w16, 0), ((.Div32, .Div32u), .w32, 0),
   ((.Div64, .Div64u), .w64, 0), ((.Mod8, .Mod8u), .w8, 0), ((.Mod16, .Mod16u), .w16, 0),
   ((.Mod32, .Mod32u), .w32, 0), ((.Mod64, .Mod64u), .w64, 0),
   ((.Ctz8, .Ctz8NonZero), .w8, 1), ((.Ctz16, .Ctz16NonZero), .w16, 1),
   ((.Ctz32, .Ctz32NonZero), .w32, 1), ((.Ctz64, .Ctz64NonZero), .w64, 1),
   ((.Mul8, .And8), .w8, 2), ((.Mul16, .And16), .w16, 2), ((.Mul32, .And32), .w32, 2),
   ((.Mul64, .And64), .w64, 2)]

/-- The rewrite of `fv` (input) into `gv` (output, same ID, type and aux) is justified under
`A`. -/
def valueOK (D : ID → Option Value) (tabs : Tables) (A : Asm) (fv gv : Value) : Bool :=
  let R := rng D tabs A rngFuel
  fv.type == gv.type && fv.aux == gv.aux &&
  match shTab.lookup fv.op, shTab.lookup gv.op with
  | some (w, a, kf), some (w', a', kg) =>
    fv.args == gv.args && w == w' && a == a' &&
    (kf == kg || (kf == 1 && kg == 2 && (R w (fv.args[0]?.getD 0)).slo ≥ 0)) &&
    (gv.auxInt == fv.auxInt || (gv.auxInt == 1 && (R a (fv.args[1]?.getD 0)).uhi < w.bits))
  | _, _ =>
    match opTab.lookup (fv.op, gv.op) with
    | some (w, 0) =>
      gv.auxInt == 0 && fv.args == gv.args && fv.args.all fun a => (R w a).slo ≥ 0
    | some (w, 1) =>
      gv.auxInt == fv.auxInt && fv.args == gv.args && 1 ≤ (R w (fv.args[0]?.getD 0)).ulo
    | some (w, 2) =>
      gv.auxInt == fv.auxInt && fv.args == gv.args && fv.args.all fun a => (R w a).uhi ≤ 1
    | _ =>
      fv.op == .Slicemask && gv.args.isEmpty && gv.auxInt == -1 &&
      match (tabs.ty fv.type).width? with
      | some w =>
        (gv.op == .Const64 && w == .w64 || gv.op == .Const32 && w == .w32) &&
        1 ≤ (R w (fv.args[0]?.getD 0)).ulo
      | none => false

/-- Branch removal: `fb` (`If c`) became `gb` (`First`, successors kept or swapped), and `c` is
decided to take the kept successor. -/
def branchOK (D : ID → Option Value) (tabs : Tables) (A : Asm) (fb gb : Block) : Bool :=
  fb.kind == .If && gb.kind == .First && gb.controls.isEmpty &&
  match fb.controls.toList, fb.succs.toList with
  | [c], [e0, e1] =>
    (gb.succs == #[e0, e1] && decides D tabs A rngFuel rngFuel c true) ||
    (gb.succs == #[e1, e0] && decides D tabs A rngFuel rngFuel c false)
  | _, _ => false

/-! ## Constant-folded arguments -/

/-- The constant op of width `w`. -/
def constOp : Width → Op
  | .w8 => .Const8
  | .w16 => .Const16
  | .w32 => .Const32
  | .w64 => .Const64

/-- `a`'s value is never a pointer word: its `canon`ical form is a range-table node of integer
shape or a side of a comparison fact. -/
def intOnly (D : ID → Option Value) (tabs : Tables) (A : Asm) (a : ID) : Bool :=
  let a := canon D tabs a
  (D a).any (fun av => termOp av.op && (rTab.lookup av.op).isSome &&
    (tabs.ty av.type).width?.isSome) ||
  A.facts.any fun fact => match relOf D tabs fact with
    | some (x, y, _, _) => x == a || y == a
    | none => false

/-- Argument `a` (of `f`) became the constant `c` (listed in `g`), and `a` is decided to have
`c`'s value: a boolean by `decides`, an integer by a one-point range. -/
def foldOK (D : ID → Option Value) (tabs : Tables) (A : Asm) (g : Func) (a c : ID) : Bool :=
  match D a, g.value? c with
  | some av, some cv =>
    (g.blocks.contains cv.block && (g.block? cv.block).any (·.values.contains c)) &&
    termOp cv.op && cv.args.isEmpty &&
    match tabs.ty av.type, tabs.ty cv.type with
    | .bool, .bool => cv.op == .ConstBool && decides D tabs A rngFuel rngFuel a (cv.auxInt != 0)
    | .int w, .int w' =>
      w == w' && cv.op == constOp w && intOnly D tabs A a &&
      let r := rng D tabs A rngFuel w a
      r.ulo == r.uhi && r.ulo == (BitVec.ofInt w.bits cv.auxInt.toInt).toNat
    | _, _ => false
  | _, _ => false

/-- The assumptions argument `i` of `fv` (listed in `fb`) is read under: a `Phi`'s, its
predecessor's facts and relations; the others', `A`. -/
def argAsm (F : Array (List (ID × Bool))) (inv : List (ID × Width × Rng))
    (RB : Array (List (ID × ID × Width × Int))) (A : Asm) (fb : Block) (fv : Value) (i : Nat) :
    Asm :=
  if fv.op == .Phi then
    let p := (fb.preds[i]?.map (·.b)).getD 0
    { facts := factsAt F p, inv, rels := relsAt RB p }
  else A

/-- Every argument of `gv` is `fv`'s or a justified constant fold of it. -/
def argsOK (D : ID → Option Value) (tabs : Tables) (F : Array (List (ID × Bool)))
    (inv : List (ID × Width × Rng)) (RB : Array (List (ID × ID × Width × Int))) (A : Asm)
    (g : Func) (fb : Block) (fv gv : Value) : Bool :=
  gv.args.size == fv.args.size &&
  (List.range fv.args.size).all fun i =>
    fv.args[i]! == gv.args[i]! ||
      foldOK D tabs (argAsm F inv RB A fb fv i) g fv.args[i]! gv.args[i]!

/-! ## The relation -/

/-- `u` and `w` define the same term (op, type, auxints, arguments). -/
def sameDef (u w : Value) : Bool :=
  u.op == w.op && u.type == w.type && u.auxInt == w.auxInt && u.aux == w.aux && u.args == w.args

/-- The definition `fv` (listed in `fb`) became `gv` justifiably under `A`: kept, rewritten, or
with arguments folded to constants and otherwise kept or rewritten. -/
def defOK (D : ID → Option Value) (tabs : Tables) (F : Array (List (ID × Bool)))
    (inv : List (ID × Width × Rng)) (RB : Array (List (ID × ID × Width × Int))) (A : Asm)
    (g : Func) (fb : Block) (fv gv : Value) : Bool :=
  sameDef fv gv || valueOK D tabs A fv gv ||
  (argsOK D tabs F inv RB A g fb fv gv &&
    (sameDef fv { gv with args := fv.args } || valueOK D tabs A fv { gv with args := fv.args }))

/-- The assumptions at block `b`. -/
def asmAt (F : Array (List (ID × Bool))) (inv : List (ID × Width × Rng))
    (RB : Array (List (ID × ID × Width × Int))) (b : ID) : Asm :=
  { facts := factsAt F b, inv, rels := relsAt RB b }

/-- Every value listed in `f` is listed in the same block of `g`, with a definition justified
under its block's assumptions (`defOK`); every block keeps its terminator or has its branch
removed justifiably. -/
def valuesOK (tabs : Tables) (f g : Func) (F : Array (List (ID × Bool)))
    (inv : List (ID × Width × Rng)) (RB : Array (List (ID × ID × Width × Int))) : Bool :=
  f.blocks.all fun b =>
    match f.block? b, g.block? b with
    | some fb, some gb =>
      let A := asmAt F inv RB b
      (fb.kind == gb.kind && fb.controls == gb.controls && fb.succs == gb.succs ||
        branchOK f.value? tabs A fb gb) &&
      fb.values.all fun x =>
        gb.values.contains x &&
        match f.value? x, g.value? x with
        | some fv, some gv =>
          gv.block == fv.block && defOK f.value? tabs F inv RB A g fb fv gv
        | _, _ => false
    | _, _ => false

/-- **The relation** the theorem needs between `f` and the checked output `g`. -/
def proveRel (tabs : Tables) (f g : Func) : Bool :=
  let A := asmOf f tabs
  atomsOK f g && closedOK f && closedOK g && f.blocks.all (DomCert.make f).inTree &&
    factsOK f (DomCert.make f) A.2.1 && invOK f tabs (DomCert.make f) A.2.1 A.2.2.1 A.2.2.1 &&
    relsOK f tabs (DomCert.make f) A.2.1 A.2.2.1 A.2.2.2 &&
    valuesOK tabs f g A.2.1 A.2.2.1 A.2.2.2

/-! ## The checked pass -/

/-- Recompute every listed value's use count and every block's predecessor edges. -/
def fixup (g : Func) : Func := Id.run do
  let mut uses : Array Nat := Array.replicate g.valueTab.size 0
  for b in g.blocks do
    let some bb := g.block? b | continue
    for x in bb.values do
      for a in (g.getV x).args do
        if a < uses.size then uses := uses.modify a (· + 1)
    for c in bb.controls do
      if c < uses.size then uses := uses.modify c (· + 1)
  let mut g := g
  for b in g.blocks do
    let some bb := g.block? b | continue
    for x in bb.values do
      g := g.modV x fun v => { v with uses := uses[x]?.getD 0 }
  for q in g.blocks do
    let some qb := g.block? q | continue
    for k in [0:qb.succs.size] do
      let e := qb.succs[k]!
      g := g.modB e.b fun cb => { cb with preds := cb.preds.set! e.i ⟨q, k⟩ }
  return g

/-- Counts of accepted and rejected rewrites by class, and the rejected ones. -/
structure Stats where
  acc : Std.HashMap String Nat := {}
  rej : Std.HashMap String Nat := {}
  why : Array (String × ID × ID) := #[]

def Stats.add (s : Stats) (k : String) (ok : Bool) (b x : ID) : Stats :=
  if ok then { s with acc := s.acc.insert k (s.acc.getD k 0 + 1) }
  else { s with rej := s.rej.insert k (s.rej.getD k 0 + 1), why := s.why.push (k, b, x) }

/-- The class of a value rewrite (statistics). -/
def classOf (fv gv : Value) : String :=
  if (shTab.lookup fv.op).isSome then
    if fv.op != gv.op then "Rsh->RshU" else if fv.auxInt != gv.auxInt then "shift bounded"
    else "args"
  else if fv.op == gv.op then "args"
  else if (opTab.lookup (fv.op, gv.op)).isSome then
    s!"{fv.op.name.takeWhile Char.isAlpha}->{gv.op.name}"
  else s!"{fv.op.name}->{gv.op.name}"

/-- Keep the rewrites of `g` (prove's output on `f`) the validator accepts, undo the others;
branch removals are undone unless `branches`. -/
def revert (tabs : Tables) (branches : Bool) (f g : Func) : Func × Stats := Id.run do
  let (_, F, inv, RB) := asmOf f tabs
  let D := f.value?
  let mut st : Stats := {}
  let mut h := g
  for b in f.blocks do
    let (some fb, some gb) := (f.block? b, g.block? b) | continue
    let A := asmAt F inv RB b
    if !(fb.kind == gb.kind && fb.controls == gb.controls && fb.succs == gb.succs) then
      let ok := branchOK D tabs A fb gb
      let cop := ((fb.controls[0]?.bind D).map (·.op.name)).getD "?"
      st := st.add s!"branch {cop}" ok b (fb.controls[0]?.getD 0)
      if !(ok && branches) then
        h := h.modB b fun hb =>
          { hb with kind := fb.kind, controls := fb.controls, succs := fb.succs,
                    likely := fb.likely, pos := fb.pos }
    for x in fb.values do
      let (some fv, some gv) := (f.value? x, g.value? x) | continue
      if sameDef fv gv then continue
      if gv.args.size == fv.args.size then
        -- keep the justified constant folds, then the op rewrite if justified
        let mut args := fv.args
        for i in [0:fv.args.size] do
          let a := fv.args[i]!
          let c := gv.args[i]!
          if a == c then continue
          let ok := foldOK D tabs (argAsm F inv RB A fb fv i) g a c
          st := st.add s!"const arg {if fv.op == .Phi then "phi" else "value"}" ok b x
          if ok then args := args.set! i c
        let gv' := { gv with args := fv.args }
        let opOK := sameDef fv gv' || valueOK D tabs A fv gv'
        if !sameDef fv gv' then st := st.add (classOf fv gv) opOK b x
        let kept := if opOK then gv' else fv
        h := h.modV x fun hv => { kept with args, uses := hv.uses }
      else
        let ok := valueOK D tabs A fv gv
        st := st.add (classOf fv gv) ok b x
        if !ok then h := h.modV x fun hv => { fv with uses := hv.uses }
  return (fixup h, st)

/-- `prove` with every unjustified rewrite undone, and its statistics; the input if the
relation fails. -/
def proveCheckedStats (env : PassEnv) (f : Func) : Except String (Func × Stats) := do
  let p ← Prove.Prover.ofEnv env
  let g ← Prove.prove p f
  let (h, st) := revert env.tables true f g
  return (if proveRel env.tables f h then h else f, st)

end GoFV.Opt.ProveCheck

namespace GoFV.Opt

/-- The checked `prove` (proven-only): the stock port with every rewrite the validator does not
justify undone, kept only if `ProveCheck.proveRel` holds. -/
def proveChecked : Pass := fun env f => do
  let (g, _) ← ProveCheck.proveCheckedStats env f
  return { func := g, tables := env.tables }

end GoFV.Opt
