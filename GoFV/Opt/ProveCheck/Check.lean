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
  hold on every incoming edge. `factsOK`/`invOK` re-check them in `proveRel`.
* **Value rewrites** (`valueOK`): the bounded-shift mark (amount below the width), signed →
  unsigned `Rsh` (nonnegative value), `Div`/`Mod` (both nonnegative), `Ctz` → `CtzNonZero`
  (nonzero argument), `Slicemask` → `-1` (positive argument), `Mul` → `And` (both arguments
  0 or 1), each from the ranges of the arguments at the value's block (`rng`).
* **Branch removal** (`branchOK`): an `If` turned `First` keeps the successor its control is
  decided to take (`decides`).

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
  let sorted := tree.qsort (fun a b => a.1 < b.1)
  let mut F : Array (List (ID × Bool)) := Array.replicate f.blockTab.size []
  for (_, b) in sorted do
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
      (p == f.entry || (factsAt F (C.up p)).all (fun fact => (factsAt F p).contains fact)) &&
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
    (f.value? z).any (·.op == .Phi) &&
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

/-- The assumptions of `f`: the dominator certificate, per block path facts, `Phi` invariants. -/
def asmOf (f : Func) (tabs : Tables) :
    DomCert.Cert × Array (List (ID × Bool)) × List (ID × Width × Rng) :=
  let C := DomCert.make f
  let F := factsOf f C
  let F := if factsOK f C F then F else Array.replicate f.blockTab.size []
  let cands := invCands f tabs C F
  (C, F, invFix f tabs C F (cands.length + 1) cands)

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

/-! ## The relation -/

/-- `u` and `w` define the same term (op, type, auxints, arguments). -/
def sameDef (u w : Value) : Bool :=
  u.op == w.op && u.type == w.type && u.auxInt == w.auxInt && u.aux == w.aux && u.args == w.args

/-- Every value listed in `f` is listed in the same block of `g`, with the same definition or a
justified rewrite under its block's assumptions; every block keeps its terminator or has its
branch removed justifiably. -/
def valuesOK (tabs : Tables) (f g : Func) (F : Array (List (ID × Bool)))
    (inv : List (ID × Width × Rng)) : Bool :=
  f.blocks.all fun b =>
    match f.block? b, g.block? b with
    | some fb, some gb =>
      let A : Asm := { facts := factsAt F b, inv }
      (fb.kind == gb.kind && fb.controls == gb.controls && fb.succs == gb.succs ||
        branchOK f.value? tabs A fb gb) &&
      fb.values.all fun x =>
        gb.values.contains x &&
        match f.value? x, g.value? x with
        | some fv, some gv =>
          gv.block == fv.block && (sameDef fv gv || valueOK f.value? tabs A fv gv)
        | _, _ => false
    | _, _ => false

/-- The rewritten values of `g` (listed in `f`, a different definition in `g`) and their blocks. -/
def rewritten (f g : Func) : List (ID × ID) :=
  f.blocks.toList.flatMap fun b =>
    match f.block? b with
    | some fb => fb.values.toList.filterMap fun x =>
        match f.value? x, g.value? x with
        | some fv, some gv => if sameDef fv gv then none else some (x, b)
        | _, _ => none
    | none => []

/-- The argument of a `Phi` of block `b` is computed in the dominator subtree of its block `ba`;
the rewritten values there that it may read are in ancestors of `b` (their facts hold at
`b`). -/
def phiArgsOK (f : Func) (C : DomCert.Cert) (rw : List (ID × ID)) : Bool :=
  rw.isEmpty ||
  f.blocks.all fun b =>
    match f.block? b with
    | some bb =>
      bb.values.all fun z =>
        match f.value? z with
        | some zv =>
          zv.op != .Phi || zv.args.all fun a =>
            match placed? f a with
            | some ba => C.anc ba b || rw.all fun (_, br) => !C.anc br ba || C.anc br b
            | none => false
        | none => false
    | none => false

/-- **The relation** the theorem needs between `f` and the checked output `g`. -/
def proveRel (tabs : Tables) (f g : Func) : Bool :=
  let (C, F, inv) := asmOf f tabs
  atomsOK f g && closedOK f && closedOK g && f.blocks.all C.inTree && factsOK f C F &&
  invOK f tabs C F inv inv && valuesOK tabs f g F inv && phiArgsOK f C (rewritten f g)

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
  let (_, F, inv) := asmOf f tabs
  let D := f.value?
  let mut st : Stats := {}
  let mut h := g
  for b in f.blocks do
    let (some fb, some gb) := (f.block? b, g.block? b) | continue
    let A : Asm := { facts := factsAt F b, inv }
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
      let ok := valueOK D tabs A fv gv
      st := st.add (classOf fv gv) ok b x
      if !ok then h := h.modV x fun hv => { fv with uses := hv.uses }
  -- rewrites a `Phi` of a block they do not dominate may read (`phiArgsOK`)
  let C := DomCert.make f
  let anchors : List (ID × ID) := f.blocks.toList.flatMap fun b =>
    match f.block? b with
    | some bb => bb.values.toList.flatMap fun z =>
        match f.value? z with
        | some zv => if zv.op != .Phi then [] else zv.args.toList.filterMap fun a =>
            match placed? f a with
            | some ba => if C.anc ba b then none else some (ba, b)
            | none => none
        | none => []
    | none => []
  for (x, br) in rewritten f h do
    if anchors.any (fun (ba, b) => C.anc br ba && !C.anc br b) then
      let (some fv, some gv) := (f.value? x, h.value? x) | continue
      st := { st with rej := st.rej.insert "phi-read" (st.rej.getD "phi-read" 0 + 1),
                      why := st.why.push (s!"phi-read {classOf fv gv}", br, x) }
      h := h.modV x fun hv => { fv with uses := hv.uses }
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
