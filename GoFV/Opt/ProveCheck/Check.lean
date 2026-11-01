import GoFV.Opt.ProveCheck.Decide
import GoFV.Opt.Prove.Pass
import GoFV.SSA.DomCert

/-!
# prove's validator: assumptions, per-rewrite checks, the checked pass (issue #24)

`proveChecked` runs the ported `prove` and keeps each of its rewrites only if the validator
re-derives the fact it needs on the input `f`:

* **assumptions** (`asmOf`): the path facts of every dominator-tree block — the control `c` of
  an `If` block `p` holds `.bool (k == 0)` in the blocks dominated by `p`'s `k`-th successor
  when that successor has `p` as its only predecessor (`c` a term placed in a strict ancestor) —
  and range invariants of `Phi`s (`invOf`: induction variables counting up from a constant,
  `Phi`s of constants), each re-checked on every incoming edge (`invOK`) and dropped otherwise;
* **branch removal** (`branchOK`): an `If` turned `First` whose kept successor is the one its
  control is decided to take (`decides`);
* **value rewrites** (`valueOK`): the bounded-shift mark (amount below the width), signed →
  unsigned `Rsh` (nonnegative value), `Div`/`Mod` (both nonnegative), `Ctz` → `CtzNonZero`
  (nonzero argument), `Slicemask` → `-1` (positive argument), `Mul` → `And` (both arguments
  0 or 1), each from the ranges (`rng`).

A rejected rewrite is undone (`revert`): the block or value of the input; use counts and
predecessor edges are recomputed. Nothing here is trusted: the theorem relies on the
relation checked on the result.
-/

namespace GoFV.Opt.ProveCheck

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck

/-- Depth bound of the range analysis and of `Not` nesting. -/
def rngFuel : Nat := 6

/-- `x` is listed in its block of `f`; its block. -/
def placed? (f : Func) (x : ID) : Option ID :=
  match f.value? x with
  | some v => if (f.block? v.block).any (·.values.contains x) then some v.block else none
  | none => none

/-! ## Assumptions -/

/-- The path fact a block `s` gets from its only predecessor, if that is an `If` with two
distinct successor blocks. -/
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

/-- The path facts of every tree block, by block ID: the parent's plus the block's own edge
fact, if its control is a term placed in a strict ancestor. -/
def factsOf (f : Func) (C : DomCert.Cert) : Array (List (ID × Bool)) := Id.run do
  let n := f.blockTab.size
  -- blocks by depth (parents first)
  let tree := f.blocks.filterMap fun b => (C.depthOf b).map (·, b)
  let sorted := tree.qsort (fun a b => a.1 < b.1)
  let mut F : Array (List (ID × Bool)) := Array.replicate n []
  for (_, b) in sorted do
    let up := if b == f.entry then [] else F[C.up b]?.getD []
    let own := match edgeFact f b with
      | some (c, v) =>
        match placed? f c, f.value? c with
        | some e, some cv => if e != b && C.anc e b && termOp cv.op then [(c, v)] else []
        | _, _ => []
      | none => []
    F := F.set! b (own ++ up)
  return F

/-- The facts of block `b`. -/
@[inline] def factsAt (F : Array (List (ID × Bool))) (b : ID) : List (ID × Bool) := F[b]?.getD []

/-- The path facts are justified: every fact of a tree block is a term placed in a strict
ancestor, the entry has none, and along every edge of a tree block `p` the target's facts are
`p`'s or `p`'s own branch. -/
def factsOK (f : Func) (C : DomCert.Cert) (F : Array (List (ID × Bool))) : Bool :=
  factsAt F f.entry == [] &&
  f.blocks.all fun p =>
    !C.inTree p ||
    match f.block? p with
    | none => false
    | some pb =>
      (factsAt F p).all (fun (c, _) =>
        match placed? f c, f.value? c with
        | some e, some cv => e != p && C.anc e p && termOp cv.op
        | _, _ => false) &&
      (List.range pb.succs.size).all fun k =>
        match pb.succs[k]? with
        | none => false
        | some e =>
          (factsAt F e.b).all fun (c, v) =>
            (factsAt F p).contains (c, v) ||
            (pb.kind == .If && pb.controls == #[c] && v == (k == 0))

/-- The `Phi`s of tree blocks with the edge assumptions of each incoming edge. -/
def phiEdges (f : Func) (C : DomCert.Cert) (F : Array (List (ID × Bool))) (z : ID) :
    List (ID × List (ID × Bool)) :=
  match placed? f z, f.value? z with
  | some h, some zv =>
    match f.block? h with
    | some hb =>
      (List.range hb.preds.size).filterMap fun i =>
        match (hb.preds[i]? : Option Edge), zv.args[i]? with
        | some ⟨p, k⟩, some a =>
          if !C.inTree p then none else
          match f.block? p with
          | some pb =>
            let own := if pb.kind == .If then
                match pb.controls.toList with
                | [c] => [(c, k == 0)]
                | _ => []
              else []
            some (a, own ++ factsAt F p)
          | none => none
        | _, _ => none
    | none => []
  | _, _ => []

/-- The invariants hold on every incoming edge of their `Phi`s, assuming all invariants. -/
def invOK (f : Func) (tabs : Tables) (C : DomCert.Cert) (F : Array (List (ID × Bool)))
    (inv : List (ID × Width × Rng)) : List (ID × Width × Rng) → Bool
  | [] => true
  | (z, w, r) :: rest =>
    ((f.value? z).any (·.op == .Phi)) &&
    (phiEdges f C F z).all (fun (a, fs) =>
      let ra := rng f.value? tabs { facts := fs, inv } rngFuel w a
      ra.empty || (r.ulo ≤ ra.ulo && ra.uhi ≤ r.uhi && r.slo ≤ ra.slo && ra.shi ≤ r.shi)) &&
    invOK f tabs C F inv rest

/-- Candidate invariants: a `Phi` of shape `int w` with an argument `Add (z, Const d)`, `d > 0`
(counting up from its other arguments' minimum); a `Phi` all of whose other arguments have
known ranges (their hull). -/
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
      let hull := rs.foldl (fun h r => ⟨min h.ulo r.ulo, max h.uhi r.uhi, min h.slo r.slo, max h.shi r.shi⟩)
        ⟨2 ^ n, 0, 2 ^ n, -2 ^ n⟩
      if others.length < edges.length then
        -- counting up: from the minimum of the starts to the signed maximum
        if hull.slo > top.slo then out := (z, w, Rng.ofS n hull.slo top.shi) :: out
      else if hull != top then out := (z, w, hull) :: out
  return out

/-- Drop invariants that fail until the rest hold (each round drops at least one). -/
def invFix (f : Func) (tabs : Tables) (C : DomCert.Cert) (F : Array (List (ID × Bool))) :
    Nat → List (ID × Width × Rng) → List (ID × Width × Rng)
  | 0, _ => []
  | fuel + 1, inv =>
    let keep := inv.filter fun e => invOK f tabs C F inv [e]
    if keep.length == inv.length then inv else invFix f tabs C F fuel keep

/-- The assumptions of `f`: per block path facts and the `Phi` invariants (both re-checked;
empty if a check fails). -/
def asmOf (f : Func) (tabs : Tables) : DomCert.Cert × Array (List (ID × Bool)) × List (ID × Width × Rng) :=
  let C := DomCert.make f
  let F := factsOf f C
  let F := if factsOK f C F then F else Array.replicate f.blockTab.size []
  let cands := invCands f tabs C F
  let inv := invFix f tabs C F (cands.length + 1) cands
  (C, F, inv)

/-! ## Per-rewrite checks -/

/-- Shift ops: `(value width, amount width, kind)` with kind 0 `Lsh`, 1 `Rsh`, 2 `RshU`. -/
def shiftOf : Op → Option (Width × Width × Nat)
  | .Lsh8x8 => some (.w8, .w8, 0) | .Lsh8x16 => some (.w8, .w16, 0)
  | .Lsh8x32 => some (.w8, .w32, 0) | .Lsh8x64 => some (.w8, .w64, 0)
  | .Lsh16x8 => some (.w16, .w8, 0) | .Lsh16x16 => some (.w16, .w16, 0)
  | .Lsh16x32 => some (.w16, .w32, 0) | .Lsh16x64 => some (.w16, .w64, 0)
  | .Lsh32x8 => some (.w32, .w8, 0) | .Lsh32x16 => some (.w32, .w16, 0)
  | .Lsh32x32 => some (.w32, .w32, 0) | .Lsh32x64 => some (.w32, .w64, 0)
  | .Lsh64x8 => some (.w64, .w8, 0) | .Lsh64x16 => some (.w64, .w16, 0)
  | .Lsh64x32 => some (.w64, .w32, 0) | .Lsh64x64 => some (.w64, .w64, 0)
  | .Rsh8x8 => some (.w8, .w8, 1) | .Rsh8x16 => some (.w8, .w16, 1)
  | .Rsh8x32 => some (.w8, .w32, 1) | .Rsh8x64 => some (.w8, .w64, 1)
  | .Rsh16x8 => some (.w16, .w8, 1) | .Rsh16x16 => some (.w16, .w16, 1)
  | .Rsh16x32 => some (.w16, .w32, 1) | .Rsh16x64 => some (.w16, .w64, 1)
  | .Rsh32x8 => some (.w32, .w8, 1) | .Rsh32x16 => some (.w32, .w16, 1)
  | .Rsh32x32 => some (.w32, .w32, 1) | .Rsh32x64 => some (.w32, .w64, 1)
  | .Rsh64x8 => some (.w64, .w8, 1) | .Rsh64x16 => some (.w64, .w16, 1)
  | .Rsh64x32 => some (.w64, .w32, 1) | .Rsh64x64 => some (.w64, .w64, 1)
  | .Rsh8Ux8 => some (.w8, .w8, 2) | .Rsh8Ux16 => some (.w8, .w16, 2)
  | .Rsh8Ux32 => some (.w8, .w32, 2) | .Rsh8Ux64 => some (.w8, .w64, 2)
  | .Rsh16Ux8 => some (.w16, .w8, 2) | .Rsh16Ux16 => some (.w16, .w16, 2)
  | .Rsh16Ux32 => some (.w16, .w32, 2) | .Rsh16Ux64 => some (.w16, .w64, 2)
  | .Rsh32Ux8 => some (.w32, .w8, 2) | .Rsh32Ux16 => some (.w32, .w16, 2)
  | .Rsh32Ux32 => some (.w32, .w32, 2) | .Rsh32Ux64 => some (.w32, .w64, 2)
  | .Rsh64Ux8 => some (.w64, .w8, 2) | .Rsh64Ux16 => some (.w64, .w16, 2)
  | .Rsh64Ux32 => some (.w64, .w32, 2) | .Rsh64Ux64 => some (.w64, .w64, 2)
  | _ => none

/-- Signed division/remainder ops and their unsigned versions, by width. -/
def divOf : Op → Option (Width × Op)
  | .Div8 => some (.w8, .Div8u) | .Div16 => some (.w16, .Div16u)
  | .Div32 => some (.w32, .Div32u) | .Div64 => some (.w64, .Div64u)
  | .Mod8 => some (.w8, .Mod8u) | .Mod16 => some (.w16, .Mod16u)
  | .Mod32 => some (.w32, .Mod32u) | .Mod64 => some (.w64, .Mod64u)
  | _ => none

def ctzOf : Op → Option (Width × Op)
  | .Ctz8 => some (.w8, .Ctz8NonZero) | .Ctz16 => some (.w16, .Ctz16NonZero)
  | .Ctz32 => some (.w32, .Ctz32NonZero) | .Ctz64 => some (.w64, .Ctz64NonZero)
  | _ => none

def mulOf : Op → Option (Width × Op)
  | .Mul8 => some (.w8, .And8) | .Mul16 => some (.w16, .And16)
  | .Mul32 => some (.w32, .And32) | .Mul64 => some (.w64, .And64)
  | _ => none

/-- `x` is nonnegative (signed) at width `w`. -/
@[inline] def nonneg (r : Rng) : Bool := r.empty || 0 ≤ r.slo

/-- The rewrite of `fv` (input) into `gv` (output, same ID) is justified under `A`. -/
def valueOK (D : ID → Option Value) (tabs : Tables) (A : Asm) (fv gv : Value) : Bool :=
  let R := rng D tabs A rngFuel
  fv.type == gv.type && fv.aux == gv.aux &&
  match shiftOf fv.op, shiftOf gv.op with
  | some (w, a, kf), some (w', a', kg) =>
    -- same args; mark `bounded` only if the amount is below the width; `Rsh` → `RshU` only on
    -- a nonnegative value
    fv.args == gv.args && w == w' && a == a' &&
    (kf == kg || (kf == 1 && kg == 2 && nonneg (R w (fv.args[0]?.getD 0)))) &&
    (gv.auxInt == fv.auxInt || (gv.auxInt == 1 &&
      let r := R a (fv.args[1]?.getD 0)
      r.empty || r.uhi < w.bits))
  | _, _ =>
    match divOf fv.op with
    | some (w, u) =>
      gv.op == u && gv.auxInt == 0 && fv.args == gv.args &&
      fv.args.all (fun a => nonneg (R w a))
    | none =>
    match ctzOf fv.op with
    | some (w, nz) =>
      gv.op == nz && gv.auxInt == fv.auxInt && fv.args == gv.args &&
      let r := R w (fv.args[0]?.getD 0)
      r.empty || 1 ≤ r.ulo
    | none =>
    match mulOf fv.op with
    | some (w, andOp) =>
      gv.op == andOp && gv.auxInt == fv.auxInt && fv.args == gv.args &&
      fv.args.all (fun a => let r := R w a; r.empty || r.uhi ≤ 1)
    | none =>
    if fv.op == .Slicemask then
      match (tabs.ty fv.type).width? with
      | some w =>
        ((w == .w64 && gv.op == .Const64) || (w == .w32 && gv.op == .Const32)) &&
        gv.auxInt == -1 && gv.args.isEmpty &&
        (let r := R w (fv.args[0]?.getD 0); r.empty || 1 ≤ r.ulo)
      | none => false
    else false

/-- Branch removal: `fb` (`If c`) became `gb` (`First`, successors kept or swapped), and `c` is
decided to take the kept successor. -/
def branchOK (D : ID → Option Value) (tabs : Tables) (A : Asm) (fb gb : Block) : Bool :=
  fb.kind == .If && gb.kind == .First && gb.controls.isEmpty && fb.succs.size == 2 &&
  match fb.controls.toList, fb.succs.toList with
  | [c], [e0, e1] =>
    (gb.succs == #[e0, e1] && decides D tabs A rngFuel rngFuel c true) ||
    (gb.succs == #[e1, e0] && decides D tabs A rngFuel rngFuel c false)
  | _, _ => false

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

/-- Counts of accepted and rejected rewrites by class. -/
structure Stats where
  acc : Std.HashMap String Nat := {}
  rej : Std.HashMap String Nat := {}

def Stats.add (s : Stats) (k : String) (ok : Bool) : Stats :=
  if ok then { s with acc := s.acc.insert k (s.acc.getD k 0 + 1) }
  else { s with rej := s.rej.insert k (s.rej.getD k 0 + 1) }

/-- The class of a value rewrite (statistics). -/
def classOf (fv gv : Value) : String :=
  if (shiftOf fv.op).isSome then
    if fv.op != gv.op then "Rsh->RshU" else "shift bounded"
  else if (divOf fv.op).isSome then "DivMod->u"
  else if (ctzOf fv.op).isSome then "Ctz->NonZero"
  else if (mulOf fv.op).isSome then s!"Mul->{gv.op.name.takeWhile Char.isAlpha}"
  else if fv.op == .Slicemask then "Slicemask->Const"
  else if fv.op == gv.op then "args" else s!"{fv.op.name}->{gv.op.name}"

/-- Keep the rewrites of `g` (prove's output on `f`) the validator accepts, undo the others. -/
def revert (tabs : Tables) (f g : Func) : Func × Stats := Id.run do
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
      st := st.add s!"branch {cop}" ok
      if !ok then
        h := h.modB b fun hb =>
          { hb with kind := fb.kind, controls := fb.controls, succs := fb.succs,
                    likely := fb.likely, pos := fb.pos }
    for x in fb.values do
      let (some fv, some gv) := (f.value? x, g.value? x) | continue
      if fv.op == gv.op && fv.args == gv.args && fv.auxInt == gv.auxInt && fv.aux == gv.aux &&
          fv.type == gv.type then continue
      let ok := valueOK D tabs A fv gv
      st := st.add (classOf fv gv) ok
      if !ok then h := h.modV x fun hv => { fv with uses := hv.uses }
  return (fixup h, st)

/-- The checked `prove`: the stock port with every unjustified rewrite undone. -/
def proveCheckedFunc (env : PassEnv) (f : Func) : Except String (Func × Stats) := do
  let p ← Prove.Prover.ofEnv env
  let g ← Prove.prove p f
  return revert env.tables f g

end GoFV.Opt.ProveCheck
