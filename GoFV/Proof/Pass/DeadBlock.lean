import GoFV.Proof.Pass.DeadRel

/-!
# Removing dead values: one block entry

For a kept block (`DeadRel`), entered by the source and the target in frames that agree on the
values `g` keeps (`Agree`): the target has a schedule (the source's restricted to the kept
values, `targetSched`); when the source enters the block, so does the target, to a frame that
agrees with the source's on the kept values (`enter_ok`); when the source panics, the target
panics alike (`enter_panic`: the panicking root is kept, and the target evaluates before it
only values the source evaluated before it, `Order.transfer`).
-/

namespace GoFV.Proof.Dead

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof
open GoFV.Proof.CopyElim (stepV_of topoRem_append_left topoRem_at topoRem_before prio_panicking)

/-- Everything the simulation uses about the source `f`, the target `g` and the kept blocks
`K`. -/
structure Setup (f g : Func) (K : ID → Prop) : Prop where
  wf : ∃ ce, WF ce f
  wg : ∃ ce, WF ce g
  rel : DeadRel f g K
  chain : Chained f K
  noNil : NoNil f

/-- The target frame agrees with the source frame on the values `g` keeps. -/
def Agree (g : Func) (frS frT : Frame) : Prop :=
  frT = { frS with regs := frT.regs } ∧ frT.regs.size = frS.regs.size ∧
    ∀ a, Listed g a → frT.regs[a]? = frS.regs[a]?

variable {f g : Func} {K : ID → Prop}

/-- A dependency chain whose end is a target node stays among target nodes. -/
theorem _root_.GoFV.Proof.Order.Dep.sub {α : Type} {N N' : α → Prop} {D D' : α → List α}
    (hcl : ∀ x y, N x → N y → x ∈ D y → N' y → N' x ∧ x ∈ D' y) :
    ∀ {x y}, Order.Dep N D x y → N' y → N' x ∧ Order.Dep N' D' x y
  | _, _, .arg hx hy hxy, hy' => by
    obtain ⟨hx', hxy'⟩ := hcl _ _ hx hy hxy hy'
    exact ⟨hx', .arg hx' hy' hxy'⟩
  | _, _, .trans h1 h2, hz => by
    obtain ⟨hy', h2'⟩ := Order.Dep.sub hcl h2 hz
    obtain ⟨hx', h1'⟩ := Order.Dep.sub hcl h1 hy'
    exact ⟨hx', .trans h1' h2'⟩

namespace Setup

variable (S : Setup f g K)
include S

/-- The source and target versions of a kept block. -/
theorem blocks {bid : ID} (hb : K bid) :
    ∃ gb fb, g.block? bid = some gb ∧ f.block? bid = some fb ∧ gb.id = bid ∧ fb.id = bid ∧
      bid ∈ f.blocks ∧ KindRel fb.kind gb.kind ∧ gb.controls = fb.controls ∧
      ∀ x ∈ gb.values, x ∈ fb.values := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  obtain ⟨gb, hgb, hgid⟩ := hwg.blockId bid (S.rel.sub bid hb)
  obtain ⟨fb, hfb, hbf, hk, hc, hsub⟩ := S.rel.block bid hb gb hgb
  obtain ⟨fb', hfb', hfid⟩ := hwf.blockId bid hbf
  rw [hfb] at hfb'; cases hfb'
  exact ⟨gb, fb, hgb, hfb, hgid, hfid, hbf, hk, hc, hsub⟩

/-- The facts of `blocks`, for given source and target blocks. -/
theorem blockFacts {bid : ID} (hb : K bid) {gb fb : Block}
    (hgb : g.block? bid = some gb) (hfb : f.block? bid = some fb) :
    gb.id = bid ∧ fb.id = bid ∧ bid ∈ f.blocks ∧ KindRel fb.kind gb.kind ∧
      gb.controls = fb.controls ∧ ∀ x ∈ gb.values, x ∈ fb.values := by
  obtain ⟨gb', fb', hgb', hfb', h⟩ := S.blocks hb
  rw [hgb] at hgb'; cases hgb'
  rw [hfb] at hfb'; cases hfb'
  exact h

/-- The source and target versions of a kept value. -/
theorem value {bid : ID} (hb : K bid) {gb fb : Block} (hgb : g.block? bid = some gb)
    (hfb : f.block? bid = some fb) {x : ID} (hx : x ∈ gb.values) :
    ∃ gv fv, g.value? x = some gv ∧ f.value? x = some fv ∧ gv.id = x ∧ fv.id = x ∧
      x ∈ fb.values ∧ gv.type = fv.type ∧ (gv.op = .Phi ↔ fv.op = .Phi) ∧
      (gv.op ≠ .Phi → gv.op = fv.op ∧ gv.aux = fv.aux ∧ gv.auxInt = fv.auxInt ∧
        gv.args = fv.args) := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  obtain ⟨gb', fb', hgb', hfb', -, -, hbf, -, -, hsub⟩ := S.blocks hb
  rw [hgb] at hgb'; cases hgb'
  rw [hfb] at hfb'; cases hfb'
  obtain ⟨gv, hgv, hgid, -⟩ := hwg.valueId bid gb ⟨S.rel.sub bid hb, hgb⟩ x hx
  obtain ⟨fv, hfv, hty, hph, hsame⟩ := S.rel.value bid hb gb hgb x hx gv hgv
  obtain ⟨fv', hfv', hfid, -⟩ := hwf.valueId bid fb ⟨hbf, hfb⟩ x (hsub x hx)
  rw [hfv] at hfv'; cases hfv'
  exact ⟨gv, fv, hgv, hfv, hgid, hfid, hsub x hx, hty, hph, hsame⟩

/-- A value kept by `g` that is a value of a kept block of `f` is kept in that block. -/
theorem keptIn {bid : ID} (hb : K bid) {gb fb : Block} (hgb : g.block? bid = some gb)
    (hfb : f.block? bid = some fb) {a : ID} (hl : Listed g a) (ha : a ∈ fb.values) :
    a ∈ gb.values := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  obtain ⟨b', gb', hb', ha'⟩ := hl
  obtain ⟨-, -, -, -, -, -, hbf, -, -, -⟩ := S.blocks hb
  obtain ⟨gv, hgv, -, hgvb⟩ := hwg.valueId b' gb' hb' a ha'
  obtain ⟨fv, hfv, -, hfvb⟩ := hwf.valueId bid fb ⟨hbf, hfb⟩ a ha
  have := S.rel.vblock a gv fv hgv hfv
  rw [hgvb, hfvb] at this
  subst this
  have hgb' := hb'.2
  rw [hgb] at hgb'; cases hgb'
  exact ha'

/-- The target's nodes of a kept block are the source's nodes it keeps. -/
theorem nodeT {bid : ID} (hb : K bid) {gb fb : Block} (hgb : g.block? bid = some gb)
    (hfb : f.block? bid = some fb) {x : ID} :
    NodeIn (schedNodes g gb).toList x ↔ x ∈ gb.values ∧ NodeIn (schedNodes f fb).toList x := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  obtain ⟨-, -, -, -, -, -, hbf, -, -, -⟩ := S.blocks hb
  rw [nodeIn_schedNodes (valuesOwn hwg (S.rel.sub bid hb) hgb),
    nodeIn_schedNodes (valuesOwn hwf hbf hfb)]
  constructor
  · rintro ⟨hx, gv, hgv, hgn⟩
    obtain ⟨gv', fv, hgv', hfv, -, -, hxf, -, hph, -⟩ := S.value hb hgb hfb hx
    rw [hgv] at hgv'; cases hgv'
    exact ⟨hx, hxf, fv, hfv, fun h => hgn (hph.2 h)⟩
  · rintro ⟨hx, -, fv, hfv, hfn⟩
    obtain ⟨gv, fv', hgv, hfv', -, -, -, -, hph, -⟩ := S.value hb hgb hfb hx
    rw [hfv] at hfv'; cases hfv'
    exact ⟨hx, gv, hgv, fun h => hfn (hph.1 h)⟩

/-- A target node's arguments are its source arguments. -/
theorem argsT {bid : ID} (hb : K bid) {gb fb : Block} (hgb : g.block? bid = some gb)
    (hfb : f.block? bid = some fb) {x : ID} (hx : NodeIn (schedNodes g gb).toList x) :
    argsOf (schedNodes g gb).toList x = argsOf (schedNodes f fb).toList x := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  obtain ⟨-, -, -, -, -, -, hbf, -, -, -⟩ := S.blocks hb
  have hbm := S.rel.sub bid hb
  obtain ⟨hxg, gv, hgv, hgn⟩ := (nodeIn_schedNodes (valuesOwn hwg hbm hgb)).1 hx
  obtain ⟨gv', fv, hgv', hfv, -, -, hxf, -, hph, hsame⟩ := S.value hb hgb hfb hxg
  rw [hgv] at hgv'; cases hgv'
  rw [argsOf_schedNodes (valuesOwn hwg hbm hgb) (hwg.valuesNodup _ _ ⟨hbm, hgb⟩) hxg hgv hgn,
    argsOf_schedNodes (valuesOwn hwf hbf hfb) (hwf.valuesNodup _ _ ⟨hbf, hfb⟩) hxf hfv
      (fun h => hgn (hph.2 h)), (hsame hgn).2.2.2]

/-- Source dependencies into a target node are target dependencies. -/
theorem depT {bid : ID} (hb : K bid) {gb fb : Block} (hgb : g.block? bid = some gb)
    (hfb : f.block? bid = some fb) {x y : ID}
    (hd : Order.Dep (NodeIn (schedNodes f fb).toList) (argsOf (schedNodes f fb).toList) x y)
    (hy : NodeIn (schedNodes g gb).toList y) :
    Order.Dep (NodeIn (schedNodes g gb).toList) (argsOf (schedNodes g gb).toList) x y := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  obtain ⟨-, -, -, -, -, -, hbf, -, -, -⟩ := S.blocks hb
  have hbm := S.rel.sub bid hb
  refine (Order.Dep.sub (fun x y hx _ hxy hy' => ?_) hd hy).2
  obtain ⟨hyg, -⟩ := (S.nodeT hb hgb hfb).1 hy'
  obtain ⟨gv, -, hgv, -, -, -, -, -, -, -⟩ := S.value hb hgb hfb hyg
  have hxy' : x ∈ argsOf (schedNodes g gb).toList y := by rw [S.argsT hb hgb hfb hy']; exact hxy
  have hxa : x ∈ gv.args := by
    obtain ⟨-, gv', hgv', hgn⟩ := (nodeIn_schedNodes (valuesOwn hwg hbm hgb)).1 hy'
    rw [hgv] at hgv'; cases hgv'
    rw [argsOf_schedNodes (valuesOwn hwg hbm hgb) (hwg.valuesNodup _ _ ⟨hbm, hgb⟩) hyg hgv hgn]
      at hxy'
    exact Array.mem_toList_iff.1 hxy'
  have hl : Listed g x := hwg.argListed _ _ _ _ ⟨⟨hbm, hgb⟩, hyg, hgv⟩ x hxa
  have hxf : x ∈ fb.values := ((nodeIn_schedNodes (valuesOwn hwf hbf hfb)).1 hx).1
  exact ⟨(S.nodeT hb hgb hfb).2 ⟨S.keptIn hb hgb hfb hl hxf, hx⟩, hxy'⟩

/-- **The target block has a schedule**: the source's, restricted to the kept values. -/
theorem targetSched {bid : ID} (hb : K bid) {gb fb : Block}
    (hgb : g.block? bid = some gb) (hfb : f.block? bid = some fb) {oS : Array ID}
    (hso : schedule f fb = some oS) : ∃ oT, schedule g gb = some oT := by
  obtain ⟨ce', hwg⟩ := S.wg
  have hT := Order.Topo.filter (schedule_spec hso).topo
    (fun x => (schedNodes g gb).toList.any (·.id == x)) (fun x => nodeIn_any)
    (fun x hx => ((S.nodeT hb hgb hfb).1 hx).2)
    (fun x hx a ha _ => by rw [← S.argsT hb hgb hfb hx]; exact ha)
  have hbm := S.rel.sub bid hb
  exact schedule_some (schedNodes_ids (valuesOwn hwg hbm hgb) (hwg.valuesNodup _ _ ⟨hbm, hgb⟩)) hT

end Setup

end GoFV.Proof.Dead
