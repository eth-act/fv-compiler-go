import GoFV.Proof.AtomSimDen
import GoFV.Proof.Avail

/-!
# What `RewriteCheck.atomsOK` says (issue #113)

`atomsOK f g`: the same entry, blocks and own aux (so the same context up to the function,
`ctx_eq`, and entry frames up to the registers, `entryFrame_eq`); per block the same ID, kind,
successors and number of controls; every atom listed in `g` is listed in the same block of `f`
with the same fields but its arguments (`BlockAtoms.sub`); both schedules exist and list their
roots in the same sequence.
-/

namespace GoFV.Proof.AtomSim

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck GoFV.Proof.Term

/-- The atom `u` of `f` has the fields of the atom `w` of `g`, but its arguments. -/
def SameAtom (u w : Value) : Prop :=
  u.op = w.op ∧ u.type = w.type ∧ u.auxInt = w.auxInt ∧ u.aux = w.aux ∧
    u.args.size = w.args.size ∧ u.block = w.block ∧ u.id = w.id

/-- `x` is a root of `h` (the schedules' filter in `atomsOK`). -/
def rootP (h : Func) (x : ID) : Bool := (h.value? x).any (Sem.isRoot ·.op)

/-- One block of `atomsOK`. -/
structure BlockAtoms (f g : Func) (fb gb : Block) : Prop where
  id : fb.id = gb.id
  kind : fb.kind = gb.kind
  succs : fb.succs = gb.succs
  csize : fb.controls.size = gb.controls.size
  sub : ∀ x ∈ gb.values, ∀ w, g.value? x = some w → termOp w.op = false →
    x ∈ fb.values ∧ ∃ u, f.value? x = some u ∧ SameAtom u w
  sched : ∃ of og, schedule f fb = some of ∧ schedule g gb = some og ∧
    of.toList.filter (rootP f) = og.toList.filter (rootP g)

/-- `atomsOK` as propositions. -/
structure AtomsOK (f g : Func) : Prop where
  entry : f.entry = g.entry
  blocks : f.blocks = g.blocks
  ownAux : f.ownAux = g.ownAux
  block : ∀ b ∈ f.blocks, ∃ fb gb, f.block? b = some fb ∧ g.block? b = some gb ∧
    BlockAtoms f g fb gb

theorem mem_atomsOf {h : Func} {b : Block} {x : ID} :
    x ∈ atomsOf h b ↔ x ∈ b.values ∧ ∃ v, h.value? x = some v ∧ termOp v.op = false := by
  unfold atomsOf
  rw [List.mem_filter, Array.mem_toList_iff]
  constructor
  · rintro ⟨hx, h2⟩
    refine ⟨hx, ?_⟩
    split at h2
    · rename_i v hv; exact ⟨v, hv, by simpa [isAtom] using h2⟩
    · cases h2
  · rintro ⟨hx, v, hv, ht⟩
    refine ⟨hx, ?_⟩
    rw [hv]; simpa [isAtom] using ht

theorem atomsOK_spec {f g : Func} (h : atomsOK f g = true) : AtomsOK f g := by
  unfold atomsOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true'] at h
  obtain ⟨⟨⟨he, hb⟩, ho⟩, hall⟩ := h
  refine ⟨he, hb, ho, fun b hbm => ?_⟩
  have h := hall b hbm
  split at h
  · rename_i fb gb hfb hgb
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨⟨⟨hid, hk⟩, hs⟩, hc⟩, ⟨hsub, -⟩, hsch⟩ := h
    refine ⟨fb, gb, hfb, hgb, hid, hk, hs, hc, fun x hx w hw ht => ?_, ?_⟩
    · have hm : x ∈ atomsOf g gb := mem_atomsOf.2 ⟨hx, w, hw, ht⟩
      have h2 := hsub x hm
      simp only [List.contains_iff_mem] at h2
      obtain ⟨hxf, h2⟩ := h2
      refine ⟨(mem_atomsOf.1 hxf).1, ?_⟩
      split at h2
      · rename_i u w' hu hw'
        rw [hw] at hw'; cases hw'
        simp only [Bool.and_eq_true, beq_iff_eq] at h2
        obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h2
        exact ⟨u, hu, h1, h2, h3, h4, h5, h6, h7⟩
      · cases h2
    · split at hsch
      · rename_i of og hof hog
        exact ⟨of, og, hof, hog, beq_iff_eq.1 hsch⟩
      · cases hsch
  · cases h

/-! ## Contexts and entry frames -/

theorem ctx_eq {tabs : Tables} {f g : Func} (h : f.ownAux = g.ownAux) :
    Ctx.make tabs g =
      { (Ctx.make tabs f) with f := g, sched := (Ctx.make tabs g).sched, tys := (Ctx.make tabs g).tys } := by
  simp only [Ctx.make, abiParams, h]

theorem entryFrame_eq {env : Env} {tabs : Tables} {f g : Func} (h : f.ownAux = g.ownAux)
    (args : List Val) (mem : Mem) :
    entryFrame env (Ctx.make tabs g) args mem =
      { entryFrame env (Ctx.make tabs f) args mem with
        regs := Array.replicate g.valueTab.size none } := by
  rw [ctx_eq (tabs := tabs) h]
  rfl

end GoFV.Proof.AtomSim
