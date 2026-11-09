import GoFV.Proof.AtomSimDen
import GoFV.Proof.Avail

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `RewriteCheck.atomsOK` says (issue #113)

`atomsOK f g`: the same entry, blocks and own aux (so the same context up to the function,
`ctx_eq`, and entry frames up to the registers, `entryFrame_eq`); per block the same ID, kind,
successors and number of controls; every atom listed in `g` is listed in the same block of `f`
with the same fields but its arguments (`BlockAtoms.sub`); both schedules exist and list their
roots in the same sequence.

`AtomsX` (issue #35), what the atom simulation assumes: `AtomsOK`, except that a `Store` of `g`
may have another aux than the one of `f` (`SameAtomX`: a combined store, whose evaluation the
simulation takes from `AtomArgsRefX`) and a root of `f` that is no root of `g` is a `Store` or a
`Zero` (which never panic; issue #151: the forwarding layer's dropped identity writes) or a
`StaticLECall` (the forwarding layer's folded `ifaceeq`/`efaceeq` calls, issue #69; the
simulation takes that it does not panic from `DropNP`); the schedules list the roots both
functions have in the same sequence. `AtomsOK.toX`; `atomsXOK_spec`: `RewriteCheck.atomsXOK`
decides it.
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
    obtain ⟨hid, ⟨hsub, -⟩, hsch⟩ := h
    refine ⟨fb, gb, hfb, hgb, hid, fun x hx w hw ht => ?_, ?_⟩
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

/-! ## The generalised atom relation (issue #35) -/

/-- `SameAtom`, but a `Store` may change its aux. -/
def SameAtomX (u w : Value) : Prop :=
  u.op = w.op ∧ u.type = w.type ∧ u.auxInt = w.auxInt ∧ (u.aux = w.aux ∨ u.op = .Store) ∧
    u.args.size = w.args.size ∧ u.block = w.block ∧ u.id = w.id

theorem SameAtom.toX {u w : Value} (h : SameAtom u w) : SameAtomX u w :=
  ⟨h.1, h.2.1, h.2.2.1, .inl h.2.2.2.1, h.2.2.2.2⟩

/-- One block of `AtomsX`. -/
structure BlockAtomsX (f g : Func) (fb gb : Block) : Prop where
  id : fb.id = gb.id
  sub : ∀ x ∈ gb.values, ∀ w, g.value? x = some w → termOp w.op = false →
    x ∈ fb.values ∧ ∃ u, f.value? x = some u ∧ SameAtomX u w
  sched : ∃ of og, schedule f fb = some of ∧ schedule g gb = some og ∧
    of.toList.filter (fun x => rootP f x && rootP g x) = og.toList.filter (rootP g) ∧
    ∀ x ∈ of.toList, rootP f x = true → rootP g x = false →
      ∃ u, f.value? x = some u ∧ (u.op = .Store ∨ u.op = .Zero ∨ u.op = .StaticLECall)

/-- What the atom simulation assumes of the atoms. -/
structure AtomsX (f g : Func) : Prop where
  entry : f.entry = g.entry
  blocks : f.blocks = g.blocks
  ownAux : f.ownAux = g.ownAux
  block : ∀ b ∈ f.blocks, ∃ fb gb, f.block? b = some fb ∧ g.block? b = some gb ∧
    BlockAtomsX f g fb gb

theorem BlockAtoms.toX {f g : Func} {fb gb : Block} (h : BlockAtoms f g fb gb) :
    BlockAtomsX f g fb gb := by
  obtain ⟨of, og, hof, hog, hfl⟩ := h.sched
  have hg : ∀ x ∈ of.toList, rootP f x = true → rootP g x = true := fun x hx hr => by
    have : x ∈ of.toList.filter (rootP f) := List.mem_filter.2 ⟨hx, hr⟩
    rw [hfl] at this
    exact (List.mem_filter.1 this).2
  refine ⟨h.id, fun x hx w hw ht => ?_, of, og, hof, hog, ?_, fun x hx hr hn => ?_⟩
  · obtain ⟨h1, u, hu, hs⟩ := h.sub x hx w hw ht
    exact ⟨h1, u, hu, hs.toX⟩
  · have h1 : of.toList.filter (fun x => rootP f x && rootP g x) =
        (of.toList.filter (rootP f)).filter (rootP g) := by
      rw [List.filter_filter]
      refine List.filter_congr fun x _ => ?_
      rw [Bool.and_comm]
    rw [h1, hfl, List.filter_filter]
    exact List.filter_congr fun x _ => by rw [Bool.and_self]
  · rw [hg x hx hr] at hn; cases hn

theorem AtomsOK.toX {f g : Func} (h : AtomsOK f g) : AtomsX f g := by
  refine ⟨h.entry, h.blocks, h.ownAux, fun b hb => ?_⟩
  obtain ⟨fb, gb, hfb, hgb, hB⟩ := h.block b hb
  exact ⟨fb, gb, hfb, hgb, hB.toX⟩

theorem atomsXOK_spec {f g : Func} {calls : Bool} (h : atomsXOK f g calls = true) : AtomsX f g := by
  unfold atomsXOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true'] at h
  obtain ⟨⟨⟨he, hb⟩, ho⟩, hall⟩ := h
  refine ⟨he, hb, ho, fun b hbm => ?_⟩
  have h := hall b hbm
  split at h
  · rename_i fb gb hfb hgb
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨hid, hsub⟩, hsch⟩ := h
    refine ⟨fb, gb, hfb, hgb, hid, fun x hx w hw ht => ?_, ?_⟩
    · have hm : x ∈ atomsOf g gb := mem_atomsOf.2 ⟨hx, w, hw, ht⟩
      have h2 := hsub x hm
      simp only [List.contains_iff_mem] at h2
      obtain ⟨hxf, h2⟩ := h2
      refine ⟨(mem_atomsOf.1 hxf).1, ?_⟩
      split at h2
      · rename_i u w' hu hw'
        rw [hw] at hw'; cases hw'
        unfold atomFieldsOK at h2
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h2
        obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h2
        exact ⟨u, hu, h1, h2, h3, h4, h5, h6, h7⟩
      · cases h2
    · split at hsch
      · rename_i of og hof hog
        simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
          Bool.not_eq_true'] at hsch
        obtain ⟨hfl, hdr⟩ := hsch
        refine ⟨of, og, hof, hog, hfl, fun x hx hr hn => ?_⟩
        rcases hdr x hx with (h | h) | h
        · unfold rootB at h; unfold rootP at hr; rw [hr] at h; cases h
        · unfold rootB at h; unfold rootP at hn; rw [hn] at h; cases h
        · cases hu : f.value? x with
          | none => rw [hu] at h; cases h
          | some u =>
            rw [hu] at h
            simp only [Option.any_some, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true] at h
            exact ⟨u, rfl, h.elim (fun h => h.elim .inl (.inr ∘ .inl)) fun h => .inr (.inr h.2)⟩
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
