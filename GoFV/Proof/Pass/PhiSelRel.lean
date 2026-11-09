import GoFV.Proof.Pass.SegSim
import GoFV.Proof.Rules.Lemmas

variable [GoFV.SSA.Sem.Addrs]

/-!
# Selections of `Phi`s of `SliceMake`s: the relation (issue #69)

What the checker `GoFV.Opt.RewriteCheck.psRel` says, declaratively: a selection turned copy
(`PSD`, from `psOK`: `v`, `SliceLen`/`SliceCap` (component `k`) of the `Phi` `p` whose arguments
are `SliceMake`s with argument `k` holding the value of `x` (`PComp`: `x`, or `Sub64 x 0`), is
`Copy x` in `g`), and the relation's global and per-block facts (`psRel_spec`, `PSRel`).
-/

namespace GoFV.Proof.PhiSel

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.RewriteCheck

variable {tabs : Tables} {f g : Func}

/-- What `psComp tabs f c x` says: `c` is `x`, or `Sub64 x z` of the `int64` shape with `z` a
`Const64 [0]` of the `int64` shape. -/
def PComp (tabs : Tables) (f : Func) (c x : ID) : Prop :=
  c = x ∨ ∃ cv z zv, f.value? c = some cv ∧ cv.op = .Sub64 ∧ cv.args.size = 2 ∧
    cv.args[0]? = some x ∧ cv.args[1]? = some z ∧ tabs.ty cv.type = .int .w64 ∧
    f.value? z = some zv ∧ zv.op = .Const64 ∧ zv.auxInt = 0 ∧ tabs.ty zv.type = .int .w64

theorem psComp_spec {c x : ID} (h : psComp tabs f c x = true) : PComp tabs f c x := by
  unfold psComp at h
  simp only [Bool.or_eq_true, beq_iff_eq, Option.any_eq_true, Bool.and_eq_true] at h
  rcases h with h | ⟨cv, hcv, ⟨⟨⟨⟨hop, hsz⟩, h0⟩, hct⟩, hz⟩⟩
  · exact .inl h
  · right
    obtain ⟨zv, hzb, ⟨⟨hzop, hza⟩, hzt⟩⟩ := hz
    cases hz1 : cv.args[1]? with
    | none => rw [hz1] at hzb; cases hzb
    | some z =>
      rw [hz1] at hzb
      exact ⟨cv, z, zv, hcv, by simpa using hop, by simpa using hsz, by simpa using h0, hz1,
        GoFV.Proof.Rules.isInt64Ty_iff.1 hct, hzb, by simpa using hzop, by simpa using hza,
        GoFV.Proof.Rules.isInt64Ty_iff.1 hzt⟩

/-- What `psOK tabs f g v` says. -/
structure PSD (tabs : Tables) (f g : Func) (v : ID) where
  u : Value
  w : Value
  k : Nat
  p : ID
  x : ID
  pv : Value
  xv : Value
  hu : f.value? v = some u
  hw : g.value? v = some w
  hk : psSel u.op = some k
  hp : u.args[0]? = some p
  hx : w.args[0]? = some x
  husz : u.args.size = 1
  hwsz : w.args.size = 1
  hwop : w.op = .Copy
  hwid : w.id = u.id
  hwb : w.block = u.block
  hut : tabs.ty u.type = .int .w64
  hwt : tabs.ty w.type = .int .w64
  hpv : f.value? p = some pv
  hxv : f.value? x = some xv
  hphi : pv.op = .Phi
  hpid : pv.id = p
  hpe : pv.block ≠ f.entry
  hpb : pv.block ∈ f.blocks
  hpl : ∃ blk, f.block? pv.block = some blk ∧ p ∈ blk.values
  hps : GoFV.Proof.Rules.isSliceTy (tabs.ty pv.type) = true
  hxt : tabs.ty xv.type = .int .w64
  hxb : xv.block ≠ pv.block
  hanc : (DomCert.make f).anc xv.block pv.block = true
  hm : ∀ m ∈ pv.args, ∃ mv, f.value? m = some mv ∧ mv.op = .SliceMake ∧ mv.args.size = 3 ∧
    (∃ c, mv.args[k]? = some c ∧ PComp tabs f c x) ∧
    GoFV.Proof.Rules.isSliceTy (tabs.ty mv.type) = true

theorem psSel_some {o : Op} {k : Nat} (h : psSel o = some k) :
    (o = .SliceLen ∧ k = 1) ∨ (o = .SliceCap ∧ k = 2) := by
  unfold psSel at h
  split at h <;> simp_all

theorem psOK_spec {v : ID} (h : psOK tabs f g v = true) : Nonempty (PSD tabs f g v) := by
  unfold psOK at h
  cases hu : f.value? v with
  | none => rw [hu] at h; cases h
  | some u =>
  cases hw : g.value? v with
  | none => rw [hu, hw] at h; cases h
  | some w =>
  rw [hu, hw] at h
  dsimp only at h
  cases hk : psSel u.op with
  | none => rw [hk] at h; cases h
  | some k =>
  cases hp : u.args[0]? with
  | none => rw [hk, hp] at h; cases h
  | some p =>
  cases hx : w.args[0]? with
  | none => rw [hk, hp, hx] at h; cases h
  | some x =>
  rw [hk, hp, hx] at h
  dsimp only at h
  cases hpv : f.value? p with
  | none => rw [hpv] at h; simp at h
  | some pv =>
  cases hxv : f.value? x with
  | none => rw [hpv, hxv] at h; simp at h
  | some xv =>
  rw [hpv, hxv] at h
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, List.all_eq_true,
    Array.all_eq_true', Option.any_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨husz, hwsz⟩, hwop⟩, hwid⟩, hwb⟩, hut⟩, hwt⟩, ⟨⟨⟨⟨⟨⟨⟨⟨⟨hphi, hpid⟩, hpe⟩, hpb⟩,
    hpl⟩, hps⟩, hxt⟩, hxb⟩, hanc⟩, hm⟩⟩ := h
  refine ⟨⟨u, w, k, p, x, pv, xv, hu, hw, hk, hp, hx, husz, hwsz, hwop, hwid, hwb,
    GoFV.Proof.Rules.isInt64Ty_iff.1 hut, GoFV.Proof.Rules.isInt64Ty_iff.1 hwt, hpv, hxv, hphi,
    hpid, hpe, Array.contains_iff_mem.1 hpb, ?_, hps, GoFV.Proof.Rules.isInt64Ty_iff.1 hxt, hxb,
    hanc, fun m hmm => ?_⟩⟩
  · obtain ⟨blk, hblk, hc⟩ := hpl
    exact ⟨blk, hblk, Array.contains_iff_mem.1 hc⟩
  obtain ⟨mv, hmv, hc⟩ := hm m hmm
  obtain ⟨⟨⟨h1, h2⟩, c, h3, h3'⟩, h4⟩ := hc
  exact ⟨mv, hmv, h1, h2, ⟨c, h3, psComp_spec h3'⟩, h4⟩

/-- Two `PSD`s of one value agree. -/
theorem PSD.eq {v : ID} (d d' : PSD tabs f g v) :
    d.u = d'.u ∧ d.w = d'.w ∧ d.k = d'.k ∧ d.p = d'.p ∧ d.x = d'.x := by
  have hu : d.u = d'.u := Option.some.inj (d.hu.symm.trans d'.hu)
  have hw : d.w = d'.w := Option.some.inj (d.hw.symm.trans d'.hw)
  have hk : d.k = d'.k := Option.some.inj (d.hk.symm.trans (hu ▸ d'.hk))
  have hp : d.p = d'.p := Option.some.inj (d.hp.symm.trans (hu ▸ d'.hp))
  have hx : d.x = d'.x := Option.some.inj (d.hx.symm.trans (hw ▸ d'.hx))
  exact ⟨hu, hw, hk, hp, hx⟩

/-- What `psRel` says. -/
structure PSRel (tabs : Tables) (f g : Func) : Prop where
  cfg : DomCert.cfgView g = DomCert.cfgView f
  ownAux : g.ownAux = f.ownAux
  size : g.valueTab.size = f.valueTab.size
  value : ∀ z fv, f.value? z = some fv → ∃ gv, g.value? z = some gv ∧
    (ssSame fv gv = true ∨ Nonempty (PSD tabs f g z))
  none : ∀ z, f.value? z = none → g.value? z = none
  block : ∀ b ∈ f.blocks, ∀ fb, f.block? b = some fb → ∃ gb, g.block? b = some gb ∧
    gb.kind = fb.kind ∧ gb.controls = fb.controls ∧ gb.values = fb.values ∧
    Sem.schedule g gb = Sem.schedule f fb

theorem psRel_spec (h : psRel tabs f g = true) : PSRel tabs f g := by
  unfold psRel at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Array.all_eq_true'] at h
  obtain ⟨⟨⟨⟨hcfg, hown⟩, hsz⟩, hval⟩, hblk⟩ := h
  refine ⟨hcfg, hown, hsz, fun z fv hfv => ?_, fun z hz => ?_, fun b hb fb hfb => ?_⟩
  · have := hval z (GoFV.Proof.lt_of_value? hfv)
    rw [hfv] at this
    cases hgv : g.value? z with
    | none => rw [hgv] at this; cases this
    | some gv =>
      rw [hgv] at this
      simp only [Bool.or_eq_true] at this
      exact ⟨gv, rfl, this.imp id psOK_spec⟩
  · rcases Nat.lt_or_ge z f.valueTab.size with hl | hl
    · have := hval z hl
      rw [hz] at this
      cases hgv : g.value? z with
      | none => rfl
      | some gv => rw [hgv] at this; cases this
    · cases hgv : g.value? z with
      | none => rfl
      | some gv =>
        have h2 : (z : Nat) < f.valueTab.size := by rw [← hsz]; exact GoFV.Proof.lt_of_value? hgv
        exact absurd h2 (Nat.not_lt.2 hl)
  · have := hblk b hb
    rw [hfb] at this
    cases hgb : g.block? b with
    | none => rw [hgb] at this; cases this
    | some gb =>
      rw [hgb] at this
      simp only [Bool.and_eq_true, beq_iff_eq] at this
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := this
      exact ⟨gb, rfl, h1, h2, h3, h4⟩

end GoFV.Proof.PhiSel
