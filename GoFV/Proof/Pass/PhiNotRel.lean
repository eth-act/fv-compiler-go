import GoFV.Proof.Pass.PhiSelRel

/-!
# `Phi`s of `Not`s: the relation (issue #69)

What the checker `GoFV.Opt.RewriteCheck.pnRel` says, declaratively: a `Phi` turned the `Not` of a
fresh `Phi` (`PND`, from `pnOK`: the `Phi` `v` of a `bool` shape, outside the entry block, is
`Not p` in `g`, where `p` is no value of `f` and a `Phi` of `v`'s type in `v`'s block whose
argument `j` is the argument of `v`'s argument `j`, a `Not`), and the relation's global and
per-block facts (`pnRel_spec`, `PNRel`).
-/

namespace GoFV.Proof.PhiNot

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.RewriteCheck

variable {tabs : Tables} {f g : Func}

theorem ty_bool {t : Ty} (h : (match t with | .bool => true | _ => false) = true) : t = .bool := by
  cases t <;> first | rfl | cases h

/-- What `pnOK tabs f g v` says. -/
structure PND (tabs : Tables) (f g : Func) (v : ID) where
  u : Value
  w : Value
  p : ID
  pv : Value
  hu : f.value? v = some u
  hw : g.value? v = some w
  hp : w.args[0]? = some p
  hphi : u.op = .Phi
  hwop : w.op = .Not
  hwsz : w.args.size = 1
  hwid : w.id = v
  hwb : w.block = u.block
  hwt : w.type = u.type
  hut : tabs.ty u.type = .bool
  hent : u.block ≠ f.entry
  hpf : f.value? p = none
  hpl : ∃ gb, g.block? u.block = some gb ∧ p ∈ gb.values
  hpv : g.value? p = some pv
  hpphi : pv.op = .Phi
  hpid : pv.id = p
  hpb : pv.block = u.block
  hpt : pv.type = u.type
  hpsz : pv.args.size = u.args.size
  hargs : ∀ (j : Nat) (c a : ID), pv.args[j]? = some c → u.args[j]? = some a → ∃ av cv, f.value? a = some av ∧
    av.op = .Not ∧ av.args.size = 1 ∧ av.args[0]? = some c ∧ tabs.ty av.type = .bool ∧
    f.value? c = some cv ∧ tabs.ty cv.type = .bool

theorem pnOK_spec {v : ID} (h : pnOK tabs f g v = true) : Nonempty (PND tabs f g v) := by
  unfold pnOK at h
  cases hu : f.value? v with
  | none => rw [hu] at h; cases h
  | some u =>
  cases hw : g.value? v with
  | none => rw [hu, hw] at h; cases h
  | some w =>
  rw [hu, hw] at h
  dsimp only at h
  cases hp : w.args[0]? with
  | none => rw [hp] at h; cases h
  | some p =>
  rw [hp] at h
  dsimp only at h
  cases hpv : g.value? p with
  | none => rw [hpv] at h; simp at h
  | some pv =>
  rw [hpv] at h
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Option.any_some,
    Option.isNone_iff_eq_none, Option.any_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hphi, hwop⟩, hwsz⟩, hwid⟩, hwb⟩, hwt⟩, hut⟩, hent⟩, hpf⟩, hpl⟩,
    ⟨⟨⟨⟨hpphi, hpid⟩, hpb⟩, hpt⟩, hpsz⟩, hz⟩ := h
  refine ⟨⟨u, w, p, pv, hu, hw, hp, hphi, hwop, hwsz, hwid, hwb, hwt, ty_bool hut, hent, hpf,
    ?_, hpv, hpphi, hpid, hpb, hpt, hpsz, fun j c a hc ha => ?_⟩⟩
  · obtain ⟨gb, hgb, hc⟩ := hpl
    exact ⟨gb, hgb, Array.contains_iff_mem.1 hc⟩
  · have hm : (c, a) ∈ pv.args.toList.zip u.args.toList := by
      rw [List.mem_iff_getElem?]
      exact ⟨j, List.getElem?_zip_eq_some.2 ⟨by rw [Array.getElem?_toList]; exact hc,
        by rw [Array.getElem?_toList]; exact ha⟩⟩
    obtain ⟨av, hav, ⟨⟨⟨hop, hsz⟩, h0⟩, hat⟩, cv, hcv, hct⟩ := hz _ hm
    exact ⟨av, cv, hav, hop, hsz, h0, ty_bool hat, hcv, ty_bool hct⟩

/-- Two `PND`s of one value agree. -/
theorem PND.eq {v : ID} (d d' : PND tabs f g v) : d.u = d'.u ∧ d.w = d'.w ∧ d.p = d'.p := by
  have hu : d.u = d'.u := Option.some.inj (d.hu.symm.trans d'.hu)
  have hw : d.w = d'.w := Option.some.inj (d.hw.symm.trans d'.hw)
  have hp : d.p = d'.p := Option.some.inj (d.hp.symm.trans (hw ▸ d'.hp))
  exact ⟨hu, hw, hp⟩

/-- What `pnFresh tabs f g z` says: `z` is the fresh `Phi` of a `pnOK` value `v` listed in `z`'s
block of `g`. -/
theorem pnFresh_spec {z : ID} (h : pnFresh tabs f g z = true) :
    ∃ v zv gb, g.value? z = some zv ∧ g.block? zv.block = some gb ∧ v ∈ gb.values ∧
      Nonempty (PND tabs f g v) ∧ ∀ d : PND tabs f g v, d.p = z := by
  unfold pnFresh at h
  cases hz : g.value? z with
  | none => rw [hz] at h; cases h
  | some zv =>
  rw [hz] at h
  simp only [Option.any_eq_true, Array.any_eq_true', Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨gb, hgb, v, hv, hok, w, hw, hw0⟩ := h
  obtain ⟨d⟩ := pnOK_spec hok
  refine ⟨v, zv, gb, rfl, hgb, hv, ⟨d⟩, fun d' => ?_⟩
  have := d'.hw
  rw [hw] at this; cases this
  exact Option.some.inj (d'.hp.symm.trans hw0)

/-- What `pnRel` says. -/
structure PNRel (tabs : Tables) (f g : Func) : Prop where
  cfg : DomCert.cfgView g = DomCert.cfgView f
  ownAux : g.ownAux = f.ownAux
  size : f.valueTab.size ≤ g.valueTab.size
  value : ∀ z fv, f.value? z = some fv → ∃ gv, g.value? z = some gv ∧
    (ssSame fv gv = true ∨ pnOK tabs f g z = true)
  fresh : ∀ z gv, f.value? z = none → g.value? z = some gv → pnFresh tabs f g z = true
  block : ∀ b ∈ f.blocks, ∀ fb, f.block? b = some fb → ∃ gb, g.block? b = some gb ∧
    gb.kind = fb.kind ∧ gb.controls = fb.controls ∧
    gb.values.toList.filter (fun z => (f.value? z).isSome) = fb.values.toList ∧
    (∀ z ∈ gb.values, (f.value? z).isSome = true ∨ pnFresh tabs f g z = true) ∧
    ∃ of og, Sem.schedule f fb = some of ∧ Sem.schedule g gb = some og ∧
      og.toList.filter (fun z => !pnOK tabs f g z) = of.toList

theorem pnRel_spec (h : pnRel tabs f g = true) : PNRel tabs f g := by
  unfold pnRel at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Array.all_eq_true'] at h
  obtain ⟨⟨⟨⟨hcfg, hown⟩, hsz⟩, hval⟩, hblk⟩ := h
  refine ⟨hcfg, hown, hsz, fun z fv hfv => ?_, fun z gv hz hgv => ?_, fun b hb fb hfb => ?_⟩
  · have := hval z (Nat.lt_of_lt_of_le (GoFV.Proof.lt_of_value? hfv) hsz)
    rw [hfv] at this
    cases hgv : g.value? z with
    | none => rw [hgv] at this; cases this
    | some gv =>
      rw [hgv] at this
      simp only [Bool.or_eq_true] at this
      exact ⟨gv, rfl, this⟩
  · have := hval z (GoFV.Proof.lt_of_value? hgv)
    rw [hz, hgv] at this
    exact this
  · have := hblk b hb
    rw [hfb] at this
    cases hgb : g.block? b with
    | none => rw [hgb] at this; cases this
    | some gb =>
      rw [hgb] at this
      simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', Bool.or_eq_true] at this
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := this
      refine ⟨gb, rfl, h1, h2, h3, h4, ?_⟩
      revert h5
      cases hof : Sem.schedule f fb with
      | none => intro h5; cases h5
      | some of =>
        cases hog : Sem.schedule g gb with
        | none => intro h5; cases h5
        | some og =>
          intro h5
          simp only [beq_iff_eq] at h5
          exact ⟨of, og, rfl, rfl, h5⟩

end GoFV.Proof.PhiNot
