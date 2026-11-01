import GoFV.Proof.Pass.ShortCircPres

/-!
# Checked `shortcircuitBlock`: the result's uses are dominated

`Setup.useDom_g : UseDom g` (issue #147), from `UseDom f` and the checker's local facts instead
of `wfDomCheck` of the result.

- Paths (`path_map`): an edge of `g` is an edge of `f` or the redirected edge `p → t` (`f` has
  `p → b → t`), so a path of `g` maps to a path of `f` with `b` inserted. Once a path has passed
  `b` (in `f`), it is in the plan's blocks until it leaves them through the block `M` a moved phi
  moved to (`closeOK`, `Closed`).
- A register outside `b`'s values keeps its block (`blockOf_keep`): a use `g` shares with `f`
  is dominated (`avail_map`; along the redirected edge, through `p → b`, `avail_redir`).
- A moved phi read where `f` reads it, outside `b` and the plan's blocks: every path there passed
  `b` in `f`, so it passed `M` in `g` (`moved_dom`).
- A `Phi` argument of `b` along an edge from `P` is defined on every path to `P` (`avail_dom`);
  every path to a block of `dS` passes `b` (`ds_mem`), entered from the predecessors `b` keeps.
-/

namespace GoFV.Proof.ShortCirc

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.ShortCircuit GoFV.Proof Dom

/-- Paths that passed `b` stay in the plan's blocks until they pass `M`. -/
def Closed (I : Info) (g : Func) (M : ID) : Prop :=
  M ∈ I.region ∧ I.t ∈ I.region ∧ (∀ e ∈ (g.getB I.s.b).succs, e.b ∈ I.region) ∧
    ∀ r ∈ I.region, r ≠ M → ∀ e ∈ (g.getB r).succs, e.b ∈ I.region

/-- A path to a block other than the entry comes from a predecessor. -/
theorem reach_pred {h : Func} {Y : ID} {l : List ID} (hr : Reach h Y l) (hY : Y ≠ h.entry) :
    ∃ P l0 blk e, l = Y :: l0 ∧ Reach h P l0 ∧ h.block? P = some blk ∧ e ∈ blk.succs ∧
      e.b = Y := by
  cases hr with
  | entry => exact absurd rfl hY
  | step hr hb he => exact ⟨_, _, _, _, rfl, hr, hb, he, rfl⟩

namespace Setup

variable {ce : CheckEnv} {tabs : Tables} {f g : Func} {s : Site} (S : Setup ce tabs f g s)
include S

set_option hygiene false in
local notation "𝓘" => infoOf tabs f g s
set_option hygiene false in
local notation "𝓣" => Info.factTab (infoOf tabs f g s) f g

/-- The site's edges in `f`: `p → b` (index `cidx`) and `b → t`. -/
theorem site_edges : ∃ fp Bb, f.block? s.p = some fp ∧ ⟨s.b, s.cidx⟩ ∈ fp.succs ∧
    f.block? s.b = some Bb ∧ s.te ∈ Bb.succs ∧ Bb.values = (𝓘).bvals ∧ s.b ∈ f.blocks ∧
    s.b ≠ f.entry := by
  obtain ⟨Bb, hBb, hbm, -, hvals, -, -, -, hpr, -, -, -, top, cv, chain, par, c, cc, -, -, -, -,
    -, -, -, -, -, -, hsucc, -⟩ := S.pre
  obtain ⟨-, fp, hfp, hps⟩ := S.wf.predLink s.b Bb ⟨hbm, hBb⟩ _ _ hpr
  refine ⟨fp, Bb, hfp, Array.mem_of_getElem? hps, hBb, Array.mem_of_getElem? hsucc, hvals, hbm,
    fun h => ?_⟩
  have := S.wf.entryPreds Bb (h ▸ hBb)
  have hlt := (Array.getElem?_eq_some_iff.1 hpr).1
  omega

/-- **An edge of `g`** is an edge of `f` or the redirected edge `p → t`. -/
theorem edge_class {P : ID} (hPm : P ∈ f.blocks) {gP : Block} (hgP : g.block? P = some gP)
    {e : Edge} (he : e ∈ gP.succs) :
    (∃ fP, f.block? P = some fP ∧ ∃ e' ∈ fP.succs, e'.b = e.b) ∨ (P = s.p ∧ e.b = s.te.b) := by
  obtain ⟨fP, gP', hfP, hgP', -, -, hout⟩ := S.gblock hPm
  rw [hgP] at hgP'; cases hgP'
  by_cases hK : P ∈ (𝓘).K
  · obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 he
    obtain ⟨-, hm⟩ := (SCI.wfKOK_spec _ hfP hgP (S.wfKOK hK)).2.2.1 j e hj
    rcases hm with hm | hm
    · by_cases hp : P = s.p
      · exact .inr ⟨hp, hm⟩
      · have hPg : P ∈ g.blocks := by rw [S.gblocks]; exact hPm
        rcases (blockOK_spec hPg hfP hgP (S.blockOK hK)).2.2 with ⟨-, hPb⟩ | ⟨-, -, -, -, -, -, -, hsu, -⟩
        · obtain ⟨-, Bb, -, -, hBb, hte, -⟩ := S.site_edges
          subst hPb
          simp only [infoOf_s, infoOf_t] at hm ⊢
          exact .inl ⟨Bb, hBb, s.te, hte, hm.symm⟩
        · obtain ⟨hsz, hk⟩ := SCI.succOK_spec _ hsu
          have hjl : j < fP.succs.size := hsz ▸ (Array.getElem?_eq_some_iff.1 hj).1
          rcases hk j e fP.succs[j] hj (Array.getElem?_eq_getElem hjl) with ⟨h1, -⟩ | ⟨h1, -⟩
          · exact absurd h1 hp
          · exact .inl ⟨fP, hfP, fP.succs[j], Array.getElem_mem hjl, h1.symm⟩
    · exact .inl ⟨fP, hfP, hm⟩
  · rw [hout hK] at he
    exact .inl ⟨fP, hfP, e, he, rfl⟩

/-- **A path of `g` maps to a path of `f`** with `b` inserted; once past `b` it passes `M`
before it leaves the plan's blocks (`Closed`). -/
theorem path_map {Y : ID} {l : List ID} (h : Reach g Y l) :
    ∃ l', Reach f Y l' ∧ (∀ z ∈ l', z ∈ l ∨ z = s.b) ∧
      ∀ M, Closed (𝓘) g M → s.b ∈ l' → M ∈ l ∨ Y ∈ (𝓘).region ∨ Y = s.b := by
  have hwg := S.wfg
  induction h with
  | entry =>
    refine ⟨[f.entry], by rw [S.gentry]; exact .entry, fun z hz => .inl (by rw [S.gentry]; exact hz),
      fun M _ hb => .inr (.inr ?_)⟩
    rw [List.mem_singleton] at hb; rw [S.gentry, hb]
  | @step P l blk e hr hb he ih =>
    obtain ⟨l', hr', hsub, hcl⟩ := ih
    have hPm : P ∈ f.blocks := by rw [← S.gblocks]; exact hr.mem hwg
    rcases S.edge_class hPm hb he with ⟨fP, hfP, e', he', heb⟩ | ⟨hp, ht⟩
    · refine ⟨e.b :: l', heb ▸ Reach.step hr' hfP he', fun z hz => ?_, fun M hM hbl => ?_⟩
      · rcases List.mem_cons.1 hz with rfl | hz
        · exact .inl List.mem_cons_self
        · rcases hsub z hz with h | h
          · exact .inl (List.mem_cons_of_mem _ h)
          · exact .inr h
      · rcases List.mem_cons.1 hbl with h | hbl
        · exact .inr (.inr h.symm)
        rcases hcl M hM hbl with h | h | h
        · exact .inl (List.mem_cons_of_mem _ h)
        · by_cases hPM : P = M
          · exact .inl (List.mem_cons_of_mem _ (hPM ▸ hr.mem_self))
          · exact .inr (.inl (hM.2.2.2 P h hPM e (by rw [getB_of hb]; exact he)))
        · subst h
          exact .inr (.inl (hM.2.2.1 e (by simp only [infoOf_s]; rw [getB_of hb]; exact he)))
    · obtain ⟨fp, Bb, hfp, hpb, hBb, hte, -⟩ := S.site_edges
      subst hp
      have hrb : Reach f s.b (s.b :: l') := Reach.step hr' hfp hpb
      have hrt : Reach f s.te.b (s.te.b :: s.b :: l') := Reach.step hrb hBb hte
      refine ⟨e.b :: s.b :: l', ht ▸ hrt, fun z hz => ?_, fun M hM _ => .inr (.inl ?_)⟩
      · rcases List.mem_cons.1 hz with rfl | hz
        · exact .inl List.mem_cons_self
        rcases List.mem_cons.1 hz with rfl | hz
        · exact .inr rfl
        rcases hsub z hz with h | h
        · exact .inl (List.mem_cons_of_mem _ h)
        · exact .inr h
      · rw [ht]; exact hM.2.1

/-- A register outside `b`'s values defined on every path of `f` to `Q` is defined on every path
of `g` to `Q`. -/
theorem avail_map {Q a : ID} (hl : Listed f a) (hab : a ∉ (𝓘).bvals)
    (hf : ∀ l', Reach f Q l' → DomCert.blockOf f a ∈ l') :
    ∀ l, Reach g Q l → DomCert.blockOf g a ∈ l := by
  intro l hr
  obtain ⟨l', hr', hsub, -⟩ := S.path_map hr
  rw [S.blockOf_keep hl hab]
  rcases hsub _ (hf l' hr') with h | h
  · exact h
  · exfalso; apply hab
    obtain ⟨v, B, -, -, hB, ha, -⟩ := blockOf_listed S.wf hl
    obtain ⟨-, Bb, -, -, hBb, -, hvals, -⟩ := S.site_edges
    rw [h, hBb] at hB; cases hB
    rw [← hvals]; exact ha

/-- Along the redirected edge: defined on every path of `f` to `b`, so on every path of `g` to
`p`. -/
theorem avail_redir {a : ID} (hl : Listed f a) (hab : a ∉ (𝓘).bvals)
    (hf : ∀ l', Reach f s.b l' → DomCert.blockOf f a ∈ l') :
    ∀ l, Reach g s.p l → DomCert.blockOf g a ∈ l := by
  obtain ⟨fp, Bb, hfp, hpb, hBb, -, hvals, -⟩ := S.site_edges
  have hne : DomCert.blockOf f a ≠ s.b := fun h => by
    apply hab
    obtain ⟨v, B, -, -, hB, ha, -⟩ := blockOf_listed S.wf hl
    rw [h, hBb] at hB; cases hB
    rw [← hvals]; exact ha
  refine S.avail_map hl hab fun l' hr' => ?_
  have := hf _ (Reach.step hr' hfp hpb)
  rcases List.mem_cons.1 this with h | h
  · exact absurd h hne
  · exact h

/-- `Closed` for the block a moved phi moved to (`closeOK`). -/
theorem closed_of {v : ID} (hv : v ∈ (𝓘).vs) (hd : (𝓘).look (𝓘).dflt v = some v) :
    Closed (𝓘) g (g.getV v).block := by
  obtain ⟨h1, h2, -, h4, h5⟩ := SCI.closeOK_spec _ S.closeOK hv hd
  exact ⟨h1, h2, h4, h5⟩

/-- A moved phi read at `Q` where `f` reads it: every path of `g` to `Q` passes its block, or
`Q` is `b` or a plan block other than that one. -/
theorem moved_dom {v Q : ID} (hv : v ∈ (𝓘).vs) (hd : (𝓘).look (𝓘).dflt v = some v)
    (hf : ∀ l', Reach f Q l' → DomCert.blockOf f v ∈ l') {l : List ID} (hr : Reach g Q l) :
    DomCert.blockOf g v ∈ l ∨ (Q ∈ (𝓘).region ∧ Q ≠ (g.getV v).block) ∨ Q = s.b := by
  obtain ⟨l', hr', -, hcl⟩ := S.path_map hr
  obtain ⟨-, hl⟩ := dflt_spec hd
  obtain ⟨gv, -, hgv, -⟩ := listedIn_spec hl
  have hfb : DomCert.blockOf f v = s.b := by
    obtain ⟨-, Bb, -, -, hBb, -, hvals, hbm, -⟩ := S.site_edges
    obtain ⟨fv, hfv, -, hb⟩ := S.wf.valueId s.b Bb ⟨hbm, hBb⟩ v (hvals ▸ (S.vs_mem hv).1)
    rw [blockOf_of hfv, hb]
  have := hcl _ (S.closed_of hv hd) (hfb ▸ hf l' hr')
  rw [blockOf_of hgv]
  rw [getV_of hgv] at this ⊢
  rcases this with h | h | h
  · exact .inl h
  · by_cases hQ : Q = gv.block
    · exact .inl (hQ ▸ hr.mem_self)
    · exact .inr (.inl ⟨h, hQ⟩)
  · exact .inr (.inr h)

/-- A `Phi` argument of `b` (in `f`) along an edge from `P`: defined on every path to `P`. -/
theorem avail_dom {P w : ID} (h : (𝓘).availAt f P w = true) :
    ∀ l, Reach g P l → DomCert.blockOf g w ∈ l := by
  obtain ⟨hw, z, hz, hp, j, e, he, heb, ha⟩ := SCI.availAt_spec _ h
  obtain ⟨-, Bb, -, -, hBb, -, hvals, hbm, -⟩ := S.site_edges
  obtain ⟨fz, hfz, hop⟩ := isPhiIn_iff.1 hp
  rw [getV_of hfz] at ha
  simp only [infoOf_s] at he
  rw [getB_of hBb] at he
  have hzB : z ∈ Bb.values := hvals ▸ hz
  refine S.avail_map (argListed_of S.wf hbm hBb hzB hfz (args_get_mem ha)) hw fun l' hr' => ?_
  exact (S.dom s.b Bb hbm hBb).2.2 z hzB fz hfz hop j w e l' ha he (heb ▸ hr')

/-- Every path of `g` to a block of `dS` passes `b`. -/
theorem ds_mem : ∀ {Y : ID} {l : List ID}, Reach g Y l → Y ∈ (𝓘).dS → s.b ∈ l := by
  have hds := SCI.dsOK_spec _ S.dsOK
  have hwg := S.wfg
  intro Y l h
  induction h with
  | entry =>
    intro hY
    rcases hds _ hY with h | ⟨h, -⟩
    · rw [h]; exact List.mem_singleton_self _
    · exact absurd rfl h
  | @step P l blk e hr hb he ih =>
    intro hY
    rcases hds _ hY with h | ⟨-, hpr⟩
    · rw [h]; exact List.mem_cons_self
    · obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 he
      obtain ⟨-, C, hC, hCp⟩ := hwg.succLink P blk ⟨hr.mem hwg, hb⟩ j e hj
      have := hpr ⟨P, j⟩ (by rw [getB_of hC]; exact Array.mem_of_getElem? hCp)
      exact List.mem_cons_of_mem _ (ih this)

/-- **A use passing `useOK`** at `Q` is dominated, given the source's facts at the same place. -/
theorem useOK_dom {Q w : ID} {a? : Option ID} {rd : Bool} (h : (𝓘).useOK f g Q w a? rd = true)
    (hsrc : ∀ a, a? = some a → Listed f a ∧
      ((rd = true ∧ Q = s.p ∧ ∀ l', Reach f s.b l' → DomCert.blockOf f a ∈ l') ∨
        (rd = false ∧ ∀ l', Reach f Q l' → DomCert.blockOf f a ∈ l'))) :
    ∀ l, Reach g Q l → DomCert.blockOf g w ∈ l := by
  intro l hr
  have hR2 : ∀ (ha : a? = some w), w ∉ (𝓘).bvals → DomCert.blockOf g w ∈ l := fun ha hb => by
    obtain ⟨hl, hs⟩ := hsrc w ha
    rcases hs with ⟨-, hQ, hf⟩ | ⟨-, hf⟩
    · subst hQ; exact S.avail_redir hl hb hf l hr
    · exact S.avail_map hl hb hf l hr
  rcases SCI.useOK_spec _ h with ⟨ha, hb⟩ | ⟨-, h⟩
  · exact hR2 ha hb
  rcases h with h | ⟨ha, hrd, hfree, hQb, hQr⟩ | h | ⟨hQ, hne, h⟩
  · rw [h]; exact hr.mem_self
  · rcases freeArg_spec hfree with hb | ⟨hvs, hd⟩
    · exact hR2 ha hb
    · obtain ⟨-, hs⟩ := hsrc w ha
      rcases hs with ⟨h1, -⟩ | ⟨-, hf⟩
      · rw [hrd] at h1; cases h1
      rcases S.moved_dom hvs hd hf hr with h | h | h
      · exact h
      · exact absurd h.1 hQr
      · exact absurd h hQb
  · exact S.avail_dom h l hr
  · simp only [infoOf_s] at h
    obtain ⟨pre, t, rfl, ht⟩ := hr.suffix (S.ds_mem hr hQ)
    refine List.mem_append_right _ ?_
    obtain ⟨-, -, -, -, -, -, -, hbe⟩ := S.site_edges
    obtain ⟨P, t', blk, e, rfl, hr', hb, he, heb⟩ := reach_pred ht (by rw [S.gentry]; exact hbe.2)
    obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 he
    have hwg := S.wfg
    obtain ⟨-, C, hC, hCp⟩ := hwg.succLink P blk ⟨hr'.mem hwg, hb⟩ j e hj
    have hav := h ⟨P, j⟩ (by rw [← heb, getB_of hC]; exact Array.mem_of_getElem? hCp)
    exact List.mem_cons_of_mem _ (S.avail_dom hav t' hr')

/-- **The result's uses are dominated** on paths, without a check of the whole result. -/
theorem useDom_g : UseDom g := by
  have hwg := S.wfg
  intro Y gY hYg hgY
  have hYm : Y ∈ f.blocks := by rw [← S.gblocks]; exact hYg
  obtain ⟨fY, gY', hfY, hgY', -, -, hout⟩ := S.gblock hYm
  rw [hgY] at hgY'; cases hgY'
  obtain ⟨hu1, hu2, hu3⟩ := S.dom Y fY hYm hfY
  by_cases hK : Y ∈ (𝓘).K
  · have hd := SCI.domKOK_spec _ (S.domKOK hK)
    rw [getB_of hgY, getB_of hfY] at hd
    refine ⟨fun l hl vid hvid v hv hnp a ha => ?_, fun l hl c hc => ?_,
      fun vid hvid v hv hp i a e l ha he hl => ?_⟩
    · obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 ha
      obtain ⟨a?, hu, hsrc⟩ := hd.2.1 vid hvid (by rw [getV_of hv]; exact hnp) k a
        (by rw [getV_of hv]; exact hk)
      refine S.useOK_dom hu (fun a' h' => ?_) l hl
      obtain ⟨hxf, fv, hfv, hfp, hr⟩ := hsrc a' h'
      exact ⟨argListed_of S.wf hYm hfY hxf hfv (args_get_mem hr),
        .inr ⟨rfl, fun l' hr' => hu1 l' hr' vid hxf fv hfv hfp a' (args_get_mem hr)⟩⟩
    · obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 hc
      refine S.useOK_dom (hd.2.2 k c hk) (fun a' h' => ?_) l hl
      have hm := Array.mem_of_getElem? h'
      exact ⟨S.wf.ctrlListed Y fY ⟨hYm, hfY⟩ a' hm, .inr ⟨rfl, fun l' hr' => hu2 l' hr' a' hm⟩⟩
    · obtain ⟨a?, hu, hsrc⟩ := hd.1 vid hvid (by rw [getV_of hv]; exact hp) i e a he
        (by rw [getV_of hv]; exact ha)
      refine S.useOK_dom hu (fun a' h' => ?_) l hl
      obtain ⟨hxf, fv, hfv, hfp, hr⟩ := hsrc a' h'
      rcases hr with ⟨hrd, hpb, hr⟩ | ⟨hrd, hpe, hr⟩
      · obtain ⟨hYt, hiT⟩ := (SCI.redir_iff _).1 hrd
        obtain ⟨-, hrt⟩ := S.redir_spec
        have hYt' : Y = s.te.b := hYt
        rw [← hYt', getB_of hgY, ← hiT, he] at hrt
        cases hrt
        simp only [infoOf_s] at hpb hr
        cases hp0 : fY.preds[s.te.i]? with
        | none => rw [hp0] at hpb; cases hpb
        | some e0 =>
          rw [hp0] at hpb
          have he0 : e0.b = s.b := by simpa using hpb
          refine ⟨argListed_of S.wf hYm hfY hxf hfv (args_get_mem hr), .inl ⟨hrd, rfl, fun l' hr' => ?_⟩⟩
          exact hu3 vid hxf fv hfv hfp _ a' e0 l' hr hp0 (he0 ▸ hr')
      · exact ⟨argListed_of S.wf hYm hfY hxf hfv (args_get_mem hr),
          .inr ⟨hrd, fun l' hr' => hu3 vid hxf fv hfv hfp _ a' e l' hr hpe hr'⟩⟩
  · have hgf := hout hK
    subst hgf
    have hYr : Y ∉ (𝓘).region := fun h => hK (S.region_spec h).2.2.1
    have hYb : Y ≠ s.b := fun h => hK (h ▸ S.bK)
    obtain ⟨hsc, hsv⟩ := S.scan_spec hYg hK
    rw [getB_of hgY] at hsc hsv
    have hmoved : ∀ {Q a : ID} {l : List ID}, Reach g Q l → (𝓘).freeArg a = true →
        Listed f a → (∀ l', Reach f Q l' → DomCert.blockOf f a ∈ l') →
        DomCert.blockOf g a ∈ l ∨ ∃ M, Closed (𝓘) g M ∧ ((Q ∈ (𝓘).region ∧ Q ≠ M) ∨ Q = s.b) := by
      intro Q a l hr hfree hla hf
      rcases freeArg_spec hfree with hb | ⟨hvs, hd⟩
      · exact .inl (S.avail_map hla hb hf l hr)
      · rcases S.moved_dom hvs hd hf hr with h | h | h
        · exact .inl h
        · exact .inr ⟨_, S.closed_of hvs hd, .inl h⟩
        · exact .inr ⟨_, S.closed_of hvs hd, .inr h⟩
    refine ⟨fun l hl vid hvid v hv hnp a ha => ?_, fun l hl c hc => ?_,
      fun vid hvid v hv hp i a e l ha he hl => ?_⟩
    · obtain ⟨fx, gx, hfx, hgx, -, -, -, -, hop, -, -, -, hargs⟩ := S.gval_out hYm hK hfY hvid
      rw [hv] at hgx; cases hgx
      have ha' : a ∈ fx.args := hargs ▸ ha
      rcases hmoved hl (hsv vid hvid a (by rw [getV_of hv]; exact ha))
        (argListed_of S.wf hYm hfY hvid hfx ha')
        (fun l' hr' => hu1 l' hr' vid hvid fx hfx (hop ▸ hnp) a ha') with h | ⟨M, -, h | h⟩
      · exact h
      · exact absurd h.1 hYr
      · exact absurd h hYb
    · rcases hmoved hl (hsc c hc) (S.wf.ctrlListed Y gY ⟨hYm, hfY⟩ c hc)
        (fun l' hr' => hu2 l' hr' c hc) with h | ⟨M, -, h | h⟩
      · exact h
      · exact absurd h.1 hYr
      · exact absurd h hYb
    · obtain ⟨fx, gx, hfx, hgx, -, -, -, -, hop, -, -, -, hargs⟩ := S.gval_out hYm hK hfY hvid
      rw [hv] at hgx; cases hgx
      have ha' : fx.args[i]? = some a := hargs ▸ ha
      obtain ⟨-, P, hP, hPs⟩ := hwg.predLink Y gY ⟨hYg, hgY⟩ i e he
      have hYs : ∀ r, r = e.b → ⟨Y, i⟩ ∈ (g.getB r).succs := fun r hr => by
        rw [hr, getB_of hP]; exact Array.mem_of_getElem? hPs
      rcases hmoved hl (hsv vid hvid a (by rw [getV_of hv]; exact args_get_mem ha))
        (argListed_of S.wf hYm hfY hvid hfx (args_get_mem ha'))
        (fun l' hr' => hu3 vid hvid fx hfx (hop ▸ hp) i a e l' ha' he hr') with h | ⟨M, hM, h | h⟩
      · exact h
      · exact absurd (hM.2.2.2 e.b h.1 h.2 ⟨Y, i⟩ (hYs _ rfl)) hYr
      · exact absurd (hM.2.2.1 ⟨Y, i⟩ (hYs _ h.symm)) hYr

end Setup

end GoFV.Proof.ShortCirc
