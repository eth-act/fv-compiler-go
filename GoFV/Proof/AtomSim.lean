import GoFV.Proof.AtomSimPanic

/-!
# The atom simulation (issue #113)

`atomSimInv_refines`: two checked functions with the same blocks and atoms
(`RewriteCheck.atomsOK`), whose atoms' arguments in `g` refine those of `f` as terms over the
atoms and whose terminators refine as functions of their controls' terms (same edge, possibly
another kind, controls or successor order, issue #151), for source valuations satisfying a
source-side invariant `I` (`AtomArgsRefP`, `StepRefsP`), refine each other under monotone
contracts: lock-step simulation (`runLoop_simE`) with the relation `BRel` at block entries
(`block_sim`: a block entry that does not panic, `enter_ok`, then the terminators,
`termStepRef_regs`; a panicking one, `enter_panic`; the invariant carried along by
`Inv.edge`), entry frames equal but their registers (`entry_rel`), and `finish_refines`.
`atomSim_refines`: the trivial invariant, `Term.TermStepRef`. `atomSimX_refines` (issue #35):
the generalised atom relation (`AtomsX`, `AtomArgsRefX`: a `Store` may change into another
`Store` whose write refines the source's, and a root of `f` that is no root of `g` is a `Store`).
`atomSimXE_refines` (issue #69): under contracts and from entry memories the invariant's
predicate `I.E` holds of (e.g. malloc contracts returning zeroed blocks, `Env.AllocZero`, and
read-only symbols holding their bytes); a block step keeps the initial memory (`blockStep_mem0`).
-/

namespace GoFV.Proof.AtomSim

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Proof.Dom GoFV.Opt GoFV.Opt.RewriteCheck GoFV.Proof.Term

/-- The simulation relation: the same block and edge, `BRel`. -/
def SimR (tabs : Tables) (f g : Func) (I : SrcInv tabs f) (frS : Frame) (bS : ID) (iS : Nat)
    (frT : Frame) (bT : ID) (iT : Nat) : Prop :=
  bT = bS ∧ iT = iS ∧ BRel tabs f g I frS frT bS iS

section
variable {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} {I : SrcInv tabs f} (H : Hyp tabs f g ce ce' I)
  {b : ID} {fb gb : Block} {of og : Array ID} (B : BlockData f g b fb gb of og)
include H B

theorem vt_placed : ∀ x, (V1 g b gb x ∨ x ∈ og.toList) → ∃ w, Placed g x w := fun x hx =>
  hx.elim (v1_placed H.wg B.bmT B.hgb x) fun hm => by
    obtain ⟨hxb, w, hw, -⟩ := (B.mT x).1 hm
    exact ⟨w, (placed_in H.wg B.bmT B.hgb hxb hw).1⟩

/-- **The terminators** (`StepRefsP`). -/
theorem term_sim {frS frT : Frame} {i : Nat} (R : BRel tabs f g I frS frT b i) {FS FT : Frame}
    (E : EndRel tabs f g I b fb gb of og FS FT) :
    Res.Rel Next.Refines (stepTerm FS fb) (stepTerm FT gb) :=
  termStepRef_regs H E.dS E.mS E.dT (vt_placed H B) E.rel E.tyS E.tyT E.inv E.qinv
    (fun a h => .inl (.inl h)) (H.ctrls b B.bmT fb gb B.hfb B.hgb).2
    (fun _ hc => (ctrl_in H.wf H.cf B.bmS B.hfb R.treeS B.mS hc).1)
    (fun _ hc => (ctrl_in H.wg H.cg B.bmT B.hgb R.treeT B.mT hc).1)

/-- Values placed in an ancestor of `b` are in `b`'s sets. -/
theorem ancV_sets : ∀ x, AncV f b x → V1 f b fb x ∨ x ∈ of.toList := fun x ⟨v, hp, hanc⟩ => by
  by_cases hvb : v.block = b
  · obtain ⟨hv, -, blk, hblk, hx⟩ := hp
    rw [hvb, B.hfb] at hblk; cases hblk
    by_cases hph : v.op = .Phi
    · exact .inl (.inr ⟨hx, v, hv, hph⟩)
    · exact .inr ((B.mS x).2 ⟨hx, v, hv, hph⟩)
  · exact .inl (.inl ⟨v, hp, hanc, hvb⟩)

/-- The relation at a successor. -/
theorem next_rel {frS frT : Frame} {i : Nat} (R : BRel tabs f g I frS frT b i) {FS FT : Frame}
    (E : EndRel tabs f g I b fb gb of og FS FT) {e : Edge} (hS : stepTerm FS fb = .ok (.goto e)) :
    BRel tabs f g I FS FT e.b e.i := by
  have he := stepTerm_goto_mem hS
  obtain ⟨n1, n2, n3, n4⟩ := next_sets H.wf H.cf B.bmS B.hfb R.treeS B.mS he
  obtain ⟨m1, m2, m3, -⟩ := next_sets H.wg H.cg B.bmT B.hgb R.treeT B.mT
    ((H.ctrls b B.bmT fb gb B.hfb B.hgb).1 e he)
  obtain ⟨l, p, ph, q⟩ := I.edge b i fb FS e _ B.hfb R.live E.inv E.qinv E.tyS E.szS E.dS
    (ancV_sets H B) n2 hS
  obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 he
  exact { fr := E.fr, szS := E.szS, szT := E.szT, tyS := E.tyS, tyT := E.tyT, mem := n4,
          treeS := n3, treeT := m3, atoms := E.atoms,
          den := ⟨_, _, E.dS, E.dT, vt_placed H B, n1, m1, n2, m2, E.mS⟩, live := l, inv := p,
          phis := ph,
          qinv := q,
          pre := .inr ⟨b, fb, k, _, B.bmS, B.hfb, hk, E.inv, E.qinv, E.dS, ancV_sets H B, n2,
            E.mS⟩ }

end

/-- Evaluating values keeps the initial memory and the arguments' images. -/
theorem evalAll_mem0 {env : Env} {ctx : Ctx} :
    ∀ {L : List ID} {fr G : Frame}, evalAll env ctx fr L = .ok G →
      (G.mem0, G.images) = (fr.mem0, fr.images)
  | [], _, _, h => by cases h; rfl
  | x :: L, fr, G, h => by
    unfold evalAll at h
    split at h
    · cases h
    · split at h
      · exact (evalAll_mem0 h).trans rfl
      · cases h
      · cases h

/-- A block step along an edge keeps the initial memory and the arguments' images. -/
theorem blockStep_mem0 {env : Env} {ctx : Ctx} {fr G : Frame} {b : ID} {i : Nat} {e : Edge}
    (h : blockStep env ctx fr b i = .goto G e) : (G.mem0, G.images) = (fr.mem0, fr.images) := by
  unfold blockStep at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
    · rename_i G' hG
      split at h
      · cases h
        obtain ⟨ps, o, -, -, hev⟩ := enterBlock_ok_split hG
        exact (evalAll_mem0 hev).trans rfl
      all_goals cases h

/-- **One block entry.** -/
theorem block_sim {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} {I : SrcInv tabs f} (H : Hyp tabs f g ce ce' I)
    {env : Env} (hE : env.Mono) {frS frT : Frame} (hEI : I.E env frS.mem0 frS.images) {b : ID} {i : Nat}
    (R : BRel tabs f g I frS frT b i) :
    StepSimE Mem.Refines (SimR tabs f g I) (blockStep env (Ctx.make tabs f) frS b i)
      (blockStep env (Ctx.make tabs g) frT b i) := by
  unfold blockStep
  cases hfb : (Ctx.make tabs f).f.block? b with
  | none => trivial
  | some fb =>
    obtain ⟨gb, of, og, B⟩ := blockData H R.mem hfb
    rw [show (Ctx.make tabs g).f.block? b = some gb from B.hgb]
    dsimp only
    cases he : enterBlock env (Ctx.make tabs f) frS fb i with
    | ok FS =>
      obtain ⟨FT, heT, E⟩ := enter_ok H hE hEI R B he
      rw [heT]
      dsimp only
      have hst := term_sim H B R E
      generalize hS : stepTerm FS fb = sS at hst ⊢
      generalize stepTerm FT gb = sT at hst ⊢
      cases hst with
      | ok hn =>
        cases hn with
        | goto e => exact ⟨FT, e, rfl, rfl, rfl, next_rel H B R E hS⟩
        | ret hl hm => exact ⟨_, _, rfl, hl, hm⟩
      | panic e hm => exact ⟨_, rfl, hm⟩
      | stuck msg r => trivial
    | panic e m =>
      obtain ⟨m', heT, hm⟩ := enter_panic H hE hEI R B he
      rw [heT]
      exact ⟨m', rfl, hm⟩
    | stuck msg => trivial

/-- The entry frames are related. -/
theorem entry_rel {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} {I : SrcInv tabs f} (H : Hyp tabs f g ce ce' I)
    (env : Env) (args : List Val) (mem : Mem) :
    BRel tabs f g I (entryFrame env (Ctx.make tabs f) args mem)
      (entryFrame env (Ctx.make tabs g) args mem) f.entry 0 := by
  have hT : entryFrame env (Ctx.make tabs g) args mem =
      { entryFrame env (Ctx.make tabs f) args mem with
        regs := Array.replicate g.valueTab.size none } := entryFrame_eq H.ok.ownAux args mem
  have hnone : ∀ (a : ID) (y' : Val), (entryFrame env (Ctx.make tabs g) args mem).regs[a]? ≠ some (some y') :=
    fun a y' h => by
      rw [hT] at h
      simp only [Array.getElem?_replicate] at h
      split at h <;> cases h
  have hentry : ∀ (h : Func) (c : CheckEnv), WF c h → CertOK h → ∀ x, ¬ SAnc h h.entry x :=
    fun h c _ hc x ⟨v, _, hanc, hne⟩ => hne (anc_of_entry hc.parents hanc)
  have hphi : ∀ (h : Func) (c : CheckEnv), WF c h → ∀ V, PhiArgs h h.entry 0 V :=
    fun h c hwf V hb hbb z hz v hv hph a ha => by
      have h1 := hwf.phiArity _ _ _ _ ⟨⟨hwf.entry, hbb⟩, hz, hv⟩ hph
      rw [hwf.entryPreds hb hbb] at h1
      have := (Array.getElem?_eq_some_iff.1 ha).1
      omega
  have hge : g.entry = f.entry := H.ok.entry.symm
  have hpois : ∀ a, rv (entryFrame env (Ctx.make tabs f) args mem) a = .poison := fun a => by
    simp [rv, entryFrame, Array.getElem?_replicate]
    split <;> rfl
  -- the entry block reads no `Phi` arguments, so its `Phi`s leave the registers poison
  have hq : PhisQ tabs f I.Q (entryFrame env (Ctx.make tabs f) args mem) f.entry 0 :=
    fun bb ps hbb hps => by
      obtain ⟨p1, p2, p3, p4⟩ := phis_spec (H.wf.valuesNodup _ _ ⟨H.wf.entry, hbb⟩) hps
      have h : rv { entryFrame env (Ctx.make tabs f) args mem with
          regs := setPhis ps (entryFrame env (Ctx.make tabs f) args mem).regs } =
          fun _ => .poison := funext fun z => by
        by_cases hlt : z < (entryFrame env (Ctx.make tabs f) args mem).regs.size
        · by_cases hk : z ∉ bb.values ∨ ∃ v, f.value? z = some v ∧ v.op ≠ .Phi
          · rw [← hpois z]; unfold rv
            exact congrArg (fun o => (Option.join o).getD .poison) (p3 z hk)
          · simp only [not_or, Decidable.not_not, not_exists, not_and] at hk
            obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (p2 z hk.1)
            obtain ⟨a, -, ha, -⟩ := p4 z hk.1 v hv (hk.2 v hv) hlt
            exact (hphi f ce H.wf (fun _ => False) bb hbb z hk.1 v hv (hk.2 v hv) a ha).elim
        · unfold rv
          rw [Array.getElem?_eq_none (show (setPhis ps _).size ≤ z by
            rw [p1]; exact Nat.le_of_not_lt hlt)]; rfl
      rw [h]; exact I.qstart
  exact
    { fr := by rw [hT], szS := by simp [entryFrame]; rfl, szT := by rw [hT]; simp,
      tyS := typed_replicate _ _ _ rfl, tyT := by rw [hT]; exact typed_replicate _ _ _ rfl,
      mem := H.wf.entry, treeS := by simp [entry_depth H.cf.parents],
      treeT := by rw [← hge]; simp [entry_depth H.cg.parents],
      atoms := fun a w _ _ y' h => absurd h (hnone a y'),
      den := ⟨fun _ => False, fun _ => False, denOK_empty _ _ _, denOK_empty _ _ _,
        fun _ h => h.elim, fun x h => hentry f ce H.wf H.cf x h,
        fun x h => hentry g ce' H.wg H.cg x (hge ▸ h), hphi f ce H.wf _, hge ▸ hphi g ce' H.wg _,
        memDefs_empty _ _ _⟩,
      live := I.start.1, inv := fun a => by rw [hpois a]; exact I.start.2 a,
      phis := fun bb hbb z hz v hv hph a ha => (hphi f ce H.wf (fun _ => False) bb hbb z hz v hv hph
        a ha).elim,
      qinv := hq,
      pre := .inl (hphi f ce H.wf _) }

/-- **The atom simulation**, generalised (issue #35): changed and dropped stores, under
contracts and from entry memories the invariant's predicate holds of (issue #69). -/
theorem atomSimXE_refines {tabs : Tables} {f g : Func} {ce ce' : CheckEnv}
    (hf : check ce f = .ok ()) (hg : check ce' g = .ok ())
    (hA : AtomsX f g) (I : SrcInv tabs f)
    (h1 : AtomArgsRefX I g) (h2 : StepRefsP I g) :
    RefinesFrom (fun env args mem =>
      env.Mono ∧ I.E env (entryFrame env (Ctx.make tabs f) args mem).mem0
        (entryFrame env (Ctx.make tabs f) args mem).images) tabs g tabs f := by
  have H : Hyp tabs f g ce ce' I := ⟨check_wf hf, check_wf hg, certOK_of_check (check_domCert hf),
    certOK_of_check (check_domCert hg), hA, h1, h2⟩
  intro env args mem ⟨hE, hEI⟩ fuel hd
  refine ⟨fuel, ?_⟩
  have hc := ctx_eq (tabs := tabs) H.ok.ownAux
  have hpar : (Ctx.make tabs g).params = (Ctx.make tabs f).params := by rw [hc]
  have houts : (Ctx.make tabs g).outs = (Ctx.make tabs f).outs := by rw [hc]
  have hact : (Ctx.make tabs g).act = (Ctx.make tabs f).act := by rw [hc]
  change (runCtx env (Ctx.make tabs f) args mem fuel).Defined at hd
  change OutcomeRefines 0 (runCtx env (Ctx.make tabs f) args mem fuel)
    (runCtx env (Ctx.make tabs g) args mem fuel)
  unfold runCtx at hd ⊢
  rw [hpar, houts, hact]
  split
  · next hn => simp only [hn] at hd; exact hd.elim
  · next hn =>
    simp only [hn] at hd
    refine finish_refines_mono hE hd (runLoop_simE (fun frS bS iS frT bT iT =>
      SimR tabs f g I frS bS iS frT bT iT ∧
        (frS.mem0, frS.images) = ((entryFrame env (Ctx.make tabs f) args mem).mem0,
          (entryFrame env (Ctx.make tabs f) args mem).images))
      (fun frS bS iS frT bT iT hR => ?_) fuel
      _ _ _ _ _ _ ⟨⟨H.ok.entry.symm, rfl, entry_rel H env args mem⟩, rfl⟩ (finish_defined hd))
    obtain ⟨⟨rfl, rfl, R⟩, hm⟩ := hR
    have hs := block_sim H hE (by simp only [Prod.mk.injEq] at hm; rw [hm.1, hm.2]; exact hEI) R
    generalize hS : blockStep env (Ctx.make tabs f) frS bT iT = sS at hs ⊢
    cases sS with
    | goto G e =>
      obtain ⟨frT', e', h1, h2⟩ := hs
      exact ⟨frT', e', h1, h2, (blockStep_mem0 hS).trans hm⟩
    | ret rs m => exact hs
    | panic e m => exact hs
    | stuck => exact hs

/-- **The atom simulation**, generalised (issue #35): changed and dropped stores, for an
invariant whose predicate always holds. -/
theorem atomSimX_refines {tabs : Tables} {f g : Func} {ce ce' : CheckEnv}
    (hf : check ce f = .ok ()) (hg : check ce' g = .ok ())
    (hA : AtomsX f g) (I : SrcInv tabs f)
    (h1 : AtomArgsRefX I g) (h2 : StepRefsP I g) (hI : ∀ env m im, I.E env m im := by intros; trivial) :
    RefinesUnder Env.Mono tabs g tabs f :=
  fun env hE args mem => atomSimXE_refines hf hg hA I h1 h2 env args mem ⟨hE, hI _ _ _⟩

/-- **The atom simulation** under a source-side invariant. -/
theorem atomSimInv_refines {tabs : Tables} {f g : Func} {ce ce' : CheckEnv}
    (hf : check ce f = .ok ()) (hg : check ce' g = .ok ())
    (hA : RewriteCheck.atomsOK f g = true) (I : SrcInv tabs f)
    (h1 : AtomArgsRefP I g) (h2 : StepRefsP I g) (hI : ∀ env m im, I.E env m im := by intros; trivial) :
    RefinesUnder Env.Mono tabs g tabs f :=
  atomSimX_refines hf hg (atomsOK_spec hA).toX I h1.toX h2 hI

/-- **The atom simulation.** -/
theorem atomSim_refines {tabs : Tables} {f g : Func} {ce ce' : CheckEnv}
    (hf : check ce f = .ok ()) (hg : check ce' g = .ok ())
    (hA : RewriteCheck.atomsOK f g = true)
    (_hcf : RewriteCheck.closedOK f = true) (_hcg : RewriteCheck.closedOK g = true)
    (h1 : Term.AtomArgsRef tabs f g) (h2 : Term.TermStepRef tabs f g) :
    RefinesUnder Env.Mono tabs g tabs f :=
  atomSimInv_refines hf hg hA (SrcInv.triv tabs f) (AtomArgsRef.toP h1 _)
    (TermStepRef.toStepRefsP h2 _)

end GoFV.Proof.AtomSim
