import GoFV.Proof.AtomSimPanic

/-!
# The atom simulation (issue #113)

`atomSimInv_refines`: two checked functions with the same blocks, terminators and atoms
(`RewriteCheck.atomsOK`), whose atoms' arguments and controls in `g` refine those of `f` as
terms over the atoms for source valuations satisfying a source-side invariant `I`
(`AtomArgsRefP`, `ControlsRefP`), refine each other under monotone contracts: lock-step
simulation (`runLoop_simE`) with the relation `BRel` at block entries (`block_sim`: a block
entry that does not panic, `enter_ok`, then refined controls, `stepTerm_mono2`; a panicking
one, `enter_panic`; the invariant carried along by `Inv.edge`), entry frames equal but their
registers (`entry_rel`), and `finish_refines`. `atomSim_refines`: the trivial invariant.
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

/-- **The terminators** on refined controls. -/
theorem term_sim {frS frT : Frame} {i : Nat} (R : BRel tabs f g I frS frT b i) {FS FT : Frame}
    (E : EndRel tabs f g I b fb gb of og FS FT) :
    Res.Rel Next.Refines (stepTerm FS fb) (stepTerm FT gb) := by
  refine stepTerm_mono2 B.ba.kind.symm B.ba.succs.symm B.ba.id.symm fun k => ?_
  unfold Sem.control
  cases hk : fb.controls[k]? with
  | none => exact .stuck _ _
  | some c =>
    have hkl : k < fb.controls.size := (Array.getElem?_eq_some_iff.1 hk).1
    have hkl' : k < gb.controls.size := B.ba.csize ▸ hkl
    have hk' : gb.controls[k]? = some gb.controls[k] := by simp [hkl']
    rw [hk']
    have hc := (ctrl_in H.wf H.cf B.bmS B.hfb R.treeS B.mS (Array.mem_of_getElem? hk)).1
    have hc' := (ctrl_in H.wg H.cg B.bmT B.hgb R.treeT B.mT (Array.getElem_mem hkl')).1
    obtain ⟨-, hTR⟩ := H.ctrls b B.bmT fb gb B.hfb B.hgb
    have hT := hTR k hkl'
    rw [getElem!_pos fb.controls k hkl, getElem!_pos gb.controls k hkl',
      (Array.getElem?_eq_some_iff.1 hk).2] at hT
    have hr := termRef_regs H E.dS E.dT (vt_placed H B) E.rel E.tyS E.tyT E.inv
      (fun a h => .inl (.inl h)) hT hc hc'
    dsimp only
    rw [reg_rv (E.dS c hc).1, reg_rv (E.dT _ hc').1]
    exact .ok hr

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
    (by rw [← B.ba.succs]; exact he)
  obtain ⟨l, p, ph⟩ := I.edge b i fb FS e _ B.hfb R.live E.inv E.dS (ancV_sets H B) n2 hS
  exact { fr := E.fr, szS := E.szS, szT := E.szT, tyS := E.tyS, tyT := E.tyT, mem := n4,
          treeS := n3, treeT := m3, atoms := E.atoms,
          den := ⟨_, _, E.dS, E.dT, vt_placed H B, n1, m1, n2, m2⟩, live := l, inv := p, phis := ph }

end

/-- **One block entry.** -/
theorem block_sim {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} {I : SrcInv tabs f} (H : Hyp tabs f g ce ce' I)
    {env : Env} (hE : env.Mono) {frS frT : Frame} {b : ID} {i : Nat}
    (R : BRel tabs f g I frS frT b i) :
    StepSimE (SimR tabs f g I) (blockStep env (Ctx.make tabs f) frS b i)
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
      obtain ⟨FT, heT, E⟩ := enter_ok H hE R B he
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
      obtain ⟨m', heT, hm⟩ := enter_panic H hE R B he
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
  exact
    { fr := by rw [hT], szS := by simp [entryFrame]; rfl, szT := by rw [hT]; simp,
      tyS := typed_replicate _ _ _ rfl, tyT := by rw [hT]; exact typed_replicate _ _ _ rfl,
      mem := H.wf.entry, treeS := by simp [entry_depth H.cf.parents],
      treeT := by rw [← hge]; simp [entry_depth H.cg.parents],
      atoms := fun a w _ _ y' h => absurd h (hnone a y'),
      den := ⟨fun _ => False, fun _ => False, denOK_empty _ _ _, denOK_empty _ _ _,
        fun _ h => h.elim, fun x h => hentry f ce H.wf H.cf x h,
        fun x h => hentry g ce' H.wg H.cg x (hge ▸ h), hphi f ce H.wf _, hge ▸ hphi g ce' H.wg _⟩,
      live := I.start.1, inv := fun a => by rw [hpois a]; exact I.start.2 a,
      phis := fun bb hbb z hz v hv hph a ha => (hphi f ce H.wf (fun _ => False) bb hbb z hz v hv hph
        a ha).elim }

/-- **The atom simulation** under a source-side invariant. -/
theorem atomSimInv_refines {tabs : Tables} {f g : Func} {ce ce' : CheckEnv}
    (hf : check ce f = .ok ()) (hg : check ce' g = .ok ())
    (hA : RewriteCheck.atomsOK f g = true) (I : SrcInv tabs f)
    (h1 : AtomArgsRefP I g) (h2 : ControlsRefP I g) :
    RefinesUnder Env.Mono tabs g tabs f := by
  have H : Hyp tabs f g ce ce' I := ⟨check_wf hf, check_wf hg, certOK_of_check (check_domCert hf),
    certOK_of_check (check_domCert hg), atomsOK_spec hA, h1, h2⟩
  intro env hE args mem fuel hd
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
    refine finish_refines hd (runLoop_simE (SimR tabs f g I) (fun frS bS iS frT bT iT hR => ?_) fuel
      _ _ _ _ _ _ ⟨H.ok.entry.symm, rfl, entry_rel H env args mem⟩ (finish_defined hd))
    obtain ⟨rfl, rfl, R⟩ := hR
    exact block_sim H hE R

/-- **The atom simulation.** -/
theorem atomSim_refines {tabs : Tables} {f g : Func} {ce ce' : CheckEnv}
    (hf : check ce f = .ok ()) (hg : check ce' g = .ok ())
    (hA : RewriteCheck.atomsOK f g = true)
    (_hcf : RewriteCheck.closedOK f = true) (_hcg : RewriteCheck.closedOK g = true)
    (h1 : Term.AtomArgsRef tabs f g) (h2 : Term.ControlsRef tabs f g) :
    RefinesUnder Env.Mono tabs g tabs f :=
  atomSimInv_refines hf hg hA (SrcInv.triv tabs f) (AtomArgsRef.toP h1 _) (ControlsRef.toP h2 _)

end GoFV.Proof.AtomSim
