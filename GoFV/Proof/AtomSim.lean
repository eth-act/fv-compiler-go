import GoFV.Proof.AtomSimPanic

/-!
# The atom simulation (issue #113)

`atomSim_refines`: two checked functions with the same blocks, terminators and atoms
(`RewriteCheck.atomsOK`), whose atoms' arguments and controls in `g` refine those of `f` as
terms over the atoms (`Term.AtomArgsRef`, `Term.ControlsRef`), refine each other under monotone
contracts: lock-step simulation (`runLoop_simE`) with the relation `BRel` at block entries
(`block_sim`: a block entry that does not panic, `enter_ok`, then refined controls,
`stepTerm_mono2`; a panicking one, `enter_panic`), entry frames equal but their registers
(`entry_rel`), and `finish_refines`.
-/

namespace GoFV.Proof.AtomSim

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Proof.Dom GoFV.Opt GoFV.Opt.RewriteCheck GoFV.Proof.Term

/-- The simulation relation: the same block and edge, `BRel`. -/
def SimR (tabs : Tables) (f g : Func) (frS : Frame) (bS : ID) (iS : Nat) (frT : Frame) (bT : ID)
    (iT : Nat) : Prop :=
  bT = bS ∧ iT = iS ∧ BRel tabs f g frS frT bS iS

section
variable {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} (H : Hyp tabs f g ce ce')
  {b : ID} {fb gb : Block} {of og : Array ID} (B : BlockData f g b fb gb of og)
include H B

theorem vt_placed : ∀ x, (V1 g b gb x ∨ x ∈ og.toList) → ∃ w, Placed g x w := fun x hx =>
  hx.elim (v1_placed H.wg B.bmT B.hgb x) fun hm => by
    obtain ⟨hxb, w, hw, -⟩ := (B.mT x).1 hm
    exact ⟨w, (placed_in H.wg B.bmT B.hgb hxb hw).1⟩

/-- **The terminators** on refined controls. -/
theorem term_sim {frS frT : Frame} {i : Nat} (R : BRel tabs f g frS frT b i) {FS FT : Frame}
    (E : EndRel tabs f g b fb gb of og FS FT) :
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
    have hr := termRef_regs H E.dS E.dT (vt_placed H B) E.rel E.tyS E.tyT hT hc hc'
    dsimp only
    rw [reg_rv (E.dS c hc).1, reg_rv (E.dT _ hc').1]
    exact .ok hr

/-- The relation at a successor. -/
theorem next_rel {frS frT : Frame} {i : Nat} (R : BRel tabs f g frS frT b i) {FS FT : Frame}
    (E : EndRel tabs f g b fb gb of og FS FT) {e : Edge} (he : e ∈ fb.succs) :
    BRel tabs f g FS FT e.b e.i := by
  obtain ⟨n1, n2, n3, n4⟩ := next_sets H.wf H.cf B.bmS B.hfb R.treeS B.mS he
  obtain ⟨m1, m2, m3, -⟩ := next_sets H.wg H.cg B.bmT B.hgb R.treeT B.mT
    (by rw [← B.ba.succs]; exact he)
  exact ⟨E.fr, E.szS, E.szT, E.tyS, E.tyT, n4, n3, m3, E.atoms,
    _, _, E.dS, E.dT, vt_placed H B, n1, m1, n2, m2⟩

end

/-- **One block entry.** -/
theorem block_sim {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} (H : Hyp tabs f g ce ce')
    {env : Env} (hE : env.Mono) {frS frT : Frame} {b : ID} {i : Nat}
    (R : BRel tabs f g frS frT b i) :
    StepSimE (SimR tabs f g) (blockStep env (Ctx.make tabs f) frS b i)
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
        | goto e => exact ⟨FT, e, rfl, rfl, rfl, next_rel H B R E (stepTerm_goto_mem hS)⟩
        | ret hl hm => exact ⟨_, _, rfl, hl, hm⟩
      | panic e hm => exact ⟨_, rfl, hm⟩
      | stuck msg r => trivial
    | panic e m =>
      obtain ⟨m', heT, hm⟩ := enter_panic H hE R B he
      rw [heT]
      exact ⟨m', rfl, hm⟩
    | stuck msg => trivial

/-- The entry frames are related. -/
theorem entry_rel {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} (H : Hyp tabs f g ce ce')
    (env : Env) (args : List Val) (mem : Mem) :
    BRel tabs f g (entryFrame env (Ctx.make tabs f) args mem)
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
  refine ⟨by rw [hT], by simp [entryFrame]; rfl, by rw [hT]; simp, typed_replicate _ _ _ rfl,
    by rw [hT]; exact typed_replicate _ _ _ rfl, H.wf.entry,
    by simp [entry_depth H.cf.parents], by rw [← hge]; simp [entry_depth H.cg.parents],
    fun a w _ _ y' h => absurd h (hnone a y'), fun _ => False, fun _ => False,
    denOK_empty _ _ _, denOK_empty _ _ _, fun _ h => h.elim,
    fun x h => hentry f ce H.wf H.cf x h, fun x h => hentry g ce' H.wg H.cg x (hge ▸ h),
    hphi f ce H.wf _, hge ▸ hphi g ce' H.wg _⟩

/-- **The atom simulation.** -/
theorem atomSim_refines {tabs : Tables} {f g : Func} {ce ce' : CheckEnv}
    (hf : check ce f = .ok ()) (hg : check ce' g = .ok ())
    (hA : RewriteCheck.atomsOK f g = true)
    (_hcf : RewriteCheck.closedOK f = true) (_hcg : RewriteCheck.closedOK g = true)
    (h1 : Term.AtomArgsRef tabs f g) (h2 : Term.ControlsRef tabs f g) :
    RefinesUnder Env.Mono tabs g tabs f := by
  have H : Hyp tabs f g ce ce' := ⟨check_wf hf, check_wf hg, certOK_of_check (check_domCert hf),
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
    refine finish_refines hd (runLoop_simE (SimR tabs f g) (fun frS bS iS frT bT iT hR => ?_) fuel
      _ _ _ _ _ _ ⟨H.ok.entry.symm, rfl, entry_rel H env args mem⟩ (finish_defined hd))
    obtain ⟨rfl, rfl, R⟩ := hR
    exact block_sim H hE R

end GoFV.Proof.AtomSim
