import GoFV.Proof.Low.SimEnter

/-!
# The lowered atom simulation (issue #385)

`GoFV.Proof.Low.atomSimL_refines`: Phase 1's atom simulation (`GoFV.Proof.AtomSim`) over `runL`
on both sides. Two checked functions with the same blocks whose atoms correspond
(`LowerCheck.atomsOKL`: the same op and fields, an atom renamed by `renameOp`, or a `Store`
lowered to an arm64 store, `memLower`), whose
corresponding atoms' arguments in `g` refine those of `f` as lowered terms over the atoms
(`AtomArgsRefL`) and whose terminators refine as functions of their controls' terms
(`TermStepRefL`) refine each other under monotone contracts: lock-step simulation
(`runLoopL_simE`) with the relation `BRel` at block entries (`block_simL`: a block entry that does
not panic, `enter_ok`, then the terminators, `termStepRefL_regs`; a panicking one,
`enter_panic`), entry frames equal but their registers (`entry_relL`), and `finish_refines_mono`.
The source runs in `f`'s mode (`Func.lowered`), the target in `g`'s, which is lowered; `f` is
lowered or has the same shapes in both modes (`shapesOK`), and `f`'s atoms are generic ops (true
of every function `lower` gets, `Func.generic_of_lowered`).
-/

namespace GoFV.Proof.Low.Sim

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Proof GoFV.Proof.Dom GoFV.Proof.Low
  GoFV.Proof.Term GoFV.Proof.AtomSim GoFV.Opt.LowerCheck GoFV.Opt.LowerTerm

/-- The simulation relation: the same block and edge, `BRel`. -/
def SimR (tabs : Tables) (f g : Func) (frS : Frame) (bS : ID) (iS : Nat) (frT : Frame) (bT : ID)
    (iT : Nat) : Prop :=
  bT = bS ∧ iT = iS ∧ BRel tabs f g frS frT bS iS

section
variable {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} (H : Hyp tabs f g ce ce')
  {b : ID} {fb gb : Block} {of og : Array ID} (B : BlockData tabs f g b fb gb of og)
include H B

theorem vt_placedL : ∀ x, (V1 g b gb x ∨ x ∈ og.toList) → ∃ w, Placed g x w := fun x hx =>
  hx.elim (v1_placed H.wg B.bmT B.hgb x) fun hm => by
    obtain ⟨hxb, w, hw, -⟩ := (B.mT x).1 hm
    exact ⟨w, (placed_in H.wg B.bmT B.hgb hxb hw).1⟩

/-- **The terminators.** -/
theorem term_simL {frS frT : Frame} {i : Nat} (R : BRel tabs f g frS frT b i) {FS FT : Frame}
    (E : EndRel tabs f g b fb gb of og FS FT) :
    Res.Rel Next.Refines (stepTermL FS fb) (stepTermL FT gb) :=
  termStepRefL_regs H E.dS E.dT (vt_placedL H B) E.rel E.tyS E.tyT B.bmT B.hfb B.hgb
    (fun _ hc => (ctrl_in H.wf H.cf B.bmS B.hfb R.treeS B.mS hc).1)
    (fun _ hc => (ctrl_in H.wg H.cg B.bmT B.hgb R.treeT B.mT hc).1)

/-- The relation at a successor. -/
theorem next_relL {frS frT : Frame} {i : Nat} (R : BRel tabs f g frS frT b i) {FS FT : Frame}
    (E : EndRel tabs f g b fb gb of og FS FT) {e : Edge} (hS : stepTermL FS fb = .ok (.goto e)) :
    BRel tabs f g FS FT e.b e.i := by
  have he := stepTermL_goto_mem hS
  obtain ⟨n1, n2, n3, n4⟩ := next_sets H.wf H.cf B.bmS B.hfb R.treeS B.mS he
  obtain ⟨m1, m2, m3, -⟩ := next_sets H.wg H.cg B.bmT B.hgb R.treeT B.mT
    ((H.ctrls b B.bmT fb gb B.hfb B.hgb).1 e he)
  exact { fr := E.fr, szS := E.szS, szT := E.szT, tyS := E.tyS, tyT := E.tyT, mem := n4,
          treeS := n3, treeT := m3, atoms := E.atoms,
          den := ⟨_, _, E.dS, E.dT, vt_placedL H B, n1, m1, n2, m2⟩ }

end

/-- **One block entry.** -/
theorem block_simL {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} (H : Hyp tabs f g ce ce')
    {env : Env} (hE : env.Mono) {frS frT : Frame} {b : ID} {i : Nat}
    (R : BRel tabs f g frS frT b i) :
    StepSimE Mem.Refines (SimR tabs f g)
      (blockStepL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f) frS b i)
      (blockStepL ⟨g.lowered, false⟩ env (Ctx.makeL tabs g) frT b i) := by
  unfold blockStepL
  rw [makeL_f, makeL_f]
  cases hfb : f.block? b with
  | none => trivial
  | some fb =>
    obtain ⟨gb, of, og, B⟩ := blockData H R.mem hfb
    rw [B.hgb]
    dsimp only
    cases he : enterBlockL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f) frS fb i with
    | ok FS =>
      obtain ⟨FT, heT, E⟩ := enter_ok H hE R B he
      rw [heT]
      dsimp only
      have hst := term_simL H B R E
      generalize hS : stepTermL FS fb = sS at hst ⊢
      generalize stepTermL FT gb = sT at hst ⊢
      cases hst with
      | ok hn =>
        cases hn with
        | goto e => exact ⟨FT, e, rfl, rfl, rfl, next_relL H B R E hS⟩
        | ret hl hm => exact ⟨_, _, rfl, hl, hm⟩
      | panic e hm => exact ⟨_, rfl, hm⟩
      | stuck msg r => trivial
    | panic e m =>
      obtain ⟨m', heT, hm⟩ := enter_panic H hE R B he
      rw [heT]
      exact ⟨m', rfl, hm⟩
    | stuck msg => trivial

/-- The entry frames are related. -/
theorem entry_relL {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} (H : Hyp tabs f g ce ce')
    (env : Env) (args : List Val) (mem : Mem) :
    BRel tabs f g (entryFrame env (Ctx.makeL tabs f) args mem)
      (entryFrame env (Ctx.makeL tabs g) args mem) f.entry 0 := by
  have hT : entryFrame env (Ctx.makeL tabs g) args mem =
      { entryFrame env (Ctx.makeL tabs f) args mem with
        regs := Array.replicate g.valueTab.size none } := entryFrameL_eq H.ok.ownAux args mem
  have hnone : ∀ (a : ID) (y' : Val),
      (entryFrame env (Ctx.makeL tabs g) args mem).regs[a]? ≠ some (some y') := fun a y' h => by
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
  exact
    { fr := by rw [hT], szS := by simp [entryFrame, makeL_f], szT := by rw [hT]; simp,
      tyS := regsTyped_replicate _ _ _ _ rfl,
      tyT := by rw [hT]; exact regsTyped_replicate _ _ _ _ rfl,
      mem := H.wf.entry, treeS := by simp [entry_depth H.cf.parents],
      treeT := by rw [← hge]; simp [entry_depth H.cg.parents],
      atoms := fun a w _ _ y' h => absurd h (hnone a y'),
      den := ⟨fun _ => False, fun _ => False, denOKL_empty _ _ _ _, denOKL_empty _ _ _ _,
        fun _ h => h.elim, fun x h => hentry f ce H.wf H.cf x h,
        fun x h => hentry g ce' H.wg H.cg x (hge ▸ h), hphi f ce H.wf _, hge ▸ hphi g ce' H.wg _⟩ }

/-- `shapesOK` (or `f` lowered) and `g` lowered: `f`'s values have the same shape in both
functions' modes. -/
theorem shp_eq_of {tabs : Tables} {f g : Func}
    (hsh : f.lowered = true ∨ GoFV.Opt.LowerCheck.shapesOK tabs f = true) (hgl : g.lowered = true) :
    ∀ x u, f.value? x = some u → shp f.lowered tabs u.type = shp g.lowered tabs u.type := by
  intro x u hu
  rcases hsh with hfl | hok
  · rw [hfl, hgl]
  · rw [hgl]
    cases hfl : f.lowered
    · simp only [shp, Bool.false_eq_true, ite_false, ite_true]
      have hmem : some u ∈ f.valueTab := by
        unfold Func.value? at hu
        cases hx : f.valueTab[x]? with
        | none => rw [hx] at hu; cases hu
        | some o => rw [hx] at hu; simp at hu; subst hu; exact Array.mem_of_getElem? hx
      unfold GoFV.Opt.LowerCheck.shapesOK at hok
      simp only [Array.all_eq_true'] at hok
      have := hok _ hmem
      simp only at this
      exact (GoFV.Proof.Pass.Rewrite.tyEq_sound this).symm
    · rfl

end GoFV.Proof.Low.Sim

namespace GoFV.Proof.Low

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Proof GoFV.Proof.Dom GoFV.Proof.AtomSim
  GoFV.Opt.LowerCheck GoFV.Opt.LowerTerm Sim

/-- **The lowered atom simulation.** `g` (lowered, `runL` in lowered mode) refines `f` (`runL`
in `f`'s mode) under monotone contracts, when both pass `check`, their atoms correspond
(`atomsOKL`), the atoms' arguments and the terminators refine as terms (`AtomArgsRefL`,
`TermStepRefL`), `f` is lowered or has the same shapes in both modes, and `f`'s atoms are generic
ops (`hfa`; every function with `f.lowered = false` has it, `Func.generic_of_lowered`). -/
theorem atomSimL_refines {tabs : Tables} {f g : Func} {ce ce' : CheckEnv}
    (hf : check ce f = .ok ()) (hg : check ce' g = .ok ())
    (hA : GoFV.Opt.LowerCheck.atomsOKL tabs f g = true)
    (hcf : GoFV.Opt.RewriteCheck.closedOK f = true) (hcg : GoFV.Opt.RewriteCheck.closedOK g = true)
    (hsh : f.lowered = true ∨ GoFV.Opt.LowerCheck.shapesOK tabs f = true)
    (hgl : g.lowered = true)
    (hfa : ∀ x u, f.value? x = some u → termVL tabs u = false → u.op.generic = true)
    (h1 : AtomArgsRefL tabs f g) (h2 : TermStepRefL tabs f g) :
    RefinesLFrom (fun env _ _ => env.Mono) tabs g tabs f := by
  have H : Sim.Hyp tabs f g ce ce' := ⟨check_wf hf, check_wf hg,
    certOK_of_check (check_domCert hf), certOK_of_check (check_domCert hg), atomsOKL_spec hA, h1,
    h2, fun _ => hgl, hgl, hfa, shp_eq_of hsh hgl⟩
  intro env args mem hE fuel hd
  refine ⟨fuel, ?_⟩
  have hc := ctxL_eq (tabs := tabs) H.ok.ownAux
  have hpar : (Ctx.makeL tabs g).params = (Ctx.makeL tabs f).params := by rw [hc]
  have houts : (Ctx.makeL tabs g).outs = (Ctx.makeL tabs f).outs := by rw [hc]
  have hdef : (Ctx.makeL tabs g).defers = (Ctx.makeL tabs f).defers := by rw [hc]
  have hact : (Ctx.makeL tabs g).act = (Ctx.makeL tabs f).act := by rw [hc]
  unfold runL at hd ⊢
  unfold runCtxL at hd ⊢
  rw [hpar, houts, hdef, hact]
  split
  · next hn => simp only [hn] at hd; exact hd.elim
  · next hn =>
    simp only [hn] at hd
    rw [makeL_f, makeL_f]
    rw [makeL_f] at hd
    refine finish_refines_mono hE hd (runLoopL_simE (SimR tabs f g)
      (fun frS bS iS frT bT iT hR => ?_) fuel _ _ _ _ _ _
      ⟨H.ok.entry.symm, rfl, entry_relL H env args mem⟩ (finish_defined hd))
    obtain ⟨rfl, rfl, R⟩ := hR
    exact block_simL H hE R

end GoFV.Proof.Low
