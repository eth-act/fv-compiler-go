import GoFV.Proof.Pass.BranchElimPanic

variable [GoFV.SSA.Sem.Addrs]

/-!
# One checked branchelim rewrite refines

`refines_of_step`: if `g` is `f` with one diamond merged (`Setup f g s`), every run of `f` is
a run of `g`. Macro-step simulation (`runLoop_simIH`): outside the diamond both functions step
alike (`normal_step`); at `dom` the source runs `dom`, the side's arm (if any) and `post` while
the target runs the merged block once (`merged_ok`, `post_panic`, `dom_panic`). The relation
`R`: the same block (never an arm or `post`), frames agreeing outside the arm values, and
lemma (D) for the source's frame at the entry of a reachable block (path dominance, `Setup.dom`).
-/

namespace GoFV.Proof.BranchElim

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.BranchElim GoFV.Proof Dom

variable {f g : Func} {s : Site}

/-- The simulation relation (see the module doc). -/
def R (env : Env) (tabs : Tables) (f : Func) (s : Site) (frS : Frame) (bS iS : Nat) (frT : Frame)
    (bT iT : Nat) : Prop :=
  bT = bS ∧ iT = iS ∧ bS ∈ f.blocks ∧ bS ≠ s.post ∧ s.arm0 ≠ some bS ∧ s.arm1 ≠ some bS ∧
    Reachable f bS ∧ frS.regs.size = f.valueTab.size ∧
    frT = { frS with regs := frT.regs } ∧ frT.regs.size = frS.regs.size ∧
    (∀ a, s.armVal f a = false → frT.regs[a]? = frS.regs[a]?) ∧
    DInv env (Ctx.make tabs f) (fun a => SDom f a bS ∧ a ≠ bS) frS

namespace Setup

variable (S : Setup f g s)
include S

/-- Lemma (D) and reachability along a source block step. -/
theorem dinv_step {env : Env} {tabs : Tables} {b : ID} (hb : b ∈ f.blocks) {B : Block}
    (hB : f.block? b = some B) (ht : Reachable f b) {fr G : Frame} {i : Nat}
    (hs : fr.regs.size = f.valueTab.size)
    (hdi : DInv env (Ctx.make tabs f) (fun a => SDom f a b ∧ a ≠ b) fr)
    (h : enterBlock env (Ctx.make tabs f) fr B i = .ok G) {e : Edge} (he : e ∈ B.succs) :
    DInv env (Ctx.make tabs f) (fun a => SDom f a e.b ∧ a ≠ e.b) G ∧
      Reachable f e.b ∧ G.regs.size = f.valueTab.size ∧ e.b ∈ f.blocks ∧
      G = { fr with regs := G.regs } := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨h1, h2, h3⟩ := dinv_enter_rel hwf S.dom hb hB hs hdi h
  obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 he
  exact ⟨dinv_edge_rel S.dom hb hB ht he h1, (S.dom.edge hb hB ht he).1, by rw [h3, hs],
    (hwf.succLink b B ⟨hb, hB⟩ k e hk).1, h2⟩

/-- The relation after a source block step to a block outside the diamond. -/
theorem R_after {env : Env} {tabs : Tables} {b : ID} (hb : b ∈ f.blocks) {B : Block}
    (hB : f.block? b = some B) (ht : Reachable f b) {fr G GT : Frame} {i : Nat}
    (hs : fr.regs.size = f.valueTab.size)
    (hdi : DInv env (Ctx.make tabs f) (fun a => SDom f a b ∧ a ≠ b) fr)
    (h : enterBlock env (Ctx.make tabs f) fr B i = .ok G) {e : Edge} (he : e ∈ B.succs)
    (hn : e.b ≠ s.post ∧ s.arm0 ≠ some e.b ∧ s.arm1 ≠ some e.b)
    (hGT : GT = { G with regs := GT.regs }) (hGTs : GT.regs.size = G.regs.size)
    (hag : ∀ a, s.armVal f a = false → GT.regs[a]? = G.regs[a]?) :
    R env tabs f s G e.b e.i GT e.b e.i := by
  obtain ⟨h1, h2, h3, h4, -⟩ := S.dinv_step hb hB ht hs hdi h he
  exact ⟨rfl, rfl, h4, hn.1, hn.2.1, hn.2.2, h2, h3, hGT, hGTs, hag, h1⟩

/-- Arm values do not panic. -/
theorem arm_no_panic {env : Env} {tabs : Tables} {a : ID} (ha : s.arm0 = some a ∨ s.arm1 = some a)
    {A : Block} (hA : f.block? a = some A) {fr : Frame} {i : Nat}
    (hs : fr.regs.size = f.valueTab.size) {e : Panic} {m : Mem} :
    enterBlock env (Ctx.make tabs f) fr A i ≠ .panic e m := by
  obtain ⟨ce, hwf⟩ := S.wf
  intro h
  obtain ⟨-, -, -, r, -, -, -, -, -, -, -, -, -, -, -, -, hrA, rv, hrv, -, hrop⟩ :=
    enter_panic_facts hwf (S.armIn ha) hA hs h
  have hra : s.armVal f r = true := by
    unfold Site.armVal
    rcases ha with ha | ha
    · rw [inArm_iff.2 ⟨a, A, ha, hA, hrA⟩]; rfl
    · rw [inArm_iff.2 ⟨a, A, ha, hA, hrA⟩]; simp
  obtain ⟨v, hv, hsafe, -⟩ := armVal_spec S.rel hra
  rw [hrv] at hv; cases hv
  have hroot : isRoot rv.op = true := by
    unfold isRoot
    rcases hrop with h | h
    · simp [h]
    · rw [h]; decide
  simp [specSafeOp, hroot] at hsafe

/-- **The source's `post` step** (after `dom` and the side's arm), matched by the target's
merged block. -/
theorem post_step {tabs : Tables} {env : Env} {frS frT G1 G' : Frame} {i k : Nat}
    {arm arm' : Option ID} {j j' : Nat} {n m : Nat}
    (ih : SimUpTo env (Ctx.make tabs f) (Ctx.make tabs g) (R env tabs f s) n) (hmn : m ≤ n + 1)
    (hfr : frT = { frS with regs := frT.regs }) (hsz : frT.regs.size = frS.regs.size)
    (hs : frS.regs.size = f.valueTab.size)
    (hag : ∀ a, s.armVal f a = false → frT.regs[a]? = frS.regs[a]?)
    (htd : Reachable f s.dom)
    (hdi : DInv env (Ctx.make tabs f) (fun a => SDom f a s.dom ∧ a ≠ s.dom) frS)
    {D P : Block} (hD : f.block? s.dom = some D) (hP : f.block? s.post = some P)
    (h1 : enterBlock env (Ctx.make tabs f) frS D i = .ok G1)
    (htk : Taken s k arm j arm' j')
    (hc : G1.regs[s.c]? = some (some (.bool (k == 0))))
    (hpath : (arm = none ∧ G' = G1) ∨
      (∃ a A, arm = some a ∧ f.block? a = some A ∧ enterBlock env (Ctx.make tabs f) G1 A 0 = .ok G'))
    (hdiP : DInv env (Ctx.make tabs f) (fun a => SDom f a s.post ∧ a ≠ s.post) G')
    (hsG : G'.regs.size = f.valueTab.size) (htp : Reachable f s.post)
    (hd : (runLoop env (Ctx.make tabs f) m G' s.post j).Defined) :
    ∃ fuelT, LoopRefines Eq (runLoop env (Ctx.make tabs f) m G' s.post j)
      (runLoop env (Ctx.make tabs g) fuelT frT s.dom i) := by
  obtain ⟨ce, hwf⟩ := S.wf
  have hpd : s.post ≠ s.dom := by obtain ⟨-, -, -, -, -, -, -, h, -⟩ := S.diamond; exact h
  have hpa0 : s.arm0 ≠ some s.post := fun h => by
    obtain ⟨D2, e0, e1, hD2, -, -, hs2, -, h0, -⟩ := S.diamond
    rcases S.side_facts hD2 (by rw [hs2]; rfl) h0 with ⟨h', -⟩ | ⟨b, A, hb, -, -, -, -, -, -, hbp, -⟩
    · rw [h'] at h; cases h
    · rw [h] at hb; cases hb; exact hbp rfl
  have hpa1 : s.arm1 ≠ some s.post := fun h => by
    obtain ⟨D2, e0, e1, hD2, -, -, hs2, -, -, h1'⟩ := S.diamond
    rcases S.side_facts hD2 (by rw [hs2]; rfl) h1' with ⟨h', -⟩ | ⟨b, A, hb, -, -, -, -, -, -, hbp, -⟩
    · rw [h'] at h; cases h
    · rw [h] at hb; cases hb; exact hbp rfl
  obtain ⟨-, P1, D1', -, hP1, hD1', -, hkP, hcP, hsuP, -⟩ := merged_spec S.rel S.wf S.wg
  rw [hP] at hP1; cases hP1
  have hctlP := (uses_spec S.rel S.postIn hP).2
  cases m with
  | zero => exact absurd hd (runLoop_zero_not_defined)
  | succ m' =>
  cases hst : blockStep env (Ctx.make tabs f) G' s.post j with
  | stuck => exact absurd hd (runLoop_stuck hst)
  | panic e mm =>
    obtain ⟨P', hP', hpan⟩ := blockStep_panic hst
    change f.block? s.post = some P' at hP'
    rw [hP] at hP'; cases hP'
    obtain ⟨D', hD', hT⟩ := S.post_panic hfr hsz hs hag htd hdi hD hP h1 htk hc hpath hpan
    refine ⟨1, ?_⟩
    rw [runLoop_panic hst, runLoop_panic (blockStep_of_panic (ctx := Ctx.make tabs g) hD' hT)]
    exact .panicked_refl e mm
  | ret rs mm =>
    obtain ⟨P', G3, hP', hG3, hterm⟩ := blockStep_ret hst
    change f.block? s.post = some P' at hP'
    rw [hP] at hP'; cases hP'
    obtain ⟨D', GT, hD', hT, -, -, hagT⟩ := S.merged_ok hfr hsz hs hag htd hdi hD hP h1 htk hc
      hpath hG3
    rw [hD'] at hD1'; cases hD1'
    have hterm' := stepTerm_same hkP hcP hsuP (fun c hc' => hagT c (hctlP c hc')) hterm
    refine ⟨1, ?_⟩
    rw [runLoop_ret hst, runLoop_ret (ctx := Ctx.make tabs g) (by
      rw [blockStep_of (ctx := Ctx.make tabs g) hD' hT, hterm'])]
    exact .returned (RefinesList.refl rs) (Mem.Refines.refl _)
  | goto G3 e3 =>
    obtain ⟨P', hP', hG3, hterm⟩ := blockStep_goto hst
    change f.block? s.post = some P' at hP'
    rw [hP] at hP'; cases hP'
    obtain ⟨D', GT, hD', hT, hGT, hGTs, hagT⟩ := S.merged_ok hfr hsz hs hag htd hdi hD hP h1 htk
      hc hpath hG3
    rw [hD'] at hD1'; cases hD1'
    have hterm' := stepTerm_same hkP hcP hsuP (fun c hc' => hagT c (hctlP c hc')) hterm
    have he3 := stepTerm_goto_mem hterm
    have hT' : blockStep env (Ctx.make tabs g) frT s.dom i = .goto GT e3 := by
      rw [blockStep_of (ctx := Ctx.make tabs g) hD' hT, hterm']
    rw [runLoop_goto hst] at hd ⊢
    exact refines_goto hT' (ih m' (by omega) G3 e3.b e3.i GT e3.b e3.i
      (S.R_after S.postIn hP htp hsG hdiP hG3 he3
        (S.succ_normal S.postIn hP hpd hpa0 hpa1 he3) hGT hGTs hagT) hd)

/-- **The source leaves `dom` along side `k`.** -/
theorem dom_goto {tabs : Tables} {env : Env} {frS frT G1 : Frame} {i k : Nat}
    {arm arm' : Option ID} {j j' : Nat} {n : Nat}
    (ih : SimUpTo env (Ctx.make tabs f) (Ctx.make tabs g) (R env tabs f s) n)
    (hfr : frT = { frS with regs := frT.regs }) (hsz : frT.regs.size = frS.regs.size)
    (hs : frS.regs.size = f.valueTab.size)
    (hag : ∀ a, s.armVal f a = false → frT.regs[a]? = frS.regs[a]?)
    (htd : Reachable f s.dom)
    (hdi : DInv env (Ctx.make tabs f) (fun a => SDom f a s.dom ∧ a ≠ s.dom) frS)
    {D : Block} (hD : f.block? s.dom = some D) {e : Edge} (he : D.succs[k]? = some e)
    (hside : sideOf f s.dom s.post k e = some (arm, j)) (htk : Taken s k arm j arm' j')
    (h1 : enterBlock env (Ctx.make tabs f) frS D i = .ok G1)
    (hc : G1.regs[s.c]? = some (some (.bool (k == 0))))
    (hd : (runLoop env (Ctx.make tabs f) n G1 e.b e.i).Defined) :
    ∃ fuelT, LoopRefines Eq (runLoop env (Ctx.make tabs f) n G1 e.b e.i)
      (runLoop env (Ctx.make tabs g) fuelT frT s.dom i) := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨P, hP, -⟩ := S.rel.shape
  obtain ⟨hdi1, hte, hs1, -, -⟩ := S.dinv_step S.domIn hD htd hs hdi h1 (Array.mem_of_getElem? he)
  rcases S.side_facts hD he hside with ⟨rfl, rfl⟩ | ⟨a, A, rfl, rfl, haIn, hA, hAk, -, hAs, -, -⟩
  · exact S.post_step ih (Nat.le_succ n) hfr hsz hs hag htd hdi hD hP h1 htk hc (.inl ⟨rfl, rfl⟩)
      hdi1 hs1 hte hd
  · have ha : s.arm0 = some a ∨ s.arm1 = some a := by
      rcases htk with ⟨-, h, -⟩ | ⟨-, h, -⟩
      · exact .inl h.symm
      · exact .inr h.symm
    cases n with
    | zero => exact (runLoop_zero_not_defined hd).elim
    | succ n' =>
    cases hst : blockStep env (Ctx.make tabs f) G1 a 0 with
    | stuck => exact absurd hd (runLoop_stuck hst)
    | panic e' m' =>
      obtain ⟨A', hA', hpan⟩ := blockStep_panic hst
      change f.block? a = some A' at hA'
      rw [hA] at hA'; cases hA'
      exact absurd hpan (S.arm_no_panic ha hA hs1)
    | ret rs m' =>
      obtain ⟨A', G', hA', -, hterm⟩ := blockStep_ret hst
      change f.block? a = some A' at hA'
      rw [hA] at hA'; cases hA'
      obtain ⟨e', -, he'⟩ := stepTerm_plain hAk hterm
      cases he'
    | goto G' e2 =>
      obtain ⟨A', hA', hG', hterm⟩ := blockStep_goto hst
      change f.block? a = some A' at hA'
      rw [hA] at hA'; cases hA'
      obtain ⟨e2', he2, he2'⟩ := stepTerm_plain hAk hterm
      cases he2'
      rw [hAs] at he2; simp at he2; subst he2
      obtain ⟨hdi2, htp, hs2, -, -⟩ := S.dinv_step haIn hA hte hs1 hdi1 hG' (e := ⟨s.post, j⟩)
        (by rw [hAs]; simp)
      rw [runLoop_goto hst] at hd ⊢
      exact S.post_step (m := n') ih (Nat.le_succ_of_le (Nat.le_succ n')) hfr hsz hs hag htd hdi hD
        hP h1 htk hc (.inr ⟨a, A, rfl, hA, hG'⟩) hdi2 hs2 htp hd

/-- **One step of the simulation** (macro step at `dom`). -/
theorem sim_step {tabs : Tables} {env : Env} (n : Nat)
    (ih : SimUpTo env (Ctx.make tabs f) (Ctx.make tabs g) (R env tabs f s) n)
    {frS frT : Frame} {bS iS bT iT : Nat} (hR : R env tabs f s frS bS iS frT bT iT)
    (hd : (runLoop env (Ctx.make tabs f) (n + 1) frS bS iS).Defined) :
    ∃ fuelT, LoopRefines Eq (runLoop env (Ctx.make tabs f) (n + 1) frS bS iS)
      (runLoop env (Ctx.make tabs g) fuelT frT bT iT) := by
  obtain ⟨hbT, hiT, hb, hbp, hba0, hba1, ht, hs, hfr, hsz, hag, hdi⟩ := hR
  rw [hbT, hiT]
  by_cases hbd : bS = s.dom
  · subst hbd
    obtain ⟨D, e0, e1, hD, hk, hctl, hsucc, -, h0, h1⟩ := S.diamond
    cases hst : blockStep env (Ctx.make tabs f) frS s.dom iS with
    | stuck => exact absurd hd (runLoop_stuck hst)
    | panic e m =>
      obtain ⟨D2, hD2, hpan⟩ := blockStep_panic hst
      change f.block? s.dom = some D2 at hD2
      rw [hD] at hD2; cases hD2
      obtain ⟨D', hD', hT⟩ := S.dom_panic hfr hsz hs hag ht hdi hD hpan
      refine ⟨1, ?_⟩
      rw [runLoop_panic hst, runLoop_panic (blockStep_of_panic (ctx := Ctx.make tabs g) hD' hT)]
      exact .panicked_refl e m
    | ret rs m =>
      obtain ⟨D2, G, hD2, -, hterm⟩ := blockStep_ret hst
      change f.block? s.dom = some D2 at hD2
      rw [hD] at hD2; cases hD2
      obtain ⟨b, e, -, -, he⟩ := stepTerm_if hk hctl hterm
      cases he
    | goto G1 e =>
      obtain ⟨D2, hD2, hG1, hterm⟩ := blockStep_goto hst
      change f.block? s.dom = some D2 at hD2
      rw [hD] at hD2; cases hD2
      obtain ⟨b, e', hcv, hse, he⟩ := stepTerm_if hk hctl hterm
      cases he
      rw [runLoop_goto hst] at hd ⊢
      cases b with
      | true =>
        have hse0 : D.succs[0]? = some e0 := by rw [hsucc]; rfl
        simp only [ite_true] at hse
        rw [hse0] at hse; cases hse
        exact S.dom_goto ih hfr hsz hs hag ht hdi hD hse0 h0
          (.inl ⟨rfl, rfl, rfl, rfl, rfl⟩) hG1 hcv hd
      | false =>
        have hse1 : D.succs[1]? = some e1 := by rw [hsucc]; rfl
        simp only [Bool.false_eq_true, ite_false] at hse
        rw [hse1] at hse; cases hse
        exact S.dom_goto ih hfr hsz hs hag ht hdi hD hse1 h1
          (.inr ⟨rfl, rfl, rfl, rfl, rfl⟩) hG1 hcv hd
  · obtain ⟨hgo, hret, hpan⟩ := S.normal_step (tabs := tabs) (env := env) (i := iS) hb hbd hbp hba0
      hba1 hfr hsz hag
    cases hst : blockStep env (Ctx.make tabs f) frS bS iS with
    | stuck => exact absurd hd (runLoop_stuck hst)
    | panic e m =>
      refine ⟨1, ?_⟩
      rw [runLoop_panic hst, runLoop_panic (hpan e m hst)]
      exact .panicked_refl e m
    | ret rs m =>
      refine ⟨1, ?_⟩
      rw [runLoop_ret hst, runLoop_ret (hret rs m hst)]
      exact .returned (RefinesList.refl rs) (Mem.Refines.refl _)
    | goto G e =>
      obtain ⟨GT, hT, hGT, hGTs, hagT⟩ := hgo G e hst
      obtain ⟨B, hB, hG, hterm⟩ := blockStep_goto hst
      change f.block? bS = some B at hB
      have he := stepTerm_goto_mem hterm
      rw [runLoop_goto hst] at hd ⊢
      exact refines_goto hT (ih n (Nat.le_refl n) G e.b e.i GT e.b e.i
        (S.R_after hb hB ht hs hdi hG he (S.succ_normal hb hB hbd hba0 hba1 he) hGT hGTs hagT) hd)

/-- **One checked branchelim rewrite refines.** -/
theorem refines_of_step {tabs : Tables} : Refines tabs g tabs f := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨-, -, hent, hown, hgsz, -⟩ := S.rel.parts
  intro env args mem fuel hd
  unfold run runCtx at hd ⊢
  rw [params_eq hown]
  split
  · rename_i hn; simp only [hn] at hd; exact hd.elim
  · rename_i hn
    simp only [hn] at hd
    have hentry : entryFrame env (Ctx.make tabs g) args mem =
        entryFrame env (Ctx.make tabs f) args mem := by
      unfold entryFrame frameMem frameAllocs
      rw [show (Ctx.make tabs g).f.valueTab.size = (Ctx.make tabs f).f.valueTab.size from hgsz]
      simp only [Ctx.make, abiParams, hown]
    have houts : (Ctx.make tabs g).outs = (Ctx.make tabs f).outs := by
      simp only [Ctx.make, abiParams, hown]
    rw [hentry, houts, show (Ctx.make tabs g).act = (Ctx.make tabs f).act from rfl,
      show (Ctx.make tabs g).f.entry = (Ctx.make tabs f).f.entry from hent]
    have hR0 : R env tabs f s (entryFrame env (Ctx.make tabs f) args mem) f.entry 0
        (entryFrame env (Ctx.make tabs f) args mem) f.entry 0 := by
      have hE := hwf.entry
      have hep : ∀ (b : ID), (s.post = b ∨ s.arm0 = some b ∨ s.arm1 = some b) → b ≠ f.entry := by
        intro b hb hbe
        subst hbe
        obtain ⟨Bb, hBb, -⟩ := hwf.blockId f.entry hE
        have h0 := hwf.entryPreds Bb hBb
        obtain ⟨D, e0, e1, hD, -, -, hs2, -, hs0, hs1⟩ := S.diamond
        rcases hb with hb | hb | hb
        · obtain ⟨P, hP, hps, -⟩ := S.rel.shape
          rw [hb, hBb] at hP; cases hP; omega
        · rcases S.side_facts hD (by rw [hs2]; rfl) hs0 with ⟨h', -⟩ | ⟨a, A, ha, -, -, hA, -, hpr, -⟩
          · rw [h'] at hb; cases hb
          · rw [hb] at ha; cases ha; rw [hBb] at hA; cases hA
            rw [hpr] at h0; simp at h0
        · rcases S.side_facts hD (by rw [hs2]; rfl) hs1 with ⟨h', -⟩ | ⟨a, A, ha, -, -, hA, -, hpr, -⟩
          · rw [h'] at hb; cases hb
          · rw [hb] at ha; cases ha; rw [hBb] at hA; cases hA
            rw [hpr] at h0; simp at h0
      exact ⟨rfl, rfl, hE, fun h => hep _ (.inl h.symm) rfl, fun h => hep _ (.inr (.inl h)) rfl,
        fun h => hep _ (.inr (.inr h)) rfl, S.dom.entry,
        by simp [Ctx.make, entryFrame], rfl, rfl, fun _ _ => rfl, dinv_entry_rel S.dom _⟩
    obtain ⟨fuelT, h⟩ := runLoop_simIH (R env tabs f s) (fun n ih _ _ _ _ _ _ hR hd' =>
      S.sim_step n ih hR hd') fuel _ _ _ _ _ _ hR0 (finish_defined hd)
    exact ⟨fuelT, finish_refines hd h⟩

end Setup

end GoFV.Proof.BranchElim
