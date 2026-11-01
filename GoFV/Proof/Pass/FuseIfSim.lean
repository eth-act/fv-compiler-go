import GoFV.Proof.Pass.FuseIfPres
import GoFV.Proof.Pass.FusePlainSim
import GoFV.Proof.SimIH

/-!
# One checked `fuseBlockIf` rewrite refines

`refines_of_step`: if `g` is the checked `fuseBlockIf` rewrite of `f` (`Setup`), every run of `f`
is a run of `g`. Macro-step simulation (`runLoop_simIH`) with frames agreeing outside the free
values `X` (`Agr`): a block other than `b` steps alike in both, entered along related edge
indices (`IdxRel`), the target's edges renumbered by `rmE` (`normal_step`); at `b` the source
takes its branch: along side 1 both continue alike; along side 0 the source runs side 0's arm
(if any) into the join block `ss` while the target runs side 1's arm (speculated, `enter_spec`)
into `ss`, whose used `Phi`s read the same value along both sides (`b_step`). The relation `Rel`
also carries lemma (D) for the source's frame (free values' arguments are defined).
-/

namespace GoFV.Proof.FuseIf

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.Fuse GoFV.Opt.Fuse.IfC GoFV.Proof
  Dom

/-- The simulation relation (see the module doc). -/
def Rel (env : Env) (tabs : Tables) (f : Func) (s : Site) (R : List ID) (frS : Frame)
    (bS iS : Nat) (frT : Frame) (bT iT : Nat) : Prop :=
  bT = bS ∧ bS ∈ f.blocks ∧ ¬ (s.unlinked f = true ∧ s.arm0 = some bS) ∧ IdxRel s f bS iS iT ∧
    Reachable f bS ∧ frS.regs.size = f.valueTab.size ∧
    DInv env (Ctx.make tabs f) (fun a => SDom f a bS ∧ a ≠ bS) frS ∧ Agr (s.inX f R) frS frT

variable {ce : CheckEnv} {f g : Func} {s : Site} {R : List ID}

namespace Setup

variable (S : Setup ce f g s R)
include S

/-- Lemma (D) and reachability along a source block step. -/
theorem dinv_step {env : Env} {tabs : Tables} {b : ID} (hb : b ∈ f.blocks) {B : Block}
    (hB : f.block? b = some B) (ht : Reachable f b) {fr G : Frame} {i : Nat}
    (hs : fr.regs.size = f.valueTab.size)
    (hdi : DInv env (Ctx.make tabs f) (fun a => SDom f a b ∧ a ≠ b) fr)
    (h : enterBlock env (Ctx.make tabs f) fr B i = .ok G) {e : Edge} (he : e ∈ B.succs) :
    DInv env (Ctx.make tabs f) (fun a => SDom f a e.b ∧ a ≠ e.b) G ∧
      Reachable f e.b ∧ G.regs.size = f.valueTab.size ∧ e.b ∈ f.blocks := by
  obtain ⟨h1, h2, h3⟩ := dinv_enter_rel S.wf S.domR hb hB hs hdi h
  obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 he
  exact ⟨dinv_edge_rel S.domR hb hB ht he h1, (S.domR.edge hb hB ht he).1, by rw [h3, hs],
    (S.wf.succLink b B ⟨hb, hB⟩ k e hk).1⟩

/-- The free values' arguments outside a reachable block are defined (lemma (D)). -/
theorem freeDef_other {env : Env} {tabs : Tables} {y : ID} (hy : y ∈ f.blocks) {Y Y' : Block}
    (hY : f.block? y = some Y) (hvals : Y'.values = Y.values) (hreach : Reachable f y)
    {frS frT : Frame} (hdi : DInv env (Ctx.make tabs f) (fun a => SDom f a y ∧ a ≠ y) frS)
    (hA : Agr (s.inX f R) frS frT) : FreeDef g (s.inX f R) Y' frT := by
  intro x hx hX gv hgv a ha hna
  rw [hvals] at hx hna
  obtain ⟨fv, gv', hfv, hgv', -, -, hargs⟩ := S.free_val hX
  rw [hgv] at hgv'; cases hgv'
  rcases hargs with h | ⟨hnp, heq, hgX, -⟩
  · rw [h] at ha; simp at ha
  · have ha' : a ∈ fv.args := heq ▸ ha
    have hsd := S.domR.uses hy hY hreach hx hfv hnp ha'
    have hl : Listed f a := S.wf.argListed y Y x fv ⟨⟨hy, hY⟩, hx, hfv⟩ a ha'
    obtain ⟨v, B, hP, hvb, hB, haB, -⟩ := blockOf_listed S.wf hl
    have hne : blockOf f a ≠ y := fun h => by rw [h, hY] at hB; cases hB; exact hna haB
    obtain ⟨r, hr, -⟩ := hdi a v hP (by rw [hvb]; exact ⟨hsd, hne⟩)
    exact ⟨r, by rw [hA.2.2 a (hgX a ha), hr]⟩

theorem b_ne_rmT : s.b ≠ s.rmT f := by
  unfold Site.rmT
  split
  · split
    · exact S.rel.ss_ne_b.symm
    · rename_i a ha _; exact S.b_ne_arm (.inl ha)
  · exact S.rel.ss_ne_b.symm

/-- **A block other than `b`** steps alike in both functions. -/
theorem normal_step {env : Env} {tabs : Tables} {n : Nat}
    (ih : SimUpTo env (Ctx.make tabs f) (Ctx.make tabs g) (Rel env tabs f s R) n)
    {frS frT : Frame} {bS iS bT iT : Nat} (hR : Rel env tabs f s R frS bS iS frT bT iT)
    (hnb : bS ≠ s.b) (hd : (runLoop env (Ctx.make tabs f) (n + 1) frS bS iS).Defined) :
    ∃ fuelT, LoopRefines Eq (runLoop env (Ctx.make tabs f) (n + 1) frS bS iS)
      (runLoop env (Ctx.make tabs g) fuelT frT bT iT) := by
  obtain ⟨hbT, hb, hna, hI, ht, hs, hdi, hA⟩ := hR
  rw [hbT]
  obtain ⟨Y, Y', hY, hY', -, -, -, -, -, hrest⟩ := S.block_core hb hna
  obtain ⟨hBR, hk, hcs, hsu, hcX⟩ := S.brel_other hb hnb hna hY hY' hI
  have hfree := S.freeDef_other hb hY (hrest hnb).1 ht hdi hA
  have B : Blocks f g bS Y Y' := ⟨hb, hY, by rw [S.rel.blocks]; exact hb, hY'⟩
  cases hst : blockStep env (Ctx.make tabs f) frS bS iS with
  | stuck => exact absurd hd (runLoop_stuck hst)
  | panic e m =>
    obtain ⟨Y2, hY2, hpan⟩ := blockStep_panic hst
    change f.block? bS = some Y2 at hY2
    rw [hY] at hY2; cases hY2
    have hT := enter_panic S.two B hBR hA hs hfree hpan
    refine ⟨1, ?_⟩
    rw [runLoop_panic hst, runLoop_panic (blockStep_of_panic (ctx := Ctx.make tabs g) hY' hT)]
    exact .panicked_refl e m
  | ret rs m =>
    obtain ⟨Y2, G, hY2, hG, hterm⟩ := blockStep_ret hst
    change f.block? bS = some Y2 at hY2
    rw [hY] at hY2; cases hY2
    obtain ⟨GT, hGT, hAG, -⟩ := enter_ok S.two B hBR hA hs hfree hG
    have hterm' : stepTerm GT Y' = .ok (.ret rs m) := by
      rw [stepTerm_agree (bS := Y') (bT := Y') ⟨rfl, rfl, rfl, rfl, rfl⟩
        (fun c hc => hAG.2.2 c (hcX c (hcs ▸ hc)))]
      exact (FusePlain.stepTerm_redirect hk hcs hsu).2 rs m hterm
    refine ⟨1, ?_⟩
    rw [runLoop_ret hst, runLoop_ret (ctx := Ctx.make tabs g)
      (by rw [blockStep_of (ctx := Ctx.make tabs g) hY' hGT, hterm'])]
    exact .returned (RefinesList.refl rs) (Mem.Refines.refl _)
  | goto G e =>
    obtain ⟨Y2, hY2, hG, hterm⟩ := blockStep_goto hst
    change f.block? bS = some Y2 at hY2
    rw [hY] at hY2; cases hY2
    obtain ⟨GT, hGT, hAG, -⟩ := enter_ok S.two B hBR hA hs hfree hG
    have hterm' : stepTerm GT Y' = .ok (.goto (s.rmE f e)) := by
      rw [stepTerm_agree (bS := Y') (bT := Y') ⟨rfl, rfl, rfl, rfl, rfl⟩
        (fun c hc => hAG.2.2 c (hcX c (hcs ▸ hc)))]
      exact (FusePlain.stepTerm_redirect hk hcs hsu).1 e hterm
    have he := stepTerm_goto_mem hterm
    obtain ⟨k, hk'⟩ := Array.mem_iff_getElem?.1 he
    obtain ⟨hne, hnd⟩ := S.succ_ok hb hY hk' (.inl hnb) hna
    obtain ⟨hdi', ht', hGs', hem⟩ := S.dinv_step hb hY ht hs hdi hG he
    have hT : blockStep env (Ctx.make tabs g) frT bS iT = .goto GT ⟨e.b, tIdx s f e.b e.i⟩ := by
      rw [blockStep_of (ctx := Ctx.make tabs g) hY' hGT, hterm', rmE_eq]
    rw [runLoop_goto hst] at hd ⊢
    exact refines_goto hT (ih n (Nat.le_refl n) _ _ _ _ _ _
      ⟨rfl, hem, hnd, .inl ⟨hne, rfl⟩, ht', hGs', hdi', hAG⟩ hd)

/-- **Side 1 of the target from `b`**: directly into `ss`, or through side 1's arm, speculated
(its values are free; their arguments are defined by lemma (D) at `b`). -/
theorem side1_target {env : Env} {tabs : Tables} {G GT : Frame} (hAG : Agr (s.inX f R) G GT)
    (hGs : G.regs.size = f.valueTab.size)
    (hdi : DInv env (Ctx.make tabs f) (fun a => SDom f a s.b) G) (hbr : Reachable f s.b) :
    ∃ GT2, Agr (s.inX f R) G GT2 ∧ ∀ (act : Nat) (o : Outcome),
      (∃ fuel, LoopRefines Eq o
        (runLoop env (Ctx.make tabs g) fuel GT2 s.ss (tIdx s f s.ss s.j1))) →
      ∃ fuel, LoopRefines Eq o
        (runLoop env (Ctx.make tabs g) fuel GT (s.rmE f s.e1).b (s.rmE f s.e1).i) := by
  have hs1 := S.rel.side1
  cases ha1 : s.arm1 with
  | none =>
    rw [ha1] at hs1
    have he := direct_spec hs1
    refine ⟨GT, hAG, fun act o h => ?_⟩
    rw [rmE_eq, he]; exact h
  | some a1 =>
    rw [ha1] at hs1
    obtain ⟨he1, ha1b, -, A1, hA1, hk1, hsu1, -⟩ := arm_spec hs1
    obtain ⟨B, hB, -, -, hsu⟩ := S.bB
    have hmem1 : s.e1 ∈ B.succs := by rw [hsu]; simp
    obtain ⟨-, hnd⟩ := S.succ_ok S.rel.bIn hB (k := 1) (e := s.e1) (by rw [hsu]; rfl)
      (.inr (by decide)) S.not_dead_b
    rw [he1] at hnd
    have ha1m := S.arm1_mem ha1
    obtain ⟨A1x, A1', hA1x, hA1', -, -, -, hsc, -, hrest⟩ := S.block_core ha1m hnd
    rw [hA1] at hA1x; cases hA1x
    obtain ⟨hv, hk', -, hsu'⟩ := hrest ha1b
    have hreach1 : Reachable f a1 := by
      have := (S.domR.edge S.rel.bIn hB hbr hmem1).1; rwa [he1] at this
    have hX : ∀ x ∈ A1.values, s.inX f R x = true := by
      intro x hx
      unfold Site.inX Site.armVal
      simp [ha1, valsOf_eq hA1, hx]
    have hss : ∀ x ∈ A1'.values, ∃ gv, g.value? x = some gv ∧ specSafeOp gv.op = true := by
      intro x hx; rw [hv] at hx
      obtain ⟨-, gv, -, hgv, hsg, -⟩ := S.free_val (hX x hx)
      exact ⟨gv, hgv, hsg⟩
    have hdef : ∀ x ∈ A1'.values, ∀ gv, g.value? x = some gv → ∀ a ∈ gv.args,
        a ∉ A1'.values → ∃ z, GT.regs[a]? = some (some z) := by
      intro x hx gv hgv a ha hna
      rw [hv] at hx hna
      obtain ⟨fv, gv', hfv, hgv', -, -, hargs⟩ := S.free_val (hX x hx)
      rw [hgv] at hgv'; cases hgv'
      rcases hargs with h | ⟨hnp, heq, hgX, -⟩
      · rw [h] at ha; simp at ha
      · have ha' : a ∈ fv.args := heq ▸ ha
        have hsd := S.domR.uses ha1m hA1 hreach1 hx hfv hnp ha'
        have hl : Listed f a := S.wf.argListed a1 A1 x fv ⟨⟨ha1m, hA1⟩, hx, hfv⟩ a ha'
        obtain ⟨v, Bv, hP, hvb, hBv, haB, -⟩ := blockOf_listed S.wf hl
        have hne : blockOf f a ≠ a1 := fun h => by
          rw [h, hA1] at hBv; cases hBv; exact hna haB
        have hsdb : SDom f (blockOf f a) s.b :=
          (S.domR.edge S.rel.bIn hB hbr hmem1).2 _ (by rw [he1]; exact hsd) (by rw [he1]; exact hne)
        obtain ⟨r, hr, -⟩ := hdi a v hP (by rw [hvb]; exact hsdb)
        exact ⟨r, by rw [hAG.2.2 a (hgX a ha), hr]⟩
    obtain ⟨GT2, hGT2, h2, h3, h4⟩ := enter_spec S.wg (tabs := tabs) (env := env)
      (by rw [S.rel.blocks]; exact ha1m) hA1' hss hsc (fr := GT)
      (by rw [hAG.2.1, hGs, S.rel.vsize]) hdef (tIdx s f a1 s.e1.i)
    refine ⟨GT2, ⟨FusePlain.frame_trans h2 hAG.1, by rw [h3, hAG.2.1], fun a haX => ?_⟩,
      fun act o h => ?_⟩
    · have hna : a ∉ A1'.values := fun hm => by
        rw [hv] at hm; rw [hX a hm] at haX; cases haX
      rw [h4 a hna, hAG.2.2 a haX]
    · have hterm : stepTerm GT2 A1' = .ok (.goto ⟨s.ss, tIdx s f s.ss s.j1⟩) := by
        unfold stepTerm; rw [hk', hk1]; unfold succ; rw [hsu', hsu1]; simp [rmE_eq]; rfl
      have hT : blockStep env (Ctx.make tabs g) GT a1 (tIdx s f a1 s.e1.i) =
          .goto GT2 ⟨s.ss, tIdx s f s.ss s.j1⟩ := by
        rw [blockStep_of (ctx := Ctx.make tabs g) hA1' hGT2, hterm]
      rw [rmE_eq, he1]
      exact refines_goto hT h

/-- **At `b`**: the source takes its branch; along side 0 it reaches `ss` (through side 0's arm
if any) while the target reaches `ss` along side 1. -/
theorem b_step {env : Env} {tabs : Tables} {n : Nat}
    (ih : SimUpTo env (Ctx.make tabs f) (Ctx.make tabs g) (Rel env tabs f s R) n)
    {frS frT : Frame} {iS bT iT : Nat} (hR : Rel env tabs f s R frS s.b iS frT bT iT)
    (hd : (runLoop env (Ctx.make tabs f) (n + 1) frS s.b iS).Defined) :
    ∃ fuelT, LoopRefines Eq (runLoop env (Ctx.make tabs f) (n + 1) frS s.b iS)
      (runLoop env (Ctx.make tabs g) fuelT frT bT iT) := by
  obtain ⟨hbT, hb, hna, hI, ht, hs, hdi, hA⟩ := hR
  rw [hbT]
  have hiT : iT = iS := by
    rcases hI with ⟨-, h⟩ | ⟨h, -⟩
    · rw [h]; unfold tIdx; rw [if_neg S.b_ne_rmT]
    · exact absurd h.symm S.rel.ss_ne_b
  rw [hiT]
  obtain ⟨B, hB, hk, hc, hsu⟩ := S.bB
  obtain ⟨B1, Bg, hB1, hBg, -⟩ := S.block_core hb hna
  rw [hB] at hB1; cases hB1
  obtain ⟨hBR, hkg, -, hsug, hfree⟩ := S.brel_b hB hBg iS (fr := frT)
  have Bk : Blocks f g s.b B Bg := ⟨hb, hB, by rw [S.rel.blocks]; exact hb, hBg⟩
  cases hst : blockStep env (Ctx.make tabs f) frS s.b iS with
  | stuck => exact absurd hd (runLoop_stuck hst)
  | panic e m =>
    obtain ⟨B2, hB2, hpan⟩ := blockStep_panic hst
    change f.block? s.b = some B2 at hB2
    rw [hB] at hB2; cases hB2
    have hT := enter_panic S.two Bk hBR hA hs hfree hpan
    refine ⟨1, ?_⟩
    rw [runLoop_panic hst, runLoop_panic (blockStep_of_panic (ctx := Ctx.make tabs g) hBg hT)]
    exact .panicked_refl e m
  | ret rs m =>
    obtain ⟨B2, G, hB2, -, hterm⟩ := blockStep_ret hst
    change f.block? s.b = some B2 at hB2
    rw [hB] at hB2; cases hB2
    obtain ⟨_, _, -, -, h⟩ := stepTerm_if hk hc hterm
    cases h
  | goto G e =>
    obtain ⟨B2, hB2, hG, hterm⟩ := blockStep_goto hst
    change f.block? s.b = some B2 at hB2
    rw [hB] at hB2; cases hB2
    obtain ⟨GT, hGT, hAG, hGs⟩ := enter_ok S.two Bk hBR hA hs hfree hG
    have htermT : stepTerm GT Bg = .ok (.goto (s.rmE f s.e1)) := by
      unfold stepTerm; rw [hkg]; unfold succ; rw [hsug]; rfl
    have hTb : blockStep env (Ctx.make tabs g) frT s.b iS = .goto GT (s.rmE f s.e1) := by
      rw [blockStep_of (ctx := Ctx.make tabs g) hBg hGT, htermT]
    obtain ⟨bv, e', -, he', hee⟩ := stepTerm_if hk hc hterm
    cases hee
    obtain ⟨hdiB, -, -⟩ := dinv_enter_rel S.wf S.domR hb hB hs hdi hG
    rw [runLoop_goto hst] at hd ⊢
    cases bv with
    | false =>
      rw [hsu] at he'
      have hee : e = s.e1 := by simpa using he'.symm
      subst hee
      obtain ⟨hne, hnd⟩ := S.succ_ok hb hB (k := 1) (e := s.e1) (by rw [hsu]; rfl)
        (.inr (by decide)) hna
      obtain ⟨hdi', ht', hGs', hem⟩ := S.dinv_step hb hB ht hs hdi hG (e := s.e1)
        (by rw [hsu]; simp)
      rw [rmE_eq] at hTb
      exact refines_goto hTb (ih n (Nat.le_refl n) _ _ _ _ _ _
        ⟨rfl, hem, hnd, .inl ⟨hne, rfl⟩, ht', hGs', hdi', hAG⟩ hd)
    | true =>
      rw [hsu] at he'
      have hee : e = s.e0 := by simpa using he'.symm
      subst hee
      obtain ⟨GT2, hAG2, hlift⟩ := S.side1_target hAG hGs hdiB ht
      refine refines_goto hTb (hlift _ _ ?_)
      have hs0 := S.rel.side0
      obtain ⟨hdi0, ht0, hGs0, hem0⟩ := S.dinv_step hb hB ht hs hdi hG (e := s.e0)
        (by rw [hsu]; simp)
      cases ha0 : s.arm0 with
      | none =>
        rw [ha0] at hs0
        have he0 := direct_spec hs0
        rw [he0] at hd hdi0 ht0 hem0 ⊢
        have hnd0 : ¬ (s.unlinked f = true ∧ s.arm0 = some s.ss) := fun ⟨hu, _⟩ => by
          unfold Site.unlinked at hu; rw [ha0] at hu; cases hu
        exact ih n (Nat.le_refl n) _ _ _ _ _ _ ⟨rfl, hem0, hnd0,
          .inr ⟨rfl, rfl, rfl⟩, ht0, hGs0, hdi0, hAG2⟩ hd
      | some a0 =>
        rw [ha0] at hs0
        obtain ⟨he0, -, ha0ss, A0, hA0, hk0, hsu0, hsafe0⟩ := arm_spec hs0
        have ha0m := S.arm0_mem ha0
        rw [he0] at hd hdi0 ht0 ⊢
        cases n with
        | zero => exact absurd hd runLoop_zero_not_defined
        | succ m =>
        cases hst2 : blockStep env (Ctx.make tabs f) G a0 s.e0.i with
        | stuck => exact absurd hd (runLoop_stuck hst2)
        | panic e2 m2 =>
          exfalso
          obtain ⟨A2, hA2, hpan⟩ := blockStep_panic hst2
          change f.block? a0 = some A2 at hA2
          rw [hA0] at hA2; cases hA2
          obtain ⟨-, -, -, r, -, -, -, -, -, -, -, -, -, -, -, -, hr, rv, hrv, -, hrp⟩ :=
            enter_panic_facts (tabs := tabs) S.wf ha0m hA0 hGs0 hpan
          obtain ⟨v, hv, hsafe⟩ := hsafe0 _ hr
          rw [hrv] at hv; cases hv
          exact specSafe_not_panicking hsafe hrp
        | ret rs m2 =>
          obtain ⟨A2, G2, hA2, -, hterm2⟩ := blockStep_ret hst2
          change f.block? a0 = some A2 at hA2
          rw [hA0] at hA2; cases hA2
          obtain ⟨_, -, h⟩ := stepTerm_plain hk0 hterm2
          cases h
        | goto G2 e2 =>
          obtain ⟨A2, hA2, hG2, hterm2⟩ := blockStep_goto hst2
          change f.block? a0 = some A2 at hA2
          rw [hA0] at hA2; cases hA2
          obtain ⟨e3, he3, hee3⟩ := stepTerm_plain hk0 hterm2
          cases hee3
          rw [hsu0] at he3
          have he2 : e2 = ⟨s.ss, s.j0⟩ := by simpa using he3.symm
          subst he2
          obtain ⟨g1, g2, g3, -⟩ := enter_ok_facts (tabs := tabs) S.wf ha0m hA0 hGs0 hG2
          obtain ⟨hdi2, ht2, hGs2, hem2⟩ := S.dinv_step ha0m hA0 ht0 hGs0 hdi0 hG2
            (e := ⟨s.ss, s.j0⟩) (by rw [hsu0]; simp)
          have hX0 : ∀ x ∈ A0.values, s.inX f R x = true := by
            intro x hx
            unfold Site.inX Site.armVal
            simp [ha0, valsOf_eq hA0, hx]
          have hAG3 : Agr (s.inX f R) G2 GT2 := by
            refine ⟨hAG2.1.trans (with_regs g1 _).symm, by rw [hAG2.2.1, g2], fun a haX => ?_⟩
            have hna : a ∉ A0.values := fun hm => by rw [hX0 a hm] at haX; cases haX
            rw [hAG2.2.2 a haX, g3 a hna]
          rw [runLoop_goto hst2] at hd ⊢
          have hnd2 : ¬ (s.unlinked f = true ∧ s.arm0 = some s.ss) := fun ⟨_, ha⟩ => by
            rw [ha0] at ha; cases ha; exact ha0ss rfl
          exact ih m (by omega) _ _ _ _ _ _ ⟨rfl, hem2, hnd2,
            .inr ⟨rfl, rfl, rfl⟩, ht2, hGs2, hdi2, hAG3⟩ hd

/-- **One step of the simulation.** -/
theorem sim_step {tabs : Tables} {env : Env} (n : Nat)
    (ih : SimUpTo env (Ctx.make tabs f) (Ctx.make tabs g) (Rel env tabs f s R) n)
    {frS frT : Frame} {bS iS bT iT : Nat} (hR : Rel env tabs f s R frS bS iS frT bT iT)
    (hd : (runLoop env (Ctx.make tabs f) (n + 1) frS bS iS).Defined) :
    ∃ fuelT, LoopRefines Eq (runLoop env (Ctx.make tabs f) (n + 1) frS bS iS)
      (runLoop env (Ctx.make tabs g) fuelT frT bT iT) := by
  by_cases hb : bS = s.b
  · subst hb; exact S.b_step ih hR hd
  · exact S.normal_step ih hR hb hd

/-- **One checked `fuseBlockIf` rewrite refines.** -/
theorem refines_of_step {tabs : Tables} : Refines tabs g tabs f := by
  intro env args mem fuel hd
  unfold GoFV.SSA.run runCtx at hd ⊢
  rw [Dead.params_eq S.rel.ownAux]
  split
  · rename_i hn; simp only [hn] at hd; exact hd.elim
  · rename_i hn
    simp only [hn] at hd
    have hentry : entryFrame env (Ctx.make tabs g) args mem =
        entryFrame env (Ctx.make tabs f) args mem := by
      unfold entryFrame frameMem frameAllocs
      rw [show (Ctx.make tabs g).f.valueTab.size = (Ctx.make tabs f).f.valueTab.size from
        S.rel.vsize]
      simp only [Ctx.make, abiParams, S.rel.ownAux]
    have houts : (Ctx.make tabs g).outs = (Ctx.make tabs f).outs := by
      simp only [Ctx.make, abiParams, S.rel.ownAux]
    rw [hentry, houts, show (Ctx.make tabs g).act = (Ctx.make tabs f).act from rfl,
      show (Ctx.make tabs g).f.entry = f.entry from S.rel.entry]
    obtain ⟨E, hE, -⟩ := S.wf.blockId f.entry S.wf.entry
    have hE0 := S.wf.entryPreds E hE
    have hR0 : Rel env tabs f s R (entryFrame env (Ctx.make tabs f) args mem) f.entry 0
        (entryFrame env (Ctx.make tabs f) args mem) f.entry 0 := by
      have hne : f.entry ≠ s.rmT f := fun h => by
        obtain ⟨C, hC, hsrc⟩ := S.rm_src
        rw [← h, hE] at hC; cases hC
        rw [Array.getElem?_eq_none (by omega)] at hsrc
        rcases hsrc with h' | ⟨_, -, -, h'⟩ <;> cases h'
      refine ⟨rfl, S.wf.entry, fun ⟨hu, ha⟩ => ?_, .inl ⟨.inl hne, by unfold tIdx; rw [if_neg hne]⟩,
        S.domR.entry, by simp [Ctx.make, entryFrame], dinv_entry_rel S.domR _, rfl, rfl,
        fun _ _ => rfl⟩
      unfold Site.unlinked at hu
      rw [ha] at hu
      simp only [hE, Option.map_some, Option.some_beq_some, beq_iff_eq] at hu
      rw [hu] at hE0; simp at hE0
    obtain ⟨fuelT, h⟩ := runLoop_simIH (Rel env tabs f s R)
      (fun n ih _ _ _ _ _ _ hR hd' => S.sim_step n ih hR hd') fuel _ _ _ _ _ _ hR0
      (finish_defined hd)
    exact ⟨fuelT, finish_refines hd h⟩

end Setup

end GoFV.Proof.FuseIf
