import GoFV.Proof.Pass.FusePlainPanic

/-!
# One checked `fuseBlockPlain` rewrite refines

`refines_of_step`: if `g` is `f` with the run `b0 … c` fused (`Setup f g run b0 c`), every run
of `f` is a run of `g`. Macro-step simulation (`runLoop_simIH`): outside the run both functions
step alike, edges into `b0` going to `c` in `g` (`normal_step`); at `b0` the source runs the
blocks of the run one after the other (`chain`, the frames related by `Acc`) while the target
runs the fused block once (`merged_ok`, `merged_panic`). The relation `R`: the same frame, the
same block (`c` for `b0`), never a later block of the run, and lemma (D) for the source's frame
at the entry of a tree block.
-/

namespace GoFV.Proof.FusePlain

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.Fuse GoFV.Opt.Fuse.Plain
  GoFV.Proof Dom

/-- A terminator with the same kind and controls and redirected successors. -/
theorem stepTerm_redirect {G : Frame} {B B' : Block} (hk : B'.kind = B.kind)
    (hc : B'.controls = B.controls) {r : Edge → Edge} (hsu : B'.succs = B.succs.map r) :
    (∀ e, stepTerm G B = .ok (.goto e) → stepTerm G B' = .ok (.goto (r e))) ∧
    (∀ rs m, stepTerm G B = .ok (.ret rs m) → stepTerm G B' = .ok (.ret rs m)) := by
  refine ⟨fun e h => ?_, fun rs m h => ?_⟩
  · rcases Dead.stepTerm_rel (.inl hk) hc (fun _ _ => rfl) h with ⟨k, e', he, hk', -, hst⟩ |
      ⟨rs, m, he, -⟩
    · cases he
      rw [hst]; unfold succ; rw [hsu, Array.getElem?_map, hk']; rfl
    · cases he
  · rcases Dead.stepTerm_rel (.inl hk) hc (fun _ _ => rfl) h with ⟨k, e', he, -, -, -⟩ |
      ⟨rs', m', he, hst⟩
    · cases he
    · cases he; exact hst

theorem redirect_b {b0 c : ID} {e : Edge} :
    (redirect b0 c e).b = if e.b = b0 then c else e.b := by
  unfold redirect; by_cases h : e.b = b0 <;> simp [h]

theorem redirect_i {b0 c : ID} {e : Edge} : (redirect b0 c e).i = e.i := by
  unfold redirect; split <;> rfl

variable {f g : Func} {run : List ID} {b0 c : ID}

/-- The simulation relation (see the module doc). -/
def R (env : Env) (tabs : Tables) (f : Func) (run : List ID) (b0 c : ID) (frS : Frame)
    (bS iS : Nat) (frT : Frame) (bT iT : Nat) : Prop :=
  frT = frS ∧ iT = iS ∧ bT = (if bS = b0 then c else bS) ∧ bS ∈ f.blocks ∧ bS ∉ run.tail ∧
    Reachable f bS ∧ frS.regs.size = f.valueTab.size ∧
    DInv env (Ctx.make tabs f) (fun a => SDom f a bS ∧ a ≠ bS) frS

namespace Setup

variable (S : Setup f g run b0 c)
include S

/-- Lemma (D) and the tree along a source block step. -/
theorem dinv_step {env : Env} {tabs : Tables} {b : ID} (hb : b ∈ f.blocks) {B : Block}
    (hB : f.block? b = some B) (ht : Reachable f b) {fr G : Frame} {i : Nat}
    (hs : fr.regs.size = f.valueTab.size)
    (hdi : DInv env (Ctx.make tabs f) (fun a => SDom f a b ∧ a ≠ b) fr)
    (h : enterBlock env (Ctx.make tabs f) fr B i = .ok G) {e : Edge} (he : e ∈ B.succs) :
    DInv env (Ctx.make tabs f) (fun a => SDom f a e.b ∧ a ≠ e.b) G ∧
      Reachable f e.b ∧ G.regs.size = f.valueTab.size ∧ e.b ∈ f.blocks := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨h1, h2, h3⟩ := dinv_enter_rel hwf S.dom hb hB hs hdi h
  obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 he
  exact ⟨dinv_edge_rel S.dom hb hB ht he h1, (S.dom.edge hb hB ht he).1, by rw [h3, hs],
    (hwf.succLink b B ⟨hb, hB⟩ k e hk).1⟩

/-- An edge into a later block of the run comes from the block before it. -/
theorem succ_later {b : ID} (hb : b ∈ f.blocks) {B : Block} (hB : f.block? b = some B)
    {e : Edge} (he : e ∈ B.succs) (hy : e.b ∈ run.tail) :
    ∃ pre suf, run = pre ++ b :: e.b :: suf := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨rest, hrest⟩ := S.rel.run_cons
  rw [hrest, List.tail_cons] at hy
  obtain ⟨p, s, hp⟩ := List.append_of_mem hy
  have hne : b0 :: p ≠ [] := List.cons_ne_nil _ _
  obtain ⟨q, x, hq⟩ : ∃ q x, b0 :: p = q ++ [x] :=
    ⟨(b0 :: p).dropLast, (b0 :: p).getLast hne, (List.dropLast_concat_getLast hne).symm⟩
  have hr : run = q ++ x :: e.b :: s := by
    rw [hrest, hp, ← List.cons_append, hq]; simp
  obtain ⟨X, Y, hX, hY, -, -, hpr⟩ := S.rel.link hr
  obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 he
  obtain ⟨-, C, hC, hci⟩ := hwf.succLink b B ⟨hb, hB⟩ k e hk
  rw [hY] at hC; cases hC
  rw [hpr] at hci
  have h0 : e.i = 0 := by
    rcases Nat.lt_or_ge e.i 1 with h' | h'
    · omega
    · rw [Array.getElem?_eq_none (by simpa using h')] at hci; cases hci
  rw [h0] at hci
  simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq, Edge.mk.injEq] at hci
  rw [hci.1] at hr
  exact ⟨q, s, hr⟩

/-- The value types are unchanged. -/
theorem tys_eq {tabs : Tables} (id : ID) :
    (Ctx.make tabs g).tys[id]? = (Ctx.make tabs f).tys[id]? := by
  obtain ⟨hsem, hv⟩ := S.rel.value_same id
  cases hf : f.value? id with
  | some fv =>
    obtain ⟨gv, hgv, hty, -⟩ := hv fv hf
    rw [tys_of_value hf, tys_of_value hgv, hty]
  | none =>
    rw [hf] at hsem
    cases hg : g.value? id with
    | some _ => rw [hg] at hsem; exact hsem.elim
    | none =>
      unfold Func.value? at hf hg
      simp only [Ctx.make, Array.getElem?_map]
      have hsz := S.gsize
      rcases Nat.lt_or_ge id f.valueTab.size with hlt | hge
      · rw [Array.getElem?_eq_getElem hlt] at hf ⊢
        rw [Array.getElem?_eq_getElem (hsz ▸ hlt)] at hg ⊢
        simp only [Option.join_some] at hf hg
        simp only [Option.map_some, hf, hg]
      · rw [Array.getElem?_eq_none hge, Array.getElem?_eq_none (by omega)]

/-- A block of `f` outside the run steps alike in `g`, edges into `b0` going to `c`. -/
theorem normal_step {tabs : Tables} {env : Env} {fr : Frame} {b : ID} {i : Nat}
    (hb : b ∈ f.blocks) (hn : b ∉ run) :
    (∀ G e, blockStep env (Ctx.make tabs f) fr b i = .goto G e →
      blockStep env (Ctx.make tabs g) fr b i = .goto G (redirect b0 c e)) ∧
    (∀ rs m, blockStep env (Ctx.make tabs f) fr b i = .ret rs m →
      blockStep env (Ctx.make tabs g) fr b i = .ret rs m) ∧
    (∀ e m, blockStep env (Ctx.make tabs f) fr b i = .panic e m →
      blockStep env (Ctx.make tabs g) fr b i = .panic e m) := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨fb, gb, hfb, hgb, hid, hvals, hk, hc, hsu⟩ := S.rel.block_out hwf hb hn
  have hown := valuesOwn hwf hb hfb
  have hidv : ∀ x ∈ fb.values, ∀ fv, f.value? x = some fv → fv.id = x := fun x hx fv hfv => by
    obtain ⟨v, hv, hvid⟩ := hown x hx
    rw [hfv] at hv; cases hv; exact hvid
  have hca : ∀ l : List ID, CtxAgree (Ctx.make tabs f) (Ctx.make tabs g) l := fun l =>
    ⟨fun x _ => (S.rel.value_same x).1, fun _ _ v _ => S.tys_eq v.id, rfl, S.params_eq, rfl⟩
  have hba : BlockAgree fb { gb with succs := fb.succs } := ⟨hid, hvals, hk, hc, rfl⟩
  have hgen : ∀ G, enterBlock env (Ctx.make tabs g) G { gb with succs := fb.succs } i =
      enterBlock env (Ctx.make tabs g) G gb i := fun G => by
    rw [enterBlock_eq, enterBlock_eq]
  have hsched : schedule g gb = schedule f fb := by
    unfold schedule
    rw [show schedNodes g gb = schedNodes f fb from
      schedNodes_semEq hvals fun x _ => (S.rel.value_same x).1]
  obtain ⟨b', hb', hbid⟩ := hwf.blockId b hb
  rw [hfb] at hb'; cases hb'
  have hE := enterBlock_agree (env := env) (i := i) (X := fun _ => False) (frS := fr) (frT := fr)
    hba (hca _) hidv (fun _ _ _ _ _ _ _ h => h)
    (by rw [hbid, sched_of_block hgb, sched_of_block hfb, hsched])
    (fun _ _ => ⟨hca _, fun _ _ => ⟨id, fun _ _ _ _ => id⟩⟩) rfl rfl (fun _ _ => rfl)
  simp only [hgen] at hE
  have hsT := fun G => stepTerm_redirect (G := G) (r := redirect b0 c) hk hc hsu
  unfold blockStep
  simp only [show (Ctx.make tabs f).f = f from rfl, show (Ctx.make tabs g).f = g from rfl, hfb, hgb]
  cases hen : enterBlock env (Ctx.make tabs f) fr fb i with
  | stuck msg => exact ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h), fun _ _ h => (nomatch h)⟩
  | panic e' m' =>
    rw [hE.2 _ _ hen]
    exact ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h), fun _ _ h => h⟩
  | ok G1 =>
    obtain ⟨GT1, hT1, hfr1, -, hag1⟩ := hE.1 G1 hen
    rw [show GT1 = G1 from frame_eq hfr1 fun z => hag1 z id] at hT1
    rw [hT1]
    simp only
    cases hs : stepTerm G1 fb with
    | ok n =>
      cases n with
      | goto e =>
        rw [(hsT G1).1 e hs]
        exact ⟨fun G e' h => by cases h; rfl, fun _ _ h => (nomatch h), fun _ _ h => (nomatch h)⟩
      | ret rs m =>
        rw [(hsT G1).2 rs m hs]
        exact ⟨fun _ _ h => (nomatch h), fun _ _ h => h, fun _ _ h => (nomatch h)⟩
    | panic e m => exact absurd hs CopyElim.stepTerm_not_panic
    | stuck msg => exact ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h), fun _ _ h => (nomatch h)⟩

/-- The block at the end of the run is `c`. -/
theorem last_eq {pre : List ID} {y : ID} (hr : run = pre ++ [y]) : y = c := by
  have hl := S.rel.last
  rw [hr, List.getLast?_concat] at hl
  exact Option.some.inj hl

/-- The relation after the source left `c` (or a block outside the run) along `e`. -/
theorem R_after {env : Env} {tabs : Tables} {b : ID} (hb : b ∈ f.blocks) {B : Block}
    (hB : f.block? b = some B) (ht : Reachable f b) {fr G : Frame} {i : Nat}
    (hs : fr.regs.size = f.valueTab.size)
    (hdi : DInv env (Ctx.make tabs f) (fun a => SDom f a b ∧ a ≠ b) fr)
    (h : enterBlock env (Ctx.make tabs f) fr B i = .ok G) {e : Edge} (he : e ∈ B.succs)
    (hn : e.b ∉ run.tail) :
    R env tabs f run b0 c G e.b e.i G (redirect b0 c e).b (redirect b0 c e).i := by
  obtain ⟨h1, h2, h3, h4⟩ := S.dinv_step hb hB ht hs hdi h he
  exact ⟨rfl, redirect_i, redirect_b, h4, hn, h2, h3, h1⟩

/-- **Along the run**: the source runs the blocks of the run from `y` on, from the frame `G`
it reached after the blocks `pre`; the target runs `c` once from `fr`. -/
theorem chain {tabs : Tables} {env : Env} {n : Nat}
    (ih : SimUpTo env (Ctx.make tabs f) (Ctx.make tabs g) (R env tabs f run b0 c) n)
    {fr : Frame} {i : Nat} (hfs : fr.regs.size = f.valueTab.size)
    (htd : Reachable f b0)
    (hdi : DInv env (Ctx.make tabs f) (fun a => SDom f a b0 ∧ a ≠ b0) fr) :
    ∀ (suf pre : List ID) (y : ID) (G : Frame) (idx m : Nat), run = pre ++ y :: suf →
      (pre = [] → y = b0 ∧ idx = i) → Acc env tabs f fr i b0 pre G →
      DInv env (Ctx.make tabs f) (fun a => SDom f a y ∧ a ≠ y) G →
      Reachable f y → G.regs.size = f.valueTab.size → m ≤ n + 1 →
      (runLoop env (Ctx.make tabs f) m G y idx).Defined →
      ∃ fuelT, LoopRefines Eq (runLoop env (Ctx.make tabs f) m G y idx)
        (runLoop env (Ctx.make tabs g) fuelT fr c i) := by
  intro suf
  induction suf with
  | nil =>
    intro pre y G idx m hr hfirst hA hdy hty hGs hm hd
    have hyc := S.last_eq hr
    subst hyc
    have hyIn : y ∈ f.blocks := S.runIn (by rw [hr]; simp)
    obtain ⟨C, C', oT, hC, hC', -, -, hkC, hcC, hsuC, -⟩ := S.rel.merged
    cases m with
    | zero => exact absurd hd runLoop_zero_not_defined
    | succ m' =>
    cases hst : blockStep env (Ctx.make tabs f) G y idx with
    | stuck => exact absurd hd (runLoop_stuck hst)
    | panic e mm =>
      obtain ⟨Y, hY, hpan⟩ := blockStep_panic hst
      obtain ⟨C2, hC2, hT⟩ := S.merged_panic hr hfs htd hdi hA hfirst hY hpan
      refine ⟨1, ?_⟩
      rw [runLoop_panic hst, runLoop_panic (blockStep_of_panic (ctx := Ctx.make tabs g) hC2 hT)]
      exact .panicked_refl e mm
    | ret rs mm =>
      obtain ⟨Y, G', hY, hG', hterm⟩ := blockStep_ret hst
      change f.block? y = some Y at hY
      rw [hC] at hY; cases hY
      have hA' := S.acc_step hr hfs hA hfirst hC hG'
      rw [← hr] at hA'
      obtain ⟨C2, hC2, hT⟩ := S.merged_ok hfs hA'
      rw [hC'] at hC2; cases hC2
      have hterm' := (stepTerm_redirect (G := G') hkC hcC hsuC).2 rs mm hterm
      refine ⟨1, ?_⟩
      rw [runLoop_ret hst, runLoop_ret (ctx := Ctx.make tabs g) (by
        rw [blockStep_of (ctx := Ctx.make tabs g) hC' hT, hterm'])]
      exact .returned (RefinesList.refl rs) (Mem.Refines.refl _)
    | goto G' e =>
      obtain ⟨Y, hY, hG', hterm⟩ := blockStep_goto hst
      change f.block? y = some Y at hY
      rw [hC] at hY; cases hY
      have hA' := S.acc_step hr hfs hA hfirst hC hG'
      rw [← hr] at hA'
      obtain ⟨C2, hC2, hT⟩ := S.merged_ok hfs hA'
      rw [hC'] at hC2; cases hC2
      have hterm' := (stepTerm_redirect (G := G') hkC hcC hsuC).1 e hterm
      have he := stepTerm_goto_mem hterm
      have hT' : blockStep env (Ctx.make tabs g) fr y i = .goto G' (redirect b0 y e) := by
        rw [blockStep_of (ctx := Ctx.make tabs g) hC' hT, hterm']
      have hnt : e.b ∉ run.tail := fun hy => by
        obtain ⟨p, s, hps⟩ := S.succ_later hyIn hC he hy
        exact List.cons_ne_nil _ _ (S.rel.c_last hps)
      rw [runLoop_goto hst] at hd ⊢
      exact refines_goto hT' (ih m' (by omega) _ _ _ _ _ _
        (S.R_after hyIn hC hty hGs hdy hG' he hnt) hd)
  | cons y' suf IH =>
    intro pre y G idx m hr hfirst hA hdy hty hGs hm hd
    have hyIn : y ∈ f.blocks := S.runIn (by rw [hr]; simp)
    obtain ⟨Y, Y', hY, hY', hkY, hsuY, -⟩ := S.rel.link hr
    cases m with
    | zero => exact absurd hd runLoop_zero_not_defined
    | succ m' =>
    cases hst : blockStep env (Ctx.make tabs f) G y idx with
    | stuck => exact absurd hd (runLoop_stuck hst)
    | panic e mm =>
      obtain ⟨Y2, hY2, hpan⟩ := blockStep_panic hst
      obtain ⟨C2, hC2, hT⟩ := S.merged_panic hr hfs htd hdi hA hfirst hY2 hpan
      refine ⟨1, ?_⟩
      rw [runLoop_panic hst, runLoop_panic (blockStep_of_panic (ctx := Ctx.make tabs g) hC2 hT)]
      exact .panicked_refl e mm
    | ret rs mm =>
      obtain ⟨Y2, G', hY2, -, hterm⟩ := blockStep_ret hst
      change f.block? y = some Y2 at hY2
      rw [hY] at hY2; cases hY2
      obtain ⟨e', -, he'⟩ := stepTerm_plain hkY hterm
      cases he'
    | goto G' e =>
      obtain ⟨Y2, hY2, hG', hterm⟩ := blockStep_goto hst
      change f.block? y = some Y2 at hY2
      rw [hY] at hY2; cases hY2
      obtain ⟨e', he1, he2⟩ := stepTerm_plain hkY hterm
      cases he2
      rw [hsuY] at he1; simp at he1; subst he1
      have hA' := S.acc_step hr hfs hA hfirst hY hG'
      obtain ⟨hdi', hty', hGs', -⟩ := S.dinv_step hyIn hY hty hGs hdy hG' (e := ⟨y', 0⟩)
        (by rw [hsuY]; simp)
      rw [runLoop_goto hst] at hd ⊢
      exact IH (pre ++ [y]) y' G' 0 m' (by rw [hr]; simp) (fun h => by simp at h) hA' hdi' hty'
        hGs' (by omega) hd

/-- **One step of the simulation** (macro step at `b0`). -/
theorem sim_step {tabs : Tables} {env : Env} (n : Nat)
    (ih : SimUpTo env (Ctx.make tabs f) (Ctx.make tabs g) (R env tabs f run b0 c) n)
    {frS frT : Frame} {bS iS bT iT : Nat} (hR : R env tabs f run b0 c frS bS iS frT bT iT)
    (hd : (runLoop env (Ctx.make tabs f) (n + 1) frS bS iS).Defined) :
    ∃ fuelT, LoopRefines Eq (runLoop env (Ctx.make tabs f) (n + 1) frS bS iS)
      (runLoop env (Ctx.make tabs g) fuelT frT bT iT) := by
  obtain ⟨hfT, hiT, hbT, hb, hnt, ht, hs, hdi⟩ := hR
  rw [hfT, hiT, hbT]
  obtain ⟨rest, hrest⟩ := S.rel.run_cons
  by_cases hb0 : bS = b0
  · subst hb0
    simp only [ite_true]
    exact S.chain ih hs ht hdi rest [] bS frS iS (n + 1) (by rw [hrest]; rfl)
      (fun _ => ⟨rfl, rfl⟩) acc_nil hdi ht hs (Nat.le_refl _) hd
  · simp only [hb0, ite_false]
    have hn : bS ∉ run := fun hm => by
      rw [hrest] at hm hnt
      rcases List.mem_cons.1 hm with h | h
      · exact hb0 h
      · exact hnt h
    obtain ⟨hgo, hret, hpan⟩ := S.normal_step (tabs := tabs) (env := env) (fr := frS) (i := iS) hb hn
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
      obtain ⟨B, hB, hG, hterm⟩ := blockStep_goto hst
      change f.block? bS = some B at hB
      have he := stepTerm_goto_mem hterm
      have hnt' : e.b ∉ run.tail := fun hy => by
        obtain ⟨p, s, hps⟩ := S.succ_later hb hB he hy
        exact hn (by rw [hps]; simp)
      rw [runLoop_goto hst] at hd ⊢
      exact refines_goto (hgo G e hst) (ih n (Nat.le_refl n) _ _ _ _ _ _
        (S.R_after hb hB ht hs hdi hG he hnt') hd)

/-- **One checked `fuseBlockPlain` rewrite refines.** -/
theorem refines_of_step {tabs : Tables} : Refines tabs g tabs f := by
  obtain ⟨ce, hwf⟩ := S.wf
  have hgsz := S.gsize
  have hown : g.ownAux = f.ownAux := S.rel.parts.2.2.2.2.2.2.2.2.1
  intro env args mem fuel hd
  unfold GoFV.SSA.run runCtx at hd ⊢
  rw [S.params_eq]
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
    rw [hentry, houts, show (Ctx.make tabs g).act = (Ctx.make tabs f).act from rfl]
    have hE := hwf.entry
    have hent : (Ctx.make tabs g).f.entry = if f.entry = b0 then c else f.entry := by
      show g.entry = _
      by_cases h : f.entry = b0
      · simp only [h, ↓reduceIte]; exact S.rel.entry.1 h
      · simp only [h, ↓reduceIte]; exact S.rel.entry.2 h
    rw [hent]
    have hR0 : R env tabs f run b0 c (entryFrame env (Ctx.make tabs f) args mem) f.entry 0
        (entryFrame env (Ctx.make tabs f) args mem) (if f.entry = b0 then c else f.entry) 0 := by
      refine ⟨rfl, rfl, rfl, hE, fun hm => ?_, S.dom.entry,
        by simp [Ctx.make, entryFrame], dinv_entry_rel S.dom _⟩
      obtain ⟨rest, hrest⟩ := S.rel.run_cons
      rw [hrest, List.tail_cons] at hm
      obtain ⟨p, s, hps⟩ := List.append_of_mem hm
      exact (S.rel.later (pre := b0 :: p) (suf := s) (by rw [hrest, hps]; rfl)
        (List.cons_ne_nil _ _)).1 rfl
    obtain ⟨fuelT, h⟩ := runLoop_simIH (R env tabs f run b0 c) (fun n ih _ _ _ _ _ _ hR hd' =>
      S.sim_step n ih hR hd') fuel _ _ _ _ _ _ hR0 (finish_defined hd)
    exact ⟨fuelT, finish_refines hd h⟩

end Setup

end GoFV.Proof.FusePlain
