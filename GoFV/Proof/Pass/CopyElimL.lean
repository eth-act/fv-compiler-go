import GoFV.Proof.Pass.CopyElimEnterL
import GoFV.Proof.Pass.CopyElim
import GoFV.Proof.Pass.DeadRelL

/-!
# copyelim refines its input on `runL`

`refinesL_of_rel`: two checked functions related by `CopyRel`, with the input in the fragment
`EmptyFrag`, lowered alike, and in the fragment `CopyLFrag`, run alike under `runL`: lock-step
simulation (`runLoopL_sim`) with equal frames and the invariant `AtL` at every block entry
(`enterL_ok`, `enterL_panic`, `stepTermL_copyRel`). The terminator of an arm64 block reads its
`auxInt` and its control (`stepTermL`), which `CopyRel` and `CopyLFrag.auxInt` keep; it never
panics and jumps along its successors (`Dead.stepTermL_not_panic`, `Dead.stepTermL_goto_mem`).
-/

namespace GoFV.Proof.CopyElim

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt Dom

variable {md : LMode} {tabs : Tables} {f g : Func}

/-! ## Terminators -/

/-- An arm64 or generic terminator of a block whose controls hold related registers. -/
theorem stepTermL_copyRel {fr : Frame} {b b' : Block} (hk : b'.kind = b.kind)
    (hs : b'.succs = b.succs) (hid : b'.id = b.id) (haux : b'.auxInt = b.auxInt)
    (hc : ∀ (k : Nat) (c : ID) (y : Val), b.controls[k]? = some c →
      fr.regs[c]? = some (some y) → ∃ c', b'.controls[k]? = some c' ∧ fr.regs[c']? = some (some y))
    {n : Next} (h : stepTermL fr b = .ok n) : stepTermL fr b' = .ok n := by
  have hsucc : ∀ k, succ b' k = succ b k := fun k => by unfold succ; rw [hs, hid]
  unfold stepTermL at h ⊢
  rw [hk]
  by_cases harm : b.kind.isArm64 = true
  · simp only [harm, ↓reduceIte] at h ⊢
    cases hc0 : Sem.control fr b 0 with
    | ok v =>
      rw [control_rel hc hc0]
      rw [hc0] at h
      simp only [hsucc, haux, hid]
      exact h
    | panic e m => rw [hc0] at h; split at h <;> cases h
    | stuck msg => rw [hc0] at h; split at h <;> cases h
  · simp only [harm, Bool.false_eq_true, ↓reduceIte] at h ⊢
    exact stepTerm_rel hk hs hid hc h

/-! ## The block step -/

/-- The simulation relation: equal frames, the invariant `AtL`. -/
def RL (md : LMode) (env : Env) (tabs : Tables) (f g : Func) (frS frT : Frame) (bid : ID)
    (i : Nat) : Prop :=
  frT = frS ∧ AtL md env tabs f g frS bid i

/-- **One block step of copyelim's simulation on `runL`.** -/
theorem stepL (S : SetupL md tabs f g) {env : Env} {fr : Frame} {bid : ID} {i : Nat}
    (hA : AtL md env tabs f g fr bid i) :
    StepSim (RL md env tabs f g) (blockStepL md env (Ctx.makeL tabs f) fr bid i)
      (blockStepL md env (Ctx.makeL tabs g) fr bid i) := by
  obtain ⟨ce, hwf⟩ := S.base.wf
  obtain ⟨ce', hwg⟩ := S.base.wg
  have hbt := hA.tree S
  unfold blockStepL
  simp only [makeL_f]
  cases hfb : f.block? bid with
  | none => exact True.intro
  | some fb =>
  simp only
  cases hen : enterBlockL md env (Ctx.makeL tabs f) fr fb i with
  | panic e m =>
    obtain ⟨gb, hgbb, hT⟩ := enterL_panic S hA hfb hen
    rw [hgbb]; simp only [hT]; rfl
  | stuck msg => exact True.intro
  | ok G =>
  obtain ⟨gb, hgbb, hT⟩ := enterL_ok S hA hfb hen
  obtain ⟨gb', hgbb', hgid, hsucc, -, hkind, hvals, -, hctl⟩ := S.base.block hbt hfb
  rw [hgbb] at hgbb'; cases hgbb'
  rw [hgbb]
  simp only [hT]
  -- the source's frame after the block, as a `MidL`
  obtain ⟨fb', hfb', hfid⟩ := hwf.blockId bid hbt.1
  rw [hfb] at hfb'; cases hfb'
  have hen' := hen
  rw [enterBlockL_eq] at hen'
  cases hpsS : fb.values.toList.filterMapM (phiStepL md (Ctx.makeL tabs f) fr i) with
  | panic e m => rw [hpsS] at hen'; cases hen'
  | stuck msg => rw [hpsS] at hen'; cases hen'
  | ok psS =>
  rw [hpsS] at hen'
  change (Res.ofOption _ ((Ctx.makeL tabs f).sched[fb.id]?).join).bind _ = _ at hen'
  rw [hfid, sched_of_blockL hfb] at hen'
  cases hsched : schedule f fb with
  | none => rw [hsched] at hen'; cases hen'
  | some oS =>
  rw [hsched] at hen'
  change evalAllL md env (Ctx.makeL tabs f) _ oS.toList = .ok G at hen'
  obtain ⟨hM, -, -⟩ := mid_ofL S hA hfb hpsS hsched (R := []) (by simp) hen'
  obtain ⟨-, -, omem⟩ := schedule_topo (valuesOwn hwf hbt.1 hfb)
    (hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩) hsched
  have hcs : ∀ (k : Nat) (c : ID) (y : Val), fb.controls[k]? = some c →
      G.regs[c]? = some (some y) → ∃ c', gb.controls[k]? = some c' ∧ G.regs[c']? = some (some y) := by
    intro k c y hc hy
    obtain ⟨c', hc', hr⟩ := hctl k c hc
    refine ⟨c', hc', ?_⟩
    rcases hr with rfl | ⟨u, hu, hop, hargs⟩
    · exact hy
    · have hcm : c ∈ fb.controls := Array.mem_of_getElem? hc
      have hcl : Listed f c := hwf.ctrlListed bid fb ⟨hbt.1, hfb⟩ c hcm
      have hcU := ctrlUse S.base.cf hbt.1 hfb hbt.2 hcm
      obtain ⟨y', h1, h2⟩ := copyEqL S hA hfb hM hcl hcU (fun hm => by
        by_cases hph : ∃ v, f.value? c = some v ∧ v.op = .Phi
        · exact .inl hph
        · obtain ⟨v, -, hv, -⟩ := S.base.value hbt hfb hm
          exact .inr (by simpa using (omem c).2 ⟨hm, v, hv, fun hp => hph ⟨v, hv, hp⟩⟩))
        hu hop hargs
      rw [hy] at h1; cases h1; exact h2
  -- frames after the block
  have hsz : fr.regs.size = f.valueTab.size := hA.size
  have hszG : fr.regs.size = g.valueTab.size := by rw [hsz, S.base.rel.vsize]
  have hbg : bid ∈ g.blocks := by rw [S.base.blocks]; exact hbt.1
  obtain ⟨hDS, -, hGs⟩ := dinvL_enter hwf S.base.cf hbt.1 hfb hsz (hA.upS S) hen
  have hupT : DInvL md env (Ctx.makeL tabs g) (fun a => Anc (make g) a bid ∧ a ≠ bid) fr := by
    rw [S.base.mk_eq]; exact hA.upT S
  obtain ⟨hDT, -, -⟩ := dinvL_enter hwg S.base.cg hbg hgbb hszG hupT hT
  rw [S.base.mk_eq] at hDT
  have hAt : ∀ e, e ∈ fb.succs → AtL md env tabs f g G e.b e.i := fun e he =>
    ⟨by rw [hGs, hsz], typedL_enter hwf hbt.1 hfb hsz hA.tyS hen,
      typedL_enter hwg hbg hgbb hszG hA.tyT hT,
      .inr ⟨bid, fb, hbt.1, hfb, hbt.2, by cases e; exact he, hDS, hDT⟩⟩
  have haux : gb.auxInt = fb.auxInt := S.frag.auxInt bid hbt fb gb hfb hgbb
  cases hst : stepTermL G fb with
  | ok n =>
    have hst' := stepTermL_copyRel hkind hsucc hgid haux hcs hst
    cases n with
    | goto e =>
      rw [hst']
      exact ⟨G, rfl, rfl, hAt e (Dead.stepTermL_goto_mem hst)⟩
    | ret rs m =>
      rw [hst']
      exact ⟨rs, rfl, RefinesList.refl rs⟩
  | panic e m => exact absurd hst Dead.stepTermL_not_panic
  | stuck msg => exact True.intro

/-! ## Refinement -/

private theorem defers_makeL_copy (tabs : Tables) (f : Func) :
    (Ctx.makeL tabs f).defers = (Ctx.make tabs f).defers := by
  unfold Ctx.makeL; split <;> rfl

/-- **copyelim's static relation gives refinement on `runL`**: `f` and `g` checked and related by
`CopyRel` with `f` in `EmptyFrag` (Phase 1's `Setup`), lowered alike, and in `CopyLFrag`. -/
theorem refinesL_of_rel (S : Setup tabs f g) (hlow : g.lowered = f.lowered)
    (hL : CopyLFrag tabs f g) : RefinesL tabs g tabs f := by
  have SL : SetupL ⟨f.lowered, false⟩ tabs f g := ⟨S, hlow, rfl, rfl, hL⟩
  intro env args mem fuel hd
  refine ⟨fuel, ?_⟩
  unfold runL runCtxL at hd ⊢
  rw [hlow]
  have hpar : (Ctx.makeL tabs g).params = (Ctx.makeL tabs f).params := by
    rw [params_makeL, params_makeL, S.params]
  rw [hpar]
  split
  · rename_i hn; simp only [hn] at hd; exact hd.elim
  · rename_i hn
    simp only [hn] at hd
    have hsz : (Ctx.make tabs g).f.valueTab.size = (Ctx.make tabs f).f.valueTab.size :=
      S.rel.vsize
    have hentry : entryFrame env (Ctx.makeL tabs g) args mem =
        entryFrame env (Ctx.makeL tabs f) args mem := by
      rw [entryFrame_makeL, entryFrame_makeL]
      unfold entryFrame frameMem frameAllocs
      rw [S.paramTys, S.locals, hsz]; rfl
    have hout : (Ctx.makeL tabs g).outs = (Ctx.makeL tabs f).outs := by
      rw [outs_makeL, outs_makeL, S.outs]
    have hdef : (Ctx.makeL tabs g).defers = (Ctx.makeL tabs f).defers := by
      rw [defers_makeL_copy, defers_makeL_copy]; rfl
    have hact : (Ctx.makeL tabs g).act = (Ctx.makeL tabs f).act := by
      rw [act_makeL, act_makeL]; rfl
    have hent : (Ctx.makeL tabs g).f.entry = (Ctx.makeL tabs f).f.entry := by
      rw [makeL_f, makeL_f]; exact S.entry
    rw [hentry, hout, hdef, hact, hent]
    exact finish_refines hd (runLoopL_sim (RL ⟨f.lowered, false⟩ env tabs f g)
      (fun frS frT bid i ⟨h1, h2⟩ => by subst h1; exact stepL SL h2) fuel _ _ _ _
      ⟨rfl, ⟨by simp [entryFrame, makeL_f], typedL_replicate _ _ _ _ rfl,
        typedL_replicate _ _ _ _ rfl, .inl (by rw [makeL_f])⟩⟩ (finish_defined hd))

end GoFV.Proof.CopyElim
