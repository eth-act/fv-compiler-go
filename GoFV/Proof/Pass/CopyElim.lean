import GoFV.Proof.Pass.CopyElimEnter

variable [GoFV.SSA.Sem.Addrs]

/-!
# copyelim refines its input

`refines_of_rel`: two checked functions related by `CopyRel`, with the input in the fragment
`EmptyFrag`, run alike: lock-step simulation (`runLoop_sim`) with equal frames, the invariant
`At` at every block entry (`enter_ok`, `enter_panic`, `stepTerm_rel`).
-/

namespace GoFV.Proof.CopyElim

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt Dom

variable {tabs : Tables} {f g : Func}

theorem control_rel {fr : Frame} {b b' : Block}
    (hc : ∀ (k : Nat) (c : ID) (y : Val), b.controls[k]? = some c →
      fr.regs[c]? = some (some y) → ∃ c', b'.controls[k]? = some c' ∧ fr.regs[c']? = some (some y))
    {k : Nat} {v : Val} (h : Sem.control fr b k = .ok v) : Sem.control fr b' k = .ok v := by
  unfold Sem.control at h ⊢
  cases hk : b.controls[k]? with
  | none => simp [hk] at h
  | some c =>
    simp only [hk] at h
    have hy : fr.regs[c]? = some (some v) := by
      cases hr : fr.regs[c]? with
      | none => simp [hr, Res.ofOption] at h
      | some o =>
        cases o with
        | none => simp [hr, Res.ofOption] at h
        | some y => simp [hr, Res.ofOption] at h; rw [h]
    obtain ⟨c', hc', hy'⟩ := hc k c v hk hy
    simp [hc', hy', Res.ofOption]

theorem stepTerm_rel {fr : Frame} {b b' : Block} (hk : b'.kind = b.kind)
    (hs : b'.succs = b.succs) (hid : b'.id = b.id)
    (hc : ∀ (k : Nat) (c : ID) (y : Val), b.controls[k]? = some c →
      fr.regs[c]? = some (some y) → ∃ c', b'.controls[k]? = some c' ∧ fr.regs[c']? = some (some y))
    {n : Next} (h : stepTerm fr b = .ok n) : stepTerm fr b' = .ok n := by
  have hsucc : ∀ k, succ b' k = succ b k := fun k => by unfold succ; rw [hs, hid]
  have hctl : ∀ v, Sem.control fr b 0 = .ok v → Sem.control fr b' 0 = .ok v := fun v h => control_rel hc h
  unfold stepTerm at h ⊢
  rw [hk]
  cases hb : b.kind <;> simp only [hb] at h ⊢
  all_goals
    try simp only [hsucc, hid]
    first
      | exact h
      | (cases hc0 : Sem.control fr b 0 with
          | ok v => rw [hctl v hc0]; rw [hc0] at h; exact h
          | panic e m => rw [hc0] at h; cases h
          | stuck msg => rw [hc0] at h; cases h)

theorem succ_mem {b : Block} {k : Nat} {e : Edge} (h : succ b k = .ok (.goto e)) :
    e ∈ b.succs := by
  unfold succ at h
  cases hk : b.succs[k]? with
  | none => rw [hk] at h; cases h
  | some e' => rw [hk] at h; cases h; exact Array.mem_of_getElem? hk

theorem stepTerm_goto_mem {fr : Frame} {b : Block} {e : Edge}
    (h : stepTerm fr b = .ok (.goto e)) : e ∈ b.succs := by
  unfold stepTerm at h
  cases hb : b.kind <;> simp only [hb] at h
  all_goals first
    | (cases h; done)
    | exact succ_mem h
    | (cases hc0 : Sem.control fr b 0 with
        | ok v =>
          rw [hc0] at h
          simp only [bind, Res.bind] at h
          split at h <;> first | (cases h; done) | exact succ_mem h | (split at h <;> first
            | (cases h; done) | (split at h <;> cases h))
        | panic e m => rw [hc0] at h; cases h
        | stuck msg => rw [hc0] at h; cases h)

theorem stepTerm_not_panic {fr : Frame} {b : Block} {e : Panic} {m : Mem} :
    stepTerm fr b ≠ .panic e m := by
  intro h
  have hsp : ∀ k, succ b k ≠ .panic e m := fun k h => by
    unfold succ at h; cases hk : b.succs[k]? <;> rw [hk] at h <;> cases h
  unfold stepTerm at h
  cases hb : b.kind <;> simp only [hb] at h
  all_goals first
    | (cases h; done)
    | exact hsp _ h
    | (cases hc0 : Sem.control fr b 0 with
        | ok v =>
          rw [hc0] at h
          simp only [bind, Res.bind] at h
          split at h <;> first | (cases h; done) | exact hsp _ h | (split at h <;> first
            | (cases h; done) | (split at h <;> cases h))
        | panic e' m' =>
          unfold Sem.control at hc0
          split at hc0
          · unfold Res.ofOption at hc0; split at hc0 <;> cases hc0
          · cases hc0
        | stuck msg => rw [hc0] at h; cases h)

/-- The simulation relation: equal frames, the invariant `At`. -/
def R (env : Env) (tabs : Tables) (f g : Func) (frS frT : Frame) (bid : ID) (i : Nat) : Prop :=
  frT = frS ∧ At env tabs f g frS bid i

/-- **One block step of copyelim's simulation.** -/
theorem step (S : Setup tabs f g) {env : Env} {fr : Frame} {bid : ID} {i : Nat}
    (hA : At env tabs f g fr bid i) :
    StepSim (R env tabs f g) (blockStep env (Ctx.make tabs f) fr bid i)
      (blockStep env (Ctx.make tabs g) fr bid i) := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  have hbt := hA.tree S
  unfold blockStep
  simp only [show (Ctx.make tabs f).f = f from rfl, show (Ctx.make tabs g).f = g from rfl]
  cases hfb : f.block? bid with
  | none => exact True.intro
  | some fb =>
  simp only
  cases hen : enterBlock env (Ctx.make tabs f) fr fb i with
  | panic e m =>
    obtain ⟨gb, hgbb, hT⟩ := enter_panic S hA hfb hen
    rw [hgbb]; simp only [hT]; rfl
  | stuck msg => exact True.intro
  | ok G =>
  obtain ⟨gb, hgbb, hT⟩ := enter_ok S hA hfb hen
  obtain ⟨gb', hgbb', hgid, hsucc, -, hkind, hvals, -, hctl⟩ := S.block hbt hfb
  rw [hgbb] at hgbb'; cases hgbb'
  rw [hgbb]
  simp only [hT]
  -- the source's frame after the block, as a `Mid`
  obtain ⟨fb', hfb', hfid⟩ := hwf.blockId bid hbt.1
  rw [hfb] at hfb'; cases hfb'
  have hen' := hen
  rw [enterBlock_eq] at hen'
  cases hpsS : fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) fr i) with
  | panic e m => rw [hpsS] at hen'; cases hen'
  | stuck msg => rw [hpsS] at hen'; cases hen'
  | ok psS =>
  rw [hpsS] at hen'
  change (Res.ofOption _ ((Ctx.make tabs f).sched[fb.id]?).join).bind _ = _ at hen'
  rw [hfid, sched_of_block hfb] at hen'
  cases hsched : schedule f fb with
  | none => rw [hsched] at hen'; cases hen'
  | some oS =>
  rw [hsched] at hen'
  change evalAll env (Ctx.make tabs f) _ oS.toList = .ok G at hen'
  obtain ⟨hM, -, -⟩ := mid_of S hA hfb hpsS hsched (R := []) (by simp) hen'
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
      have hcU := ctrlUse S.cf hbt.1 hfb hbt.2 hcm
      obtain ⟨y', h1, h2⟩ := copyEq S hA hfb hM hcl hcU (fun hm => by
        by_cases hph : ∃ v, f.value? c = some v ∧ v.op = .Phi
        · exact .inl hph
        · obtain ⟨v, -, hv, -⟩ := S.value hbt hfb hm
          exact .inr (by simpa using (omem c).2 ⟨hm, v, hv, fun hp => hph ⟨v, hv, hp⟩⟩))
        hu hop hargs
      rw [hy] at h1; cases h1; exact h2
  -- frames after the block
  have hsz : fr.regs.size = f.valueTab.size := hA.size
  have hszG : fr.regs.size = g.valueTab.size := by rw [hsz, S.rel.vsize]
  have hbg : bid ∈ g.blocks := by rw [S.blocks]; exact hbt.1
  obtain ⟨hDS, -, hGs⟩ := dinv_enter hwf S.cf hbt.1 hfb hsz (hA.upS S) hen
  have hupT : DInv env (Ctx.make tabs g) (fun a => Anc (make g) a bid ∧ a ≠ bid) fr := by
    rw [S.mk_eq]; exact hA.upT S
  obtain ⟨hDT, -, -⟩ := dinv_enter hwg S.cg hbg hgbb hszG hupT hT
  rw [S.mk_eq] at hDT
  have hAt : ∀ e, e ∈ fb.succs → At env tabs f g G e.b e.i := fun e he =>
    ⟨by rw [hGs, hsz], typed_enter hwf hbt.1 hfb hsz hA.tyS hen,
      typed_enter hwg hbg hgbb hszG hA.tyT hT,
      .inr ⟨bid, fb, hbt.1, hfb, hbt.2, by cases e; exact he, hDS, hDT⟩⟩
  cases hst : stepTerm G fb with
  | ok n =>
    have hst' := stepTerm_rel hkind hsucc hgid hcs hst
    cases n with
    | goto e =>
      rw [hst']
      exact ⟨G, rfl, rfl, hAt e (stepTerm_goto_mem hst)⟩
    | ret rs m =>
      rw [hst']
      exact ⟨rs, rfl, RefinesList.refl rs⟩
  | panic e m => exact absurd hst stepTerm_not_panic
  | stuck msg => exact True.intro

/-- **copyelim's static relation gives refinement.** -/
theorem refines_of_rel (S : Setup tabs f g) : Refines tabs g tabs f := by
  intro env args mem fuel hd
  refine ⟨fuel, ?_⟩
  unfold run runCtx at hd ⊢
  rw [S.params]
  split
  · rename_i hn; simp only [hn] at hd; exact hd.elim
  · rename_i hn
    simp only [hn] at hd
    have hsz : (Ctx.make tabs g).f.valueTab.size = (Ctx.make tabs f).f.valueTab.size :=
      S.rel.vsize
    have hentry : entryFrame env (Ctx.make tabs g) args mem = entryFrame env (Ctx.make tabs f) args mem := by
      unfold entryFrame frameMem frameAllocs
      rw [S.paramTys, S.locals, hsz]; rfl
    rw [hentry, S.outs, show (Ctx.make tabs g).act = (Ctx.make tabs f).act from rfl,
      show (Ctx.make tabs g).f.entry = (Ctx.make tabs f).f.entry from S.entry]
    exact finish_refines hd (runLoop_sim (R env tabs f g)
      (fun frS frT bid i ⟨h1, h2⟩ => by subst h1; exact step S h2) fuel _ _ _ _
      ⟨rfl, by simp [Ctx.make, entryFrame], typed_replicate _ _ _ rfl, typed_replicate _ _ _ rfl,
        .inl rfl⟩ (finish_defined hd))

end GoFV.Proof.CopyElim
