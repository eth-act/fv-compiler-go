import GoFV.Proof.Pass.PhiOptPanic
import GoFV.Proof.Pass.ZCSE

/-!
# phiopt refines its input

`refines_of_rel`: two well-formed functions related by `PRel` (`f` passing the dominator
certificate, in zcse's fragment) run alike: lock-step simulation (`runLoop_sim`) with the
source-side invariant `At` (lemma (D), `ArglessInv`, the edge facts) and the target's frame
related on the values of `f` (`TR`). `phiopt_refines`: the validated pass (`phioptPass`)
refines its input, since it returns either the input or a result its checker accepted
(`prel_sound`).
-/

namespace GoFV.Proof.PhiOpt

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.PhiOpt Dom
open GoFV.Proof.CopyElim (stepTerm_goto_mem stepTerm_not_panic)
open GoFV.Proof.ZCSE (Chained NoNil stepTerm_frames enter_shape arglessInv_enter
  arglessInv_init)

variable {tabs : Tables} {f g : Func}

/-- The simulation relation. -/
def R (env : Env) (tabs : Tables) (f g : Func) (frS frT : Frame) (bid : ID) (i : Nat) : Prop :=
  At env tabs f frS bid i ∧ TR f g frS frT

/-- Entering a block changes only the registers of its values. -/
theorem enter_keep {ce : CheckEnv} (hwf : WF ce f) {b : ID} {blk : Block} (hb : b ∈ f.blocks)
    (hbb : f.block? b = some blk) {env : Env} {fr G : Frame} {i : Nat}
    (hs : fr.regs.size = f.valueTab.size)
    (h : enterBlock env (Ctx.make tabs f) fr blk i = .ok G) :
    ∀ z, z ∉ blk.values → G.regs[z]? = fr.regs[z]? := by
  have hnd := hwf.valuesNodup b blk ⟨hb, hbb⟩
  have hown := valuesOwn hwf hb hbb
  obtain ⟨b', hb', hid⟩ := hwf.blockId b hb
  rw [hbb] at hb'; cases hb'
  obtain ⟨frP, o, ho, hev, -, hPs, -, hkeep, -⟩ := enterBlock_spec hnd h
  rw [hid, sched_of_block hbb] at ho
  obtain ⟨ond, otopo, omem⟩ := schedule_topo hown hnd ho
  obtain ⟨-, -, e3, -⟩ := evalAll_spec ond otopo (by rw [hPs, hs]; rfl) hev
  intro z hz
  rw [e3 z (fun hm => hz ((omem z).1 hm).1), hkeep z (.inl hz)]

/-- **One block step of phiopt's simulation.** -/
theorem step (S : Setup tabs f g) {env : Env} {fr frT : Frame} {bid : ID} {i : Nat}
    (hA : At env tabs f fr bid i) (hT : TR f g fr frT) :
    StepSim (R env tabs f g) (blockStep env (Ctx.make tabs f) fr bid i)
      (blockStep env (Ctx.make tabs g) frT bid i) := by
  obtain ⟨ce, hwf⟩ := S.wf
  have hbt := hA.tree S
  unfold blockStep
  simp only [show (Ctx.make tabs f).f = f from rfl, show (Ctx.make tabs g).f = g from rfl]
  cases hfb : f.block? bid with
  | none => exact True.intro
  | some fb =>
  simp only
  cases hen : enterBlock env (Ctx.make tabs f) fr fb i with
  | panic e m =>
    obtain ⟨gb, hgbb, hTen⟩ := enter_panic S hA hT hfb hen
    rw [hgbb]; simp only [hTen]; rfl
  | stuck msg => exact True.intro
  | ok G =>
  obtain ⟨gb, GT, hgbb, hTen, hTR⟩ := enter_ok S hA hT hfb hen
  obtain ⟨gb', hgbb', hgid, hsucc, -, hkind, hctl, -, -⟩ := S.block hbt.1 hfb
  rw [hgbb] at hgbb'; cases hgbb'
  rw [hgbb]
  simp only [hTen]
  have hnd := hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩
  obtain ⟨hGfr, hGsz⟩ := enter_shape hen
  have hszG : G.regs.size = f.valueTab.size := by rw [hGsz, hA.size]
  have hcs : ∀ (k : Nat) (c : ID) (y : Val), fb.controls[k]? = some c →
      G.regs[c]? = some (some y) → GT.regs[c]? = some (some y) :=
    fun k c y hc hy => by
      rw [hTR.2.2 c (hwf.ctrlListed bid fb ⟨hbt.1, hfb⟩ c (Array.mem_of_getElem? hc))]; exact hy
  cases hst : stepTerm G fb with
  | ok n =>
    have hst' := stepTerm_frames hkind hsucc hgid hctl hcs hst
    cases n with
    | goto e =>
      rw [hst']
      have he := stepTerm_goto_mem hst
      obtain ⟨hdG, -, -⟩ := dinv_enter (tabs := tabs) hwf S.cf hbt.1 hfb hA.size hA.dinv hen
      refine ⟨_, rfl, ⟨hszG, arglessInv_enter hA.inv hnd hen,
        dinv_edge S.cf hbt.1 hfb hbt.2 he hdG,
        path_step hwf ⟨hbt.1, hfb⟩ (hA.edge S hfb) hA.path
          (enter_keep hwf hbt.1 hfb hA.size hen) hst,
        .inr ⟨bid, fb, hbt.1, hfb, hbt.2, by cases e; exact he⟩⟩, hTR⟩
    | ret rs m =>
      rw [hst']
      exact ⟨rs, rfl, RefinesList.refl rs⟩
  | panic e m => exact absurd hst stepTerm_not_panic
  | stuck msg => exact True.intro

/-- **phiopt's output relation gives refinement.** -/
theorem refines_of_rel (S : Setup tabs f g) : Refines tabs g tabs f := by
  obtain ⟨ce, hwf⟩ := S.wf
  intro env args mem fuel hd
  refine ⟨fuel, ?_⟩
  unfold run runCtx at hd ⊢
  rw [S.params]
  split
  · rename_i hn; simp only [hn] at hd; exact hd.elim
  · rename_i hn
    simp only [hn] at hd
    have hentry : entryFrame env (Ctx.make tabs g) args mem =
        { entryFrame env (Ctx.make tabs f) args mem with
          regs := Array.replicate g.valueTab.size none } := by
      unfold entryFrame frameMem
      rw [S.paramTys, S.locals]; rfl
    rw [hentry, S.outs, show (Ctx.make tabs g).act = (Ctx.make tabs f).act from rfl,
      show (Ctx.make tabs g).f.entry = (Ctx.make tabs f).f.entry from S.entry]
    have hA0 : At env tabs f (entryFrame env (Ctx.make tabs f) args mem) f.entry 0 :=
      ⟨by simp [Ctx.make, entryFrame], arglessInv_init _ _ _ _ rfl, dinv_entry S.cf _,
        pathOK_entry hwf _, .inl ⟨rfl, rfl⟩⟩
    have hT0 : TR f g (entryFrame env (Ctx.make tabs f) args mem)
        { entryFrame env (Ctx.make tabs f) args mem with
          regs := Array.replicate g.valueTab.size none } := by
      refine ⟨rfl, by simp, fun x hx => ?_⟩
      have hlt := listed_lt hwf hx
      have hlt' : x < g.valueTab.size := Nat.lt_of_lt_of_le hlt S.gsize
      simp [entryFrame, Ctx.make, hlt, hlt']
    exact finish_refines hd (runLoop_sim (R env tabs f g)
      (fun frS frT bid i ⟨h1, h2⟩ => step S h1 h2) fuel _ _ _ _ ⟨hA0, hT0⟩
      (finish_defined hd))

/-- **phiopt refines its input.** The validated pass returns the input or a result its
checker accepted; on a checked input in the fragment, either refines the input. -/
theorem phiopt_refines {penv : PassEnv} {f : Func} {out : PassOut} {ce ce' : CheckEnv}
    (h : phioptPass penv f = .ok out) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ()) (hch : Chained f) (hnn : NoNil f) :
    Refines out.tables out.func penv.tables f := by
  unfold phioptPass Pass.ofFunc phioptChecked at h
  cases hu : penv.typ? "UInt8" with
  | none => simp [hu, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at h
  | some u8 =>
    cases hp : phiopt penv.tables u8 f with
    | error msg => simp [hu, hp, bind, Except.bind] at h
    | ok g =>
      simp only [hu, hp, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only at hg ⊢
      split
      · rename_i hrel
        simp only [hrel, ↓reduceIte] at hg
        exact refines_of_rel
          { wf := ⟨ce, check_wf hf⟩, wg := ⟨ce', check_wf hg⟩,
            cf := certOK_of_check (check_domCert hf), rel := prel_sound hrel, chained := hch,
            noNil := hnn }
      · exact Refines.refl _ _

end GoFV.Proof.PhiOpt
