import GoFV.Proof.Pass.ZCSEPanic
import GoFV.Proof.Pass.CopyElim

variable [GoFV.SSA.Sem.Addrs]

/-!
# zero arg cse refines its input

`refines_of_rel`: two well-formed functions related by `ZRel` (`f` passing the dominator
certificate) run alike: lock-step simulation (`runLoop_sim`) where the target's frame is the
source's at the entry and `fill` of it afterwards (`TF`), with the source-side invariant `At`
at every block entry (`enter_ok`, `enter_panic`, `stepTerm`
reading the related controls). `zcse_refines`: the validated pass (`zcsePass`) refines its
input, since it returns either the input or a result its checker accepted (`zrel_sound`).
-/

namespace GoFV.Proof.ZCSE

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.ZCSE Dom
open GoFV.Proof.CopyElim (stepTerm_goto_mem stepTerm_not_panic)

variable {tabs : Tables} {f g : Func}

theorem control_frames {fr fr' : Frame} {b : Block}
    (hc : ∀ (k : Nat) (c : ID) (y : Val), b.controls[k]? = some c →
      fr.regs[c]? = some (some y) → fr'.regs[c]? = some (some y))
    {k : Nat} {v : Val} (h : Sem.control fr b k = .ok v) : Sem.control fr' b k = .ok v := by
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
    simp [hc k c v hk hy, Res.ofOption]

/-- The terminator reads only the controls: frames agreeing on them, blocks with the same
kind, successors, ID and controls step alike. -/
theorem stepTerm_frames {fr fr' : Frame} {b b' : Block} (hk : b'.kind = b.kind)
    (hs : b'.succs = b.succs) (hid : b'.id = b.id) (hcs : b'.controls = b.controls)
    (hc : ∀ (k : Nat) (c : ID) (y : Val), b.controls[k]? = some c →
      fr.regs[c]? = some (some y) → fr'.regs[c]? = some (some y))
    {n : Next} (h : stepTerm fr b = .ok n) : stepTerm fr' b' = .ok n := by
  have hsucc : ∀ k, succ b' k = succ b k := fun k => by unfold succ; rw [hs, hid]
  have hctl : ∀ v, Sem.control fr b 0 = .ok v → Sem.control fr' b' 0 = .ok v := fun v h => by
    have := control_frames hc h
    unfold Sem.control at this ⊢
    rw [hcs, hid]; exact this
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

theorem evalAll_shape {env : Env} {ctx : Ctx} :
    ∀ {o : List ID} {fr fr' : Frame}, evalAll env ctx fr o = .ok fr' →
      fr' = { fr with regs := fr'.regs } ∧ fr'.regs.size = fr.regs.size
  | [], _, _, h => by cases h; exact ⟨rfl, rfl⟩
  | x :: o, fr, fr', h => by
    rw [evalAll_cons] at h
    cases hx : stepV env ctx fr x with
    | ok y =>
      rw [hx] at h
      obtain ⟨h1, h2⟩ := evalAll_shape h
      exact ⟨h1, by rw [h2]; simp [Frame.set]⟩
    | panic e m => rw [hx] at h; cases h
    | stuck msg => rw [hx] at h; cases h

/-- Entering a block changes only registers, of the same number. -/
theorem enter_shape {env : Env} {ctx : Ctx} {fr fr' : Frame} {b : Block} {i : Nat}
    (h : enterBlock env ctx fr b i = .ok fr') :
    fr' = { fr with regs := fr'.regs } ∧ fr'.regs.size = fr.regs.size := by
  rw [enterBlock_eq] at h
  cases hps : b.values.toList.filterMapM (phiStep ctx fr i) with
  | panic e m => rw [hps] at h; cases h
  | stuck msg => rw [hps] at h; cases h
  | ok ps =>
    rw [hps] at h
    change (Res.ofOption _ (ctx.sched[b.id]?).join).bind _ = _ at h
    cases ho : (ctx.sched[b.id]?).join with
    | none => rw [ho] at h; cases h
    | some o =>
      rw [ho] at h
      change evalAll env ctx _ o.toList = .ok fr' at h
      obtain ⟨h1, h2⟩ := evalAll_shape h
      exact ⟨h1, by rw [h2]; exact setPhis_size ps fr.regs⟩

/-- The simulation relation: `At` for the source, `TF` for the target. -/
def R (env : Env) (tabs : Tables) (f g : Func) (frS frT : Frame) (bid : ID) (i : Nat) : Prop :=
  At env tabs f frS bid i ∧ TF env tabs f g frS frT bid

/-- **One block step of zcse's simulation.** -/
theorem step (S : Setup tabs f g) {env : Env} {fr frT : Frame} {bid : ID} {i : Nat}
    (hA : At env tabs f fr bid i) (hT : TF env tabs f g fr frT bid) :
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
  obtain ⟨gb, hgbb, hTen⟩ := enter_ok S hA hT hfb hen
  obtain ⟨gb', hgbb', hgid, hsucc, -, hkind, hctl, -, -⟩ := S.block hbt.1 hfb
  rw [hgbb] at hgbb'; cases hgbb'
  rw [hgbb]
  simp only [hTen]
  obtain ⟨hGfr, hGsz⟩ := enter_shape hen
  have hinvG := arglessInv_enter hA.inv (hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩) hen
  have hszG : G.regs.size = f.valueTab.size := by rw [hGsz, hA.size]
  have hAt : ∀ e, e ∈ fb.succs → R env tabs f g G (fill env tabs g G) e.b e.i := fun e he =>
    ⟨⟨hszG, by rw [hGfr]; exact hA.images, hinvG,
      .inr ⟨bid, fb, hbt.1, hfb, hbt.2, by cases e; exact he⟩⟩,
      .inr ⟨(edge S.cf hbt.1 hfb hbt.2 he).1, rfl⟩⟩
  have hcs : ∀ (k : Nat) (c : ID) (y : Val), fb.controls[k]? = some c →
      G.regs[c]? = some (some y) → (fill env tabs g G).regs[c]? = some (some y) :=
    fun k c y hc hy => argRead S hinvG hszG
      (hwf.ctrlListed bid fb ⟨hbt.1, hfb⟩ c (Array.mem_of_getElem? hc)) hy (.inl rfl)
  cases hst : stepTerm G fb with
  | ok n =>
    have hst' := stepTerm_frames hkind hsucc hgid hctl hcs hst
    cases n with
    | goto e =>
      rw [hst']
      exact ⟨_, rfl, hAt e (stepTerm_goto_mem hst)⟩
    | ret rs m =>
      rw [hst']
      exact ⟨rs, rfl, RefinesList.refl rs⟩
  | panic e m => exact absurd hst stepTerm_not_panic
  | stuck msg => exact True.intro

/-- **zcse's output relation gives refinement.** -/
theorem refines_of_rel (S : Setup tabs f g) : Refines tabs g tabs f := by
  intro env args mem fuel hd
  refine ⟨fuel, ?_⟩
  unfold run runCtx at hd ⊢
  rw [S.params]
  split
  · rename_i hn; simp only [hn] at hd; exact hd.elim
  · rename_i hn
    simp only [hn] at hd
    have hlen : args.length = (Ctx.make tabs f).params.size := by simpa using hn
    have hsz : (Ctx.make tabs g).f.valueTab.size = (Ctx.make tabs f).f.valueTab.size :=
      S.rel.vsize
    have hentry : entryFrame env (Ctx.make tabs g) args mem =
        entryFrame env (Ctx.make tabs f) args mem := by
      unfold entryFrame frameMem frameAllocs
      rw [S.paramTys, S.locals, hsz]; rfl
    rw [hentry, S.outs, show (Ctx.make tabs g).act = (Ctx.make tabs f).act from rfl,
      show (Ctx.make tabs g).f.entry = (Ctx.make tabs f).f.entry from S.entry]
    have hA0 : At env tabs f (entryFrame env (Ctx.make tabs f) args mem) f.entry 0 :=
      ⟨by simp [Ctx.make, entryFrame], by simp [entryFrame, Ctx.make, hlen] at hlen ⊢,
        arglessInv_init _ _ _ _ rfl, .inl rfl⟩
    exact finish_refines hd (runLoop_sim (R env tabs f g)
      (fun frS frT bid i ⟨h1, h2⟩ => step S h1 h2) fuel _ _ _ _
      ⟨hA0, .inl ⟨rfl, rfl⟩⟩ (finish_defined hd))

/-- **zero arg cse refines its input.** The validated pass returns the input or a result its
checker accepted; on a checked input, either refines the input. -/
theorem zcse_refines {penv : PassEnv} {f : Func} {out : PassOut} {ce ce' : CheckEnv}
    (h : zcsePass penv f = .ok out) (hf : check ce f = .ok ()) (hg : check ce' out.func = .ok ()) :
    Refines out.tables out.func penv.tables f := by
  simp only [zcsePass, Pass.ofFunc, bind, Except.bind, pure, Except.pure] at h
  cases h
  simp only [zcseChecked] at hg ⊢
  split
  · rename_i hz
    simp only [hz, ite_true] at hg
    exact refines_of_rel
      { wf := ⟨ce, check_wf hf⟩, wg := ⟨ce', check_wf hg⟩,
        cf := certOK_of_check (check_domCert hf), rel := zrel_sound hz }
  · exact Refines.refl _ _

end GoFV.Proof.ZCSE
