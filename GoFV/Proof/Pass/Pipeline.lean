import GoFV.Opt.Verified
import GoFV.Proof.Pass.NumberLines
import GoFV.Proof.Pass.Identity
import GoFV.Proof.Pass.CopyElimPass
import GoFV.Proof.Pass.DeadcodePass
import GoFV.Proof.Pass.Rewrite
import GoFV.Proof.Pass.ZCSE
import GoFV.Proof.Pass.CSE
import GoFV.Proof.Pass.PhiOpt
import GoFV.Proof.Pass.NilSim
import GoFV.Proof.Pass.Prove
import GoFV.Proof.Pass.KnownBits
import GoFV.Proof.Pass.BranchElimPass
import GoFV.Proof.Pass.DAE
import GoFV.Proof.Pass.Sccp
import GoFV.Proof.Pass.DSE
import GoFV.Proof.Pass.FuseEarlyPass
import GoFV.Proof.Pass.ECMain
import GoFV.Proof.Pass.MemCombine
import GoFV.Proof.Pass.ShortCircPass
import GoFV.Proof.Pass.FuseLatePass
import GoFV.Proof.Pass.WBSim
import GoFV.Proof.TabsAgree
import GoFV.Proof.Pass.Decompose

variable [GoFV.SSA.Sem.Addrs]

/-!
# The verified generic pipeline refines its input (issue #189)

The pass theorems conclude seven relations: `Refines`, `RefinesUnder Env.Mono` (passes that
rewrite call arguments rely on monotone contracts), `RefinesUnder (Env.Mono ∧ Env.FrameKeep)`
(expand calls: the function's stack-assigned results stay writable in their frame slots across
calls), `RefinesFrom (FrameSafe ∧ InitAvoids)`
(dead auto elim), `RefinesFrom (RwPre tabs fe f)` (the checked rewrite passes: monotone
contracts, malloc-family contracts that return non-nil pointers, non-nil dictionary arguments of
the pass input `f`, the runtime's memory-call contracts, `InitAvoids`; issue #151),
`RefinesFrom WbPre`
(writebarrier: a defined, read-only write-barrier flag and no write-barrier buffer, kept by the
contracts; issue #36) and
`RefinesFrom DecPre` (decompose user/builtin: monotone contracts that cannot tell whether
unreachable frame temporaries exist, `InitAvoids`; issue #17). All seven imply
`VRefines k ro eq := RefinesFrom (VPre k ro eq)`, where
`VPre k ro eq` is their conjunction with the input's dictionary parameters `k`, read-only
symbols `ro` and `ifaceeq`/`efaceeq` descriptor symbols `eq` (`relHolds_toV`; the pipeline runs a
proven pass only on states whose dictionary parameters are the input's and whose read-only and
descriptor symbols are among the input's, `VState.dict`, `VState.ro`, `VState.eq`), and
`VRefines k ro eq` composes (`RefinesFrom.trans`).

`stockPasses_sound`: every `proven` step of `GoFV.Opt.stockPasses` satisfies its theorem
(`Step.Sound`: the pass's result relates to its input whenever both pass `check` and the guard
accepts the input). `verifiedPipeline_refines`: when `verifiedPipeline` returns a `verified`
state, its function refines the input, by induction over the passes with the invariant
`Inv` (verified ⇒ refines the input; `wf` ⇒ `check`).
-/

namespace GoFV.Proof.Pipeline

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.Verified GoFV.Proof

/-- The environments and inputs on which every pass theorem holds, for an input whose
dictionary parameters are `k` (`NilCheck.dictParams`): monotone, frame-safe contracts,
malloc-family contracts that return non-nil pointers, inputs that hold no pointer into a frame
temporary, non-nil dictionary arguments, a memory with a defined, read-only write-barrier
flag and no write-barrier buffer, kept by the contracts (`WB.WbPre`), contracts that cannot
tell whether unreachable frame temporaries exist (`Env.TempOblivious`),
`runtime.memclrNoHeapPointers`/`runtime.memmove` contracts that are the runtime's, if present
(`Env.MemOps`), read-only symbols `ro` holding their exported bytes in the memory with the
global image, kept by the contracts (`RoImage`), contracts that keep the caller's frame
blocks and return no memory (`Env.FrameKeep`), malloc-family contracts asked for a positive
size that return an all-zero heap block (`Env.AllocZero`), `runtime.growslice` contracts that
return a slice of the requested length (`Env.GrowLen`), and `runtime.ifaceeq`/`efaceeq`
contracts that return the pointer equality of their data words on the descriptor symbols `eq`
(`Env.IfaceEq`). -/
def VPre (k : List Nat) (ro : List (String × Alloc)) (eq : List String × List String) (env : Env)
    (args : List Val) (mem : Mem) : Prop :=
  env.Mono ∧ env.FrameSafe ∧ InitAvoids env args mem ∧ env.AllocNonNil ∧ DictArgs k args ∧
    WB.WbPre env args mem ∧ env.TempOblivious ∧ env.MemOps ∧ RoImage ro env mem ∧
    env.FrameKeep ∧ env.AllocZero ∧ env.GrowLen ∧ env.IfaceEq eq

/-- The refinement the verified pipeline establishes. -/
abbrev VRefines (k : List Nat) (ro : List (String × Alloc)) (eq : List String × List String)
    (tabs' : Tables) (f' : Func) (tabs : Tables) (f : Func) : Prop :=
  RefinesFrom (VPre k ro eq) tabs' f' tabs f

variable {k : List Nat} {ro : List (String × Alloc)} {eq : List String × List String}
  {tabs tabs' : Tables} {f f' : Func}

theorem Refines.toV (h : Refines tabs' f' tabs f) : VRefines k ro eq tabs' f' tabs f :=
  Refines.from (VPre k ro eq) h

theorem RefinesUnder.toV (h : RefinesUnder Env.Mono tabs' f' tabs f) :
    VRefines k ro eq tabs' f' tabs f :=
  RefinesFrom.mono (fun _ _ _ hp => hp.1) h.from

theorem RefinesUnder.frameKeep_toV
    (h : RefinesUnder (fun env => env.Mono ∧ env.FrameKeep) tabs' f' tabs f) :
    VRefines k ro eq tabs' f' tabs f :=
  RefinesFrom.mono (fun _ _ _ hp => ⟨hp.1, hp.2.2.2.2.2.2.2.2.2.1⟩) h.from

theorem RefinesFrom.frameSafe_toV
    (h : RefinesFrom (fun env args mem => env.FrameSafe ∧ InitAvoids env args mem) tabs' f' tabs f) :
    VRefines k ro eq tabs' f' tabs f :=
  RefinesFrom.mono (fun _ _ _ hp => ⟨hp.2.1, hp.2.2.1⟩) h

theorem RefinesFrom.rw_toV {fe : Tables} (hk : NilCheck.dictParams tabs f = k)
    (hro : ∀ e ∈ RewriteCheck.roPass tabs fe f, e ∈ ro)
    (heq : (∀ s ∈ (RewriteCheck.eqPass tabs fe).1, s ∈ eq.1) ∧
      ∀ s ∈ (RewriteCheck.eqPass tabs fe).2, s ∈ eq.2)
    (h : RefinesFrom (Pass.Rewrite.RwPre tabs fe f) tabs' f' tabs f) :
    VRefines k ro eq tabs' f' tabs f :=
  RefinesFrom.mono (fun _ _ _ hp =>
    ⟨hp.1, ⟨hp.2.2.2.1, by rw [hk]; exact hp.2.2.2.2.1⟩, hp.2.2.2.2.2.2.2.1,
      hp.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.1.sub hro, hp.2.2.1,
      hp.2.2.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.2.sub heq.1 heq.2⟩) h

theorem RefinesFrom.wb_toV (h : RefinesFrom WB.WbPre tabs' f' tabs f) :
    VRefines k ro eq tabs' f' tabs f :=
  RefinesFrom.mono (fun _ _ _ hp => hp.2.2.2.2.2.1) h

theorem RefinesFrom.dec_toV (h : RefinesFrom Decompose.DecPre tabs' f' tabs f) :
    VRefines k ro eq tabs' f' tabs f :=
  RefinesFrom.mono (fun _ _ _ hp => ⟨hp.1, hp.2.2.2.2.2.2.1, hp.2.2.1⟩) h

/-- The relation a `Rel` names (`fe`: the frontend tables, which the rewrite passes'
precondition reads). -/
def relHolds : Rel → Tables → Tables → Func → Tables → Func → Prop
  | .refines => fun _ => Refines
  | .mono => fun _ => RefinesUnder Env.Mono
  | .frameSafe => fun _ => RefinesFrom (fun env args mem => env.FrameSafe ∧ InitAvoids env args mem)
  | .rw => fun fe tabs' f' tabs f => RefinesFrom (Pass.Rewrite.RwPre tabs fe f) tabs' f' tabs f
  | .wb => fun _ => RefinesFrom WB.WbPre
  | .dec => fun _ => RefinesFrom Decompose.DecPre
  | .frameKeep => fun _ => RefinesUnder (fun env => env.Mono ∧ env.FrameKeep)

/-- Each pass relation implies the pipeline's, for an input with dictionary parameters `k`. -/
theorem relHolds_toV {fe : Tables} (hk : NilCheck.dictParams tabs f = k)
    (hro : ∀ e ∈ RewriteCheck.roPass tabs fe f, e ∈ ro)
    (heq : (∀ s ∈ (RewriteCheck.eqPass tabs fe).1, s ∈ eq.1) ∧
      ∀ s ∈ (RewriteCheck.eqPass tabs fe).2, s ∈ eq.2) :
    {r : Rel} → relHolds r fe tabs' f' tabs f → VRefines k ro eq tabs' f' tabs f
  | .refines, h => Refines.toV h
  | .mono, h => RefinesUnder.toV h
  | .frameSafe, h => RefinesFrom.frameSafe_toV h
  | .rw, h => RefinesFrom.rw_toV hk hro heq h
  | .wb, h => RefinesFrom.wb_toV h
  | .dec, h => RefinesFrom.dec_toV h
  | .frameKeep, h => RefinesUnder.frameKeep_toV h

/-- A `proven` step's theorem: the result relates to the input when both pass `check` and the
guard accepts the input. -/
def stepSound : Verified.Step → Prop
  | .proven run rel guard => ∀ (penv : PassEnv) (f : Func) (out : PassOut) (ce ce' : CheckEnv),
      run penv f = .ok out → check ce f = .ok () → check ce' out.func = .ok () →
      guard penv f = true → relHolds rel penv.frontend out.tables out.func penv.tables f
  | .stock _ => True

theorem deadcodeStep_sound : stepSound deadcodeStep :=
  fun _ _ _ _ _ h hf hg hd => Dead.deadcode_refines h hf hg (Dead.deadFrag_of hd)

theorem optStep_sound : stepSound optStep :=
  fun _ _ _ _ _ h hf hg _ => Pass.Rewrite.opt_refines h hf hg

/-- **Every proven step of the stock pass table satisfies its theorem.** -/
theorem stockPasses_sound : ∀ p ∈ stockPasses.toList, stepSound p.step := by
  intro p hp
  simp only [stockPasses, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  -- number lines
  · exact fun _ _ _ _ _ h _ _ _ => numberLines_refines h
  -- early phielim and copyelim
  · intro _ _ _ _ _ h hf hg hd
    simp only [copyGuard, Bool.and_eq_true] at hd
    exact CopyElim.copyelim_refines h hf hg (CopyElim.copyFrag_sound hd.1)
      (CopyElim.emptyFrag_of hd.2)
  · exact deadcodeStep_sound
  -- short circuit
  · exact fun _ _ _ _ _ h _ _ _ => ShortCirc.shortcircuit_refines h
  -- decompose user
  · exact fun _ _ _ _ _ h hf hg hd => Decompose.decomposeUser_refines h hf hg hd
  · exact deadcodeStep_sound
  · exact optStep_sound
  -- zero arg cse
  · exact fun _ _ _ _ _ h hf hg _ => ZCSE.zcse_refines h hf hg
  · exact deadcodeStep_sound
  -- generic cse
  · exact fun _ _ _ _ _ h hf hg hd => CSE.cse_refines h hf hg hd
  -- phiopt
  · exact fun _ _ _ _ _ h hf hg _ => PhiOpt.phiopt_refines h hf hg
  · exact deadcodeStep_sound
  -- nilcheckelim
  · exact fun _ _ _ _ _ h hf _ hd => Nil.nilcheck_refines h hf hd
  -- prove
  · exact fun _ _ _ _ _ h hf hg _ => ProveCheck.proveChecked_refines h hf hg
  -- divisible, divmod
  · exact fun _ _ _ _ _ h hf hg _ => Pass.Rewrite.divisible_refines h hf hg
  · exact fun _ _ _ _ _ h hf hg _ => Pass.Rewrite.divmod_refines h hf hg
  · exact optStep_sound
  -- known bits
  · exact fun _ _ _ _ _ h hf hg _ => KnownBits.knownBits_refines h hf hg
  -- early fuse
  · exact fun _ _ _ _ _ h _ _ _ => FuseEarly.fuseEarly_refines h
  -- expand calls
  · exact fun _ _ _ _ _ h hf hg hd => EC.expandCalls_refines h hf hg hd
  -- decompose builtin
  · exact fun _ _ _ _ _ h hf hg hd => Decompose.decomposeBuiltin_refines h hf hg hd
  -- softfloat
  · exact fun _ _ _ _ _ h _ _ _ => softfloat_refines h
  -- branchelim
  · exact fun _ _ _ _ _ h _ _ _ => BranchElim.branchelim_refines h
  · exact optStep_sound
  -- dead auto elim
  · exact fun _ _ _ _ _ h hf hg hd => DAE.dead_auto_elim_refines h hf hg hd
  -- sccp
  · exact fun _ _ _ _ _ h hf hg _ => Sccp.sccp_refines h hf hg
  · exact deadcodeStep_sound
  -- late fuse
  · exact fun _ _ _ _ _ h _ _ _ => FuseLate.fuseLate_refines h
  -- check bce
  · exact fun _ _ _ _ _ h _ _ _ => checkbce_refines h
  -- dse
  · exact fun _ _ _ _ _ h hf hg hd => DSE.dse_refines h hf hg hd
  -- memcombine
  · exact fun _ _ _ _ _ h hf hg _ => MemCombine.memcombine_refines h hf hg
  -- writebarrier
  · intro _ _ _ _ _ h hf hg hd
    refine writebarrier_refines ?_ hf hg
    simp only [wbGuard] at hd
    simp only [writebarrierPass] at h
    rw [h] at hd
    simp only [writebarrierChecked, h, hd, bind, Except.bind, ↓reduceIte, pure, Except.pure]
  · trivial
  · trivial
  · trivial

/-! ## The pipeline -/

/-- The invariant of the pipeline's states from input `f0`: a verified state refines the
input, `wf` means the state passes `check`, and the state records the input's dictionary
parameters, read-only symbols and the pipeline's descriptor symbols. -/
def Inv (env : PassEnv) (f0 : Func) (st : VState) : Prop :=
  (st.verified = true → VRefines (NilCheck.dictParams env.tables f0)
    (pipelineRo env f0) (pipelineEq env) st.tables st.func env.tables f0) ∧
  (st.wf = true → check (checkEnv env st.tables) st.func = .ok ()) ∧
  st.dict = NilCheck.dictParams env.tables f0 ∧ st.ro = pipelineRo env f0 ∧
  st.eq = pipelineEq env

private theorem ok_of_toBool {ε : Type} {e : Except ε Unit} (h : e.toBool = true) : e = .ok () := by
  revert h; cases e <;> simp [Except.toBool]

theorem VState.same_eq {st : VState} {out : PassOut} (h : st.same out = true) :
    out.func = st.func ∧ out.tables = st.tables := by
  simp only [VState.same, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hf, h1⟩, h2⟩, h3⟩, h4⟩ := h
  refine ⟨hf, ?_⟩
  cases ho : out.tables
  cases hs : st.tables
  rw [ho, hs] at h1 h2 h3 h4
  simp only at h1 h2 h3 h4
  rw [h1, h2, h3, h4]

variable {env : PassEnv} {f0 : Func}

theorem Inv.init (zv : Array (ID × Nat)) : Inv env f0 (VState.init env f0 zv) :=
  ⟨fun _ => Refines.toV (Refines.refl _ _), ok_of_toBool, rfl, rfl, rfl⟩

theorem Inv.skip {st : VState} (h : Inv env f0 st) (name why : String) :
    Inv env f0 (st.skip name why) := h

theorem Inv.adopt {st : VState} (h : Inv env f0 st) {name : String} {out : PassOut} {wf : Bool}
    {v : Verdict}
    (hv : v.ok = true → VRefines (NilCheck.dictParams env.tables f0)
      (pipelineRo env f0) (pipelineEq env) out.tables out.func st.tables
      st.func)
    (hwf : wf = true → check (checkEnv env out.tables) out.func = .ok ()) :
    Inv env f0 (st.adopt name out wf v) := by
  refine ⟨fun hver => ?_, hwf, h.2.2⟩
  simp only [VState.adopt, Bool.and_eq_true] at hver
  exact RefinesFrom.trans (h.1 hver.1) (hv hver.2)

theorem Inv.continue {st : VState} (h : Inv env f0 st) {p : StockPass} {out : PassOut}
    {claim : Option String}
    (hc : claim = none → check (checkEnv env out.tables) out.func = .ok () →
      VRefines (NilCheck.dictParams env.tables f0) (pipelineRo env f0)
        (pipelineEq env) out.tables out.func st.tables st.func) :
    Inv env f0 (st.continue env p out claim) := by
  unfold VState.continue
  by_cases hs : st.same out = true
  · obtain ⟨hf, ht⟩ := VState.same_eq hs
    simp only [hs, ↓reduceIte]
    refine h.adopt (fun _ => ?_) (fun hw => ?_)
    · rw [hf, ht]; exact Refines.toV (Refines.refl _ _)
    · rw [hf, ht]; exact h.2.1 hw
  · simp only [hs, ↓reduceIte, Bool.false_eq_true]
    have hwf := ok_of_toBool (e := check (checkEnv env out.tables) out.func)
    by_cases ht : (decide (out.func = st.func) && tabsAgree st.tables out.tables st.func) = true
    · simp only [ht, ↓reduceIte]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
      refine h.adopt (fun _ => ?_) hwf
      rw [ht.1]
      exact Refines.toV (refines_of_tabsAgree ht.2 (Refines.refl _ _))
    simp only [ht, Bool.false_eq_true, ↓reduceIte]
    cases claim with
    | some why => exact h.adopt (fun hv => by cases hv) hwf
    | none =>
      simp only
      by_cases hw : (check (checkEnv env out.tables) out.func).toBool = true
      · simp only [hw, ↓reduceIte]; exact h.adopt (fun _ => hc rfl (ok_of_toBool hw)) (fun _ => ok_of_toBool hw)
      · simp only [hw, ↓reduceIte]
        by_cases hr : p.required = true
        · simp only [hr, ↓reduceIte]; exact h.adopt (fun hv => by cases hv) (fun hf => by cases hf)
        · simp only [hr, ↓reduceIte]; exact h.skip _ _

theorem ro_sub {l ro : List (String × Alloc)} (h : l.all ro.contains = true) :
    ∀ e ∈ l, e ∈ ro := fun e he => by
  rw [List.all_eq_true] at h
  exact List.contains_iff_mem.1 (h e he)

/-- The rewrite passes' read-only symbols on a state are pinned by the pipeline's precondition:
the state's own (checked by `runPass`) and the frontend's (`pipelineRo` has them all). -/
theorem roPass_sub {st : VState} (h : Inv env f0 st)
    (hro : (RewriteCheck.roSyms st.tables st.func).all st.ro.contains = true) (name : String) :
    ∀ e ∈ RewriteCheck.roPass st.tables (st.passEnv env name).frontend st.func,
      e ∈ pipelineRo env f0 := fun e he => by
  rcases List.mem_append.1 he with he | he
  · exact (h.2.2.2.1 ▸ ro_sub hro) e he
  · exact List.mem_append.2 (.inl (List.mem_append.2 (.inl (List.mem_append.2 (.inr he)))))

/-- The rewrite passes' descriptor symbols on a state are pinned by the pipeline's precondition:
the state's tables' (checked by `runPass`) and the frontend's (`pipelineEq` has them all). -/
theorem eqPass_sub {st : VState} (h : Inv env f0 st)
    (heq : ((RewriteCheck.eqSyms st.tables).1.all st.eq.1.contains &&
      (RewriteCheck.eqSyms st.tables).2.all st.eq.2.contains) = true) (name : String) :
    (∀ s ∈ (RewriteCheck.eqPass st.tables (st.passEnv env name).frontend).1,
        s ∈ (pipelineEq env).1) ∧
      ∀ s ∈ (RewriteCheck.eqPass st.tables (st.passEnv env name).frontend).2,
        s ∈ (pipelineEq env).2 := by
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true, h.2.2.2.2] at heq
  simp only [pipelineEq, RewriteCheck.eqPass, VState.passEnv, List.mem_append] at heq ⊢
  refine ⟨fun s hs => hs.elim (fun hs => ?_) .inr, fun s hs => hs.elim (fun hs => ?_) .inr⟩
  · exact List.mem_append.1 (List.contains_iff_mem.1 (heq.1 s hs))
  · exact List.mem_append.1 (List.contains_iff_mem.1 (heq.2 s hs))

theorem runPass_inv {st st' : VState} {p : StockPass} (hp : stepSound p.step) (h : Inv env f0 st)
    (hr : runPass env st p = .ok st') : Inv env f0 st' := by
  rcases p with ⟨name, required, simd, disabled, step, full⟩
  unfold runPass at hr
  simp only at hr
  split at hr
  · cases hr
  · cases hr; exact h
  · cases step with
    | stock run =>
      simp only at hr
      split at hr
      · cases hr
      · cases hr; exact h.continue (fun hn => by cases hn)
    | proven run rel guard =>
      simp only at hr
      split at hr
      · cases hr; exact h.skip _ _
      · next hwhy =>
        split at hr
        · cases hr
        · next out hrun =>
          cases full with
          | none =>
            cases hr
            refine h.continue (fun hn hg => ?_)
            rw [hn] at hwhy
            simp only [Bool.not_eq_true'] at hn
            have hwf : st.wf = true := by
              cases hw : st.wf <;> simp_all
            have hgd : guard (st.passEnv env name) st.func = true := by
              cases hgd : guard (st.passEnv env name) st.func <;> simp_all
            have hd : NilCheck.dictParams st.tables st.func = st.dict := by
              by_cases hd : NilCheck.dictParams st.tables st.func = st.dict
              · exact hd
              · simp_all
            have hro : (RewriteCheck.roSyms st.tables st.func).all st.ro.contains = true := by
              by_cases hro : (RewriteCheck.roSyms st.tables st.func).all st.ro.contains = true
              · exact hro
              · simp_all
            have heq : ((RewriteCheck.eqSyms st.tables).1.all st.eq.1.contains &&
                (RewriteCheck.eqSyms st.tables).2.all st.eq.2.contains) = true := by
              by_cases heq : ((RewriteCheck.eqSyms st.tables).1.all st.eq.1.contains &&
                  (RewriteCheck.eqSyms st.tables).2.all st.eq.2.contains) = true
              · exact heq
              · simp_all
            exact relHolds_toV (hd.trans h.2.2.1) (roPass_sub h hro name) (eqPass_sub h heq name)
              (hp _ _ _ _ _ hrun (h.2.1 hwf) hg hgd)
          | some fp =>
            simp only at hr
            split at hr
            · cases hr
            · split at hr
              · cases hr
                refine h.continue (fun hn hg => ?_)
                rw [hn] at hwhy
                simp only [Bool.not_eq_true'] at hn
                have hwf : st.wf = true := by
                  cases hw : st.wf <;> simp_all
                have hgd : guard (st.passEnv env name) st.func = true := by
                  cases hgd : guard (st.passEnv env name) st.func <;> simp_all
                have hd : NilCheck.dictParams st.tables st.func = st.dict := by
                  by_cases hd : NilCheck.dictParams st.tables st.func = st.dict
                  · exact hd
                  · simp_all
                have hro : (RewriteCheck.roSyms st.tables st.func).all st.ro.contains = true := by
                  by_cases hro : (RewriteCheck.roSyms st.tables st.func).all st.ro.contains = true
                  · exact hro
                  · simp_all
                have heq : ((RewriteCheck.eqSyms st.tables).1.all st.eq.1.contains &&
                    (RewriteCheck.eqSyms st.tables).2.all st.eq.2.contains) = true := by
                  by_cases heq : ((RewriteCheck.eqSyms st.tables).1.all st.eq.1.contains &&
                      (RewriteCheck.eqSyms st.tables).2.all st.eq.2.contains) = true
                  · exact heq
                  · simp_all
                exact relHolds_toV (hd.trans h.2.2.1) (roPass_sub h hro name) (eqPass_sub h heq name)
                  (hp _ _ _ _ _ hrun (h.2.1 hwf) hg hgd)
              · cases hr; exact h.continue (fun hn => by cases hn)

theorem runPasses_inv : ∀ {ps : List StockPass} {st st' : VState},
    (∀ p ∈ ps, stepSound p.step) → Inv env f0 st → runPasses env ps st = .ok st' → Inv env f0 st'
  | [], _, _, _, h, hr => by cases hr; exact h
  | p :: ps, st, st', hs, h, hr => by
    unfold runPasses at hr
    split at hr
    · cases hr
    · next st1 h1 =>
      exact runPasses_inv (fun q hq => hs q (List.mem_cons_of_mem _ hq))
        (runPass_inv (hs p List.mem_cons_self) h h1) hr

/-- **The verified pipeline refines its input**: when `verifiedPipeline` (from any start pass)
returns a `verified` state, its function (with its tables) refines the input `f` (with the
environment's tables) on every environment and input in `VPre` (with `f`'s dictionary
parameters and read-only symbols, and the descriptor symbols of the environment's tables and
frontend tables, `pipelineEq`). -/
theorem verifiedPipeline_refines {env : PassEnv} {f : Func} {start : Nat} {zv : Array (ID × Nat)}
    {r : VState} (h : verifiedPipeline env f start zv = .ok r) (hv : r.verified = true) :
    VRefines (NilCheck.dictParams env.tables f) (pipelineRo env f)
      (pipelineEq env) r.tables r.func env.tables f :=
  (runPasses_inv (fun p hp => stockPasses_sound p (List.mem_of_mem_drop hp)) (Inv.init zv) h).1 hv

end GoFV.Proof.Pipeline
