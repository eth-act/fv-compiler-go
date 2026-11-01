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
import GoFV.Proof.TabsAgree

/-!
# The verified generic pipeline refines its input (issue #189)

The pass theorems conclude four relations: `Refines`, `RefinesUnder Env.Mono` (passes that
rewrite call arguments rely on monotone contracts), `RefinesFrom (FrameSafe ∧ InitAvoids)`
(dead auto elim) and `RefinesFrom (RwPre tabs f)` (the checked rewrite passes: monotone
contracts, malloc-family contracts that return non-nil pointers, non-nil dictionary arguments of
the pass input `f`; issue #151). All four imply `VRefines k := RefinesFrom (VPre k)`, where
`VPre k` is their conjunction with the input's dictionary parameters `k` (`relHolds_toV`; the
pipeline runs a proven pass only on states whose dictionary parameters are the input's,
`VState.dict`), and `VRefines k` composes (`RefinesFrom.trans`).

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
temporary and non-nil dictionary arguments. -/
def VPre (k : List Nat) (env : Env) (args : List Val) (mem : Mem) : Prop :=
  env.Mono ∧ env.FrameSafe ∧ InitAvoids env args mem ∧ env.AllocNonNil ∧ DictArgs k args

/-- The refinement the verified pipeline establishes. -/
abbrev VRefines (k : List Nat) (tabs' : Tables) (f' : Func) (tabs : Tables) (f : Func) : Prop :=
  RefinesFrom (VPre k) tabs' f' tabs f

variable {k : List Nat} {tabs tabs' : Tables} {f f' : Func}

theorem Refines.toV (h : Refines tabs' f' tabs f) : VRefines k tabs' f' tabs f :=
  Refines.from (VPre k) h

theorem RefinesUnder.toV (h : RefinesUnder Env.Mono tabs' f' tabs f) : VRefines k tabs' f' tabs f :=
  RefinesFrom.mono (fun _ _ _ hp => hp.1) h.from

theorem RefinesFrom.frameSafe_toV
    (h : RefinesFrom (fun env args mem => env.FrameSafe ∧ InitAvoids env args mem) tabs' f' tabs f) :
    VRefines k tabs' f' tabs f :=
  RefinesFrom.mono (fun _ _ _ hp => ⟨hp.2.1, hp.2.2.1⟩) h

theorem RefinesFrom.rw_toV (hk : NilCheck.dictParams tabs f = k)
    (h : RefinesFrom (Pass.Rewrite.RwPre tabs f) tabs' f' tabs f) : VRefines k tabs' f' tabs f :=
  RefinesFrom.mono (fun _ _ _ hp => ⟨hp.1, hp.2.2.2.1, by rw [hk]; exact hp.2.2.2.2⟩) h

/-- The relation a `Rel` names. -/
def relHolds : Rel → Tables → Func → Tables → Func → Prop
  | .refines => Refines
  | .mono => RefinesUnder Env.Mono
  | .frameSafe => RefinesFrom (fun env args mem => env.FrameSafe ∧ InitAvoids env args mem)
  | .rw => fun tabs' f' tabs f => RefinesFrom (Pass.Rewrite.RwPre tabs f) tabs' f' tabs f

/-- Each pass relation implies the pipeline's, for an input with dictionary parameters `k`. -/
theorem relHolds_toV (hk : NilCheck.dictParams tabs f = k) :
    {r : Rel} → relHolds r tabs' f' tabs f → VRefines k tabs' f' tabs f
  | .refines, h => Refines.toV h
  | .mono, h => RefinesUnder.toV h
  | .frameSafe, h => RefinesFrom.frameSafe_toV h
  | .rw, h => RefinesFrom.rw_toV hk h

/-- A `proven` step's theorem: the result relates to the input when both pass `check` and the
guard accepts the input. -/
def stepSound : Verified.Step → Prop
  | .proven run rel guard => ∀ (penv : PassEnv) (f : Func) (out : PassOut) (ce ce' : CheckEnv),
      run penv f = .ok out → check ce f = .ok () → check ce' out.func = .ok () →
      guard penv f = true → relHolds rel out.tables out.func penv.tables f
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
  · trivial
  · trivial
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
  · trivial
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
  · trivial
  -- check bce
  · exact fun _ _ _ _ _ h _ _ _ => checkbce_refines h
  -- dse
  · exact fun _ _ _ _ _ h hf hg hd => DSE.dse_refines h hf hg hd
  -- memcombine
  · exact fun _ _ _ _ _ h hf hg _ => MemCombine.memcombine_refines h hf hg
  · trivial
  · trivial
  · trivial
  · trivial

/-! ## The pipeline -/

/-- The invariant of the pipeline's states from input `f0`: a verified state refines the
input, `wf` means the state passes `check`, and the state records the input's dictionary
parameters. -/
def Inv (env : PassEnv) (f0 : Func) (st : VState) : Prop :=
  (st.verified = true → VRefines (NilCheck.dictParams env.tables f0) st.tables st.func env.tables f0) ∧
  (st.wf = true → check (checkEnv env st.tables) st.func = .ok ()) ∧
  st.dict = NilCheck.dictParams env.tables f0

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
  ⟨fun _ => Refines.toV (Refines.refl _ _), ok_of_toBool, rfl⟩

theorem Inv.skip {st : VState} (h : Inv env f0 st) (name why : String) :
    Inv env f0 (st.skip name why) := h

theorem Inv.adopt {st : VState} (h : Inv env f0 st) {name : String} {out : PassOut} {wf : Bool}
    {v : Verdict}
    (hv : v.ok = true → VRefines (NilCheck.dictParams env.tables f0) out.tables out.func st.tables st.func)
    (hwf : wf = true → check (checkEnv env out.tables) out.func = .ok ()) :
    Inv env f0 (st.adopt name out wf v) := by
  refine ⟨fun hver => ?_, hwf, h.2.2⟩
  simp only [VState.adopt, Bool.and_eq_true] at hver
  exact RefinesFrom.trans (h.1 hver.1) (hv hver.2)

theorem Inv.continue {st : VState} (h : Inv env f0 st) {p : StockPass} {out : PassOut}
    {claim : Option String}
    (hc : claim = none → check (checkEnv env out.tables) out.func = .ok () →
      VRefines (NilCheck.dictParams env.tables f0) out.tables out.func st.tables st.func) :
    Inv env f0 (st.continue env p out claim) := by
  unfold VState.continue
  by_cases hs : st.same out = true
  · obtain ⟨hf, ht⟩ := VState.same_eq hs
    simp only [hs, ↓reduceIte]
    refine h.adopt (fun _ => ?_) (fun hw => ?_)
    · rw [hf, ht]; exact Refines.toV (Refines.refl _ _)
    · rw [hf, ht]; exact h.2.1 hw
  · simp only [hs, ↓reduceIte, Bool.false_eq_true]
    have hwf := @ok_of_toBool _ (check (checkEnv env out.tables) out.func)
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

theorem runPass_inv {st st' : VState} {p : StockPass} (hp : stepSound p.step) (h : Inv env f0 st)
    (hr : runPass env st p = .ok st') : Inv env f0 st' := by
  rcases p with ⟨name, required, simd, disabled, step⟩
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
          exact relHolds_toV (hd.trans h.2.2) (hp _ _ _ _ _ hrun (h.2.1 hwf) hg hgd)

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
parameters). -/
theorem verifiedPipeline_refines {env : PassEnv} {f : Func} {start : Nat} {zv : Array (ID × Nat)}
    {r : VState} (h : verifiedPipeline env f start zv = .ok r) (hv : r.verified = true) :
    VRefines (NilCheck.dictParams env.tables f) r.tables r.func env.tables f :=
  (runPasses_inv (fun p hp => stockPasses_sound p (List.mem_of_mem_drop hp)) (Inv.init zv) h).1 hv

end GoFV.Proof.Pipeline
