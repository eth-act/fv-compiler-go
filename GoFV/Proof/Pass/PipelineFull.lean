import GoFV.Opt.VerifiedFull
import GoFV.Proof.Pass.Pipeline
import GoFV.Proof.RefineSched
import GoFV.Proof.Low.Lower
import GoFV.Proof.Low.TabsAgreeL
import GoFV.Proof.Pass.TightenL
import GoFV.Proof.Pass.CSELPass
import GoFV.Proof.Pass.UnreadL
import GoFV.Proof.Pass.TupleSelL
import GoFV.Proof.Pass.DeadcodePassL
import GoFV.Proof.Pass.LowCong
import GoFV.Proof.Pass.LicmL
import GoFV.Proof.Pass.CopyElimPassL
import GoFV.Proof.Pass.CriticalL
import GoFV.Proof.Pass.PhiTightenL
import GoFV.Proof.Pass.NilLateL
import GoFV.Proof.Pass.SchedLPass
import GoFV.Proof.Pass.FlagAllocL
import GoFV.Proof.Pass.LateLowerL
import GoFV.Proof.Pass.PairL
import GoFV.Proof.Pass.LoopRotateLoc
import GoFV.Proof.Pass.TrimLoc
import GoFV.Proof.Regalloc.Sound
import GoFV.Proof.TabsAgreeModL

variable [GoFV.SSA.Sem.Addrs]

/-!
# The verified pipeline through `trim` refines its input (issues #385, #189)

The pass theorems from `lower` on relate two runners each (`docs/plans/semantics2.md` §2):
`run`/`runL` (`lower`), `runL`/`runL` (`lower` … `layout`), `runL`/`runSched` (`schedule`,
against `runLF` on the inputs whose pointer-shaped parameter pieces and checked pointer-shaped
values read nil or pointers that are not wild, `ArgPtrsOK` and `NilPtrsOK`; on those where `runL` and `runLF` agree as well, `NoNilFault`, a `runL`
refinement), `runSched`/`runSched` (`late nilcheck`), `runSched`/`runLoc` (`regalloc`) and
`runLoc`/`runLoc` (`loop rotate`, `trim`). `LayerRefines P lt tabs' f' ls tabs f` is the one
relation with the runner of each side given by its `Layer` (`layerRun`); `RefinesFrom`,
`RefinesLFrom`, `RefinesSchedLFrom`, `RefinesSchedFrom`, `RefinesLSFrom` and `RefinesLocFrom`
are its instances, and it composes (`LayerRefines.trans`).

`regalloc`'s theorem `checkRA_sound` runs both sides in the `regalloc` section's tables; the
source ran in the `flagalloc` section's. `runSched_tabsAgreeL`: when `tabsAgreeL` holds (Phase 1's
`tabsAgree` and the lowered shapes of the function's values), the source runs alike in both;
`runSched_tabsAgreeModL`: so it does when `tabsAgreeModL` holds (the output tables add the autos
of new spill slots), for inputs and contracts with `InitAvoids`, `TempOblivious`, `FrameSafe`.

`loweredVPasses_sound`: every `proven` step of `GoFV.Opt.loweredVPasses` satisfies its theorem
(`stepSoundL`). `verifiedPipelineFull_layer`: a `verified` result of `verifiedPipelineFull`
refines the input across the layers, under `PreFull`: Phase 1's `VPre`, and `NoNilFault`,
`ArgPtrsOK` and `NilPtrsOK` of the recorded `schedule` inputs. `verifiedPipelineFull_refines`: for a
`fullyVerified` result, every returning or panicking `run` of the input is, up to refinement, a
`runLoc` of the result.
-/

namespace GoFV.Proof.PipelineFull

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.Verified GoFV.Proof GoFV.Proof.Pipeline

/-! ## One refinement across the layers -/

/-- The semantics of a layer. -/
def layerRun : Layer → Env → Tables → Func → List Val → Mem → Nat → Outcome
  | .gen => GoFV.SSA.run
  | .low => GoFV.SSA.runL
  | .sched => GoFV.SSA.runSched
  | .loc => GoFV.SSA.runLoc

/-- `f'` (tables `tabs'`, run as layer `lt`) refines `f` (tables `tabs`, run as layer `ls`), for
the inputs with `P`. -/
def LayerRefines (P : Env → List Val → Mem → Prop) (lt : Layer) (tabs' : Tables) (f' : Func)
    (ls : Layer) (tabs : Tables) (f : Func) : Prop :=
  ∀ (env : Env) (args : List Val) (mem : Mem), P env args mem → ∀ (fuel : Nat),
    (layerRun ls env tabs f args mem fuel).Defined →
      ∃ fuel', OutcomeRefines 0 (layerRun ls env tabs f args mem fuel)
        (layerRun lt env tabs' f' args mem fuel')

theorem LayerRefines.refl (P : Env → List Val → Mem → Prop) (l : Layer) (tabs : Tables)
    (f : Func) : LayerRefines P l tabs f l tabs f :=
  fun _ _ _ _ fuel h => ⟨fuel, OutcomeRefines.refl h⟩

theorem LayerRefines.trans {P : Env → List Val → Mem → Prop} {l1 l2 l3 : Layer}
    {t1 t2 t3 : Tables} {f1 f2 f3 : Func} (h12 : LayerRefines P l2 t2 f2 l1 t1 f1)
    (h23 : LayerRefines P l3 t3 f3 l2 t2 f2) : LayerRefines P l3 t3 f3 l1 t1 f1 := by
  intro env args mem hP fuel h
  obtain ⟨fuel2, h2⟩ := h12 env args mem hP fuel h
  obtain ⟨fuel3, h3⟩ := h23 env args mem hP fuel2 h2.defined_right
  exact ⟨fuel3, h2.trans h3⟩

theorem LayerRefines.mono {P Q : Env → List Val → Mem → Prop} {lt ls : Layer} {tabs tabs' : Tables}
    {f f' : Func} (hPQ : ∀ env args mem, Q env args mem → P env args mem)
    (h : LayerRefines P lt tabs' f' ls tabs f) : LayerRefines Q lt tabs' f' ls tabs f :=
  fun env args mem hQ => h env args mem (hPQ env args mem hQ)

/-! ## `regalloc`'s tables -/

section
open GoFV.Proof.TabsAgree

/-- **A scheduled function runs alike in tables that agree on it** (`tabsAgreeL`): `runSched`
reads the tables as `runL` does, and its schedule order depends only on the lowered shapes of the
values (`Ctx.makeSched`). -/
theorem runSched_tabsAgreeL {tabs tabs' : Tables} {f : Func}
    (h : LowerCheck.tabsAgreeL tabs tabs' f = true) (env : Env) (args : List Val) (mem : Mem)
    (fuel : Nat) : runSched env tabs' f args mem fuel = runSched env tabs f args mem fuel := by
  unfold LowerCheck.tabsAgreeL at h
  rw [Bool.and_eq_true] at h
  obtain ⟨ha, hs⟩ := h
  have A := tabsAgree_sound ha
  have hmap : f.valueTab.map (valueTy (typeShapesL tabs')) =
      f.valueTab.map (valueTy (typeShapesL tabs)) :=
    Array.map_congr_left fun o ho => Ty.eq_of_beq (List.all_eq_true.mp hs o (Array.mem_def.mp ho))
  have hctxL : Ctx.makeL tabs' f = { Ctx.makeL tabs f with tabs := tabs' } := by
    unfold Ctx.makeL
    by_cases hl : f.lowered = true
    · simp only [hl, ite_true, A.ctx, hmap]
    · simp only [hl, Bool.false_eq_true, ite_false, A.ctx]
  have hctx : Ctx.makeSched tabs' f = { Ctx.makeSched tabs f with tabs := tabs' } := by
    unfold Ctx.makeSched
    rw [hctxL]
  have hc : (Ctx.makeSched tabs f).tabs = tabs := by
    unfold Ctx.makeSched Ctx.makeL; split <;> rfl
  have hf : (Ctx.makeSched tabs f).f = f := by
    unfold Ctx.makeSched Ctx.makeL; split <;> rfl
  have hval : ∀ id v, (Ctx.makeSched tabs f).f.value? id = some v →
      AuxAgree (Ctx.makeSched tabs f).tabs tabs' v.aux := by
    intro id v hv; rw [hf] at hv; rw [hc]; exact A.value id v hv
  have hloc : (Ctx.makeSched tabs f).locals = (Ctx.make tabs f).locals := by
    unfold Ctx.makeSched Ctx.makeL; split <;> rfl
  show runCtxL _ env (Ctx.makeSched tabs' f) args mem fuel =
    runCtxL _ env (Ctx.makeSched tabs f) args mem fuel
  rw [hctx]
  exact Low.runCtxL_tabs hval _ env (by rw [hc]; exact A.outargs)
    (by rw [hloc, hc]; exact A.forgeable) args mem fuel

end

/-! ## The lowered steps -/

/-- The precondition of a lowered pass theorem on input `f` in `tabs` with output `f'`. -/
def lrelPre : LRel → Tables → Func → Func → Env → List Val → Mem → Prop
  | .lower, tabs, f, _ => fun env _ mem =>
    env.Mono ∧ RoImage (LowerCheck.roPre tabs (LowerCheck.invUnknown f)) env mem
  | .lowFrame, _, _, _ => fun env args mem => env.FrameSafe ∧ InitAvoids env args mem
  | .sched, tabs, f, f' => fun env args mem =>
    NoNilFault tabs f env args mem ∧ ArgPtrsOK tabs f env args mem ∧
      NilPtrsOK tabs f env args mem ∧ NilHoistOK tabs f f' env args mem
  | .ls, _, _, _ => fun env args mem =>
    env.TempOblivious ∧ env.FrameSafe ∧ InitAvoids env args mem
  | _, _, _, _ => fun _ _ _ => True

/-- The relation an `LRel` names. -/
def lrelHolds (r : LRel) (tabs' : Tables) (f' : Func) (tabs : Tables) (f : Func) : Prop :=
  LayerRefines (lrelPre r tabs f f') r.tgt tabs' f' r.src tabs f

/-- A `proven` step's theorem: its relation ends in the pass's layer, and the result relates to
the input when both pass `check` (if the step asks for it) and the guard accepts. -/
def stepSoundL (p : LPass) : Prop :=
  match p.step with
  | .proven run rel wf guard => rel.tgt = p.out ∧
      ∀ (penv : PassEnv) (f : Func) (out : PassOut), run penv f = .ok out →
        (wf = true → check (checkEnv penv penv.tables) f = .ok () ∧
          check (checkEnv penv out.tables) out.func = .ok ()) →
        guard penv f out = true → lrelHolds rel out.tables out.func penv.tables f
  | .stock _ => True

private theorem low_of {tabs tabs' : Tables} {f f' : Func} (h : RefinesL tabs' f' tabs f) :
    lrelHolds .low tabs' f' tabs f :=
  fun env args mem _ => h env args mem

private theorem loc_of {tabs tabs' : Tables} {f f' : Func} (h : RefinesLoc tabs' f' tabs f) :
    lrelHolds .loc tabs' f' tabs f :=
  fun env args mem _ => h env args mem

private theorem ok_of_toBoolF {ε : Type} {e : Except ε Unit} (h : e.toBool = true) : e = .ok () := by
  revert h; cases e <;> simp [Except.toBool]

theorem deadcodeStepL_sound (p : LPass) (hs : p.step = deadcodeStepL) (ho : p.out = .low) :
    stepSoundL p := by
  unfold stepSoundL
  rw [hs]
  refine ⟨ho.symm, fun penv f out h hw hg => ?_⟩
  simp only [deadGuardL, Bool.and_eq_true, beq_iff_eq] at hg
  obtain ⟨hf, hg'⟩ := hw rfl
  exact low_of (Dead.deadcode_refinesL h hf hg' (Dead.deadFrag_of hg.1.1) hg.2
    (Dead.deadFragL_of hg.1.2))

/-- **Every proven step of the lowered pass table satisfies its theorem.** -/
theorem loweredVPasses_sound : ∀ p ∈ loweredVPasses.toList, stepSoundL p := by
  intro p hp
  simp only [loweredVPasses, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  -- lower
  · refine ⟨rfl, fun penv f out h _ hg => ?_⟩
    simp only [lowerGuard, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hg
    intro env args mem hM fuel hd
    exact Low.lower_refines_runU h hg.1 hg.2 hM.1 hM.2 hd
  -- addressing modes
  · exact ⟨rfl, fun _ _ _ h _ _ => low_of (addressingModes_refinesL h)⟩
  -- late lower
  · exact ⟨rfl, fun _ _ _ h _ hg => low_of (LateLowerL.lateLower_refinesL h hg)⟩
  -- pair
  · refine ⟨rfl, fun penv f out h hw hg => ?_⟩
    obtain ⟨hf, hg'⟩ := hw rfl
    exact low_of (MoveL.pair_refinesL h hf hg' hg)
  -- lowered deadcode for cse
  · exact deadcodeStepL_sound _ rfl rfl
  -- lowered cse
  · refine ⟨rfl, fun penv f out h hw hg => ?_⟩
    obtain ⟨hf, hg'⟩ := hw rfl
    exact low_of (CSEL.loweredCse_refinesL h hf hg' hg)
  -- elim unread autos
  · refine ⟨rfl, fun penv f out h hw hg => ?_⟩
    obtain ⟨hf, hg'⟩ := hw rfl
    exact UnreadL.elimUnreadAutos_refinesL h hf hg' hg
  -- tighten tuple selectors
  · refine ⟨rfl, fun penv f out h hw hg => ?_⟩
    obtain ⟨hf, hg'⟩ := hw rfl
    exact low_of (MoveL.tightenTupleSelectors_refinesL h hf hg' hg)
  -- lowered deadcode
  · exact deadcodeStepL_sound _ rfl rfl
  -- checkLower
  · exact ⟨rfl, fun _ _ _ h _ _ => low_of (checkLower_refinesL h)⟩
  -- loop invariant
  · refine ⟨rfl, fun penv f out h hw hg => ?_⟩
    obtain ⟨hf, hg'⟩ := hw rfl
    simp only [licmGuard, Bool.and_eq_true] at hg
    exact low_of (MoveL.licm_refinesL h hf hg' (checkOK_sound hg.1.1) hg.1.2 hg.2)
  -- late phielim and copyelim
  · refine ⟨rfl, fun penv f out h hw hg => ?_⟩
    obtain ⟨hf, hg'⟩ := hw rfl
    simp only [copyGuardL, Bool.and_eq_true, beq_iff_eq] at hg
    exact low_of (CopyElim.copyelim_refinesL h hf hg' (CopyElim.copyFrag_sound hg.1.1.1)
      (CopyElim.emptyFrag_of hg.1.1.2) hg.1.2 (CopyElim.copyLFrag_of hg.2))
  -- tighten
  · refine ⟨rfl, fun penv f out h hw hg => ?_⟩
    obtain ⟨hf, hg'⟩ := hw rfl
    exact low_of (MoveL.tighten_refinesL h hf hg' hg)
  -- late deadcode
  · exact deadcodeStepL_sound _ rfl rfl
  -- critical
  · refine ⟨rfl, fun penv f out h hw hg => ?_⟩
    exact low_of (Crit.critical_refinesL h (hw rfl).1 hg)
  -- phi tighten
  · refine ⟨rfl, fun penv f out h hw hg => ?_⟩
    obtain ⟨hf, hg'⟩ := hw rfl
    exact low_of (MoveL.phiTighten_refinesL h hf hg' hg)
  -- likelyadjust, layout
  · exact ⟨rfl, fun _ _ _ h _ _ => low_of (likelyadjust_refinesL h)⟩
  · exact ⟨rfl, fun _ _ _ h _ _ => low_of (layout_refinesL h)⟩
  -- schedule
  · refine ⟨rfl, fun penv f out h hw hg => ?_⟩
    exact SchedL.schedule_refinesSchedL h (hw rfl).1 hg
  -- late nilcheck
  · refine ⟨rfl, fun penv f out h hw hg => ?_⟩
    exact fun env args mem _ => NilLateL.nilcheckelim2_refinesSched h (hw rfl).1 hg env args mem
  -- flagalloc
  · refine ⟨rfl, fun penv f out h hw hg => ?_⟩
    exact fun env args mem _ => FlagAllocL.flagalloc_refinesSched h (hw rfl).1 hg env args mem
  -- regalloc
  · refine ⟨rfl, fun penv f out _ _ hg => ?_⟩
    simp only [regallocGuard, Bool.and_eq_true, Bool.or_eq_true] at hg
    obtain ⟨hta, hra⟩ := hg
    have R := RA.checkRA_sound (ok_of_toBoolF hra)
    intro env args mem hpre fuel hd
    change (runSched env penv.tables f args mem fuel).Defined at hd
    show ∃ fuel', OutcomeRefines 0 (runSched env penv.tables f args mem fuel)
      (runLoc env out.tables out.func args mem fuel')
    rcases hta with hta | hta
    · rw [← runSched_tabsAgreeL hta] at hd ⊢
      exact R env args mem fuel hd
    · obtain ⟨hE, hfs, hinit⟩ := hpre
      have h1 := runSched_tabsAgreeModL hta hE hfs hinit hd
      obtain ⟨fuel', h2⟩ := R env args mem fuel h1.defined_right
      exact ⟨fuel', h1.trans h2⟩
  -- loop rotate
  · exact ⟨rfl, fun _ _ _ h _ _ => loc_of (loopRotate_refinesLoc h)⟩
  -- trim
  · exact ⟨rfl, fun _ _ _ h _ hg => loc_of (trim_refinesLoc h hg)⟩

/-- The table's passes are `compile.go`'s from `lower` to `trim`, in order. -/
theorem loweredVPasses_names : loweredVPasses.map (·.name) = loweredPasses := by
  simp [loweredVPasses, loweredPasses]

/-! ## The pipeline -/

/-- The precondition of the end-to-end theorem: Phase 1's `VPre` for the input's dictionary
parameters `k` and read-only symbols `ro`, no nil-page fault of the `schedule` inputs `nnf`
(`NoNilFault`: `runL` and `runLF` of each agree), and their pointer-shaped parameter pieces
(`ArgPtrsOK`) and checked pointer-shaped values (`NilPtrsOK`) read nil or pointers that are not
wild, and so do the checked pointers that the `schedule` runs `nhs` (input, output) hoist above a
fault (`NilHoistOK`) (Go-level assumptions). -/
def PreFull (k : List Nat) (ro : List (String × Alloc)) (eq : List String × List String)
    (nnf : List (Tables × Func)) (nhs : List (Tables × Func × Func)) (env : Env) (args : List Val)
    (mem : Mem) : Prop :=
  VPre k ro eq env args mem ∧
    (∀ x ∈ nnf, NoNilFault x.1 x.2 env args mem ∧ ArgPtrsOK x.1 x.2 env args mem ∧
      NilPtrsOK x.1 x.2 env args mem) ∧
    ∀ x ∈ nhs, NilHoistOK x.1 x.2.1 x.2.2 env args mem

variable {env : PassEnv} {f0 : Func} {l0 : Layer}

/-- The invariant of the states from input `f0` (layer `l0`): a verified state refines the
input under `PreFull` of its `schedule` runs, `wf` means the state passes `check`, and the
state records the pipeline's read-only symbols. -/
def InvF (env : PassEnv) (f0 : Func) (l0 : Layer) (s : FState) : Prop :=
  (s.st.verified = true → LayerRefines (PreFull (NilCheck.dictParams env.tables f0)
    (pipelineRo env f0) (pipelineEq env) s.nnf s.nhs) s.layer s.st.tables s.st.func
    l0 env.tables f0) ∧
  (s.st.wf = true → check (checkEnv env s.st.tables) s.st.func = .ok ()) ∧
  s.st.ro = pipelineRo env f0

theorem PreFull.sub {k : List Nat} {ro : List (String × Alloc)} {eq : List String × List String}
    {n n' : List (Tables × Func)} {h h' : List (Tables × Func × Func)} (hn : ∀ x ∈ n, x ∈ n')
    (hh : ∀ x ∈ h, x ∈ h') {e : Env} {args : List Val} {mem : Mem}
    (hP : PreFull k ro eq n' h' e args mem) : PreFull k ro eq n h e args mem :=
  ⟨hP.1, fun x hx => hP.2.1 x (hn x hx), fun x hx => hP.2.2 x (hh x hx)⟩

theorem InvF.adopt {s : FState} (h : InvF env f0 l0 s) {p : LPass} {out : PassOut} {wf : Bool}
    {v : Verdict} {nnf : List (Tables × Func)} {nhs : List (Tables × Func × Func)}
    (hn : ∀ x ∈ s.nnf, x ∈ nnf) (hh : ∀ x ∈ s.nhs, x ∈ nhs)
    (hv : v.ok = true → LayerRefines (PreFull (NilCheck.dictParams env.tables f0)
      (pipelineRo env f0) (pipelineEq env) nnf nhs) p.out out.tables out.func
      s.layer s.st.tables s.st.func)
    (hwf : wf = true → check (checkEnv env out.tables) out.func = .ok ()) :
    InvF env f0 l0 (s.adopt p out wf v nnf nhs) := by
  refine ⟨fun hver => ?_, hwf, h.2.2⟩
  simp only [FState.adopt, VState.adopt, Bool.and_eq_true] at hver
  exact LayerRefines.trans ((h.1 hver.1).mono fun _ _ _ hp => hp.sub hn hh) (hv hver.2)

theorem InvF.skip {s : FState} (h : InvF env f0 l0 s) (p : LPass) (why : String) :
    InvF env f0 l0 (s.skip p why) := h

theorem outWf_sound {p : LPass} {out : PassOut} (h : outWf env p out = true) :
    check (checkEnv env out.tables) out.func = .ok () := by
  simp only [outWf, Bool.and_eq_true] at h
  exact ok_of_toBoolF h.2

/-- An unchanged result in the same layer is the identity. -/
theorem InvF.same {s : FState} (h : InvF env f0 l0 s) {p : LPass} {out : PassOut}
    (hs : (s.st.same out && s.layer == p.out) = true) :
    InvF env f0 l0 (s.adopt p out s.st.wf .identity s.nnf s.nhs) := by
  simp only [Bool.and_eq_true, beq_iff_eq] at hs
  obtain ⟨hf, ht⟩ := VState.same_eq hs.1
  refine h.adopt (fun _ hx => hx) (fun _ hx => hx) (fun _ => ?_) (fun hw => ?_)
  · rw [hf, ht, hs.2]; exact LayerRefines.refl _ _ _ _
  · rw [hf, ht]; exact h.2.1 hw

theorem InvF.next {s : FState} (h : InvF env f0 l0 s) {p : LPass} {out : PassOut}
    {bad : Bool → Option String} {nnf : List (Tables × Func)}
    {nhs : List (Tables × Func × Func)} (hn : ∀ x ∈ s.nnf, x ∈ nnf) (hh : ∀ x ∈ s.nhs, x ∈ nhs)
    (hb : ∀ wf, bad wf = none → (wf = true → check (checkEnv env out.tables) out.func = .ok ()) →
      LayerRefines (PreFull (NilCheck.dictParams env.tables f0) (pipelineRo env f0)
        (pipelineEq env) nnf nhs) p.out
        out.tables out.func s.layer s.st.tables s.st.func) :
    InvF env f0 l0 (s.next env p out bad nnf nhs) := by
  unfold FState.next
  split
  · next hs => exact h.same hs
  · dsimp only
    split
    · next hbad => exact h.adopt hn hh (fun _ => hb _ hbad outWf_sound) outWf_sound
    · split
      · exact h.adopt (fun _ hx => hx) (fun _ hx => hx) (fun hv => by cases hv) outWf_sound
      · exact h.skip _ _

/-- What `whyNot = none` gives. -/
theorem whyNot_none {s : FState} {penv : PassEnv} {rel : LRel} {wfReq : Bool}
    {guard : PassEnv → Func → PassOut → Bool} {out : PassOut} {wf : Bool}
    (h : s.whyNot penv rel wfReq guard out wf = none) :
    s.layer = rel.src ∧ (wfReq = true → s.st.wf = true ∧ wf = true) ∧
      guard penv s.st.func out = true ∧
      (rel = .lower → (LowerCheck.roPre s.st.tables (LowerCheck.invUnknown s.st.func)).all
        s.st.ro.contains = true) := by
  unfold FState.whyNot at h
  split at h
  · cases h
  · next h1 =>
    split at h
    · cases h
    · next h2 =>
      split at h
      · cases h
      · next h3 =>
        split at h
        · cases h
        · next h4 =>
          split at h
          · cases h
          · next h5 =>
            refine ⟨by simpa using h1, fun hw => ⟨?_, ?_⟩, by simpa using h4, fun hl => ?_⟩
            · simpa [hw] using h2
            · simpa [hw] using h3
            · simpa [hl] using h5

theorem pre_lrel {k : List Nat} {ro : List (String × Alloc)} {eq : List String × List String}
    {s : FState} (rel : LRel) {out : PassOut} {e : Env} {args : List Val} {mem : Mem}
    (hro : rel = .lower → ∀ x ∈ LowerCheck.roPre s.st.tables (LowerCheck.invUnknown s.st.func),
      x ∈ ro)
    (h : PreFull k ro eq (s.nnfAfter rel) (s.nhsAfter rel out) e args mem) :
    lrelPre rel s.st.tables s.st.func out.func e args mem := by
  cases rel with
  | lower => exact ⟨h.1.1, h.1.2.2.2.2.2.2.2.2.1.sub (hro rfl)⟩
  | lowFrame => exact ⟨h.1.2.1, h.1.2.2.1⟩
  | sched =>
    have hm : (s.st.tables, s.st.func) ∈ s.nnfAfter .sched := by
      unfold FState.nnfAfter
      exact List.mem_cons_self
    obtain ⟨h1, h2, h3⟩ := h.2.1 _ hm
    refine ⟨h1, h2, h3, ?_⟩
    cases hh : ScheduleCheck.hoistNeeded s.st.tables s.st.func out.func
    · exact nilHoistOK_of_noHoist hh e args mem
    · have hm' : (s.st.tables, s.st.func, out.func) ∈ s.nhsAfter .sched out := by
        unfold FState.nhsAfter
        simp only [hh]
        exact List.mem_cons_self
      exact h.2.2 _ hm'
  | ls => exact ⟨h.1.2.2.2.2.2.2.1, h.1.2.1, h.1.2.2.1⟩
  | low | schedS | loc => trivial

theorem nnfAfter_sub (s : FState) (rel : LRel) : ∀ x ∈ s.nnf, x ∈ s.nnfAfter rel := by
  intro x hx
  unfold FState.nnfAfter
  split
  · exact List.mem_cons_of_mem _ hx
  · exact hx

theorem nhsAfter_sub (s : FState) (rel : LRel) (out : PassOut) :
    ∀ x ∈ s.nhs, x ∈ s.nhsAfter rel out := by
  intro x hx
  unfold FState.nhsAfter
  split
  · exact List.mem_cons_of_mem _ hx
  · exact hx

theorem runPassL_inv {s s' : FState} {p : LPass} (hp : stepSoundL p) (h : InvF env f0 l0 s)
    (hr : runPassL env s p = .ok s') : InvF env f0 l0 s' := by
  rcases p with ⟨name, required, out, step, full⟩
  unfold runPassL at hr
  simp only at hr
  split at hr
  · cases hr
  · cases hr; exact h
  · cases step with
    | stock run =>
      simp only at hr
      split at hr
      · cases hr
      · cases hr
        split
        · next hs => exact h.same hs
        · exact h.adopt (fun _ hx => hx) (fun _ hx => hx) (fun hv => by cases hv) outWf_sound
    | proven run rel wfReq guard =>
      obtain ⟨htgt, hsound⟩ := hp
      simp only at hr
      split at hr
      · cases hr
      · next o hrun =>
        have key : ∀ wf, s.whyNot (s.passEnv env name) rel wfReq guard o wf = none →
            (wf = true → check (checkEnv env o.tables) o.func = .ok ()) →
            LayerRefines (PreFull (NilCheck.dictParams env.tables f0) (pipelineRo env f0)
              (pipelineEq env)
              (s.nnfAfter rel) (s.nhsAfter rel o)) out o.tables o.func s.layer s.st.tables
              s.st.func := by
          intro wf hw hwf
          obtain ⟨hl, hc, hg, hro⟩ := whyNot_none hw
          have R := hsound _ _ _ hrun
            (fun hreq => ⟨h.2.1 (hc hreq).1, hwf (hc hreq).2⟩) hg
          simp only at htgt
          rw [← htgt, hl]
          exact R.mono fun _ _ _ hP => pre_lrel rel (fun hr => h.2.2 ▸ ro_sub (hro hr)) hP
        cases full with
        | none =>
          cases hr
          exact h.next (nnfAfter_sub s rel) (nhsAfter_sub s rel o) key
        | some fp =>
          simp only at hr
          split at hr
          · cases hr
          · split at hr
            · cases hr
              exact h.next (nnfAfter_sub s rel) (nhsAfter_sub s rel o) key
            · cases hr
              exact h.adopt (fun _ hx => hx) (fun _ hx => hx) (fun hv => by cases hv) outWf_sound

theorem runPassesL_inv : ∀ {ps : List LPass} {s s' : FState},
    (∀ p ∈ ps, stepSoundL p) → InvF env f0 l0 s → runPassesL env ps s = .ok s' → InvF env f0 l0 s'
  | [], _, _, _, h, hr => by cases hr; exact h
  | p :: ps, s, s', hs, h, hr => by
    unfold runPassesL at hr
    split at hr
    · cases hr
    · next s1 h1 =>
      exact runPassesL_inv (fun q hq => hs q (List.mem_cons_of_mem _ hq))
        (runPassL_inv (hs p List.mem_cons_self) h h1) hr

/-- A pass records a `schedule` run in `nhs` only when it hoists a checked pointer above a fault
(`ScheduleCheck.hoistNeeded`). -/
theorem runPassL_nhs {s s' : FState} {p : LPass}
    (h : ∀ x ∈ s.nhs, ScheduleCheck.hoistNeeded x.1 x.2.1 x.2.2 = true)
    (hr : runPassL env s p = .ok s') :
    ∀ x ∈ s'.nhs, ScheduleCheck.hoistNeeded x.1 x.2.1 x.2.2 = true := by
  have hA : ∀ (rel : LRel) (o : PassOut), ∀ x ∈ s.nhsAfter rel o,
      ScheduleCheck.hoistNeeded x.1 x.2.1 x.2.2 = true := by
    intro rel o x hx
    unfold FState.nhsAfter at hx
    split at hx
    · next hc =>
      rcases List.mem_cons.1 hx with rfl | hx
      · simp only [Bool.and_eq_true] at hc; exact hc.2
      · exact h x hx
    · exact h x hx
  have hN : ∀ {q : LPass} {o : PassOut} {bad : Bool → Option String} {n : List (Tables × Func)}
      {nh : List (Tables × Func × Func)},
      (∀ x ∈ nh, ScheduleCheck.hoistNeeded x.1 x.2.1 x.2.2 = true) →
      ∀ x ∈ (s.next env q o bad n nh).nhs, ScheduleCheck.hoistNeeded x.1 x.2.1 x.2.2 = true := by
    intro q o bad n nh hnh x hx
    unfold FState.next at hx
    split at hx
    · exact h x hx
    · dsimp only at hx
      split at hx
      · exact hnh x hx
      · split at hx
        · exact h x hx
        · exact h x hx
  rcases p with ⟨name, required, out, step, full⟩
  unfold runPassL at hr
  simp only at hr
  split at hr
  · cases hr
  · cases hr; exact h
  · cases step with
    | stock run =>
      simp only at hr
      split at hr
      · cases hr
      · cases hr
        split <;> exact h
    | proven run rel wfReq guard =>
      simp only at hr
      split at hr
      · cases hr
      · next o hrun =>
        cases full with
        | none => cases hr; exact hN (hA rel o)
        | some fp =>
          simp only at hr
          split at hr
          · cases hr
          · split at hr
            · cases hr; exact hN (hA rel o)
            · cases hr; exact h

theorem runPassesL_nhs : ∀ {ps : List LPass} {s s' : FState},
    (∀ x ∈ s.nhs, ScheduleCheck.hoistNeeded x.1 x.2.1 x.2.2 = true) →
    runPassesL env ps s = .ok s' → ∀ x ∈ s'.nhs, ScheduleCheck.hoistNeeded x.1 x.2.1 x.2.2 = true
  | [], _, _, h, hr => by cases hr; exact h
  | p :: ps, s, s', h, hr => by
    unfold runPassesL at hr
    split at hr
    · cases hr
    · next s1 h1 => exact runPassesL_nhs (runPassL_nhs h h1) hr

/-- **`nhs` records only the `schedule` runs that hoist a checked pointer above a fault**
(`ScheduleCheck.hoistNeeded`): for a function whose `schedule` run needs no such swap, `r.nhs`
is empty and `NilHoistOK` assumes nothing. -/
theorem verifiedPipelineFull_nhs {env : PassEnv} {f : Func} {start : Nat}
    {zv : Array (ID × Nat)} {dcl : Nat} {r : FState}
    (h : verifiedPipelineFull env f start zv dcl = .ok r) :
    ∀ x ∈ r.nhs, ScheduleCheck.hoistNeeded x.1 x.2.1 x.2.2 = true := by
  unfold verifiedPipelineFull at h
  split at h
  · cases h
  · exact runPassesL_nhs (fun _ hx => by simp at hx) h

/-- **The verified pipeline through `trim` refines its input across the layers**: when
`verifiedPipelineFull` (from any start pass) returns a `verified` state, its function, run in its
layer, refines the input `f` run in the layer of the start pass (`startLayer`), on every
environment and input in `PreFull` (Phase 1's `VPre` with `f`'s dictionary parameters and
read-only symbols and the pipeline's descriptor symbols, `pipelineEq`, and no nil-page fault of
the `schedule` inputs the result records). -/
theorem verifiedPipelineFull_layer {env : PassEnv} {f : Func} {start : Nat}
    {zv : Array (ID × Nat)} {dcl : Nat} {r : FState}
    (h : verifiedPipelineFull env f start zv dcl = .ok r) (hv : r.st.verified = true) :
    LayerRefines (PreFull (NilCheck.dictParams env.tables f) (pipelineRo env f)
      (pipelineEq env) r.nnf r.nhs) r.layer
      r.st.tables r.st.func (startLayer start) env.tables f := by
  unfold verifiedPipelineFull at h
  split at h
  · cases h
  · next st hst =>
    have I := runPasses_inv (fun p hp => stockPasses_sound p (List.mem_of_mem_drop hp))
      (Inv.init zv) hst
    have I0 : InvF env f (startLayer start)
        { st, layer := startLayer start, dclLen := dcl + newAutos env.tables st.tables
          genVerified := st.verified } := by
      refine ⟨fun hver => ?_, I.2.1, I.2.2.2.1⟩
      by_cases hs : start ≤ stockPasses.size
      · have hl : startLayer start = .gen := by simp [startLayer, hs]
        simp only [hl]
        intro e args mem hP fuel hd
        exact I.1 hver e args mem hP.1 fuel hd
      · have hnil : stockPasses.toList.drop start = [] :=
          List.drop_eq_nil_of_le (by rw [Array.length_toList]; omega)
        unfold verifiedPipeline at hst
        rw [hnil] at hst
        cases hst
        exact LayerRefines.refl _ _ _ _
    exact (runPassesL_inv (fun p hp => loweredVPasses_sound p (List.mem_of_mem_drop hp)) I0 h).1 hv

/-- **The verified pipeline through `trim` refines its input** (H7/H8): when
`verifiedPipelineFull` from `number lines` returns a `fullyVerified` state (every run proven,
identity or skipped, the state allocated and free of `InvertFlags`), every returning or panicking `run` of the input
`f` (with the environment's tables) is, up to refinement, a `runLoc` of the result after `trim`,
on every environment and input in Phase 1's `VPre` (with `f`'s dictionary parameters and
read-only symbols) on which the recorded `schedule` inputs do not fault in the nil page and
their pointer-shaped parameter pieces and checked pointer-shaped values read nil or pointers
that are not wild, and so do the checked pointers that the recorded `schedule` runs hoist above a
fault (`NilHoistOK`; none for a run without such a swap, `verifiedPipelineFull_nhs`). -/
theorem verifiedPipelineFull_refines {env : PassEnv} {f : Func} {zv : Array (ID × Nat)}
    {dcl : Nat} {r : FState} (h : verifiedPipelineFull env f 0 zv dcl = .ok r)
    (hv : r.fullyVerified = true) {e : Env} {args : List Val} {mem : Mem}
    (hP : VPre (NilCheck.dictParams env.tables f) (pipelineRo env f)
      (pipelineEq env) e args mem)
    (hn : ∀ x ∈ r.nnf, NoNilFault x.1 x.2 e args mem)
    (ha : ∀ x ∈ r.nnf, ArgPtrsOK x.1 x.2 e args mem)
    (hnp : ∀ x ∈ r.nnf, NilPtrsOK x.1 x.2 e args mem)
    (hnh : ∀ x ∈ r.nhs, NilHoistOK x.1 x.2.1 x.2.2 e args mem) {fuel : Nat}
    (hd : (GoFV.SSA.run e env.tables f args mem fuel).Defined) :
    ∃ fuel', OutcomeRefines 0 (GoFV.SSA.run e env.tables f args mem fuel)
      (runLoc e r.st.tables r.st.func args mem fuel') := by
  simp only [FState.fullyVerified, Bool.and_eq_true, beq_iff_eq] at hv
  have R := verifiedPipelineFull_layer h hv.1.1
  rw [hv.1.2, show startLayer 0 = .gen by simp [startLayer]] at R
  exact R e args mem ⟨hP, fun x hx => ⟨hn x hx, ha x hx, hnp x hx⟩, hnh⟩ fuel hd

end GoFV.Proof.PipelineFull
