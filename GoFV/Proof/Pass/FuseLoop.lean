import GoFV.Opt.Fuse.Basic
import GoFV.Proof.DomRel
import GoFV.Proof.Refine
import GoFV.Proof.Cong

/-!
# The fuse driver keeps refinement and `WFDom`, for any checked step

`Fuse.StepOK ce step`: every successful result of `step` (`fuseLoop`'s per-block step) on a
function with `WFDom ce` refines it and keeps `WFDom ce` — the shape of the checked fuse steps'
theorems (`fuseBlockPlainChecked_refines`, `fuseComparisonsChecked_refines`). `FinalOK ce
final`: the same for the optional whole-function step. Then `fuseLoop_refines`: a successful
`fuseLoop step final fuel f` from `WFDom ce f` refines `f` and keeps `WFDom ce` (`sweep_inv` over
one sweep; `invalidateCFG` changes only analysis caches: `invalidateCFG_refines`,
`WFDom.invalidateCFG`). Shared by early fuse, late fuse and short circuit.
-/

namespace GoFV.Proof.Fuse

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.Fuse GoFV.Proof Dom

/-- See the module doc. -/
def StepOK (ce : CheckEnv) (step : Func → ID → Except String (Func × Bool)) : Prop :=
  ∀ (tabs : Tables) (f : Func) (b : ID) (g : Func) (ch : Bool), step f b = .ok (g, ch) →
    WFDom ce f → Refines tabs g tabs f ∧ WFDom ce g

/-- See the module doc. -/
def FinalOK (ce : CheckEnv) (final : Option (Func → Except String (Func × Bool))) : Prop :=
  ∀ fin, final = some fin → ∀ (tabs : Tables) (f g : Func) (ch : Bool), fin f = .ok (g, ch) →
    WFDom ce f → Refines tabs g tabs f ∧ WFDom ce g

/-- `FinalOK` at the tables `tabs` only: a final step whose checker reads the tables (late
fuse's branch redirect decides comparisons with them). -/
def FinalOKAt (ce : CheckEnv) (tabs : Tables) (final : Option (Func → Except String (Func × Bool))) :
    Prop :=
  ∀ fin, final = some fin → ∀ (f g : Func) (ch : Bool), fin f = .ok (g, ch) →
    WFDom ce f → Refines tabs g tabs f ∧ WFDom ce g

theorem FinalOK.at {ce : CheckEnv} {final : Option (Func → Except String (Func × Bool))}
    (h : FinalOK ce final) (tabs : Tables) : FinalOKAt ce tabs final :=
  fun fin hfin f g ch hf hw => h fin hfin tabs f g ch hf hw

theorem finalOK_none {ce : CheckEnv} : FinalOK ce none := fun _ h => nomatch h

/-- The loop invariant: refines the input, keeps `WFDom`. -/
def Inv (ce : CheckEnv) (tabs : Tables) (f0 f : Func) : Prop :=
  Refines tabs f tabs f0 ∧ WFDom ce f

theorem Inv.step {ce : CheckEnv} {tabs : Tables} {f0 f g : Func} (hI : Inv ce tabs f0 f)
    (h : WFDom ce f → Refines tabs g tabs f ∧ WFDom ce g) : Inv ce tabs f0 g := by
  obtain ⟨hr, hw⟩ := h hI.2
  exact ⟨hI.1.trans hr, hw⟩

theorem sweepAux_inv {ce : CheckEnv} {tabs : Tables} {f0 : Func}
    {step : Func → ID → Except String (Func × Bool)} (hs : StepOK ce step) (blocks : Array ID) :
    ∀ (k : Nat) (f : Func) (ch : Bool) (g : Func) (ch' : Bool),
      sweepAux step blocks k f ch = .ok (g, ch') → Inv ce tabs f0 f → Inv ce tabs f0 g
  | 0, f, ch, g, ch', h, hI => by
    simp only [sweepAux, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact hI
  | k + 1, f, ch, g, ch', h, hI => by
    simp only [sweepAux, bind, Except.bind] at h
    cases he : step f blocks[k]! with
    | error e => rw [he] at h; cases h
    | ok r =>
      rw [he] at h
      obtain ⟨f', c⟩ := r
      exact sweepAux_inv hs blocks k f' _ g ch' h (hI.step (hs tabs f _ f' c he))

theorem sweep_inv {ce : CheckEnv} {tabs : Tables} {f0 : Func}
    {step : Func → ID → Except String (Func × Bool)} (hs : StepOK ce step) {f g : Func}
    {ch : Bool} (h : sweep step f = .ok (g, ch)) (hI : Inv ce tabs f0 f) : Inv ce tabs f0 g :=
  sweepAux_inv hs f.blocks _ f false g ch h hI

/-- `invalidateCFG` changes only the analysis caches, which runs do not read. -/
theorem invalidateCFG_refines {tabs : Tables} (f : Func) :
    Refines tabs f.invalidateCFG tabs f :=
  Refines.of_eraseF rfl

theorem reach_invalidateCFG {f : Func} {x : ID} {l : List ID} :
    Reach f.invalidateCFG x l ↔ Reach f x l := by
  constructor
  · intro h
    induction h with
    | entry => exact .entry
    | step _ hb he ih => exact .step ih hb he
  · intro h
    induction h with
    | entry => exact .entry
    | step _ hb he ih => exact .step ih hb he

theorem wf_invalidateCFG {ce : CheckEnv} {f : Func} (h : WF ce f) : WF ce f.invalidateCFG :=
  ⟨h.blockId, h.blocksNodup, h.valueId, h.valuesNodup, h.valueOnce, h.predLink, h.succLink,
    h.arity, h.phiArity, h.boolAux, h.argListed, h.ctrlListed, h.entry, h.entryPreds⟩

theorem WFDom.invalidateCFG {ce : CheckEnv} {f : Func} (h : WFDom ce f) :
    WFDom ce f.invalidateCFG := by
  refine ⟨wf_invalidateCFG h.wf, fun b blk hbm hb => ?_⟩
  obtain ⟨h1, h2, h3⟩ := h.dom b blk hbm hb
  exact ⟨fun l hl => h1 l (reach_invalidateCFG.1 hl), fun l hl => h2 l (reach_invalidateCFG.1 hl),
    fun vid hv v hvv hph i a e l ha he hr => h3 vid hv v hvv hph i a e l ha he
      (reach_invalidateCFG.1 hr)⟩

theorem fuseLoop_inv {ce : CheckEnv} {tabs : Tables} {f0 : Func}
    {step : Func → ID → Except String (Func × Bool)}
    {final : Option (Func → Except String (Func × Bool))} (hs : StepOK ce step)
    (hfin : FinalOKAt ce tabs final) :
    ∀ (n : Nat) (f g : Func), fuseLoop step final n f = .ok g → Inv ce tabs f0 f →
      Inv ce tabs f0 g
  | 0, f, g, h, _ => by simp [fuseLoop, throw, throwThe, MonadExceptOf.throw] at h
  | n + 1, f, g, h, hI => by
    simp only [fuseLoop, bind, Except.bind] at h
    cases hsw : sweep step f with
    | error e => rw [hsw] at h; cases h
    | ok r =>
      rw [hsw] at h
      obtain ⟨f1, c1⟩ := r
      have hI1 := sweep_inv hs hsw hI
      -- the optional final step, then the next round
      have hnext : ∀ f2 c2, Inv ce tabs f0 f2 →
          (if c2 = true then fuseLoop step final n f2.invalidateCFG else .ok f2) = .ok g →
          Inv ce tabs f0 g := fun f2 c2 hI2 h => by
        split at h
        · exact fuseLoop_inv hs hfin n _ g h
            ⟨Refines.trans hI2.1 (invalidateCFG_refines f2), WFDom.invalidateCFG hI2.2⟩
        · simp only [Except.ok.injEq] at h
          rw [← h]; exact hI2
      cases hfn : final with
      | none =>
        simp only [hfn, pure, Except.pure] at h
        rw [← hfn] at h
        exact hnext f1 c1 hI1 h
      | some fin =>
        simp only [hfn] at h
        cases hf : fin f1 with
        | error e => rw [hf] at h; cases h
        | ok r =>
          rw [hf] at h
          obtain ⟨f2, c2⟩ := r
          simp only [pure, Except.pure] at h
          rw [← hfn] at h
          exact hnext f2 (c2 || c1) (hI1.step (hfin fin hfn f1 f2 c2 hf)) h

/-- **The fuse driver refines its input** and keeps `WFDom`, for any checked step and a final
step checked at the tables `tabs`. -/
theorem fuseLoop_refines_at {ce : CheckEnv} {tabs : Tables}
    {step : Func → ID → Except String (Func × Bool)}
    {final : Option (Func → Except String (Func × Bool))} (hs : StepOK ce step)
    (hfin : FinalOKAt ce tabs final) {n : Nat} {f g : Func} (h : fuseLoop step final n f = .ok g)
    (hf : WFDom ce f) : Refines tabs g tabs f ∧ WFDom ce g :=
  fuseLoop_inv (f0 := f) hs hfin n f g h ⟨Refines.refl _ _, hf⟩

/-- **The fuse driver refines its input** and keeps `WFDom`, for any checked step. -/
theorem fuseLoop_refines {ce : CheckEnv} {tabs : Tables}
    {step : Func → ID → Except String (Func × Bool)}
    {final : Option (Func → Except String (Func × Bool))} (hs : StepOK ce step)
    (hfin : FinalOK ce final) {n : Nat} {f g : Func} (h : fuseLoop step final n f = .ok g)
    (hf : WFDom ce f) : Refines tabs g tabs f ∧ WFDom ce g :=
  fuseLoop_refines_at hs (hfin.at tabs) h hf

end GoFV.Proof.Fuse
