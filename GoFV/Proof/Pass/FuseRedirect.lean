import GoFV.Proof.Pass.FuseRedirectSim
import GoFV.Proof.Pass.FuseLoop
import GoFV.Proof.Pass.DeadEdge

/-!
# The checked `fuseBranchRedirect` refines its input

`redirect_refines`: one checked redirect (`Redir.stepOK`) of a function with `WFDom` refines it
and keeps `WFDom` (`Setup.refines_of_step`, `Base.wf_pres`, `Base.useDom_pres`). `dead_refines`:
marking a block without predecessors that is not the entry `Invalid` (only its kind changes)
neither changes a run, which never enters it, nor well-formedness or use dominance.
`fuseBranchRedirectChecked_ok`: the whole checked step, a sweep of predecessor loops of such
redirects and markings, is a final step of the fuse driver checked at the tables it decides
with (`Fuse.FinalOKAt`).
-/

namespace GoFV.Proof.FuseRedirect

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.Fuse GoFV.Opt.Prove GoFV.Proof Dom

/-- **One checked redirect refines its input** and keeps `WFDom`. -/
theorem redirect_refines {tabs : Tables} {ce : CheckEnv} {f g : Func} {b : ID} {k out : Nat}
    (h : Redir.stepOK tabs f g b k out = true) (hf : WFDom ce f) :
    Refines tabs g tabs f ∧ WFDom ce g := by
  have R : RRel tabs f g (Redir.siteOf f b k out) := ⟨h⟩
  obtain ⟨B, P, C, H⟩ := R.sh
  have S : Setup ce tabs f g _ B P C := ⟨⟨hf.wf, R⟩, H, hf.dom⟩
  exact ⟨S.refines_of_step, ⟨S.base.wf_pres H, S.base.useDom_pres H hf.dom⟩⟩

/-! ## A block without predecessors becomes `Invalid` -/

section
variable {env : Env} {ctx ctx' : Sem.Ctx}

/-- Evaluation reads of the context only the tables, the shapes, the parameters and the
activation. -/
private theorem evalValue_ctx' (htabs : ctx.tabs = ctx'.tabs) (htys : ctx.tys = ctx'.tys)
    (hpar : ctx.params = ctx'.params) (hact : ctx.act = ctx'.act) (fr : Frame) (v : Value) :
    evalValue env ctx fr v = evalValue env ctx' fr v := by
  obtain ⟨f, tabs, tys, sched, params, paramTys, outs, locals, act⟩ := ctx
  obtain ⟨f', tabs', tys', sched', params', paramTys', outs', locals', act'⟩ := ctx'
  dsimp only at htabs htys hpar hact
  subst htabs htys hpar hact
  rfl

private theorem evalAll_ctx' (htabs : ctx.tabs = ctx'.tabs) (htys : ctx.tys = ctx'.tys)
    (hpar : ctx.params = ctx'.params) (hact : ctx.act = ctx'.act)
    (hv : ∀ x, ctx.f.value? x = ctx'.f.value? x) :
    ∀ (fr : Frame) (ids : List ID), evalAll env ctx fr ids = evalAll env ctx' fr ids := by
  intro fr ids
  induction ids generalizing fr with
  | nil => rfl
  | cons id ids ih =>
    unfold evalAll
    rw [hv id]
    cases ctx'.f.value? id with
    | none => rfl
    | some v =>
      dsimp only
      rw [evalValue_ctx' htabs htys hpar hact]
      split <;> simp only [ih]

private theorem enterBlock_ctx' (htabs : ctx.tabs = ctx'.tabs) (htys : ctx.tys = ctx'.tys)
    (hsched : ctx.sched = ctx'.sched) (hpar : ctx.params = ctx'.params)
    (hact : ctx.act = ctx'.act) (hv : ∀ x, ctx.f.value? x = ctx'.f.value? x) (fr : Frame)
    (b : Block) (i : Nat) : enterBlock env ctx fr b i = enterBlock env ctx' fr b i := by
  unfold enterBlock
  rw [hsched]
  congr 1
  · congr 1
    funext id
    rw [htys, hv id]
  · funext phis
    simp only [evalAll_ctx' htabs htys hpar hact hv]

end

/-- Set a block's kind to `Invalid`. -/
abbrev kInv (x : Block) : Block := { x with kind := .Invalid }

section
variable {tabs : Tables} {ce : CheckEnv} {f : Func} {b : ID}

/-- A block entry of `f.modB b kInv`: `b`'s with its kind changed. -/
def kf (b y : ID) (X : Block) : Block := if b = y then kInv X else X

theorem kf_id {y : ID} {X : Block} : (kf b y X).id = X.id := by unfold kf; split <;> rfl
theorem kf_values {y : ID} {X : Block} : (kf b y X).values = X.values := by
  unfold kf; split <;> rfl
theorem kf_preds {y : ID} {X : Block} : (kf b y X).preds = X.preds := by unfold kf; split <;> rfl
theorem kf_succs {y : ID} {X : Block} : (kf b y X).succs = X.succs := by unfold kf; split <;> rfl
theorem kf_controls {y : ID} {X : Block} : (kf b y X).controls = X.controls := by
  unfold kf; split <;> rfl

theorem dead_block (y : ID) : (f.modB b kInv).block? y = (f.block? y).map (kf b y) := by
  rw [Dead.block?_modB]
  unfold kf
  by_cases h : b = y
  · simp [h]
  · simp [h]

theorem dead_block_inv {y : ID} {Y : Block} (h : (f.modB b kInv).block? y = some Y) :
    ∃ X, f.block? y = some X ∧ Y = kf b y X := by
  rw [dead_block] at h
  cases hX : f.block? y with
  | none => rw [hX] at h; cases h
  | some X => rw [hX] at h; exact ⟨X, rfl, (Option.some.inj h).symm⟩

theorem dead_listed {a : ID} (h : Listed f a) : Listed (f.modB b kInv) a := by
  obtain ⟨y, Y, ⟨hy, hY⟩, ha⟩ := h
  exact ⟨y, _, ⟨hy, by rw [dead_block, hY]; rfl⟩, by rw [kf_values]; exact ha⟩

theorem dead_wf (hwf : WF ce f) : WF ce (f.modB b kInv) := by
  have hblk : ∀ bid b', BlockIn (f.modB b kInv) bid b' → ∃ X, BlockIn f bid X ∧ b' = kf b bid X :=
    fun bid b' ⟨hm, hb'⟩ => by
      obtain ⟨X, hX, rfl⟩ := dead_block_inv hb'
      exact ⟨X, ⟨hm, hX⟩, rfl⟩
  have hg : ∀ y X, f.block? y = some X → (f.modB b kInv).block? y = some (kf b y X) :=
    fun y X hX => by rw [dead_block, hX]; rfl
  exact {
    blockId := fun bid hm => by
      obtain ⟨X, hX, hid⟩ := hwf.blockId bid hm
      exact ⟨_, hg bid X hX, by rw [kf_id, hid]⟩
    blocksNodup := hwf.blocksNodup
    valueId := fun bid b' hb vid hv => by
      obtain ⟨X, hX, rfl⟩ := hblk bid b' hb
      exact hwf.valueId bid X hX vid (by rwa [kf_values] at hv)
    valuesNodup := fun bid b' hb => by
      obtain ⟨X, hX, rfl⟩ := hblk bid b' hb
      rw [kf_values]; exact hwf.valuesNodup bid X hX
    valueOnce := fun bid1 b1 bid2 b2 hb1 hb2 vid h1 h2 => by
      obtain ⟨X1, hX1, rfl⟩ := hblk bid1 b1 hb1
      obtain ⟨X2, hX2, rfl⟩ := hblk bid2 b2 hb2
      rw [kf_values] at h1 h2
      exact hwf.valueOnce bid1 X1 bid2 X2 hX1 hX2 vid h1 h2
    predLink := fun bid b' hb i e he => by
      obtain ⟨X, hX, rfl⟩ := hblk bid b' hb
      rw [kf_preds] at he
      obtain ⟨hm, P, hP, hs⟩ := hwf.predLink bid X hX i e he
      exact ⟨hm, _, hg e.b P hP, by rw [kf_succs]; exact hs⟩
    succLink := fun bid b' hb j e he => by
      obtain ⟨X, hX, rfl⟩ := hblk bid b' hb
      rw [kf_succs] at he
      obtain ⟨hm, C, hC, hs⟩ := hwf.succLink bid X hX j e he
      exact ⟨hm, _, hg e.b C hC, by rw [kf_preds]; exact hs⟩
    arity := fun bid b' vid v ⟨hb, hv, hvv⟩ hl => by
      obtain ⟨X, hX, rfl⟩ := hblk bid b' hb
      exact hwf.arity bid X vid v ⟨hX, by rwa [kf_values] at hv, hvv⟩ hl
    phiArity := fun bid b' vid v ⟨hb, hv, hvv⟩ hp => by
      obtain ⟨X, hX, rfl⟩ := hblk bid b' hb
      rw [kf_preds]
      exact hwf.phiArity bid X vid v ⟨hX, by rwa [kf_values] at hv, hvv⟩ hp
    boolAux := fun bid b' vid v ⟨hb, hv, hvv⟩ hp => by
      obtain ⟨X, hX, rfl⟩ := hblk bid b' hb
      exact hwf.boolAux bid X vid v ⟨hX, by rwa [kf_values] at hv, hvv⟩ hp
    argListed := fun bid b' vid v ⟨hb, hv, hvv⟩ a ha => by
      obtain ⟨X, hX, rfl⟩ := hblk bid b' hb
      exact dead_listed (hwf.argListed bid X vid v ⟨hX, by rwa [kf_values] at hv, hvv⟩ a ha)
    ctrlListed := fun bid b' hb c hc => by
      obtain ⟨X, hX, rfl⟩ := hblk bid b' hb
      exact dead_listed (hwf.ctrlListed bid X hX c (by rwa [kf_controls] at hc))
    entry := hwf.entry
    entryPreds := fun b' hb' => by
      obtain ⟨X, hX, rfl⟩ := dead_block_inv hb'
      rw [kf_preds]; exact hwf.entryPreds X hX }

theorem dead_reach {x : ID} {l : List ID} : Reach (f.modB b kInv) x l ↔ Reach f x l := by
  constructor
  · intro h
    induction h with
    | entry => exact .entry
    | step _ hb he ih =>
      obtain ⟨X, hX, rfl⟩ := dead_block_inv hb
      exact .step ih hX (by rwa [kf_succs] at he)
  · intro h
    induction h with
    | entry => exact .entry
    | @step y l blk e _ hb he ih =>
      exact .step ih (by rw [dead_block, hb]; rfl) (by rw [kf_succs]; exact he)

theorem dead_useDom (hu : UseDom f) : UseDom (f.modB b kInv) := by
  intro bid blk hbm hbb
  obtain ⟨X, hX, rfl⟩ := dead_block_inv hbb
  obtain ⟨h1, h2, h3⟩ := hu bid X hbm hX
  refine ⟨fun l hl vid hv v hvv hnp a ha => ?_, fun l hl x hx => ?_,
    fun vid hv v hvv hp i a e l ha he hr => ?_⟩
  · exact h1 l (dead_reach.1 hl) vid (by rwa [kf_values] at hv) v hvv hnp a ha
  · exact h2 l (dead_reach.1 hl) x (by rwa [kf_controls] at hx)
  · exact h3 vid (by rwa [kf_values] at hv) v hvv hp i a e l ha (by rwa [kf_preds] at he)
      (dead_reach.1 hr)

theorem dead_sched : (Ctx.make tabs (f.modB b kInv)).sched = (Ctx.make tabs f).sched := by
  have hsch : ∀ X, schedule (f.modB b kInv) X = schedule f X := fun X =>
    schedule_congr (fun _ => rfl) rfl
  apply Array.ext_getElem?
  intro i
  simp only [Ctx.make, Array.getElem?_map, hsch]
  show Option.map _ (f.blockTab.modify b (Option.map kInv))[i]? = _
  rw [Array.getElem?_modify]
  split
  · cases f.blockTab[i]? with
    | none => rfl
    | some o =>
      cases o with
      | none => rfl
      | some X =>
        simp only [Option.map_some, Option.bind_some]
        exact congrArg some (schedule_congr (fun _ => rfl) rfl)
  · rfl

/-- The runs from a listed block other than `b` (which has no predecessors) are the same. -/
theorem dead_runLoop (hwf : WF ce f) {B : Block} (hB : f.block? b = some B)
    (hp : B.preds.size = 0) {env : Env} :
    ∀ fuel fr y i, y ∈ f.blocks → y ≠ b →
      runLoop env (Ctx.make tabs (f.modB b kInv)) fuel fr y i =
        runLoop env (Ctx.make tabs f) fuel fr y i := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ n ih =>
    intro fr y i hy hyb
    rw [runLoop_succ, runLoop_succ]
    have hb' : (Ctx.make tabs (f.modB b kInv)).f.block? y = (Ctx.make tabs f).f.block? y := by
      show (f.modB b kInv).block? y = f.block? y
      rw [dead_block]
      cases f.block? y with
      | none => rfl
      | some Y => simp only [Option.map_some]; unfold kf; rw [if_neg (Ne.symm hyb)]
    rw [hb']
    cases hY : (Ctx.make tabs f).f.block? y with
    | none => rfl
    | some Y =>
      have hY' : f.block? y = some Y := hY
      simp only
      rw [enterBlock_ctx' (ctx := Ctx.make tabs (f.modB b kInv)) (ctx' := Ctx.make tabs f) rfl rfl
        dead_sched rfl rfl (fun _ => rfl)]
      cases enterBlock env (Ctx.make tabs f) fr Y i with
      | panic e m => rfl
      | stuck msg => rfl
      | ok G =>
        simp only
        cases ht : stepTerm G Y with
        | ok nx =>
          cases nx with
          | goto e =>
            simp only
            have he := GoFV.Proof.stepTerm_goto_mem ht
            obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 he
            obtain ⟨hem, C, hC, hci⟩ := hwf.succLink y Y ⟨hy, hY'⟩ j e hj
            refine ih G e.b e.i hem fun h => ?_
            rw [h, hB] at hC; cases hC
            have := (Array.getElem?_eq_some_iff.1 hci).1
            omega
          | ret rs m => rfl
        | panic e m => rfl
        | stuck msg => rfl

/-- **Marking a block without predecessors `Invalid`** refines and keeps `WFDom`. -/
theorem dead_refines (hf : WFDom ce f) {B : Block} (hB : f.block? b = some B)
    (hp : B.preds.size = 0) (he : b ≠ f.entry) :
    Refines tabs (f.modB b kInv) tabs f ∧ WFDom ce (f.modB b kInv) := by
  refine ⟨Refines.of_run_eq fun env args mem fuel => ?_, ⟨dead_wf hf.wf, dead_useDom hf.dom⟩⟩
  show runCtx env (Ctx.make tabs (f.modB b kInv)) args mem fuel =
    runCtx env (Ctx.make tabs f) args mem fuel
  unfold runCtx
  have hpar : (Ctx.make tabs (f.modB b kInv)).params = (Ctx.make tabs f).params := rfl
  rw [hpar]
  split
  · rfl
  · have hen : entryFrame env (Ctx.make tabs (f.modB b kInv)) args mem =
        entryFrame env (Ctx.make tabs f) args mem := rfl
    rw [hen]
    have hr := dead_runLoop (tabs := tabs) (env := env) hf.wf hB hp fuel
      (entryFrame env (Ctx.make tabs f) args mem) f.entry 0 hf.wf.entry (Ne.symm he)
    exact congrArg (finish env (Ctx.make tabs f).outs (Ctx.make tabs f).defers (Ctx.make tabs f).act) hr

end

/-- **`markDead` refines and keeps `WFDom`.** -/
theorem markDead_refines {tabs : Tables} {ce : CheckEnv} {f : Func} {b : ID} (hf : WFDom ce f) :
    Refines tabs (markDead f b) tabs f ∧ WFDom ce (markDead f b) := by
  unfold markDead
  split
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hc
    cases hB : f.block? b with
    | none =>
      have : f.modB b (fun x => { x with kind := .Invalid }) = f := by
        unfold Func.modB
        congr 1
        apply Array.ext_getElem?
        intro i
        rw [Array.getElem?_modify]
        split
        · rename_i h; subst h
          unfold Func.block? at hB
          cases h' : f.blockTab[b]? with
          | none => rfl
          | some o => rw [h'] at hB; cases o <;> simp_all
        · rfl
      rw [this]; exact ⟨Refines.refl _ _, hf⟩
    | some B =>
      have hp : B.preds.size = 0 := by
        have := hc.1; unfold Func.getB at this; rw [hB] at this; exact this
      exact dead_refines hf hB hp hc.2
  · exact ⟨Refines.refl _ _, hf⟩

/-! ## The checked step -/

section
variable {tabs : Tables} {ce : CheckEnv} {pv : Prover}

theorem predLoopC_ok {b : ID} :
    ∀ (fuel : Nat) (f : Func) (ft : FactsTable) (k : Nat) (ch : Bool) (g : Func) (ft' : FactsTable)
      (ch' : Bool), predLoopC pv tabs b fuel f ft k ch = (g, ft', ch') → WFDom ce f →
      Refines tabs g tabs f ∧ WFDom ce g
  | 0, f, ft, k, ch, g, ft', ch', h, hf => by
    simp only [predLoopC, Prod.mk.injEq] at h
    rw [← h.1]; exact ⟨Refines.refl _ _, hf⟩
  | fuel + 1, f, ft, k, ch, g, ft', ch', h, hf => by
    unfold predLoopC at h
    split at h
    · split at h
      · rename_i ft1 out _
        dsimp only at h
        split at h
        · rename_i hok
          obtain ⟨r1, w1⟩ := redirect_refines (ce := ce) hok hf
          obtain ⟨r2, w2⟩ := predLoopC_ok fuel _ _ _ _ g ft' ch' h w1
          exact ⟨r1.trans r2, w2⟩
        · exact predLoopC_ok fuel _ _ _ _ g ft' ch' h hf
      · exact predLoopC_ok fuel _ _ _ _ g ft' ch' h hf
    · simp only [Prod.mk.injEq] at h
      rw [← h.1]; exact ⟨Refines.refl _ _, hf⟩

theorem redirectBlock_ok {f : Func} {ft : FactsTable} {b : ID} {g : Func} {ft' : FactsTable}
    {ch : Bool} (h : redirectBlock pv tabs f ft b = (g, ft', ch)) (hf : WFDom ce f) :
    Refines tabs g tabs f ∧ WFDom ce g := by
  unfold redirectBlock at h
  dsimp only at h
  split at h
  · simp only [Prod.mk.injEq] at h; rw [← h.1]; exact ⟨Refines.refl _ _, hf⟩
  · split at h
    · simp only [Prod.mk.injEq] at h; rw [← h.1]; exact ⟨Refines.refl _ _, hf⟩
    · generalize hp : predLoopC pv tabs b _ f ft 0 false = r at h
      obtain ⟨f1, ft1, c1⟩ := r
      simp only [Prod.mk.injEq] at h
      obtain ⟨r1, w1⟩ := predLoopC_ok _ _ _ _ _ _ _ _ hp hf
      obtain ⟨r2, w2⟩ := markDead_refines (tabs := tabs) (b := b) w1
      rw [← h.1]
      exact ⟨r1.trans r2, w2⟩

theorem redirectSweep_ok (blocks : Array ID) :
    ∀ (k : Nat) (f : Func) (ft : FactsTable) (ch : Bool) (g : Func) (ft' : FactsTable) (ch' : Bool),
      redirectSweep pv tabs blocks k f ft ch = (g, ft', ch') → WFDom ce f →
      Refines tabs g tabs f ∧ WFDom ce g
  | 0, f, ft, ch, g, ft', ch', h, hf => by
    simp only [redirectSweep, Prod.mk.injEq] at h
    rw [← h.1]; exact ⟨Refines.refl _ _, hf⟩
  | k + 1, f, ft, ch, g, ft', ch', h, hf => by
    unfold redirectSweep at h
    generalize hb : redirectBlock pv tabs f ft blocks[k]! = r at h
    obtain ⟨f1, ft1, c1⟩ := r
    obtain ⟨r1, w1⟩ := redirectBlock_ok hb hf
    obtain ⟨r2, w2⟩ := redirectSweep_ok blocks k _ _ _ g ft' ch' h w1
    exact ⟨r1.trans r2, w2⟩

end

/-- **The checked `fuseBranchRedirect` is a checked final step** of the fuse driver, at the
tables its decisions read. -/
theorem fuseBranchRedirectChecked_ok {ce : CheckEnv} (pv : Prover) (tabs : Tables) :
    Fuse.FinalOKAt ce tabs (some (fuseBranchRedirectChecked pv tabs)) := by
  intro fin hfin f g ch h hf
  cases hfin
  unfold fuseBranchRedirectChecked at h
  generalize hs : redirectSweep pv tabs f.blocks f.blocks.size f _ false = r at h
  obtain ⟨g1, ft1, c1⟩ := r
  simp only at h
  split at h
  · cases h
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact redirectSweep_ok _ _ _ _ _ _ _ _ hs hf

end GoFV.Proof.FuseRedirect
