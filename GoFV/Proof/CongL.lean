import GoFV.Proof.RefineL
import GoFV.Proof.Cong
import GoFV.SSA.Analysis.CfgCache
import GoFV.SSA.Alloc

/-!
# `runL` ignores block order, positions, predictions, caches and the lowered-pass state

`runL` reads of a function only its entry block, its `ownAux` (the ABI), and its value and block
tables up to positions, use counts and branch predictions (`eraseV`, `eraseB`). `eraseFL f`
keeps exactly these; functions with the same `eraseFL` have the same `runL`s (`runL_congr`).
So passes that only reorder `f.Blocks` (`layout`), set `Likely` (`likelyadjust`), refresh the
analysis caches or the lowered-pass flags refine their input by this lemma alone
(`RefinesL.of_eraseFL`).

`CacheOnly f g`: `g` is `f` with other analysis caches (`f.postorder`, `f.idom`, `f.sdom`,
`f.loopnestfor`, `f.loopnest` produce such functions).
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem

-- Unification must never unfold the scheduler (`kahn` is a big imperative loop).
attribute [local irreducible] schedule kahn schedValid

/-- What `runL` reads of a function: entry, `ownAux` and the erased value and block tables. -/
def eraseFL (f : Func) : Func :=
  { (default : Func) with
    entry := f.entry, ownAux := f.ownAux,
    valueTab := f.valueTab.map (Option.map eraseV),
    blockTab := f.blockTab.map (Option.map eraseB) }

/-- `eraseF`-equal functions are `eraseFL`-equal. -/
theorem eraseFL_of_eraseF {f g : Func} (h : eraseF f = eraseF g) : eraseFL f = eraseFL g := by
  have he : f.entry = g.entry := by have := congrArg Func.entry h; exact this
  have ho : f.ownAux = g.ownAux := by have := congrArg Func.ownAux h; exact this
  have hv : f.valueTab.map (Option.map eraseV) = g.valueTab.map (Option.map eraseV) :=
    congrArg Func.valueTab h
  have hb : f.blockTab.map (Option.map eraseB) = g.blockTab.map (Option.map eraseB) :=
    congrArg Func.blockTab h
  simp only [eraseFL, he, ho, hv, hb]

theorem value?_eraseFL (f : Func) (id : ID) :
    (eraseFL f).value? id = (f.value? id).map eraseV := by
  simp only [Func.value?, eraseFL, Array.getElem?_map]
  cases f.valueTab[id]? with
  | none => rfl
  | some o => cases o <;> rfl

theorem block?_eraseFL (f : Func) (id : ID) :
    (eraseFL f).block? id = (f.block? id).map eraseB := by
  simp only [Func.block?, eraseFL, Array.getElem?_map]
  cases f.blockTab[id]? with
  | none => rfl
  | some o => cases o <;> rfl

theorem eraseF_value_of_eraseFL {f g : Func} (h : eraseFL f = eraseFL g) (id : ID) :
    (f.value? id).map eraseV = (g.value? id).map eraseV := by
  rw [← value?_eraseFL, ← value?_eraseFL, h]

theorem eraseF_block_of_eraseFL {f g : Func} (h : eraseFL f = eraseFL g) (id : ID) :
    (f.block? id).map eraseB = (g.block? id).map eraseB := by
  rw [← block?_eraseFL, ← block?_eraseFL, h]

/-! ## Congruence of the lowered runner -/

theorem evalValueL_eraseV (md : LMode) (env : Env) (ctx : Ctx) (fr : Frame) (v : Value) :
    evalValueL md env ctx fr (eraseV v) = evalValueL md env ctx fr v := (rfl)

theorem stepTermL_eraseB (fr : Frame) (b : Block) : stepTermL fr (eraseB b) = stepTermL fr b :=
  (rfl)

/-- Two value tables equal up to erasure agree on whether erasure-equal values sign-extend. -/
theorem signExtendsIn_eraseV {val? val?' : ID → Option Value}
    (hv : ∀ id, (val? id).map eraseV = (val?' id).map eraseV) {u u' : Value}
    (he : eraseV u = eraseV u') : Arm64.signExtendsIn val? u = Arm64.signExtendsIn val?' u' := by
  have hop : u.op = u'.op := by have := congrArg Value.op he; exact this
  have hargs : u.args = u'.args := by have := congrArg Value.args he; exact this
  have h0 : ((u'.args[0]?.bind val?).map (·.op == .ARM64LDPSW)) =
      ((u'.args[0]?.bind val?').map (·.op == .ARM64LDPSW)) := by
    cases u'.args[0]? with
    | none => rfl
    | some a =>
      simp only [Option.bind_some]
      rcases map_eraseV_eq (hv a) with ⟨h1, h2⟩ | ⟨w, w', h1, h2, hw⟩
      · rw [h1, h2]
      · have : w.op = w'.op := by have := congrArg Value.op hw; exact this
        rw [h1, h2]; simp only [Option.map_some, this]
  unfold Arm64.signExtendsIn
  rw [hop, hargs]
  congr 1
  split <;> simp only [h0]

theorem evalValueL_ctx {md : LMode} {env : Env} {ctx ctx' : Ctx} (h : CtxEq ctx ctx')
    (fr : Frame) (v : Value) : evalValueL md env ctx fr v = evalValueL md env ctx' fr v := by
  have hop : ∀ o : Option ID, ((o.bind ctx.f.value?).map (Arm64.signExtendsIn ctx.f.value?)) =
      ((o.bind ctx'.f.value?).map (Arm64.signExtendsIn ctx'.f.value?)) := by
    intro o
    cases o with
    | none => rfl
    | some a =>
      simp only [Option.bind_some]
      rcases map_eraseV_eq (h.value a) with ⟨h1, h2⟩ | ⟨u, u', h1, h2, he⟩
      · rw [h1, h2]; rfl
      · rw [h1, h2]
        simp only [Option.map_some, signExtendsIn_eraseV h.value he]
  obtain ⟨f, tabs, tys, sched, params, paramTys, outs, locals, act⟩ := ctx
  obtain ⟨f', tabs', tys', sched', params', paramTys', outs', locals', act'⟩ := ctx'
  obtain ⟨h1, h2, -, h4, -, -, -, h8, -, -⟩ := h
  dsimp only at h1 h2 h4 h8 hop
  subst h1 h2 h4 h8
  simp only [evalValueL, evalOpL, arm64Op, hop]
  rfl

theorem evalAllL_congr {md : LMode} {env : Env} {ctx ctx' : Ctx} (h : CtxEq ctx ctx') :
    ∀ (fr : Frame) (ids : List ID), evalAllL md env ctx fr ids = evalAllL md env ctx' fr ids := by
  intro fr ids
  induction ids generalizing fr with
  | nil => rfl
  | cons id ids ih =>
    unfold evalAllL
    rcases map_eraseV_eq (h.value id) with ⟨h1, h2⟩ | ⟨v, v', h1, h2, he⟩
    · rw [h1, h2]
    · rw [h1, h2]
      dsimp only
      rw [evalValueL_ctx h, ← evalValueL_eraseV md env ctx' fr v, he, evalValueL_eraseV]
      split <;> simp only [ih]

theorem enterBlockL_congr {md : LMode} {env : Env} {ctx ctx' : Ctx} (h : CtxEq ctx ctx')
    (fr : Frame) {b b' : Block} (hb : eraseB b = eraseB b') (i : Nat) :
    enterBlockL md env ctx fr b i = enterBlockL md env ctx' fr b' i := by
  have hv : b.values = b'.values := by have := congrArg Block.values hb; exact this
  have hid : b.id = b'.id := by have := congrArg Block.id hb; exact this
  unfold enterBlockL
  rw [hv, hid, h.sched]
  congr 1
  · congr 1
    funext id
    rw [h.tys]
    rcases map_eraseV_eq (h.value id) with ⟨h1, h2⟩ | ⟨v, v', h1, h2, he⟩
    · rw [h1, h2]
    · rw [h1, h2]
      have hop : v.op = v'.op := by have := congrArg Value.op he; exact this
      have hargs : v.args = v'.args := by have := congrArg Value.args he; exact this
      simp only [hop, hargs]
  · funext phis
    simp only [evalAllL_congr h]

theorem runLoopL_congr {md : LMode} {env : Env} {ctx ctx' : Ctx} (h : CtxEq ctx ctx') :
    ∀ (fuel : Nat) (fr : Frame) (bid : ID) (i : Nat),
      runLoopL md env ctx fuel fr bid i = runLoopL md env ctx' fuel fr bid i := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ n ih =>
    intro fr bid i
    rw [runLoopL_succ, runLoopL_succ]
    rcases map_eraseB_eq (h.block bid) with ⟨h1, h2⟩ | ⟨b, b', h1, h2, he⟩
    · rw [h1, h2]
    · rw [h1, h2]
      simp only
      rw [enterBlockL_congr h fr he i]
      split
      · rfl
      · rfl
      · next fr1 _ =>
        rw [← stepTermL_eraseB fr1 b, he, stepTermL_eraseB]
        split <;> simp only [ih]

/-! ## `eraseFL`-equal functions run alike -/

theorem lowered_eraseFL (f : Func) : (eraseFL f).lowered = f.lowered := by
  unfold Func.lowered eraseFL
  simp only [Array.any_map]
  congr 1
  · congr 1; funext o; cases o <;> rfl
  · congr 1; funext o; cases o <;> rfl

theorem lowered_of_eraseFL {f g : Func} (h : eraseFL f = eraseFL g) : f.lowered = g.lowered := by
  rw [← lowered_eraseFL f, h, lowered_eraseFL]

theorem ctxEq_makeL (tabs : Tables) {f g : Func} (h : eraseFL f = eraseFL g) :
    CtxEq (Ctx.makeL tabs f) (Ctx.makeL tabs g) := by
  have hv := eraseF_value_of_eraseFL h
  have hb := eraseF_block_of_eraseFL h
  have hvt : f.valueTab.map (Option.map eraseV) = g.valueTab.map (Option.map eraseV) :=
    congrArg Func.valueTab h
  have hbt : f.blockTab.map (Option.map eraseB) = g.blockTab.map (Option.map eraseB) :=
    congrArg Func.blockTab h
  have hown : f.ownAux = g.ownAux := by have := congrArg Func.ownAux h; exact this
  have hps : abiParams tabs f = abiParams tabs g := by unfold abiParams; rw [hown]
  have hp : (Ctx.make tabs f).params = (Ctx.make tabs g).params := params_make tabs hown
  have hlow := lowered_of_eraseFL h
  have hm : CtxEq (Ctx.make tabs f) (Ctx.make tabs g) := by
    refine ⟨rfl, tys_make tabs hvt, sched_make tabs hv hbt, hp, ?_, ?_, ?_, rfl, hv, hb⟩
    · unfold Ctx.make; simp only [hps]
    · unfold Ctx.make; simp only [hps]
    · unfold Ctx.make; simp only [hps]
  unfold Ctx.makeL
  rw [hlow]
  split
  · have htys : f.valueTab.map (valueTy (typeShapesL tabs)) =
        g.valueTab.map (valueTy (typeShapesL tabs)) :=
      map_eq_of_factor (H := valueTy (typeShapesL tabs))
        (fun o => by cases o <;> rfl) (fun o => by cases o <;> rfl) hvt
    exact { hm with tys := htys }
  · exact hm

/-- **Functions with the same `eraseFL` have the same `runL`s.** -/
theorem runL_congr {f g : Func} (h : eraseFL f = eraseFL g) (env : Env) (tabs : Tables)
    (args : List Val) (mem : Mem) (fuel : Nat) :
    runL env tabs f args mem fuel = runL env tabs g args mem fuel := by
  have hc := ctxEq_makeL tabs h
  have hlow := lowered_of_eraseFL h
  have hsize : f.valueTab.size = g.valueTab.size := by
    have e1 : (eraseFL f).valueTab.size = f.valueTab.size := Array.size_map ..
    have e2 : (eraseFL g).valueTab.size = g.valueTab.size := Array.size_map ..
    rw [← e1, ← e2, h]
  have hsize' : (Ctx.makeL tabs f).f.valueTab.size = (Ctx.makeL tabs g).f.valueTab.size := by
    unfold Ctx.makeL; split <;> split <;> exact hsize
  have hentry : f.entry = g.entry := by have := congrArg Func.entry h; exact this
  have hent' : (Ctx.makeL tabs f).f.entry = (Ctx.makeL tabs g).f.entry := by
    unfold Ctx.makeL; split <;> split <;> exact hentry
  show runCtxL ⟨f.lowered, false⟩ env (Ctx.makeL tabs f) args mem fuel =
    runCtxL ⟨g.lowered, false⟩ env (Ctx.makeL tabs g) args mem fuel
  rw [hlow]
  unfold runCtxL
  rw [hc.params]
  split
  · rfl
  · rw [runLoopL_congr hc, hc.outs, hc.act, entryFrame_ctx hc hsize', hent']
    rw [show (Ctx.makeL tabs f).defers = (Ctx.makeL tabs g).defers by
      unfold Ctx.makeL; split <;> split <;> rfl]

theorem RefinesL.of_eraseFL {tabs : Tables} {f g : Func} (h : eraseFL g = eraseFL f) :
    RefinesL tabs g tabs f :=
  RefinesL.of_runL_eq fun env args mem fuel => runL_congr h env tabs args mem fuel

/-! ## Caches -/

/-- `g` is `f` with other analysis caches. -/
def CacheOnly (f g : Func) : Prop := ∃ c, g = { f with cache := c }

theorem CacheOnly.refl (f : Func) : CacheOnly f f := ⟨f.cache, rfl⟩

theorem CacheOnly.trans {f g h : Func} (h1 : CacheOnly f g) (h2 : CacheOnly g h) :
    CacheOnly f h := by
  obtain ⟨c, rfl⟩ := h1
  obtain ⟨d, rfl⟩ := h2
  exact ⟨d, rfl⟩

theorem CacheOnly.eraseFL {f g : Func} (h : CacheOnly f g) : eraseFL g = eraseFL f := by
  obtain ⟨c, rfl⟩ := h
  rfl

/-- Updating a block in a way `eraseB` cannot see (its branch prediction, its position) keeps
`eraseFL`. -/
theorem eraseFL_modB {f : Func} {b : ID} {g : Block → Block}
    (hg : ∀ x, eraseB (g x) = eraseB x) : eraseFL (f.modB b g) = eraseFL f := by
  simp only [eraseFL, Func.modB]
  congr 1
  apply Array.ext_getElem?
  intro i
  simp only [Array.getElem?_map, Array.getElem?_modify]
  split
  · cases f.blockTab[i]? with
    | none => rfl
    | some o => cases o <;> simp [hg]
  · rfl

/-- Case rule for loop bodies: an `if` whose two branches' successful results have `R`. (The
bodies of the passes' loops are large; `split at` on them exceeds `simp`'s step limit.) -/
theorem ok_ite {ε σ : Type} {R : σ → Prop} {p : Prop} [Decidable p] {A B : Except ε σ}
    (ha : ∀ s, A = .ok s → R s) (hb : ∀ s, B = .ok s → R s) :
    ∀ s, (if p then A else B) = .ok s → R s := by
  split
  · exact ha
  · exact hb

theorem CacheOnly.postorder (f : Func) : CacheOnly f f.postorder.2 := by
  unfold Func.postorder
  split
  · exact CacheOnly.refl f
  · exact ⟨_, rfl⟩

theorem CacheOnly.idom (f : Func) : CacheOnly f f.idom.2 := by
  unfold Func.idom
  split
  · exact CacheOnly.refl f
  · exact ⟨_, rfl⟩

theorem CacheOnly.sdom (f : Func) : CacheOnly f f.sdom.2 := by
  unfold Func.sdom
  split
  · exact CacheOnly.refl f
  · have h1 := CacheOnly.idom f
    have h2 := CacheOnly.postorder f.idom.2
    exact (h1.trans h2).trans ⟨_, rfl⟩

theorem CacheOnly.loopnestfor {f : Func} {n : Analysis.LoopNest} {g : Func}
    (h : f.loopnestfor = .ok (n, g)) : CacheOnly f g := by
  unfold Func.loopnestfor at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · cases h
    exact (CacheOnly.postorder f).trans (CacheOnly.sdom _)

theorem CacheOnly.loopnest {f : Func} {n : Analysis.LoopNest} {g : Func}
    (h : f.loopnest = .ok (n, g)) : CacheOnly f g := by
  unfold Func.loopnest at h
  split at h
  · cases h; exact CacheOnly.refl f
  · simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · rename_i r hr
      cases h
      exact (CacheOnly.loopnestfor hr).trans ⟨_, rfl⟩

end GoFV.Proof
