import GoFV.Proof.SimLoc
import GoFV.Proof.Pass.TrimLocCheck
import GoFV.Opt.Trim

/-!
# `trim` refines its input under `runLoc`

`refinesLoc_of_trimRelB`: if `trimRelB f g` (`GoFV.Proof.TrimLoc.trimRelB`), then `g` refines
`f` under `runLoc`; `trim_refinesLoc` is the pass wrapper.

The proof is a stuttering simulation (`runLoopLoc_simIH`) whose related states are equal machine
states, the source at the entry of block `x` and the target at the entry of block `t`, where `x`
is an entry point of `t` (`entryLocB f g x t`):

1. *Phis.* Under `runLoc` a `Phi` does nothing or gets stuck. So a defined source run of a value
   list is the run of its non-`Phi` values (`enterList_np_src`); a target block whose `Phi`s keep
   their arguments' homes (**phis**) runs exactly its non-`Phi` values (`enterList_np_tgt`).
2. *Chains.* From `x`, the source runs the removed blocks of the chain (each `Plain` without
   controls, so its terminator jumps to its successor and changes nothing:
   `stepTermLoc_plain`), then the kept block `t`: altogether the values `code` of
   `chaseLoc f g n x` and then `t`'s terminator (`chase_run`), consuming at least one block
   entry.
3. *Values.* The target block `t` runs `code` too, and each of these values (and its arguments)
   is a value of both functions with the same op, shape and, up to position, use count and
   block, the same fields (**values**, **closed**): the two contexts run it alike
   (`stepLoc_trim`, `enterList_trim`).
4. *Terminators.* `t`'s terminator in `g` is `f`'s up to its successors' targets (**kept**):
   it reads the same controls (`stepTermLoc_trim`) and jumps along the successor of the same
   index (`stepTermL_succs`), whose source target is an entry point of its target target
   (**kept**), which re-establishes the relation.
5. *Entry.* Both runs start from the same state (`refinesLoc_of_loop`, **ctx**) at entries
   related by **entry**.
-/

namespace GoFV.Proof.TrimLoc

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof

-- Unification must never unfold the scheduler (`kahn` is a big imperative loop).
attribute [local irreducible] schedule kahn schedValid

/-! ## Contexts -/

private theorem mk_f (tabs : Tables) (f : Func) : (LocCtx.make tabs f).ctx.f = f := by
  show (Ctx.makeL tabs f).f = f
  unfold Ctx.makeL; split <;> rfl

private theorem mk_homes (tabs : Tables) (f : Func) : (LocCtx.make tabs f).homes = locHomes f :=
  rfl

private theorem value?_some {f : Func} {id : ID} {v : Value} (h : f.value? id = some v) :
    f.valueTab[id]? = some (some v) := by
  unfold Func.value? at h
  cases h' : f.valueTab[id]? with
  | none => rw [h'] at h; cases h
  | some o => rw [h'] at h; cases o with
    | none => cases h
    | some w => cases h; rfl

/-- The shape of a value under `runLoc` depends on its type and on `lowered` only. -/
private theorem ty_of_value (tabs : Tables) {f : Func} {id : ID} {v : Value}
    (h : f.value? id = some v) :
    (LocCtx.make tabs f).ty id =
      ((if f.lowered then typeShapesL tabs else typeShapes tabs)[v.type]?.getD .other) := by
  have hv := value?_some h
  unfold LocCtx.ty
  show (Ctx.makeL tabs f).tys[id]?.getD .other = _
  unfold Ctx.makeL
  split
  · next hl =>
    simp only [hl, ↓reduceIte, Array.getElem?_map, hv, Option.map_some, Option.getD_some,
      valueTy]
  · next hl =>
    simp only [hl, Bool.false_eq_true, ↓reduceIte, Ctx.make, Array.getElem?_map, hv,
      Option.map_some, Option.getD_some, valueTy]

private theorem abi_eq (tabs : Tables) {f g : Func} (hown : f.ownAux = g.ownAux) :
    abiParams tabs f = abiParams tabs g := by
  unfold abiParams; rw [hown]

private theorem makeL_with (tabs : Tables) (f : Func) :
    ∃ tys, Ctx.makeL tabs f = { Ctx.make tabs f with tys } := by
  unfold Ctx.makeL
  split
  · exact ⟨_, rfl⟩
  · exact ⟨(Ctx.make tabs f).tys, rfl⟩

private theorem locCtxW_trim (tabs : Tables) {f g : Func} (hown : f.ownAux = g.ownAux)
    (hsize : f.valueTab.size = g.valueTab.size) (hra : f.low.regAlloc = g.low.regAlloc)
    (htr : f.low.tempRegs = g.low.tempRegs) :
    LocCtxW (LocCtx.make tabs f) (LocCtx.make tabs g) := by
  have hps := abi_eq tabs hown
  obtain ⟨t1, h1⟩ := makeL_with tabs f
  obtain ⟨t2, h2⟩ := makeL_with tabs g
  have hc : ∀ f, (LocCtx.make tabs f).ctx = Ctx.makeL tabs f := fun _ => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first
    | (show (LocCtx.make tabs f).homes = (LocCtx.make tabs g).homes
       unfold LocCtx.make; simp only [hsize, hra])
    | (show (LocCtx.make tabs f).temps = (LocCtx.make tabs g).temps
       unfold LocCtx.make; simp only [hsize, htr])
    | (rw [hc, hc, h1, h2]; simp only [Ctx.make, hps])

/-! ## The checker's facts -/

/-- What `trimRelB f g = true` gives. -/
structure Facts (f g : Func) : Prop where
  entry : f.entry = g.entry
  ownAux : f.ownAux = g.ownAux
  regAlloc : f.low.regAlloc = g.low.regAlloc
  tempRegs : f.low.tempRegs = g.low.tempRegs
  size : f.valueTab.size = g.valueTab.size
  lowered : f.lowered = g.lowered
  value : ∀ id v', g.value? id = some v' → ∃ v, f.value? id = some v ∧ v'.id = id ∧
    v.op = v'.op ∧ v.type = v'.type ∧ (v'.op ≠ .Phi → eraseVT v = eraseVT v') ∧
    ((v'.op = .Select0 ∨ v'.op = .Select1) → ∀ a ∈ v'.args, hasV g a = true)
  entryOK : entryLocB f g f.entry g.entry = true
  block : ∀ t T, g.block? t = some T → T.id = t ∧ keptLocB f g T = true ∧
    closedLocB g T = true ∧ phisLocB g (locHomes g) T = true

private theorem lt_of_block {f : Func} {bid : ID} {b : Block} (h : f.block? bid = some b) :
    bid < f.blockTab.size := by
  unfold Func.block? at h
  rcases Nat.lt_or_ge bid f.blockTab.size with hx | hx
  · exact hx
  · rw [Array.getElem?_eq_none hx] at h; cases h

private theorem lt_of_value {f : Func} {vid : ID} {v : Value} (h : f.value? vid = some v) :
    vid < f.valueTab.size := by
  unfold Func.value? at h
  rcases Nat.lt_or_ge vid f.valueTab.size with hx | hx
  · exact hx
  · rw [Array.getElem?_eq_none hx] at h; cases h

theorem facts_of_trimRelB {f g : Func} (h : trimRelB f g = true) : Facts f g := by
  unfold trimRelB at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨hc, hv⟩, he⟩, hb⟩ := h
  unfold ctxLocB at hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hc
  refine ⟨h1, h2, h3, h4, h5, h6, ?_, he, ?_⟩
  · intro id v' hg
    have := hv id (List.mem_range.2 (lt_of_value hg))
    unfold valLocB at this
    rw [hg] at this
    cases hf : f.value? id with
    | none => rw [hf] at this; cases this
    | some v =>
      rw [hf] at this
      simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at this
      obtain ⟨⟨⟨⟨hid, hop⟩, hty⟩, hor⟩, hsel⟩ := this
      refine ⟨v, rfl, hid, hop, hty, fun hne => ?_, fun hs a ha => ?_⟩
      · rcases hor with hp | hp
        · exact absurd hp hne
        · exact hp
      · have hs' : (v'.op == .Select0 || v'.op == .Select1) = true := by
          rcases hs with h | h <;> simp [h]
        rw [hs'] at hsel
        simp only [Bool.not_true, Array.all_eq_true] at hsel
        obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem ha
        rcases hsel with h | h
        · cases h
        · exact h i hi
  · intro t T ht
    have hm : (t, T) ∈ blocksIdx g := by
      unfold blocksIdx
      exact List.mem_filterMap.2 ⟨t, List.mem_range.2 (lt_of_block ht), by rw [ht]; rfl⟩
    have := hb (t, T) hm
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    obtain ⟨⟨⟨hid, hk⟩, hcl⟩, hph⟩ := this
    exact ⟨hid, hk, hcl, hph⟩

/-! ## Phis -/

theorem mem_npLoc {f : Func} {ids : List ID} {id : ID} (h : id ∈ npLoc f ids) :
    id ∈ ids ∧ ∀ v, f.value? id = some v → v.op ≠ .Phi := by
  unfold npLoc at h
  rw [List.mem_filter] at h
  refine ⟨h.1, fun v hv hp => ?_⟩
  have := h.2
  rw [hv] at this
  simp [hp] at this

private theorem enterList_cons {env : Env} {lc : LocCtx} {s : LocState} {id : ID} {ids : List ID}
    {v : Value} (hv : lc.ctx.f.value? id = some v) :
    enterListLoc env lc s (id :: ids) =
      match stepLoc env lc s v with
      | .ok s' => enterListLoc env lc s' ids
      | .panic e m => .panic e m
      | .stuck msg => .stuck msg := by
  cases h : stepLoc env lc s v <;> simp [enterListLoc, hv, h]

private theorem np_phi {f : Func} {id : ID} {ids : List ID} {v : Value}
    (hv : f.value? id = some v) (hp : v.op = .Phi) : npLoc f (id :: ids) = npLoc f ids := by
  unfold npLoc; simp [List.filter_cons, hv, hp]

private theorem np_nphi {f : Func} {id : ID} {ids : List ID} {v : Value}
    (hv : f.value? id = some v) (hp : v.op ≠ .Phi) :
    npLoc f (id :: ids) = id :: npLoc f ids := by
  unfold npLoc; simp [List.filter_cons, hv, hp]

private theorem np_none {f : Func} {id : ID} {ids : List ID} (hv : f.value? id = none) :
    npLoc f (id :: ids) = id :: npLoc f ids := by
  unfold npLoc; simp [List.filter_cons, hv]

private theorem stepLoc_phi (env : Env) (lc : LocCtx) (s : LocState) {v : Value}
    (hp : v.op = .Phi) :
    stepLoc env lc s v = if v.args.all (lc.home · == lc.home v.id) then .ok s
      else .stuck s!"phi v{v.id}: an argument has another home" := by
  unfold stepLoc
  simp only [hp, beq_self_eq_true, ↓reduceIte]

/-- A defined source run of a value list is the run of its non-`Phi` values. -/
theorem enterList_np_src (env : Env) (lc : LocCtx) :
    ∀ (l : List ID) (s : LocState), (∀ msg, enterListLoc env lc s l ≠ .stuck msg) →
      enterListLoc env lc s (npLoc lc.ctx.f l) = enterListLoc env lc s l := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons id ids ih =>
    intro s hns
    cases hv : lc.ctx.f.value? id with
    | none =>
      exfalso
      apply hns (s!"v{id} is not in the function")
      simp only [enterListLoc, hv]
    | some v =>
      by_cases hp : v.op = .Phi
      · rw [np_phi hv hp, enterList_cons hv, stepLoc_phi env lc s hp]
        rw [enterList_cons hv, stepLoc_phi env lc s hp] at hns
        by_cases hall : (v.args.all fun x => lc.home x == lc.home v.id) = true
        · simp only [hall, ↓reduceIte] at hns ⊢
          exact ih s hns
        · simp only [hall, Bool.false_eq_true, ↓reduceIte] at hns
          exact absurd rfl (hns _)
      · rw [np_nphi hv hp, enterList_cons hv, enterList_cons hv]
        rw [enterList_cons hv] at hns
        cases hs : stepLoc env lc s v with
        | ok s' =>
          rw [hs] at hns
          exact ih s' hns
        | panic e m => rfl
        | stuck msg => rfl

/-- A list whose `Phi`s keep their arguments' homes runs as its non-`Phi` values. -/
theorem enterList_np_tgt (env : Env) (lc : LocCtx) :
    ∀ (l : List ID) (s : LocState), (∀ id ∈ l, ∀ v, lc.ctx.f.value? id = some v →
        v.op = .Phi → v.args.all (lc.home · == lc.home v.id) = true) →
      enterListLoc env lc s (npLoc lc.ctx.f l) = enterListLoc env lc s l := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons id ids ih =>
    intro s hph
    have hph' : ∀ id ∈ ids, ∀ v, lc.ctx.f.value? id = some v → v.op = .Phi →
        v.args.all (lc.home · == lc.home v.id) = true :=
      fun i hi => hph i (List.mem_cons_of_mem _ hi)
    cases hv : lc.ctx.f.value? id with
    | none =>
      rw [np_none hv]
      simp only [enterListLoc, hv]
    | some v =>
      by_cases hp : v.op = .Phi
      · have hall := hph id List.mem_cons_self v hv hp
        rw [np_phi hv hp, enterList_cons hv, stepLoc_phi env lc s hp]
        simp only [hall, ↓reduceIte]
        exact ih s hph'
      · rw [np_nphi hv hp, enterList_cons hv, enterList_cons hv]
        cases stepLoc env lc s v with
        | ok s' => exact ih s' hph'
        | panic e m => rfl
        | stuck msg => rfl

/-! ## Values -/

section Values

variable {tabs : Tables} {f g : Func} (F : Facts f g)
include F

theorem ty_trim {id : ID} {v' : Value} (hg : g.value? id = some v') :
    (LocCtx.make tabs f).ty id = (LocCtx.make tabs g).ty id := by
  obtain ⟨v, hf, -, -, hty, -⟩ := F.value id v' hg
  rw [ty_of_value tabs hf, ty_of_value tabs hg, F.lowered, hty]

theorem stepLoc_trim (env : Env) (s : LocState) {id : ID} {v' : Value}
    (hg : g.value? id = some v') (hnp : v'.op ≠ .Phi) (hargs : ∀ a ∈ v'.args, hasV g a = true)
    {v : Value} (hf : f.value? id = some v) :
    stepLoc env (LocCtx.make tabs f) s v = stepLoc env (LocCtx.make tabs g) s v' := by
  obtain ⟨v1, hf1, hid, -, -, he, -⟩ := F.value id v' hg
  rw [hf] at hf1; cases hf1
  have he := he hnp
  have hw := locCtxW_trim tabs F.ownAux F.size F.regAlloc F.tempRegs
  have hpres : ∀ a ∈ v'.args, ∃ u', g.value? a = some u' := fun a ha => by
    have := hargs a ha
    unfold hasV at this
    cases h : g.value? a with
    | none => rw [h] at this; cases this
    | some u' => exact ⟨u', rfl⟩
  have e1 : stepLoc env (LocCtx.make tabs f) s v =
      stepLoc env (LocCtx.make tabs f) s (eraseVT v) := (rfl)
  have e2 : stepLoc env (LocCtx.make tabs f) s v' =
      stepLoc env (LocCtx.make tabs f) s (eraseVT v') := (rfl)
  rw [e1, he, ← e2]
  refine stepLoc_congrW hw s v' (by rw [hid]; exact ty_trim F hg)
    (fun a ha => by obtain ⟨u', hu⟩ := hpres a ha; exact ty_trim F hu) ?_
  unfold sxArgLoc
  rw [mk_f, mk_f]
  cases h0 : v'.args[0]? with
  | none => rfl
  | some a =>
    obtain ⟨u', hu⟩ := hpres a (Array.mem_of_getElem? h0)
    obtain ⟨u, hu', -, hop, -, heu, hsel⟩ := F.value a u' hu
    simp only [Option.bind_some, hu, hu', Option.map_some, Option.some.injEq]
    refine Arm64.signExtendsIn_congr hop fun hs => ?_
    have hs' : u'.op = .Select0 ∨ u'.op = .Select1 := hop ▸ hs
    have hnp' : u'.op ≠ .Phi := by rcases hs' with h | h <;> rw [h] <;> decide
    have hargs' : u.args = u'.args := by have := congrArg Value.args (heu hnp'); exact this
    rw [hargs']
    cases hc : u'.args[0]? with
    | none => rfl
    | some c =>
      have hcv := hsel hs' c (Array.mem_of_getElem? hc)
      unfold hasV at hcv
      cases hw' : g.value? c with
      | none => rw [hw'] at hcv; cases hcv
      | some w' =>
        obtain ⟨w, hw, -, hopw, -⟩ := F.value c w' hw'
        simp only [Option.bind_some, hw, hw', Option.map_some, hopw]

/-- A list of non-`Phi` values of `g` with arguments in `g` runs alike in both contexts. -/
theorem enterList_trim (env : Env) :
    ∀ (code : List ID) (s : LocState), (∀ id ∈ code, ∃ v', g.value? id = some v' ∧
        v'.op ≠ .Phi ∧ ∀ a ∈ v'.args, hasV g a = true) →
      enterListLoc env (LocCtx.make tabs f) s code = enterListLoc env (LocCtx.make tabs g) s code := by
  intro code
  induction code with
  | nil => intro _ _; rfl
  | cons id ids ih =>
    intro s hc
    obtain ⟨v', hg, hnp, hargs⟩ := hc id List.mem_cons_self
    obtain ⟨v, hf, -⟩ := F.value id v' hg
    unfold enterListLoc
    rw [mk_f, mk_f, hf, hg]
    dsimp only
    rw [stepLoc_trim F env s hg hnp hargs hf]
    cases stepLoc env (LocCtx.make tabs g) s v' with
    | ok s' => exact ih s' fun i hi => hc i (List.mem_cons_of_mem _ hi)
    | panic e m => rfl
    | stuck msg => rfl

end Values

/-! ## Terminators -/

/-- The staging of `stepTermLoc`'s controls. -/
def stageBody (lc : LocCtx) (s : LocState) (c : ID) (regs : Array (Option Val)) :
    Res (ForInStep (Array (Option Val))) := do
  let x ← s.control lc c
  pure (ForInStep.yield (if c < regs.size then regs.set! c (some x) else regs))

/-- The state with the block controls staged in `regs`. -/
def stageLoc (s : LocState) (regs : Array (Option Val)) : LocState :=
  { s with fr := { s.fr with regs } }

private theorem ok_bind {α β : Type} (a : α) (k : α → Res β) : (Res.ok a >>= k) = k a := rfl

theorem stepTermLoc_eq (lc : LocCtx) (s : LocState) (b : Block) :
    stepTermLoc lc s b =
      (forIn b.controls.toList s.fr.regs (stageBody lc s)) >>= fun regs =>
        (stepTermL (stageLoc s regs).fr b) >>= fun n => pure (n, stageLoc s regs) := by
  unfold stepTermLoc
  rw [Array.forIn_toList]
  rfl

theorem forIn_stage_congr {lc lc' : LocCtx} {s : LocState} :
    ∀ (l : List ID) (regs : Array (Option Val)), (∀ c ∈ l, s.control lc c = s.control lc' c) →
      forIn l regs (stageBody lc s) = forIn l regs (stageBody lc' s) := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons c cs ih =>
    intro regs h
    simp only [List.forIn_cons, stageBody, h c List.mem_cons_self]
    cases s.control lc' c with
    | ok x => exact ih _ fun c' hc' => h c' (List.mem_cons_of_mem _ hc')
    | panic e m => rfl
    | stuck msg => rfl

section Term

variable {tabs : Tables} {f g : Func} (F : Facts f g)
include F

theorem control_trim (s : LocState) {c : ID} {v' : Value} (hg : g.value? c = some v')
    (hmr : v'.op = .MakeResult → ∀ a ∈ v'.args, hasV g a = true) :
    s.control (LocCtx.make tabs f) c = s.control (LocCtx.make tabs g) c := by
  obtain ⟨v, hf, -, hop, -, he, -⟩ := F.value c v' hg
  have hw := locCtxW_trim tabs F.ownAux F.size F.regAlloc F.tempRegs
  unfold LocState.control
  rw [mk_f, mk_f, hf, hg]
  dsimp only
  rw [hop, read_congrW hw s (ty_trim F hg), ty_trim F hg]
  by_cases hm : v'.op = .MakeResult
  · have hne : v'.op ≠ .Phi := by rw [hm]; decide
    have hargs : v.args = v'.args := by
      have := congrArg Value.args (he hne); exact this
    have hmap : ∀ l : List ID, (∀ a ∈ l, hasV g a = true) →
        l.mapM (s.read (LocCtx.make tabs f)) = l.mapM (s.read (LocCtx.make tabs g)) := by
      intro l hl
      refine mapM_congr' _ fun a ha => read_congrW hw s ?_
      have := hl a ha
      unfold hasV at this
      cases h : g.value? a with
      | none => rw [h] at this; cases this
      | some u' => exact ty_trim F h
    rw [hargs, hmap v'.args.toList fun a ha => hmr hm a (Array.mem_toList_iff.1 ha)]
  · simp only [hm, beq_iff_eq, ↓reduceIte]

/-- The terminator of a kept block runs in `g` as in `f`, up to the successors' targets. -/
theorem stepTermLoc_trim (s : LocState) {T Kf : Block} (hT : g.block? T.id = some T)
    (hK : f.block? T.id = some Kf) :
    (∀ e s', stepTermLoc (LocCtx.make tabs f) s Kf = .ok (.goto e, s') →
      ∃ e', SuccIdx Kf T.succs e e' ∧ stepTermLoc (LocCtx.make tabs g) s T = .ok (.goto e', s')) ∧
    (∀ rs m s', stepTermLoc (LocCtx.make tabs f) s Kf = .ok (.ret rs m, s') →
      ∃ s'', stepTermLoc (LocCtx.make tabs g) s T = .ok (.ret rs m, s'')) ∧
    (∀ e m, stepTermLoc (LocCtx.make tabs f) s Kf = .panic e m →
      stepTermLoc (LocCtx.make tabs g) s T = .panic e m) := by
  obtain ⟨-, hk, hcl, -⟩ := F.block T.id T hT
  unfold keptLocB at hk
  rw [hK] at hk
  simp only [Bool.and_eq_true, beq_iff_eq] at hk
  obtain ⟨⟨he, hsz⟩, -⟩ := hk
  -- `T` is `Kf` with other successors (and fields no terminator reads)
  have hctl : T.controls = Kf.controls := by have := congrArg Block.controls he; exact this
  have hTK : ∀ fr, stepTermL fr T = stepTermL fr { Kf with succs := T.succs } := by
    intro fr
    calc stepTermL fr T = stepTermL fr { eraseBT T with succs := T.succs } := (rfl)
      _ = stepTermL fr { eraseBT Kf with succs := T.succs } := by rw [he]
      _ = stepTermL fr { Kf with succs := T.succs } := (rfl)
  -- the controls read alike
  have hc : ∀ c ∈ Kf.controls.toList, s.control (LocCtx.make tabs f) c =
      s.control (LocCtx.make tabs g) c := by
    intro c hc
    unfold closedLocB at hcl
    simp only [Bool.and_eq_true, Array.all_eq_true'] at hcl
    have := hcl.2 c (by rw [hctl]; exact Array.mem_toList_iff.1 hc)
    cases hg : g.value? c with
    | none => rw [hg] at this; cases this
    | some v' =>
      rw [hg] at this
      refine control_trim F s hg fun hm a ha => ?_
      simp only [hm, bne_self_eq_false, Bool.false_or, Array.all_eq_true'] at this
      exact this a ha
  rw [stepTermLoc_eq, stepTermLoc_eq, hctl, forIn_stage_congr _ _ hc]
  have hsz' : T.succs.size = Kf.succs.size := hsz
  cases forIn Kf.controls.toList s.fr.regs (stageBody (LocCtx.make tabs g) s) with
  | ok regs =>
    have hrel := stepTermL_succs (stageLoc s regs).fr Kf T.succs hsz'
    rw [← hTK] at hrel
    simp only [ok_bind]
    generalize stepTermL (stageLoc s regs).fr Kf = A at hrel ⊢
    generalize stepTermL (stageLoc s regs).fr T = B at hrel ⊢
    cases hrel with
    | goto hidx =>
      refine ⟨fun e s' h => ?_, fun _ _ _ h => ?_, fun _ _ h => ?_⟩
      · cases h; exact ⟨_, hidx, rfl⟩
      · cases h
      · cases h
    | ret rs m =>
      refine ⟨fun e s' h => ?_, fun _ _ _ h => ?_, fun _ _ h => ?_⟩
      · cases h
      · cases h; exact ⟨_, rfl⟩
      · cases h
    | panic e m =>
      exact ⟨fun _ _ h => (nomatch h), fun _ _ _ h => (nomatch h), fun _ _ h => h⟩
    | stuck msg msg' =>
      exact ⟨fun _ _ h => (nomatch h), fun _ _ _ h => (nomatch h), fun _ _ h => (nomatch h)⟩
  | panic e m =>
    exact ⟨fun _ _ h => (nomatch h), fun _ _ _ h => (nomatch h), fun _ _ h => h⟩
  | stuck msg =>
    exact ⟨fun _ _ h => (nomatch h), fun _ _ _ h => (nomatch h), fun _ _ h => (nomatch h)⟩

end Term

/-! ## Chains -/

/-- The continuation of `runLoopLoc` after block `b`'s values: its terminator, then the loop. -/
def termLoc (env : Env) (lc : LocCtx) (fuel : Nat) (s : LocState) (b : Block) : Outcome :=
  match stepTermLoc lc s b with
  | .ok (.goto e, s) => runLoopLoc env lc fuel s e.b
  | .ok (.ret rs m, _) => .returned rs m
  | .panic e m => .panicked e m
  | .stuck msg => .stuck msg

theorem runLoopLoc_enter (env : Env) (lc : LocCtx) (fuel : Nat) (s : LocState) {bid : ID}
    {b : Block} (hb : lc.ctx.f.block? bid = some b) :
    runLoopLoc env lc (fuel + 1) s bid =
      match enterBlockLoc env lc s b with
      | .panic e m => .panicked e m
      | .stuck msg => .stuck msg
      | .ok s => termLoc env lc fuel s b := by
  rw [runLoopLoc_succ, hb]; rfl

/-- **Chains.** From the entry of `x`, a defined source run runs the chain's values `code` and
then the terminator of the chain's kept end `t`, after at least one block entry. -/
theorem chase_run {tabs : Tables} {f g : Func} (env : Env) :
    ∀ (k : Nat) (x t : ID) (code : List ID), chaseLoc f g k x = some (t, code) →
      ∃ Kf, f.block? t = some Kf ∧ ∀ (m : Nat) (s : LocState),
        (runLoopLoc env (LocCtx.make tabs f) m s x).Defined → ∃ m', m' + 1 ≤ m ∧
          ((∃ s1, enterListLoc env (LocCtx.make tabs f) s code = .ok s1 ∧
              runLoopLoc env (LocCtx.make tabs f) m s x =
                termLoc env (LocCtx.make tabs f) m' s1 Kf) ∨
           (∃ e mm, enterListLoc env (LocCtx.make tabs f) s code = .panic e mm ∧
              runLoopLoc env (LocCtx.make tabs f) m s x = .panicked e mm)) := by
  intro k
  induction k with
  | zero => intro _ _ _ h; cases h
  | succ k ih =>
    intro x t code h
    unfold chaseLoc at h
    cases hc : f.block? x with
    | none => rw [hc] at h; cases h
    | some c =>
      rw [hc] at h
      dsimp only at h
      have hb : (LocCtx.make tabs f).ctx.f.block? x = some c := by rw [mk_f]; exact hc
      split at h
      · -- `x` is kept: `t = x`
        cases h
        refine ⟨c, hc, fun m s hd => ?_⟩
        cases m with
        | zero => exact hd.elim
        | succ m =>
          refine ⟨m, Nat.le_refl _, ?_⟩
          rw [runLoopLoc_enter env _ m s hb] at hd ⊢
          have hne : ∀ msg, enterListLoc env (LocCtx.make tabs f) s c.values.toList ≠
              .stuck msg := by
            intro msg hm
            rw [enterBlockLoc_eq, hm] at hd
            exact hd
          have hnp := enterList_np_src env (LocCtx.make tabs f) c.values.toList s hne
          rw [mk_f] at hnp
          rw [enterBlockLoc_eq, ← hnp]
          cases hs1 : enterListLoc env (LocCtx.make tabs f) s (npLoc f c.values.toList) with
          | ok s1 => exact .inl ⟨s1, rfl, rfl⟩
          | panic e mm => exact .inr ⟨e, mm, rfl, rfl⟩
          | stuck msg => exact (hne msg (by rw [← hnp]; exact hs1)).elim
      · split at h
        · next hpl =>
          simp only [Bool.and_eq_true, beq_iff_eq, Array.isEmpty_iff] at hpl
          obtain ⟨hk, hcn⟩ := hpl
          cases he : c.succs[0]? with
          | none => rw [he] at h; cases h
          | some e =>
            rw [he] at h
            dsimp only at h
            cases hch : chaseLoc f g k e.b with
            | none => rw [hch] at h; cases h
            | some r =>
              rw [hch] at h
              obtain ⟨t', code'⟩ := r
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨Kf, hKf, hrun⟩ := ih e.b _ code' hch
              refine ⟨Kf, hKf, fun m s hd => ?_⟩
              cases m with
              | zero => exact hd.elim
              | succ m =>
                rw [runLoopLoc_enter env _ m s hb] at hd ⊢
                have hne : ∀ msg, enterListLoc env (LocCtx.make tabs f) s c.values.toList ≠
                    .stuck msg := by
                  intro msg hm
                  rw [enterBlockLoc_eq, hm] at hd
                  exact hd
                have hnp := enterList_np_src env (LocCtx.make tabs f) c.values.toList s hne
                rw [mk_f] at hnp
                rw [enterBlockLoc_eq, ← hnp] at hd ⊢
                rw [enterListLoc_append]
                cases hs1 : enterListLoc env (LocCtx.make tabs f) s (npLoc f c.values.toList) with
                | ok s1 =>
                  rw [hs1] at hd
                  dsimp only at hd ⊢
                  have hpl : ∀ (n : Nat), termLoc env (LocCtx.make tabs f) n s1 c =
                      runLoopLoc env (LocCtx.make tabs f) n s1 e.b := by
                    intro n
                    unfold termLoc
                    rw [stepTermLoc_plain _ _ hk hcn he]
                  rw [hpl] at hd ⊢
                  obtain ⟨m', hle, hcase⟩ := hrun m s1 hd
                  exact ⟨m', by omega, hcase⟩
                | panic e' mm =>
                  exact ⟨m, Nat.le_refl _, .inr ⟨e', mm, rfl, rfl⟩⟩
                | stuck msg => rw [hs1] at hd; exact hd.elim
        · cases h

/-! ## The simulation -/

/-- **`trimRelB f g` makes `g` refine `f` under `runLoc`.** -/
theorem refinesLoc_of_trimRelB {tabs : Tables} {f g : Func} (h : trimRelB f g = true) :
    RefinesLoc tabs g tabs f := by
  have F := facts_of_trimRelB h
  have hw := locCtxW_trim tabs F.ownAux F.size F.regAlloc F.tempRegs
  refine refinesLoc_of_loop hw F.size fun env args mem fuel hd => ?_
  let R : LocState → ID → LocState → ID → Prop := fun sS x sT t =>
    sT = sS ∧ entryLocB f g x t = true
  refine runLoopLoc_simIH (lcS := LocCtx.make tabs f) (lcT := LocCtx.make tabs g) R
    (fun n ih sS x sT t hR hd => ?_) fuel _ _ _ _ ⟨rfl, F.entryOK⟩ hd
  obtain ⟨hst, hE⟩ := hR
  rw [hst]
  unfold entryLocB at hE
  cases hch : chaseLoc f g (chaseFuel f) x with
  | none => rw [hch] at hE; cases hE
  | some r =>
    obtain ⟨t', code⟩ := r
    rw [hch] at hE
    simp only [Bool.and_eq_true, beq_iff_eq] at hE
    obtain ⟨ht, hT⟩ := hE
    subst ht
    cases hgt : g.block? t' with
    | none => rw [hgt] at hT; cases hT
    | some T =>
      rw [hgt] at hT
      simp only [beq_iff_eq] at hT
      obtain ⟨Kf, hKf, hrun⟩ := chase_run (tabs := tabs) env _ x t' code hch
      obtain ⟨hid, hk, hcl, hph⟩ := F.block t' T hgt
      obtain ⟨m', hle, hcase⟩ := hrun (n + 1) sS hd
      have hTid : g.block? T.id = some T := by rw [hid]; exact hgt
      have hKid : f.block? T.id = some Kf := by rw [hid]; exact hKf
      have hbG : (LocCtx.make tabs g).ctx.f.block? t' = some T := by rw [mk_f]; exact hgt
      -- the target block runs `code`
      have hcode : ∀ s, enterBlockLoc env (LocCtx.make tabs g) s T =
          enterListLoc env (LocCtx.make tabs f) s code := by
        intro s
        rw [enterBlockLoc_eq]
        have hnp := enterList_np_tgt env (LocCtx.make tabs g) T.values.toList s (by
          intro id hm v hv hp
          rw [mk_f] at hv
          unfold phisLocB at hph
          rw [Array.all_eq_true'] at hph
          have := hph id (Array.mem_toList_iff.1 hm)
          rw [hv] at this
          simp only [hp, bne_self_eq_false, Bool.false_or] at this
          obtain ⟨-, -, hvid, -⟩ := F.value id v hv
          unfold LocCtx.home
          rw [mk_homes, hvid]
          exact this)
        rw [mk_f] at hnp
        rw [← hnp, hT]
        refine (enterList_trim F env code s fun id hm => ?_).symm
        rw [← hT] at hm
        unfold closedLocB at hcl
        simp only [Bool.and_eq_true, List.all_eq_true] at hcl
        have := hcl.1 id hm
        cases hg : g.value? id with
        | none => rw [hg] at this; cases this
        | some v' =>
          rw [hg] at this
          refine ⟨v', rfl, (mem_npLoc hm).2 v' hg, fun a ha => ?_⟩
          rw [Array.all_eq_true'] at this
          exact this a ha
      rcases hcase with ⟨s1, hs1, hsrc⟩ | ⟨e, mm, hs1, hsrc⟩
      · rw [hsrc] at hd ⊢
        have tg := stepTermLoc_trim (tabs := tabs) F s1 hTid hKid
        unfold termLoc at hd ⊢
        cases hst : stepTermLoc (LocCtx.make tabs f) s1 Kf with
        | ok p =>
          obtain ⟨nx, s2⟩ := p
          cases nx with
          | goto e =>
            obtain ⟨e', hidx, htgt⟩ := tg.1 e s2 hst
            rw [hst] at hd
            dsimp only at hd ⊢
            -- the successors are related
            have hrel : entryLocB f g e.b e'.b = true := by
              unfold keptLocB at hk
              rw [hKid] at hk
              simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at hk
              obtain ⟨k, hk1, hk2⟩ := hidx
              have hlt : k < Kf.succs.size := (Array.getElem?_eq_some_iff.1 hk1).1
              have := hk.2 k hlt
              rw [hk1, hk2] at this
              exact this
            obtain ⟨fuelT, hft⟩ := ih m' (by omega) s2 e.b s2 e'.b ⟨rfl, hrel⟩ hd
            refine ⟨fuelT + 1, ?_⟩
            rw [runLoopLoc_enter env _ fuelT sS hbG, hcode, hs1]
            dsimp only
            unfold termLoc
            rw [htgt]
            exact hft
          | ret rs mm =>
            obtain ⟨s'', htgt⟩ := tg.2.1 rs mm s2 hst
            refine ⟨m' + 1, ?_⟩
            rw [runLoopLoc_enter env _ m' sS hbG, hcode, hs1]
            dsimp only
            unfold termLoc
            rw [htgt]
        | panic e mm =>
          have htgt := tg.2.2 e mm hst
          refine ⟨m' + 1, ?_⟩
          rw [runLoopLoc_enter env _ m' sS hbG, hcode, hs1]
          dsimp only
          unfold termLoc
          rw [htgt]
        | stuck msg => rw [hst] at hd; exact hd.elim
      · refine ⟨m' + 1, ?_⟩
        rw [hsrc, runLoopLoc_enter env _ m' sS hbG, hcode, hs1]

end GoFV.Proof.TrimLoc

namespace GoFV.Proof

open GoFV.SSA GoFV.Opt

/-- **`trim` refines its input under `runLoc`**, when its input and output are in `trimRelB`
(0 rejections on the `trim` sections of quick-v7 and full-v9). -/
theorem trim_refinesLoc {penv : PassEnv} {f : Func} {out : PassOut}
    (h : trimPass penv f = .ok out) (hrel : TrimLoc.trimRelB f out.func = true) :
    RefinesLoc out.tables out.func penv.tables f := by
  simp only [trimPass, Pass.ofFunc, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · cases h
    exact TrimLoc.refinesLoc_of_trimRelB hrel

end GoFV.Proof
