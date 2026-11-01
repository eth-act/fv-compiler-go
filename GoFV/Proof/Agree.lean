import GoFV.Proof.Frame
import GoFV.Proof.Eval

/-!
# Unchanged blocks in frames that differ on unread values

A pass that rewrites part of a function leaves the other blocks alone: same values (with the
same table entries), kind, controls and successors. Running such a block in two frames that
agree outside a set `X` of values the block does not read and does not define gives the same
outcome, with frames that still agree outside `X` (`enterBlock_agree`, `stepTerm_agree`).
Contexts may differ (another function) as long as they agree on what the evaluation reads:
tables, parameters, activation, the shapes of the block's values and its schedule.
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem

/-- Two table entries that evaluate alike: the same ID, op, aux, auxint and arguments (the
shape comes from the context, `CtxAgree.tys`; positions, use counts and blocks are not read). -/
def SemEq : Option Value → Option Value → Prop
  | some v, some v' => v'.id = v.id ∧ v'.op = v.op ∧ v'.aux = v.aux ∧ v'.auxInt = v.auxInt ∧
      v'.args = v.args
  | none, none => True
  | _, _ => False

theorem SemEq.refl : ∀ o : Option Value, SemEq o o
  | some _ => ⟨rfl, rfl, rfl, rfl, rfl⟩
  | none => trivial

/-- Evaluation reads of the context only the tables, the parameters, the activation and the
value's shape. -/
theorem evalValue_ctx_congr {env : Env} {ctxS ctxT : Ctx} {frS frT : Frame} {v v' : Value}
    (hv : SemEq (some v) (some v'))
    (hfr : frT = { frS with regs := frT.regs }) (hag : ∀ a ∈ v.args, frT.regs[a]? = frS.regs[a]?)
    (hty : ctxT.tys[v.id]? = ctxS.tys[v.id]?) (htabs : ctxT.tabs = ctxS.tabs)
    (hpar : ctxT.params = ctxS.params) (hact : ctxT.act = ctxS.act) :
    evalValue env ctxT frT v' = evalValue env ctxS frS v := by
  obtain ⟨hid, hop, haux, hai, hargs⟩ := hv
  rw [← evalValue_congr (env := env) (ctx := ctxT) hfr fun a ha => (hag a (hargs ▸ ha)).symm]
  unfold evalValue
  rw [hargs, hid, hty]
  simp only [evalOp_congr (ctx := ctxS) (ctx' := ctxT) (v := v) (v' := v') hop haux hai hid htabs
    hpar hact]

/-- What two contexts agree on for the values of a list. -/
structure CtxAgree (ctxS ctxT : Ctx) (l : List ID) : Prop where
  value : ∀ x ∈ l, SemEq (ctxS.f.value? x) (ctxT.f.value? x)
  tys : ∀ x ∈ l, ∀ v, ctxS.f.value? x = some v → ctxT.tys[v.id]? = ctxS.tys[v.id]?
  tabs : ctxT.tabs = ctxS.tabs
  params : ctxT.params = ctxS.params
  act : ctxT.act = ctxS.act

theorem CtxAgree.mono {ctxS ctxT : Ctx} {l l' : List ID} (h : CtxAgree ctxS ctxT l)
    (hs : ∀ x ∈ l', x ∈ l) : CtxAgree ctxS ctxT l' :=
  ⟨fun z hz => h.value z (hs z hz), fun z hz => h.tys z (hs z hz), h.tabs, h.params, h.act⟩

/-- The values of a list are outside `X` and read nothing in `X`. -/
def Unread (f : Func) (X : ID → Prop) (l : List ID) : Prop :=
  ∀ x ∈ l, ¬ X x ∧ ∀ v, f.value? x = some v → ∀ a ∈ v.args, ¬ X a

theorem Unread.mono {f : Func} {X : ID → Prop} {l l' : List ID} (h : Unread f X l)
    (hs : ∀ x ∈ l', x ∈ l) : Unread f X l' := fun z hz => h z (hs z hz)

theorem stepV_agree {env : Env} {ctxS ctxT : Ctx} {frS frT : Frame} {X : ID → Prop} {x : ID}
    {l : List ID} (hx : x ∈ l) (hc : CtxAgree ctxS ctxT l) (hu : Unread ctxS.f X l)
    (hfr : frT = { frS with regs := frT.regs }) (hag : ∀ a, ¬ X a → frT.regs[a]? = frS.regs[a]?) :
    stepV env ctxT frT x = stepV env ctxS frS x := by
  unfold stepV
  have hsem := hc.value x hx
  cases hv : ctxS.f.value? x with
  | none =>
    rw [hv] at hsem
    cases hv' : ctxT.f.value? x with
    | none => rfl
    | some _ => rw [hv'] at hsem; exact hsem.elim
  | some v =>
    rw [hv] at hsem
    cases hv' : ctxT.f.value? x with
    | none => rw [hv'] at hsem; exact hsem.elim
    | some v' =>
      rw [hv'] at hsem
      exact evalValue_ctx_congr hsem hfr (fun a ha => hag a ((hu x hx).2 v hv a ha))
        (hc.tys x hx v hv) hc.tabs hc.params hc.act

/-- **Evaluating a list in agreeing frames.** -/
theorem evalAll_agree {env : Env} {ctxS ctxT : Ctx} {X : ID → Prop} :
    ∀ {l : List ID} {frS frT : Frame}, CtxAgree ctxS ctxT l → Unread ctxS.f X l →
      frT = { frS with regs := frT.regs } → frT.regs.size = frS.regs.size →
      (∀ a, ¬ X a → frT.regs[a]? = frS.regs[a]?) →
      (∀ G, evalAll env ctxS frS l = .ok G → ∃ GT, evalAll env ctxT frT l = .ok GT ∧
        GT = { G with regs := GT.regs } ∧ GT.regs.size = G.regs.size ∧
        ∀ a, ¬ X a → GT.regs[a]? = G.regs[a]?) ∧
      (∀ e m, evalAll env ctxS frS l = .panic e m → evalAll env ctxT frT l = .panic e m)
  | [], frS, frT, _, _, hfr, hs, hag =>
    ⟨fun G h => by cases h; exact ⟨frT, rfl, hfr, hs, hag⟩, fun _ _ h => (nomatch h)⟩
  | x :: l, frS, frT, hc, hu, hfr, hs, hag => by
    have hx := stepV_agree (env := env) List.mem_cons_self hc hu hfr hag
    rw [evalAll_cons, evalAll_cons, hx]
    cases hst : stepV env ctxS frS x with
    | panic e m => exact ⟨fun _ h => (nomatch h), fun _ _ h => h⟩
    | stuck msg => exact ⟨fun _ h => (nomatch h), fun _ _ h => (nomatch h)⟩
    | ok y =>
      simp only
      refine evalAll_agree (hc.mono fun z hz => List.mem_cons_of_mem _ hz)
        (hu.mono fun z hz => List.mem_cons_of_mem _ hz) (by rw [hfr]; rfl)
        (by simp [Frame.set, hs]) fun a ha => ?_
      by_cases hxa : x = a
      · subst hxa
        simp only [Frame.set, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self, hs]
      · rw [Frame.set_regs_ne hxa, Frame.set_regs_ne hxa]; exact hag a ha

/-- The fields of a block its entry and terminator read. -/
structure BlockAgree (bS bT : Block) : Prop where
  id : bT.id = bS.id
  values : bT.values = bS.values
  kind : bT.kind = bS.kind
  controls : bT.controls = bS.controls
  succs : bT.succs = bS.succs

theorem phiStep_agree {ctxS ctxT : Ctx} {frS frT : Frame} {X : ID → Prop} {i : Nat} {z : ID}
    {l : List ID} (hz : z ∈ l) (hc : CtxAgree ctxS ctxT l)
    (hu : ∀ v, ctxS.f.value? z = some v → v.op = .Phi → ∀ a, v.args[i]? = some a → ¬ X a)
    (hown : ∀ v, ctxS.f.value? z = some v → v.id = z)
    (hag : ∀ a, ¬ X a → frT.regs[a]? = frS.regs[a]?) :
    phiStep ctxT frT i z = phiStep ctxS frS i z := by
  unfold phiStep
  have hsem := hc.value z hz
  cases hv : ctxS.f.value? z with
  | none =>
    rw [hv] at hsem
    cases hv' : ctxT.f.value? z with
    | none => rfl
    | some _ => rw [hv'] at hsem; exact hsem.elim
  | some v =>
    rw [hv] at hsem
    cases hv' : ctxT.f.value? z with
    | none => rw [hv'] at hsem; exact hsem.elim
    | some v' =>
    rw [hv'] at hsem
    obtain ⟨-, hop, -, -, hargs⟩ := hsem
    have hty : ctxT.tys[z]? = ctxS.tys[z]? := by
      have := hc.tys z hz v hv; rwa [hown v hv] at this
    simp only [hty, hop, hargs]
    by_cases hph : v.op = .Phi
    · simp only [hph, beq_self_eq_true, ite_true]
      cases ha : v.args[i]? with
      | none => rfl
      | some a => simp only [hag a (hu v hv hph a ha)]
    · simp only [show (v.op == .Phi) = false by simpa using hph, Bool.false_eq_true, ite_false]

theorem filterMapM_phi_agree {ctxS ctxT : Ctx} {frS frT : Frame} {X : ID → Prop} {i : Nat}
    {L : List ID} (hc : CtxAgree ctxS ctxT L)
    (hu : ∀ z ∈ L, ∀ v, ctxS.f.value? z = some v → v.op = .Phi → ∀ a, v.args[i]? = some a → ¬ X a)
    (hown : ∀ z ∈ L, ∀ v, ctxS.f.value? z = some v → v.id = z)
    (hag : ∀ a, ¬ X a → frT.regs[a]? = frS.regs[a]?) :
    ∀ {l : List ID}, (∀ z ∈ l, z ∈ L) →
      l.filterMapM (phiStep ctxT frT i) = l.filterMapM (phiStep ctxS frS i)
  | [], _ => rfl
  | z :: l, hl => by
    rw [List.filterMapM_cons, List.filterMapM_cons,
      phiStep_agree (hl z List.mem_cons_self) hc (hu z (hl z List.mem_cons_self))
        (hown z (hl z List.mem_cons_self)) hag,
      filterMapM_phi_agree hc hu hown hag (l := l) fun y hy => hl y (List.mem_cons_of_mem _ hy)]

theorem setPhis_agree {X : ID → Prop} :
    ∀ (ps : List (ID × Val)) {r r' : Array (Option Val)}, r'.size = r.size →
      (∀ a, ¬ X a → r'[a]? = r[a]?) → ∀ a, ¬ X a → (setPhis ps r')[a]? = (setPhis ps r)[a]?
  | [], _, _, _, h, a, ha => h a ha
  | (id, x) :: ps, r, r', hs, h, a, ha => by
    unfold setPhis
    rw [List.foldl_cons, List.foldl_cons]
    refine setPhis_agree ps (r := r.set! id (some x)) (r' := r'.set! id (some x))
      (by simp [hs]) (fun b hb => ?_) a ha
    simp only [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    split
    · rw [hs]
    · exact h b hb

/-- **Entering an unchanged block** in frames agreeing outside `X`, where the block's values are
outside `X` and read nothing in `X` (its `Phi`s read along the incoming edge). -/
theorem enterBlock_agree {env : Env} {ctxS ctxT : Ctx} {frS frT : Frame} {bS bT : Block}
    {i : Nat} {X : ID → Prop} (hb : BlockAgree bS bT)
    (hc : CtxAgree ctxS ctxT bS.values.toList)
    (hown : ∀ z ∈ bS.values, ∀ v, ctxS.f.value? z = some v → v.id = z)
    (hphi : ∀ z ∈ bS.values, ∀ v, ctxS.f.value? z = some v → v.op = .Phi →
      ∀ a, v.args[i]? = some a → ¬ X a)
    (hsched : (ctxT.sched[bS.id]?).join = (ctxS.sched[bS.id]?).join)
    (horder : ∀ o, (ctxS.sched[bS.id]?).join = some o →
      CtxAgree ctxS ctxT o.toList ∧ Unread ctxS.f X o.toList)
    (hfr : frT = { frS with regs := frT.regs }) (hs : frT.regs.size = frS.regs.size)
    (hag : ∀ a, ¬ X a → frT.regs[a]? = frS.regs[a]?) :
    (∀ G, enterBlock env ctxS frS bS i = .ok G → ∃ GT, enterBlock env ctxT frT bT i = .ok GT ∧
      GT = { G with regs := GT.regs } ∧ GT.regs.size = G.regs.size ∧
      ∀ a, ¬ X a → GT.regs[a]? = G.regs[a]?) ∧
    (∀ e m, enterBlock env ctxS frS bS i = .panic e m → enterBlock env ctxT frT bT i = .panic e m) := by
  rw [enterBlock_eq, enterBlock_eq, hb.values, hb.id,
    filterMapM_phi_agree hc (fun z hz => hphi z (Array.mem_toList_iff.1 hz))
      (fun z hz => hown z (Array.mem_toList_iff.1 hz)) hag (fun z hz => hz), hsched]
  cases hps : bS.values.toList.filterMapM (phiStep ctxS frS i) with
  | panic e m => exact ⟨fun _ h => (nomatch h), fun _ _ h => h⟩
  | stuck msg => exact ⟨fun _ h => (nomatch h), fun _ _ h => (nomatch h)⟩
  | ok ps =>
    simp only [Res.bind]
    cases ho : (ctxS.sched[bS.id]?).join with
    | none => exact ⟨fun _ h => (nomatch h), fun _ _ h => (nomatch h)⟩
    | some o =>
      obtain ⟨hco, huo⟩ := horder o ho
      exact evalAll_agree hco huo (by rw [hfr]) (by simp [setPhis_size, hs])
        (setPhis_agree ps hs hag)

/-- **The terminator of an unchanged block** reads only its controls. -/
theorem stepTerm_agree {frS frT : Frame} {bS bT : Block} (hb : BlockAgree bS bT)
    (hag : ∀ c ∈ bS.controls, frT.regs[c]? = frS.regs[c]?) :
    stepTerm frT bT = stepTerm frS bS := by
  have hc0 : Sem.control frT bT 0 = Sem.control frS bS 0 := by
    unfold Sem.control
    rw [hb.controls, hb.id]
    cases hk : bS.controls[0]? with
    | none => rfl
    | some c => simp only [hag c (Array.mem_of_getElem? hk)]
  have hs : ∀ k, succ bT k = succ bS k := fun k => by unfold succ; rw [hb.succs, hb.id]
  unfold stepTerm
  rw [hc0, hb.kind, hs 0, hs 1, hb.id]
  simp only [hs]

theorem list_filterMap_congr {α β : Type} {f g : α → Option β} :
    ∀ (l : List α), (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | x :: l, h => by
    rw [List.filterMap_cons, List.filterMap_cons, h x List.mem_cons_self,
      list_filterMap_congr l fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- A block with the same values, each evaluating alike, has the same schedule nodes. -/
theorem schedNodes_semEq {f g : Func} {fb gb : Block} (hv : gb.values = fb.values)
    (h : ∀ x ∈ fb.values, SemEq (f.value? x) (g.value? x)) : schedNodes g gb = schedNodes f fb := by
  unfold schedNodes
  rw [hv]
  apply Array.ext'
  simp only [Array.toList_filterMap]
  refine list_filterMap_congr _ fun x hx => ?_
  have hs := h x (Array.mem_toList_iff.1 hx)
  cases hf : f.value? x with
  | none =>
    rw [hf] at hs
    cases hg : g.value? x with
    | none => rfl
    | some _ => rw [hg] at hs; exact hs.elim
  | some v =>
    rw [hf] at hs
    cases hg : g.value? x with
    | none => rw [hg] at hs; exact hs.elim
    | some v' =>
      rw [hg] at hs
      obtain ⟨hid, hop, -, -, hargs⟩ := hs
      simp only [hid, hop, hargs]

end GoFV.Proof
