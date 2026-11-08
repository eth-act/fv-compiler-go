import GoFV.Proof.FrameL
import GoFV.Proof.Avail

variable [GoFV.SSA.Sem.Addrs]

/-!
# `Val.retypeL` is idempotent; registers of a lowered run are typed

A value that already has shape `t` (`Val.hasTy`) is unchanged by `Val.widen t`
(`Val.widen_of_hasTy`): widening only moves a narrower integer or a boolean to a wider integer
or pointer shape, which such a value does not have. So `Val.retypeL t = Val.retype t ∘ Val.widen t`
is idempotent (`Val.retypeL_idem`), and so is the mode's shaping `LMode.retype md`
(`LMode.retype_idem`): a register written at its value's shape is fixed by reading it there.

`TypedL md ctx fr`: every register is fixed by `md.retype` at its value's shape (Phase 1's
`Typed` under mode `md`). A value's result is (`evalValueL_typed`), and entering a block keeps a
frame typed (`typedL_enter`). `tysL_of_value`: the shape of a value in `Ctx.makeL`.
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem

mutual
theorem Val.widen_of_hasTy : ∀ (t : Ty) (u : Val), u.hasTy t = true → u.widen t = u
  | .tuple ts, .tuple vs, h => by
    simp only [Val.hasTy] at h
    simp only [Val.widen, Val.widenList_of_hasTyPre ts vs h]
  | .int w', .int w x, h => by
    simp only [Val.hasTy, beq_iff_eq] at h
    subst h
    simp [Val.widen]
  | .ptr _, .int w x, h => by
    cases w <;> simp_all [Val.hasTy, Val.widen, Width.bits]
  | .int _, .bool _, h | .ptr _, .bool _, h => by simp [Val.hasTy] at h
  | .int _, .poison, _ | .int _, .mem _, _ | .int _, .tuple _, _ | .int _, .ptr _, _
  | .int _, .agg _, _ | .int _, .blob _, _ | .int _, .empty, _ => by simp [Val.widen]
  | .ptr _, .poison, _ | .ptr _, .mem _, _ | .ptr _, .tuple _, _ | .ptr _, .ptr _, _
  | .ptr _, .agg _, _ | .ptr _, .blob _, _ | .ptr _, .empty, _ => by simp [Val.widen]
  | .tuple _, .poison, _ | .tuple _, .int _ _, _ | .tuple _, .bool _, _ | .tuple _, .mem _, _
  | .tuple _, .ptr _, _ | .tuple _, .agg _, _ | .tuple _, .blob _, _
  | .tuple _, .empty, _ => by simp [Val.widen]
  | .bool, _, _ | .mem, _, _ | .other, _, _ | .agg _ _, _, _ | .str, _, _ | .slice _, _, _
  | .blob _, _, _ | .empty, _, _ | .opaque _, _, _ => by simp [Val.widen]

theorem Val.widenList_of_hasTyPre :
    ∀ (ts : List Ty) (vs : List Val), Val.hasTyPre vs ts = true → Val.widenList ts vs = vs
  | [], vs, _ => by cases vs <;> simp [Val.widenList]
  | _ :: _, [], _ => by simp [Val.widenList]
  | t :: ts, v :: vs, h => by
    simp only [Val.hasTyPre, Bool.and_eq_true] at h
    simp only [Val.widenList, Val.widen_of_hasTy t v h.1, Val.widenList_of_hasTyPre ts vs h.2]
end

/-- A value at shape `t` in lowered code has that shape. -/
theorem Val.retypeL_hasTy (t : Ty) (v : Val) : (v.retypeL t).hasTy t = true :=
  Val.retype_hasTy t _

theorem Val.retypeL_of_hasTy {t : Ty} {v : Val} (h : v.hasTy t = true) : v.retypeL t = v := by
  unfold Val.retypeL
  rw [Val.widen_of_hasTy t v h, Val.retype_of_hasTy h]

/-- **`Val.retypeL` is idempotent.** -/
theorem Val.retypeL_idem (t : Ty) (v : Val) : (v.retypeL t).retypeL t = v.retypeL t :=
  Val.retypeL_of_hasTy (Val.retypeL_hasTy t v)

/-- **A mode's shaping is idempotent.** -/
theorem LMode.retype_idem (md : LMode) (t : Ty) (v : Val) :
    md.retype t (md.retype t v) = md.retype t v := by
  unfold LMode.retype
  split
  · exact Val.retypeL_idem t v
  · exact Val.retype_idem t v

theorem LMode.retype_hasTy (md : LMode) (t : Ty) (v : Val) : (md.retype t v).hasTy t = true := by
  unfold LMode.retype
  split
  · exact Val.retypeL_hasTy t v
  · exact Val.retype_hasTy t v

/-! ## Typed registers -/

/-- Every register of a frame is fixed by `md.retype` at its value's shape. -/
def TypedL (md : LMode) (ctx : Ctx) (fr : Frame) : Prop :=
  ∀ (x : ID) (y : Val), fr.regs[x]? = some (some y) → md.retype (ctx.tys[x]?.getD .other) y = y

theorem typedL_replicate (md : LMode) (ctx : Ctx) (n : Nat) (fr : Frame)
    (h : fr.regs = Array.replicate n none) : TypedL md ctx fr := fun x y hx => by
  rw [h, Array.getElem?_replicate] at hx
  split at hx <;> cases hx

/-- A lowered value's result is fixed by `md.retype` at its own shape. -/
theorem evalValueL_typed {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {y : Val}
    (h : evalValueL md env ctx fr v = .ok y) : md.retype (ctx.tys[v.id]?.getD .other) y = y := by
  unfold evalValueL at h
  cases hm : v.args.toList.mapM (fun a =>
      Res.ofOption s!"v{v.id}: argument v{a} has no value" (fr.regs[a]?).join) with
  | panic e m => rw [hm] at h; cases h
  | stuck msg => rw [hm] at h; cases h
  | ok argv =>
    rw [hm] at h
    simp only [bind, Res.bind] at h
    cases ho : evalOpL md.faulting env ctx fr v argv (ctx.tys[v.id]?.getD .other) with
    | ok r => rw [ho] at h; cases h; exact LMode.retype_idem _ _ _
    | panic e m => rw [ho] at h; cases h
    | stuck msg => rw [ho] at h; cases h

/-- Setting the `Phi`s keeps the registers typed. -/
theorem typedL_phis {md : LMode} {ctx : Ctx} {blk : Block} {fr frP : Frame} {i : Nat}
    (ht : TypedL md ctx fr) (hPs : frP.regs.size = fr.regs.size)
    (hkeep : ∀ z, (z ∉ blk.values ∨ ∃ v, ctx.f.value? z = some v ∧ v.op ≠ .Phi) →
      frP.regs[z]? = fr.regs[z]?)
    (hphi : ∀ z ∈ blk.values, ∀ v, ctx.f.value? z = some v → v.op = .Phi → z < fr.regs.size →
      ∃ a y, v.args[i]? = some a ∧ fr.regs[a]? = some (some y) ∧
        frP.regs[z]? = some (some (md.retype (ctx.tys[z]?.getD .other) y)))
    (hall : ∀ z ∈ blk.values, (ctx.f.value? z).isSome) : TypedL md ctx frP := by
  intro z y hz
  by_cases hph : z ∈ blk.values ∧ ∃ v, ctx.f.value? z = some v ∧ v.op = .Phi
  · obtain ⟨hzb, v, hv, hp⟩ := hph
    have hlt : z < fr.regs.size := by
      rw [← hPs]
      rcases Nat.lt_or_ge z frP.regs.size with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none h'] at hz; cases hz
    obtain ⟨a, y0, -, -, hy⟩ := hphi z hzb v hv hp hlt
    rw [hz] at hy; cases hy
    exact LMode.retype_idem _ _ _
  · have hk : z ∉ blk.values ∨ ∃ v, ctx.f.value? z = some v ∧ v.op ≠ .Phi := by
      by_cases hzb : z ∈ blk.values
      · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hall z hzb)
        exact .inr ⟨v, hv, fun hp => hph ⟨hzb, v, hv, hp⟩⟩
      · exact .inl hzb
    rw [hkeep z hk] at hz
    exact ht z y hz

/-- Evaluating values with their own IDs keeps the registers typed. -/
theorem typedL_evalAll {md : LMode} {env : Env} {ctx : Ctx} {o : List ID} {fr fr' : Frame}
    (ht : TypedL md ctx fr) (hown : ∀ x ∈ o, ∀ v, ctx.f.value? x = some v → v.id = x)
    (e3 : ∀ z, z ∉ o → fr'.regs[z]? = fr.regs[z]?)
    (e4 : ∀ x ∈ o, ∃ v y, ctx.f.value? x = some v ∧ fr'.regs[x]? = some (some y) ∧
      evalValueL md env ctx fr' v = .ok y) : TypedL md ctx fr' := by
  intro z y hz
  by_cases hzo : z ∈ o
  · obtain ⟨v, y', hv, hy', hev'⟩ := e4 z hzo
    rw [hz] at hy'; cases hy'
    have := evalValueL_typed hev'
    rwa [hown z hzo v hv] at this
  · rw [e3 z hzo] at hz
    exact ht z y hz

/-- **Entering a lowered block keeps every register typed.** -/
theorem typedL_enter {md : LMode} {ce : CheckEnv} {tabs : Tables} {f : Func} {env : Env}
    (hwf : WF ce f) {b : ID} {blk : Block} (hb : b ∈ f.blocks) (hbb : f.block? b = some blk)
    {fr fr' : Frame} {i : Nat} (hs : fr.regs.size = f.valueTab.size)
    (ht : TypedL md (Ctx.makeL tabs f) fr)
    (h : enterBlockL md env (Ctx.makeL tabs f) fr blk i = .ok fr') :
    TypedL md (Ctx.makeL tabs f) fr' := by
  have hnd := hwf.valuesNodup b blk ⟨hb, hbb⟩
  have hown := valuesOwn hwf hb hbb
  obtain ⟨b', hb', hid⟩ := hwf.blockId b hb
  rw [hbb] at hb'; cases hb'
  obtain ⟨frP, o, ho, hev, -, hPs, hall, hkeep, hphi⟩ := enterBlockL_spec hnd h
  rw [hid, sched_of_blockL hbb] at ho
  obtain ⟨ond, otopo, omem⟩ := schedule_topo hown hnd ho
  have hcf := makeL_f tabs f
  obtain ⟨-, -, e3, e4⟩ := evalAllL_spec (ctx := Ctx.makeL tabs f) ond (by rw [hcf]; exact otopo)
    (by rw [hPs, hs, hcf]) hev
  refine typedL_evalAll (typedL_phis ht hPs hkeep hphi hall) (fun x hx v hv => ?_) e3 e4
  obtain ⟨v', hv', hvid⟩ := hown x ((omem x).1 hx).1
  rw [hcf] at hv
  rw [hv] at hv'; cases hv'; exact hvid

/-- The shapes of `runL`'s context for `f`: lowered (`typeShapesL`) if `f` is lowered. -/
def shapesL (low : Bool) (tabs : Tables) : Array Ty :=
  if low then typeShapesL tabs else typeShapes tabs

theorem tysL_of_value {tabs : Tables} {f : Func} {x : ID} {v : Value} (h : f.value? x = some v) :
    (Ctx.makeL tabs f).tys[x]? = some ((shapesL f.lowered tabs)[v.type]?.getD .other) := by
  rw [tys_makeL]
  unfold Func.value? at h
  simp only [Array.getElem?_map]
  cases hx : f.valueTab[x]? with
  | none => rw [hx] at h; cases h
  | some o =>
    rw [hx] at h; simp at h; subst h
    simp only [Option.map_some, valueTy, shapesL]

end GoFV.Proof
