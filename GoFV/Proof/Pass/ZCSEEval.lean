import GoFV.Proof.Pass.ZCSESched

/-!
# zcse: argument-free values are constants of a run

`evalValue_argless`: two argument-free values with the same op, aux, auxint and shape evaluate
alike in any two frames of one activation (their IDs only name them in error messages).
`safe_ok`: a `safe` value evaluates. `ArglessInv`: in the source's frames, every register of an
argument-free value holds its evaluation (`arglessInv_enter`: entering a block keeps it).
-/

namespace GoFV.Proof.ZCSE

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.ZCSE Dom

theorem frameVal_eq {ctx ctx' : Ctx} {v v' : Value} (hop : v'.op = v.op) (haux : v'.aux = v.aux)
    (htabs : ctx'.tabs = ctx.tabs) (hact : ctx'.act = ctx.act) :
    frameVal ctx' v' = frameVal ctx v := by
  unfold frameVal; rw [hop, haux, htabs, hact]

/-- Argument-free ops with the same op, aux and auxint give the same result. -/
theorem evalOp_argless {env : Env} {ctx ctx' : Ctx} {fr fr' : Frame} {v v' : Value} {ty : Ty}
    {r : Val} (hop : v'.op = v.op) (haux : v'.aux = v.aux) (hai : v'.auxInt = v.auxInt)
    (htabs : ctx'.tabs = ctx.tabs) (hpar : ctx'.params = ctx.params) (hact : ctx'.act = ctx.act)
    (hfr : fr' = { fr with regs := fr'.regs }) (h : evalOp env ctx fr v [] ty = .ok r) :
    evalOp env ctx' fr' v' [] ty = .ok r := by
  have hfv := frameVal_eq (ctx := ctx) (ctx' := ctx') hop haux htabs hact
  unfold evalOp at h ⊢
  rw [hfv, hop, haux, hai, htabs, hfr]
  simp only [argVal_regs, argVal_params hpar]
  split at h <;> first | exact h | (cases h; done) | skip
  all_goals
    first
      | (obtain ⟨_, hs⟩ := callOp_nil_stuck (env := env) (ctx := ctx) (v := v)
         rw [hs] at h; cases h)
      | (unfold memRoot at h; simp at h; done)
      | (split at h <;> first | exact h | (cases h; done) | (simp only [pure] at h ⊢; split at h <;>
          first | exact h | (cases h; done) | (cases h; simp_all)))

/-- Argument-free values with the same op, aux, auxint and shape evaluate alike. -/
theorem evalValue_argless {env : Env} {ctx ctx' : Ctx} {fr fr' : Frame} {v v' : Value} {y : Val}
    (ha : v.args = #[]) (ha' : v'.args = #[]) (hop : v'.op = v.op) (haux : v'.aux = v.aux)
    (hai : v'.auxInt = v.auxInt) (hty : ctx'.tys[v'.id]? = ctx.tys[v.id]?)
    (htabs : ctx'.tabs = ctx.tabs) (hpar : ctx'.params = ctx.params) (hact : ctx'.act = ctx.act)
    (hfr : fr' = { fr with regs := fr'.regs }) (h : evalValue env ctx fr v = .ok y) :
    evalValue env ctx' fr' v' = .ok y := by
  unfold evalValue at h ⊢
  rw [ha] at h
  rw [ha', hty]
  simp only [List.mapM_nil, bind, Res.bind, pure] at h ⊢
  cases he : evalOp env ctx fr v [] (ctx.tys[v.id]?.getD .other) with
  | ok r =>
    rw [he] at h
    rw [evalOp_argless hop haux hai htabs hpar hact hfr he]
    exact h
  | panic e m => rw [he] at h; cases h
  | stuck msg => rw [he] at h; cases h

/-- An argument-free value evaluates the same in all frames of an activation. -/
theorem evalValue_argless_regs {env : Env} {ctx : Ctx} {fr fr' : Frame} {v : Value}
    (ha : v.args = #[]) (hfr : fr' = { fr with regs := fr'.regs }) :
    evalValue env ctx fr' v = evalValue env ctx fr v :=
  (evalValue_congr hfr fun a h => by rw [ha] at h; simp at h).symm

theorem params_make (tabs : Tables) (f : Func) : (Ctx.make tabs f).params = params tabs f := rfl

/-- A parameter name's piece evaluates. -/
theorem argVal_ok {ctx : Ctx} {fr : Frame} {n : AuxRef} {off : Int} {ty : Ty}
    (h : (ctx.params.findIdx? (· == some n)).isSome = true)
    (hlen : fr.images.size = ctx.params.size) : ∃ y, argVal ctx fr n off ty = .ok y := by
  unfold argVal
  obtain ⟨i, hi⟩ := Option.isSome_iff_exists.1 h
  have hlt : i < ctx.params.size := (Array.findIdx?_eq_some_iff_getElem.1 hi).1
  rw [hi]
  simp only
  rw [Array.getElem?_eq_getElem (hlen ▸ hlt)]
  simp only
  split <;> exact ⟨_, rfl⟩

/-- **A `safe` value evaluates** (in a frame with one argument image per parameter). -/
theorem safe_ok {env : Env} {tabs : Tables} {g : Func} {fr : Frame} {v : Value}
    (h : safe tabs (params tabs g) v = true)
    (hlen : fr.images.size = (Ctx.make tabs g).params.size) :
    ∃ y, evalValue env (Ctx.make tabs g) fr v = .ok y := by
  unfold safe at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hal, hop⟩ := h
  obtain ⟨ha, -⟩ := argless_iff.1 hal
  rw [← params_make] at hop
  obtain ⟨r, hr⟩ : ∃ r, evalOp env (Ctx.make tabs g) fr v []
      ((Ctx.make tabs g).tys[v.id]?.getD .other) = .ok r := by
    unfold evalOp
    split
    · exact ⟨_, rfl⟩
    · rename_i heq
      simp only [heq] at hop
      split at hop
      · rename_i n hn; rw [hn]; exact argVal_ok hop hlen
      · cases hop
    · rename_i heq
      simp only [heq] at hop
      split at hop
      · rename_i hn; rw [show (Ctx.make tabs g).tabs = tabs from rfl, hn]
        exact argVal_ok hop hlen
      · cases hop
    all_goals first
      | (rename_i heq; simp [heq] at hop; done)
      | (rename_i heq; rw [heq] at hop; exact absurd hop (by decide))
      | skip
    have hop' : isRoot v.op = false := by
      revert hop; split <;> simp_all
    split
    · exact ⟨_, rfl⟩
    · simp only [hop', Bool.false_eq_true, ite_false]; exact ⟨_, rfl⟩
  refine ⟨r.retype ((Ctx.make tabs g).tys[v.id]?.getD .other), ?_⟩
  unfold evalValue
  rw [ha]
  simp only [List.mapM_nil, bind, Res.bind, pure, hr]

/-- In the frames of a run, the register of every argument-free value holds its evaluation. -/
def ArglessInv (env : Env) (ctx : Ctx) (fr : Frame) : Prop :=
  ∀ x v y, ctx.f.value? x = some v → v.args = #[] → v.op ≠ .Phi → fr.regs[x]? = some (some y) →
    evalValue env ctx fr v = .ok y

theorem arglessInv_init (env : Env) (ctx : Ctx) (fr : Frame) (n : Nat)
    (h : fr.regs = Array.replicate n none) : ArglessInv env ctx fr := by
  intro x v y _ _ _ hy
  rw [h] at hy
  simp [Array.getElem?_replicate] at hy

theorem ArglessInv.frame {env : Env} {ctx : Ctx} {fr fr' : Frame} (h : ArglessInv env ctx fr)
    (hfr : fr' = { fr with regs := fr'.regs })
    (hr : ∀ x v, ctx.f.value? x = some v → v.args = #[] → v.op ≠ .Phi →
      fr'.regs[x]? = fr.regs[x]?) : ArglessInv env ctx fr' := by
  intro x v y hv ha hn hy
  rw [evalValue_argless_regs ha hfr]
  exact h x v y hv ha hn (by rw [← hr x v hv ha hn]; exact hy)

theorem arglessInv_evalAll {env : Env} {ctx : Ctx} :
    ∀ {o : List ID} {fr fr' : Frame}, ArglessInv env ctx fr → evalAll env ctx fr o = .ok fr' →
      ArglessInv env ctx fr' ∧ fr' = { fr with regs := fr'.regs }
  | [], fr, fr', h, he => by cases he; exact ⟨h, rfl⟩
  | x :: o, fr, fr', h, he => by
    rw [evalAll_cons] at he
    unfold stepV at he
    cases hv : ctx.f.value? x with
    | none => rw [hv] at he; cases he
    | some vx =>
      rw [hv] at he
      simp only at he
      cases hex : evalValue env ctx fr vx with
      | panic e m => rw [hex] at he; cases he
      | stuck msg => rw [hex] at he; cases he
      | ok yx =>
        rw [hex] at he
        simp only at he
        have h1 : ArglessInv env ctx (fr.set x yx) := by
          intro z v y hz ha hn hy
          rw [evalValue_argless_regs ha (fr := fr) rfl]
          by_cases hzx : x = z
          · subst hzx
            rw [hv] at hz; cases hz
            by_cases hlt : x < fr.regs.size
            · rw [Frame.set_regs_self hlt] at hy; cases hy; exact hex
            · simp [Frame.set, hlt] at hy
          · exact h z v y hz ha hn (by rw [← Frame.set_regs_ne hzx]; exact hy)
        obtain ⟨h2, h3⟩ := arglessInv_evalAll (o := o) h1 he
        exact ⟨h2, by rw [h3]; rfl⟩

/-- **Entering a block keeps `ArglessInv`.** -/
theorem arglessInv_enter {env : Env} {ctx : Ctx} {fr fr' : Frame} {b : Block} {i : Nat}
    (h : ArglessInv env ctx fr) (hnd : b.values.toList.Nodup)
    (he : enterBlock env ctx fr b i = .ok fr') : ArglessInv env ctx fr' := by
  obtain ⟨frP, o, -, hev, hfrP, -, -, hkeep, -⟩ := enterBlock_spec hnd he
  have hP : ArglessInv env ctx frP :=
    h.frame hfrP fun x v hv _ hn => hkeep x (.inr ⟨v, hv, hn⟩)
  exact (arglessInv_evalAll hP hev).1

end GoFV.Proof.ZCSE
