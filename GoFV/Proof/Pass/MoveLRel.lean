import GoFV.Proof.Pass.MoveLOps
import GoFV.Proof.Speculate
import GoFV.Proof.RetypeL

/-!
# Related values (`Rel`) and their evaluation

`Rel ok f g x y`: some `relB ok f g n x y` holds (a value `x` of `g` stands for `y` of `f`).
Inversion (`relB_cases`, `okLocal_spec`), `Phi`s are only related to themselves
(`rel_phi_left`, `rel_phi_right`), and two related non-`Phi`s whose corresponding arguments hold
equal registers evaluate alike (`evalValueL_ident`, `evalValueL_clone`); a `Copy` evaluates to its
argument at its shape (`evalValueL_copy`).
-/

namespace GoFV.Proof.MoveL

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof

variable {ok : Array Bool} {f g : Func}

/-- `x` of `g` stands for `y` of `f`. -/
def Rel (ok : Array Bool) (f g : Func) (x y : ID) : Prop := ∃ n, relB ok f g n x y = true

theorem okLocal_of (hc : certValid ok f g = true) {x : ID} (h : okAt ok x = true) :
    okLocal ok f g x = true := by
  have hlt : x < ok.size := by
    unfold okAt at h
    rcases Nat.lt_or_ge x ok.size with hl | hl
    · exact hl
    · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none hl] at h; cases h
  have := List.all_eq_true.1 hc x (List.mem_range.2 hlt)
  simpa [h] using this

/-- What the certificate says at `x`. -/
theorem okLocal_spec {x : ID} (h : okLocal ok f g x = true) :
    ∃ gv fv, g.value? x = some gv ∧ f.value? x = some fv ∧ gv.op = fv.op ∧ gv.type = fv.type ∧
      gv.args.size = fv.args.size ∧
      (∀ (k : Nat) (hk : k < gv.args.size) (hk' : k < fv.args.size),
        Rel ok f g gv.args[k] fv.args[k]) ∧
      (gv.op = .Phi → gv.block = fv.block) ∧
      (gv.op ≠ .Phi → gv.aux = fv.aux ∧ gv.auxInt = fv.auxInt ∧ sxOf g gv = sxOf f fv) := by
  unfold okLocal at h
  cases hg : g.value? x with
  | none => rw [hg] at h; cases h
  | some gv =>
  cases hf : f.value? x with
  | none => rw [hg, hf] at h; cases h
  | some fv =>
  rw [hg, hf] at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hop, hty⟩, hsz⟩, hargs⟩, hrest⟩ := h
  refine ⟨gv, fv, rfl, rfl, hop, hty, hsz, fun k hk hk' => ?_, fun hp => ?_, fun hp => ?_⟩
  · have := List.all_eq_true.1 hargs k (List.mem_range.2 hk)
    refine ⟨relFuel, ?_⟩
    simpa [getElem!_pos, hk, hk'] using this
  · rw [ite_eq_left (by rw [hp])] at hrest
    simpa using hrest
  · rw [ite_eq_right (by simpa using hp)] at hrest
    simp only [Bool.and_eq_true, beq_iff_eq] at hrest
    exact ⟨hrest.1.1, hrest.1.2, hrest.2⟩

/-- **Inversion of `relB`**: identity in the certificate, a clone, or a `Copy`. -/
theorem relB_cases {n : Nat} {x y : ID} (h : relB ok f g n x y = true) :
    (x = y ∧ okAt ok x = true) ∨
    (∃ gv fv, g.value? x = some gv ∧ f.value? y = some fv ∧ cloneB ok f g gv fv = true) ∨
    (∃ gv fv z m, g.value? x = some gv ∧ f.value? y = some fv ∧ gv.op = .Copy ∧ fv.op ≠ .Phi ∧
      gv.type = fv.type ∧ gv.args.toList = [z] ∧ n = m + 1 ∧ relB ok f g m z y = true) := by
  rw [relB] at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact .inl h
  · cases hg : g.value? x with
    | none => rw [hg] at h; cases h
    | some gv =>
    cases hf : f.value? y with
    | none => rw [hg, hf] at h; cases h
    | some fv =>
    rw [hg, hf] at h
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
    rcases h with h | ⟨⟨⟨hc, hph⟩, hty⟩, hm⟩
    · exact .inr (.inl ⟨gv, fv, rfl, rfl, h⟩)
    · refine .inr (.inr ?_)
      split at hm
      · rename_i m z hl
        exact ⟨gv, fv, z, m, rfl, rfl, hc, hph, hty, hl, rfl, hm⟩
      · cases hm

theorem cloneB_spec {gv fv : Value} (h : cloneB ok f g gv fv = true) :
    totalOp gv.op = true ∧ gv.op = fv.op ∧ gv.type = fv.type ∧ gv.aux = fv.aux ∧
      gv.auxInt = fv.auxInt ∧ gv.args = fv.args ∧ (∀ a ∈ gv.args, okAt ok a = true) ∧
      sxOf g gv = sxOf f fv := by
  unfold cloneB at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

theorem totalOp_ne_phi {op : Op} (h : totalOp op = true) : op ≠ .Phi := by
  intro hp; rw [hp] at h; cases h

/-- An identity in the certificate is related. -/
theorem rel_ident {x : ID} (h : okAt ok x = true) : Rel ok f g x x :=
  ⟨0, by rw [relB]; simp [h]⟩

/-- A `Phi` of `g` is related only to itself. -/
theorem rel_phi_left {x y : ID} {gv : Value} (h : Rel ok f g x y) (hg : g.value? x = some gv)
    (hp : gv.op = .Phi) : x = y ∧ okAt ok x = true := by
  obtain ⟨n, h⟩ := h
  rcases relB_cases h with h | ⟨gv', fv, hg', -, hc⟩ | ⟨gv', fv, z, m, hg', -, hc, -⟩
  · exact h
  · rw [hg] at hg'; cases hg'
    exact absurd hp (totalOp_ne_phi (cloneB_spec hc).1)
  · rw [hg] at hg'; cases hg'; rw [hp] at hc; cases hc

/-- A `Phi` of `f` is related only to itself. -/
theorem rel_phi_right {x y : ID} {fv : Value} (h : Rel ok f g x y) (hf : f.value? y = some fv)
    (hp : fv.op = .Phi) : x = y ∧ okAt ok x = true := by
  obtain ⟨n, h⟩ := h
  rcases relB_cases h with h | ⟨gv, fv', -, hf', hc⟩ | ⟨gv, fv', z, m, -, hf', -, hne, -⟩
  · exact h
  · rw [hf] at hf'; cases hf'
    have := cloneB_spec hc
    exact absurd (this.2.1.trans hp) (totalOp_ne_phi this.1)
  · rw [hf] at hf'; cases hf'; exact absurd hp hne

/-! ## Evaluation -/

/-- Two values evaluate alike when their corresponding arguments hold equal registers, their
shapes agree and their ops evaluate alike on equal arguments. -/
theorem evalValueL_eq_of {md : LMode} {env : Env} {ctxT ctxS : Ctx} {frT frS : Frame}
    {gv fv : Value} (hsz : gv.args.size = fv.args.size)
    (hargs : ∀ (k : Nat) (a : ID), gv.args[k]? = some a →
      ∃ b z, fv.args[k]? = some b ∧ frT.regs[a]? = some (some z) ∧ frS.regs[b]? = some (some z))
    (hty : ctxT.tys[gv.id]? = ctxS.tys[fv.id]?)
    (hop : ∀ argv ty, evalOpL md.faulting env ctxT frT gv argv ty =
      evalOpL md.faulting env ctxS frS fv argv ty) :
    evalValueL md env ctxT frT gv = evalValueL md env ctxS frS fv := by
  unfold evalValueL
  rw [mapM_ofOption_eq (l := gv.args.toList) (l' := fv.args.toList)
    (m := fun a => s!"v{gv.id}: argument v{a} has no value")
    (m' := fun a => s!"v{fv.id}: argument v{a} has no value")
    (r := fun a => (frT.regs[a]?).join) (r' := fun a => (frS.regs[a]?).join) (by simp [hsz])
    (fun k a ha => by
      rw [Array.getElem?_toList] at ha
      obtain ⟨b, z, hb, h1, h2⟩ := hargs k a ha
      exact ⟨b, z, by rw [Array.getElem?_toList]; exact hb, by simp [h1], by simp [h2]⟩)]
  rw [hty]
  simp only [hop]

/-- **An identity**: the same op, aux, auxint, ID, shape and first-argument sign extension. -/
theorem evalValueL_ident {md : LMode} {env : Env} {tabs : Tables} {frT frS : Frame}
    {gv fv : Value} (hfr : frT = { frS with regs := frT.regs }) (hop : gv.op = fv.op)
    (haux : gv.aux = fv.aux) (hai : gv.auxInt = fv.auxInt) (hid : gv.id = fv.id)
    (hsz : gv.args.size = fv.args.size)
    (hargs : ∀ (k : Nat) (a : ID), gv.args[k]? = some a →
      ∃ b z, fv.args[k]? = some b ∧ frT.regs[a]? = some (some z) ∧ frS.regs[b]? = some (some z))
    (hty : (Ctx.makeL tabs g).tys[gv.id]? = (Ctx.makeL tabs f).tys[fv.id]?)
    (hsx : sxOf g gv = sxOf f fv) (hown : g.ownAux = f.ownAux) :
    evalValueL md env (Ctx.makeL tabs g) frT gv = evalValueL md env (Ctx.makeL tabs f) frS fv := by
  refine evalValueL_eq_of hsz hargs hty fun argv ty => ?_
  rw [hfr, evalOpL_frame]
  exact evalOpL_congr hop haux hai hid (by rw [tabs_makeL, tabs_makeL])
    (by rw [params_makeL, params_makeL]; simp only [Ctx.make, abiParams, hown]) (by rw [act_makeL, act_makeL]; rfl)
    (by rw [makeL_f, makeL_f]; exact hsx)

/-- **A clone** (a total op): the same op, aux, auxint, shape and first-argument sign extension,
any ID. -/
theorem evalValueL_clone {md : LMode} (hmd : md.faulting = false) {env : Env} {tabs : Tables}
    {frT frS : Frame} {gv fv : Value} (hfr : frT = { frS with regs := frT.regs })
    (ht : totalOp fv.op = true) (hop : gv.op = fv.op) (haux : gv.aux = fv.aux)
    (hai : gv.auxInt = fv.auxInt) (hsz : gv.args.size = fv.args.size)
    (hargs : ∀ (k : Nat) (a : ID), gv.args[k]? = some a →
      ∃ b z, fv.args[k]? = some b ∧ frT.regs[a]? = some (some z) ∧ frS.regs[b]? = some (some z))
    (hty : (Ctx.makeL tabs g).tys[gv.id]? = (Ctx.makeL tabs f).tys[fv.id]?)
    (hsx : sxOf g gv = sxOf f fv) (hown : g.ownAux = f.ownAux) :
    evalValueL md env (Ctx.makeL tabs g) frT gv = evalValueL md env (Ctx.makeL tabs f) frS fv := by
  refine evalValueL_eq_of hsz hargs hty fun argv ty => ?_
  rw [hmd, hfr, evalOpL_frame]
  rw [evalOpL_congr (ctx := Ctx.makeL tabs f) (ctx' := Ctx.makeL tabs g) (v := { fv with id := gv.id })
    hop haux hai rfl (by rw [tabs_makeL, tabs_makeL])
    (by rw [params_makeL, params_makeL]; simp only [Ctx.make, abiParams, hown])
    (by rw [act_makeL, act_makeL]; rfl) (by rw [makeL_f, makeL_f]; exact hsx)]
  obtain ⟨r, h1, h2⟩ := totalOp_ok (env := env) (ctx := Ctx.makeL tabs f) (fr := frS) (v := fv)
    (argv := argv) (ty := ty) ht
  rw [h2, h1]

/-- **A `Copy`** evaluates to its argument at its shape. -/
theorem evalValueL_copy {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {gv : Value} {z : ID}
    {w : Val} (hop : gv.op = .Copy) (hl : gv.args.toList = [z])
    (hz : fr.regs[z]? = some (some w)) :
    evalValueL md env ctx fr gv = .ok (md.retype (ctx.tys[gv.id]?.getD .other) w) := by
  unfold evalValueL
  rw [hl]
  simp only [List.mapM_cons, List.mapM_nil, hz, Option.join_some, Res.ofOption]
  show (evalOpL md.faulting env ctx fr gv [w] _).bind _ = _
  rw [evalOpL_copy hop]
  rfl

/-- An evaluated value has its shape. -/
theorem evalValueL_retype {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {y : Val}
    (h : evalValueL md env ctx fr v = .ok y) :
    md.retype (ctx.tys[v.id]?.getD .other) y = y := by
  unfold evalValueL at h
  cases hm : v.args.toList.mapM (fun a =>
      Res.ofOption s!"v{v.id}: argument v{a} has no value" (fr.regs[a]?).join) with
  | panic e m => rw [hm] at h; cases h
  | stuck msg => rw [hm] at h; cases h
  | ok argv =>
    rw [hm] at h
    change (evalOpL md.faulting env ctx fr v argv (ctx.tys[v.id]?.getD .other)).bind _ = _ at h
    cases ho : evalOpL md.faulting env ctx fr v argv (ctx.tys[v.id]?.getD .other) with
    | panic e m => rw [ho] at h; cases h
    | stuck msg => rw [ho] at h; cases h
    | ok r =>
      rw [ho] at h; cases h
      exact LMode.retype_idem md _ r

end GoFV.Proof.MoveL
