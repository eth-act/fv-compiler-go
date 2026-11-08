import GoFV.Proof.Pass.NilEval
import GoFV.Proof.NilPre
import GoFV.Proof.Eval

variable [GoFV.SSA.Sem.Addrs]

/-!
# nilcheckelim's checker: the rewrite passes' seeds (issue #151)

`NilCheck.safePtr true` also takes as non-nil the first result of a malloc-family call
(`NilCheck.mallocCall`, `generic.rules:1367`/`:1372`) and a dictionary parameter
(`NilCheck.dictArg`, `:1384`). Under `Env.AllocNonNil` the call's register holds a tuple whose
first component is a non-nil pointer or `poison` (`safe_selectN_malloc`); under `DictFrame` (the
frame's argument images of the dictionary parameters encode non-nil pointers; `DictArgs` at the
entry, `dictFrame_entry`) the `Arg` reads a non-nil pointer or `poison` (`safe_argVal_dict`).
-/

namespace GoFV.Proof.Nil

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof.CSE

/-- The images of `f`'s dictionary parameters in frame `fr` encode non-nil pointers. -/
def DictFrame (tabs : Tables) (f : Func) (fr : Frame) : Prop :=
  ∀ i ∈ NilCheck.dictParams tabs f, ∀ t, (Ctx.make tabs f).paramTys[i]? = some t →
    ∃ p : Ptr, p.blk ≠ .nil ∧ fr.images[i]? = some (encode t (.ptr p))

theorem DictFrame.images {tabs : Tables} {f : Func} {fr fr' : Frame} (h : DictFrame tabs f fr)
    (hi : fr'.images = fr.images) : DictFrame tabs f fr' := by
  intro i hi' t ht; rw [hi]; exact h i hi' t ht

/-- **At the entry**, `DictArgs` gives `DictFrame`. -/
theorem dictFrame_entry {env : Env} {tabs : Tables} {f : Func} {args : List Val} {mem : Mem}
    (h : DictArgs (NilCheck.dictParams tabs f) args) :
    DictFrame tabs f (entryFrame env (Ctx.make tabs f) args mem) := by
  intro i hi t ht
  obtain ⟨p, hp, hnn⟩ := h i hi
  refine ⟨p, hnn, ?_⟩
  have hz : (args.toArray.zip (Ctx.make tabs f).paramTys)[i]? = some (.ptr p, t) :=
    Array.getElem?_zip_eq_some.2 ⟨by simpa using hp, ht⟩
  simp only [entryFrame, Array.getElem?_map, hz, Option.map_some]

theorem inParams_name {tabs : Tables} {f : Func} {n : AuxRef} {i : Nat}
    (h : ((NilCheck.inParams tabs f).map (·.name)).findIdx? (· == some n) = some i) :
    ∃ p, (NilCheck.inParams tabs f)[i]? = some p ∧ p.name = some n := by
  obtain ⟨hlt, heq, -⟩ := Array.findIdx?_eq_some_iff_getElem.1 h
  simp only [Array.size_map] at hlt
  refine ⟨_, Array.getElem?_eq_getElem hlt, ?_⟩
  simpa using heq

/-- What `dictArg` says: `n` is input parameter `i`, a dictionary parameter of pointer shape. -/
theorem dictArg_spec {tabs : Tables} {f : Func} {n : AuxRef} (h : NilCheck.dictArg tabs f n = true) :
    ∃ i e, (Ctx.make tabs f).params.findIdx? (· == some n) = some i ∧
      i ∈ NilCheck.dictParams tabs f ∧ (Ctx.make tabs f).paramTys[i]? = some (.ptr e) := by
  unfold NilCheck.dictArg at h
  dsimp only at h
  cases hi : ((NilCheck.inParams tabs f).map (·.name)).findIdx? (· == some n) with
  | none => rw [hi] at h; cases h
  | some i =>
    rw [hi] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hd, hp⟩ := h
    obtain ⟨p, hpi, hpn⟩ := inParams_name hi
    rw [hpi] at hp
    simp only at hp
    obtain ⟨e, he⟩ : ∃ e, tabs.ty p.type = .ptr e := by
      unfold NilCheck.ptrShaped at hp
      split at hp
      · exact ⟨_, by assumption⟩
      · cases hp
    have hlt : i < (NilCheck.inParams tabs f).size := (Array.getElem?_eq_some_iff.1 hpi).1
    refine ⟨i, e, hi, ?_, ?_⟩
    · simp only [NilCheck.dictParams, List.mem_filter, List.mem_range, hpi, Option.bind_some,
        hpn, Option.map_some, Option.getD_some]
      exact ⟨hlt, hd⟩
    · show ((NilCheck.inParams tabs f).map (tabs.ty ·.type))[i]? = _
      simp [hpi, he]

/-- **A dictionary `Arg` is `Safe`** under `DictFrame`. -/
theorem safe_argVal_dict {tabs : Tables} {f : Func} {fr : Frame} {n : AuxRef} {e : Option Nat}
    {y : Val} (hD : DictFrame tabs f fr) (hda : NilCheck.dictArg tabs f n = true)
    (h : argVal (Ctx.make tabs f) fr n 0 (.ptr e) = .ok y) : Safe y := by
  obtain ⟨i, e', hi, hdi, hti⟩ := dictArg_spec hda
  obtain ⟨p, hnn, himg⟩ := hD i hdi _ hti
  unfold argVal at h
  rw [hi] at h
  simp only at h
  rw [himg] at h
  simp only at h
  split at h
  · cases h; trivial
  · cases h
    have hsz : (ptrBytes p).size = 8 := by simp [ptrBytes]
    have hb : bytesPtr? (ptrBytes p) = some p := by
      simp [bytesPtr?, ptrBytes, List.range, List.range.loop]
    show Safe (decodePtr ((ptrBytes p).extract 0 8))
    rw [Array.extract_eq_self_of_le (by omega), decodePtr, hb]
    exact safe_word hnn

/-- A static call that returns: its callee's contract returned `rs`, and the call's value is the
tuple of `rs` at the ABI's result shapes, then the memory and the result addresses. -/
theorem callOp_static_ok {env : Env} {ctx : Ctx} {v : Value} {argv : List Val} {r : Val}
    (hop : v.op = .StaticLECall) (h : callOp env ctx v argv = .ok r) :
    ∃ name c args m rs m' tail, v.aux.bind ctx.tabs.callee? = some name ∧
      (env.atAct ctx.act).extern name = some c ∧ c args none m = .returned rs m' ∧
      r = .tuple (retypeResults ctx.tabs
        ((((callABI? ctx.tabs v.aux).map (·.params.toList)).getD []).filter (·.out)) rs ++ tail) := by
  unfold callOp at h
  simp only [callTarget, hop, nilClosure_none] at h
  have hb : (Op.StaticLECall == Op.StaticCall || Op.StaticLECall == Op.ClosureCall ||
      Op.StaticLECall == Op.InterCall) = false := by decide
  simp only [Res.ofOption, bind, Res.bind, pure, hb, Bool.false_eq_true, ite_false,
    Option.map_none, Option.getD_none, Bool.or_false] at h
  split at h
  · next m hm =>
    split at h
    · cases h
    split at h
    · cases h
    cases hname : v.aux.bind ctx.tabs.callee? with
    | none => rw [hname] at h; cases h
    | some name =>
    rw [hname] at h
    simp only at h
    cases hc : (env.atAct ctx.act).extern name with
    | none => rw [hc] at h; cases h
    | some c =>
      rw [hc] at h
      simp only at h
      split at h
      · next rs m' hret =>
        split at h
        · cases h
          exact ⟨name, c, _, _, rs, m', _, rfl, hc, hret, rfl⟩
        all_goals cases h
      · cases h
      · cases h
  · cases h

/-- The first result of a call whose contract returned a non-nil pointer first, at a pointer
shape (or no ABI result shape), is `Safe`. -/
theorem retypeResults_head {tabs : Tables} {outs : List ABIParam} {rs : List Val} {p : Ptr}
    (hrs : rs.head? = some (.ptr p)) (hnn : p.blk ≠ .nil)
    (hout : (match outs with | [] => true | o :: _ => NilCheck.ptrShaped tabs o.type) = true) :
    ∃ v rest, retypeResults tabs outs rs = v :: rest ∧ Safe v := by
  match rs, hrs, outs, hout with
  | .ptr p :: rs, rfl, [], _ => exact ⟨_, rs, rfl, hnn⟩
  | .ptr p :: rs, rfl, o :: os, hout =>
    simp only at hout
    unfold NilCheck.ptrShaped at hout
    refine ⟨_, retypeResults tabs os rs, rfl, ?_⟩
    split at hout
    · next e he => rw [he]; exact safe_word hnn
    · cases hout

/-- **The `SelectN [0]` of a malloc-family call is `Safe`** under `Env.AllocNonNil`. -/
theorem safe_selectN_malloc {env : Env} {tabs : Tables} {f : Func} {fr : Frame} {c : ID}
    {cv : Value} {yc : Val} (hA : env.AllocNonNil) (hmc : NilCheck.mallocCall tabs f c = true)
    (hcv : f.value? c = some cv) (hid : cv.id = c)
    (hev : evalValue env (Ctx.make tabs f) fr cv = .ok yc) : Safe (Tuple.selectN 0 [yc]) := by
  unfold NilCheck.mallocCall at hmc
  rw [hcv] at hmc
  simp only [Bool.and_eq_true, beq_iff_eq] at hmc
  obtain ⟨⟨⟨hop, hname⟩, hty⟩, hout⟩ := hmc
  obtain ⟨e0, ts, hts⟩ : ∃ e0 ts, tabs.ty cv.type = .tuple (.ptr e0 :: ts) := by
    split at hty
    · exact ⟨_, _, by assumption⟩
    · cases hty
  obtain ⟨vs, hvs⟩ := argVals_of_eval (env := env) (ctx := Ctx.make tabs f) (fr := fr) (v := cv)
    (by rw [hev]; nofun)
  rw [evalValue_of_argVals hvs] at hev
  have htys : (Ctx.make tabs f).tys[cv.id]?.getD .other = .tuple (.ptr e0 :: ts) := by
    rw [hid, tys_of_value hcv]; simpa using hts
  rw [htys] at hev
  obtain ⟨r, hr, rfl⟩ := bind_ok hev
  have hco : evalOp env (Ctx.make tabs f) fr cv vs (.tuple (.ptr e0 :: ts)) =
      callOp env (Ctx.make tabs f) cv vs := by simp only [evalOp, hop]
  rw [hco] at hr
  obtain ⟨name, c', args, m, rs, m', tail, hn, hc, hret, rfl⟩ := callOp_static_ok hop hr
  have hn' : cv.aux.bind tabs.callee? = some name := hn
  rw [hn'] at hname
  obtain ⟨p, hp, hnn⟩ := hA.atAct _ name c' (by simpa using hname) hc args none m rs m' hret
  obtain ⟨v, rest, hrest, hv⟩ := retypeResults_head (tabs := tabs) hp hnn hout
  have : (Ctx.make tabs f).tabs = tabs := rfl
  rw [this, hrest]
  simp only [List.cons_append, Val.retype]
  split
  · simp only [Val.retypePre, Option.map_eq_some_iff] at *
    rename_i vs' hvs'
    obtain ⟨l, -, rfl⟩ := hvs'
    simp only [Tuple.selectN]
    exact safe_retype_ptr _ hv
  · trivial

end GoFV.Proof.Nil
