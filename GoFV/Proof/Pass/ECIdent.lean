import GoFV.Proof.Pass.ECShape
import GoFV.Proof.RunMono
import GoFV.Proof.AtomSimOK
import GoFV.Proof.Frame

/-!
# `expand calls`: unchanged, invalidated and new values (issue #28)

The local obligations (`Obl`) of the source values `expand calls` keeps (`identOK`: the same op,
type, aux, auxint and arguments, or a `Dereference` that became a `Load`) and of those it
invalidated (`OpInvalid` in the target, conversion `poison`; only pure values, which never
panic), and `NewEval` of the values it adds (`newEvalB`: pure ops, frame values and pieces of the
function's parameters).
-/

namespace GoFV.Proof.EC

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.ECCheck GoFV.Proof.AtomSim

/-! ## `evalOp` reads only some fields of the value -/

theorem evalOp_upd (env : Env) (ctx : Ctx) (fr : Frame) (u : Value) (p : Pos) (n : Nat) (b : ID)
    (t : TypeRef) (argv : List Val) (ty : Ty) :
    evalOp env ctx fr { u with pos := p, uses := n, block := b, type := t } argv ty =
      evalOp env ctx fr u argv ty := by
  cases u; rfl

theorem evalOp_load_deref (env : Env) (ctx : Ctx) (fr : Frame) {u : Value} (hop : u.op = .Dereference)
    (argv : List Val) (ty : Ty) :
    evalOp env ctx fr { u with op := .Load } argv ty = evalOp env ctx fr u argv ty := by
  obtain ⟨id, op, type, auxInt, aux, pos, uses, args, block⟩ := u
  simp only at hop
  subst hop
  rfl

/-- A target value related to a source value by `identOK` (same ID) evaluates its op like the
source value. -/
theorem evalOp_of_identOK {f g : Func} {u w : Value} (h : identOK f g u w = true) (hid : w.id = u.id)
    (env : Env) (ctx : Ctx) (fr : Frame) (argv : List Val) (ty : Ty) :
    evalOp env ctx fr w argv ty = evalOp env ctx fr u argv ty := by
  unfold identOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hop, hty⟩, hai⟩, hax⟩, hargs⟩, -⟩ := h
  have hw : w = { u with op := w.op, pos := w.pos, uses := w.uses, block := w.block } := by
    cases u; cases w; simp_all
  rcases hop with hop | ⟨hd, hl⟩
  · rw [hw, hop]
    exact evalOp_upd env ctx fr u w.pos w.uses w.block u.type argv ty
  · rw [hw, hl]
    have := evalOp_upd env ctx fr { u with op := .Load } w.pos w.uses w.block u.type argv ty
    simp only at this
    rw [this]
    exact evalOp_load_deref env ctx fr hd argv ty

/-! ## Results related by the identity -/

theorem resCv_of_refines {c : Val → Val} (hc : ∀ y, c y = y) {r r' : Res Val}
    (h : Res.Refines r r') : ResCv c r r' := by
  cases h with
  | ok h => exact .ok (by rw [hc]; exact h)
  | panic e hm => exact .panic e hm
  | stuck msg _ => exact .stuck msg _

/-- The arguments' registers, refined. -/
theorem mapM_regs_refines {frS T : Frame} :
    ∀ (as : List ID), (∀ a ∈ as, ∀ y, frS.regs[a]? = some (some y) →
      ∃ y', T.regs[a]? = some (some y') ∧ Sem.Refines y y') →
    ∀ (msg : ID → String),
    Res.Rel RefinesList (as.mapM fun a => Res.ofOption (msg a) (frS.regs[a]?).join)
      (as.mapM fun a => Res.ofOption (msg a) (T.regs[a]?).join)
  | [], _, _ => .ok .nil
  | a :: as, h, msg => by
    simp only [List.mapM_cons]
    have ih := mapM_regs_refines as (fun b hb => h b (List.mem_cons_of_mem _ hb)) msg
    have h1 : Res.Rel Sem.Refines (Res.ofOption (msg a) (frS.regs[a]?).join)
        (Res.ofOption (msg a) (T.regs[a]?).join) := by
      cases hy : (frS.regs[a]?).join with
      | none => exact .stuck _ _
      | some y =>
        have hs : frS.regs[a]? = some (some y) := by
          cases h1 : frS.regs[a]? with
          | none => rw [h1] at hy; cases hy
          | some o => rw [h1] at hy; cases o <;> simp_all
        obtain ⟨y', hy', hyy⟩ := h a List.mem_cons_self y hs
        rw [hy']
        exact .ok hyy
    refine Res.Rel.bind h1 fun y y' hyy => Res.Rel.bind ih fun l l' hl => ?_
    exact .ok (.cons hyy hl)

/-- **The obligation of an unchanged value.** -/
theorem obl_ident {tabs : Tables} {f g : Func} {x : ID} {u w : Value} {HS HT : ID → Prop} (hu : f.value? x = some u)
    (hw : g.value? x = some w) (hux : u.id = x) (hwx : w.id = x)
    (hok : identOK f g u w = true) (hsp : special f g x = false) (hown : g.ownAux = f.ownAux) :
    Obl tabs f g (ecCv tabs f g) (isNewB f) (ecFront f g x) HS HT x := by
  intro u' w' hu' hw' env hE frS T hT _ E _ _ hregT _ hfront _ _
  rw [hu] at hu'; cases hu'
  rw [hw] at hw'; cases hw'
  have hcv : ∀ y, ecCv tabs f g x y = y := ecCv_of_not_special hsp
  refine resCv_of_refines hcv ?_
  have hok' := hok
  unfold identOK at hok'
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.not_eq_true'] at hok'
  obtain ⟨⟨⟨⟨⟨-, hty⟩, -⟩, -⟩, hargs⟩, hsa⟩ := hok'
  have hfr : ∀ a ∈ u.args.toList, ∀ y, frS.regs[a]? = some (some y) →
      ∃ y', T.regs[a]? = some (some y') ∧ Sem.Refines y y' := by
    intro a ha y hy
    have hfa : a ∈ ecFront f g x := by
      have hi : invalidated g x = false := by
        unfold special at hsp; simp only [Bool.or_eq_false_iff] at hsp; exact hsp.2
      unfold ecFront; rw [hi, if_neg Bool.false_ne_true, hu]; exact List.mem_append_left _ ha
    obtain ⟨y', hy', hyy⟩ := hfront a hfa y hy
    have hsa' := Array.all_eq_true'.1 hsa a (Array.mem_toList_iff.1 ha)
    simp only [Bool.not_eq_true'] at hsa'
    rw [ecCv_of_not_special hsa'] at hyy
    exact ⟨y', hy', hyy⟩
  unfold evalValue
  rw [hargs]
  have hrel := mapM_regs_refines u.args.toList hfr (fun (a : ID) => s!"v{u.id}: argument v{a} has no value")
  have hmsg : (fun (a : ID) => Res.ofOption s!"v{w.id}: argument v{a} has no value" (T.regs[a]?).join) =
      (fun (a : ID) => Res.ofOption s!"v{u.id}: argument v{a} has no value" (T.regs[a]?).join) := by
    rw [hux, hwx]
  rw [hmsg]
  have htys : (Ctx.make tabs g).tys[w.id]?.getD .other = (Ctx.make tabs f).tys[u.id]?.getD .other := by
    rw [hux, hwx, tys_of_value hu, tys_of_value hw, hty]
  rw [htys]
  revert hrel
  generalize u.args.toList.mapM (fun a => Res.ofOption s!"v{u.id}: argument v{a} has no value" (frS.regs[a]?).join) = rS
  generalize u.args.toList.mapM (fun a => Res.ofOption s!"v{u.id}: argument v{a} has no value" (T.regs[a]?).join) = rT
  intro hrel
  cases hrel with
  | stuck msg r => exact .stuck _ _
  | panic e hm => exact .panic e hm
  | @ok argv argv' hl =>
    show Res.Refines (Res.bind (Res.ok argv) _) (Res.bind (Res.ok argv') _)
    simp only [Res.bind_ok]
    rw [evalOp_of_identOK hok (hwx.trans hux.symm)]
    have hctx := AtomSim.ctx_eq (tabs := tabs) hown.symm
    have hm := evalOp_mono env hE (Ctx.make tabs f) (Ctx.make tabs g) hctx frS T
      (by rw [hT]) (by rw [hT]) (by rw [hT]) (by rw [hT]) u
      ((Ctx.make tabs f).tys[u.id]?.getD .other) hl
    revert hm
    generalize evalOp env (Ctx.make tabs f) frS u argv _ = r
    generalize evalOp env (Ctx.make tabs g) T u argv' _ = r'
    intro hm
    cases hm with
    | ok h => exact .ok (retype_mono _ h)
    | panic e hm => exact .panic e hm
    | stuck msg r => exact .stuck _ _

end GoFV.Proof.EC
