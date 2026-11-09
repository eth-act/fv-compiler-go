import GoFV.Proof.Pass.PhiOptSched

variable [GoFV.SSA.Sem.Addrs]

/-!
# phiopt: one block entry, the pieces

`At`: the source-side invariant at a block entry (frame size, `ArglessInv`, lemma (D) for the
strict ancestors, the edge facts, the block reached from the entry or along an edge of a tree
block). `TR`: the target's frame has the source's inputs and registers on the values listed
in `f`. `targetPhis`: the target's `Phi`s (the source's, less the rewritten ones) read the
same arguments. `armFacts`: on entry, what the forms need of the source frame. `newFrame`:
the source's frame after the block, extended to the target's size and with the block's new
values evaluated (`H`, the reference frame of the target's evaluation).
-/

namespace GoFV.Proof.PhiOpt

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.PhiOpt Dom
open GoFV.Proof.CopyElim (Tree)
open GoFV.Proof.ZCSE (ArglessInv)

variable {tabs : Tables} {f g : Func}

/-- The source-side invariant at the entry of block `bid` along edge `i`. -/
structure At (env : Env) (tabs : Tables) (f : Func) (fr : Frame) (bid : ID) (i : Nat) :
    Prop where
  size : fr.regs.size = f.valueTab.size
  inv : ArglessInv env (Ctx.make tabs f) fr
  dinv : DInv env (Ctx.make tabs f) (fun a => Anc (make f) a bid ∧ a ≠ bid) fr
  path : PathOK f fr bid i
  pre : (bid = f.entry ∧ i = 0) ∨ ∃ p blkp, p ∈ f.blocks ∧ f.block? p = some blkp ∧
    ((make f).depthOf p).isSome ∧ (⟨bid, i⟩ : Edge) ∈ blkp.succs
  dom : DomOK f fr bid

/-- The target's frame: the source's inputs, and its registers on the values listed in `f`. -/
def TR (f g : Func) (frS frT : Frame) : Prop :=
  frT = { frS with regs := frT.regs } ∧ frT.regs.size = g.valueTab.size ∧
    ∀ x, Listed f x → frT.regs[x]? = frS.regs[x]?

theorem At.tree (S : Setup tabs f g) {env : Env} {fr : Frame} {bid : ID} {i : Nat}
    (h : At env tabs f fr bid i) : Tree f bid := by
  obtain ⟨ce, hwf⟩ := S.wf
  rcases h.pre with ⟨rfl, -⟩ | ⟨p, blkp, hp, hpb, hpt, he⟩
  · exact ⟨hwf.entry, by simp [entry_depth S.cf.parents]⟩
  · obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 he
    exact ⟨(hwf.succLink p blkp ⟨hp, hpb⟩ j _ hj).1, (edge S.cf hp hpb hpt he).2.1⟩

/-- The entry edge is an edge of the block (or the start of the run). -/
theorem At.edge (S : Setup tabs f g) {env : Env} {fr : Frame} {bid : ID} {i : Nat}
    (h : At env tabs f fr bid i) {fb : Block} (hfb : f.block? bid = some fb) :
    bid = f.entry ∨ i < fb.preds.size := by
  obtain ⟨ce, hwf⟩ := S.wf
  rcases h.pre with ⟨rfl, -⟩ | ⟨p, blkp, hp, hpb, -, he⟩
  · exact .inl rfl
  · right
    obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 he
    obtain ⟨-, c, hc, hci⟩ := hwf.succLink p blkp ⟨hp, hpb⟩ j _ hj
    rw [hfb] at hc; cases hc
    exact (Array.getElem?_eq_some_iff.1 hci).1

/-- An available value has a register on entry. -/
theorem At.avail (S : Setup tabs f g) {env : Env} {fr : Frame} {bid : ID} {i : Nat}
    (h : At env tabs f fr bid i) {x : ID} (hx : avail f bid x = true) :
    ∃ y, fr.regs[x]? = some (some y) := by
  obtain ⟨v, blk, hv, hvb, hblk, hxb, hanc, hne, -⟩ := avail_spec hx
  obtain ⟨y, hy, -⟩ := h.dinv x v ⟨hv, hvb, blk, hblk, hxb⟩
    ⟨(anc_iff S.cf.parents).1 hanc, hne⟩
  exact ⟨y, hy⟩

/-- A listed value of `f` is not new. -/
theorem listed_some {ce : CheckEnv} (hwf : WF ce f) {x : ID} (h : Listed f x) :
    ∃ v, f.value? x = some v := by
  obtain ⟨bid, b, hb, hx⟩ := h
  obtain ⟨v, hv, -⟩ := hwf.valueId bid b hb x hx
  exact ⟨v, hv⟩

/-! ## Evaluating new values -/

theorem mapM_ofOption_ok {m : ID → String} {r : ID → Option Val} :
    ∀ {l : List ID}, (∀ a ∈ l, ∃ z, r a = some z) →
      ∃ L, l.mapM (fun a => Res.ofOption (m a) (r a)) = .ok L
  | [], _ => ⟨[], rfl⟩
  | a :: l, h => by
    obtain ⟨z, hz⟩ := h a List.mem_cons_self
    obtain ⟨L, hL⟩ := mapM_ofOption_ok (m := m) (l := l) fun b hb => h b (List.mem_cons_of_mem _ hb)
    refine ⟨z :: L, ?_⟩
    rw [List.mapM_cons, hz]
    change Res.bind (List.mapM (fun a => Res.ofOption (m a) (r a)) l) _ = _
    rw [hL]; rfl

/-- A form op evaluates when its arguments have registers. -/
theorem evalValue_form_ok {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} (h : formOp v.op)
    (ha : ∀ a ∈ v.args, ∃ z, fr.regs[a]? = some (some z)) : ∃ r, evalValue env ctx fr v = .ok r := by
  obtain ⟨L, hL⟩ := mapM_ofOption_ok (l := v.args.toList)
    (m := fun a => s!"v{v.id}: argument v{a} has no value") (r := fun a => (fr.regs[a]?).join)
    fun a hm => by
      obtain ⟨z, hz⟩ := ha a (Array.mem_toList_iff.1 hm)
      exact ⟨z, by simp [hz]⟩
  unfold evalValue
  rw [hL]
  exact ⟨(evalPure v.op (ctx.tys[v.id]?.getD .other) v.auxInt v.aux L).retype
    (ctx.tys[v.id]?.getD .other), by simp only [bind, Res.bind, pure, evalOp_form h]⟩

/-- `evalAll` of form-op values in a dependency order, whose arguments have registers or are
listed before, succeeds. -/
theorem evalAll_form_ok {env : Env} {ctx : Ctx} :
    ∀ {o : List ID} {fr : Frame}, TopoRem (argsF ctx.f) o →
      (∀ x ∈ o, ∃ v, ctx.f.value? x = some v ∧ formOp v.op ∧
        ∀ a ∈ v.args, a ∈ o ∨ ∃ z, fr.regs[a]? = some (some z)) →
      fr.regs.size = ctx.f.valueTab.size →
      ∃ fr', evalAll env ctx fr o = .ok fr'
  | [], fr, _, _, _ => ⟨fr, rfl⟩
  | x :: o, fr, ⟨h1, h2⟩, h, hs => by
    obtain ⟨v, hv, hop, hargs⟩ := h x List.mem_cons_self
    obtain ⟨r, hr⟩ := evalValue_form_ok (env := env) (ctx := ctx) (fr := fr) hop fun a ha => by
      rcases hargs a ha with hm | hz
      · exact absurd hm (h1 a (by rw [argsF_of hv]; exact Array.mem_toList_iff.2 ha))
      · exact hz
    have hxlt : x < fr.regs.size := hs ▸ lt_of_value? hv
    obtain ⟨fr', h'⟩ := evalAll_form_ok (o := o) (fr := fr.set x r) h2 (fun y hy => by
      obtain ⟨w, hw, hwop, hwargs⟩ := h y (List.mem_cons_of_mem _ hy)
      refine ⟨w, hw, hwop, fun a ha => ?_⟩
      rcases hwargs a ha with hm | ⟨z, hz⟩
      · rcases List.mem_cons.1 hm with rfl | hm
        · exact .inr ⟨r, Frame.set_regs_self hxlt⟩
        · exact .inl hm
      · by_cases hxa : x = a
        · subst hxa; exact .inr ⟨r, Frame.set_regs_self hxlt⟩
        · exact .inr ⟨z, by rw [Frame.set_regs_ne hxa]; exact hz⟩)
      (by simp [Frame.set, hs])
    refine ⟨fr', ?_⟩
    rw [evalAll_cons]
    unfold stepV
    rw [hv]
    simp only [hr]
    exact h'

end GoFV.Proof.PhiOpt
