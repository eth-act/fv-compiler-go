import GoFV.Proof.Agree

/-!
# Entering a block along renumbered edges

`enterBlock_rel` generalises `enterBlock_agree` to a target that enters the block along another
predecessor index, with `Phi`s whose arguments were renumbered (edge removal by swap-removal):
the `Phi` step results are given as a hypothesis (`filterMapM_phi_rel`: per `Phi`, the target's
argument at its index is the source's at its index, with the same register). The block's other
values are unchanged (`schedNodes_phiEq`: the schedule ignores `Phi` arguments).
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem

/-- A `Phi` step whose argument the target reads at another index. -/
theorem phiStep_rel {ctxS ctxT : Ctx} {frS frT : Frame} {iS iT : Nat} {z : ID}
    {r : Option (ID × Val)}
    (hv : ∀ v, ctxS.f.value? z = some v → ∃ w, ctxT.f.value? z = some w ∧ w.op = v.op ∧
      (v.op = .Phi → w.args[iT]? = v.args[iS]? ∧
        ∀ a, v.args[iS]? = some a → frT.regs[a]? = frS.regs[a]?))
    (hty : ctxT.tys[z]? = ctxS.tys[z]?)
    (h : phiStep ctxS frS iS z = .ok r) : phiStep ctxT frT iT z = .ok r := by
  unfold phiStep at h ⊢
  cases hvs : ctxS.f.value? z with
  | none => rw [hvs] at h; cases h
  | some v =>
    rw [hvs] at h
    obtain ⟨w, hw, hop, hph⟩ := hv v hvs
    rw [hw]
    simp only at h ⊢
    rw [hop, hty]
    by_cases hp : v.op = .Phi
    · simp only [hp, beq_self_eq_true, ite_true] at h ⊢
      obtain ⟨ha, hreg⟩ := hph hp
      rw [ha]
      cases hai : v.args[iS]? with
      | none => rw [hai] at h; cases h
      | some a =>
        rw [hai] at h
        simp only at h ⊢
        rw [hreg a hai]
        exact h
    · simp only [show (v.op == .Phi) = false by simpa using hp, Bool.false_eq_true,
        ite_false] at h ⊢
      exact h

/-- The `Phi` steps of a list of values, the target reading at another index. -/
theorem filterMapM_phi_rel {ctxS ctxT : Ctx} {frS frT : Frame} {iS iT : Nat} :
    ∀ {l : List ID} {ps : List (ID × Val)},
      (∀ z ∈ l, ∀ v, ctxS.f.value? z = some v → ∃ w, ctxT.f.value? z = some w ∧ w.op = v.op ∧
        (v.op = .Phi → w.args[iT]? = v.args[iS]? ∧
          ∀ a, v.args[iS]? = some a → frT.regs[a]? = frS.regs[a]?)) →
      (∀ z ∈ l, ctxT.tys[z]? = ctxS.tys[z]?) →
      l.filterMapM (phiStep ctxS frS iS) = .ok ps → l.filterMapM (phiStep ctxT frT iT) = .ok ps
  | [], ps, _, _, h => h
  | z :: l, ps, hv, hty, h => by
    rw [List.filterMapM_cons] at h ⊢
    cases hz : phiStep ctxS frS iS z with
    | panic e m => rw [hz] at h; cases h
    | stuck msg => rw [hz] at h; cases h
    | ok r =>
      rw [hz] at h
      rw [phiStep_rel (hv z List.mem_cons_self) (hty z List.mem_cons_self) hz]
      simp only [bind, Res.bind] at h ⊢
      cases hl : l.filterMapM (phiStep ctxS frS iS) with
      | panic e m => rw [hl] at h; cases r <;> cases h
      | stuck msg => rw [hl] at h; cases r <;> cases h
      | ok ps' =>
        rw [hl] at h
        rw [filterMapM_phi_rel (fun y hy => hv y (List.mem_cons_of_mem _ hy))
          (fun y hy => hty y (List.mem_cons_of_mem _ hy)) hl]
        exact h

/-- **Entering a block along renumbered edges**: as `enterBlock_agree`, with the target's `Phi`
step results given. -/
theorem enterBlock_rel {env : Env} {ctxS ctxT : Ctx} {frS frT : Frame} {bS bT : Block}
    {iS iT : Nat} {X : ID → Prop} (hid : bT.id = bS.id) (hv : bT.values = bS.values)
    (hps : ∀ ps, bS.values.toList.filterMapM (phiStep ctxS frS iS) = .ok ps →
      bS.values.toList.filterMapM (phiStep ctxT frT iT) = .ok ps)
    (hsched : (ctxT.sched[bS.id]?).join = (ctxS.sched[bS.id]?).join)
    (horder : ∀ o, (ctxS.sched[bS.id]?).join = some o →
      CtxAgree ctxS ctxT o.toList ∧ Unread ctxS.f X o.toList)
    (hfr : frT = { frS with regs := frT.regs }) (hs : frT.regs.size = frS.regs.size)
    (hag : ∀ a, ¬ X a → frT.regs[a]? = frS.regs[a]?) :
    (∀ G, enterBlock env ctxS frS bS iS = .ok G → ∃ GT, enterBlock env ctxT frT bT iT = .ok GT ∧
      GT = { G with regs := GT.regs } ∧ GT.regs.size = G.regs.size ∧
      ∀ a, ¬ X a → GT.regs[a]? = G.regs[a]?) ∧
    (∀ e m, enterBlock env ctxS frS bS iS = .panic e m →
      enterBlock env ctxT frT bT iT = .panic e m) := by
  rw [enterBlock_eq, enterBlock_eq, hv, hid, hsched]
  cases hpsS : bS.values.toList.filterMapM (phiStep ctxS frS iS) with
  | panic e m => exact absurd hpsS filterMapM_phi_not_panic
  | stuck msg => exact ⟨fun _ h => (nomatch h), fun _ _ h => (nomatch h)⟩
  | ok ps =>
    rw [hps ps hpsS]
    simp only [Res.bind]
    cases ho : (ctxS.sched[bS.id]?).join with
    | none => exact ⟨fun _ h => (nomatch h), fun _ _ h => (nomatch h)⟩
    | some o =>
      obtain ⟨hco, huo⟩ := horder o ho
      exact evalAll_agree hco huo (by rw [hfr]) (by simp [setPhis_size, hs])
        (setPhis_agree ps hs hag)

/-- A block with the same values, `Phi`s staying `Phi`s and the others evaluating alike, has the
same schedule nodes (the nodes ignore `Phi`s). -/
theorem schedNodes_phiEq {f g : Func} {fb gb : Block} (hv : gb.values = fb.values)
    (h : ∀ x ∈ fb.values, (f.value? x = none → g.value? x = none) ∧
      ∀ v, f.value? x = some v → ∃ w, g.value? x = some w ∧ w.id = v.id ∧ w.op = v.op ∧
        (v.op ≠ .Phi → w.args = v.args)) :
    schedNodes g gb = schedNodes f fb := by
  unfold schedNodes
  rw [hv]
  apply Array.ext'
  simp only [Array.toList_filterMap]
  refine list_filterMap_congr _ fun x hx => ?_
  obtain ⟨hn, hs⟩ := h x (Array.mem_toList_iff.1 hx)
  cases hf : f.value? x with
  | none => rw [hn hf]
  | some v =>
    obtain ⟨w, hw, hid, hop, hargs⟩ := hs v hf
    rw [hw]
    simp only [hop, hid]
    by_cases hp : v.op = .Phi
    · simp [hp]
    · simp [hp, hargs hp]

end GoFV.Proof
