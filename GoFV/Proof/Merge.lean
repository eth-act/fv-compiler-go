import GoFV.Proof.Pass.DeadRel
import GoFV.Proof.Mixed
import GoFV.Proof.Checked

/-!
# Shared lemmas for passes that merge blocks (branchelim, fuse)

Block steps (`blockStep_goto`, `blockStep_ret`, `blockStep_panic`, `blockStep_of`) and
terminators (`stepTerm_if`, `stepTerm_plain`, `stepTerm_same`); frames of one activation
(`frame_same`, `with_regs_same`); the non-pure nodes of a block's schedule (`npIn_schedNodes`,
`not_before_append`, `prio_root`); a listed value's block (`blockOf_listed`).
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt Dom

variable {f : Func}

/-- A listed value is listed in its block. -/
theorem blockOf_listed {ce : CheckEnv} (hwf : WF ce f) {a : ID} (hl : Listed f a) :
    ∃ v B, Placed f a v ∧ v.block = blockOf f a ∧ f.block? (blockOf f a) = some B ∧
      a ∈ B.values ∧ blockOf f a ∈ f.blocks := by
  obtain ⟨bid, B, ⟨hb, hB⟩, ha⟩ := hl
  obtain ⟨v, hP, hvb, -⟩ := placed_of_mem hwf hb hB ha
  have hbo := blockOf_placed hP
  refine ⟨v, B, hP, hbo.symm, ?_, ?_, ?_⟩
  · rw [hbo, hvb]; exact hB
  · exact ha
  · rw [hbo, hvb]; exact hb

/-- The result of one block entry that continues along an edge. -/
theorem blockStep_goto {env : Env} {ctx : Ctx} {fr G : Frame} {b : ID} {i : Nat} {e : Edge}
    (h : blockStep env ctx fr b i = .goto G e) :
    ∃ B, ctx.f.block? b = some B ∧ enterBlock env ctx fr B i = .ok G ∧
      stepTerm G B = .ok (.goto e) := by
  unfold blockStep at h
  split at h
  · cases h
  · rename_i B hB
    split at h
    · cases h
    · cases h
    · rename_i G' hG
      split at h
      · rename_i e' he; cases h; exact ⟨B, hB, hG, he⟩
      · cases h
      · cases h
      · cases h

theorem blockStep_ret {env : Env} {ctx : Ctx} {fr : Frame} {b : ID} {i : Nat} {rs : List Val}
    {m : Mem} (h : blockStep env ctx fr b i = .ret rs m) :
    ∃ B G, ctx.f.block? b = some B ∧ enterBlock env ctx fr B i = .ok G ∧
      stepTerm G B = .ok (.ret rs m) := by
  unfold blockStep at h
  split at h
  · cases h
  · rename_i B hB
    split at h
    · cases h
    · cases h
    · rename_i G' hG
      split at h
      · cases h
      · rename_i rs' m' he; cases h; exact ⟨B, G', hB, hG, he⟩
      · cases h
      · cases h

theorem blockStep_panic {env : Env} {ctx : Ctx} {fr : Frame} {b : ID} {i : Nat} {e : Panic}
    {m : Mem} (h : blockStep env ctx fr b i = .panic e m) :
    ∃ B, ctx.f.block? b = some B ∧ enterBlock env ctx fr B i = .panic e m := by
  unfold blockStep at h
  split at h
  · cases h
  · rename_i B hB
    split at h
    · rename_i e' m' hG; cases h; exact ⟨B, hB, hG⟩
    · cases h
    · rename_i G' hG
      split at h
      · cases h
      · cases h
      · rename_i e' m' he; exact absurd he CopyElim.stepTerm_not_panic
      · cases h

/-- The step of a block whose entry the target matches. -/
theorem blockStep_of {env : Env} {ctx : Ctx} {fr G : Frame} {b : ID} {i : Nat} {B : Block}
    (hB : ctx.f.block? b = some B) (hG : enterBlock env ctx fr B i = .ok G) :
    blockStep env ctx fr b i = match stepTerm G B with
      | .ok (.goto e) => .goto G e
      | .ok (.ret rs m) => .ret rs m
      | .panic e m => .panic e m
      | .stuck _ => .stuck := by
  unfold blockStep; rw [hB]; simp only [hG]; rfl

theorem blockStep_of_panic {env : Env} {ctx : Ctx} {fr : Frame} {b : ID} {i : Nat} {B : Block}
    (hB : ctx.f.block? b = some B) {e : Panic} {m : Mem}
    (h : enterBlock env ctx fr B i = .panic e m) : blockStep env ctx fr b i = .panic e m := by
  unfold blockStep; rw [hB]; simp only [h]

/-- An `If` terminator continues along successor 0 on `true`, 1 on `false`. -/
theorem stepTerm_if {G : Frame} {B : Block} {c : ID} (hk : B.kind = .If) (hc : B.controls = #[c])
    {n : Next} (h : stepTerm G B = .ok n) :
    ∃ b e, G.regs[c]? = some (some (.bool b)) ∧ B.succs[if b then 0 else 1]? = some e ∧
      n = .goto e := by
  unfold stepTerm at h
  rw [hk] at h
  cases hctl : Sem.control G B 0 with
  | ok v =>
    rw [hctl] at h
    simp only [bind, Res.bind] at h
    have hv : G.regs[c]? = some (some v) := by
      unfold Sem.control at hctl
      rw [hc] at hctl
      simp only [Array.getElem?_singleton, ite_true] at hctl
      cases hr : G.regs[c]? with
      | none => rw [hr] at hctl; simp [Res.ofOption] at hctl
      | some o =>
        cases o with
        | none => rw [hr] at hctl; simp [Res.ofOption] at hctl
        | some v' => rw [hr] at hctl; simp [Res.ofOption] at hctl; rw [hctl]
    split at h
    · obtain ⟨e, he, rfl⟩ := Dead.succ_ok h
      exact ⟨true, e, hv, he, rfl⟩
    · obtain ⟨e, he, rfl⟩ := Dead.succ_ok h
      exact ⟨false, e, hv, he, rfl⟩
    · cases h
  | panic e m => rw [hctl] at h; cases h
  | stuck msg => rw [hctl] at h; cases h

/-- A `Plain` terminator continues along successor 0. -/
theorem stepTerm_plain {G : Frame} {B : Block} (hk : B.kind = .Plain) {n : Next}
    (h : stepTerm G B = .ok n) : ∃ e, B.succs[0]? = some e ∧ n = .goto e := by
  unfold stepTerm at h
  rw [hk] at h
  exact Dead.succ_ok h

/-- A terminator with the same kind, controls and successors, in a frame agreeing on the
controls, does the same. -/
theorem stepTerm_same {G GT : Frame} {B BT : Block} (hk : BT.kind = B.kind)
    (hc : BT.controls = B.controls) (hsu : BT.succs = B.succs)
    (hag : ∀ c ∈ B.controls, GT.regs[c]? = G.regs[c]?) {n : Next} (h : stepTerm G B = .ok n) :
    stepTerm GT BT = .ok n := by
  rcases Dead.stepTerm_rel (.inl hk) hc hag h with ⟨k, e, rfl, he, -, hst⟩ | ⟨rs, m, rfl, hst⟩
  · rw [hst]; unfold succ; rw [hsu, he]; rfl
  · exact hst

theorem stepTerm_goto_mem {G : Frame} {B : Block} {e : Edge} (h : stepTerm G B = .ok (.goto e)) :
    e ∈ B.succs := by
  rcases Dead.stepTerm_rel (.inl rfl) rfl (fun _ _ => rfl) h with ⟨k, e', he, hk, -⟩ | ⟨rs, m, he, -⟩
  · cases he; exact Array.mem_of_getElem? hk
  · cases he

/-- An argument of a node listed before it in a dependency order. -/
theorem topoRem_arg_prefix {D : ID → List ID} :
    ∀ {L1 L2 : List ID}, TopoRem D (L1 ++ L2) → ∀ x ∈ L1, ∀ a ∈ D x, a ∈ L1 ++ L2 → a ∈ L1
  | [], _, _, x, hx, _, _, _ => absurd hx List.not_mem_nil
  | y :: L1, L2, ⟨h1, h2⟩, x, hx, a, ha, hm => by
    rcases List.mem_cons.1 hx with rfl | hx
    · exact absurd hm (h1 a ha)
    · rcases List.mem_cons.1 hm with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (topoRem_arg_prefix h2 x hx a ha hm)

/-- A block's non-pure schedule nodes are its `npOf` values. -/
theorem npIn_schedNodes {f : Func} {B : Block} (hown : ValuesOwn f B)
    (hnd : B.values.toList.Nodup) : npIn (schedNodes f B).toList = npOf f B := by
  funext x
  by_cases hx : x ∈ B.values ∧ ∃ v, f.value? x = some v ∧ v.op ≠ .Phi
  · obtain ⟨hxB, v, hv, hp⟩ := hx
    unfold npIn npOf
    rw [CopyElim.nodeOf_schedNodes hown hnd hxB hv hp, hv]
    simp [hxB, hp]
  · have hn : ¬ NodeIn (schedNodes f B).toList x := fun h => hx ((nodeIn_schedNodes hown).1 h)
    unfold npIn npOf
    rw [CopyElim.nodeOf_none hn]
    cases hc : B.values.contains x with
    | false => rfl
    | true =>
      cases hv : f.value? x with
      | none => rfl
      | some v =>
        have hph : v.op = .Phi := Classical.byContradiction fun hp =>
          hx ⟨Array.contains_iff_mem.1 hc, v, hv, hp⟩
        simp [hph]

/-- In `L1 ++ L2` nothing outside `L1` comes before a member of `L1`. -/
theorem not_before_append {L1 L2 : List ID} (hnd : (L1 ++ L2).Nodup) {x r : ID} (hr : r ∈ L1)
    (hx : x ∉ L1) : ¬ Order.Before (L1 ++ L2) x r := by
  rintro ⟨i, j, hij, hi, hj⟩
  obtain ⟨j', hj'⟩ := List.getElem?_of_mem hr
  have hj'lt : j' < L1.length := (List.getElem?_eq_some_iff.1 hj').1
  have := Order.idx_unique hnd hj (by rw [List.getElem?_append_left hj'lt]; exact hj')
  subst this
  rw [List.getElem?_append_left (by omega)] at hi
  exact hx (List.mem_of_getElem? hi)

/-- The priority of a root is not 0. -/
theorem prio_root {op : Op} (h : isRoot op = true) : prio op ≠ 0 := by
  unfold prio
  split <;> (try split) <;> simp_all

/-- Two frames of one activation. -/
theorem frame_same {a b c : Frame} (h1 : a = { c with regs := a.regs })
    (h2 : b = { c with regs := b.regs }) : a = { b with regs := a.regs } := by
  obtain ⟨ra, aa, ma, ia⟩ := a
  obtain ⟨rb, ab, mb, ib⟩ := b
  obtain ⟨rc, ac, mc, ic⟩ := c
  simp only [Frame.mk.injEq] at h1 h2 ⊢
  simp_all

/-- The phis of `dom` collected by the source. -/
theorem phis_of_enter {tabs : Tables} {env : Env} {fr G : Frame} {B : Block} {i : Nat}
    (h : enterBlock env (Ctx.make tabs f) fr B i = .ok G) :
    ∃ ps, B.values.toList.filterMapM (phiStep (Ctx.make tabs f) fr i) = .ok ps := by
  rw [enterBlock_eq] at h
  cases hps : B.values.toList.filterMapM (phiStep (Ctx.make tabs f) fr i) with
  | ok ps => exact ⟨ps, rfl⟩
  | panic e m => rw [hps] at h; cases h
  | stuck msg => rw [hps] at h; cases h

theorem with_regs_same {a b c : Frame} (h1 : a = { c with regs := a.regs })
    (h2 : b = { c with regs := b.regs }) (X : Array (Option Val)) :
    ({ a with regs := X } : Frame) = { b with regs := X } := by
  obtain ⟨ra, aa, ma, ia⟩ := a
  obtain ⟨rb, ab, mb, ib⟩ := b
  obtain ⟨rc, ac, mc, ic⟩ := c
  simp only [Frame.mk.injEq] at h1 h2 ⊢
  simp_all

theorem mixOK_of_single {env : Env} {ctx : Ctx} {G : Frame} {F : ID → Prop} {L : List ID}
    (h : ∀ x ∈ L, MixOK env ctx G F [x]) : MixOK env ctx G F L :=
  fun x hx => h x hx x List.mem_cons_self

end GoFV.Proof
