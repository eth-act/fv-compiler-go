import GoFV.Proof.Pass.DAEBlock
import GoFV.Proof.Sim
import GoFV.Proof.Refine

/-!
# dead auto elim: lock-step simulation with memories equal outside `U`

`ORel U o o'`: a returned outcome with related results and memories equal outside `U`, or the
same panic with memories equal outside `U`. `runLoop_simD`: a relation at block entries that
every source block step preserves (`StepRelD`) gives `ORel` of the loops' outcomes. `finish_rel`:
when `U` holds only frame temporaries of activation 0, `finish` turns `ORel` into refinement:
results are decoded from related values (same encodings) and from the frame's `Blk.local`
results (outside `U`), and the frame removal (`freeFrame`/`dropFrames`) makes the memories equal.
-/

namespace GoFV.Proof.DAE

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof

variable {U : Blk → Prop}

/-- Related outcomes of the loops. -/
inductive ORel (U : Blk → Prop) : Outcome → Outcome → Prop where
  | ret {rs rs' : List Val} {m m' : Mem} : VRL U rs rs' → Mem.EqOff U m m' →
      ORel U (.returned rs m) (.returned rs' m')
  | panic (e : Panic) {m m' : Mem} : Mem.EqOff U m m' → ORel U (.panicked e m) (.panicked e m')

/-- The target's block step matches a source block step along the same edge. -/
def StepRelD (U : Blk → Prop) (R : Frame → Frame → ID → Nat → Prop) : Step → Step → Prop
  | .goto frS e, sT => ∃ frT, sT = .goto frT e ∧ R frS frT e.b e.i
  | .ret rs m, sT => ∃ rs' m', sT = .ret rs' m' ∧ VRL U rs rs' ∧ Mem.EqOff U m m'
  | .panic e m, sT => ∃ m', sT = .panic e m' ∧ Mem.EqOff U m m'
  | .stuck, _ => True

/-- **Lock-step simulation** with related outcomes. -/
theorem runLoop_simD {env : Env} {ctxS ctxT : Ctx} (R : Frame → Frame → ID → Nat → Prop)
    (hsim : ∀ frS frT bid i, R frS frT bid i →
      StepRelD U R (blockStep env ctxS frS bid i) (blockStep env ctxT frT bid i)) :
    ∀ fuel frS frT bid i, R frS frT bid i → (runLoop env ctxS fuel frS bid i).Defined →
      ORel U (runLoop env ctxS fuel frS bid i) (runLoop env ctxT fuel frT bid i) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ h; exact h.elim
  | succ n ih =>
    intro frS frT bid i hR hd
    have hs := hsim frS frT bid i hR
    obtain ⟨g1, r1, p1, s1⟩ := runLoop_blockStep env ctxS n frS bid i
    obtain ⟨g2, r2, p2, -⟩ := runLoop_blockStep env ctxT n frT bid i
    cases hS : blockStep env ctxS frS bid i with
    | goto frS' e =>
      rw [hS] at hs
      obtain ⟨frT', hT, hR'⟩ := hs
      rw [g1 _ _ hS] at hd ⊢
      rw [g2 _ _ hT]
      exact ih _ _ _ _ hR' hd
    | ret rs m =>
      rw [hS] at hs
      obtain ⟨rs', m', hT, hr, hm⟩ := hs
      rw [r1 _ _ hS, r2 _ _ hT]
      exact .ret hr hm
    | panic e m =>
      rw [hS] at hs
      obtain ⟨m', hT, hm⟩ := hs
      rw [p1 _ _ hS, p2 _ _ hT]
      exact .panic e hm
    | stuck => exact absurd hd (s1 hS)

/-! ## `finish` -/

theorem VRL.take : ∀ (n : Nat) {as bs : List Val}, VRL U as bs → VRL U (as.take n) (bs.take n)
  | 0, _, _, _ => by simp; exact .nil
  | _ + 1, _, _, .nil => .nil
  | n + 1, _, _, .cons h t => by simp only [List.take_succ_cons]; exact .cons h (VRL.take n t)

theorem VRL.drop : ∀ (n : Nat) {as bs : List Val}, VRL U as bs → VRL U (as.drop n) (bs.drop n)
  | 0, _, _, h => by simpa using h
  | _ + 1, _, _, .nil => .nil
  | n + 1, _, _, .cons _ t => by simp only [List.drop_succ_cons]; exact VRL.drop n t

theorem putBytes_fold_eq : ∀ {pieces pieces' : List Val}, VRL U pieces pieces' →
    ∀ (ls : List (Nat × Ty)) (buf : Array Byte),
      ((ls.zip pieces').foldl (fun buf ((o, lt), v) => putBytes buf o (encode lt v)) buf) =
        ((ls.zip pieces).foldl (fun buf ((o, lt), v) => putBytes buf o (encode lt v)) buf)
  | _, _, .nil, ls, _ => by simp
  | _, _, .cons _ _, [], _ => by simp
  | _, _, .cons h t, _ :: ls, buf => by
    simp only [List.zip_cons_cons, List.foldl_cons]
    rw [h.encode]
    exact putBytes_fold_eq t ls _

theorem local_notU (hU : TempU U) (a n : Nat) : ¬ U (.local a n) := by
  intro hu; obtain ⟨k, hk⟩ := hU _ hu; cases hk

theorem goResults_post_eq (hU : TempU U) {m m' : Mem} (hm : Mem.EqOff U m m') :
    ∀ (os : List (Option AuxRef × Ty × Nat)) {pieces pieces' : List Val},
      VRL U pieces pieces' →
      goResults.post 0 m' pieces' os = goResults.post 0 m pieces os
  | [], pieces, pieces', hp => by
    unfold goResults.post
    rw [show pieces'.isEmpty = pieces.isEmpty by cases hp <;> rfl]
  | (name, t, k) :: os, pieces, pieces', hp => by
    unfold goResults.post
    have hlen := hp.length
    simp only [hlen, goResults_post_eq hU hm os (hp.drop k),
      putBytes_fold_eq (hp.take k)]
    split
    · cases name with
      | none => rfl
      | some n =>
        have hr : ∀ (n' sz : Nat), m'.read ⟨.local 0 n', 0⟩ sz = m.read ⟨.local 0 n', 0⟩ sz :=
          fun n' sz => EqOff.read hm ⟨.local 0 n', 0⟩ sz (local_notU hU 0 n')
        rw [goResults_post_eq hU hm os hp]
        simp only [hr]
    · rfl

theorem encode_zip_eq : ∀ {rs rs' : List Val}, VRL U rs rs' →
    ∀ (os : List (Option AuxRef × Ty × Nat)),
      ((rs'.zip os).map fun (v, (_, t, _)) => encode t v) =
        ((rs.zip os).map fun (v, (_, t, _)) => encode t v)
  | _, _, .nil, _ => rfl
  | _, _, .cons _ _, [] => rfl
  | _, _, .cons h t, _ :: os => by
    simp only [List.zip_cons_cons, List.map_cons, h.encode, encode_zip_eq t os]

theorem hasTy_zip_eq' : ∀ {rs rs' : List Val}, VRL U rs rs' →
    ∀ (os : List (Option AuxRef × Ty × Nat)),
      ((rs'.zip os).all fun (v, (_, t, _)) => v.hasTy t) =
        ((rs.zip os).all fun (v, (_, t, _)) => v.hasTy t)
  | _, _, .nil, _ => rfl
  | _, _, .cons _ _, [] => rfl
  | _, _, .cons h t, _ :: os => by
    simp only [List.zip_cons_cons, List.all_cons, h.hasTy, hasTy_zip_eq' t os]

theorem goResults_eq (hU : TempU U) (outs : Array (Option AuxRef × Ty × Nat)) {rs rs' : List Val}
    {m m' : Mem} (hr : VRL U rs rs') (hm : Mem.EqOff U m m') :
    goResults outs 0 rs' m' = goResults outs 0 rs m := by
  unfold goResults
  simp only [hr.length, hasTy_zip_eq' hr, encode_zip_eq hr, goResults_post_eq hU hm _ hr]

/-- **`finish` turns related loop outcomes into refinement.** -/
theorem finish_rel (hU : TempU U) {outs : Array (Option AuxRef × Ty × Nat)} {o o' : Outcome}
    (hd : (finish outs 0 o).Defined) (h : ORel U o o') :
    OutcomeRefines 0 (finish outs 0 o) (finish outs 0 o') := by
  cases h with
  | panic e hm =>
    refine .panicked e ?_
    rw [EqOff.dropFrames hU hm]
    exact Mem.Refines.refl _
  | @ret rs rs' m m' hr hm =>
    have hfin : finish outs 0 (.returned rs' m') = finish outs 0 (.returned rs m) := by
      simp only [finish, hr.anyPoison, goResults_eq hU outs hr hm, EqOff.freeFrame hU hm]
    rw [hfin]
    exact OutcomeRefines.refl hd

end GoFV.Proof.DAE
