import GoFV.Proof.Pass.MoveLCheck
import GoFV.Proof.Pass.CSEOp
import GoFV.Proof.EvalOpLDispatch

variable [GoFV.SSA.Sem.Addrs]

/-!
# Total ops (`totalOp`) under `runL`

A total op's non-faulting lowered evaluation (`evalOpL false`) is `.ok`, and its result does not
depend on the value's ID (`totalOp_ok`); a `Copy` returns its argument (`evalOpL_copy`). Only
`mayPanic` values panic (`mayPanic_of_panic`).
-/

namespace GoFV.Proof.MoveL

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof

/-- `actOp` is `LowerTerm.actOp` (`evalOpL_eq`): the same 91 ops. -/
private theorem actOp_eq_lowerActOp (op : Op) : actOp op = GoFV.Opt.LowerTerm.actOp op := by
  cases op <;> rfl

/-- `evalOpL`'s last arm, for an arm64 op outside `actOp`. -/
theorem evalOpL_pure {faulting : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} (hg : v.op.generic = false) (ha : actOp v.op = false) :
    evalOpL faulting env ctx fr v argv ty =
      if isRoot v.op then atomicRoot v argv else pure (Arm64.evalPure v.op ty v.auxInt v.aux argv) := by
  exact evalOpL_of_not_actOp hg (by rw [← actOp_eq_lowerActOp]; exact ha)

/-- `evalOpL` at an `actOp` op is `arm64Op`. -/
theorem evalOpL_act {faulting : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} (hg : v.op.generic = false) (ha : actOp v.op = true) :
    evalOpL faulting env ctx fr v argv ty = arm64Op faulting env ctx fr v argv ty := by
  exact evalOpL_of_actOp hg (by rw [← actOp_eq_lowerActOp]; exact ha)

/-- `arm64Op` (not faulting) at an `actTotal` op: `.ok`, independently of the value's ID. -/
theorem arm64Op_total {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (ht : actTotal v.op = true) :
    ∃ r, arm64Op false env ctx fr v argv ty = .ok r ∧
      ∀ i, arm64Op false env ctx fr { v with id := i } argv ty = .ok r := by
  have hnf : ∀ w : Value, nilFaults false ctx w argv = none := fun _ => rfl
  unfold actTotal at ht
  split at ht
  all_goals first
    | exact absurd ht Bool.false_ne_true
    | (rename_i heq
       unfold arm64Op
       simp only [hnf, heq]
       repeat' split
       all_goals exact ⟨_, rfl, fun _ => rfl⟩)

/-- **A total op evaluates**, to a result that does not depend on the value's ID. -/
theorem totalOp_ok {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (ht : totalOp v.op = true) :
    ∃ r, evalOpL false env ctx fr v argv ty = .ok r ∧
      ∀ i, evalOpL false env ctx fr { v with id := i } argv ty = .ok r := by
  unfold totalOp at ht
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at ht
  obtain ⟨⟨-, hr⟩, hc⟩ := ht
  cases hg : v.op.generic
  · rw [hg] at hc
    simp only [Bool.false_eq_true, ite_false, Bool.or_eq_true, Bool.not_eq_true'] at hc
    rcases hc with hc | hc
    · have hact : actOp v.op = true := by
        unfold actTotal at hc; unfold actOp
        split at hc <;> first | exact absurd hc (by decide) | (rename_i heq; rw [heq])
      obtain ⟨r, h1, h2⟩ := arm64Op_total (env := env) (ctx := ctx) (fr := fr) (argv := argv)
        (ty := ty) hc
      exact ⟨r, by rw [evalOpL_act hg hact]; exact h1,
        fun i => by rw [evalOpL_act (v := { v with id := i }) hg hact]; exact h2 i⟩
    · refine ⟨Arm64.evalPure v.op ty v.auxInt v.aux argv, ?_, fun i => ?_⟩
      · rw [evalOpL_pure hg hc, hr]; rfl
      · rw [evalOpL_pure (v := { v with id := i }) hg hc]
        show (if isRoot v.op then _ else _) = _
        rw [hr]; rfl
  · rw [hg] at hc
    simp only [ite_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
    obtain ⟨ha, hb⟩ := hc
    obtain ⟨r, hr1⟩ := CSE.evalOp_total (env := env) (ctx := ctx) (fr := fr) (argv := argv) (ty := ty) hr ha hb
    refine ⟨r, by rw [evalOpL_generic _ _ _ _ _ _ hg]; exact hr1, fun i => ?_⟩
    rw [evalOpL_generic _ _ _ _ _ _ (v := { v with id := i }) hg]
    obtain ⟨r', hr2⟩ := CSE.evalOp_total (env := env) (ctx := ctx) (fr := fr) (v := { v with id := i })
      (argv := argv) (ty := ty) hr ha hb
    rw [hr2, CSE.evalOp_ok_id (u := v) (v := { v with id := i }) rfl rfl rfl hr hr1 hr2]

/-- A `Copy` returns its argument. -/
theorem evalOpL_copy {faulting : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {ty : Ty} {x : Val} (hop : v.op = .Copy) : evalOpL faulting env ctx fr v [x] ty = .ok x := by
  have hg : v.op.generic = true := by rw [hop]; rfl
  rw [evalOpL_generic _ _ _ _ _ _ hg]
  have hr : isRoot v.op = false := by rw [hop]; rfl
  rw [CSE.evalOp_tail hr (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun)]
  have hf : frameVal ctx v = none := by unfold frameVal; rw [hop]
  rw [hf]
  show Res.ok (evalPure v.op ty v.auxInt v.aux [x]) = _
  rw [hop]; rfl

/-- **Only `mayPanic` values panic** under `runL` (not faulting). -/
theorem mayPanic_of_panic {md : LMode} (hmd : md.faulting = false) {env : Env} {ctx : Ctx}
    {fr : Frame} {f : Func} {x : ID} {v : Value} (hv : f.value? x = some v) {e : Panic} {m : Mem}
    (h : evalValueL md env ctx fr v = .panic e m) : mayPanic f x = true := by
  have hp := evalValueL_panic_op h
  rw [hmd] at hp
  unfold mayPanic; rw [hv]
  simp only [Bool.or_eq_true]
  rcases hp with hp | hp | ⟨hp, -⟩
  · exact .inl hp
  · exact .inr hp
  · exact absurd hp Bool.false_ne_true

/-- A total op does not panic. -/
theorem totalOp_not_mayPanic {op : Op} (ht : totalOp op = true) : (op.call || op.nilCheck) = false := by
  unfold totalOp isRoot at ht
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_false_iff] at ht
  obtain ⟨⟨-, ⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, -⟩⟩, -⟩ := ht
  rw [h1, h2]; rfl

end GoFV.Proof.MoveL
