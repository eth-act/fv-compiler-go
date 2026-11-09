import GoFV.Proof.TabsAgreeModOps
import GoFV.Proof.Pass.DAESrc
import GoFV.Opt.TabsAgreeMod

variable [GoFV.SSA.Sem.Addrs]

/-!
# Running in tables with extra frame temporaries: the source avoids them

The source runs in the input tables, where the extra frame temporaries `X` do not exist; no
value of the function names them, no integer converts to a `temp` block, and the run's inputs
and the contracts' results hold no pointer into them. `evalOp_avoids`: a value on arguments that
avoid `X` has a result that avoids `X` (`DAE.evalOp_avoids`). `evalOp_notArm`: an op `evalOp`
does not evaluate by name is `stuck` if it is a root (`evalOp_stuckRoot`) and `evalPure`
otherwise.
-/

namespace GoFV.Proof.TabsMod

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof.DSE

/-- `evalOp` of an op it does not evaluate by name. -/
theorem evalOp_notArm {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val} {ty : Ty}
    (hn : v.op ∉ evalOpArms) :
    evalOp env ctx fr v argv ty =
      if isRoot v.op then atomicRoot v argv
      else pure (evalPure v.op ty v.auxInt v.aux argv) := by
  have hf : frameVal ctx v = none := by
    unfold frameVal
    split <;> first | rfl | (rename_i heq; rw [heq] at hn; simp [evalOpArms] at hn)
  unfold evalOp
  split <;> first | (rename_i heq; rw [heq] at hn; simp [evalOpArms] at hn; done) | skip
  rw [hf]

/-- A root `evalOp` does not evaluate by name is `stuck`. -/
theorem evalOp_stuckRoot {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (h : stuckRoot v.op = true) : ∃ msg, evalOp env ctx fr v argv ty = .stuck msg := by
  unfold stuckRoot at h
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
  have hn : v.op ∉ evalOpArms := by
    intro hm; rw [List.contains_iff_mem.2 hm] at h; cases h.1.2
  rw [evalOp_notArm hn, h.1.1]
  exact atomicRoot_unmodelled h.2 argv

/-- A non-root op `evalOp` does not evaluate by name is `evalPure`. -/
theorem evalOp_pure_of {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (hn : v.op ∉ evalOpArms) (hr : isRoot v.op = false) :
    evalOp env ctx fr v argv ty = .ok (evalPure v.op ty v.auxInt v.aux argv) := by
  rw [evalOp_notArm hn, hr]; rfl

variable {X : Blk → Bool}

local notation "U" => fun b => X b = true

/-- A call on arguments that avoid `X` returns a result that avoids `X` (the contracts are
oblivious to the extra temporaries, `callOp_rel`). -/
theorem callOp_avoidsX {env : Env} (hE : env.TempOblivious) (hX : TempX X) {ctx : Ctx} {v : Value}
    {argv : List Val} (hargs : ∀ z ∈ argv, Val.Avoids U z) :
    ∀ r, callOp env ctx v argv = .ok r → Val.Avoids U r := by
  intro r h
  rcases List.eq_nil_or_concat argv with rfl | ⟨L, w, rfl⟩
  · obtain ⟨msg, hm⟩ := callOp_nil_stuck (env := env) (ctx := ctx) (v := v)
    rw [hm] at h; cases h
  · rw [List.concat_eq_append] at hargs h
    exact ((callOp_rel hE hX (.refl w) hargs).1 r h).1

/-- **A value on arguments that avoid `X` has a result that avoids `X`** (its frame inputs avoid
`X`, and a `LocalAddr` names no block of `X`; `DAE.evalOp_avoids`). -/
theorem evalOp_avoids {env : Env} (hE : env.TempOblivious) (hX : TempX X) {ctx : Ctx} {fr : Frame}
    (hfr : DAE.FrameOK U fr) {v : Value}
    (hloc : ∀ n, v.aux = some n → X (frameBlk ctx.tabs ctx.act n) = false)
    {argv : List Val} {ty : Ty} {r : Val} (hargs : ∀ z ∈ argv, Val.Avoids U z)
    (h : evalOp env ctx fr v argv ty = .ok r) : Val.Avoids U r :=
  DAE.evalOp_avoids (tempU_of hX) hfr (callOp_avoidsX hE hX hargs)
    (fun n _ hn hu => by rw [hloc n hn] at hu; cases hu) hargs h

end GoFV.Proof.TabsMod
