import GoFV.Opt.LowerTerm

/-!
# `evalOpL`'s dispatch as an `if` chain

`evalOpL` (`GoFV/SSA/Sem/RunL.lean`) picks `arm64Op` by a 91-arm `match` on the op. A `split` or
`simp` that meets that `match` on a variable op realizes its splitter and equations privately in
the module doing it: ~12 s per module, regenerated in 15 proof modules (whole-tree profile at
f53b580; LEARNINGS.md, "Large `match` on a variable"). `evalOpL_eq` states the same function as an
`if` chain on `LowerTerm.actOp` (the same 91 ops), proved once here by cases on the op; importers
rewrite with it and split the `if`s instead.
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem

theorem evalOpL_eq {faulting : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} :
    evalOpL faulting env ctx fr v argv ty =
      if v.op.generic then evalOp env ctx fr v argv ty
      else if GoFV.Opt.LowerTerm.actOp v.op then arm64Op faulting env ctx fr v argv ty
      else if isRoot v.op then atomicRoot v argv
      else pure (Arm64.evalPure v.op ty v.auxInt v.aux argv) := by
  unfold evalOpL
  generalize v.op = op
  cases op <;> rfl

/-- An op `evalOpL` sends to `arm64Op`. -/
theorem evalOpL_of_actOp {faulting : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} (hg : v.op.generic = false)
    (ha : GoFV.Opt.LowerTerm.actOp v.op = true) :
    evalOpL faulting env ctx fr v argv ty = arm64Op faulting env ctx fr v argv ty := by
  rw [evalOpL_eq, hg, ha]; rfl

/-- An arm64 op `evalOpL` does not send to `arm64Op`: `atomicRoot` for a root, else pure. -/
theorem evalOpL_of_not_actOp {faulting : Bool} {env : Env} {ctx : Ctx} {fr : Frame} {v : Value}
    {argv : List Val} {ty : Ty} (hg : v.op.generic = false)
    (ha : GoFV.Opt.LowerTerm.actOp v.op = false) :
    evalOpL faulting env ctx fr v argv ty =
      if isRoot v.op then atomicRoot v argv else pure (Arm64.evalPure v.op ty v.auxInt v.aux argv) := by
  rw [evalOpL_eq, hg, ha]; rfl

/-- The non-root ops `evalOpL` sends to `arm64Op` evaluate when memory ops do not fault. -/
theorem arm64Op_total_of_actOp {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (ha : GoFV.Opt.LowerTerm.actOp v.op = true) (hr : isRoot v.op = false) :
    ∃ r, arm64Op false env ctx fr v argv ty = .ok r := by
  obtain ⟨id, op, type, auxInt, aux, pos, uses, args, block⟩ := v
  dsimp only at ha hr
  cases op
  all_goals first | exact absurd ha Bool.false_ne_true | exact absurd hr (by decide) | skip
  all_goals
    delta arm64Op nilFaults
    simp only [Bool.not_false, ↓reduceIte]
    first | exact ⟨_, rfl⟩ | ((repeat' split) <;> exact ⟨_, rfl⟩)

end GoFV.Proof
