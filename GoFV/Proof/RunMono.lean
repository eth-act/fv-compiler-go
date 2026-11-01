import GoFV.Proof.Refine
import GoFV.Proof.PureMono

/-!
# The interpreter is monotone in refinement

`Res.Refines`: refinement of value results (`Res.Rel Refines`: results refined, the same panic
with refined memories, a stuck source refined by anything). `EvalOpMono P`: in every
environment with `P`, `evalOp` maps refined arguments to refined results, for contexts that
differ only in the function, its schedule and its value types, and frames with the same
arguments, initial memory and argument images.
-/

namespace GoFV.SSA.Sem

/-- Refinement of value results: `ok a ⊑ ok b` if `Refines a b`, `panic e m ⊑ panic e m'` if
`Mem.Refines m m'`, `stuck _ ⊑ r` for every `r`. -/
abbrev Res.Refines : Res Val → Res Val → Prop := Res.Rel Sem.Refines

end GoFV.SSA.Sem

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem

/-- `evalOp` is monotone in every environment with `P`. -/
def EvalOpMono (P : Env → Prop) : Prop :=
  ∀ (env : Env), P env → ∀ (ctx ctx' : Ctx),
    ctx' = { ctx with f := ctx'.f, sched := ctx'.sched, tys := ctx'.tys } →
    ∀ (fr fr' : Frame), fr'.args = fr.args → fr'.mem0 = fr.mem0 → fr'.images = fr.images →
    ∀ (v : Value) (ty : Ty) {argv argv' : List Val}, RefinesList argv argv' →
      Res.Refines (evalOp env ctx fr v argv ty) (evalOp env ctx' fr' v argv' ty)

end GoFV.Proof
