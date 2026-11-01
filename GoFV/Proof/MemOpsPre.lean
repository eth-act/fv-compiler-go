import GoFV.SSA.Sem.Runtime

/-!
# Environments whose memory runtime calls are the model's contracts (#151)

`Env.MemOps`: `runtime.memclrNoHeapPointers` and `runtime.memmove`, if the environment has them
at all, are `Runtime.memclr` and `Runtime.memmove`. A missing contract makes `callOp` stuck, so
the call lemmas of `GoFV.Proof.Pass.SegCall` (a call ⊑ the plain `Zero`/`Move` write) hold in
every such environment: `Env.runtime` and `Env.p1` (which has neither).
-/

namespace GoFV.SSA.Sem

/-- `runtime.memclrNoHeapPointers` and `runtime.memmove` are the runtime model's contracts, or
missing. -/
def Env.MemOps (env : Env) : Prop :=
  (∀ c, env.extern "runtime.memclrNoHeapPointers" = some c → c = Runtime.memclr) ∧
    (∀ c, env.extern "runtime.memmove" = some c → c = Runtime.memmove)

theorem Env.runtime_memOps : Env.runtime.MemOps :=
  ⟨fun _ h => (Option.some.inj h).symm, fun _ h => (Option.some.inj h).symm⟩

theorem Env.p1_memOps : Env.p1.MemOps :=
  ⟨fun _ h => (by cases h), fun _ h => (by cases h)⟩

end GoFV.SSA.Sem
