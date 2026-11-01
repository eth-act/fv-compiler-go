import GoFV.Proof.Pass.WBPanicFacts

/-!
# writebarrier: a block entry that panics (issue #36)

`chain_panic`: when the source's entry of block `b` panics at node `r`, the target's chain
panics alike. `r` is a kept node of segment `k` (a call or nil check): the target walks to
segment `k` and panics at `r` there. Or `r` is the dropped nil check of run `j`: the target
walks to segment `j`, runs it, and panics at the nil check's copy in the buffer block (flag set)
or in segment `j + 1` (flag clear), with the run's memory. Before its panic point the target
evaluates only values whose source counterparts the source evaluated before `r`
(`ord_pre`, `np_before`).
-/

namespace GoFV.Proof.WB

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Opt GoFV.Opt.WBCheck GoFV.Proof

namespace Setup

variable {c : WBCheck.Ctx} {b : ID} {B : Block} {rs : List Run} {l : ID}

/-- **A panicking block entry.** -/
theorem chain_panic (S : Setup c b B rs l) (hall : ∀ b' ∈ c.f.blocks, c.blockOK b' = true)
    {ce : CheckEnv} (hwf : WF ce c.f) (hcf : CertOK c.f) {env : Env} (hE : ContractsOK env)
    {frS frT : Frame} {i : Nat} (hA : SimAt env c frS frT b i) {e : Panic} {m : Mem}
    (hen : enterBlock env (Ctx.make c.tabs c.f) frS B i = .panic e m) :
    ∃ n, runLoop env (Ctx.make c.tabs c.g) n frT b i = .panicked e m := by
  sorry

end Setup

end GoFV.Proof.WB
