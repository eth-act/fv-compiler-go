import GoFV.Proof.Pass.WBNpOrder

/-!
# writebarrier: the source facts of the chain's values (issue #36)

`cov_intro`: a value of the chain has its source facts (`Cov`) when the source evaluated, in the
reference frame, every value of a set `P` closed under in-block arguments that contains the value
itself (kept, role `held`) or the run its role copies (stores and dropped nil check), and the
run's memory is a memory for a `WB`. `runMem_of_ev`: a run whose first store the source evaluated
has a memory. `grOK_panic`: the reference frame of a block entry that panics after the prefix
`pre` of its schedule.
-/

namespace GoFV.Proof.WB

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Opt GoFV.Opt.WBCheck GoFV.Proof

namespace Setup

variable {c : WBCheck.Ctx} {b : ID} {B : Block} {rs : List Run} {l : ID}

/-- A run whose first store the source evaluated: its memory is a memory. -/
theorem runMem_of_ev (S : Setup c b B rs l) {env : Env} {Gr : Frame} {j : Nat} {r : Run}
    (hr : rs[j]? = some r) {s0 : ID} (hs0 : r.src[0]? = some s0) (hev : Ev env c Gr s0) :
    ∃ M, RunMem Gr rs j M := by
  sorry

/-- **Source facts from a closed set of evaluated values.** -/
theorem cov_intro (S : Setup c b B rs l) {env : Env} {Gr : Frame} {P : ID → Prop}
    (hEv : ∀ x, P x → Ev env c Gr x)
    (hPcl : ∀ x a v, P x → c.f.value? x = some v → a ∈ v.args → a ∈ B.values →
      (∀ va, c.f.value? a = some va → va.op ≠ .Phi) → P a)
    {x : ID}
    (hheld : c.roleOf rs x = .held → c.K.getD x false = true →
      (∀ u, c.f.value? x = some u → u.op ≠ .Phi) → P x)
    (hrun : ∀ j, ((∃ k, c.roleOf rs x = .tgt j k) ∨ c.roleOf rs x = .ncEnd j ∨
        c.roleOf rs x = .ncThen j) →
      ∀ r, rs[j]? = some r → (∀ s ∈ r.src, P s) ∧ (∀ n ∈ ncsOf c r, P n))
    (hwb : ∀ j, c.roleOf rs x = .wb j → ∃ M, RunMem Gr rs j M) :
    Cov env c rs Gr x := by
  sorry

/-- **The reference frame of a panicking block entry.** -/
theorem grOK_panic (S : Setup c b B rs l) (hall : ∀ b' ∈ c.f.blocks, c.blockOK b' = true)
    {ce : CheckEnv} (hwf : WF ce c.f) (hcf : CertOK c.f) {env : Env} (hE : ContractsOK env)
    {frS frT : Frame} {i : Nat} (hA : SimAt env c frS frT b i) {ps : List (ID × Val)}
    (hps : B.values.toList.filterMapM (phiStep (Ctx.make c.tabs c.f) frS i) = .ok ps)
    {o : Array ID} (ho : schedule c.f B = some o) {pre post : List ID} {r : ID}
    (hsplit : o.toList = pre ++ r :: post) {Gpre : Frame}
    (hpre : evalAll env (Ctx.make c.tabs c.f) { frS with regs := setPhis ps frS.regs } pre =
      .ok Gpre)
    (hGf : Gpre = { frS with regs := Gpre.regs })
    (hGo : ∀ z, z ∉ B.values → Gpre.regs[z]? = frS.regs[z]?)
    (hGv : ∀ x ∈ pre, ∃ v y, c.f.value? x = some v ∧ Gpre.regs[x]? = some (some y) ∧
      evalValue env (Ctx.make c.tabs c.f) Gpre v = .ok y) :
    GrOK c B rs Gpre frS := by
  sorry

end Setup

end GoFV.Proof.WB
