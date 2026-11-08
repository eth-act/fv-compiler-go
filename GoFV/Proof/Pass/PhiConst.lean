import GoFV.Proof.Pass.SccpTerm

variable [GoFV.SSA.Sem.Addrs]

/-!
# Constant `Phi`s refine (issue #69)

The constant-`Phi` layer of the rewrite validator (`GoFV.Opt.RewriteCheck.pcRel`;
`generic.rules:782`–`:785`, `(Phi (Const64 [c]) (Const64 [c])) => (Const64 [c])` and the
narrower widths) relates its input `f` to `g` by sccp's checker (`Sccp.sccpOK` with the
certificate `pcCells`: the turned `Phi`s and their constant arguments claim their constants,
every edge and block is executable). sccp's simulation then applies as in `sccp_refines`: the
source invariant `sccpInv` (a register with a constant cell holds `poison` or the constant) and
the atom simulation (`AtomSim.atomSimInv_refines`).
-/

namespace GoFV.Proof.PhiConst

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof.AtomSim GoFV.Proof.Sccp

/-- **Constant `Phi`s refine** under monotone contracts: what `pcRel` accepts between checked
functions refines. -/
theorem pc_refines {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} (hf : check ce f = .ok ())
    (hg : check ce' g = .ok ()) (h : RewriteCheck.pcRel tabs f g = true) :
    RefinesUnder Env.Mono tabs g tabs f := by
  have K := sccpOK_spec h
  have hwf := check_wf hf
  exact atomSimInv_refines hf hg K.atoms (sccpInv hwf K) (sc_atomArgs hwf K) (sc_steps hwf K)

end GoFV.Proof.PhiConst
