import GoFV.Proof.Pass.SccpTerm

/-!
# sccp refines its input (issue #32)

`sccp_refines`: the validated pass (`GoFV.Opt.sccpChecked`) refines its input under monotone
contracts. A rejected or unchanged result is the input; an accepted one (`sccpOK`) is the atom
simulation under sccp's source invariant (`sccpInv`: registers with a constant cell hold `poison`
or the constant, on executable blocks), whose premises are `sc_atomArgs` and `sc_steps`.
-/

namespace GoFV.Proof.Sccp

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof.AtomSim

/-- **sccp refines its input.** -/
theorem sccp_refines {penv : PassEnv} {f : Func} {out : PassOut} {ce ce' : CheckEnv}
    (h : sccpChecked penv f = .ok out) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ()) :
    RefinesUnder Env.Mono out.tables out.func penv.tables f := by
  unfold sccpChecked at h
  cases hr : GoFV.Rules.RwEnv.ofPassEnv penv with
  | error e => simp [hr, bind, Except.bind] at h
  | ok rw =>
    cases ha : Sccp.analyze rw penv.tables f with
    | error e => simp [hr, ha, bind, Except.bind] at h
    | ok a =>
      simp only [hr, ha, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only at hg ⊢
      split
      · rename_i hok
        simp only [hok, ↓reduceIte] at hg
        simp only [Bool.and_eq_true] at hok
        have K := sccpOK_spec hok.2
        have hwf := check_wf hf
        exact atomSimInv_refines hf hg K.atoms (sccpInv hwf K) (sc_atomArgs hwf K) (sc_steps hwf K)
      · exact RefinesUnder.refl _ _ _

end GoFV.Proof.Sccp
