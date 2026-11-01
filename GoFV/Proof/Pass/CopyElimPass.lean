import GoFV.Proof.Pass.CopyElim
import GoFV.Proof.Pass.CopyElimLoop

/-!
# `early phielim and copyelim` refines its input

`copyelim_refines`: `copyelim_rel` (the pass establishes `CopyRel`) and `refines_of_rel` (the
relation gives refinement), for an input and output that pass `check`, with the input in the
fragments `CopyFrag` and `SimFrag`.
-/

namespace GoFV.Proof.CopyElim

open GoFV.SSA GoFV.Opt Dom

/-- **copyelim refines its input.** -/
theorem copyelim_refines {penv : PassEnv} {f : Func} {out : PassOut} {ce ce' : CheckEnv}
    (h : copyelimPass penv f = .ok out) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ()) (hcf : CopyFrag penv.tables f)
    (hsf : SimFrag penv.tables f) : Refines out.tables out.func penv.tables f := by
  simp only [copyelimPass, Pass.ofFunc, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i g hcp
    cases h
    exact refines_of_rel
      { wf := ⟨ce, check_wf hf⟩, wg := ⟨ce', check_wf hg⟩,
        cf := certOK_of_check (check_domCert hf), cg := certOK_of_check (check_domCert hg),
        rel := copyelim_rel hf hcf hcp, frag := hsf }

end GoFV.Proof.CopyElim
