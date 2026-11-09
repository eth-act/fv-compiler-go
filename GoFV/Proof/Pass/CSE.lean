import GoFV.Proof.Pass.CSESim
import GoFV.Proof.Pass.CSEBlock

variable [GoFV.SSA.Sem.Addrs]

/-!
# generic cse refines its input

`csePass` runs cse and keeps its result only if the checker `CSE.crel` accepts it (else the
input). On an input in the fragment `cseFrag` (the strict checker accepts the result too: `Load`
merges through different memory arguments are re-derived through provably disjoint stores, and
every block's roots keep their order), an accepted result is related to the input by `CRel`
(`crel_sound`), and `CRel` gives refinement: lock-step simulation with equal frames at block
entries (`refines_of_rel`), each block evaluating alike (`blockOK`: representatives hold their
values, `rep_corr`).
-/

namespace GoFV.Proof.CSE

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.SSA.DomCert Dom

/-- **generic cse refines its input** (on inputs in `cseFrag`). -/
theorem cse_refines {penv : PassEnv} {f : Func} {out : PassOut} {ce ce' : CheckEnv}
    (h : csePass penv f = .ok out) (hf : check ce f = .ok ()) (hg : check ce' out.func = .ok ())
    (hfrag : cseFrag penv f = true) : Refines out.tables out.func penv.tables f :=
  cse_refines_of h hf hg hfrag fun env _ _ _ hrel =>
    blockOK hrel ⟨ce, check_wf hf⟩ (certOK_of_check (check_domCert hf)) env

end GoFV.Proof.CSE
