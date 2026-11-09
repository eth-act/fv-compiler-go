import GoFV.Proof.Pass.CSELSim
import GoFV.Proof.Pass.CSE

variable [GoFV.SSA.Sem.Addrs]

/-!
# `lowered cse` refines its input on `runL`

`loweredCse_refinesL`: the `lowered cse` pass (`loweredCsePass`, Phase 1's `cse` port run on
lowered ARM64 SSA) refines its input under `runL` when its input passes `check` and the lowered
checker `CSEL.crel` accepts the result against cse's substitution (`CSEL.frag`, decided; measured
by `lake exe csel-probe`): `crel_sound` gives `CRelL`, and `refinesL_of_rel` refinement.
-/

namespace GoFV.Proof.CSEL

open GoFV.SSA GoFV.Opt Dom

/-- **lowered cse refines its input on `runL`** (on inputs in `CSEL.frag`). -/
theorem loweredCse_refinesL {penv : PassEnv} {f : Func} {out : PassOut} {ce ce' : CheckEnv}
    (h : loweredCsePass penv f = .ok out) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ()) (hfrag : CSEL.frag penv f = true) :
    RefinesL out.tables out.func penv.tables f := by
  unfold CSEL.frag at hfrag
  simp only [loweredCsePass, Pass.ofFunc, bind, Except.bind, pure, Except.pure] at h
  cases hc : cseCtx penv with
  | error e => rw [hc] at h; cases h
  | ok c =>
    rw [hc] at h hfrag
    simp only at h hfrag
    unfold cse at h
    cases hr : cseRw c f with
    | error e => rw [hr] at h; cases h
    | ok p =>
      obtain ⟨g, rw⟩ := p
      rw [hr] at h hfrag
      simp only [Functor.map, Except.map] at h hfrag
      cases h
      rw [CSE.cseCtx_tabs hc] at hfrag
      exact refinesL_of_rel ⟨ce, check_wf hf⟩ (certOK_of_check (check_domCert hf))
        (crel_sound hfrag)

end GoFV.Proof.CSEL
