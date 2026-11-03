import GoFV.Proof.Pass.MoveL
import GoFV.Opt.Tighten

/-!
# `phi tighten` refines its input on `runL` (issue #385)

`phiTighten_refinesL`: `phi tighten` keeps the CFG and clones each rematerializeable `Phi`
argument into the corresponding predecessor (a fresh value, the `Phi` reading the clone); for an
input and output that pass `check` and a pair the value-motion validator `moveB` accepts
(clones of total ops, `refinesL_of_move`), the output refines the input under `runL`.
-/

namespace GoFV.Proof.MoveL

open GoFV.SSA GoFV.Opt

/-- **phi tighten refines its input on `runL`.** -/
theorem phiTighten_refinesL {penv : PassEnv} {f : Func} {out : PassOut} {ce ce' : CheckEnv}
    (h : phiTightenPass penv f = .ok out) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ()) (hm : moveB f out.func = true) :
    RefinesL out.tables out.func penv.tables f := by
  simp only [phiTightenPass, Pass.ofFunc, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · cases h
    exact refinesL_of_move hf hg hm

end GoFV.Proof.MoveL
