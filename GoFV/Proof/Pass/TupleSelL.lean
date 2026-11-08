import GoFV.Proof.Pass.MoveL
import GoFV.Opt.TupleSelectors

variable [GoFV.SSA.Sem.Addrs]

/-!
# `tighten tuple selectors` refines its input on `runL` (issue #395, #385)

`tightenTupleSelectors_refinesL`: `tighten tuple selectors` keeps the CFG; a selector outside
its tuple's block is cloned into that block and becomes a `Copy` of the clone, a later selector
of the same tuple component becomes a `Copy` of the first. For an input and output that pass
`check` and a pair the value-motion validator `moveB` accepts (clones of total ops, copies of
related values, `refinesL_of_move`), the output refines the input under `runL`.
-/

namespace GoFV.Proof.MoveL

open GoFV.SSA GoFV.Opt

/-- **tighten tuple selectors refines its input on `runL`.** -/
theorem tightenTupleSelectors_refinesL {penv : PassEnv} {f : Func} {out : PassOut}
    {ce ce' : CheckEnv} (h : tightenTupleSelectorsPass penv f = .ok out)
    (hf : check ce f = .ok ()) (hg : check ce' out.func = .ok ()) (hm : moveB f out.func = true) :
    RefinesL out.tables out.func penv.tables f := by
  simp only [tightenTupleSelectorsPass, Pass.ofFunc, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · cases h
    exact refinesL_of_move hf hg hm

end GoFV.Proof.MoveL
