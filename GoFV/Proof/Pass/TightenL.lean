import GoFV.Proof.Pass.MoveL
import GoFV.Opt.Tighten

/-!
# `tighten` refines its input on `runL` (issue #385)

`tighten_refinesL`: `tighten` keeps the CFG and moves values between blocks (down to the
dominator-tree LCA of their uses, out of loops); for an input and output that pass `check` and a
pair the value-motion validator `moveB` accepts (translation validation, `refinesL_of_move`),
the output refines the input under `runL`. The pass keeps the tables.
-/

namespace GoFV.Proof.MoveL

open GoFV.SSA GoFV.Opt

/-- **tighten refines its input on `runL`.** -/
theorem tighten_refinesL {penv : PassEnv} {f : Func} {out : PassOut} {ce ce' : CheckEnv}
    (h : tightenPass penv f = .ok out) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ()) (hm : moveB f out.func = true) :
    RefinesL out.tables out.func penv.tables f := by
  simp only [tightenPass, Pass.ofFunc, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · cases h
    exact refinesL_of_move hf hg hm

end GoFV.Proof.MoveL
