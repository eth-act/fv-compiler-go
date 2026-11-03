import GoFV.Proof.Pass.CopyElimL
import GoFV.Proof.Pass.CopyElimLoop

/-!
# `late phielim and copyelim` refines its input on `runL`

`copyelim_refinesL`: `copyelim_rel` (the pass establishes `CopyRel`) and `refinesL_of_rel` (the
relation gives refinement under `runL`), for an input and output that pass `check`, with the
input in Phase 1's fragments `CopyFrag` and `EmptyFrag`, input and output lowered alike
(`Func.lowered`, so `runL` runs both in one mode) and the pair in `CopyLFrag` (kept block
`auxInt`s, `MOVDreg`/`MOVDnop` sign extensions and, in lowered code, copies of their argument's
lowered shape; decided by `copyLFragB`, `copyLFrag_of`). `copyelimPass` is the pass of
`late phielim and copyelim` (and of `early phielim and copyelim`).
-/

namespace GoFV.Proof.CopyElim

open GoFV.SSA GoFV.Opt Dom

/-- **copyelim refines its input on `runL`.** -/
theorem copyelim_refinesL {penv : PassEnv} {f : Func} {out : PassOut} {ce ce' : CheckEnv}
    (h : copyelimPass penv f = .ok out) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ()) (hcf : CopyFrag penv.tables f)
    (hsf : EmptyFrag penv.tables f) (hlow : out.func.lowered = f.lowered)
    (hL : CopyLFrag penv.tables f out.func) : RefinesL out.tables out.func penv.tables f := by
  simp only [copyelimPass, Pass.ofFunc, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i g hcp
    cases h
    exact refinesL_of_rel
      { wf := ⟨ce, check_wf hf⟩, wg := ⟨ce', check_wf hg⟩,
        cf := certOK_of_check (check_domCert hf), cg := certOK_of_check (check_domCert hg),
        rel := copyelim_rel hf hcf hcp, frag := hsf } hlow hL

end GoFV.Proof.CopyElim
