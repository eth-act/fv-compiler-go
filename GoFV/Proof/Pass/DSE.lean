import GoFV.Proof.Pass.DSESim

/-!
# dse refines its input

`dse` turns a `Store`/`Zero`/`Move` whose bytes later stores of its block overwrite before any
read into `Copy mem`. On an input in `dseFrag` (dse fails, or the checker `DSE.drel` accepts its
result: every eliminated store's bytes are in pending ranges along the memory chain until kept
stores overwrite them, and nothing else reads that chain), the result is related to the input by
`DRel` (`drel_sound`), and `DRel` gives refinement: lock-step simulation with frames agreeing on
every value without pending ranges at block entries, the memories along a chain equal outside
its pending bytes (`refines_of_rel`).
-/

namespace GoFV.Proof.DSE

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.SSA.DomCert Dom

/-- **dse refines its input** (on inputs in `dseFrag`). -/
theorem dse_refines {penv : PassEnv} {f : Func} {out : PassOut} {ce ce' : CheckEnv}
    (h : dsePass penv f = .ok out) (hf : check ce f = .ok ()) (hg : check ce' out.func = .ok ())
    (hfrag : dseFrag penv f = true) : Refines out.tables out.func penv.tables f := by
  unfold dseFrag at hfrag
  simp only [dsePass, Pass.ofFunc, bind, Except.bind, pure, Except.pure] at h
  cases hm : penv.typ? "Mem" with
  | none => rw [hm] at h; cases h
  | some mem =>
    rw [hm] at h hfrag
    simp only at h hfrag
    cases hd : dse penv.tables mem f with
    | error e => rw [hd] at h; cases h
    | ok g =>
      rw [hd] at h hfrag
      simp only at h hfrag
      cases h
      exact refines_of_rel ⟨ce, check_wf hf⟩ (certOK_of_check (check_domCert hf))
        (drel_sound hfrag)

end GoFV.Proof.DSE
