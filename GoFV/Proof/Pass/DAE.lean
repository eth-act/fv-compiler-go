import GoFV.Proof.Pass.DAESim
import GoFV.Proof.CheckFacts
import GoFV.Proof.DomCert

/-!
# dead auto elim refines its input

`dead auto elim` turns writes (`Store`/`Zero`/`Move`/`VarDef`) to frame variables whose address
is used for nothing else into `Copy mem`. On an input in `daeFrag` (the pass fails, or the
checker `DAE.arel` accepts its result: every eliminated variable is a frame temporary
`Blk.temp`, its address flows only into eliminated writes and pointer arithmetic on it, and the
kept values with memory- or pointer-shaped operands or results have ops the proof covers), the
result is related to the input by `ARelD` (`arel_sound`), and `ARelD` gives refinement for
environments whose contracts are frame-safe and inputs holding no pointer into a frame
temporary (`refines_of_rel`): lock-step simulation in which the memories differ only in the
eliminated temporaries, which nothing reads, and which the frame removal at the end drops.
-/

namespace GoFV.Proof.DAE

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.SSA.DomCert Dom

/-- **dead auto elim refines its input** (on inputs in `daeFrag`, for frame-safe environments
and inputs that hold no pointer into a frame temporary). -/
theorem dead_auto_elim_refines {penv : PassEnv} {f : Func} {out : PassOut}
    {ce ce' : CheckEnv} (h : elimDeadAutosPass penv f = .ok out) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ()) (hfrag : daeFrag penv f = true) :
    RefinesFrom (fun env args mem => env.FrameSafe ∧ InitAvoids env args mem)
      out.tables out.func penv.tables f := by
  unfold daeFrag at hfrag
  simp only [elimDeadAutosPass, Pass.ofFunc, bind, Except.bind, pure, Except.pure] at h
  cases hm : penv.typ? "Mem" with
  | none => rw [hm] at h; cases h
  | some mem =>
    rw [hm] at h hfrag
    cases hfl : penv.typ? "Flags" with
    | none => rw [hfl] at h; cases h
    | some flags =>
      rw [hfl] at h hfrag
      simp only at h hfrag
      cases hd : elimDeadAutosGeneric penv.tables mem flags (penv.abi == 1) f with
      | error e => rw [hd] at h; cases h
      | ok g =>
        rw [hd] at h hfrag
        simp only at h hfrag
        cases h
        exact refines_of_rel (check_wf hf) (certOK_of_check (check_domCert hf))
          (arel_sound hfrag)

end GoFV.Proof.DAE
