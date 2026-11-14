import GoFV.Proof.Pass.SchedLSim
import GoFV.Opt.Schedule

variable [GoFV.SSA.Sem.Addrs]

/-!
# `schedule` refines its input (`schedule_refinesSchedLF`, issue #385)

The `schedule` pass (`GoFV.Opt.schedulePass`) on an input that passes `check`, with its output
accepted by the validator `scheduleCheck` (`GoFV/Opt/ScheduleCheck.lean`): every returning or
panicking `runLF` of the input (`runL` with memory ops faulting on the nil page, as under
`runSched`) whose pointer-shaped parameter pieces read nil or pointers that are not wild
(`ArgPtrsOK`), whose checked pointer-shaped values do as well (`NilPtrsOK`) and whose checked
pointers that the output hoists above a fault do as well (`NilHoistOK`, trivial when the output
needs no such swap, `nilHoistOK_of_noHoist`), all Go-level assumptions, is matched by a
`runSched` of the output (`refinesSchedLF_of_rel`). On the inputs where `runLF` and `runL` agree
as well (`NoNilFault`: no run of the input accesses the nil page) this is a refinement of `runL`
(`schedule_refinesSchedL`).
-/

namespace GoFV.Proof.SchedL

open GoFV.SSA GoFV.Opt GoFV.Proof Dom

/-- **`schedule` refines its input** (`runSched` of the output against `runLF` of the input),
for a checked input and an output that `scheduleCheck` accepts, on the inputs whose
pointer-shaped parameter pieces (`ArgPtrsOK`), checked pointer-shaped values (`NilPtrsOK`) and
hoisted checked pointers (`NilHoistOK`) read nil or pointers that are not wild. -/
theorem schedule_refinesSchedLF {penv : PassEnv} {f : Func} {out : PassOut} {ce : CheckEnv}
    (h : schedulePass penv f = .ok out) (hf : check ce f = .ok ())
    (hv : scheduleCheck penv.tables f out.func = true) :
    RefinesSchedLFFrom (fun env args mem => ArgPtrsOK penv.tables f env args mem ∧
      NilPtrsOK penv.tables f env args mem ∧ NilHoistOK penv.tables f out.func env args mem)
      out.tables out.func penv.tables f := by
  have ht : out.tables = penv.tables := by
    simp only [schedulePass, Pass.ofFunc, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · cases h; rfl
  rw [ht]
  exact refinesSchedLF_of_rel ⟨⟨ce, check_wf hf⟩, certOK_of_check (check_domCert hf),
    schedRel_of_check hv⟩

/-- **`schedule` refines its input under `runL`** on the inputs without nil-page accesses whose
pointer-shaped parameter pieces, checked pointer-shaped values and hoisted checked pointers read
nil or pointers that are not wild. -/
theorem schedule_refinesSchedL {penv : PassEnv} {f : Func} {out : PassOut} {ce : CheckEnv}
    (h : schedulePass penv f = .ok out) (hf : check ce f = .ok ())
    (hv : scheduleCheck penv.tables f out.func = true) :
    RefinesSchedLFrom
      (fun env args mem => NoNilFault penv.tables f env args mem ∧
        ArgPtrsOK penv.tables f env args mem ∧ NilPtrsOK penv.tables f env args mem ∧
        NilHoistOK penv.tables f out.func env args mem)
      out.tables out.func penv.tables f :=
  (schedule_refinesSchedLF h hf hv).schedL.mono fun _ _ _ h => ⟨⟨h.2.1, h.2.2⟩, h.1⟩

end GoFV.Proof.SchedL
