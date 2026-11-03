import GoFV.Proof.Pass.SchedLPass
import GoFV.Proof.Witness.SchedL
import GoFV.Proof.Witness.LowCong
import GoFV.Proof.Witness.DeadcodeL
import GoFV.Proof.Witness.Util
import GoFV.Proof.RunLFCases

/-!
# Non-vacuity witness: `schedule` on lowered `clamp`

`schedule` (`GoFV.Opt.schedulePass`) runs on `clampL` (by kernel evaluation): it lists `b1`'s
values in Go's order `v8 v9 v10 v1 v22` (`clampS`'s blocks, section 53 of the corpus), and
`scheduleCheck` accepts the output. By `schedule_refinesSchedLF` the output's `runSched` returns
`clamp(5, 0, 10) = 5`, as `runLF` of `clampL` does (`clampL_runLF`). `clampL` has no memory
op and no nil check, so `runLF` is `runL` on it (`noNilFault_of_noAct`) and
`schedule_refinesSchedL` reads the same off `runL` (`clampL_run5`).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof GoFV.Proof.SchedL

/-- A pass environment for `schedule` on lowered `clamp` (`optimize 1`; the SSA pseudo-types). -/
def clampSchedPassEnv : PassEnv :=
  { clampLPassEnv "schedule" with
    config := #[("arch", #[.word "arm64"]), ("hasgreg", #[.word "1"]), ("optimize", #[.word "1"])]
    typs := #[("Mem", 28), ("Flags", 29), ("Void", 0)] }

theorem clampL_check : (check clampLCheckEnv clampL).toBool = true := by decide +kernel

/-- `schedule` accepts `clampL`, its output has `clampS`'s blocks and `scheduleCheck` holds. -/
theorem clampL_schedule_facts :
    ((schedulePass clampSchedPassEnv clampL).toOption.map fun o =>
      decide (scheduleCheck clampLTabs clampL o.func = true ∧ o.func.blockTab = clampSBlocks)) =
      some true := by
  decide +kernel

/-- **`schedule_refinesSchedLF` is not vacuous**: `schedule` accepts `clampL`, `scheduleCheck`
accepts its output, and the output's `runSched` returns `clamp(5, 0, 10) = 5`. -/
theorem schedule_witness :
    ∃ out, schedulePass clampSchedPassEnv clampL = .ok out ∧
      scheduleCheck clampLTabs clampL out.func = true ∧ out.func.blockTab = clampSBlocks ∧
      ∃ fuel m, runSched Env.p1 out.tables out.func (clampArgs 5) {} fuel = .returned [.i64 5] m := by
  obtain ⟨out, hp, hv, hb⟩ := ok_of_toOption
    (P := fun o => scheduleCheck clampLTabs clampL o.func = true ∧ o.func.blockTab = clampSBlocks)
    clampL_schedule_facts
  refine ⟨out, hp, hv, hb, ?_⟩
  obtain ⟨m, hm⟩ := returnsInt_iff.1 clampL_runLF.1
  exact (schedule_refinesSchedLF (penv := clampSchedPassEnv) hp (ok_of_toBool clampL_check) hv).returned_int hm

/-- `clampL` has no value evaluated by `arm64Op`. -/
theorem clampL_noAct :
    clampL.valueTab.all (fun o => o.all fun v => !ScheduleCheck.actOp v.op) = true := by
  decide +kernel

/-- **`schedule_refinesSchedL` is not vacuous**: on `clampL`'s inputs (no nil-page access), the
output's `runSched` returns `runL`'s `clamp(5, 0, 10) = 5`. -/
theorem schedule_refinesSchedL_witness :
    ∃ out, schedulePass clampSchedPassEnv clampL = .ok out ∧
      ∃ fuel m, runSched Env.p1 out.tables out.func (clampArgs 5) {} fuel = .returned [.i64 5] m := by
  obtain ⟨out, hp, hv, -⟩ := ok_of_toOption
    (P := fun o => scheduleCheck clampLTabs clampL o.func = true ∧ o.func.blockTab = clampSBlocks)
    clampL_schedule_facts
  refine ⟨out, hp, ?_⟩
  obtain ⟨m, hm⟩ := clampL_run5
  obtain ⟨fuel', ho⟩ := schedule_refinesSchedL (penv := clampSchedPassEnv) hp
    (ok_of_toBool clampL_check) hv Env.p1 (clampArgs 5) {}
    (noNilFault_of_noAct clampL_noAct Env.p1 (clampArgs 5) {}) 3
    (by show (runL Env.p1 clampLTabs clampL (clampArgs 5) {} 3).Defined; rw [hm]; trivial)
  change OutcomeRefines 0 (runL Env.p1 clampLTabs clampL (clampArgs 5) {} 3) _ at ho
  rw [hm] at ho
  refine ⟨fuel', ?_⟩
  generalize runSched Env.p1 out.tables out.func (clampArgs 5) {} fuel' = o at ho ⊢
  cases ho with
  | @returned _ _ _ m' hl _ =>
    cases hl with
    | cons h1 t =>
      cases t
      cases h1
      exact ⟨m', rfl⟩

end GoFV.Proof.Witness
