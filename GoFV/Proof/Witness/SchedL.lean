import GoFV.Proof.RefineSched
import GoFV.Proof.Witness.ClampRA

/-!
# Witnesses: refinement over `runSched` and `runLF`

On `clamp` after `flagalloc` (`clampS`, L1, `GoFV.Proof.Witness.ClampRA`) and before `schedule`
(`clampL`, L0): `runSched` and `runLF` return `clamp(5, 0, 10) = 5`, so `RefinesSched`,
`RefinesSchedLF` and their compositions are about defined runs (non-vacuity of the definitions
of `GoFV.Proof.RefineSched`).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof

/-- `runLF` (faulting `runL`) of the lowered `clamp` returns `clamp(5, 0, 10) = 5`,
`clamp(-3, 0, 10) = 0` and `clamp(12, 0, 10) = 10`, as `runL` does (`clampL_run`). -/
theorem clampL_runLF :
    returnsInt (runLF Env.p1 clampLTabs clampL (clampArgs 5) {} 3) 5 = true ∧
      returnsInt (runLF Env.p1 clampLTabs clampL (clampArgs (-3)) {} 3) 0 = true ∧
      returnsInt (runLF Env.p1 clampLTabs clampL (clampArgs 12) {} 3) 10 = true := by
  decide +kernel

/-- `RefinesSched.refl` on `clampS`, read off with `RefinesSched.returned_int`: a returning
target run. -/
theorem clampS_refinesSched_witness :
    ∃ fuel m, runSched Env.p1 clampLTabs clampS (clampArgs 5) {} fuel = .returned [.i64 5] m := by
  obtain ⟨m, h⟩ := returnsInt_iff.1 clampRA_run.1
  exact (RefinesSched.refl clampLTabs clampS).returned_int h

/-- `runLF_mono`/`runLF_det` on a defined run. -/
theorem clampL_runLF_det :
    runLF Env.p1 clampLTabs clampL (clampArgs 5) {} 7 =
      runLF Env.p1 clampLTabs clampL (clampArgs 5) {} 3 := by
  have hd : (runLF Env.p1 clampLTabs clampL (clampArgs 5) {} 3).Defined := by
    obtain ⟨m, h⟩ := returnsInt_iff.1 clampL_runLF.1
    rw [h]; trivial
  exact runLF_mono (by decide) hd

end GoFV.Proof.Witness
