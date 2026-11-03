import GoFV.SSA.Sem.RunL
import GoFV.Proof.Witness.Early

/-!
# Non-vacuity witness: `runL_generic` on `clamp`

`clamp` has no arm64 op and no arm64 block kind (`Func.lowered`, by kernel evaluation), so
`runL_generic` applies: `runL` returns `clamp(5, 0, 10) = 5`, as `run` does (`clamp_run5`).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem

theorem clamp_not_lowered : clamp.lowered = false := by decide +kernel

theorem runL_generic_witness :
    ∃ m, runL Env.p1 clampTabs clamp (clampArgs 5) {} 3 = .returned [.i64 5] m := by
  obtain ⟨m, hm⟩ := clamp_run5
  exact ⟨m, by rw [runL_generic _ _ clamp_not_lowered]; exact hm⟩

end GoFV.Proof.Witness
