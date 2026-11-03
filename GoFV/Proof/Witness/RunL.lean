import GoFV.SSA.Sem.RunL
import GoFV.Proof.Witness.Early

/-!
# Non-vacuity witness: `runL_generic` on `clamp`

`clamp` has no arm64 op and no arm64 block kind (`Func.lowered`, by kernel evaluation), so
`runL_generic` applies: `runL` returns `clamp(5, 0, 10) = 5`, as `run` does (`clamp_run5`).

`signExtendsIn_ldpsw_witness`: a `Select1` of an `LDPSW` holds a sign-extended register (the
`MOVDreg (Select1 (LDPSW …))` of `runtime.checkdead`), a `Select1` of an `LDPW` does not.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem

theorem clamp_not_lowered : clamp.lowered = false := by decide +kernel

theorem runL_generic_witness :
    ∃ m, runL Env.p1 clampTabs clamp (clampArgs 5) {} 3 = .returned [.i64 5] m := by
  obtain ⟨m, hm⟩ := clamp_run5
  exact ⟨m, by rw [runL_generic _ _ clamp_not_lowered]; exact hm⟩

theorem signExtendsIn_ldpsw_witness :
    let sel : Value := { (default : Value) with op := .Select1, args := #[1] }
    let pair (op : Op) : ID → Option Value := fun i =>
      if i = 1 then some { (default : Value) with op } else none
    Arm64.signExtendsIn (pair .ARM64LDPSW) sel = true ∧
      Arm64.signExtendsIn (pair .ARM64LDPW) sel = false := by
  decide

end GoFV.Proof.Witness
