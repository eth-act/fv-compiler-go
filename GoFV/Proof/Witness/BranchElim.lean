import GoFV.Proof.Pass.BranchElimPass
import GoFV.Proof.Witness.Max3

/-!
# Non-vacuity witness: branchelim on `max3`

branchelim merges both if-triangles of `max3` (each rewrite accepted by the step checker; the
function becomes one `Ret` block, by kernel evaluation), so by `branchelim_refines` the output
returns `max3(1, 7, 4) = 7`, as the source does.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof GoFV.Proof.BranchElim

def max3PassEnv : PassEnv where
  passName := "branchelim"
  pkg := GoStr.ofString "main"
  funcName := GoStr.ofString "max3"
  abi := 1
  nosplit := false
  pgohot := false
  config := #[("arch", #[.word "arm64"]), ("regsize", #[.word "8"]),
    ("havecondselect", #[.word "1"])]
  typs := #[("Bool", 3), ("Int", 2), ("Uintptr", 15), ("Mem", 28), ("Void", 30)]
  typeOrder := default
  tables := max3Tabs

/-- branchelim turns `max3` into one `Ret` block whose two `Phi`s are `CondSelect`s. -/
theorem max3_branchelim :
    (match branchelimPass max3PassEnv max3 with
      | .ok out => decide ((out.func.block? 1).map (·.kind) = some .Ret) &&
          decide ((out.func.value? 15).map (·.op) = some .CondSelect) &&
          decide ((out.func.value? 18).map (·.op) = some .CondSelect)
      | .error _ => false) = true := by
  decide +kernel

theorem branchelim_witness :
    ∃ out, branchelimPass max3PassEnv max3 = .ok out ∧
      (out.func.block? 1).map (·.kind) = some .Ret ∧
      ∃ fuel m, run Env.p1 out.tables out.func max3Args {} fuel = .returned [.i64 7] m := by
  have h1 := max3_branchelim
  obtain ⟨m, hm⟩ := returnsInt_iff.1 max3_run
  cases hp : branchelimPass max3PassEnv max3 with
  | error e => rw [hp] at h1; cases h1
  | ok out =>
    rw [hp] at h1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    obtain ⟨fuel, h⟩ := Refines.returned_int (branchelim_refines hp) hm
    exact ⟨out, rfl, h1.1.1, fuel, m, h⟩

end GoFV.Proof.Witness
