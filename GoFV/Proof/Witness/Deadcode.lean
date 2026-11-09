import GoFV.Proof.Pass.DeadcodePass
import GoFV.Proof.Witness.NextPow2

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: deadcode on `nextPowerOfTwo`

`generic deadcode` accepts `nextPowerOfTwo` (section 26), removes a block (the `Exit` of the
`panicshift` call) and a value (the call), input and output pass `check`, and the input is in
`DeadFrag` (all by kernel evaluation), so `deadcode_refines` applies: the output returns
`nextPowerOfTwo(5) = 8`.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof GoFV.Proof.Dead

def np2CheckEnv : CheckEnv :=
  { tabs := np2Tabs, typs := #[("Bool", 4), ("Int", 2), ("Uintptr", 15), ("Mem", 28)] }

/-- A pass environment for `nextPowerOfTwo`'s section 26. -/
def np2PassEnv : PassEnv where
  passName := "generic deadcode"
  pkg := GoStr.ofString "slices"
  funcName := GoStr.ofString "nextPowerOfTwo"
  abi := 1
  nosplit := false
  pgohot := false
  config := #[]
  typs := #[]
  typeOrder := default
  tables := np2Tabs

/-- The number of values listed in the blocks of `f`. -/
def listedValues (f : Func) : Nat :=
  f.blocks.foldl (fun n b => n + (((f.block? b).map (·.values.size)).getD 0)) 0

theorem np2_checks :
    (check np2CheckEnv np2).toBool = true ∧
    ((deadcode np2Tabs np2).toOption.map fun g =>
      (check np2CheckEnv g).toBool && decide (g.blocks.size < np2.blocks.size) &&
        decide (listedValues g < listedValues np2)) = some true ∧
    deadFragB np2Tabs np2 = true := by
  decide +kernel

theorem deadcode_witness :
    ∃ out, deadcodePass np2PassEnv np2 = .ok out ∧ out.func.blocks.size < np2.blocks.size ∧
      listedValues out.func < listedValues np2 ∧
      ∃ fuel m, run Env.p1 out.tables out.func [.i64 5] {} fuel = .returned [.i64 8] m := by
  obtain ⟨h1, h2, h3⟩ := np2_checks
  obtain ⟨m, hm⟩ := returnsInt_iff.1 np2_run.1
  have hf : check np2CheckEnv np2 = .ok () := by
    revert h1; cases check np2CheckEnv np2 <;> simp [Except.toBool]
  cases hc : deadcode np2Tabs np2 with
  | error e => rw [hc] at h2; cases h2
  | ok g =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Bool.and_eq_true,
      decide_eq_true_eq] at h2
    obtain ⟨⟨hgc, hb⟩, hv⟩ := h2
    have hg : check np2CheckEnv g = .ok () := by
      revert hgc; cases check np2CheckEnv g <;> simp [Except.toBool]
    have hp : deadcodePass np2PassEnv np2 = .ok { func := g, tables := np2Tabs } := by
      simp only [deadcodePass, Pass.ofFunc, np2PassEnv]
      rw [hc]; rfl
    refine ⟨_, hp, hb, hv, ?_⟩
    obtain ⟨fuel, m', h⟩ := Refines.returned_int
      (deadcode_refines hp hf (ce' := np2CheckEnv) hg (deadFrag_of h3)) hm
    exact ⟨fuel, m', h⟩

end GoFV.Proof.Witness
