import GoFV.Proof.Pass.NumberLines
import GoFV.Proof.Pass.Identity
import GoFV.Proof.Witness.Clamp

/-!
# Non-vacuity witnesses: `number lines`, `check bce`, `softfloat` on `clamp`

Each pass accepts `clamp` (the `.ok` hypothesis of its theorem is satisfiable) and its theorem
then shows that the pass's output returns `clamp(5, 0, 10) = 5`, as the source does.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof

/-- A pass environment for `clamp`'s section 0 (configuration: `softfloat 0`). -/
def clampPassEnv (passName : String) : PassEnv where
  passName := passName
  pkg := GoStr.ofString "main"
  funcName := GoStr.ofString "clamp"
  abi := 1
  nosplit := false
  pgohot := false
  config := #[("softfloat", #[.word "0"])]
  typs := #[]
  typeOrder := default
  tables := clampTabs

theorem clamp_run5 : ∃ m, run Env.p1 clampTabs clamp (clampArgs 5) {} 3 = .returned [.i64 5] m :=
  returnsInt_iff.1 clamp_run.1

theorem numberLines_witness : ∃ out, numberLinesPass (clampPassEnv "number lines") clamp = .ok out ∧
    ∃ fuel m, run Env.p1 out.tables out.func (clampArgs 5) {} fuel = .returned [.i64 5] m := by
  obtain ⟨m, hm⟩ := clamp_run5
  refine ⟨_, rfl, ?_⟩
  obtain ⟨fuel, h⟩ := Refines.returned_int
    (numberLines_refines (penv := clampPassEnv "number lines") (f := clamp) rfl) hm
  exact ⟨fuel, m, h⟩

theorem checkbce_witness : ∃ out, checkbcePass (clampPassEnv "check bce") clamp = .ok out ∧
    ∃ fuel m, run Env.p1 out.tables out.func (clampArgs 5) {} fuel = .returned [.i64 5] m := by
  obtain ⟨m, hm⟩ := clamp_run5
  refine ⟨_, rfl, ?_⟩
  obtain ⟨fuel, h⟩ := Refines.returned_int
    (checkbce_refines (penv := clampPassEnv "check bce") (f := clamp) rfl) hm
  exact ⟨fuel, m, h⟩

theorem softfloat_witness : ∃ out, softfloatPass (clampPassEnv "softfloat") clamp = .ok out ∧
    ∃ fuel m, run Env.p1 out.tables out.func (clampArgs 5) {} fuel = .returned [.i64 5] m := by
  obtain ⟨m, hm⟩ := clamp_run5
  refine ⟨_, rfl, ?_⟩
  obtain ⟨fuel, h⟩ := Refines.returned_int
    (softfloat_refines (penv := clampPassEnv "softfloat") (f := clamp) rfl) hm
  exact ⟨fuel, m, h⟩

end GoFV.Proof.Witness
