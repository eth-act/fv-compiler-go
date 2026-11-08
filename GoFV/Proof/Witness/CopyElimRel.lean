import GoFV.Proof.Pass.CopyElimLoop
import GoFV.Proof.Witness.Clamp
import GoFV.Proof.Witness.Util

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: `copyelim_rel` on `clamp`

`clamp` (section 0, which has copies) passes `check`, satisfies `CopyFrag`, and copyelim
accepts it (all three evaluated by the kernel), so `copyelim_rel` applies.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.Opt GoFV.Proof GoFV.Proof.CopyElim

/-- The check environment of `clamp`'s section 0. -/
def clampCE : CheckEnv :=
  { tabs := clampTabs, typs := #[("Mem", 28), ("Uintptr", 15), ("Int", 2)] }

theorem clamp_check : check clampCE clamp = .ok () := by
  obtain ⟨⟨⟩, h⟩ := exists_ok_of_toBool (x := check clampCE clamp) (by decide +kernel)
  exact h

theorem clamp_copyFrag : CopyFrag clampTabs clamp := copyFrag_sound (by decide +kernel)

theorem copyelim_rel_witness :
    ∃ g, copyelim clampTabs clamp = .ok g ∧ CopyRel clampTabs clamp g := by
  obtain ⟨g, h⟩ := exists_ok_of_toBool (x := copyelim clampTabs clamp) (by decide +kernel)
  exact ⟨g, h, copyelim_rel clamp_check clamp_copyFrag h⟩

end GoFV.Proof.Witness
