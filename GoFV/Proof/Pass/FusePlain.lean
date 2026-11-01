import GoFV.Proof.Pass.FusePlainSim
import GoFV.Proof.Checked

/-!
# The checked `fuseBlockPlain` step refines its input

`fuseBlockPlainChecked_refines`: if `f` passes `check`, the result of the checked plain
fusion step (`Fuse.Plain.fuseBlockPlainChecked`, shared by early fuse, late fuse and short
circuit) refines `f` and passes `check`. An accepted rewrite is one `Setup` (`stepOK`: the
result passes `check` and fuses the run `plainRun f b`), refined by `refines_of_step`; a
rejected one leaves `f`.
-/

namespace GoFV.Proof.FusePlain

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.Fuse GoFV.Opt.Fuse.Plain GoFV.Proof

theorem relB_sound {f g : Func} {run : List ID} (h : relB f g run = true) :
    ∃ b0 c, PRel f g run b0 c := by
  unfold relB at h
  split at h
  · rename_i b0 c hb0 hc
    exact ⟨b0, c, ⟨hb0, hc, by unfold relB; rw [hb0, hc]; exact h⟩⟩
  · cases h

theorem stepOK_sound {ce : CheckEnv} {f g : Func} {b : ID} (h : stepOK ce f g b = true) :
    check ce g = .ok () ∧ ∃ run b0 c, PRel f g run b0 c := by
  unfold stepOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨checkOK_sound h1, ?_⟩
  split at h2
  · rename_i run _
    obtain ⟨b0, c, hr⟩ := relB_sound h2
    exact ⟨run, b0, c, hr⟩
  · cases h2

/-- **The checked plain fusion step refines its input** and keeps `check`. -/
theorem fuseBlockPlainChecked_refines {tabs : Tables} {ce : CheckEnv} {f : Func} {b : ID}
    (hf : check ce f = .ok ()) :
    Refines tabs (fuseBlockPlainChecked ce f b).1 tabs f ∧
      check ce (fuseBlockPlainChecked ce f b).1 = .ok () := by
  unfold fuseBlockPlainChecked
  split
  rename_i g ch _
  split
  · rename_i hok
    rw [Bool.and_eq_true] at hok
    obtain ⟨hcg, run, b0, c, hrel⟩ := stepOK_sound hok.2
    have S : Setup f g run b0 c := ⟨⟨ce, check_wf hf⟩, ⟨ce, check_wf hcg⟩,
      Dom.certOK_of_check (check_domCert hf), hrel⟩
    exact ⟨S.refines_of_step, hcg⟩
  · exact ⟨Refines.refl _ _, hf⟩

end GoFV.Proof.FusePlain
