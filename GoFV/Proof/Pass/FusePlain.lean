import GoFV.Proof.Pass.FusePlainSim
import GoFV.Proof.Checked

/-!
# The checked `fuseBlockPlain` step refines its input

`fuseBlockPlainChecked_refines`: if `f` is well formed with its uses dominated on paths
(`Dom.WFDom`, a consequence of `check`), the result of the checked plain fusion step
(`Fuse.Plain.fuseBlockPlainChecked`, shared by early fuse, late fuse and short circuit) refines
`f` and keeps `WFDom` (`PRel.wf_pres`, `PRel.useDom_pres`). An accepted rewrite is one `Setup`
(`stepOK`: the result fuses the run `plainRun f b`), refined by `refines_of_step`; a rejected
one leaves `f`.
-/

namespace GoFV.Proof.FusePlain

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.Fuse GoFV.Opt.Fuse.Plain GoFV.Proof Dom

theorem stepOK_sound {ce : CheckEnv} {f g : Func} {b : ID} (hwf : WF ce f)
    (h : stepOK f g b = true) : ∃ run b0 c, PRel f g run b0 c := by
  unfold stepOK at h
  split at h
  · rename_i run _
    obtain ⟨b0, c, hr⟩ := relB_sound hwf h
    exact ⟨run, b0, c, hr⟩
  · cases h

/-- **The checked plain fusion step refines its input** and keeps `WFDom` (well-formedness
and use dominance), so the passes need not `check` the result. -/
theorem fuseBlockPlainChecked_refines {tabs : Tables} {ce : CheckEnv} {f : Func} {b : ID}
    (hf : WFDom ce f) :
    Refines tabs (fuseBlockPlainChecked f b).1 tabs f ∧ WFDom ce (fuseBlockPlainChecked f b).1 := by
  unfold fuseBlockPlainChecked
  split
  rename_i g ch _
  split
  · rename_i hok
    rw [Bool.and_eq_true] at hok
    obtain ⟨run, b0, c, hrel⟩ := stepOK_sound hf.wf hok.2
    have hwg := hrel.wf_pres hf.wf
    have S : Setup f g run b0 c := ⟨⟨ce, hf.wf⟩, ⟨ce, hwg⟩, hf.dom, hrel⟩
    exact ⟨S.refines_of_step, hwg, hrel.useDom_pres hf.wf hf.dom⟩
  · exact ⟨Refines.refl _ _, hf⟩

end GoFV.Proof.FusePlain
