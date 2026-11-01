import GoFV.Proof.Pass.FusePlainSim
import GoFV.Proof.Checked

/-!
# The checked `fuseBlockPlain` step refines its input

`fuseBlockPlainChecked_refines`: if `f` is well formed with its uses dominated on paths
(`Dom.WFDom`, a consequence of `check`), a result of the checked plain fusion step
(`Fuse.Plain.fuseBlockPlainChecked`, shared by early fuse, late fuse and short circuit) refines
`f` and keeps `WFDom` (`PRel.wf_pres`, `PRel.useDom_pres`). An accepted rewrite is one `Setup`
(`checked_sound`: the result fuses the run of the snapshot), refined by `refines_of_step`; a
skipped one leaves `f`; a rejected one is an error.
-/

namespace GoFV.Proof.FusePlain

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.Fuse GoFV.Opt.Fuse.Plain GoFV.Proof Dom

/-- **The checked plain fusion step refines its input** and keeps `WFDom` (well-formedness
and use dominance), so the passes need not `check` the result. -/
theorem fuseBlockPlainChecked_refines {tabs : Tables} {ce : CheckEnv} {f g : Func} {b : ID}
    {ch : Bool} (h : fuseBlockPlainChecked f b = .ok (g, ch)) (hf : WFDom ce f) :
    Refines tabs g tabs f ∧ WFDom ce g := by
  unfold fuseBlockPlainChecked at h
  split at h
  · cases h; exact ⟨Refines.refl _ _, hf⟩
  rename_i s hs
  rcases hfb : fuseBlockPlain f b with ⟨g', ch'⟩
  simp only [hfb] at h
  split at h
  · rename_i hok
    cases h
    rw [Bool.and_eq_true] at hok
    have hrel := checked_sound hf.wf hs (by rw [hfb]; exact hok.2)
    rw [hfb] at hrel
    have hwg := hrel.wf_pres hf.wf
    have S : Setup f g s.run s.b0 s.c := ⟨⟨ce, hf.wf⟩, ⟨ce, hwg⟩, hf.dom, hrel⟩
    exact ⟨S.refines_of_step, hwg, hrel.useDom_pres hf.wf hf.dom⟩
  · cases h

end GoFV.Proof.FusePlain
