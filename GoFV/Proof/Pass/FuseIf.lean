import GoFV.Proof.Pass.FuseIfSim

/-!
# The checked `fuseBlockIf` step refines its input

`fuseBlockIfChecked_refines`: if `f` is well formed with its uses dominated on paths
(`Dom.WFDom`), the result of the checked `fuseBlockIf` step (`Fuse.fuseBlockIfChecked`, late
fuse) refines `f` and keeps `WFDom`. An accepted rewrite is one `Setup` (`IfC.stepOK`: the
result is the rewrite at `siteOf tv f b` and passes `check`), refined by `refines_of_step`; a
rejected one leaves `f`.
-/

namespace GoFV.Proof.FuseIf

open GoFV.SSA GoFV.Opt GoFV.Opt.Fuse GoFV.Proof Dom

theorem stepOK_sound {ce : CheckEnv} {tv : TypeView} {f g : Func} {b : ID} (hf : WFDom ce f)
    (h : IfC.stepOK ce tv f g b = true) : ∃ s R, Setup ce f g s R := by
  unfold IfC.stepOK at h
  split at h
  · rename_i s _
    exact ⟨s, _, hf.wf, hf.dom, relB_sound h⟩
  · cases h

/-- **The checked `fuseBlockIf` step refines its input** and keeps `WFDom`. -/
theorem fuseBlockIfChecked_refines {tabs : Tables} {ce : CheckEnv} {tv : TypeView} {f g : Func}
    {b : ID} {ch : Bool} (h : fuseBlockIfChecked ce tv f b = .ok (g, ch)) (hf : WFDom ce f) :
    Refines tabs g tabs f ∧ WFDom ce g := by
  unfold fuseBlockIfChecked at h
  cases hfb : fuseBlockIf tv f b with
  | error e => rw [hfb] at h; cases h
  | ok p =>
    obtain ⟨g', ch'⟩ := p
    rw [hfb] at h
    simp only [bind, Except.bind] at h
    split at h
    · rename_i hok
      cases h
      rw [Bool.and_eq_true] at hok
      obtain ⟨s, R, S⟩ := stepOK_sound hf hok.2
      exact ⟨S.refines_of_step, WFDom.of_check S.rel.wg⟩
    · cases h
      exact ⟨Refines.refl _ _, hf⟩

end GoFV.Proof.FuseIf
