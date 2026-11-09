import GoFV.Proof.Pass.FuseCmpSim
import GoFV.Proof.Pass.FuseCmpPres

variable [GoFV.SSA.Sem.Addrs]

/-!
# The checked `fuseComparisons` step refines its input

`fuseComparisonsChecked_refines`: if `f` is well formed with its uses dominated on paths
(`Dom.WFDom`, a consequence of `check`), the result of the checked comparison fusion step
(`Fuse.Cmp.fuseComparisonsChecked`, early fuse's `fuseIntInRange`, `fuseSingleBitDifference`
and `fuseNanCheck`) refines `f` and keeps `WFDom` (`Base.wf_pres`, `Base.useDom_pres`), for any
`canOpt` predicate and memory-type query: an accepted rewrite is one `Setup` (`stepOK`: `CRel`
at the rewrite's site), refined by `refines_of_step`; a rejected one leaves `f`.
-/

namespace GoFV.Proof.FuseCmp

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.Fuse GoFV.Opt.Fuse.Cmp GoFV.Proof Dom

theorem stepOK_sound {f g : Func} {b : ID} (h : stepOK f g b = true) : CRel f g (site f g b) :=
  ⟨rfl, h⟩

/-- **The checked comparison fusion step refines its input** and keeps `WFDom`
(well-formedness and use dominance), so the pass need not `check` the result. -/
theorem fuseComparisonsChecked_refines {tabs : Tables} {ce : CheckEnv} {isMem : TypeRef → Bool}
    {canOpt : Func → Value → Value → Op → Bool} {f : Func} {b : ID} (hf : WFDom ce f) :
    Refines tabs (fuseComparisonsChecked isMem canOpt f b).1 tabs f ∧
      WFDom ce (fuseComparisonsChecked isMem canOpt f b).1 := by
  unfold fuseComparisonsChecked
  split
  rename_i g ch _
  split
  · rename_i hok
    rw [Bool.and_eq_true] at hok
    have B : Base f g (site f g b) := ⟨⟨ce, hf.wf⟩, stepOK_sound hok.2⟩
    have hwg := B.wf_pres hf.wf
    have S : Setup f g (site f g b) := ⟨B, ⟨ce, hwg⟩, hf.dom⟩
    exact ⟨S.refines_of_step, hwg, B.useDom_pres hf.dom⟩
  · exact ⟨Refines.refl _ _, hf⟩

end GoFV.Proof.FuseCmp
