import GoFV.Proof.Pass.FuseLoop
import GoFV.Proof.Pass.FuseCmp
import GoFV.Proof.Pass.FusePlain
import GoFV.Opt.Fuse

/-!
# early fuse refines its input

`fuseEarly_refines`: the output of `fuseEarlyPass` refines its input. The pass runs the slim
input check `wfDomCheck` once (`Dom.WFDom.of_wfDomCheck`; a failing input is returned
unchanged) and then the fuse driver with the early per-block step, whose four rewrites are each
checked: three comparison fusions
(`fuseComparisonsChecked_refines`) and plain fusion (`fuseBlockPlainChecked_refines`), each
keeping `WFDom` (`earlyStep_ok`). The driver keeps refinement and `WFDom` for any such step
(`Fuse.fuseLoop_refines`).
-/

namespace GoFV.Proof.FuseEarly

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.Fuse GoFV.Proof Dom

/-- **The early fuse step is a checked step.** -/
theorem earlyStep_ok {ce : CheckEnv} (isMem : TypeRef → Bool) :
    Fuse.StepOK ce (earlyStep isMem) := by
  intro tabs f b g ch h hf
  unfold earlyStep at h
  have k1 := FuseCmp.fuseComparisonsChecked_refines (tabs := tabs) (isMem := isMem)
    (canOpt := canOptIntInRange) (b := b) hf
  generalize Cmp.fuseComparisonsChecked isMem canOptIntInRange f b = r1 at h k1
  obtain ⟨f1, c1⟩ := r1
  dsimp only at h k1
  have k2 := FuseCmp.fuseComparisonsChecked_refines (tabs := tabs) (isMem := isMem)
    (canOpt := canOptSingleBitDifference) (b := b) k1.2
  generalize Cmp.fuseComparisonsChecked isMem canOptSingleBitDifference f1 b = r2 at h k2
  obtain ⟨f2, c2⟩ := r2
  dsimp only at h k2
  have k3 := FuseCmp.fuseComparisonsChecked_refines (tabs := tabs) (isMem := isMem)
    (canOpt := canOptNanCheck) (b := b) k2.2
  generalize Cmp.fuseComparisonsChecked isMem canOptNanCheck f2 b = r3 at h k3
  obtain ⟨f3, c3⟩ := r3
  dsimp only at h k3
  simp only [bind, Except.bind] at h
  cases h4 : Plain.fuseBlockPlainChecked f3 b with
  | error e => rw [h4] at h; cases h
  | ok r4 =>
    rw [h4] at h
    obtain ⟨f4, c4⟩ := r4
    have k4 := FusePlain.fuseBlockPlainChecked_refines (tabs := tabs) h4 k3.2
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact ⟨k1.1.trans (k2.1.trans (k3.1.trans k4.1)), k4.2⟩

/-- **early fuse refines its input.** -/
theorem fuseEarly_refines {penv : PassEnv} {f : Func} {out : PassOut}
    (h : fuseEarlyPass penv f = .ok out) :
    Refines out.tables out.func penv.tables f := by
  simp only [fuseEarlyPass, Pass.ofFunc, bind, Except.bind, pure, Except.pure] at h
  cases htv : typeView penv with
  | error e => rw [htv] at h; cases h
  | ok tv =>
    rw [htv] at h
    simp only at h
    cases hg : fuseEarly tv f with
    | error e => rw [hg] at h; cases h
    | ok g =>
      rw [hg] at h
      cases h
      unfold fuseEarly at hg
      split at hg
      · cases hg; exact Refines.refl _ _
      · rename_i hck
        have hck' : wfDomOK f = true := by
          simpa using hck
        unfold orInput at hg
        split at hg
        · rename_i g' hl
          cases hg
          exact (Fuse.fuseLoop_refines (earlyStep_ok tv.isMem) Fuse.finalOK_none hl
            (WFDom.of_wfDomCheck (ce := { tabs := penv.tables, typs := penv.typs })
              (wfDomOK_sound hck'))).1
        · cases hg; exact Refines.refl _ _

end GoFV.Proof.FuseEarly
