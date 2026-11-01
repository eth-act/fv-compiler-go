import GoFV.Proof.Pass.FuseLoop
import GoFV.Proof.Pass.FuseIf
import GoFV.Proof.Pass.FusePlain
import GoFV.Proof.Pass.FuseRedirect
import GoFV.Opt.Fuse

/-!
# late fuse refines its input

`fuseLate_refines`: the output of `fuseLatePass` refines its input. The pass runs the slim input
check `wfDomCheck` once (`Dom.WFDom.of_wfDomCheck`; a failing input is returned unchanged) and
then the fuse driver with the late per-block step, whose two rewrites are each checked:
`fuseBlockIf` (`fuseBlockIfChecked_refines`) and plain fusion (`fuseBlockPlainChecked_refines`),
each keeping `WFDom` (`lateStep_ok`); after each sweep the checked branch redirect
(`FuseRedirect.fuseBranchRedirectChecked_ok`, at the pass's tables, which its decisions read).
The driver keeps refinement and `WFDom` (`Fuse.fuseLoop_refinesAt`).
-/

namespace GoFV.Proof.FuseLate

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.Fuse GoFV.Proof Dom

/-- **The late fuse step is a checked step.** -/
theorem lateStep_ok {ce : CheckEnv} (tv : TypeView) : Fuse.StepOK ce (lateStep ce tv) := by
  intro tabs f b g ch h hf
  unfold lateStep at h
  simp only [bind, Except.bind] at h
  cases h1 : fuseBlockIfChecked ce tv f b with
  | error e => rw [h1] at h; cases h
  | ok r1 =>
    rw [h1] at h
    obtain ⟨f1, c1⟩ := r1
    have k1 := FuseIf.fuseBlockIfChecked_refines (tabs := tabs) h1 hf
    simp only at h
    cases h2 : Plain.fuseBlockPlainChecked f1 b with
    | error e => rw [h2] at h; cases h
    | ok r2 =>
      rw [h2] at h
      obtain ⟨f2, c2⟩ := r2
      have k2 := FusePlain.fuseBlockPlainChecked_refines (tabs := tabs) h2 k1.2
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      exact ⟨k1.1.trans k2.1, k2.2⟩

/-- **late fuse refines its input.** -/
theorem fuseLate_refines {penv : PassEnv} {f : Func} {out : PassOut}
    (h : fuseLatePass penv f = .ok out) : Refines out.tables out.func penv.tables f := by
  simp only [fuseLatePass, Pass.ofFunc, bind, Except.bind, pure, Except.pure] at h
  cases htv : typeView penv with
  | error e => rw [htv] at h; cases h
  | ok tv =>
    rw [htv] at h
    simp only at h
    cases hpv : Prove.Prover.ofEnv penv with
    | error e => rw [hpv] at h; cases h
    | ok pv =>
      rw [hpv] at h
      simp only at h
      cases hg : fuseLate { tabs := penv.tables, typs := penv.typs } tv pv f with
      | error e => rw [hg] at h; cases h
      | ok g =>
        rw [hg] at h
        cases h
        unfold fuseLate at hg
        split at hg
        · cases hg; exact Refines.refl _ _
        · rename_i hck
          have hck' : wfDomOK f = true := by simpa using hck
          unfold orInput at hg
          split at hg
          · rename_i g' hl
            cases hg
            exact (Fuse.fuseLoop_refinesAt ((lateStep_ok tv).at _)
              (FuseRedirect.fuseBranchRedirectChecked_ok pv penv.tables) hl
              (WFDom.of_wfDomCheck (ce := { tabs := penv.tables, typs := penv.typs })
                (wfDomOK_sound hck'))).1
          · cases hg; exact Refines.refl _ _

end GoFV.Proof.FuseLate
