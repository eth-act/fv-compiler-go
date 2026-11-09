import GoFV.Proof.Pass.FuseLoop
import GoFV.Proof.Pass.FusePlain
import GoFV.Proof.Pass.ShortCircCpa
import GoFV.Proof.Pass.ShortCircSim
import GoFV.Opt.ShortCircuit

variable [GoFV.SSA.Sem.Addrs]

/-!
# short circuit refines its input

`shortcircuit_refines`: the output of `shortcircuitPass` refines its input. The pass runs the
slim input check `wfDomCheck` once (a failing input is returned unchanged), the checked
`constPhiArgs` (`constPhiArgsChecked_refines`, which needs the dominator certificate the check
validates), then the fuse driver with the short circuit per-block step: checked plain fusion
(`fuseBlockPlainChecked_refines`) and the checked `shortcircuitBlock`
(`shortcircuitBlockChecked_refines`), each keeping `WFDom` (`step_ok`). The step's checker reads
the tables, so the driver lemma is `Fuse.fuseLoop_refinesAt`.
-/

namespace GoFV.Proof.ShortCirc

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.ShortCircuit GoFV.Opt.Fuse GoFV.Proof Dom

/-- **The short circuit step is a checked step** (at the tables its checker reads). -/
theorem step_ok {ce : CheckEnv} (tabs : Tables) : Fuse.StepOKAt ce tabs (step tabs) := by
  intro f b g ch h hf
  unfold step at h
  simp only [bind, Except.bind] at h
  cases h1 : Plain.fuseBlockPlainChecked f b with
  | error e => rw [h1] at h; cases h
  | ok r1 =>
    rw [h1] at h
    obtain ⟨f1, c1⟩ := r1
    have k1 := FusePlain.fuseBlockPlainChecked_refines (tabs := tabs) h1 hf
    simp only at h
    cases h2 : shortcircuitBlockChecked tabs f1 b with
    | mk f2 c2 =>
      have k2 := shortcircuitBlockChecked_refines h2 k1.2
      rw [h2] at h
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      exact ⟨k1.1.trans k2.1, k2.2⟩

/-- **short circuit refines its input.** -/
theorem shortcircuit_refines {penv : PassEnv} {f : Func} {out : PassOut}
    (h : shortcircuitPass penv f = .ok out) : Refines out.tables out.func penv.tables f := by
  simp only [shortcircuitPass, Pass.ofFunc, bind, Except.bind, pure, Except.pure] at h
  cases hb : penv.typ? "Bool" with
  | none => rw [hb] at h; cases h
  | some boolT =>
    rw [hb] at h
    simp only at h
    generalize hs : ShortCircuit.shortcircuit { tabs := penv.tables, typs := penv.typs }
      (fun t => (penv.type? t).map (·.kind) == some .BOOL) penv.typeOrder.eq boolT f = r at h
    cases r with
    | error e => cases h
    | ok g =>
      cases h
      unfold ShortCircuit.shortcircuit at hs
      split at hs
      · cases hs; exact Refines.refl _ _
      · rename_i hck
        have hck' : wfDomOK f = true := by simpa using hck
        have hwd := wfDomOK_sound hck'
        unfold orInput at hs
        split at hs
        · rename_i g' hl
          cases hs
          simp only [bind, Except.bind] at hl
          split at hl
          · cases hl
          · rename_i f1 hc
            have k1 := constPhiArgsChecked_refines
              (ce := { tabs := penv.tables, typs := penv.typs }) hc hwd
            exact k1.1.trans (Fuse.fuseLoop_refinesAt (step_ok _)
              ((Fuse.finalOK_none).at _) hl k1.2).1
        · cases hs; exact Refines.refl _ _

end GoFV.Proof.ShortCirc
