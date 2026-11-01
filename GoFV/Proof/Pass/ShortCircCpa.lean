import GoFV.Proof.Pass.ShortCircCpaSim
import GoFV.Proof.Pass.ZCSE
import GoFV.Opt.ShortCircuit

/-!
# short circuit, step 1 (`constPhiArgs`), checked: refinement

`cpaOK_refines`: a result `g` that `cpaOK` accepts for an `f` passing the slim input check
(`wfDomCheck`: well formed, dominator certificate valid) refines `f` and is well formed with
uses dominated on paths (`WFDom`, the invariant of the fuse loop that follows). The
refinement goes through `mid f g`, `f` with the new constants added to its entry: `mid f g`
refines `f` by zcse's simulation (`ZCSE.refines_of_rel`, the relation `CRel.zrel_mid`), and `g`
runs like `mid f g` (`CRel.refines_mid`: the replaced `Phi` arguments read the constants the
controls hold on the incoming edges).
-/

namespace GoFV.Proof.ShortCirc

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.ShortCircuit GoFV.Proof Dom

/-- **A `constPhiArgs` result that `cpaOK` accepts refines its checked input and keeps
`WFDom`.** -/
theorem cpaOK_refines {tabs : Tables} {ce : CheckEnv} {f g : Func} (hf : wfDomCheck f = .ok ())
    (h : cpaOK tabs f g = true) : Refines tabs g tabs f ∧ WFDom ce g := by
  have C := cpaOK_sound h
  have hwf : WF ce f := wfDomCheck_wf hf
  have hc := certOK_of_check (wfDomCheck_domCert hf)
  obtain ⟨fE, news, E⟩ := C.ext_g
  obtain ⟨fE', news', E'⟩ := C.ext_mid
  have hmid : Refines tabs (mid f g) tabs f :=
    ZCSE.refines_of_rel (ZCSE.Setup.mk ⟨ce, hwf⟩ ⟨ce, E'.wf hwf⟩
      hc C.zrel_mid)
  exact ⟨hmid.trans (C.refines_mid hwf), E.wf hwf, E.useDom hwf (UseDom.of_cert hwf hc)⟩

/-- **Checked `constPhiArgs` refines its checked input and keeps `WFDom`.** -/
theorem constPhiArgsChecked_refines {tabs : Tables} {ce : CheckEnv} {isBool : TypeRef → Bool}
    {sameType : TypeRef → TypeRef → Bool} {boolT : TypeRef} {f g : Func}
    (h : constPhiArgsChecked tabs isBool sameType boolT f = .ok g) (hf : wfDomCheck f = .ok ()) :
    Refines tabs g tabs f ∧ WFDom ce g := by
  unfold constPhiArgsChecked at h
  dsimp only at h
  split at h
  · cases h; exact cpaOK_refines hf (by assumption)
  · cases h

end GoFV.Proof.ShortCirc
