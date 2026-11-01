import GoFV.Proof.Pass.ECSim
import GoFV.Proof.Pass.ECStruct
import GoFV.Proof.Pass.ECObl
import GoFV.Proof.TabsAgree

/-!
# `expand calls` refines its input (issue #28)

`ecRel_of_check`: two checked functions accepted by the checker `ECCheck.ecCheck` are related by
the conversion simulation's `CvRel` with the conversion `ecCv`, the new values `isNewB f`, the
fronts `ecFront` and the return relation `ecRR`: per block the structural fields from `blockOK`
(`ecs_block`), the obligations by class (`eco_obl`, with the `IMake` facts `ecs_imk`), the `Ret`
relation of the `MakeResult` control (`ret_result`), and `finish` (`finish_ecRR`).

`expandCalls_refines`: on the fragment `expandCallsFrag` (the checker accepts the pass's output in
the output tables, and the input runs alike in the input and output tables, `tabsAgree`), the
output of `expandCallsPass` refines its input under monotone contracts.
-/

namespace GoFV.Proof.EC

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Opt GoFV.Opt.ECCheck GoFV.Proof.AtomSim
  GoFV.Proof.Order

/-- `valueOK` of a `MakeResult`: the target's node at its ID passes `resultOK`. -/
theorem ecm_valueOK_result {tabs : Tables} {f g : Func} {x : ID} {u : Value}
    (h : valueOK tabs (typeShapes tabs) f g x = true) (hu : f.value? x = some u)
    (hop : u.op = .MakeResult) :
    ∃ w, g.value? x = some w ∧ resultOK tabs (typeShapes tabs) f g u w = true := by
  unfold valueOK at h
  rw [hu] at h
  cases hw : g.value? x with
  | none => rw [hw] at h; cases h
  | some w =>
    rw [hw] at h
    have hc : (callOpMap u.op).isSome = false := by rw [hop]; rfl
    simp only [hc, hop, Bool.false_eq_true, ite_false, beq_self_eq_true, ite_true] at h
    exact ⟨w, rfl, h⟩

/-- **`ecCheck` gives the conversion simulation's relation.** -/
theorem ecRel_of_check {tabs : Tables} {f g : Func} {ce ce' : CheckEnv}
    (hf : check ce f = .ok ()) (hg : check ce' g = .ok ()) (hec : ecCheck tabs f g = true) :
    CvRel tabs f g (ecCv tabs f g) (isNewB f) (ecFront f g) (ecRR tabs f) := by
  obtain ⟨hcfg, hown, hreg, hblk⟩ := eco_ecCheck hec
  have hwf := check_wf hf
  have hwg := check_wf hg
  refine ⟨hcfg, hown, fun bid hbm fb hfb => ?_, finish_ecRR hreg⟩
  have hb := hblk bid hbm
  obtain ⟨gb, hgb, -⟩ := eco_blockOK hb hfb
  have hbg : bid ∈ g.blocks := by
    have hbl : (cfgView g).blocks = (cfgView f).blocks := congrArg Func.blocks hcfg
    have h : bid ∈ (cfgView f).blocks := hbm
    rw [← hbl] at h; exact h
  have himk := ecs_imk hwg hbg hfb hgb hb
  refine ⟨gb, hgb, ecs_block hwf hwg hcfg hbm hfb hgb hb
    (fun htree x hx u hu hphi => eco_obl hf hg hec hbm hfb hgb htree hx hu hphi
      (fun hcv => himk x hx hcv u hu)) ?_⟩
  intro hk c hc0
  obtain ⟨c', u, hc0', hu, hop⟩ := (ecs_parts hfb hgb hb).ret hk
  rw [hc0] at hc0'; cases hc0'
  obtain ⟨cbid, cb, ⟨hcbm, hcb⟩, hccb⟩ :=
    hwf.ctrlListed bid fb ⟨hbm, hfb⟩ c (Array.mem_of_getElem? hc0)
  have hphi : u.op ≠ .Phi := by rw [hop]; decide
  obtain ⟨-, -, -, hval, -⟩ := eco_blockOK (hblk cbid hcbm) hcb
  obtain ⟨w, hw, hok⟩ := ecm_valueOK_result (hval c hccb u hu hphi) hu hop
  exact ret_result hu hw hop hok hreg

/-- **`expand calls` refines its input** on the fragment `expandCallsFrag`. -/
theorem expandCalls_refines {penv : PassEnv} {f : Func} {out : PassOut} {ce ce' : CheckEnv}
    (h : expandCallsPass penv f = .ok out) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ()) (hfrag : expandCallsFrag penv f = true) :
    RefinesUnder Env.Mono out.tables out.func penv.tables f := by
  unfold expandCallsFrag at hfrag
  rw [h] at hfrag
  simp only [Bool.and_eq_true] at hfrag
  exact refinesUnder_of_tabsAgree hfrag.1 (cvSim_refines hf hg (ecRel_of_check hf hg hfrag.2))

end GoFV.Proof.EC
