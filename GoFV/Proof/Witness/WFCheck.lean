import GoFV.Proof.DomRel
import GoFV.Proof.Checked
import GoFV.Proof.Witness.Max3

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: the slim input check on `max3`

`max3` (corpus section 22, two nested if-triangles with `Phi`s) passes `wfDomCheck` (kernel
evaluation, dominator certificate included), so `wfCheck_wf`, `wfDomCheck_wf`,
`wfDomCheck_domCert`, `WFDom.of_wfDomCheck` and `UseDom.of_cert` apply to it; a copy whose
entry has a predecessor is rejected.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.Opt GoFV.Proof

def max3WFCE : CheckEnv :=
  { tabs := max3Tabs, typs := #[("Bool", 3), ("Int", 2), ("Uintptr", 15), ("Mem", 28), ("Void", 30)] }

theorem max3_wfDomOK : wfDomOK max3 = true := by
  decide +kernel

/-- `v1` of `max3`'s entry block passes the per-value shape test. -/
theorem max3_valueOK :
    (match max3.block? 1, max3.value? 1 with
      | some b, some v => WFCheck.valueOK b v
      | _, _ => false) = true := by
  decide +kernel

/-- `max3` with a self-loop edge into its entry recorded as a predecessor only. -/
def max3EntryPred : Func :=
  let tab := max3.blockTab.modify max3.entry
    (Option.map fun b => { b with preds := b.preds.push ⟨max3.entry, 0⟩ })
  { max3 with blockTab := tab }

/-- The entry gets a predecessor: rejected. -/
theorem max3_entryPred_rejected : wfDomOK max3EntryPred = false := by
  decide +kernel

theorem max3_wfCheck_witness : WF max3WFCE max3 := by
  have h := wfDomOK_sound max3_wfDomOK
  unfold wfDomCheck at h
  obtain ⟨⟨⟩, h1, -⟩ := CheckFacts.bind_ok h
  exact wfCheck_wf h1

theorem max3_wfDomCheck_witness :
    WF max3WFCE max3 ∧ DomCert.check max3 = .ok () ∧ Dom.WFDom max3WFCE max3 ∧
      Dom.UseDom max3 :=
  have h := wfDomOK_sound max3_wfDomOK
  ⟨wfDomCheck_wf h, wfDomCheck_domCert h, Dom.WFDom.of_wfDomCheck h,
    Dom.UseDom.of_cert (ce := max3WFCE) (wfDomCheck_wf h)
      (Dom.certOK_of_check (wfDomCheck_domCert h))⟩

/-- `valueOK_spec` on `v1` of `max3`. -/
theorem max3_valueOK_spec_witness :
    ∃ b v, max3.block? 1 = some b ∧ max3.value? 1 = some v ∧ v.block = b.id ∧
      (v.op.argLen ≠ -1 → (v.args.size : Int) = v.op.argLen) := by
  have h := max3_valueOK
  split at h
  · rename_i b v hb hv
    have s := WFCheckFacts.valueOK_spec h
    exact ⟨b, v, hb, hv, s.2.2.1, s.1⟩
  · cases h

end GoFV.Proof.Witness
