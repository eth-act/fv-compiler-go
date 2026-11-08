import GoFV.Proof.Pass.DecPhiSim
import GoFV.Proof.Witness.FormatBool
import GoFV.Proof.Witness.Util

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: decompose's phi splitting on `strconv.FormatBool`

Decompose builtin's phi stage (`Decompose.phiStage … true`) turns `FormatBool`'s string `Phi`
`v11` into `StringMake` of two new `Phi`s over `StringPtr`/`StringLen` extractors
(`formatBoolOut`); decompose user's phi stage (`… false`) turns the struct variant `pair`'s
`Phi` `v11` into `StructMake` of two new `Phi`s over `StructSelect` extractors (`pairOut`).
Both outputs are checked against the stage in `GoFVTest/Proof/DecPhisStage.lean`. By kernel
evaluation: inputs and outputs pass `check` and `decPhiCheck` accepts them, so
`decPhis_refines` applies.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof

/-- What the witness needs of a pair of functions, as one `Bool`. -/
def decPhisOK (tabs : Tables) (f g : Func) (mk : Op) : Bool :=
  (check { tabs, typs := fbTyps } f).toBool && (check { tabs, typs := fbTyps } g).toBool &&
    DecPhiCheck.decPhiCheck tabs f g && (f.value? 11).map (·.op) == some .Phi &&
    (g.value? 11).map (·.op) == some mk

theorem formatBool_decPhisOK : decPhisOK formatBoolTabs formatBool formatBoolOut .StringMake = true := by
  decide +kernel

theorem pair_decPhisOK : decPhisOK pairTabs pair pairOut .StructMake = true := by
  decide +kernel

theorem decPhis_of_ok {tabs : Tables} {f g : Func} {mk : Op} (h : decPhisOK tabs f g mk = true) :
    (f.value? 11).map (·.op) = some .Phi ∧ (g.value? 11).map (·.op) = some mk ∧
      RefinesUnder Env.Mono tabs g tabs f := by
  unfold decPhisOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hcf, hcg⟩, hc⟩, hphi⟩, hmk⟩ := h
  exact ⟨hphi, hmk, DecPhi.decPhis_refines hc (ok_of_toBool hcf) (ok_of_toBool hcg)⟩

/-- **Non-vacuity of `decPhis_refines`** (decompose builtin): `FormatBool`'s string `Phi` `v11`
becomes a `StringMake`, and the phi stage's output refines its input. -/
theorem decPhis_formatBool_witness :
    (formatBool.value? 11).map (·.op) = some .Phi ∧
      (formatBoolOut.value? 11).map (·.op) = some .StringMake ∧
      RefinesUnder Env.Mono formatBoolTabs formatBoolOut formatBoolTabs formatBool :=
  decPhis_of_ok formatBool_decPhisOK

/-- **Non-vacuity of `decPhis_refines`** (decompose user): `pair`'s struct `Phi` `v11` becomes a
`StructMake`, and the phi stage's output refines its input. -/
theorem decPhis_pair_witness :
    (pair.value? 11).map (·.op) = some .Phi ∧ (pairOut.value? 11).map (·.op) = some .StructMake ∧
      RefinesUnder Env.Mono pairTabs pairOut pairTabs pair :=
  decPhis_of_ok pair_decPhisOK

end GoFV.Proof.Witness
