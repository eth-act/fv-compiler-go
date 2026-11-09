import GoFV.Proof.Witness.Max3
import GoFV.SSA.DomCert

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: the compiled forms of the dominator certificate

`make_eq_ofView` (`make` without the `cfgView` copy) and `usesOK_eq_usesOKFast` (`usesOK`
reading one shared ancestor path) on `max3`, by kernel evaluation: both sides agree on the
certificate of `max3` (whose uses pass) and on a certificate that puts every block at depth 0
(whose cross-block uses fail).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.DomCert

theorem max3_make_witness :
    ((make max3).idom == (ofView max3).idom && (make max3).depth == (ofView max3).depth) = true ∧
      (make max3).depth.any (· == some 2) = true := by
  decide +kernel

/-- `max3`'s certificate with every tree block at depth 0: only self-ancestry remains. -/
def max3FlatCert : Cert :=
  { make max3 with depth := (make max3).depth.map (·.map fun _ => 0) }

theorem max3_usesOK_witness :
    usesOKFast (make max3) max3 = true ∧ usesOK (make max3) max3 = true ∧
      usesOKFast max3FlatCert max3 = false ∧ usesOK max3FlatCert max3 = false := by
  decide +kernel

end GoFV.Proof.Witness
