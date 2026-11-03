import GoFV.Proof.Low.RuleL
import GoFV.Proof.PureMono
import GoFV.Proof.Retype
import GoFV.Proof.Eval

/-!
# Monotonicity of lowered terms and `Val.retypeL` (issue #385)

`armPure_mono`: the pure arm64 ops of `armTerm` give refined results on refined arguments;
`opValL_mono`: so do all lowered term nodes (`opValL`: Phase 1's `opVal`, `movAddr`, `Arm64.evalPure`).
The facts about `Val.retypeL` the term proofs use: monotone, idempotent, its result has the
shape, and Phase 1's `Val.retype` refines into it (`retype_le_retypeL`), so a generic function's
terms read in lowered mode refine their Phase 1 reading.
-/

namespace GoFV.Proof.Low

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.LowerTerm

theorem armPure_mono {op : Op} (h : armTerm op = true) (ty : Ty) (k : Int64) (ax : Option AuxRef)
    {as bs : List Val} (hr : RefinesList as bs) :
    Refines (Arm64.evalPure op ty k ax as) (Arm64.evalPure op ty k ax bs) := by
  sorry

theorem movAddr_mono (tabs : Tables) (ai : Int64) (ax : Option AuxRef) {as bs : List Val}
    (hr : RefinesList as bs) : Refines (movAddr tabs ai ax as) (movAddr tabs ai ax bs) := by
  sorry

theorem retypeL_mono (t : Ty) {v v' : Val} (h : Refines v v') : Refines (v.retypeL t) (v'.retypeL t) := by
  sorry

theorem retypeL_idem (t : Ty) (v : Val) : (v.retypeL t).retypeL t = v.retypeL t := by
  sorry

theorem retypeL_hasTy (t : Ty) (v : Val) : (v.retypeL t).hasTy t = true := by
  sorry

theorem retype_le_retypeL (t : Ty) (v : Val) : Refines (v.retype t) (v.retypeL t) := by
  sorry

theorem retypeL_poison (t : Ty) : Val.poison.retypeL t = .poison := by
  sorry

end GoFV.Proof.Low
