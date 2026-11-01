import GoFV.Opt.Checked

/-!
# Soundness of the shared checker pieces (`GoFV.Opt.Checked`)
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.Opt

theorem checkOK_sound {ce : CheckEnv} {f : Func} (h : checkOK ce f = true) :
    check ce f = .ok () := by
  unfold checkOK at h
  split at h
  · rename_i h'; exact h'
  · cases h

theorem valsOf_eq {f : Func} {b : ID} {B : Block} (h : f.block? b = some B) :
    valsOf f b = B.values := by
  unfold valsOf; rw [h]; rfl

end GoFV.Proof
