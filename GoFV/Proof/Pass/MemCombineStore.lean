import GoFV.Proof.Pass.MemCombineRef

/-!
# memcombine: a combined store writes what its chain wrote (issue #35)

`store_chgRef`: a combined store `storeOK` accepts satisfies the atom simulation's changed-store
obligation (`AtomSim.ChgRefP`).
-/

namespace GoFV.Proof.MemCombine

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.MemCombine.Check GoFV.Opt.RewriteCheck GoFV.Proof.Term
open GoFV.Proof.AtomSim

section
variable {tabs : Tables} {f g : Func} {R : Array Bool} {ce ce' : CheckEnv}
  (hwf : WF ce f) (hwg : WF ce' g) (K : McFacts tabs f g R)
include hwf hwg K

/-- **A combined store** writes a memory refining the one its chain of stores wrote. -/
theorem store_chgRef {x : ID} {u w : Value} (hu : f.value? x = some u)
    (hs : storeOK tabs f g (relMarks f g R) x u w = true) :
    ChgRefP f.value? tabs u (listedDefs g) w := by
  sorry

end

end GoFV.Proof.MemCombine
