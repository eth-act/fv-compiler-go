import GoFV.Proof.Pass.MoveL
import GoFV.Proof.Pass.CriticalL
import GoFV.Opt.Licm

/-!
# `loop invariant` refines its input on `runL` (issues #398, #385)

`licm` moves loop-invariant values of a leaf loop to the predecessor of its header outside the
loop, first splitting that edge with a new empty `Plain` block (a preheader) when the
predecessor is not `Plain`. `licm_refinesL` composes two validated steps through `unhoist f g`
(`g`'s CFG, with `f`'s values and their placement; the preheaders empty):

* `f` to `unhoist f g`: only edges split by empty `Plain` blocks (`critRelB`,
  `GoFV.Proof.Crit.refinesL_of_critRel`);
* `unhoist f g` to `g`: values moved on a fixed CFG (`moveB`, `refinesL_of_move`).
-/

namespace GoFV.Proof.MoveL

open GoFV.SSA GoFV.Opt

/-- `g`'s CFG with `f`'s values: every block of `g` lists the values `f` lists in the block with
its ID (none for a block `f` lacks, a preheader), the value table is `f`'s. -/
def unhoist (f g : Func) : Func :=
  { g with
    valueTab := f.valueTab
    blockTab := g.blockTab.map fun ob => ob.map fun gb =>
      { gb with values := ((f.block? gb.id).map (·.values)).getD #[] } }

/-- **loop invariant refines its input on `runL`.** -/
theorem licm_refinesL {penv : PassEnv} {f : Func} {out : PassOut} {ce ce' : CheckEnv}
    (h : licmPass penv f = .ok out) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ()) (hu : check ce' (unhoist f out.func) = .ok ())
    (hc : Crit.critRelB f (unhoist f out.func) = true)
    (hm : moveB (unhoist f out.func) out.func = true) :
    RefinesL out.tables out.func penv.tables f := by
  simp only [licmPass, Pass.ofFunc, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · cases h
    exact (Crit.refinesL_of_critRel (check_wf hf) (Crit.critRelB_sound hc)).trans
      (refinesL_of_move hu hg hm)

end GoFV.Proof.MoveL
