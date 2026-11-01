import GoFV.SSA.Check
import GoFV.SSA.Sem.Run

/-!
# Shared pieces of the per-rewrite checkers (branchelim, fuse)

`checkOK`: `f` passes `check`. `valsOf`: a block's values. `npOf`: a non-pure node of a block
(a non-`Phi` value of scheduling priority ≠ 0), for the checkers that compare the order of the
non-pure nodes of merged blocks with the source blocks' schedules.
-/

namespace GoFV.Opt

open GoFV.SSA

/-- `f` passes `check`. -/
def checkOK (ce : CheckEnv) (f : Func) : Bool :=
  match check ce f with
  | .ok () => true
  | .error _ => false

/-- The values of block `b` (none if `b` is not a block). -/
def valsOf (f : Func) (b : ID) : Array ID := ((f.block? b).map (·.values)).getD #[]

/-- `x` is a non-pure node of block `B` of `f`: a non-`Phi` value of priority ≠ 0. -/
def npOf (f : Func) (B : Block) (x : ID) : Bool :=
  B.values.contains x &&
    match f.value? x with
    | some v => v.op != .Phi && Sem.prio v.op != 0
    | none => false

end GoFV.Opt
