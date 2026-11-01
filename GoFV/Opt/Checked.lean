import GoFV.SSA.Check
import GoFV.SSA.Sem.Run

/-!
# Shared pieces of the per-rewrite checkers (branchelim, fuse)

`checkOK`: `f` passes `check`. `valsOf`: a block's values. `npOf`: a non-pure node of a block
(a non-`Phi` value of scheduling priority ≠ 0), for the checkers that compare the order of the
non-pure nodes of merged blocks with the source blocks' schedules. `tabEq`: two tables agree
outside a set of indices, compared by pointer first, so a step checker pays only for the
entries a rewrite replaced (issue #147).
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

/-- The compiled `tabEq`: entries that are the same object are equal, so only the others are
compared (whole tables first, then entry by entry). -/
unsafe def tabEqImpl {α : Type} [DecidableEq α] (a b : Array α) (skip : Nat → Bool) : Bool :=
  Id.run do
    if ptrAddrUnsafe a == ptrAddrUnsafe b then return true
    if a.size != b.size then return false
    for h : i in [0:a.size] do
      if h2 : i < b.size then
        if ptrAddrUnsafe a[i] != ptrAddrUnsafe b[i] && !skip i && !decide (a[i] = b[i]) then
          return false
    return true

/-- `a` and `b` have the same size and agree at every index outside `skip`. -/
@[implemented_by tabEqImpl]
def tabEq {α : Type} [DecidableEq α] (a b : Array α) (skip : Nat → Bool) : Bool :=
  a.size == b.size && (List.range a.size).all fun i => skip i || decide (a[i]? = b[i]?)

end GoFV.Opt
