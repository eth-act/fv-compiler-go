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

theorem nat_all_true {n : Nat} {f : (i : Nat) → i < n → Bool} (h : ∀ i (hi : i < n), f i hi = true) :
    Nat.all n f = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Nat.all_succ, Bool.and_eq_true]
    exact ⟨ih fun i hi => h i (by omega), h n (by omega)⟩

/-- `a` and `b` have the same size and agree at every index outside `skip`. Compiled, entries
(and whole tables) that are the same object are not compared (`withPtrEq`), so a step checker
pays only for the entries a rewrite replaced. -/
def tabEq {α : Type} [DecidableEq α] [Inhabited α] (a b : Array α) (skip : Nat → Bool) : Bool :=
  withPtrEq a b
    (fun _ => a.size == b.size && Nat.all a.size fun i _ =>
      skip i || withPtrEq a[i]! b[i]! (fun _ => decide (a[i]! = b[i]!)) decide_eq_true)
    (fun h => by
      subst h
      simp only [beq_self_eq_true, Bool.true_and]
      exact nat_all_true fun i _ => by simp [withPtrEq])

end GoFV.Opt
