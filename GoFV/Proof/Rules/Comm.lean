import GoFV.Proof.Rules.Tactic

/-!
# Commutative patterns

`Rule.Sound` considers only the written argument order of a pattern. The interpreter also
matches a `commute` node (rulegen's commutative expansion) with its first two arguments
swapped; this module proves that the value of every phase-P1 op that a pattern of the four
rule files marks `commute` does not depend on that order (`commOpsP1_sound`), so a swapped
match is an unswapped match of the same value.

The other ops marked `commute` (`Add32F`, `Add64F`, `Mul32F`, `Mul64F`, `Eq32F`, `Eq64F`,
`Neq32F`, `Neq64F`, `EqPtr`, `NeqPtr`, `MemEq`) belong to later phases; their lemmas come with
their semantics.
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem

/-- The phase-P1 ops some pattern of the four rule files marks `commute`. -/
def commOpsP1 : List Op :=
  [.Add8, .Add16, .Add32, .Add64, .Add64carry, .And8, .And16, .And32, .And64, .AndB, .Eq8,
   .Eq16, .Eq32, .Eq64, .EqB, .Mul8, .Mul16, .Mul32, .Mul64, .Mul32uhilo, .Mul32uover,
   .Mul64uhilo, .Mul64uover, .Neq8, .Neq16, .Neq32, .Neq64, .NeqB, .Or8, .Or16, .Or32, .Or64,
   .OrB, .Xor8, .Xor16, .Xor32, .Xor64]

/-- The value of `o` does not depend on the order of its first two arguments. -/
def CommSound (o : Op) : Prop :=
  ∀ (t : Ty) (a : Int64) (x : Option AuxRef) (p q : Val) (rest : List Val),
    evalPure o t a x (p :: q :: rest) = evalPure o t a x (q :: p :: rest)

theorem int2_comm (w : Width) (f : BitVec w.bits → BitVec w.bits → Val)
    (hf : ∀ x y, f x y = f y x) (p q : Val) (rest : List Val) :
    int2 w f (p :: q :: rest) = int2 w f (q :: p :: rest) := by
  cases rest with
  | cons _ _ => rfl
  | nil =>
    simp only [int2]
    cases p.asInt w <;> cases q.asInt w <;> simp [hf]

theorem int3_comm (w : Width) (f : BitVec w.bits → BitVec w.bits → BitVec w.bits → Val)
    (hf : ∀ x y z, f x y z = f y x z) (p q : Val) (rest : List Val) :
    int3 w f (p :: q :: rest) = int3 w f (q :: p :: rest) := by
  match rest with
  | [] => rfl
  | [_] =>
    simp only [int3]
    cases p.asInt w <;> cases q.asInt w <;> simp [hf]
  | _ :: _ :: _ => rfl

theorem bool2_comm (f : Bool → Bool → Bool) (hf : ∀ x y, f x y = f y x) (p q : Val)
    (rest : List Val) : bool2 f (p :: q :: rest) = bool2 f (q :: p :: rest) := by
  cases rest with
  | cons _ _ => rfl
  | nil =>
    simp only [bool2]
    cases p.asBool <;> cases q.asBool <;> simp [hf]

theorem commOpsP1_sound : ∀ o ∈ commOpsP1, CommSound o := by
  intro o ho t a x p q rest
  simp only [commOpsP1, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp only [reduceEvalPure, Sem.Int.add, Sem.Int.mul, Sem.Int.and, Sem.Int.or, Sem.Int.xor,
    Sem.Int.mulhilo, Sem.Int.mulover, Sem.Int.addcarry, Cmp.eq, Cmp.neq, Cmp.andB, Cmp.orB,
    Cmp.eqB, Cmp.neqB] <;>
  first
  | exact int2_comm _ _ (fun x y => by
      simp only [BitVec.add_comm, BitVec.mul_comm, BitVec.and_comm, BitVec.or_comm,
        BitVec.xor_comm, beq_comm, bne_comm, Nat.mul_comm]) _ _ _
  | exact int3_comm _ _ (fun x y z => by simp only [Nat.add_comm x.toNat y.toNat]) _ _ _
  | exact bool2_comm _ (fun x y => by cases x <;> cases y <;> rfl) _ _ _

/-- Non-vacuity: `Add16` is commutative on concrete arguments (and `Sub16` is not, so
`CommSound` is not trivial). -/
example : evalPure .Add16 (.int .w16) 0 none [.i16 3, .i16 5] =
    evalPure .Add16 (.int .w16) 0 none [.i16 5, .i16 3] := by rfl
theorem sub16_not_comm : ¬ CommSound .Sub16 := by
  intro h
  have := h (.int .w16) 0 none (.i16 3) (.i16 5) []
  simp [reduceEvalPure, Sem.Int.sub, int2] at this

end GoFV.Proof.Rules
