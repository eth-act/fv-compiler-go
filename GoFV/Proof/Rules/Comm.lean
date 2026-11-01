import GoFV.Proof.Rules.Tactic

/-!
# Commutative patterns

`Rule.Sound` considers only the written argument order of a pattern. The interpreter also
matches a `commute` node (rulegen's commutative expansion) with its first two arguments
swapped; this module proves that the value of every phase-P1 op that a pattern of the four
rule files marks `commute`, of the pointer comparisons `EqPtr`/`NeqPtr` (#156: same block
and offset) and of the commutative float ops `Add`/`Mul`/`Eq`/`Neq{32,64}F` (their operands
in encoding order, `FOps.ordered_comm`) does not depend on that order (`commOpsP1_sound`), so
a swapped match is an unswapped match of the same value.

The other op marked `commute` (`MemEq`) belongs to a later phase; its lemma comes with its
semantics.
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem

/-- The phase-P1 ops some pattern of the four rule files marks `commute`, `EqPtr`/`NeqPtr` and
the commutative float ops. -/
def commOpsP1 : List Op :=
  [.Add8, .Add16, .Add32, .Add64, .Add64carry, .And8, .And16, .And32, .And64, .AndB, .Eq8,
   .Eq16, .Eq32, .Eq64, .EqB, .Mul8, .Mul16, .Mul32, .Mul64, .Mul32uhilo, .Mul32uover,
   .Mul64uhilo, .Mul64uover, .Neq8, .Neq16, .Neq32, .Neq64, .NeqB, .Or8, .Or16, .Or32, .Or64,
   .OrB, .Xor8, .Xor16, .Xor32, .Xor64, .EqPtr, .NeqPtr, .Add32F, .Add64F, .Mul32F, .Mul64F,
   .Eq32F, .Eq64F, .Neq32F, .Neq64F]

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
    rw [int2_eq, int2_eq]
    cases p.asInt w <;> cases q.asInt w <;> simp [hf]

theorem int3_comm (w : Width) (f : BitVec w.bits → BitVec w.bits → BitVec w.bits → Val)
    (hf : ∀ x y z, f x y z = f y x z) (p q : Val) (rest : List Val) :
    int3 w f (p :: q :: rest) = int3 w f (q :: p :: rest) := by
  match rest with
  | [] => rfl
  | [c] =>
    rw [int3_eq, int3_eq]
    cases p.asInt w <;> cases q.asInt w <;> simp only [Option.elim_none, Option.elim_some]
    exact congrArg _ (funext fun z => hf _ _ z)
  | _ :: _ :: _ => rfl

theorem bool2_comm (f : Bool → Bool → Bool) (hf : ∀ x y, f x y = f y x) (p q : Val)
    (rest : List Val) : bool2 f (p :: q :: rest) = bool2 f (q :: p :: rest) := by
  cases rest with
  | cons _ _ => rfl
  | nil =>
    rw [bool2_eq, bool2_eq]
    cases p.asBool <;> cases q.asBool <;> simp [hf]

theorem asBool_cases (v : Val) : v.asBool = none ∨ v = .bool true ∨ v = .bool false := by
  cases v <;> simp [Val.asBool]

theorem asBool_bool (b : Bool) : (Val.bool b).asBool = some b := rfl

theorem andB_comm (p q : Val) (rest : List Val) :
    Cmp.andB (p :: q :: rest) = Cmp.andB (q :: p :: rest) := by
  cases rest with
  | cons _ _ => rfl
  | nil =>
    rcases asBool_cases p with hp | rfl | rfl <;> rcases asBool_cases q with hq | rfl | rfl <;>
      simp_all [Cmp.andB, asBool_bool]

theorem orB_comm (p q : Val) (rest : List Val) :
    Cmp.orB (p :: q :: rest) = Cmp.orB (q :: p :: rest) := by
  cases rest with
  | cons _ _ => rfl
  | nil =>
    rcases asBool_cases p with hp | rfl | rfl <;> rcases asBool_cases q with hq | rfl | rfl <;>
      simp_all [Cmp.orB, asBool_bool]

theorem eqPtr_comm (neg : Bool) (p q : Val) (rest : List Val) :
    PtrOps.eqPtr neg (p :: q :: rest) = PtrOps.eqPtr neg (q :: p :: rest) := by
  cases rest with
  | cons _ _ => rfl
  | nil =>
    simp only [PtrOps.eqPtr]
    cases p.asPtrWord <;> cases q.asPtrWord <;> simp only
    rename_i a b
    rw [show a.eq b = b.eq a by simp only [Ptr.eq, BEq.comm]]

theorem commOpsP1_sound : ∀ o ∈ commOpsP1, CommSound o := by
  intro o ho t a x p q rest
  simp only [commOpsP1, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
  simp only [reduceEvalPure, Sem.Int.add, Sem.Int.mul, Sem.Int.and, Sem.Int.or, Sem.Int.xor,
    Sem.Int.mulhilo, Sem.Int.mulover, Sem.Int.addcarry, Cmp.eq, Cmp.neq, Cmp.eqB,
    Cmp.neqB, FOps.add, FOps.mul, FOps.eq, FOps.neq, FOps.bin, FOps.cmpC] <;>
  first
  | exact int2_comm _ _ (fun x y => by
      first
      | rw [FOps.ordered_comm]
      | simp only [BitVec.add_comm, BitVec.mul_comm, BitVec.and_comm, BitVec.or_comm,
          BitVec.xor_comm, Bool.beq_comm, bne_comm, Nat.mul_comm, eq_comm]) _ _ _
  | exact int3_comm _ _ (fun x y z => by simp only [Nat.add_comm x.toNat y.toNat]) _ _ _
  | exact bool2_comm _ (fun x y => by cases x <;> cases y <;> rfl) _ _ _
  | exact andB_comm _ _ _
  | exact orB_comm _ _ _
  | exact eqPtr_comm _ _ _ _

/-- Non-vacuity: `Add16` is commutative on concrete arguments (and `Sub16` is not, so
`CommSound` is not trivial). -/
example : evalPure .Add16 (.int .w16) 0 none [.i16 3, .i16 5] =
    evalPure .Add16 (.int .w16) 0 none [.i16 5, .i16 3] := by rfl
theorem sub16_not_comm : ¬ CommSound .Sub16 := by
  intro h
  have := h (.int .w16) 0 none (.i16 3) (.i16 5) []
  simp [reduceEvalPure, Sem.Int.sub, int2] at this

end GoFV.Proof.Rules
