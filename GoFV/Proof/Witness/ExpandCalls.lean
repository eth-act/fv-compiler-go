import GoFV.Proof.Pass.ECMain
import GoFV.Proof.Witness.SumOfInt
import GoFV.Proof.Witness.Util

/-!
# Non-vacuity witness: expand calls on `sumOf[int]` of `examples/generics`

expand calls lowers `sumOf[int]`'s slice parameter (`Arg` `v6` becomes a `SliceMake` of three
`ArgIntReg`s) and its call `v9` of `sumOf[go.shape.int]` (`StaticLECall` becomes `StaticCall`
with the slice's three words as register arguments). By kernel evaluation: the pass succeeds,
the input and the output (in the output's tables) pass `check`, and the input is in
`expandCallsFrag` (the output's tables agree with the input's and `ECCheck.ecCheck` accepts the
output), so `expandCalls_refines` applies.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof

/-- `check`'s environment for the pass output (in the output's tables). -/
def sumOfOutCheckEnv (o : PassOut) : CheckEnv := { tabs := o.tables, typs := sumOfTyps }

/-! ## Certificates (kernel evaluation) -/

theorem sumOf_checks :
    (check sumOfCheckEnv sumOf).toBool = true ∧ expandCallsFrag sumOfPassEnv sumOf = true ∧
      (sumOf.value? 9).map (·.op) = some .StaticLECall := by
  decide +kernel

theorem sumOf_pass :
    ((expandCallsPass sumOfPassEnv sumOf).toOption.map fun o =>
      (check (sumOfOutCheckEnv o) o.func).toBool &&
        (o.func.value? 9).map (·.op) == some .StaticCall) = some true := by
  decide +kernel

/-! ## The witness -/

/-- **Non-vacuity of `expandCalls_refines`**: expand calls lowers `sumOf[int]`'s call `v9`
(`StaticLECall` to `StaticCall`), and the output refines the input. -/
theorem expandCalls_witness :
    ∃ out, expandCallsPass sumOfPassEnv sumOf = .ok out ∧
      (sumOf.value? 9).map (·.op) = some .StaticLECall ∧
      (out.func.value? 9).map (·.op) = some .StaticCall ∧
      RefinesUnder Env.Mono out.tables out.func sumOfPassEnv.tables sumOf := by
  obtain ⟨hc, hfrag, hle⟩ := sumOf_checks
  have hp := sumOf_pass
  cases hpe : expandCallsPass sumOfPassEnv sumOf with
  | error e => rw [hpe] at hp; cases hp
  | ok out =>
    rw [hpe] at hp
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Bool.and_eq_true,
      beq_iff_eq] at hp
    obtain ⟨hcg, hcall⟩ := hp
    exact ⟨out, rfl, hle, hcall,
      GoFV.Proof.EC.expandCalls_refines hpe (ok_of_toBool hc) (ok_of_toBool hcg) hfrag⟩

/-! ## Non-vacuity of the call-argument lemmas (#28) -/

/-- `ecc_ofPieces_arg` at a pointer argument of a `uintptr` parameter (`castOK`): the decoded
argument refines the pointer retyped at the parameter's shape. -/
theorem expandCalls_castArg_witness :
    Sem.Refines ((Val.ptr ⟨.outargs 0, 8⟩).retype (.int .w64))
      (ofPieces (.int .w64) [.ptr ⟨.outargs 0, 8⟩]) :=
  GoFV.Proof.EC.ecc_ofPieces_arg rfl (.inr ⟨rfl, none, rfl⟩) (.cons (Sem.Refines.refl _) .nil)

/-- `ecs_decode_hasTy_mov` at a blob (a `Move`-copied `[2]byte` stack argument). -/
theorem expandCalls_movTy_witness : (decode #[.b 1, .b 2] 0 (.blob 2)).hasTy (.blob 2) = true :=
  GoFV.Proof.EC.ecs_decode_hasTy_mov (.blob 2) _ 0 rfl (by decide)

/-- `ecc_hasPoison_retype` at an aggregate with a `poison` field. -/
theorem expandCalls_poisonArg_witness :
    ((Val.agg [.poison]).retype (.agg [(0, .int .w64)] 8)).hasPoison = true :=
  GoFV.Proof.EC.ecc_hasPoison_retype _ _ rfl

end GoFV.Proof.Witness
