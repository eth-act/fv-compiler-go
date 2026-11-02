import GoFV.Proof.Pass.ECMain
import GoFV.Proof.Witness.SumOfInt
import GoFV.Proof.Witness.HasWaitingReaders
import GoFV.Proof.Witness.Util

/-!
# Non-vacuity witnesses: expand calls on `sumOf[int]` and `syscall_hasWaitingReaders`

expand calls lowers `sumOf[int]`'s slice parameter (`Arg` `v6` becomes a `SliceMake` of three
`ArgIntReg`s) and its call `v9` of `sumOf[go.shape.int]` (`StaticLECall` becomes `StaticCall`
with the slice's three words as register arguments). In the ABI0 wrapper
`syscall_hasWaitingReaders` (a stack-assigned result, issue #28) it stores the result into its
frame slot (`v2 = Store {bool} (LocalAddr {~r0}) v10 v9`) and returns only the memory
(`v11 = MakeResult v2`). By kernel evaluation: the pass succeeds, the input and the output (in
the output's tables) pass `check`, and the input is in `expandCallsFrag` (the output's tables
agree with the input's and `ECCheck.ecCheck` accepts the output), so `expandCalls_refines`
applies; its contracts' condition holds for `Env.p1` (`Env.p1_mono`, `Env.p1_frameKeep`).
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
      RefinesUnder (fun env => env.Mono ∧ env.FrameKeep) out.tables out.func sumOfPassEnv.tables
        sumOf := by
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

/-! ## A stack-assigned result -/

/-- `check`'s environment for the pass output of `syscall_hasWaitingReaders`. -/
def hwrOutCheckEnv (o : PassOut) : CheckEnv := { tabs := o.tables, typs := hwrTyps }

theorem hwr_checks :
    (check hwrCheckEnv hwr).toBool = true ∧ expandCallsFrag hwrPassEnv hwr = true ∧
      (hwr.value? 11).map (·.args) = some #[10, 9] := by
  decide +kernel

theorem hwr_pass :
    ((expandCallsPass hwrPassEnv hwr).toOption.map fun o =>
      (check (hwrOutCheckEnv o) o.func).toBool &&
        (o.func.value? 2).map (·.op) == some .Store &&
        (o.func.value? 11).map (·.args) == some #[2]) = some true := by
  decide +kernel

/-- **Non-vacuity of `expandCalls_refines` on a stack-assigned result**: expand calls stores
`syscall_hasWaitingReaders`'s result (`MakeResult v10 v9`) into its frame slot (the `Store` `v2`,
returned as `MakeResult v2`), the output refines the input under monotone contracts that keep
the caller's frame, and `Env.p1` satisfies that condition. -/
theorem expandCalls_stack_witness :
    ∃ out, expandCallsPass hwrPassEnv hwr = .ok out ∧
      (hwr.value? 11).map (·.args) = some #[10, 9] ∧
      (out.func.value? 2).map (·.op) = some .Store ∧ (out.func.value? 11).map (·.args) = some #[2] ∧
      RefinesUnder (fun env => env.Mono ∧ env.FrameKeep) out.tables out.func hwrPassEnv.tables
        hwr ∧ (Env.p1.Mono ∧ Env.p1.FrameKeep) := by
  obtain ⟨hc, hfrag, hres⟩ := hwr_checks
  have hp := hwr_pass
  cases hpe : expandCallsPass hwrPassEnv hwr with
  | error e => rw [hpe] at hp; cases hp
  | ok out =>
    rw [hpe] at hp
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Bool.and_eq_true,
      beq_iff_eq] at hp
    obtain ⟨⟨hcg, hst⟩, hmr⟩ := hp
    exact ⟨out, rfl, hres, hst, hmr,
      GoFV.Proof.EC.expandCalls_refines hpe (ok_of_toBool hc) (ok_of_toBool hcg) hfrag,
      Env.p1_mono, Env.p1_frameKeep⟩

end GoFV.Proof.Witness
