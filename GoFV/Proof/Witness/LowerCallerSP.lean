import GoFV.Proof.Witness.LowerAtomic

/-!
# Witness function for `lower` on the caller's stack pointer: `gcs` (hand-written, issue #385)

`gcs() int { return int(getcallersp()) }` as `lower` sees it (one block: `v2 = GetCallerSP
<uintptr> v1`, returned by `v3 = MakeResult v2 v1`): the checked lower fires `(GetCallerSP ...)
=> (LoweredGetCallerSP ...)` (456), an atom the validator pairs with the `GetCallerSP`
(`renameOp`, `callRename`); `runL` runs it as the activation's `frameVal` of `GetCallerSP`, as
`run` runs the generic op. By `lower_refines` every returning or panicking `run` of `gcs` is, up
to refinement, a `runL` of the result; both return `2^62 + 2^42`, the caller's stack pointer of
activation 0.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- `gcs`, the input of `lower` (on `ald`'s tables: `uintptr` is type 4). -/
def gcsFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 3
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[3] #[] #[] #[1, 2, 3])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 2 #[] 1),
    some (mkV 2 .GetCallerSP 4 none p0 1 #[1] 1),
    some (mkV 3 .MakeResult 33 none p0 1 #[2, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `gcs`. -/
def gcsPassEnv : PassEnv :=
  { aldPassEnv with funcName := GoStr.ofString "gcs" }

theorem gcs_generic : gcsFunc.lowered = false := by decide +kernel

/-- `gcs` has no fused multiply-add shape: its contraction is itself. -/
theorem gcs_noFma : GoFV.Opt.FmaContract.contractAll gcsFunc = gcsFunc := by decide +kernel

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 200000 in
/-- By kernel evaluation: the checked lower keeps a lowered result whose `v2` is
`LoweredGetCallerSP v1`, and `gcs` returns `2^62 + 2^42` under `run` of the input and `runL` of
the result. -/
theorem gcs_checks :
    (lowerChecked gcsPassEnv gcsFunc).toOption.map (fun o =>
      ((o.func.value? 2).map (fun v => (v.op, v.auxInt, v.aux, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [] {} 1) (BitVec.ofNat 64 (2 ^ 62 + 2 ^ 42)))) =
      some (some (.ARM64LoweredGetCallerSP, 0, none, #[1]), true, true) ∧
    returnsInt (run Env.p1 aldTabs gcsFunc [] {} 1) (BitVec.ofNat 64 (2 ^ 62 + 2 ^ 42)) = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on the caller's stack
pointer: on `gcs`, the checked lower lowers `GetCallerSP` to `LoweredGetCallerSP`, and every
returning or panicking `run` of `gcs` is, up to refinement, a `runL` of the result. -/
theorem gcs_lower :
    ∃ out, lowerChecked gcsPassEnv gcsFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 2).map (fun v => (v.op, v.auxInt, v.aux, v.args)) =
        some (.ARM64LoweredGetCallerSP, 0, none, #[1]) ∧
      (∃ f', GoFV.Proof.Low.Contract gcsFunc f' ∧
        RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func gcsPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem fuel, (run env aldTabs gcsFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env aldTabs gcsFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := gcs_checks
  cases hc : lowerChecked gcsPassEnv gcsFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h2, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h2, GoFV.Proof.Low.lower_refines hc gcs_generic,
      fun env hE args mem fuel hd => GoFV.Proof.Low.lower_refines_run hc gcs_generic gcs_noFma hE hd⟩

end GoFV.Proof.Witness
