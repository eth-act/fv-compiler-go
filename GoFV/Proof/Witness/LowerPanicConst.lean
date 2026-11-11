import GoFV.Proof.Witness.LowerAdd
import GoFV.Proof.Witness.LowerWBPanic

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower` on a bounds panic with a constant length: `pbx` (hand-written, issue #385)

`pbx(x, y int)` as `lower` sees it (one `Exit` block): `v4 = PanicBounds [0] v2 v3 v1` panics on
the index `v2`, the register argument `x`, and the length `v3 = Const64 [3]`. The checked lower
renames the bounds panic (`ARM64.rules:512`) and folds the constant length into its aux (513:
`LoweredPanicBoundsRC [0] {3} v2 v1`; the validator relates the aux to `f`'s `Const64` operand,
`GoFV.Opt.LowerCheck.pbConstOK`). By `lower_refines` every returning or panicking `run` of `pbx`
is, up to refinement, a `runL` of the result; `pbx(5, 4)` panics with the index error `5` out of
range `3` under both.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- `pbx`, the input of `lower` (the tables and ABI of `add`, `laTabs`). -/
def pbxFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 4
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Exit p0 #[4] #[] #[] #[1, 2, 3, 4])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 1 #[] 1),
    some (mkVI 2 .ArgIntReg 2 0 (some 6) p0 1 #[] 1),
    some (mkVI 3 .Const64 2 3 none p0 1 #[] 1),
    some (mkV 4 .PanicBounds 28 none p0 1 #[2, 3, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `pbx`. -/
def pbxPassEnv : PassEnv := { laPassEnv with funcName := GoStr.ofString "pbx" }

theorem pbx_generic : pbxFunc.lowered = false := by decide +kernel

/-- `pbx` has no fused multiply-add shape: its contraction is itself. -/
theorem pbx_noFma : GoFV.Opt.FmaContract.contractAll pbxFunc = pbxFunc := by decide +kernel

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 200000 in
/-- By kernel evaluation: the checked lower keeps a lowered result whose `v4` is
`LoweredPanicBoundsRC [0] v2 v1`, and `pbx(5, 4)` panics with the index error under `run` of the
input and `runL` of the result. -/
theorem pbx_checks :
    (lowerChecked pbxPassEnv pbxFunc).toOption.map (fun o =>
      ((o.func.value? 4).map (fun v => (v.op, v.auxInt, v.args)), o.func.lowered,
        panicsIdx53 (runL Env.p1 o.tables o.func [.int .w64 5, .int .w64 4] {} 1))) =
      some (some (.ARM64LoweredPanicBoundsRC, 0, #[2, 1]), true, true) ∧
    panicsIdx53 (run Env.p1 laTabs pbxFunc [.int .w64 5, .int .w64 4] {} 1) = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a bounds panic with a
constant operand: on `pbx`, the checked lower lowers `PanicBounds` to `LoweredPanicBoundsRC` with
the constant length in its aux, and every returning or panicking `run` of `pbx` is, up to
refinement, a `runL` of the result. -/
theorem pbx_lower :
    ∃ out, lowerChecked pbxPassEnv pbxFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 4).map (fun v => (v.op, v.auxInt, v.args)) =
        some (.ARM64LoweredPanicBoundsRC, 0, #[2, 1]) ∧
      (∃ f', GoFV.Proof.Low.Contract pbxFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.LowerCheck.roPre pbxPassEnv.tables pbxFunc) env mem)
        out.tables out.func pbxPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.LowerCheck.roPre pbxPassEnv.tables pbxFunc) env mem → ∀ fuel,
        (run env laTabs pbxFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env laTabs pbxFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := pbx_checks
  cases hc : lowerChecked pbxPassEnv pbxFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h4, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h4, GoFV.Proof.Low.lower_refines hc pbx_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc pbx_generic pbx_noFma hE hro hd⟩

end GoFV.Proof.Witness
