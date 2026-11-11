import GoFV.Proof.Witness.LowerStoreSym

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower` on a write barrier and a bounds panic: `wbp` (hand-written, issue #385)

One `Exit` block: `v4 = WB <(*int,mem)> [1] v1` allocates a write-barrier buffer entry on the
initial memory, `v5 = Select1 <mem> v4` its memory, `v6 = PanicBounds [0] v2 v3 v5` panics on
the index `v2 = Const64 [5]` and the length `v3 = Const64 [3]`. The checked lower fires
`(WB ...) => (LoweredWB ...)` (507, a term of lowered SSA on both sides, `wbOp`) and
`(PanicBounds ...) => (LoweredPanicBoundsRR ...)` (512, an atom rename, `panicBounds` on both
sides), the constants' `(Const64 [val]) => (MOVDconst [val])`, and folds both constant operands
into the bounds panic's aux (513, then 515: `LoweredPanicBoundsCC [0] {5, 3} v5`). By
`lower_refines` every returning or panicking `run` of `wbp` is, up to refinement, a `runL` of the
result; both panic with the index error `5` out of range `3`.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- The tables of `gst` with the tuple `(*int,mem)` (type 30). -/
def wbpTabs : Tables :=
  { gstTabs with types := gstTabs.types.set! 30 (some (mkT .TUPLE none "(*int,mem)" (.tuple 3 28))) }

/-- `wbp`, the input of `lower`. -/
def wbpFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 6
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Exit p0 #[6] #[] #[] #[1, 2, 3, 4, 5, 6])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 1 #[] 1),
    some (mkVI 2 .Const64 2 5 none p0 1 #[] 1),
    some (mkVI 3 .Const64 2 3 none p0 1 #[] 1),
    some (mkVI 4 .WB 30 1 none p0 1 #[1] 1),
    some (mkV 5 .Select1 28 none p0 1 #[4] 1),
    some (mkV 6 .PanicBounds 28 none p0 1 #[2, 3, 5] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `wbp`. -/
def wbpPassEnv : PassEnv :=
  { gstPassEnv with funcName := GoStr.ofString "wbp", tables := wbpTabs }

/-- The outcome is the index panic of `5` against the length `3`. -/
def panicsIdx53 : Outcome → Bool
  | .panicked (.bounds 0 5 3) _ => true
  | _ => false

theorem wbp_generic : wbpFunc.lowered = false := by decide +kernel

/-- `wbp` has no fused multiply-add shape: its contraction is itself. -/
theorem wbp_noFma : GoFV.Opt.FmaContract.contractAll wbpFunc = wbpFunc := by decide +kernel

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 200000 in
/-- By kernel evaluation: the checked lower keeps a lowered result whose `v4` is
`LoweredWB [1] v1` and whose `v6` is `LoweredPanicBoundsCC [0] v5`, and `wbp` panics with
the index error under `run` of the input and `runL` of the result. -/
theorem wbp_checks :
    (lowerChecked wbpPassEnv wbpFunc).toOption.map (fun o =>
      ((o.func.value? 4).map (fun v => (v.op, v.auxInt, v.args)),
        (o.func.value? 6).map (fun v => (v.op, v.auxInt, v.args)), o.func.lowered,
        panicsIdx53 (runL Env.p1 o.tables o.func [] {} 1))) =
      some (some (.ARM64LoweredWB, 1, #[1]), some (.ARM64LoweredPanicBoundsCC, 0, #[5]),
        true, true) ∧
    panicsIdx53 (run Env.p1 wbpTabs wbpFunc [] {} 1) = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a write barrier and a
bounds panic: on `wbp`, the checked lower lowers `WB` to `LoweredWB` and `PanicBounds` on two
constants to `LoweredPanicBoundsCC`, and every returning or panicking `run` of `wbp` is, up to
refinement, a `runL` of the result. -/
theorem wbp_lower :
    ∃ out, lowerChecked wbpPassEnv wbpFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 4).map (fun v => (v.op, v.auxInt, v.args)) =
        some (.ARM64LoweredWB, 1, #[1]) ∧
      (out.func.value? 6).map (fun v => (v.op, v.auxInt, v.args)) =
        some (.ARM64LoweredPanicBoundsCC, 0, #[5]) ∧
      (∃ f', GoFV.Proof.Low.Contract wbpFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.LowerCheck.roPre wbpPassEnv.tables wbpFunc) env mem)
        out.tables out.func wbpPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.LowerCheck.roPre wbpPassEnv.tables wbpFunc) env mem → ∀ fuel,
        (run env wbpTabs wbpFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env wbpTabs wbpFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := wbp_checks
  cases hc : lowerChecked wbpPassEnv wbpFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h4, h6, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h4, h6, GoFV.Proof.Low.lower_refines hc wbp_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc wbp_generic wbp_noFma hE hro hd⟩

end GoFV.Proof.Witness
