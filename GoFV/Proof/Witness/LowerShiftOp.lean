import GoFV.Proof.Witness.LowerAdd

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower` folding a shift into an add: `sho` (hand-written, issue #385)

`sho(x, y int) int { return x + y<<3 }` as `lower` sees it (one block: `v4 = Const64 [3]`, `v5 =
Lsh64x64 [1] v3 v4` (a bounded shift), `v6 = Add64 v2 v5` of the register arguments, returned by
`v7 = MakeResult v6 v1`). The checked lower fires `(Const64 [val]) => (MOVDconst [int64(val)])`
(182), `(Lsh64x64 <t> x y) && shiftIsBounded(v) => (SLL <t> x y)` (152), `(SLL x (MOVDconst
[c])) => (SLLconst x [c&63])` (983), `(Add64 ...) => (ADD ...)` (5) and `(ADD x0
x1:(SLLconst [c] y)) && clobberIfDead(x1) => (ADDshiftLL x0 y [c])` (1433,
`GoFV.Proof.Low.Rules.r_ARM64_1433_sound`): `v6` becomes `ADDshiftLL [3] v2 v3`, and `v4`, `v5` are
dead. `sho(1, 2)` returns 17 under `run` of the input and `runL` of the result, and by
`lower_refines` every returning or panicking `run` of `sho` is, up to refinement, a `runL` of the
result.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

-- `DecidableEq` of the nested options of tuples below exceeds the default instance size.
set_option synthInstance.maxSize 1024

/-- `sho`, the input of `lower` (the tables of `add`). -/
def shoFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 7
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[7] #[] #[] #[1, 2, 3, 4, 5, 6, 7])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 1 #[] 1),
    some (mkVI 2 .ArgIntReg 2 0 (some 6) p0 1 #[] 1),
    some (mkVI 3 .ArgIntReg 2 1 (some 7) p0 1 #[] 1),
    some (mkVI 4 .Const64 2 3 none p0 1 #[] 1),
    some (mkVI 5 .Lsh64x64 2 1 none p0 1 #[3, 4] 1),
    some (mkV 6 .Add64 2 none p0 1 #[2, 5] 1),
    some (mkV 7 .MakeResult 33 none p0 1 #[6, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `sho`. -/
def shoPassEnv : PassEnv := { laPassEnv with funcName := GoStr.ofString "sho" }

theorem sho_generic : shoFunc.lowered = false := by decide +kernel

/-- `sho` has no fused multiply-add shape: its contraction is itself. -/
theorem sho_noFma : GoFV.Opt.FmaContract.contractAll shoFunc = shoFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose `v6` is `ADDshiftLL [3] v2
v3` and whose `v5` is dead, and `sho(1, 2) = 17` under `run` of the input and `runL` of the
result. -/
theorem sho_checks :
    (lowerChecked shoPassEnv shoFunc).toOption.map (fun o =>
      ((o.func.value? 5).isSome,
        (o.func.value? 6).map (fun v => (v.op, v.auxInt, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [.int .w64 1, .int .w64 2] {} 1) 17)) =
      some (false, some (.ARM64ADDshiftLL, 3, #[2, 3]), true, true) ∧
    returnsInt (run Env.p1 laTabs shoFunc [.int .w64 1, .int .w64 2] {} 1) 17 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a shift folded into an
add (`ARM64.rules:1433`): on `sho`, the checked lower computes `ADDshiftLL [3] v2 v3`, and every
returning or panicking `run` of `sho` is, up to refinement, a `runL` of the result. -/
theorem sho_lower :
    ∃ out, lowerChecked shoPassEnv shoFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 5).isSome = false ∧
      (out.func.value? 6).map (fun v => (v.op, v.auxInt, v.args)) =
        some (.ARM64ADDshiftLL, 3, #[2, 3]) ∧
      (∃ f', GoFV.Proof.Low.Contract shoFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.LowerCheck.roPre shoPassEnv.tables shoFunc) env mem)
        out.tables out.func shoPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.LowerCheck.roPre shoPassEnv.tables shoFunc) env mem → ∀ fuel,
        (run env laTabs shoFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env laTabs shoFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := sho_checks
  cases hc : lowerChecked shoPassEnv shoFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h5, h6, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h5, h6, GoFV.Proof.Low.lower_refines hc sho_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc sho_generic sho_noFma hE hro hd⟩

end GoFV.Proof.Witness
