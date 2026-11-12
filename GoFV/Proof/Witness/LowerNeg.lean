import GoFV.Proof.Witness.LowerCvtMask

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness functions for `lower` on `NEG` of `SUB` and of `NEG`: `nsb`, `nng` (hand-written, issue #385)

* `nsb(x, y int) int { return -(x - y) }` as `lower` sees it (one block: `v4 = Sub64 v2 v3` of
  the register arguments, `v5 = Neg64 v4`, returned by `v6 = MakeResult v5 v1`). The checked lower
  lowers both ops and then fires `(NEG (SUB x y)) => (SUB y x)` (`ARM64.rules:1183`,
  `GoFV.Proof.Low.Rules.r_ARM64_1183_sound`): `v5` becomes `SUB v3 v2`, and `v4` is dead.
  `nsb(3, 5)` returns 2 under `run` of the input and `runL` of the result.
* `nng(x, y int) int { return -(-x) & y }` (one block: `v4 = Neg64 v2`, `v5 = Neg64 v4`, `v6 =
  And64 v5 v3`, returned by `v7 = MakeResult v6 v1`). The checked lower fires `(NEG (NEG x)) =>
  x` (`ARM64.rules:1184`, `GoFV.Proof.Low.Rules.r_ARM64_1184_sound`), which `lower` eliminates
  inline: `v6` becomes `AND v2 v3`, and `v4`, `v5` are gone. `nng(-7, -1)` returns -7 under
  both.

By `lower_refines` every returning or panicking `run` of either function is, up to refinement, a
`runL` of the result.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

-- `DecidableEq` of the nested options of tuples below exceeds the default instance size.
set_option synthInstance.maxSize 1024

/-- `nsb`, the input of `lower` (the tables of `add`). -/
def nsbFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 6
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[6] #[] #[] #[1, 2, 3, 4, 5, 6])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 1 #[] 1),
    some (mkVI 2 .ArgIntReg 2 0 (some 6) p0 1 #[] 1),
    some (mkVI 3 .ArgIntReg 2 1 (some 7) p0 1 #[] 1),
    some (mkV 4 .Sub64 2 none p0 1 #[2, 3] 1),
    some (mkV 5 .Neg64 2 none p0 1 #[4] 1),
    some (mkV 6 .MakeResult 33 none p0 1 #[5, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `nsb`. -/
def nsbPassEnv : PassEnv := { laPassEnv with funcName := GoStr.ofString "nsb" }

theorem nsb_generic : nsbFunc.lowered = false := by decide +kernel

/-- `nsb` has no fused multiply-add shape: its contraction is itself. -/
theorem nsb_noFma : GoFV.Opt.FmaContract.contractAll nsbFunc = nsbFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose `v5` is `SUB v3 v2` and
which has no `v4`, and `nsb(3, 5) = 2` under `run` of the input and `runL` of the result. -/
theorem nsb_checks :
    (lowerChecked nsbPassEnv nsbFunc).toOption.map (fun o =>
      ((o.func.value? 4).isSome, (o.func.value? 5).map (fun v => (v.op, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [.int .w64 3, .int .w64 5] {} 1) 2)) =
      some (false, some (.ARM64SUB, #[3, 2]), true, true) ∧
    returnsInt (run Env.p1 laTabs nsbFunc [.int .w64 3, .int .w64 5] {} 1) 2 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on `NEG` of `SUB`
(`ARM64.rules:1183`): on `nsb`, the checked lower computes `SUB v3 v2` (the `SUB v2 v3` is gone),
and every returning or panicking `run` of `nsb` is, up to refinement, a `runL` of the result. -/
theorem nsb_lower :
    ∃ out, lowerChecked nsbPassEnv nsbFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 4).isSome = false ∧
      (out.func.value? 5).map (fun v => (v.op, v.args)) = some (.ARM64SUB, #[3, 2]) ∧
      (∃ f', GoFV.Proof.Low.Contract nsbFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.LowerCheck.roPre nsbPassEnv.tables nsbFunc) env mem)
        out.tables out.func nsbPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.LowerCheck.roPre nsbPassEnv.tables nsbFunc) env mem → ∀ fuel,
        (run env laTabs nsbFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env laTabs nsbFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := nsb_checks
  cases hc : lowerChecked nsbPassEnv nsbFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h4, h5, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h4, h5, GoFV.Proof.Low.lower_refines hc nsb_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc nsb_generic nsb_noFma hE hro hd⟩

/-- `nng`, the input of `lower` (the tables of `add`). -/
def nngFunc : Func where
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
    some (mkV 4 .Neg64 2 none p0 1 #[2] 1),
    some (mkV 5 .Neg64 2 none p0 1 #[4] 1),
    some (mkV 6 .And64 2 none p0 1 #[5, 3] 1),
    some (mkV 7 .MakeResult 33 none p0 1 #[6, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `nng`. -/
def nngPassEnv : PassEnv := { laPassEnv with funcName := GoStr.ofString "nng" }

theorem nng_generic : nngFunc.lowered = false := by decide +kernel

/-- `nng` has no fused multiply-add shape: its contraction is itself. -/
theorem nng_noFma : GoFV.Opt.FmaContract.contractAll nngFunc = nngFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose `v6` is `AND v2 v3` and
which has neither `v4` nor `v5`, and `nng(-7, -1) = -7` under `run` of the input and `runL` of
the result. -/
theorem nng_checks :
    (lowerChecked nngPassEnv nngFunc).toOption.map (fun o =>
      ((o.func.value? 4).isSome, (o.func.value? 5).isSome,
        (o.func.value? 6).map (fun v => (v.op, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [.int .w64 (-7), .int .w64 (-1)] {} 1) (-7))) =
      some (false, false, some (.ARM64AND, #[2, 3]), true, true) ∧
    returnsInt (run Env.p1 laTabs nngFunc [.int .w64 (-7), .int .w64 (-1)] {} 1) (-7) = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on `NEG` of `NEG`
(`ARM64.rules:1184`): on `nng`, the checked lower computes `AND v2 v3` (both negations are
gone), and every returning or panicking `run` of `nng` is, up to refinement, a `runL` of the
result. -/
theorem nng_lower :
    ∃ out, lowerChecked nngPassEnv nngFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 4).isSome = false ∧ (out.func.value? 5).isSome = false ∧
      (out.func.value? 6).map (fun v => (v.op, v.args)) = some (.ARM64AND, #[2, 3]) ∧
      (∃ f', GoFV.Proof.Low.Contract nngFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.LowerCheck.roPre nngPassEnv.tables nngFunc) env mem)
        out.tables out.func nngPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.LowerCheck.roPre nngPassEnv.tables nngFunc) env mem → ∀ fuel,
        (run env laTabs nngFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env laTabs nngFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := nng_checks
  cases hc : lowerChecked nngPassEnv nngFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h4, h5, h6, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h4, h5, h6, GoFV.Proof.Low.lower_refines hc nng_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc nng_generic nng_noFma hE hro hd⟩

end GoFV.Proof.Witness
