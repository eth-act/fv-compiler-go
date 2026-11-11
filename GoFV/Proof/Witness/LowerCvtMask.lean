import GoFV.Proof.Witness.LowerCondSel

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness functions for `lower` on `CvtBoolToUint8` and a sign-masked add: `cvb`, `ams` (hand-written, issue #385)

* `cvb(x, y int) int { return int(b2u(x < y)) }` as `lower` sees it (one block: `v4 = Less64 v2
  v3` of the register arguments, `v5 = CvtBoolToUint8 <uint8> v4`, `v6 = ZeroExt8to64 v5`,
  returned by `v7 = MakeResult v6 v1`). The checked lower fires `(CvtBoolToUint8 ...) => (Copy
  ...)` (`ARM64.rules:233`, `GoFV.Proof.Low.Rules.r_ARM64_233_sound`), which `lower` eliminates
  inline: `v6` becomes `MOVBUreg v4`, `v5` is gone. `cvb(1, 2)` returns 1 under `run` of the input
  and `runL` of the result.
* `ams(x, y int) int { return x + (x>>63) & (y<<3) }` (one block: `v4 = Const64 [63]`, `v5 =
  Rsh64x64 [1] v2 v4`, `v6 = Const64 [3]`, `v7 = Lsh64x64 [1] v3 v6` (bounded shifts), `v8 = And64
  v5 v7`, `v9 = Add64 v2 v8`, returned by `v10 = MakeResult v9 v1`). The checked lower folds the
  shifts into `v8 = ANDshiftLL [3] (SRAconst [63] v2) v3` and then fires `(ADD x0
  x1:(ANDshiftLL x2:(SRAconst [63] z) y [sl])) && … => (ADDshiftLL x0 (ANDshiftRA <y.Type> y z [63])
  [sl])` (`ARM64.rules:1635`, `GoFV.Proof.Low.Rules.r_ARM64_1635_sound`): `v9` becomes
  `ADDshiftLL [3] v2 v11` of a fresh `v11`, and `v4`–`v8` are dead. `ams(-1, 2)` returns 15 under
  both.

By `lower_refines` every returning or panicking `run` of either function is, up to refinement, a
`runL` of the result.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

-- `DecidableEq` of the nested options of tuples below exceeds the default instance size.
set_option synthInstance.maxSize 1024

/-- The definition tables of `cvb`: `smin`'s and `uint8` (type 4). -/
def cvbTabs : Tables :=
  { lcsTabs with types := lcsTabs.types.set! 4 (some (mkT .UINT8 (some 1) "uint8")) }

/-- `cvb`, the input of `lower`. -/
def cvbFunc : Func where
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
    some (mkV 4 .Less64 3 none p0 1 #[2, 3] 1),
    some (mkV 5 .CvtBoolToUint8 4 none p0 1 #[4] 1),
    some (mkV 6 .ZeroExt8to64 2 none p0 1 #[5] 1),
    some (mkV 7 .MakeResult 33 none p0 1 #[6, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `cvb` (`typ.UInt8` is type 4). -/
def cvbPassEnv : PassEnv :=
  { lcsPassEnv with funcName := GoStr.ofString "cvb", tables := cvbTabs,
                    typs := lcsPassEnv.typs.push ("UInt8", 4) }

theorem cvb_generic : cvbFunc.lowered = false := by decide +kernel

/-- `cvb` has no fused multiply-add shape: its contraction is itself. -/
theorem cvb_noFma : GoFV.Opt.FmaContract.contractAll cvbFunc = cvbFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose `v6` is `MOVBUreg v4`
and which has no `v5`, and `cvb(1, 2) = 1` under `run` of the input and `runL` of the result. -/
theorem cvb_checks :
    (lowerChecked cvbPassEnv cvbFunc).toOption.map (fun o =>
      ((o.func.value? 5).isSome, (o.func.value? 6).map (fun v => (v.op, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [.int .w64 1, .int .w64 2] {} 1) 1)) =
      some (false, some (.ARM64MOVBUreg, #[4]), true, true) ∧
    returnsInt (run Env.p1 cvbTabs cvbFunc [.int .w64 1, .int .w64 2] {} 1) 1 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on `CvtBoolToUint8`
(`ARM64.rules:233`): on `cvb`, the checked lower's `v6` is `MOVBUreg v4` (the `Copy` it made of
`v5` is gone), and every returning or panicking `run` of `cvb` is, up to refinement, a `runL` of
the result. -/
theorem cvb_lower :
    ∃ out, lowerChecked cvbPassEnv cvbFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 5).isSome = false ∧
      (out.func.value? 6).map (fun v => (v.op, v.args)) = some (.ARM64MOVBUreg, #[4]) ∧
      (∃ f', GoFV.Proof.Low.Contract cvbFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.RewriteCheck.roSyms cvbPassEnv.tables cvbFunc) env mem)
        out.tables out.func cvbPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.RewriteCheck.roSyms cvbPassEnv.tables cvbFunc) env mem → ∀ fuel,
        (run env cvbTabs cvbFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env cvbTabs cvbFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := cvb_checks
  cases hc : lowerChecked cvbPassEnv cvbFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h5, h6, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h5, h6, GoFV.Proof.Low.lower_refines hc cvb_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc cvb_generic cvb_noFma hE hro hd⟩

/-- `ams`, the input of `lower` (the tables of `add`). -/
def amsFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 10
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[10] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 1 #[] 1),
    some (mkVI 2 .ArgIntReg 2 0 (some 6) p0 2 #[] 1),
    some (mkVI 3 .ArgIntReg 2 1 (some 7) p0 1 #[] 1),
    some (mkVI 4 .Const64 2 63 none p0 1 #[] 1),
    some (mkVI 5 .Rsh64x64 2 1 none p0 1 #[2, 4] 1),
    some (mkVI 6 .Const64 2 3 none p0 1 #[] 1),
    some (mkVI 7 .Lsh64x64 2 1 none p0 1 #[3, 6] 1),
    some (mkV 8 .And64 2 none p0 1 #[5, 7] 1),
    some (mkV 9 .Add64 2 none p0 1 #[2, 8] 1),
    some (mkV 10 .MakeResult 33 none p0 1 #[9, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `ams`. -/
def amsPassEnv : PassEnv := { laPassEnv with funcName := GoStr.ofString "ams" }

theorem ams_generic : amsFunc.lowered = false := by decide +kernel

/-- `ams` has no fused multiply-add shape: its contraction is itself. -/
theorem ams_noFma : GoFV.Opt.FmaContract.contractAll amsFunc = amsFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose `v9` is `ADDshiftLL [3] v2
v11` and whose `v8` is dead, and `ams(-1, 2) = 15` under `run` of the input and `runL` of the
result. -/
theorem ams_checks :
    (lowerChecked amsPassEnv amsFunc).toOption.map (fun o =>
      ((o.func.value? 8).isSome, (o.func.value? 9).map (fun v => (v.op, v.auxInt, v.args)),
        o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [.int .w64 (-1), .int .w64 2] {} 1) 15)) =
      some (false, some (.ARM64ADDshiftLL, 3, #[2, 11]), true, true) ∧
    returnsInt (run Env.p1 laTabs amsFunc [.int .w64 (-1), .int .w64 2] {} 1) 15 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a sign-masked shifted
add (`ARM64.rules:1635`): on `ams`, the checked lower computes `ADDshiftLL [3] v2 v11`, and every
returning or panicking `run` of `ams` is, up to refinement, a `runL` of the result. -/
theorem ams_lower :
    ∃ out, lowerChecked amsPassEnv amsFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 8).isSome = false ∧
      (out.func.value? 9).map (fun v => (v.op, v.auxInt, v.args)) =
        some (.ARM64ADDshiftLL, 3, #[2, 11]) ∧
      (∃ f', GoFV.Proof.Low.Contract amsFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.RewriteCheck.roSyms amsPassEnv.tables amsFunc) env mem)
        out.tables out.func amsPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.RewriteCheck.roSyms amsPassEnv.tables amsFunc) env mem → ∀ fuel,
        (run env laTabs amsFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env laTabs amsFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := ams_checks
  cases hc : lowerChecked amsPassEnv amsFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h8, h9, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h8, h9, GoFV.Proof.Low.lower_refines hc ams_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc ams_generic ams_noFma hE hro hd⟩

end GoFV.Proof.Witness
