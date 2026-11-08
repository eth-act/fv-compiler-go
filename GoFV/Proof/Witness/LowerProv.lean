import GoFV.Proof.Witness.LowerCvtMask

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness functions for `lower` on the provenance cases of `MADD`, `CSINC`, `CMPshift*` and `CMN`: `mad`, `csi`, `csh`, `cng` (hand-written, issue #385)

* `mad(x, y int) int { return x + x*y }` (one block: `v4 = Mul64 v2 v3`, `v5 = Add64 v2 v4`,
  returned by `v6 = MakeResult v5 v1`). The checked lower fires `(ADD a l:(MUL x y)) && … =>
  (MADD a x y)` (`ARM64.rules:1012`, `GoFV.Proof.Low.Rules.r_ARM64_1012_sound`): `v5` becomes
  `MADD v2 v2 v3` and `v4` is gone. `mad(3, 4)` returns 15 under `run` of the input and `runL` of
  the result.
* `csi(x, y int) int { if x < y { return x + 1 }; return y }` after branchelim (`v4 = Less64 v2
  v3`, `v5 = Const64 [1]`, `v6 = Add64 v2 v5`, `v7 = CondSelect <int> v6 v3 v4`, `v8 = MakeResult
  v7 v1`). The checked lower builds `CSEL [cc] (ADDconst [1] v2) v3 flag` and fires `(CSEL [cc]
  (ADDconst [1] a) x flag) => (CSINC [arm64Negate(cc)] x a flag)` (`1191`, split by the
  condition, `r_ARM64_1191_cc_sound`): `v7` becomes `CSINC v3 v2 v10` of a fresh `v10 = CMP v3
  v2`. `csi(3, 4)` returns 4 under both.
* `csh(x, y int) int { return int(b2u(x < y<<3)) }` (`v4 = Const64 [3]`, `v5 = Lsh64x64 [1] v3
  v4`, `v6 = Less64 v2 v5`, `v7 = CvtBoolToUint8 v6`, `v8 = ZeroExt8to64 v7`, `v9 = MakeResult v8
  v1`). The checked lower fires `(CMP x0 x1:(SLLconst [c] y)) && … => (CMPshiftLL x0 y [c])`
  (`1463`, `r_ARM64_1463_sound`): the compare is `v10 = CMPshiftLL [3] v2 v3`. `csh(1, 1)`
  returns 1 under both.
* `cng(x, y int) int { return int(b2u(x < -5)) }` (`v4 = Const64 [-5]`, `v5 = Less64 v2 v4`, `v6 =
  CvtBoolToUint8 v5`, `v7 = ZeroExt8to64 v6`, `v8 = MakeResult v7 v1`). The checked lower fires
  `(CMPconst [c] y) && c < 0 && c != -1<<63 => (CMNconst [-c] y)` (`597`, `r_ARM64_597_2_sound`):
  the compare is `v9 = CMNconst [5] v2`. `cng(-6, 0)` returns 1 under both.

By `lower_refines` every returning or panicking `run` of each function is, up to refinement, a
`runL` of the result.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

-- `DecidableEq` of the nested options of tuples below exceeds the default instance size.
set_option synthInstance.maxSize 1024

/-! ## `mad`: `MADD` (`1012`) -/

/-- `mad`, the input of `lower` (the tables of `add`). -/
def madFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 6
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[6] #[] #[] #[1, 2, 3, 4, 5, 6])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 1 #[] 1),
    some (mkVI 2 .ArgIntReg 2 0 (some 6) p0 2 #[] 1),
    some (mkVI 3 .ArgIntReg 2 1 (some 7) p0 1 #[] 1),
    some (mkV 4 .Mul64 2 none p0 1 #[2, 3] 1),
    some (mkV 5 .Add64 2 none p0 1 #[2, 4] 1),
    some (mkV 6 .MakeResult 33 none p0 1 #[5, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `mad`. -/
def madPassEnv : PassEnv := { laPassEnv with funcName := GoStr.ofString "mad" }

theorem mad_generic : madFunc.lowered = false := by decide +kernel

/-- `mad` has no fused multiply-add shape: its contraction is itself. -/
theorem mad_noFma : GoFV.Opt.FmaContract.contractAll madFunc = madFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose `v5` is `MADD v2 v2 v3`
and which has no `v4`, and `mad(3, 4) = 15` under `run` of the input and `runL` of the result. -/
theorem mad_checks :
    (lowerChecked madPassEnv madFunc).toOption.map (fun o =>
      ((o.func.value? 4).isSome, (o.func.value? 5).map (fun v => (v.op, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [.int .w64 3, .int .w64 4] {} 1) 15)) =
      some (false, some (.ARM64MADD, #[2, 2, 3]), true, true) ∧
    returnsInt (run Env.p1 laTabs madFunc [.int .w64 3, .int .w64 4] {} 1) 15 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on `MADD`
(`ARM64.rules:1012`): on `mad`, the checked lower computes `MADD v2 v2 v3`, and every returning
or panicking `run` of `mad` is, up to refinement, a `runL` of the result. -/
theorem mad_lower :
    ∃ out, lowerChecked madPassEnv madFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 4).isSome = false ∧
      (out.func.value? 5).map (fun v => (v.op, v.args)) = some (.ARM64MADD, #[2, 2, 3]) ∧
      (∃ f', GoFV.Proof.Low.Contract madFunc f' ∧
        RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func madPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem fuel, (run env laTabs madFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env laTabs madFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := mad_checks
  cases hc : lowerChecked madPassEnv madFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h4, h5, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h4, h5, GoFV.Proof.Low.lower_refines hc mad_generic,
      fun env hE args mem fuel hd => GoFV.Proof.Low.lower_refines_run hc mad_generic mad_noFma hE hd⟩

/-! ## `csi`: `CSINC` (`1191`) -/

/-- `csi`, the input of `lower` (the tables of `smin`). -/
def csiFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 8
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[8] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 1 #[] 1),
    some (mkVI 2 .ArgIntReg 2 0 (some 6) p0 2 #[] 1),
    some (mkVI 3 .ArgIntReg 2 1 (some 7) p0 2 #[] 1),
    some (mkV 4 .Less64 3 none p0 1 #[2, 3] 1),
    some (mkVI 5 .Const64 2 1 none p0 1 #[] 1),
    some (mkV 6 .Add64 2 none p0 1 #[2, 5] 1),
    some (mkV 7 .CondSelect 2 none p0 1 #[6, 3, 4] 1),
    some (mkV 8 .MakeResult 33 none p0 1 #[7, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `csi`. -/
def csiPassEnv : PassEnv := { lcsPassEnv with funcName := GoStr.ofString "csi" }

theorem csi_generic : csiFunc.lowered = false := by decide +kernel

/-- `csi` has no fused multiply-add shape: its contraction is itself. -/
theorem csi_noFma : GoFV.Opt.FmaContract.contractAll csiFunc = csiFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose `v7` is `CSINC v3 v2 v10`
and which has no `v6`, and `csi(3, 4) = 4` under `run` of the input and `runL` of the result. -/
theorem csi_checks :
    (lowerChecked csiPassEnv csiFunc).toOption.map (fun o =>
      ((o.func.value? 6).isSome, (o.func.value? 7).map (fun v => (v.op, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [.int .w64 3, .int .w64 4] {} 1) 4)) =
      some (false, some (.ARM64CSINC, #[3, 2, 10]), true, true) ∧
    returnsInt (run Env.p1 lcsTabs csiFunc [.int .w64 3, .int .w64 4] {} 1) 4 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on `CSINC`
(`ARM64.rules:1191`): on `csi`, the checked lower computes `CSINC v3 v2 v10`, and every returning
or panicking `run` of `csi` is, up to refinement, a `runL` of the result. -/
theorem csi_lower :
    ∃ out, lowerChecked csiPassEnv csiFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 6).isSome = false ∧
      (out.func.value? 7).map (fun v => (v.op, v.args)) = some (.ARM64CSINC, #[3, 2, 10]) ∧
      (∃ f', GoFV.Proof.Low.Contract csiFunc f' ∧
        RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func csiPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem fuel, (run env lcsTabs csiFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env lcsTabs csiFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := csi_checks
  cases hc : lowerChecked csiPassEnv csiFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h6, h7, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h6, h7, GoFV.Proof.Low.lower_refines hc csi_generic,
      fun env hE args mem fuel hd => GoFV.Proof.Low.lower_refines_run hc csi_generic csi_noFma hE hd⟩

/-! ## `csh`: `CMPshiftLL` (`1463`) -/

/-- `csh`, the input of `lower` (the tables of `cvb`). -/
def cshFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 9
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[9] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8, 9])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 1 #[] 1),
    some (mkVI 2 .ArgIntReg 2 0 (some 6) p0 1 #[] 1),
    some (mkVI 3 .ArgIntReg 2 1 (some 7) p0 1 #[] 1),
    some (mkVI 4 .Const64 2 3 none p0 1 #[] 1),
    some (mkVI 5 .Lsh64x64 2 1 none p0 1 #[3, 4] 1),
    some (mkV 6 .Less64 3 none p0 1 #[2, 5] 1),
    some (mkV 7 .CvtBoolToUint8 4 none p0 1 #[6] 1),
    some (mkV 8 .ZeroExt8to64 2 none p0 1 #[7] 1),
    some (mkV 9 .MakeResult 33 none p0 1 #[8, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `csh`. -/
def cshPassEnv : PassEnv := { cvbPassEnv with funcName := GoStr.ofString "csh" }

theorem csh_generic : cshFunc.lowered = false := by decide +kernel

/-- `csh` has no fused multiply-add shape: its contraction is itself. -/
theorem csh_noFma : GoFV.Opt.FmaContract.contractAll cshFunc = cshFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose `v10` is `CMPshiftLL [3]
v2 v3` and which has no `v5`, and `csh(1, 1) = 1` under `run` of the input and `runL` of the
result. -/
theorem csh_checks :
    (lowerChecked cshPassEnv cshFunc).toOption.map (fun o =>
      ((o.func.value? 5).isSome, (o.func.value? 10).map (fun v => (v.op, v.auxInt, v.args)),
        o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [.int .w64 1, .int .w64 1] {} 1) 1)) =
      some (false, some (.ARM64CMPshiftLL, 3, #[2, 3]), true, true) ∧
    returnsInt (run Env.p1 cvbTabs cshFunc [.int .w64 1, .int .w64 1] {} 1) 1 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on `CMPshiftLL`
(`ARM64.rules:1463`): on `csh`, the checked lower computes `CMPshiftLL [3] v2 v3`, and every
returning or panicking `run` of `csh` is, up to refinement, a `runL` of the result. -/
theorem csh_lower :
    ∃ out, lowerChecked cshPassEnv cshFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 5).isSome = false ∧
      (out.func.value? 10).map (fun v => (v.op, v.auxInt, v.args)) =
        some (.ARM64CMPshiftLL, 3, #[2, 3]) ∧
      (∃ f', GoFV.Proof.Low.Contract cshFunc f' ∧
        RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func cshPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem fuel, (run env cvbTabs cshFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env cvbTabs cshFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := csh_checks
  cases hc : lowerChecked cshPassEnv cshFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h5, h10, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h5, h10, GoFV.Proof.Low.lower_refines hc csh_generic,
      fun env hE args mem fuel hd => GoFV.Proof.Low.lower_refines_run hc csh_generic csh_noFma hE hd⟩

/-! ## `cng`: `CMNconst` (`597`) -/

/-- `cng`, the input of `lower` (the tables of `cvb`). -/
def cngFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 8
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[8] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 1 #[] 1),
    some (mkVI 2 .ArgIntReg 2 0 (some 6) p0 1 #[] 1),
    some (mkVI 3 .ArgIntReg 2 1 (some 7) p0 0 #[] 1),
    some (mkVI 4 .Const64 2 (-5) none p0 1 #[] 1),
    some (mkV 5 .Less64 3 none p0 1 #[2, 4] 1),
    some (mkV 6 .CvtBoolToUint8 4 none p0 1 #[5] 1),
    some (mkV 7 .ZeroExt8to64 2 none p0 1 #[6] 1),
    some (mkV 8 .MakeResult 33 none p0 1 #[7, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `cng`. -/
def cngPassEnv : PassEnv := { cvbPassEnv with funcName := GoStr.ofString "cng" }

theorem cng_generic : cngFunc.lowered = false := by decide +kernel

/-- `cng` has no fused multiply-add shape: its contraction is itself. -/
theorem cng_noFma : GoFV.Opt.FmaContract.contractAll cngFunc = cngFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose `v9` is `CMNconst [5] v2`
and which has no `v4`, and `cng(-6, 0) = 1` under `run` of the input and `runL` of the result. -/
theorem cng_checks :
    (lowerChecked cngPassEnv cngFunc).toOption.map (fun o =>
      ((o.func.value? 4).isSome, (o.func.value? 9).map (fun v => (v.op, v.auxInt, v.args)),
        o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [.int .w64 (-6), .int .w64 0] {} 1) 1)) =
      some (false, some (.ARM64CMNconst, 5, #[2]), true, true) ∧
    returnsInt (run Env.p1 cvbTabs cngFunc [.int .w64 (-6), .int .w64 0] {} 1) 1 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on `CMNconst`
(`ARM64.rules:597`, the `CMPconst` form): on `cng`, the checked lower computes `CMNconst [5] v2`,
and every returning or panicking `run` of `cng` is, up to refinement, a `runL` of the result. -/
theorem cng_lower :
    ∃ out, lowerChecked cngPassEnv cngFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 4).isSome = false ∧
      (out.func.value? 9).map (fun v => (v.op, v.auxInt, v.args)) =
        some (.ARM64CMNconst, 5, #[2]) ∧
      (∃ f', GoFV.Proof.Low.Contract cngFunc f' ∧
        RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func cngPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem fuel, (run env cvbTabs cngFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env cvbTabs cngFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := cng_checks
  cases hc : lowerChecked cngPassEnv cngFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h4, h9, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h4, h9, GoFV.Proof.Low.lower_refines hc cng_generic,
      fun env hE args mem fuel hd => GoFV.Proof.Low.lower_refines_run hc cng_generic cng_noFma hE hd⟩

end GoFV.Proof.Witness
