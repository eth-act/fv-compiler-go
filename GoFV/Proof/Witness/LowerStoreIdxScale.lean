import GoFV.Proof.Witness.LowerStoreIdx

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness for an indexed store's index scaled in `lower`: `sts` (hand-written, issue #385)

`sts` is `sti` (`GoFV.Proof.Witness.LowerStoreIdx`: `*(*int)(unsafe.Add(p, i<<3)) = 5; return 5`)
with the `Store` `v6` listed before the `AddPtr` `v4` it stores at. `lower` then rewrites `v6` to
`MOVDstore v4 v5 v1` while `v4` is still the `AddPtr`, `v4` to `ADD v2 v8` (`v8 = SLLconst [3] v3`),
then `v6` to `MOVDstoreidx v2 v8 v5 v1` (`ARM64.rules:786`), and only then `v6` to `MOVDstoreidx8
v2 v3 v5 v1`: `(MOVDstoreidx ptr (SLLconst [3] idx) val mem) => (MOVDstoreidx8 ptr idx val mem)`
(`809`), which the validator replays by `stIdxScale` (`sts_scale` checks that event on the
replayed definitions) and `GoFV.Proof.Low.Val.ReplayInvL.scaleIdx` proves. By `lower_refines`
every returning or panicking `run` of `sts` is, up to refinement, a `runL` of the result; on a
16-byte heap block and the index 1 both store 5 at offset 8 and return 5.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- `sts`: `sti` with the `Store` before the `AddPtr` in the block. -/
def stsFunc : Func :=
  { stxFunc true with
    blockTab := #[none, some (mkB 1 .Ret p0 #[9] #[] #[] #[1, 2, 3, 7, 8, 6, 4, 5, 9])] }

theorem sts_generic : stsFunc.lowered = false := by decide +kernel

/-- `sts` has no fused multiply-add shape: its contraction is itself. -/
theorem sts_noFma : GoFV.Opt.FmaContract.contractAll stsFunc = stsFunc := by decide +kernel

/-- The replayed definitions at the `809` event: `v6 = MOVDstoreidx v2 v8 v5 v1` on `v8 =
SLLconst [3] v3`. -/
def stsM : GoFV.Opt.RewriteCheck.Defs := #[none,
  some (mkV 1 .InitMem 28 none p0 1 #[] 1),
  some (mkVI 2 .ArgIntReg 3 0 (some 6) p0 1 #[] 1),
  some (mkVI 3 .ArgIntReg 2 1 (some 7) p0 1 #[] 1),
  some (mkV 4 .ARM64ADD 3 none p0 1 #[2, 8] 1),
  some (mkVI 5 .ARM64MOVDconst 2 5 none p0 2 #[] 1),
  some (mkV 6 .ARM64MOVDstoreidx 28 none p0 1 #[2, 8, 5, 1] 1),
  some (mkVI 7 .ARM64MOVDconst 2 3 none p0 1 #[] 1),
  some (mkVI 8 .ARM64SLLconst 2 3 none p0 1 #[3] 1),
  some (mkV 9 .MakeResult 33 none p0 1 #[5, 6] 1)]

/-- By kernel evaluation: the validator accepts the `809` event at `v6` of `sts` (`stIdxScale`,
`v6`'s source a `Store` on three arguments). -/
theorem sts_scale :
    GoFV.Opt.LowerCheck.atomDef stxTabs stsFunc stsM 6
        [mkV 6 .ARM64MOVDstoreidx 28 none p0 1 #[2, 8, 5, 1] 1,
          mkV 6 .ARM64MOVDstoreidx8 28 none p0 1 #[2, 3, 5, 1] 1] =
      some (mkV 6 .ARM64MOVDstoreidx8 28 none p0 1 #[2, 3, 5, 1] 1, none) ∧
    GoFV.Opt.LowerCheck.stIdxScale stxTabs stsM
        (mkV 6 .ARM64MOVDstoreidx 28 none p0 1 #[2, 8, 5, 1] 1)
        (mkV 6 .ARM64MOVDstoreidx8 28 none p0 1 #[2, 3, 5, 1] 1) = true := by
  decide +kernel

set_option synthInstance.maxSize 2048 in
/-- By kernel evaluation: the checked lower keeps a lowered result whose `v6` is `MOVDstoreidx8 v2
v3 v5 v1`, and both return 5 under `run` of the input and `runL` of the result. -/
theorem sts_checks :
    (lowerChecked stxPassEnv stsFunc).toOption.map (fun o =>
      ((o.func.value? 6).map (fun v => (v.op, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func (stxArgs true) ldxMem 1) 5)) =
      some (some (.ARM64MOVDstoreidx8, #[2, 3, 5, 1]), true, true) ∧
    returnsInt (run Env.p1 stxTabs stsFunc (stxArgs true) ldxMem 1) 5 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a scaled index: on
`sts` the checked lower rewrites the store's `MOVDstoreidx v2 (SLLconst [3] v3) v5 v1` to
`MOVDstoreidx8 v2 v3 v5 v1` (`ARM64.rules:809`), and every returning or panicking `run` is, up to
refinement, a `runL` of the result. -/
theorem sts_lower :
    ∃ out, lowerChecked stxPassEnv stsFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 6).map (fun v => (v.op, v.args)) =
        some (.ARM64MOVDstoreidx8, #[2, 3, 5, 1]) ∧
      (∃ f', GoFV.Proof.Low.Contract stsFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.LowerCheck.roPre stxPassEnv.tables stsFunc) env mem)
        out.tables out.func stxPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.LowerCheck.roPre stxPassEnv.tables stsFunc) env mem → ∀ fuel,
        (run env stxTabs stsFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env stxTabs stsFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := sts_checks
  cases hc : lowerChecked stxPassEnv stsFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h6, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h6, GoFV.Proof.Low.lower_refines hc sts_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc sts_generic sts_noFma hE hro hd⟩

end GoFV.Proof.Witness
