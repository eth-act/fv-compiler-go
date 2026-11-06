import GoFV.Proof.Pass.SchedLPass
import GoFV.Proof.Witness.SchedL
import GoFV.Proof.Witness.LowCong
import GoFV.Proof.Witness.DeadcodeL
import GoFV.Proof.Witness.Util
import GoFV.Proof.RunLFCases

/-!
# Non-vacuity witness: `schedule` on lowered `clamp`

`schedule` (`GoFV.Opt.schedulePass`) runs on `clampL` (by kernel evaluation): it lists `b1`'s
values in Go's order `v8 v9 v10 v1 v22` (`clampS`'s blocks, section 53 of the corpus), and
`scheduleCheck` accepts the output. `clampL` has no pointer-shaped parameter piece and no nil
check, so `ArgPtrsOK` and `NilPtrsOK` hold on every input (`argPtrsOK_of_none`,
`nilPtrsOK_of_none`), and by `schedule_refinesSchedLF` the output's `runSched` returns
`clamp(5, 0, 10) = 5`, as `runLF` of `clampL` does (`clampL_runLF`). `clampL` has no memory op
and no nil check, so `runLF` is `runL` on it (`noNilFault_of_noAct`) and `schedule_refinesSchedL`
reads the same off `runL` (`clampL_run5`).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof GoFV.Proof.SchedL GoFV.Opt.ScheduleCheck

/-- A pass environment for `schedule` on lowered `clamp` (`optimize 1`; the SSA pseudo-types). -/
def clampSchedPassEnv : PassEnv :=
  { clampLPassEnv "schedule" with
    config := #[("arch", #[.word "arm64"]), ("hasgreg", #[.word "1"]), ("optimize", #[.word "1"])]
    typs := #[("Mem", 28), ("Flags", 29), ("Void", 0)] }

theorem clampL_check : (check clampLCheckEnv clampL).toBool = true := by decide +kernel

/-- `schedule` accepts `clampL`, its output has `clampS`'s blocks and `scheduleCheck` holds. -/
theorem clampL_schedule_facts :
    ((schedulePass clampSchedPassEnv clampL).toOption.map fun o =>
      decide (scheduleCheck clampLTabs clampL o.func = true ∧ o.func.blockTab = clampSBlocks)) =
      some true := by
  decide +kernel

/-- `clampL` has no pointer-shaped register piece of a parameter (its `ArgIntReg`s are integers). -/
theorem clampL_noArgPtr :
    (List.range clampL.valueTab.size).all
      (fun x => !argPtr clampLTabs (Ctx.makeL clampLTabs clampL).params
        (Ctx.makeL clampLTabs clampL).tys clampL x) = true := by
  decide +kernel

/-- No nil check of `clampL` checks a pointer-shaped value (it has no nil check). -/
theorem clampL_noNilPtr :
    clampL.valueTab.all (fun o => o.all fun v => !v.op.nilCheck ||
      (v.args[0]?.all fun q => !ptrShape ((Ctx.makeL clampLTabs clampL).tys[q]?.getD .other))) =
      true := by
  decide +kernel

/-- **`schedule_refinesSchedLF` is not vacuous**: `schedule` accepts `clampL`, `scheduleCheck`
accepts its output, and the output's `runSched` returns `clamp(5, 0, 10) = 5`. -/
theorem schedule_witness :
    ∃ out, schedulePass clampSchedPassEnv clampL = .ok out ∧
      scheduleCheck clampLTabs clampL out.func = true ∧ out.func.blockTab = clampSBlocks ∧
      ∃ fuel m, runSched Env.p1 out.tables out.func (clampArgs 5) {} fuel = .returned [.i64 5] m := by
  obtain ⟨out, hp, hv, hb⟩ := ok_of_toOption
    (P := fun o => scheduleCheck clampLTabs clampL o.func = true ∧ o.func.blockTab = clampSBlocks)
    clampL_schedule_facts
  refine ⟨out, hp, hv, hb, ?_⟩
  obtain ⟨m, hm⟩ := returnsInt_iff.1 clampL_runLF.1
  exact (schedule_refinesSchedLF (penv := clampSchedPassEnv) hp (ok_of_toBool clampL_check) hv).returned_int
    ⟨argPtrsOK_of_none clampL_noArgPtr Env.p1 (clampArgs 5) {},
      nilPtrsOK_of_none clampL_noNilPtr Env.p1 (clampArgs 5) {}⟩ hm

/-- `clampL` has no value evaluated by `arm64Op`. -/
theorem clampL_noAct :
    clampL.valueTab.all (fun o => o.all fun v => !ScheduleCheck.actOp v.op) = true := by
  decide +kernel

/-- **`schedule_refinesSchedL` is not vacuous**: on `clampL`'s inputs (no nil-page access), the
output's `runSched` returns `runL`'s `clamp(5, 0, 10) = 5`. -/
theorem schedule_refinesSchedL_witness :
    ∃ out, schedulePass clampSchedPassEnv clampL = .ok out ∧
      ∃ fuel m, runSched Env.p1 out.tables out.func (clampArgs 5) {} fuel = .returned [.i64 5] m := by
  obtain ⟨out, hp, hv, -⟩ := ok_of_toOption
    (P := fun o => scheduleCheck clampLTabs clampL o.func = true ∧ o.func.blockTab = clampSBlocks)
    clampL_schedule_facts
  refine ⟨out, hp, ?_⟩
  obtain ⟨m, hm⟩ := clampL_run5
  obtain ⟨fuel', ho⟩ := schedule_refinesSchedL (penv := clampSchedPassEnv) hp
    (ok_of_toBool clampL_check) hv Env.p1 (clampArgs 5) {}
    ⟨noNilFault_of_noAct clampL_noAct Env.p1 (clampArgs 5) {},
      argPtrsOK_of_none clampL_noArgPtr Env.p1 (clampArgs 5) {},
      nilPtrsOK_of_none clampL_noNilPtr Env.p1 (clampArgs 5) {}⟩ 3
    (by show (runL Env.p1 clampLTabs clampL (clampArgs 5) {} 3).Defined; rw [hm]; trivial)
  change OutcomeRefines 0 (runL Env.p1 clampLTabs clampL (clampArgs 5) {} 3) _ at ho
  rw [hm] at ho
  refine ⟨fuel', ?_⟩
  generalize runSched Env.p1 out.tables out.func (clampArgs 5) {} fuel' = o at ho ⊢
  cases ho with
  | @returned _ _ _ m' hl _ =>
    cases hl with
    | cons h1 t =>
      cases t
      cases h1
      exact ⟨m', rfl⟩

/-- **`swapOK`'s `argOK` case is not vacuous**: `clampL`'s `x` (`v8`, an `ArgIntReg` of
parameter `x`) is a parameter's register piece, so `scheduleCheck` lets the target run it before
any value that may fail (`evalValueL_argOK`: it evaluates). -/
theorem clampL_argOK :
    argOK clampLTabs (Ctx.makeL clampLTabs clampL).params
      (mkVI 8 .ArgIntReg 2 0 (some 7) (pos 2 22 7 0) 3 #[] 1) = true := by
  decide +kernel

/-- `clampL` plus `v25 = LoweredNilCheck v8 v1` in `b1`. -/
def clampNC : Func :=
  { clampL with
    vidLast := 25
    valueTab := clampLValues.push (some (mkV 25 .ARM64LoweredNilCheck 0 none p0 1 #[8, 1] 1)) }

/-- **`swapOK`'s `nnBase` case is not vacuous**: a load `MOVDload v25 v1` whose pointer is a nil
check's result never faults, so `swapOK` lets the target run a later failing value before it. -/
theorem clampNC_nnBase :
    nnBase clampLTabs #[] clampNC (mkV 26 .ARM64MOVDload 2 none p0 1 #[25, 1] 1) = true := by
  decide +kernel

/-- `clampL` plus `v25 = MOVDload v9 v1` and `v26 = LoweredNilCheck v8 v1` in `b1`. -/
def clampAP : Func :=
  { clampL with
    vidLast := 26
    valueTab := (clampLValues.push (some (mkV 25 .ARM64MOVDload 2 none p0 1 #[9, 1] 1))).push
      (some (mkV 26 .ARM64LoweredNilCheck 0 none p0 1 #[8, 1] 1)) }

/-- Shapes of `clampAP` with `v8` (parameter `x`'s register piece) a pointer. -/
def clampAPTys : Array Ty := (Array.replicate 27 Ty.other).set! 8 (.ptr none)

/-- **`swapOK`'s `argPtr` case is not vacuous**: with the source order `v1 v8 v9 v10 v25 v26 v22`,
the target may run the nil check `v26` of the pointer-shaped parameter piece `v8` (listed before
the load) before the load `v25` on the same memory, and only through the source positions: without
them (`#[]`) no case of `swapOK` holds. -/
theorem clampAP_argPtr :
    swapOK clampLTabs (Ctx.makeL clampLTabs clampAP).params clampAPTys clampAP
        (srcPos 27 [1, 8, 9, 10, 25, 26, 22]) 25 26 = true ∧
      swapOK clampLTabs (Ctx.makeL clampLTabs clampAP).params clampAPTys clampAP #[] 25 26 =
        false := by
  decide +kernel

/-- **`swapOK`'s `argPtr` case for a piece outside the block is not vacuous**: with the source
order `v1 v9 v10 v25 v26 v22` of a block without `v8` (the pointer-shaped parameter piece), the
target may run the nil check `v26` of `v8` before the load `v25` on the same memory; with `v8`
listed after the load it may not. -/
theorem clampAP_argPtrOut :
    swapOK clampLTabs (Ctx.makeL clampLTabs clampAP).params clampAPTys clampAP
        (srcPos 27 [1, 9, 10, 25, 26, 22]) 25 26 = true ∧
      swapOK clampLTabs (Ctx.makeL clampLTabs clampAP).params clampAPTys clampAP
        (srcPos 27 [1, 9, 10, 25, 8, 26, 22]) 25 26 = false := by
  decide +kernel

/-- `clampL` plus `v25 = LDAR v9 v1` and `v26 = MOVDload v8 v1` in `b1`. -/
def clampLD : Func :=
  { clampL with
    vidLast := 26
    valueTab := (clampLValues.push (some (mkV 25 .ARM64LDAR 0 none p0 1 #[9, 1] 1))).push
      (some (mkV 26 .ARM64MOVDload 2 none p0 1 #[8, 1] 1)) }

/-- **`swapOK`'s load case covers `LDAR`** (a `faultOp`, `Cls.load`): the target may run the load
`v26` before the acquiring load `v25` on the same memory, whichever faults first panics with
`nilDeref` of it. -/
theorem clampLD_ldar :
    cls clampLTabs (mkV 25 .ARM64LDAR 0 none p0 1 #[9, 1] 1) = .load ∧
      swapOK clampLTabs (Ctx.makeL clampLTabs clampLD).params #[] clampLD
        (srcPos 27 [1, 8, 9, 10, 25, 26, 22]) 25 26 = true := by
  decide +kernel

/-- `clampL` plus `v25 = MOVDload v9 v1` (a loaded pointer), `v26 = MOVDload v8 v1` and
`v27 = LoweredNilCheck v25 v1` in `b1`. -/
def clampNP : Func :=
  { clampL with
    vidLast := 27
    valueTab := ((clampLValues.push (some (mkV 25 .ARM64MOVDload 2 none p0 1 #[9, 1] 1))).push
      (some (mkV 26 .ARM64MOVDload 2 none p0 1 #[8, 1] 1))).push
      (some (mkV 27 .ARM64LoweredNilCheck 0 none p0 1 #[25, 1] 1)) }

/-- Shapes of `clampNP` with `v25` a pointer. -/
def clampNPTys : Array Ty := (Array.replicate 28 Ty.other).set! 25 (.ptr none)

/-- **`swapOK`'s `NilPtrsOK` case (`nilPtrSwap`) is not vacuous**: with the source order
`v1 v8 v9 v10 v25 v26 v27 v22`, the target may run the nil check `v27` of the loaded pointer
`v25` before the load `v26` on the same memory, only through `nilPtrSwap` (`swapOKB` rejects the
swap); with `v25` listed after the load it may not. -/
theorem clampNP_nilPtr :
    swapOK clampLTabs (Ctx.makeL clampLTabs clampNP).params clampNPTys clampNP
        (srcPos 28 [1, 8, 9, 10, 25, 26, 27, 22]) 26 27 = true ∧
      swapOKB clampLTabs (Ctx.makeL clampLTabs clampNP).params clampNPTys clampNP
        (srcPos 28 [1, 8, 9, 10, 25, 26, 27, 22]) 26 27 = false ∧
      swapOK clampLTabs (Ctx.makeL clampLTabs clampNP).params clampNPTys clampNP
        (srcPos 28 [1, 8, 9, 10, 26, 25, 27, 22]) 26 27 = false := by
  decide +kernel

end GoFV.Proof.Witness
