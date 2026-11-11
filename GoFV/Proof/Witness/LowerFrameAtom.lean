import GoFV.Proof.Witness.LowerLocalAddr

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower` on a frame address at offset 0: `fpa` (hand-written, issue #385)

`fpa() int { var x int; var y *int; x = 5; y = &x; return *y }` as `lower` sees it when `&x` is
`&x[0]`-like, an `OffPtr [0]` of the frame address (one block: `v4 = LocalAddr <*int> {x} v2 v1`
and `v6 = LocalAddr <**int> {y} v2 v5` of `v2 = SP`, `v5 = Store {int} v4 v3 v1` of `v3 = Const64
[5]`, `v7 = OffPtr <*int> [0] v4`, `v8 = Store {*int} v6 v7 v5`, the loads `v9 = Load <*int> v6 v8`
and `v10 = Load <int> v9 v8`, returned by `v11 = MakeResult v10 v8`). The checked lower fires
`(OffPtr [off] ptr) => (ADDconst [off] ptr)` (306) at `v7` and folds the lowered frame address into
it, `(ADDconst [off1] (MOVDaddr [off2] {sym} ptr)) => (MOVDaddr [off1+off2] {sym} ptr)` (650), so
`v7` is `MOVDaddr {x} v2`: an atom of the output where the input has a term (`frameAtomG`), which
the validator relates to the replayed `ADDconst [0]` of `x`'s address (`frameFinal`). The stored
value is that atom, `x`'s address word in activation 0 (`FrameValsL`, `RegsFrameL`). By
`lower_refines` every returning or panicking `run` of `fpa` is, up to refinement, a `runL` of the
result; both return 5.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

-- `DecidableEq` of the nested options of tuples below exceeds the default instance size.
set_option synthInstance.maxSize 1024

/-- `fpa`, the input of `lower` (the tables of `lad`). -/
def fpaFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 11
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[11] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 2 #[] 1),
    some (mkV 2 .SP 4 none p0 2 #[] 1),
    some (mkVI 3 .Const64 2 5 none p0 1 #[] 1),
    some (mkV 4 .LocalAddr 3 (some 4) p0 2 #[2, 1] 1),
    some (mkV 5 .Store 28 (some 6) p0 2 #[4, 3, 1] 1),
    some (mkV 6 .LocalAddr 5 (some 5) p0 2 #[2, 5] 1),
    some (mkVI 7 .OffPtr 3 0 none p0 1 #[4] 1),
    some (mkV 8 .Store 28 (some 7) p0 3 #[6, 7, 5] 1),
    some (mkV 9 .Load 3 none p0 1 #[6, 8] 1),
    some (mkV 10 .Load 2 none p0 1 #[9, 8] 1),
    some (mkV 11 .MakeResult 33 none p0 1 #[10, 8] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `fpa`. -/
def fpaPassEnv : PassEnv := { ladPassEnv with funcName := GoStr.ofString "fpa" }

theorem fpa_generic : fpaFunc.lowered = false := by decide +kernel

/-- `fpa` has no fused multiply-add shape: its contraction is itself. -/
theorem fpa_noFma : GoFV.Opt.FmaContract.contractAll fpaFunc = fpaFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose `v7` is `MOVDaddr {x} v2`
and whose `v8` stores it, and `fpa` returns 5 under `run` of the input and `runL` of the
result. -/
theorem fpa_checks :
    (lowerChecked fpaPassEnv fpaFunc).toOption.map (fun o =>
      ((o.func.value? 7).map (fun v => (v.op, v.auxInt, v.aux, v.args)),
        (o.func.value? 8).map (fun v => (v.op, v.args.size, v.args[1]?)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [] {} 1) 5)) =
      some (some (.ARM64MOVDaddr, 0, some 4, #[2]), some (.ARM64MOVDstore, 3, some 7), true,
        true) ∧
    returnsInt (run Env.p1 ladTabs fpaFunc [] {} 1) 5 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a frame address at
offset 0 where the input has a term: on `fpa`, the checked lower's `v7` is `MOVDaddr {x} v2` (the
`OffPtr [0]` of `x`'s address folded, `frameAtomG`/`frameFinal`), stored by `v8`, and every
returning or panicking `run` of `fpa` is, up to refinement, a `runL` of the result. -/
theorem fpa_lower :
    ∃ out, lowerChecked fpaPassEnv fpaFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 7).map (fun v => (v.op, v.auxInt, v.aux, v.args)) =
        some (.ARM64MOVDaddr, 0, some 4, #[2]) ∧
      (out.func.value? 8).map (fun v => (v.op, v.args.size, v.args[1]?)) =
        some (.ARM64MOVDstore, 3, some 7) ∧
      (∃ f', GoFV.Proof.Low.Contract fpaFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.LowerCheck.roPre fpaPassEnv.tables fpaFunc) env mem)
        out.tables out.func fpaPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.LowerCheck.roPre fpaPassEnv.tables fpaFunc) env mem → ∀ fuel,
        (run env ladTabs fpaFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env ladTabs fpaFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := fpa_checks
  cases hc : lowerChecked fpaPassEnv fpaFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h7, h8, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h7, h8, GoFV.Proof.Low.lower_refines hc fpa_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc fpa_generic fpa_noFma hE hro hd⟩

end GoFV.Proof.Witness
