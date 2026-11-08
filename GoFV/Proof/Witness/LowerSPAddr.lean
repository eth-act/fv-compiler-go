import GoFV.Proof.Witness.LowerStoreSym

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower` on the stack pointer moved by an offset: `osp` (hand-written, issue #385)

`osp() int { g = &outargs[1]; return 5 }` with a global `g` of type `*int`, as `lower` sees it
(one block: `v3 = Addr <**int> {g} v2` of `v2 = SB`, `v4 = SP`, `v5 = OffPtr <*int> [8] v4`,
`v6 = Store {*int} v3 v5 v1`, `v7 = Const64 [5]`, returned by `v8 = MakeResult v7 v6`). The checked
lower fires `(OffPtr [off] ptr:(SP)) && is32Bit(off) => (MOVDaddr [int32(off)] ptr)` (305) at `v5`,
which the replay keeps as `OffPtr` (`spFoldEv`), so `v5` is `MOVDaddr [8] v4`: a term of the output
the store reads, which the validator relates to the replayed `OffPtr [8]` of `f`'s `SP`
(`spFinal`); the source's `SP` holds the stack pointer of activation 0 (`SPVals`, `RegsFrame`). By
`lower_refines` every returning or panicking `run` of `osp` is, up to refinement, a `runL` of the
result; both return 5.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

-- `DecidableEq` of the nested options of tuples below exceeds the default instance size.
set_option synthInstance.maxSize 1024

/-- The definition tables of `osp`: `gst`'s, `**int` (type 5), the global `main.g` (aux 4) of
type `*int` and the `Store`'s type aux `*int` (6). -/
def ospTabs : Tables :=
  { gstTabs with
    types := gstTabs.types.set! 5 (some (mkT .PTR (some 8) "**int" (.elem 3)))
    auxes := gstTabs.auxes.push (some { fmt := GoStr.ofString "*int", kind := .type 3 }) }

/-- `osp`, the input of `lower`. -/
def ospFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 8
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[8] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 1 #[] 1),
    some (mkV 2 .SB 4 none p0 1 #[] 1),
    some (mkV 3 .Addr 5 (some 4) p0 1 #[2] 1),
    some (mkV 4 .SP 4 none p0 1 #[] 1),
    some (mkVI 5 .OffPtr 3 8 none p0 1 #[4] 1),
    some (mkV 6 .Store 28 (some 6) p0 1 #[3, 5, 1] 1),
    some (mkVI 7 .Const64 2 5 none p0 1 #[] 1),
    some (mkV 8 .MakeResult 33 none p0 1 #[7, 6] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `osp`. -/
def ospPassEnv : PassEnv :=
  { gstPassEnv with funcName := GoStr.ofString "osp", tables := ospTabs }

theorem osp_generic : ospFunc.lowered = false := by decide +kernel

/-- `osp` has no fused multiply-add shape: its contraction is itself. -/
theorem osp_noFma : GoFV.Opt.FmaContract.contractAll ospFunc = ospFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose `v5` is `MOVDaddr [8] v4`
and whose `v6` stores it, and `osp` returns 5 under `run` of the input and `runL` of the result. -/
theorem osp_checks :
    (lowerChecked ospPassEnv ospFunc).toOption.map (fun o =>
      ((o.func.value? 5).map (fun v => (v.op, v.auxInt, v.aux, v.args)),
        (o.func.value? 6).map (fun v => (v.op, v.args[1]?)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [] gstMem 1) 5)) =
      some (some (.ARM64MOVDaddr, 8, none, #[4]), some (.ARM64MOVDstore, some 5), true, true) ∧
    returnsInt (run Env.p1 ospTabs ospFunc [] gstMem 1) 5 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on the stack pointer moved
by an offset: on `osp`, the checked lower's `v5` is `MOVDaddr [8] v4` of `SP` (the replay's
`OffPtr [8]`, `spFinal`), stored by `v6`, and every returning or panicking `run` of `osp` is, up to
refinement, a `runL` of the result. -/
theorem osp_lower :
    ∃ out, lowerChecked ospPassEnv ospFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 5).map (fun v => (v.op, v.auxInt, v.aux, v.args)) =
        some (.ARM64MOVDaddr, 8, none, #[4]) ∧
      (out.func.value? 6).map (fun v => (v.op, v.args[1]?)) = some (.ARM64MOVDstore, some 5) ∧
      (∃ f', GoFV.Proof.Low.Contract ospFunc f' ∧
        RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func ospPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem fuel, (run env ospTabs ospFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env ospTabs ospFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := osp_checks
  cases hc : lowerChecked ospPassEnv ospFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h5, h6, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h5, h6, GoFV.Proof.Low.lower_refines hc osp_generic,
      fun env hE args mem fuel hd => GoFV.Proof.Low.lower_refines_run hc osp_generic osp_noFma hE hd⟩

end GoFV.Proof.Witness
