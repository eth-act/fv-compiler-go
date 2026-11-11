import GoFV.Proof.Witness.LowerLoadFold

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower` folding an offset into a store: `sto` (hand-written, issue #385)

`sto(p *[2]int) int { p[1] = 5; return p[1] }` as `lower` sees it (one block: `v3 = OffPtr <*int>
[8] v2` of the register argument `v2`, `v5 = Store {int} v3 v4 v1` of the constant `v4 = Const64
[5]`, `v6 = Load <int> v3 v5`, returned by `v7 = MakeResult v6 v5`). The checked lower with the
proven `ARM64.rules` fires `(OffPtr [off] ptr) => (ADDconst [off] ptr)` (306), `(Store {t} ptr val
mem) && t.Size() == 8 && !t.IsFloat() => (MOVDstore ptr val mem)` (329) and then `(MOVDstore
[off1] {sym} (ADDconst [off2] ptr) val mem) && … => (MOVDstore [off1+int32(off2)] {sym} ptr val
mem)` (767), so `v5` becomes `MOVDstore [8] v2 v4 v1` (the validator's `stFold`); the load folds
likewise (676). By `lower_refines` every returning or panicking `run` of `sto` is, up to
refinement, a `runL` of the result; on a 16-byte heap block both return 5.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- `sto`: the tables of `ldst` (`*int` is type 3, the `Store`'s type aux 6). -/
def stoFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 7
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[7] #[] #[] #[1, 2, 3, 4, 5, 6, 7])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 1 #[] 1),
    some (mkVI 2 .ArgIntReg 3 0 (some 5) p0 1 #[] 1),
    some (mkVI 3 .OffPtr 3 8 none p0 2 #[2] 1),
    some (mkVI 4 .Const64 2 5 none p0 1 #[] 1),
    some (mkV 5 .Store 28 (some 6) p0 2 #[3, 4, 1] 1),
    some (mkV 6 .Load 2 none p0 1 #[3, 5] 1),
    some (mkV 7 .MakeResult 33 none p0 1 #[6, 5] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

theorem sto_generic : stoFunc.lowered = false := by decide +kernel

/-- `sto` has no fused multiply-add shape: its contraction is itself. -/
theorem sto_noFma : GoFV.Opt.FmaContract.contractAll stoFunc = stoFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose `v5` is `MOVDstore [8] v2
v4 v1`, and `sto` returns 5 under `run` of the input and `runL` of the result (on `ldo`'s 16-byte
heap block). -/
theorem sto_checks :
    (lowerChecked ldsPassEnv stoFunc).toOption.map (fun o =>
      ((o.func.value? 5).map (fun v => (v.op, v.auxInt, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func ldsArgs ldoMem 1) 5)) =
      some (some (.ARM64MOVDstore, 8, #[2, 4, 1]), true, true) ∧
    returnsInt (run Env.p1 ldsTabs stoFunc ldsArgs ldoMem 1) 5 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on an offset folded into a
store: on `sto`, the checked lower folds the `OffPtr`'s offset into the store (`MOVDstore [8] v2 v4
v1`), and every returning or panicking `run` of `sto` is, up to refinement, a `runL` of the
result. -/
theorem sto_lower :
    ∃ out, lowerChecked ldsPassEnv stoFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 5).map (fun v => (v.op, v.auxInt, v.args)) =
        some (.ARM64MOVDstore, 8, #[2, 4, 1]) ∧
      (∃ f', GoFV.Proof.Low.Contract stoFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.RewriteCheck.roSyms ldsPassEnv.tables stoFunc) env mem)
        out.tables out.func ldsPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.RewriteCheck.roSyms ldsPassEnv.tables stoFunc) env mem → ∀ fuel,
        (run env ldsTabs stoFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env ldsTabs stoFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := sto_checks
  cases hc : lowerChecked ldsPassEnv stoFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h5, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h5, GoFV.Proof.Low.lower_refines hc sto_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc sto_generic sto_noFma hE hro hd⟩

end GoFV.Proof.Witness
