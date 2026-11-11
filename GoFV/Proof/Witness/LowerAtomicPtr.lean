import GoFV.Proof.Witness.LowerAtomicRmw

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower` on a pointer's atomic store: `asp` (hand-written, issue #385)

`asp() int { atomic.StorePointer((*unsafe.Pointer)(unsafe.Pointer(&g)), unsafe.Pointer(&g));
return 5 }` with a global `g` as `lower` sees it (one block: `v3 = Addr <*int> {g} v2` of `v2 =
SB`, `v4 = AtomicStorePtrNoWB v3 v3 v1`, `v5 = Const64 [5]`, returned by `v6 = MakeResult v5
v4`): the checked lower fires `(Addr {sym} base) => (MOVDaddr {sym} base)` (308), the constant's
lowering and `(AtomicStorePtrNoWB ...) => (STLR ...)` (490): `v4` becomes `STLR v3 v3 v1`, an atom
the validator pairs with the `AtomicStorePtrNoWB` (`renameOp`, `atomicRen`), which `runL` runs as
`AtomicStore64` (`GoFV.Proof.Low.Sim.atomicRoot_ptrStore`). By `lower_refines` every returning or
panicking `run` of `asp` is, up to refinement, a `runL` of the result; both store `g`'s address
into `g` and return 5.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- `asp`, the input of `lower` (on `ald`'s tables). -/
def aspFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 6
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[6] #[] #[] #[1, 2, 3, 4, 5, 6])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 1 #[] 1),
    some (mkV 2 .SB 4 none p0 1 #[] 1),
    some (mkV 3 .Addr 3 (some 4) p0 2 #[2] 1),
    some (mkV 4 .AtomicStorePtrNoWB 28 none p0 1 #[3, 3, 1] 1),
    some (mkVI 5 .Const64 2 5 none p0 1 #[] 1),
    some (mkV 6 .MakeResult 33 none p0 1 #[5, 4] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `asp`. -/
def aspPassEnv : PassEnv :=
  { aldPassEnv with funcName := GoStr.ofString "asp" }

theorem asp_generic : aspFunc.lowered = false := by decide +kernel

/-- `asp` has no fused multiply-add shape: its contraction is itself. -/
theorem asp_noFma : GoFV.Opt.FmaContract.contractAll aspFunc = aspFunc := by decide +kernel

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 200000 in
/-- By kernel evaluation: the checked lower keeps a lowered result whose `v4` is `STLR v3 v3 v1`,
and `asp` returns 5 under `run` of the input and `runL` of the result. -/
theorem asp_checks :
    (lowerChecked aspPassEnv aspFunc).toOption.map (fun o =>
      ((o.func.value? 4).map (fun v => (v.op, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [] aadMem 1) 5)) =
      some (some (.ARM64STLR, #[3, 3, 1]), true, true) ∧
    returnsInt (run Env.p1 aldTabs aspFunc [] aadMem 1) 5 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a pointer's atomic
store: on `asp`, the checked lower lowers `AtomicStorePtrNoWB` to `STLR` (`ARM64.rules:490`), and
every returning or panicking `run` of `asp` is, up to refinement, a `runL` of the result. -/
theorem asp_lower :
    ∃ out, lowerChecked aspPassEnv aspFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 4).map (fun v => (v.op, v.args)) = some (.ARM64STLR, #[3, 3, 1]) ∧
      (∃ f', GoFV.Proof.Low.Contract aspFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.LowerCheck.roPre aspPassEnv.tables aspFunc) env mem)
        out.tables out.func aspPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.LowerCheck.roPre aspPassEnv.tables aspFunc) env mem → ∀ fuel,
        (run env aldTabs aspFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env aldTabs aspFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := asp_checks
  cases hc : lowerChecked aspPassEnv aspFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h4, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h4, GoFV.Proof.Low.lower_refines hc asp_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc asp_generic asp_noFma hE hro hd⟩

end GoFV.Proof.Witness
