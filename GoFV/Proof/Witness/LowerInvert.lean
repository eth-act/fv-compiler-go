import GoFV.Proof.Witness.LowerCondSel

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower` on `InvertFlags`: `cmax` (hand-written, issue #385)

`cmax(x, y int) int { if x < y { return y }; return x }` as `lower` sees it (entry block `b1`:
`v4 = Less64 v2 v3` of the register arguments, `If v4` to `b2`, returning `y`, and `b3`, returning
`x`). The checked lower fires `(Less64 x y) => (LessThan (CMP x y))` (`ARM64.rules:256`, a fresh
`v7 = CMP v2 v3`), `(CMP x y) && canonLessThan(x,y) => (InvertFlags (CMP y x))` (`1003`: `v7`
becomes `InvertFlags v8` of a fresh `v8 = CMP v3 v2`), `(If (LessThan cc) yes no) => (LT cc yes
no)` (`463`) and `(LT (InvertFlags cmp) yes no) => (GT cmp yes no)` (`1332`): `b1` becomes `GT
v8`, and `v7` is dead. By `lower_refines` every returning or panicking `run` of `cmax` is, up to
refinement, a `runL` of the result; `cmax(3, 4)` returns 4 and `cmax(5, 4)` returns 5 under both.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

set_option synthInstance.maxSize 1024

/-- `cmax`, the input of `lower`. -/
def invFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 6
  bidLast := 3
  blocks := #[1, 2, 3]
  blockTab := #[none,
    some (mkB 1 .If p0 #[4] #[⟨2, 0⟩, ⟨3, 0⟩] #[] #[1, 2, 3, 4]),
    some (mkB 2 .Ret p0 #[5] #[] #[⟨1, 0⟩] #[5]),
    some (mkB 3 .Ret p0 #[6] #[] #[⟨1, 1⟩] #[6])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 2 #[] 1),
    some (mkVI 2 .ArgIntReg 2 0 (some 6) p0 2 #[] 1),
    some (mkVI 3 .ArgIntReg 2 1 (some 7) p0 2 #[] 1),
    some (mkV 4 .Less64 3 none p0 1 #[2, 3] 1),
    some (mkV 5 .MakeResult 33 none p0 1 #[3, 1] 2),
    some (mkV 6 .MakeResult 33 none p0 1 #[2, 1] 3)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `inv` (`typ.Flags` is type 29). -/
def invPassEnv : PassEnv :=
  { lcsPassEnv with funcName := GoStr.ofString "cmax" }

theorem inv_generic : invFunc.lowered = false := by decide +kernel

/-- `cmax` has no fused multiply-add shape: its contraction is itself. -/
theorem inv_noFma : GoFV.Opt.FmaContract.contractAll invFunc = invFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose `b1` is `GT v8` with
`v8 = CMP v3 v2`, and `cmax(3, 4) = 4`, `cmax(5, 4) = 5` under `run` of the input and `runL` of
the result. -/
theorem inv_checks :
    (lowerChecked invPassEnv invFunc).toOption.map (fun o =>
      ((o.func.block? 1).map (fun b => (b.kind, b.auxInt, b.controls)),
        (o.func.value? 8).map (fun v => (v.op, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [.int .w64 3, .int .w64 4] {} 2) 4,
        returnsInt (runL Env.p1 o.tables o.func [.int .w64 5, .int .w64 4] {} 2) 5)) =
      some (some (.ARM64GT, 0, #[8]), some (.ARM64CMP, #[3, 2]), true, true, true) ∧
    returnsInt (run Env.p1 lcsTabs invFunc [.int .w64 3, .int .w64 4] {} 2) 4 = true ∧
    returnsInt (run Env.p1 lcsTabs invFunc [.int .w64 5, .int .w64 4] {} 2) 5 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on `InvertFlags`: on
`cmax`, the checked lower swaps the compare (`1003`) and branches by `GT` on `CMP v3 v2` (`1332`),
and every returning or panicking `run` of `cmax` is, up to refinement, a `runL` of the result. -/
theorem inv_lower :
    ∃ out, lowerChecked invPassEnv invFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.block? 1).map (fun b => (b.kind, b.auxInt, b.controls)) =
        some (.ARM64GT, 0, #[8]) ∧
      (out.func.value? 8).map (fun v => (v.op, v.args)) = some (.ARM64CMP, #[3, 2]) ∧
      (∃ f', GoFV.Proof.Low.Contract invFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.LowerCheck.roPre invPassEnv.tables invFunc) env mem)
        out.tables out.func invPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.LowerCheck.roPre invPassEnv.tables invFunc) env mem → ∀ fuel,
        (run env lcsTabs invFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env lcsTabs invFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := inv_checks
  cases hc : lowerChecked invPassEnv invFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨hb, h8, hl, -⟩ := h1
    exact ⟨out, rfl, hl, hb, h8, GoFV.Proof.Low.lower_refines hc inv_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc inv_generic inv_noFma hE hro hd⟩

end GoFV.Proof.Witness
