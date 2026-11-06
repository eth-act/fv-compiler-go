import GoFV.Proof.Witness.LowerAdd

/-!
# Witness function for `lower` on a `CondSelect`: `smin` (hand-written, issue #385)

`smin(x, y int) int { if x < y { return x }; return y }` after branchelim, as `lower` sees it (one
block: `v4 = Less64 v2 v3` of the register arguments, `v5 = CondSelect <int> v2 v3 v4`, returned by
`v6 = MakeResult v5 v1`). The checked lower fires `(Less64 x y) => (LessThan (CMP x y))`
(`ARM64.rules:256`, a fresh `v7 = CMP v2 v3`), `(CMP x y) && canonLessThan(x,y) => (InvertFlags
(CMP y x))` (`1003`: `v7` becomes `InvertFlags v8` of a fresh `v8 = CMP v3 v2`), then
`(CondSelect x y boolval) && flagArg(boolval) != nil => (CSEL [boolval.Op] x y flagArg(boolval))`
(`302`) in its split form on `LessThan` (`GoFV.Rules.Derive.flagSplit`): `v5` becomes `CSEL
[LessThan] v2 v3 v7` and `v4` is dead. `CSEL` reads `LT` on the flags of the swapped compare
(`Sem.invertFlags`). By `lower_refines` every returning or panicking `run` of `smin` is, up to
refinement, a `runL` of the result; `smin(3, 4)` returns 3 and `smin(5, 4)` returns 4 under both.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

-- `DecidableEq` of the nested options of tuples below exceeds the default instance size.
set_option synthInstance.maxSize 1024

/-- The definition tables of `smin`: `add`'s, `bool` (type 3) and `flags` (29). -/
def lcsTabs : Tables :=
  { laTabs with
    types := (laTabs.types.set! 3 (some (mkT .BOOL (some 1) "bool"))).set! 29
      (some (mkT .SSA none "flags")) }

/-- `smin`, the input of `lower`. -/
def lcsFunc : Func where
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
    some (mkVI 3 .ArgIntReg 2 1 (some 7) p0 2 #[] 1),
    some (mkV 4 .Less64 3 none p0 1 #[2, 3] 1),
    some (mkV 5 .CondSelect 2 none p0 1 #[2, 3, 4] 1),
    some (mkV 6 .MakeResult 33 none p0 1 #[5, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `smin` (`typ.Flags` is type 29). -/
def lcsPassEnv : PassEnv :=
  { laPassEnv with funcName := GoStr.ofString "smin", tables := lcsTabs,
                   typs := #[("Int", 2), ("Bool", 3), ("Mem", 28), ("Flags", 29), ("Void", 31)] }

theorem lcs_generic : lcsFunc.lowered = false := by decide +kernel

/-- `smin` has no fused multiply-add shape: its contraction is itself. -/
theorem lcs_noFma : GoFV.Opt.FmaContract.contractAll lcsFunc = lcsFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose `v5` is `CSEL
[LessThan] v2 v3 v7`, `v7` `InvertFlags v8` and `v8` `CMP v3 v2`, and `smin(3, 4) = 3`,
`smin(5, 4) = 4` under `run` of the input and `runL` of the result. -/
theorem lcs_checks :
    (lowerChecked lcsPassEnv lcsFunc).toOption.map (fun o =>
      ((o.func.value? 5).map (fun v => (v.op, v.auxInt, v.args)),
        (o.func.value? 7).map (fun v => (v.op, v.args)),
        (o.func.value? 8).map (fun v => (v.op, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [.int .w64 3, .int .w64 4] {} 1) 3,
        returnsInt (runL Env.p1 o.tables o.func [.int .w64 5, .int .w64 4] {} 1) 4)) =
      some (some (.ARM64CSEL, Int64.ofNat Op.ARM64LessThan.goNum, #[2, 3, 7]),
        some (.ARM64InvertFlags, #[8]), some (.ARM64CMP, #[3, 2]), true, true, true) ∧
    returnsInt (run Env.p1 lcsTabs lcsFunc [.int .w64 3, .int .w64 4] {} 1) 3 = true ∧
    returnsInt (run Env.p1 lcsTabs lcsFunc [.int .w64 5, .int .w64 4] {} 1) 4 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a `CondSelect`: on
`smin`, the checked lower selects by `CSEL [LessThan]` on `InvertFlags` of `CMP v3 v2`, and every
returning or panicking `run` of `smin` is, up to refinement, a `runL` of the result. -/
theorem lcs_lower :
    ∃ out, lowerChecked lcsPassEnv lcsFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 5).map (fun v => (v.op, v.auxInt, v.args)) =
        some (.ARM64CSEL, Int64.ofNat Op.ARM64LessThan.goNum, #[2, 3, 7]) ∧
      (out.func.value? 7).map (fun v => (v.op, v.args)) = some (.ARM64InvertFlags, #[8]) ∧
      (out.func.value? 8).map (fun v => (v.op, v.args)) = some (.ARM64CMP, #[3, 2]) ∧
      (∃ f', GoFV.Proof.Low.Contract lcsFunc f' ∧
        RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func lcsPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem fuel, (run env lcsTabs lcsFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env lcsTabs lcsFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := lcs_checks
  cases hc : lowerChecked lcsPassEnv lcsFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h5, h7, h8, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h5, h7, h8, GoFV.Proof.Low.lower_refines hc lcs_generic,
      fun env hE args mem fuel hd => GoFV.Proof.Low.lower_refines_run hc lcs_generic lcs_noFma hE hd⟩

end GoFV.Proof.Witness
