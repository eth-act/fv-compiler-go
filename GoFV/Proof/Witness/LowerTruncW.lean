import GoFV.Proof.Witness.LowerTrunc

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower` reading a truncation through a `W` op: `trw` (hand-written, issue #385)

`trw() int { x := int32(g); return int(x * x) }` with a global `g` as `lower` sees it (one block:
`v3 = Addr <*int> {g} v2` of `v2 = SB`, `v4 = Load <int> v3 v1`, `v5 = Trunc64to32 <int32> v4`,
`v6 = Mul32 <int32> v5 v5`, `v7 = SignExt32to64 <int> v6`, returned by `v8 = MakeResult v7 v1`).
The checked lower fires `(Trunc64to32 ...) => (Copy ...)` (196) and `(Mul32 ...) => (MULW ...)`
(12); `applyRewrite` eliminates the `Copy` inline, so the built `v6` is `MULW v4 v4`, where the
replay keeps the rule's `MULW v5 v5` (`ruleDefsL`): the validator accepts the output's arguments,
which the narrowing `Copy` `v5` copies and which keep the 32 bits `MULW` reads (`truncReachL`,
`GoFV.Proof.Low.Val.w32_mono`). By `lower_refines` every returning or panicking `run` of `trw` is,
up to refinement, a `runL` of the result; on `g` holding `2^32 - 5` both return `25`.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- `trw`, the input of `lower`. -/
def trwFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 8
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[8] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 2 #[] 1),
    some (mkV 2 .SB 4 none p0 1 #[] 1),
    some (mkV 3 .Addr 3 (some 4) p0 1 #[2] 1),
    some (mkV 4 .Load 2 none p0 1 #[3, 1] 1),
    some (mkV 5 .Trunc64to32 5 none p0 2 #[4] 1),
    some (mkV 6 .Mul32 5 none p0 1 #[5, 5] 1),
    some (mkV 7 .SignExt32to64 2 none p0 1 #[6] 1),
    some (mkV 8 .MakeResult 33 none p0 1 #[7, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `trw`. -/
def trwPassEnv : PassEnv :=
  { gstPassEnv with funcName := GoStr.ofString "trw", tables := trcTabs }

theorem trw_generic : trwFunc.lowered = false := by decide +kernel

/-- `trw` has no fused multiply-add shape: its contraction is itself. -/
theorem trw_noFma : GoFV.Opt.FmaContract.contractAll trwFunc = trwFunc := by decide +kernel

set_option synthInstance.maxSize 2048 in
/-- By kernel evaluation: the checked lower keeps a lowered result whose `v6` is `MULW v4 v4`,
and `trw` returns `25` under `run` of the input and `runL` of the result. -/
theorem trw_checks :
    (lowerChecked trwPassEnv trwFunc).toOption.map (fun o =>
      ((o.func.value? 6).map (fun v => (v.op, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [] trcMem 1) 25)) =
      some (some (.ARM64MULW, #[4, 4]), true, true) ∧
    returnsInt (run Env.p1 trcTabs trwFunc [] trcMem 1) 25 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a `W` op of a
truncation: on `trw`, the checked lower's `v6` is `MULW v4 v4` (the narrowing `Copy` it read is
gone, `truncReachL`), and every returning or panicking `run` of `trw` is, up to refinement, a
`runL` of the result. -/
theorem trw_lower :
    ∃ out, lowerChecked trwPassEnv trwFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 6).map (fun v => (v.op, v.args)) = some (.ARM64MULW, #[4, 4]) ∧
      (∃ f', GoFV.Proof.Low.Contract trwFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.LowerCheck.roPre trwPassEnv.tables trwFunc) env mem)
        out.tables out.func trwPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.LowerCheck.roPre trwPassEnv.tables trwFunc) env mem → ∀ fuel,
        (run env trcTabs trwFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env trcTabs trwFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := trw_checks
  cases hc : lowerChecked trwPassEnv trwFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h6, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h6, GoFV.Proof.Low.lower_refines hc trw_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc trw_generic trw_noFma hE hro hd⟩

end GoFV.Proof.Witness
