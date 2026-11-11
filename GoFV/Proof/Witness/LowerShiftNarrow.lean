import GoFV.Proof.Witness.LowerTrunc

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower` on a 64-bit shift typed narrower: `nts` (hand-written, issue #385)

`nts() int { return int(int32(uint64(g) >> 3)) }` with a global `g`, as `lower` sees it after
`divmod.rules`-style typing (one block: `v3 = Addr <*int> {g} v2` of `v2 = SB`, `v4 = Load <int> v3
v1`, `v5 = Const64 [3]`, the bounded shift `v6 = Rsh64Ux64 <int32> [1] v4 v5` typed `int32`, `v7 =
SignExt32to64 <int> v6`, returned by `v8 = MakeResult v7 v1`). The checked lower fires `(Rsh64Ux64
x y) && shiftIsBounded(v) => (SRL <t> x y)` (166) at the `int32` shape, which `topOKL` admits for
the 64-bit shifts (`top64Op`), then folds the constant amount into `SRLconst [3] v4`; `v7` becomes
`MOVWreg v6`. By `lower_refines` every returning or panicking `run` of `nts` is, up to refinement, a
`runL` of the result; on `g` holding `2^35 + 40` both return 5.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- `nts`, the input of `lower` (the tables of `trc`: `int32` is type 5). -/
def ntsFunc : Func where
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
    some (mkVI 5 .Const64 2 3 none p0 1 #[] 1),
    some (mkVI 6 .Rsh64Ux64 5 1 none p0 1 #[4, 5] 1),
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

/-- The pass environment of `lower` on `nts`. -/
def ntsPassEnv : PassEnv :=
  { gstPassEnv with funcName := GoStr.ofString "nts", tables := trcTabs }

/-- The global `main.g` holding `2^35 + 40`. -/
def ntsMem : Mem :=
  { blocks := #[(.global "main.g", { data := #[.b 40, .b 0, .b 0, .b 0, .b 8, .b 0, .b 0, .b 0] })] }

theorem nts_generic : ntsFunc.lowered = false := by decide +kernel

/-- `nts` has no fused multiply-add shape: its contraction is itself. -/
theorem nts_noFma : GoFV.Opt.FmaContract.contractAll ntsFunc = ntsFunc := by decide +kernel

set_option synthInstance.maxSize 2048 in
/-- By kernel evaluation: the checked lower keeps a lowered result whose `v6` is `SRLconst [3] v4`
and whose `v7` is `MOVWreg v6`, and `nts` returns 5 under `run` of the input and `runL` of the
result. -/
theorem nts_checks :
    (lowerChecked ntsPassEnv ntsFunc).toOption.map (fun o =>
      ((o.func.value? 6).map (fun v => (v.op, v.auxInt, v.args)),
        (o.func.value? 7).map (fun v => (v.op, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [] ntsMem 1) 5)) =
      some (some (.ARM64SRLconst, 3, #[4]), some (.ARM64MOVWreg, #[6]), true, true) ∧
    returnsInt (run Env.p1 trcTabs ntsFunc [] ntsMem 1) 5 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a 64-bit shift typed
`int32`: on `nts`, the checked lower's `v6` is `SRLconst [3] v4` (rule 166 at the `int32` shape,
`top64Op`), and every returning or panicking `run` of `nts` is, up to refinement, a `runL` of the
result. -/
theorem nts_lower :
    ∃ out, lowerChecked ntsPassEnv ntsFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 6).map (fun v => (v.op, v.auxInt, v.args)) =
        some (.ARM64SRLconst, 3, #[4]) ∧
      (∃ f', GoFV.Proof.Low.Contract ntsFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.RewriteCheck.roSyms ntsPassEnv.tables ntsFunc) env mem)
        out.tables out.func ntsPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.RewriteCheck.roSyms ntsPassEnv.tables ntsFunc) env mem → ∀ fuel,
        (run env trcTabs ntsFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env trcTabs ntsFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := nts_checks
  cases hc : lowerChecked ntsPassEnv ntsFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h6, -, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h6, GoFV.Proof.Low.lower_refines hc nts_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc nts_generic nts_noFma hE hro hd⟩

end GoFV.Proof.Witness
