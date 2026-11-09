import GoFV.Proof.Witness.LowerStoreSym

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower` reading a truncation through an extension: `trc` (hand-written, issue #385)

`trc() int { return int(int32(g)) }` with a global `g` as `lower` sees it (one block: `v3 = Addr
<*int> {g} v2` of `v2 = SB`, `v4 = Load <int> v3 v1`, `v5 = Trunc64to32 <int32> v4`, `v6 =
SignExt32to64 <int> v5`, returned by `v7 = MakeResult v6 v1`). The checked lower fires `(Addr {sym}
base) => (MOVDaddr {sym} base)` (308), the load's lowering, `(Trunc64to32 ...) => (Copy ...)` (196)
and `(SignExt32to64 ...) => (MOVWreg ...)`; `lower` eliminates the `Copy` while `v6` is still
generic, so `v6` becomes `MOVWreg v4`, where the replay keeps `MOVWreg v5`: the validator accepts
the output's argument, which the narrowing `Copy` `v5` copies and which keeps the 32 bits `MOVWreg`
reads (`truncReachL`). By `lower_refines` every returning or panicking `run` of `trc` is, up to
refinement, a `runL` of the result; on `g` holding `2^32 - 5` both return `-5`.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- The tables of `gst` with `int32` (type 5). -/
def trcTabs : Tables := { gstTabs with types := gstTabs.types.set! 5 (some (mkT .INT32 (some 4) "int32")) }

/-- `trc`, the input of `lower`. -/
def trcFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 7
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[7] #[] #[] #[1, 2, 3, 4, 5, 6, 7])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 2 #[] 1),
    some (mkV 2 .SB 4 none p0 1 #[] 1),
    some (mkV 3 .Addr 3 (some 4) p0 1 #[2] 1),
    some (mkV 4 .Load 2 none p0 1 #[3, 1] 1),
    some (mkV 5 .Trunc64to32 5 none p0 1 #[4] 1),
    some (mkV 6 .SignExt32to64 2 none p0 1 #[5] 1),
    some (mkV 7 .MakeResult 33 none p0 1 #[6, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `trc`. -/
def trcPassEnv : PassEnv :=
  { gstPassEnv with funcName := GoStr.ofString "trc", tables := trcTabs }

/-- The global `main.g` holding `2^32 - 5`. -/
def trcMem : Mem :=
  { blocks := #[(.global "main.g", { data := #[.b 0xfb, .b 0xff, .b 0xff, .b 0xff, .b 0, .b 0, .b 0,
      .b 0] })] }

theorem trc_generic : trcFunc.lowered = false := by decide +kernel

/-- `trc` has no fused multiply-add shape: its contraction is itself. -/
theorem trc_noFma : GoFV.Opt.FmaContract.contractAll trcFunc = trcFunc := by decide +kernel

set_option synthInstance.maxSize 2048 in
/-- By kernel evaluation: the checked lower keeps a lowered result whose `v6` is `MOVWreg v4`, and
`trc` returns `-5` under `run` of the input and `runL` of the result. -/
theorem trc_checks :
    (lowerChecked trcPassEnv trcFunc).toOption.map (fun o =>
      ((o.func.value? 6).map (fun v => (v.op, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [] trcMem 1) (-5))) =
      some (some (.ARM64MOVWreg, #[4]), true, true) ∧
    returnsInt (run Env.p1 trcTabs trcFunc [] trcMem 1) (-5) = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a sign extension of a
truncation: on `trc`, the checked lower's `v6` is `MOVWreg v4` (the narrowing `Copy` it read is
gone, `truncReachL`), and every returning or panicking `run` of `trc` is, up to refinement, a
`runL` of the result. -/
theorem trc_lower :
    ∃ out, lowerChecked trcPassEnv trcFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 6).map (fun v => (v.op, v.args)) = some (.ARM64MOVWreg, #[4]) ∧
      (∃ f', GoFV.Proof.Low.Contract trcFunc f' ∧
        RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func trcPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem fuel, (run env trcTabs trcFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env trcTabs trcFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := trc_checks
  cases hc : lowerChecked trcPassEnv trcFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h6, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h6, GoFV.Proof.Low.lower_refines hc trc_generic,
      fun env hE args mem fuel hd => GoFV.Proof.Low.lower_refines_run hc trc_generic trc_noFma hE hd⟩

end GoFV.Proof.Witness
