import GoFV.Proof.Witness.LowerStoreSym

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower` on a `Zero`: `gzr` (hand-written, issue #385)

`gzr() int` with a 32-byte global `g` as `lower` sees it (one block: `v3 = Addr <*int> {g} v2` of
`v2 = SB`, `v4 = Zero {int} [32] v3 v1`, `v5 = Load <int> v3 v4`, returned by `v6 = MakeResult v5
v4`). The checked lower fires `(Addr {sym} base) => (MOVDaddr {sym} base)` (308) and `(Zero [s]
ptr mem) && s > 16 && s < 192 => (LoweredZero [s] ptr mem)` (376): `v4` becomes `LoweredZero [32]
v3 v1`, which is not a root of lowered SSA (the validator compares the order of `f`'s roots,
`atomsOKL`, and pairs it with the `Zero`, `bulkLower`). By `lower_refines` every returning or
panicking `run` of `gzr` is, up to refinement, a `runL` of the result; on `g` holding 5 both
return 0.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- The global `main.g` of 32 bytes. -/
def gzrG : AuxDef :=
  { fmt := GoStr.ofString "main.g",
    kind := .sym (GoStr.ofString "main.g") 0 "" 32 default none none none #[] none }

/-- The tables of `gst` with the global `main.g` of 32 bytes. -/
def gzrTabs : Tables := { gstTabs with auxes := gstTabs.auxes.set! 4 (some gzrG) }

/-- `gzr`, the input of `lower`. -/
def gzrFunc : Func where
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
    some (mkVI 4 .Zero 28 32 (some 5) p0 2 #[3, 1] 1),
    some (mkV 5 .Load 2 none p0 1 #[3, 4] 1),
    some (mkV 6 .MakeResult 33 none p0 1 #[5, 4] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `gzr`. -/
def gzrPassEnv : PassEnv :=
  { gstPassEnv with funcName := GoStr.ofString "gzr", tables := gzrTabs }

/-- The global `main.g`, 32 bytes, the first word 5. -/
def gzrMem : Mem :=
  { blocks := #[(.global "main.g", { data := #[.b 5] ++ Array.replicate 31 (.b 0) })] }

theorem gzr_generic : gzrFunc.lowered = false := by decide +kernel

/-- `gzr` has no fused multiply-add shape: its contraction is itself. -/
theorem gzr_noFma : GoFV.Opt.FmaContract.contractAll gzrFunc = gzrFunc := by decide +kernel

set_option synthInstance.maxSize 2048 in
/-- By kernel evaluation: the checked lower keeps a lowered result whose `v4` is `LoweredZero [32]
v3 v1`, and `gzr` returns 0 under `run` of the input and `runL` of the result. -/
theorem gzr_checks :
    (lowerChecked gzrPassEnv gzrFunc).toOption.map (fun o =>
      ((o.func.value? 4).map (fun v => (v.op, v.auxInt, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [] gzrMem 1) 0)) =
      some (some (.ARM64LoweredZero, 32, #[3, 1]), true, true) ∧
    returnsInt (run Env.p1 gzrTabs gzrFunc [] gzrMem 1) 0 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a `Zero`: on `gzr`, the
checked lower lowers `Zero [32]` to `LoweredZero [32]`, and every returning or panicking `run` of
`gzr` is, up to refinement, a `runL` of the result. -/
theorem gzr_lower :
    ∃ out, lowerChecked gzrPassEnv gzrFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 4).map (fun v => (v.op, v.auxInt, v.args)) =
        some (.ARM64LoweredZero, 32, #[3, 1]) ∧
      (∃ f', GoFV.Proof.Low.Contract gzrFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.RewriteCheck.roSyms gzrPassEnv.tables gzrFunc) env mem)
        out.tables out.func gzrPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.RewriteCheck.roSyms gzrPassEnv.tables gzrFunc) env mem → ∀ fuel,
        (run env gzrTabs gzrFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env gzrTabs gzrFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := gzr_checks
  cases hc : lowerChecked gzrPassEnv gzrFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h4, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h4, GoFV.Proof.Low.lower_refines hc gzr_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc gzr_generic gzr_noFma hE hro hd⟩

end GoFV.Proof.Witness
