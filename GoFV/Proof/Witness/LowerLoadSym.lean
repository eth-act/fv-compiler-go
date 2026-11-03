import GoFV.Proof.Witness.LowerStoreSym

/-!
# Witness function for `lower` folding a global's address into a load: `gld` (hand-written,
issue #385)

`gld() int { return g[1] }` with a global `g [2]int` as `lower` sees it (one block: `v3 = Addr
<*int> {g} v2` of `v2 = SB`, `v4 = OffPtr <*int> [8] v3`, `v5 = Load <int> v4 v1`, returned by `v6 =
MakeResult v5 v1`). The checked lower fires `(Addr {sym} base) => (MOVDaddr {sym} base)` (308),
`(OffPtr [off] ptr) => (ADDconst [off] ptr)` (306), `(ADDconst [off1] (MOVDaddr [off2] {sym} ptr))
&& is32Bit(off1+int64(off2)) => (MOVDaddr [int32(off1)+off2] {sym} ptr)` (650), so `v4` becomes
`MOVDaddr [8] {g} v2`, then lowers the load and folds the symbol into it (`(MOVDload [off1] {sym1}
(MOVDaddr [off2] {sym2} ptr) mem) && canMergeSym(sym1,sym2) … => (MOVDload [off1+off2]
{mergeSym(sym1,sym2)} ptr mem)`, 856): `v5` becomes `MOVDload [8] {g} v2 v1`. By `lower_refines`
every returning or panicking `run` of `gld` is, up to refinement, a `runL` of the result; on a `g`
holding `[0, 7]` both return 7.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

-- `DecidableEq` of the nested options of tuples below exceeds the default instance size.
set_option synthInstance.maxSize 1024

/-- The definition tables of `gld`: `gst`'s, the global `main.g` (aux 4) of 16 bytes. -/
def gldTabs : Tables :=
  { gstTabs with
    auxes := gstTabs.auxes.set! 4 (some { fmt := GoStr.ofString "main.g",
      kind := .sym (GoStr.ofString "main.g") 0 "" 16 default none none none #[] none }) }

/-- `gld`, the input of `lower`. -/
def gldFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 6
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[6] #[] #[] #[1, 2, 3, 4, 5, 6])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 2 #[] 1),
    some (mkV 2 .SB 4 none p0 1 #[] 1),
    some (mkV 3 .Addr 3 (some 4) p0 1 #[2] 1),
    some (mkVI 4 .OffPtr 3 8 none p0 1 #[3] 1),
    some (mkV 5 .Load 2 none p0 1 #[4, 1] 1),
    some (mkV 6 .MakeResult 33 none p0 1 #[5, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `gld`. -/
def gldPassEnv : PassEnv :=
  { gstPassEnv with funcName := GoStr.ofString "gld", tables := gldTabs }

/-- The global `main.g` holding `[0, 7]`. -/
def gldMem : Mem :=
  { blocks := #[(.global "main.g",
      { data := Array.replicate 8 (.b 0) ++ #[.b 7] ++ Array.replicate 7 (.b 0) })] }

theorem gld_generic : gldFunc.lowered = false := by decide +kernel

/-- `gld` has no fused multiply-add shape: its contraction is itself. -/
theorem gld_noFma : GoFV.Opt.FmaContract.contractAll gldFunc = gldFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose `v4` is `MOVDaddr [8] {g}
v2` and `v5` `MOVDload [8] {g} v2 v1`, and `gld` returns 7 under `run` of the input and `runL` of
the result. -/
theorem gld_checks :
    (lowerChecked gldPassEnv gldFunc).toOption.map (fun o =>
      ((o.func.value? 4).map (fun v => (v.op, v.auxInt, v.aux, v.args)),
        (o.func.value? 5).map (fun v => (v.op, v.auxInt, v.aux, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [] gldMem 1) 7)) =
      some (some (.ARM64MOVDaddr, 8, some 4, #[2]), some (.ARM64MOVDload, 8, some 4, #[2, 1]),
        true, true) ∧
    returnsInt (run Env.p1 gldTabs gldFunc [] gldMem 1) 7 = true := by
  sorry

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on an offset folded into a
global's address and the global's address folded into a load: on `gld`, the checked lower turns
`v4` into `MOVDaddr [8] {g} v2` and loads at `{g}` directly (`MOVDload [8] {g} v2 v1`), and every
returning or panicking `run` of `gld` is, up to refinement, a `runL` of the result. -/
theorem gld_lower :
    ∃ out, lowerChecked gldPassEnv gldFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 4).map (fun v => (v.op, v.auxInt, v.aux, v.args)) =
        some (.ARM64MOVDaddr, 8, some 4, #[2]) ∧
      (out.func.value? 5).map (fun v => (v.op, v.auxInt, v.aux, v.args)) =
        some (.ARM64MOVDload, 8, some 4, #[2, 1]) ∧
      (∃ f', GoFV.Proof.Low.Contract gldFunc f' ∧
        RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func gldPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem fuel, (run env gldTabs gldFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env gldTabs gldFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := gld_checks
  cases hc : lowerChecked gldPassEnv gldFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h4, h5, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h4, h5, GoFV.Proof.Low.lower_refines hc gld_generic,
      fun env hE args mem fuel hd => GoFV.Proof.Low.lower_refines_run hc gld_generic gld_noFma hE hd⟩

end GoFV.Proof.Witness
