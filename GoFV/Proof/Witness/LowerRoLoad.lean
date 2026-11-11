import GoFV.Proof.Witness.LowerLoadSym

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower` folding a load of a read-only symbol to a constant: `rld`
(hand-written, issue #385)

`rld() int { return tab[1] }` with a read-only `tab [2]int` holding `[0, 7]` (an `SRODATA` symbol
with its bytes) as `lower` sees it: `gld` (`GoFV/Proof/Witness/LowerLoadSym.lean`) with `{tab}`
read-only (one block: `v3 = Addr <*int> {tab} v2` of `v2 = SB`, `v4 = OffPtr <*int> [8] v3`, `v5 =
Load <int> v4 v1`, returned by `v6 = MakeResult v5 v1`). The checked lower fires 308, 306, 650 and
856 as on `gld` (`v5` becomes `MOVDload [8] {tab} v2 v1`), then `(MOVDload [off] {sym} (SB) _) &&
symIsRO(sym) => (MOVDconst [int64(read64(sym, int64(off), config.ctxt.Arch.ByteOrder))])`
(1814): `v5` becomes `MOVDconst [7]`. The validator replays the event as the constant
(`GoFV.Opt.LowerCheck.roLoadDef`: the load from `tab`'s allocation alone gives 7,
`LowerCheck.roLoadWord`). By `lower_refines` every returning or panicking `run` of `rld` is, up to
refinement, a `runL` of the result on the inputs whose memory holds `tab`'s read-only allocation
(`RoImage` of `LowerCheck.roPre`: `rld`'s values are generic memory-typed ops, so the symbols its
`Addr`s name, `[("main.tab", rldAlloc)]`); `rld_pre` gives one such input, on which both return 7.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

set_option synthInstance.maxSize 1024

/-- The bytes of `main.tab`: `[0, 7]` as two little-endian 64-bit words. -/
def rldBytes : ByteArray := ByteArray.mk (Array.replicate 8 0 ++ #[7] ++ Array.replicate 7 0)

/-- The definition tables of `rld`: `gld`'s, with aux 4 the `SRODATA` symbol `main.tab` of 16
bytes holding `rldBytes`. -/
def rldTabs : Tables :=
  { gldTabs with
    auxes := gldTabs.auxes.set! 4 (some
      { fmt := GoStr.ofString "main.tab",
        kind := .sym (GoStr.ofString "main.tab") 0 "SRODATA" 16 default none none
          (some rldBytes) #[] none }) }

/-- The pass environment of `lower` on `rld` (`gldFunc` read in `rldTabs`). -/
def rldPassEnv : PassEnv :=
  { gldPassEnv with funcName := GoStr.ofString "rld", tables := rldTabs }

/-- The global image's allocation of `main.tab` (`Sem.rodataAlloc`), read-only. -/
def rldAlloc : Alloc := rodataAlloc rldBytes 16 #[]

/-- A memory holding `main.tab`'s read-only allocation. -/
def rldMem : Mem := { blocks := #[(.global "main.tab", rldAlloc)] }

/-- The precondition's read-only symbols of `rld`: `main.tab` with its allocation. -/
theorem rld_roPre :
    LowerCheck.roPre rldPassEnv.tables gldFunc = [("main.tab", rldAlloc)] := by
  decide +kernel

/-- **The precondition is satisfiable**: `Env.p1` keeps the read-only allocations, and `rldMem`
holds `main.tab`'s. -/
theorem rld_pre : RoImage (LowerCheck.roPre rldPassEnv.tables gldFunc) Env.p1 rldMem := by
  refine ⟨Env.p1_keepsRo, fun n a h => ?_⟩
  rw [rld_roPre, List.mem_singleton, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨by decide +kernel, by decide +kernel⟩

/-- By kernel evaluation: the checked lower keeps a lowered result whose `v5` is `MOVDconst [7]`,
and `rld` returns 7 under `run` of the input and `runL` of the result. -/
theorem rld_checks :
    (lowerChecked rldPassEnv gldFunc).toOption.map (fun o =>
      ((o.func.value? 5).map (fun v => (v.op, v.auxInt, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [] rldMem 1) 7)) =
      some (some (.ARM64MOVDconst, 7, #[]), true, true) ∧
    returnsInt (run Env.p1 rldTabs gldFunc [] rldMem 1) 7 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a load of a read-only
symbol: on `rld`, the checked lower replaces the load of `tab[1]` by the constant 7 (`MOVDconst
[7]`, `ARM64.rules:1814`), and every returning or panicking `run` of `rld` is, up to refinement, a
`runL` of the result, on the inputs with `tab`'s read-only allocation (`rld_pre`). -/
theorem rld_lower :
    ∃ out, lowerChecked rldPassEnv gldFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 5).map (fun v => (v.op, v.auxInt, v.args)) =
        some (.ARM64MOVDconst, 7, #[]) ∧
      (∃ f', GoFV.Proof.Low.Contract gldFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.LowerCheck.roPre rldPassEnv.tables gldFunc) env mem)
        out.tables out.func rldPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.LowerCheck.roPre rldPassEnv.tables gldFunc) env mem → ∀ fuel,
        (run env rldTabs gldFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env rldTabs gldFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := rld_checks
  cases hc : lowerChecked rldPassEnv gldFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h5, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h5, GoFV.Proof.Low.lower_refines hc gld_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc gld_generic gld_noFma hE hro hd⟩

end GoFV.Proof.Witness
