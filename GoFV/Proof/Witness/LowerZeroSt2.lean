import GoFV.Proof.Witness.LowerZeroSt

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower` on `Zero [12]`: `zst2` (hand-written, issue #385)

`zst2() int { *(*[12]uint8)(unsafe.Pointer(&k)) = [12]uint8{}; return k[0] }` with the global `k`
of type `[2]int` as `lower` sees it (one block: `v3 = Addr <*int> {k} v2` of `v2 = SB`,
`v4 = Zero {[12]uint8} [12] v3 v1`, `v5 = Load <int> v3 v4`, returned by `v6 = MakeResult v5 v4`).
The checked lower fires `(Addr {sym} base) => (MOVDaddr {sym} base)` (308) and `(Zero [12] ptr
mem) => (MOVWstore [8] ptr (MOVDconst [0]) (MOVDstore ptr (MOVDconst [0]) mem))` (361), then folds
the symbol into both stores and the load: `v4` becomes the outer `MOVWstore [8] {k} v2 v7 v8` on
the inner `MOVDstore {k} v2 v7 v1` at the fresh `v8`, of the fresh `MOVDconst [0]` term `v7`,
paired with the `Zero` (`zero2Lower`; `GoFV.Proof.Low.Sim.zero2_inner_eval`, `zero2_outer_eval`).
By `lower_refines` every returning or panicking `run` of `zst2` is, up to refinement, a `runL` of
the result; on `k` holding 1 in its first byte both return 0.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- The tables of `zst` with `uint8` (type 7), `[12]uint8` (type 8) and its type aux (8). -/
def zst2Tabs : Tables :=
  { zstTabs with
    types := (zstTabs.types.set! 7 (some (mkT .UINT8 (some 1) "uint8"))).set! 8
      (some { mkT .ARRAY (some 12) "[12]uint8" (.array 7 12) with align := some 1 })
    auxes := zstTabs.auxes.push (some { fmt := GoStr.ofString "[12]uint8", kind := .type 8 }) }

/-- `zst2`, the input of `lower`. -/
def zst2Func : Func where
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
    some (mkV 3 .Addr 3 (some 6) p0 2 #[2] 1),
    some (mkVI 4 .Zero 28 12 (some 8) p0 2 #[3, 1] 1),
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

/-- The pass environment of `lower` on `zst2`. -/
def zst2PassEnv : PassEnv :=
  { zstPassEnv with funcName := GoStr.ofString "zst2", tables := zst2Tabs }

/-- The stores of `zst2`'s lowered result (op, offset, aux, arguments). -/
def zst2Show (f : Func) : List (Option (Op × Int64 × Option AuxRef × Array ID)) :=
  [4, 8].map fun i => (f.value? i).map fun v => (v.op, v.auxInt, v.aux, v.args)

/-- What `zst2Show` gives on the checked lower's result: the outer `MOVWstore [8] {k} v2 v7 v8`
and the inner `MOVDstore {k} v2 v7 v1` of the fresh `MOVDconst [0]` term `v7`. -/
def zst2Out : List (Option (Op × Int64 × Option AuxRef × Array ID)) :=
  [some (.ARM64MOVWstore, 8, some 6, #[2, 7, 8]), some (.ARM64MOVDstore, 0, some 6, #[2, 7, 1])]

theorem zst2_generic : zst2Func.lowered = false := by decide +kernel

/-- `zst2` has no fused multiply-add shape: its contraction is itself. -/
theorem zst2_noFma : GoFV.Opt.FmaContract.contractAll zst2Func = zst2Func := by decide +kernel

set_option synthInstance.maxSize 2048 in
/-- By kernel evaluation: the checked lower keeps a lowered result whose `v4` is the outer store
`MOVWstore [8] {k} v2 v7 v8` on the inner `MOVDstore {k} v2 v7 v1` at `v8`, and `zst2` returns 0
under `run` of the input and `runL` of the result. -/
theorem zst2_checks :
    (lowerChecked zst2PassEnv zst2Func).toOption.map (fun o =>
      (zst2Show o.func, o.func.lowered, returnsInt (runL Env.p1 o.tables o.func [] zstMem 1) 0)) =
      some (zst2Out, true, true) ∧
    returnsInt (run Env.p1 zst2Tabs zst2Func [] zstMem 1) 0 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on `Zero [12]`: on
`zst2`, the checked lower lowers it to two overlapping stores of `MOVDconst [0]` (`ARM64.rules:361`,
`GoFV.Proof.Low.Rules.r_ARM64_361_sound`) with the global's symbol folded into both, and every
returning or panicking `run` of `zst2` is, up to refinement, a `runL` of the result. -/
theorem zst2_lower :
    ∃ out, lowerChecked zst2PassEnv zst2Func = .ok out ∧ out.func.lowered = true ∧
      zst2Show out.func = zst2Out ∧
      (∃ f', GoFV.Proof.Low.Contract zst2Func f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.LowerCheck.roPre zst2PassEnv.tables zst2Func) env mem)
        out.tables out.func zst2PassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.LowerCheck.roPre zst2PassEnv.tables zst2Func) env mem → ∀ fuel,
        (run env zst2Tabs zst2Func args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env zst2Tabs zst2Func args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := zst2_checks
  cases hc : lowerChecked zst2PassEnv zst2Func with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h5, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h5, GoFV.Proof.Low.lower_refines hc zst2_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc zst2_generic zst2_noFma hE hro hd⟩

end GoFV.Proof.Witness
