import GoFV.Proof.Witness.LowerMoveQ

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower` on `Zero [8]` and `Zero [16]`: `zst` (hand-written, issue #385)

`zst() int { g = 0; k = [2]int{}; return g }` with globals `g` of type `int` and `k` of type
`[2]int` as `lower` sees it (one block: `v3`, `v4 = Addr <*int> {g|k} v2` of `v2 = SB`,
`v5 = Zero {int} [8] v3 v1`, `v6 = Zero {[2]int} [16] v4 v5`, `v7 = Load <int> v3 v6`, returned by
`v8 = MakeResult v7 v6`). The checked lower fires `(Addr {sym} base) => (MOVDaddr {sym} base)`
(308), `(Zero [8] ptr mem) => (MOVDstore ptr (MOVDconst [0]) mem)` (351) and `(Zero [16] ptr mem)
=> (STP [0] ptr (MOVDconst [0]) (MOVDconst [0]) mem)` (373), then folds the symbols into both
stores (`893`, `897`): `v5` becomes `MOVDstore {g} v2 c v1` and `v6` `STP {k} v2 c' c' v5` of
fresh `MOVDconst [0]` terms, paired with the `Zero`s (`zeroLower`;
`GoFV.Proof.Low.Sim.zeroSt_lower_eval`). By `lower_refines` every returning or panicking `run` of
`zst` is, up to refinement, a `runL` of the result; on `g` holding 7 both return 0.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- The tables of `gst` with `[2]int` (type 5) and `uint64` (6, the type of the `MOVDconst [0]`
the stores write), the global `main.k` (aux 6) of 16 bytes and the second `Zero`'s type aux (7);
`main.g` (aux 4) and the type aux of `int` (5) are `gst`'s. -/
def zstTabs : Tables :=
  { gstTabs with
    types := (gstTabs.types.set! 5 (some { mkT .ARRAY (some 16) "[2]int" (.array 2 2) with
      align := some 8 })).set! 6 (some (mkT .UINT64 (some 8) "uint64"))
    auxes := (gstTabs.auxes.push (some (mvqG "main.k" 16))).push
      (some { fmt := GoStr.ofString "[2]int", kind := .type 5 }) }

/-- `zst`, the input of `lower`. -/
def zstFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 8
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[8] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 1 #[] 1),
    some (mkV 2 .SB 4 none p0 2 #[] 1),
    some (mkV 3 .Addr 3 (some 4) p0 2 #[2] 1),
    some (mkV 4 .Addr 3 (some 6) p0 1 #[2] 1),
    some (mkVI 5 .Zero 28 8 (some 5) p0 1 #[3, 1] 1),
    some (mkVI 6 .Zero 28 16 (some 7) p0 2 #[4, 5] 1),
    some (mkV 7 .Load 2 none p0 1 #[3, 6] 1),
    some (mkV 8 .MakeResult 33 none p0 1 #[7, 6] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `zst` (`typ.UInt64` for the `MOVDconst [0]`). -/
def zstPassEnv : PassEnv :=
  { gstPassEnv with funcName := GoStr.ofString "zst", tables := zstTabs,
                    typs := gstPassEnv.typs.push ("UInt64", 6) }

/-- The globals: `main.g` holding 7, `main.k` holding 1 in its first byte. -/
def zstMem : Mem :=
  { blocks := #[(.global "main.g", { data := #[.b 7] ++ Array.replicate 7 (.b 0) }),
      (.global "main.k", { data := #[.b 1] ++ Array.replicate 15 (.b 0) })] }

/-- The stores of `zst`'s lowered result (op, offset, aux, arguments). -/
def zstShow (f : Func) : List (Option (Op × Int64 × Option AuxRef × Array ID)) :=
  [5, 6].map fun i => (f.value? i).map fun v => (v.op, v.auxInt, v.aux, v.args)

/-- What `zstShow` gives on the checked lower's result: `MOVDstore {g} v2 v9 v1` and
`STP {k} v2 v10 v10 v5` of the fresh `MOVDconst [0]` terms `v9`, `v10`. -/
def zstOut : List (Option (Op × Int64 × Option AuxRef × Array ID)) :=
  [some (.ARM64MOVDstore, 0, some 4, #[2, 9, 1]), some (.ARM64STP, 0, some 6, #[2, 10, 10, 5])]

theorem zst_generic : zstFunc.lowered = false := by decide +kernel

/-- `zst` has no fused multiply-add shape: its contraction is itself. -/
theorem zst_noFma : GoFV.Opt.FmaContract.contractAll zstFunc = zstFunc := by decide +kernel

set_option synthInstance.maxSize 2048 in
/-- By kernel evaluation: the checked lower keeps a lowered result whose `v5` and `v6` are the
stores of `0` `MOVDstore {g} v2 v9 v1` and `STP {k} v2 v10 v10 v5`, and `zst` returns 0 under
`run` of the input and `runL` of the result. -/
theorem zst_checks :
    (lowerChecked zstPassEnv zstFunc).toOption.map (fun o =>
      (zstShow o.func, o.func.lowered, returnsInt (runL Env.p1 o.tables o.func [] zstMem 1) 0)) =
      some (zstOut, true, true) ∧
    returnsInt (run Env.p1 zstTabs zstFunc [] zstMem 1) 0 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on `Zero [8]` and `Zero
[16]`: on `zst`, the checked lower lowers them to `MOVDstore` and `STP` of `MOVDconst [0]`
(`ARM64.rules:351`, `373`, `GoFV.Proof.Low.Rules.r_ARM64_351_sound`, `r_ARM64_373_sound`) with the
globals' symbols folded in (`893`, `897`), and every returning or panicking `run` of `zst` is, up
to refinement, a `runL` of the result. -/
theorem zst_lower :
    ∃ out, lowerChecked zstPassEnv zstFunc = .ok out ∧ out.func.lowered = true ∧
      zstShow out.func = zstOut ∧
      (∃ f', GoFV.Proof.Low.Contract zstFunc f' ∧
        RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func zstPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem fuel, (run env zstTabs zstFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env zstTabs zstFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := zst_checks
  cases hc : lowerChecked zstPassEnv zstFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h5, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h5, GoFV.Proof.Low.lower_refines hc zst_generic,
      fun env hE args mem fuel hd => GoFV.Proof.Low.lower_refines_run hc zst_generic zst_noFma hE hd⟩

end GoFV.Proof.Witness
