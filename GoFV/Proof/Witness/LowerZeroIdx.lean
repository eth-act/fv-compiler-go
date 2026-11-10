import GoFV.Proof.Witness.LowerStoreIdx

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower` on an indexed `Zero [8]`: `zsx` (hand-written, issue #385)

`zsx(p *int, i int) int { *(*int)(unsafe.Add(p, i<<3)) = 0; return *(*int)(unsafe.Add(p, i<<3)) }`
as `lower` sees it (one block: `v4 = AddPtr <*int> v2 (Lsh64x64 [bounded] v3 (Const64 [3]))` of
the register arguments, `v6 = Zero {int} [8] v4 v1`, `v5 = Load <int> v4 v6`, returned by
`v9 = MakeResult v5 v6`). The checked lower fires `(Lsh64x64 ...) => (SLLconst [3] ...)` (148), the
`AddPtr` of it to `ADDshiftLL [3] v2 v3`, `(Zero [8] ptr mem) => (MOVDstore ptr (MOVDconst [0])
mem)` (351) and `(MOVDstore [off] {sym} (ADDshiftLL [3] ptr idx) val mem) && off == 0 && sym ==
nil => (MOVDstoreidx8 ptr idx val mem)` (806): `v6` becomes `MOVDstoreidx8 v2 v3 c v1` of a fresh
`MOVDconst [0]` `c`, paired with the `Zero` (`zeroIdxLower`; `GoFV.Proof.Low.Sim.zeroIdx_lower_eval`,
the replay relating it by `ZeroIdxRefL`, `GoFV.Proof.Low.Val.ReplayInvL.idxFold`). By
`lower_refines` every returning or panicking `run` of `zsx` is, up to refinement, a `runL` of the
result; on a 16-byte heap block holding 1 at offset 8 and the index 1 both return 0.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- The tables of `stx` with `uint64` (type 6, the type of the `MOVDconst [0]` the store writes). -/
def zsxTabs : Tables :=
  { stxTabs with types := stxTabs.types.set! 6 (some (mkT .UINT64 (some 8) "uint64")) }

/-- `zsx`, the input of `lower`. -/
def zsxFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 9
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[9] #[] #[] #[1, 2, 3, 7, 8, 4, 6, 5, 9])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 1 #[] 1),
    some (mkVI 2 .ArgIntReg 3 0 (some 6) p0 1 #[] 1),
    some (mkVI 3 .ArgIntReg 2 1 (some 7) p0 1 #[] 1),
    some (mkV 4 .AddPtr 3 none p0 2 #[2, 8] 1),
    some (mkV 5 .Load 2 none p0 1 #[4, 6] 1),
    some (mkVI 6 .Zero 28 8 (some 8) p0 2 #[4, 1] 1),
    some (mkVI 7 .Const64 2 3 none p0 1 #[] 1),
    some (mkVI 8 .Lsh64x64 2 1 none p0 1 #[3, 7] 1),
    some (mkV 9 .MakeResult 33 none p0 1 #[5, 6] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `zsx` (`typ.UInt64` for the `MOVDconst [0]`). -/
def zsxPassEnv : PassEnv :=
  { stxPassEnv with funcName := GoStr.ofString "zsx", tables := zsxTabs,
                    typs := stxPassEnv.typs.push ("UInt64", 6) }

/-- The pointer to a 16-byte heap block holding 1 at offset 8, and the index 1 (scaled by 8). -/
def zsxArgs : List Val := [.ptr ⟨.heap 0, 0⟩, .int .w64 1]

/-- The heap block of 16 bytes: 1 at offset 8. -/
def zsxMem : Mem :=
  { blocks := #[(.heap 0, { data := (Array.replicate 16 (.b 0)).set! 8 (.b 1) })], nextHeap := 1 }

theorem zsx_generic : zsxFunc.lowered = false := by decide +kernel

/-- `zsx` has no fused multiply-add shape: its contraction is itself. -/
theorem zsx_noFma : GoFV.Opt.FmaContract.contractAll zsxFunc = zsxFunc := by decide +kernel

set_option synthInstance.maxSize 2048 in
/-- By kernel evaluation: the checked lower keeps a lowered result whose `v6` is the indexed store
of `0` `MOVDstoreidx8 v2 v3 v10 v1` (`v10` the fresh `MOVDconst [0]`), and `zsx` returns 0 under
`run` of the input and `runL` of the result (the 1 at offset 8 zeroed). -/
theorem zsx_checks :
    (lowerChecked zsxPassEnv zsxFunc).toOption.map (fun o =>
      ((o.func.value? 6).map (fun v => (v.op, v.auxInt, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func zsxArgs zsxMem 1) 0)) =
      some (some (.ARM64MOVDstoreidx8, 0, #[2, 3, 10, 1]), true, true) ∧
    returnsInt (run Env.p1 zsxTabs zsxFunc zsxArgs zsxMem 1) 0 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on an indexed `Zero [8]`:
on `zsx` the checked lower lowers the `Zero [8]` at `v2 + v3<<3` to `MOVDstoreidx8 v2 v3 v10 v1`
of a fresh `MOVDconst [0]` (`ARM64.rules:351`, `806`; `GoFV.Proof.Low.Rules.r_ARM64_351_sound`,
`r_ARM64_806_sound`), and every returning or panicking `run` of `zsx` is, up to refinement, a
`runL` of the result. -/
theorem zsx_lower :
    ∃ out, lowerChecked zsxPassEnv zsxFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 6).map (fun v => (v.op, v.auxInt, v.args)) =
        some (.ARM64MOVDstoreidx8, 0, #[2, 3, 10, 1]) ∧
      (∃ f', GoFV.Proof.Low.Contract zsxFunc f' ∧
        RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func zsxPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem fuel, (run env zsxTabs zsxFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env zsxTabs zsxFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := zsx_checks
  cases hc : lowerChecked zsxPassEnv zsxFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h6, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h6, GoFV.Proof.Low.lower_refines hc zsx_generic,
      fun env hE args mem fuel hd => GoFV.Proof.Low.lower_refines_run hc zsx_generic zsx_noFma hE hd⟩

end GoFV.Proof.Witness
