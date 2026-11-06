import GoFV.Proof.Witness.LowerLoadIdx

/-!
# Witness functions for `lower` on indexed stores: `stx`, `sti` (hand-written, issue #385)

`stx(p *int, i int) int { *(*int)(unsafe.Add(p, i)) = 5; return 5 }` as `lower` sees it (one
block: `v4 = AddPtr <*int> v2 v3` of the register arguments, `v5 = Const64 [5]`, `v6 = Store {int}
v4 v5 v1`, returned by `v9 = MakeResult v5 v6`). The checked lower fires `(AddPtr ...) => (ADD
...)` (5), `(Store {t} ptr val mem) && t.Size() == 8 => (MOVDstore ptr val mem)` and
`(MOVDstore [off] {sym} (ADD ptr idx) val mem) && off == 0 && sym == nil => (MOVDstoreidx ptr idx
val mem)` (786), so `v6` becomes `MOVDstoreidx v2 v3 v5 v1`, whose indexed address is the `ADD`'s
value (`GoFV.Proof.Low.Val.ReplayInvL.idxFold`). `sti` is `stx` storing at `p + i<<3`: `v8 =
Lsh64x64 [bounded] v3 (Const64 [3])` lowers to `SLLconst [3]` (148), the `AddPtr` of it to
`ADDshiftLL [3] v2 v3` and the store to `MOVDstoreidx8 v2 v3 v5 v1` (806). By `lower_refines` every
returning or panicking `run` of either is, up to refinement, a `runL` of the result; on a 16-byte
heap block and the index 8 (`stx`) or 1 (`sti`) both store 5 at offset 8 and return 5.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- The tables of `ldx` with the `flags` type (29) and the store type `int` (aux 8). -/
def stxTabs : Tables :=
  { ldxTabs with
    types := ldxTabs.types.set! 29 (some (mkT .SSA none "flags"))
    auxes := ldxTabs.auxes.push (some { fmt := GoStr.ofString "int", kind := .type 2 }) }

/-- `stx` (`scaled = false`: the address `AddPtr v2 v3`) or `sti` (`scaled = true`: the address
`AddPtr v2 (Lsh64x64 [bounded] v3 (Const64 [3]))`), the input of `lower`. -/
def stxFunc (scaled : Bool) : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 9
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[9] #[] #[]
    (if scaled then #[1, 2, 3, 7, 8, 4, 5, 6, 9] else #[1, 2, 3, 4, 5, 6, 9]))]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 1 #[] 1),
    some (mkVI 2 .ArgIntReg 3 0 (some 6) p0 1 #[] 1),
    some (mkVI 3 .ArgIntReg 2 1 (some 7) p0 1 #[] 1),
    some (mkV 4 .AddPtr 3 none p0 1 (if scaled then #[2, 8] else #[2, 3]) 1),
    some (mkVI 5 .Const64 2 5 none p0 2 #[] 1),
    some (mkV 6 .Store 28 (some 8) p0 1 #[4, 5, 1] 1),
    (if scaled then some (mkVI 7 .Const64 2 3 none p0 1 #[] 1) else none),
    (if scaled then some (mkVI 8 .Lsh64x64 2 1 none p0 1 #[3, 7] 1) else none),
    some (mkV 9 .MakeResult 33 none p0 1 #[5, 6] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := if scaled then [] else [7, 8]
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `stx` and `sti`. -/
def stxPassEnv : PassEnv :=
  { laPassEnv with
    funcName := GoStr.ofString "stx"
    tables := stxTabs
    typs := #[("Int", 2), ("Mem", 28), ("Flags", 29), ("Void", 31)] }

/-- The pointer to `ldxMem`'s block and the index: 8 (`stx`) or 1 (`sti`, scaled by 8). -/
def stxArgs (scaled : Bool) : List Val := [.ptr ⟨.heap 0, 0⟩, .int .w64 (if scaled then 1 else 8)]

theorem stx_generic (scaled : Bool) : (stxFunc scaled).lowered = false := by
  cases scaled <;> decide +kernel

/-- `stx` and `sti` have no fused multiply-add shape: their contraction is themselves. -/
theorem stx_noFma (scaled : Bool) :
    GoFV.Opt.FmaContract.contractAll (stxFunc scaled) = stxFunc scaled := by
  cases scaled <;> decide +kernel

set_option synthInstance.maxSize 2048 in
/-- By kernel evaluation: the checked lower keeps a lowered result whose `v6` is `MOVDstoreidx v2
v3 v5 v1` (`stx`) or `MOVDstoreidx8 v2 v3 v5 v1` (`sti`), and both return 5 under `run` of the
input and `runL` of the result. -/
theorem stx_checks (scaled : Bool) :
    (lowerChecked stxPassEnv (stxFunc scaled)).toOption.map (fun o =>
      ((o.func.value? 6).map (fun v => (v.op, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func (stxArgs scaled) ldxMem 1) 5)) =
      some (some (if scaled then .ARM64MOVDstoreidx8 else .ARM64MOVDstoreidx, #[2, 3, 5, 1]), true,
        true) ∧
    returnsInt (run Env.p1 stxTabs (stxFunc scaled) (stxArgs scaled) ldxMem 1) 5 = true := by
  cases scaled <;> decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on indexed stores: on
`stx` the checked lower lowers the store at `AddPtr v2 v3` to `MOVDstoreidx v2 v3 v5 v1`
(`ARM64.rules:786`), on `sti` the store at `v2 + v3<<3` to `MOVDstoreidx8 v2 v3 v5 v1` (`806`),
and every returning or panicking `run` of either is, up to refinement, a `runL` of the result. -/
theorem stx_lower (scaled : Bool) :
    ∃ out, lowerChecked stxPassEnv (stxFunc scaled) = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 6).map (fun v => (v.op, v.args)) =
        some (if scaled then .ARM64MOVDstoreidx8 else .ARM64MOVDstoreidx, #[2, 3, 5, 1]) ∧
      (∃ f', GoFV.Proof.Low.Contract (stxFunc scaled) f' ∧
        RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func stxPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem fuel, (run env stxTabs (stxFunc scaled) args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env stxTabs (stxFunc scaled) args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := stx_checks scaled
  cases hc : lowerChecked stxPassEnv (stxFunc scaled) with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h6, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h6, GoFV.Proof.Low.lower_refines hc (stx_generic scaled),
      fun env hE args mem fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc (stx_generic scaled) (stx_noFma scaled) hE hd⟩

end GoFV.Proof.Witness
