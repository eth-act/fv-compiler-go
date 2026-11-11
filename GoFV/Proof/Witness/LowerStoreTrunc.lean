import GoFV.Proof.Witness.LowerTrunc
import GoFV.Proof.Witness.LowerStoreIdx

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness functions for `lower` storing a truncation: `stw`, `sxw` (hand-written, issue #385)

`stw() int { *(*int32)(unsafe.Pointer(&g)) = int32(g + g); return g }` with a global `g` as `lower`
sees it (one block: `v3 = Addr <*int> {g} v2` of `v2 = SB`, `v4 = Load <int> v3 v1`, `v5 = Add64
<int> v4 v4`, `v6 = Trunc64to32 <int32> v5`, `v7 = Store {int32} v3 v6 v1`, `v8 = Load <int> v3 v7`,
returned by `v9 = MakeResult v8 v7`), built with `-dynlink` so the global's address is not folded
into the store. The checked lower fires `(Trunc64to32 ...) => (Copy ...)` (196) and `(Store {t} ptr
val mem) && t.Size() == 4 && !t.IsFloat() => (MOVWstore ptr val mem)` (328); `lower` eliminates the
`Copy` inline, so `v7` is `MOVWstore v3 v5 v1`: the validator accepts the store's value, which the
narrowing `Copy` `v6` copies and whose low 32 bits the `MOVWstore` writes (`stValPick`,
`truncFitL`, `GoFV.Proof.Low.encode_le_storeBytes_fit`). By `lower_refines` every returning or
panicking `run` of `stw` is, up to refinement, a `runL` of the result; on `g` holding `2^32 - 5`
both return `2^32 - 10`.

`sxw(p *int, i int) int { *(*int32)(unsafe.Add(p, i)) = int32(i); return *(*int)(unsafe.Add(p, i))
}` (one block: `v4 = AddPtr <*int> v2 v3` of the register arguments, `v5 = Trunc64to32 <int32>
v3`, `v6 = Store {int32} v4 v5 v1`, `v7 = Load <int> v4 v6`, returned by `v8 = MakeResult v7 v6`):
the checked lower fires `(AddPtr ...) => (ADD ...)` (5), 196, 328 and `(MOVWstore [off] {sym} (ADD
ptr idx) val mem) && off == 0 && sym == nil => (MOVWstoreidx ptr idx val mem)` (786), so `v6` is
`MOVWstoreidx v2 v3 v3 v1`: the indexed store's value read through the narrowing `Copy`
(`stValPick` at argument 2, `stIdxValW`, `GoFV.Proof.Low.idx_lower_eval_fit`). On a 16-byte heap
block and the index 8 both return 8.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- The tables of `trc` with the `Store`'s type aux `int32` (aux 6). -/
def stwTabs : Tables :=
  { trcTabs with
    auxes := trcTabs.auxes.push (some { fmt := GoStr.ofString "int32", kind := .type 5 }) }

/-- `stw`, the input of `lower`. -/
def stwFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 9
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[9] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8, 9])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 2 #[] 1),
    some (mkV 2 .SB 4 none p0 1 #[] 1),
    some (mkV 3 .Addr 3 (some 4) p0 3 #[2] 1),
    some (mkV 4 .Load 2 none p0 2 #[3, 1] 1),
    some (mkV 5 .Add64 2 none p0 1 #[4, 4] 1),
    some (mkV 6 .Trunc64to32 5 none p0 1 #[5] 1),
    some (mkV 7 .Store 28 (some 6) p0 2 #[3, 6, 1] 1),
    some (mkV 8 .Load 2 none p0 1 #[3, 7] 1),
    some (mkV 9 .MakeResult 33 none p0 1 #[8, 7] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `stw`, with `-dynlink` (`config flagdynlink`): the fold of
`SB`'s symbol address into the store (`ptr.Op != OpSB || !Flag_dynlink`) does not fire. -/
def stwPassEnv : PassEnv :=
  { gstPassEnv with funcName := GoStr.ofString "stw", tables := stwTabs,
                    config := laPassEnv.config.push ("flagdynlink", #[.word "1"]) }

theorem stw_generic : stwFunc.lowered = false := by decide +kernel

/-- `stw` has no fused multiply-add shape: its contraction is itself. -/
theorem stw_noFma : GoFV.Opt.FmaContract.contractAll stwFunc = stwFunc := by decide +kernel

set_option synthInstance.maxSize 2048 in
/-- By kernel evaluation: the checked lower keeps a lowered result whose `v7` is `MOVWstore v3 v5
v1`, and `stw` returns `2^32 - 10` under `run` of the input and `runL` of the result. -/
theorem stw_checks :
    (lowerChecked stwPassEnv stwFunc).toOption.map (fun o =>
      ((o.func.value? 7).map (fun v => (v.op, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [] trcMem 1) (2 ^ 32 - 10))) =
      some (some (.ARM64MOVWstore, #[3, 5, 1]), true, true) ∧
    returnsInt (run Env.p1 stwTabs stwFunc [] trcMem 1) (2 ^ 32 - 10) = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a narrow store of a
truncation: on `stw`, the checked lower's `v7` is `MOVWstore v3 v5 v1` (the narrowing `Copy` it
read is gone, `stValPick`), and every returning or panicking `run` of `stw` is, up to refinement, a
`runL` of the result. -/
theorem stw_lower :
    ∃ out, lowerChecked stwPassEnv stwFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 7).map (fun v => (v.op, v.args)) = some (.ARM64MOVWstore, #[3, 5, 1]) ∧
      (∃ f', GoFV.Proof.Low.Contract stwFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.RewriteCheck.roSyms stwPassEnv.tables stwFunc) env mem)
        out.tables out.func stwPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.RewriteCheck.roSyms stwPassEnv.tables stwFunc) env mem → ∀ fuel,
        (run env stwTabs stwFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env stwTabs stwFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := stw_checks
  cases hc : lowerChecked stwPassEnv stwFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h7, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h7, GoFV.Proof.Low.lower_refines hc stw_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc stw_generic stw_noFma hE hro hd⟩

/-- The tables of `stx` with `int32` (type 5) and the `Store`'s type aux `int32` (aux 9). -/
def sxwTabs : Tables :=
  { stxTabs with
    types := stxTabs.types.set! 5 (some (mkT .INT32 (some 4) "int32"))
    auxes := stxTabs.auxes.push (some { fmt := GoStr.ofString "int32", kind := .type 5 }) }

/-- `sxw`, the input of `lower`. -/
def sxwFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 8
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[8] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 1 #[] 1),
    some (mkVI 2 .ArgIntReg 3 0 (some 6) p0 1 #[] 1),
    some (mkVI 3 .ArgIntReg 2 1 (some 7) p0 2 #[] 1),
    some (mkV 4 .AddPtr 3 none p0 2 #[2, 3] 1),
    some (mkV 5 .Trunc64to32 5 none p0 1 #[3] 1),
    some (mkV 6 .Store 28 (some 9) p0 2 #[4, 5, 1] 1),
    some (mkV 7 .Load 2 none p0 1 #[4, 6] 1),
    some (mkV 8 .MakeResult 33 none p0 1 #[7, 6] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `sxw`. -/
def sxwPassEnv : PassEnv := { stxPassEnv with funcName := GoStr.ofString "sxw", tables := sxwTabs }

theorem sxw_generic : sxwFunc.lowered = false := by decide +kernel

/-- `sxw` has no fused multiply-add shape: its contraction is itself. -/
theorem sxw_noFma : GoFV.Opt.FmaContract.contractAll sxwFunc = sxwFunc := by decide +kernel

set_option synthInstance.maxSize 2048 in
/-- By kernel evaluation: the checked lower keeps a lowered result whose `v6` is `MOVWstoreidx v2
v3 v3 v1`, and `sxw` returns 8 under `run` of the input and `runL` of the result. -/
theorem sxw_checks :
    (lowerChecked sxwPassEnv sxwFunc).toOption.map (fun o =>
      ((o.func.value? 6).map (fun v => (v.op, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func ldxArgs ldxMem 1) 8)) =
      some (some (.ARM64MOVWstoreidx, #[2, 3, 3, 1]), true, true) ∧
    returnsInt (run Env.p1 sxwTabs sxwFunc ldxArgs ldxMem 1) 8 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a narrow indexed store
of a truncation: on `sxw`, the checked lower's `v6` is `MOVWstoreidx v2 v3 v3 v1` (the narrowing
`Copy` its value was is gone, `stValPick`), and every returning or panicking `run` of `sxw` is, up
to refinement, a `runL` of the result. -/
theorem sxw_lower :
    ∃ out, lowerChecked sxwPassEnv sxwFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 6).map (fun v => (v.op, v.args)) = some (.ARM64MOVWstoreidx, #[2, 3, 3, 1]) ∧
      (∃ f', GoFV.Proof.Low.Contract sxwFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.RewriteCheck.roSyms sxwPassEnv.tables sxwFunc) env mem)
        out.tables out.func sxwPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.RewriteCheck.roSyms sxwPassEnv.tables sxwFunc) env mem → ∀ fuel,
        (run env sxwTabs sxwFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env sxwTabs sxwFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := sxw_checks
  cases hc : lowerChecked sxwPassEnv sxwFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h6, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h6, GoFV.Proof.Low.lower_refines hc sxw_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc sxw_generic sxw_noFma hE hro hd⟩

end GoFV.Proof.Witness
