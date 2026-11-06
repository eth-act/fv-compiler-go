import GoFV.Proof.Witness.LowerStoreSym

/-!
# Witness function for `lower` on an atomic load and a `uintptr` address: `ald` (hand-written, issue #385)

`ald() int { x := atomic.LoadUint64(&g); *(*uintptr)(unsafe.Pointer(&g)) = uintptr(unsafe.Pointer(&g));
return int(x) }` with a global `g` as `lower` sees it (one block: `v3 = Addr <*int> {g} v2` of `v2 =
SB`, `v4 = AtomicLoad64 <(int,mem)> v3 v1`, its selectors `v5`/`v6`, `v7 = Addr <uintptr> {g} v2`,
`v8 = Store {uintptr} v3 v7 v6`, returned by `v9 = MakeResult v5 v8`): the checked lower fires
`(Addr {sym} base) => (MOVDaddr {sym} base)` (308) at the pointer shape and at the `uintptr` shape
(`topOKL`'s word shapes), `(AtomicLoad64 ...) => (LDAR ...)` (484, a term of lowered SSA,
`pureActOp`) and the store lowering with the global's address folded in (329, 893). By
`lower_refines` every returning or panicking `run` of `ald` is, up to refinement, a `runL` of the
result; with `g = 5` both return 5.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- The tables of `gst` with the tuple `(int,mem)` (type 30), `ald`'s names and the `Store`'s type
aux `uintptr` (5). -/
def aldTabs : Tables where
  types := gstTabs.types.set! 30 (some (mkT .TUPLE none "(int,mem)" (.tuple 2 28)))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.ald}", kind := .call (some 2) (some ladABI) },
    some { fmt := GoStr.ofString "main.ald",
           kind := .sym (GoStr.ofString "main.ald") 1 "" 0 default none none none #[] none },
    some (paramName "~r0" .PPARAMOUT 0),
    some { fmt := GoStr.ofString "main.g",
           kind := .sym (GoStr.ofString "main.g") 0 "" 8 default none none none #[] none },
    some { fmt := GoStr.ofString "uintptr", kind := .type 4 }]

/-- `ald`, the input of `lower`. -/
def aldFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 9
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[9] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8, 9])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 1 #[] 1),
    some (mkV 2 .SB 4 none p0 2 #[] 1),
    some (mkV 3 .Addr 3 (some 4) p0 2 #[2] 1),
    some (mkV 4 .AtomicLoad64 30 none p0 2 #[3, 1] 1),
    some (mkV 5 .Select0 2 none p0 1 #[4] 1),
    some (mkV 6 .Select1 28 none p0 1 #[4] 1),
    some (mkV 7 .Addr 4 (some 4) p0 1 #[2] 1),
    some (mkV 8 .Store 28 (some 5) p0 1 #[3, 7, 6] 1),
    some (mkV 9 .MakeResult 33 none p0 1 #[5, 8] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `ald`. -/
def aldPassEnv : PassEnv :=
  { gstPassEnv with funcName := GoStr.ofString "ald", tables := aldTabs }

/-- The global `main.g` holding 5. -/
def aldMem : Mem :=
  { blocks := #[(.global "main.g", { data := #[.b 5, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0] })] }

theorem ald_generic : aldFunc.lowered = false := by decide +kernel

/-- `ald` has no fused multiply-add shape: its contraction is itself. -/
theorem ald_noFma : GoFV.Opt.FmaContract.contractAll aldFunc = aldFunc := by decide +kernel

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 200000 in
/-- By kernel evaluation: the checked lower keeps a lowered result whose `v4` is `LDAR v3 v1` and
whose `v7` is the `uintptr` `MOVDaddr {g} v2`, and `ald` returns 5 under `run` of the input and
`runL` of the result. -/
theorem ald_checks :
    (lowerChecked aldPassEnv aldFunc).toOption.map (fun o =>
      ((o.func.value? 4).map (fun v => (v.op, v.auxInt, v.aux, v.args)),
        (o.func.value? 7).map (fun v => (v.op, v.auxInt, v.aux, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [] aldMem 1) 5)) =
      some (some (.ARM64LDAR, 0, none, #[3, 1]), some (.ARM64MOVDaddr, 0, some 4, #[2]), true, true) ∧
    returnsInt (run Env.p1 aldTabs aldFunc [] aldMem 1) 5 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on an atomic load and an
`Addr` at the `uintptr` shape: on `ald`, the checked lower lowers `AtomicLoad64` to `LDAR` and the
`uintptr` `Addr` to `MOVDaddr`, and every returning or panicking `run` of `ald` is, up to
refinement, a `runL` of the result. -/
theorem ald_lower :
    ∃ out, lowerChecked aldPassEnv aldFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 4).map (fun v => (v.op, v.auxInt, v.aux, v.args)) =
        some (.ARM64LDAR, 0, none, #[3, 1]) ∧
      (out.func.value? 7).map (fun v => (v.op, v.auxInt, v.aux, v.args)) =
        some (.ARM64MOVDaddr, 0, some 4, #[2]) ∧
      (∃ f', GoFV.Proof.Low.Contract aldFunc f' ∧
        RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func aldPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem fuel, (run env aldTabs aldFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env aldTabs aldFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := ald_checks
  cases hc : lowerChecked aldPassEnv aldFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h4, h7, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h4, h7, GoFV.Proof.Low.lower_refines hc ald_generic,
      fun env hE args mem fuel hd => GoFV.Proof.Low.lower_refines_run hc ald_generic ald_noFma hE hd⟩

end GoFV.Proof.Witness
