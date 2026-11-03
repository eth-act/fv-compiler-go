import GoFV.Proof.Witness.LowerLocalAddr

/-!
# Witness functions for `lower` folding a frame variable's or a global's address into a store:
`lad`, `gst` (hand-written, issue #385)

`lad` (`GoFV/Proof/Witness/LowerLocalAddr.lean`): besides lowering its `LocalAddr`s to `MOVDaddr`,
the checked lower with the proven `ARM64.rules` folds both frame variables' addresses into the
stores (`(MOVDstore [off1] {sym1} (MOVDaddr [off2] {sym2} ptr) val mem) && canMergeSym(sym1,sym2)
… => (MOVDstore [off1+off2] {mergeSym(sym1,sym2)} ptr val mem)`, 893): `v5` becomes `MOVDstore
{x} v2 v3 v1` and `v7` `MOVDstore {y} v11 v4 v5` (the validator's `stFoldAddr`, a frame
variable).

`gst() int { g = 5; return g }` with a global `g` as `lower` sees it (one block: `v3 = Addr <*int>
{g} v2` of `v2 = SB`, `v5 = Store {int} v3 v4 v1` of `v4 = Const64 [5]`, `v6 = Load <int> v3 v5`,
returned by `v7 = MakeResult v6 v5`): the checked lower fires `(Addr {sym} base) => (MOVDaddr
{sym} base)` (308), `(Store {t} ptr val mem) && t.Size() == 8 && !t.IsFloat() => (MOVDstore ptr val
mem)` (329) and then 893, so `v5` becomes `MOVDstore {g} v2 v4 v1` (`stFoldAddr`, a global symbol).

By `lower_refines` every returning or panicking `run` of either is, up to refinement, a `runL` of
the result; both return 5.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

-- `DecidableEq` of the nested options of tuples below exceeds the default instance size.
set_option synthInstance.maxSize 1024

/-- By kernel evaluation: the checked lower of `lad` keeps a lowered result whose stores `v5` and
`v7` write at the frame variables `x` (aux 4) and `y` (aux 5). -/
theorem ladf_checks :
    (lowerChecked ladPassEnv ladFunc).toOption.map (fun o =>
      ((o.func.value? 5).map (fun v => (v.op, v.auxInt, v.aux, v.args)),
        (o.func.value? 7).map (fun v => (v.op, v.auxInt, v.aux, v.args)), o.func.lowered)) =
      some (some (.ARM64MOVDstore, 0, some 4, #[2, 3, 1]),
        some (.ARM64MOVDstore, 0, some 5, #[11, 4, 5]), true) := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on frame variables'
addresses folded into stores: on `lad`, the checked lower stores at `{x}` and `{y}` directly
(`MOVDstore {x} v2 v3 v1`, `MOVDstore {y} v11 v4 v5`), and every returning or panicking `run` of
`lad` is, up to refinement, a `runL` of the result. -/
theorem ladf_lower :
    ∃ out, lowerChecked ladPassEnv ladFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 5).map (fun v => (v.op, v.auxInt, v.aux, v.args)) =
        some (.ARM64MOVDstore, 0, some 4, #[2, 3, 1]) ∧
      (out.func.value? 7).map (fun v => (v.op, v.auxInt, v.aux, v.args)) =
        some (.ARM64MOVDstore, 0, some 5, #[11, 4, 5]) ∧
      (∃ f', GoFV.Proof.Low.Contract ladFunc f' ∧
        RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func ladPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem fuel, (run env ladTabs ladFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env ladTabs ladFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  have h1 := ladf_checks
  cases hc : lowerChecked ladPassEnv ladFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h5, h7, hl⟩ := h1
    exact ⟨out, rfl, hl, h5, h7, GoFV.Proof.Low.lower_refines hc lad_generic,
      fun env hE args mem fuel hd => GoFV.Proof.Low.lower_refines_run hc lad_generic lad_noFma hE hd⟩

/-- The definition tables of `gst`: `int` (type 2), `*int` (3), `uintptr` (4), `mem` (28), the
results tuple (33), the `AuxCall` of `gst`, its result name, the global `main.g` (aux 4) and the
`Store`'s type aux (5). -/
def gstTabs : Tables where
  types :=
    let t := Array.replicate 34 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func() int" (.func 0 0 1 #[])))
    let t := t.set! 2 (some (mkT .INT (some 8) "int"))
    let t := t.set! 3 (some (mkT .PTR (some 8) "*int" (.elem 2)))
    let t := t.set! 4 (some (mkT .UINTPTR (some 8) "uintptr"))
    let t := t.set! 28 (some (mkT .SSA none "mem"))
    let t := t.set! 31 (some (mkT .SSA none "void"))
    t.set! 33 (some (mkT .RESULTS none "int,mem" (.results #[2, 28])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.gst}", kind := .call (some 2) (some ladABI) },
    some { fmt := GoStr.ofString "main.gst",
           kind := .sym (GoStr.ofString "main.gst") 1 "" 0 default none none none #[] none },
    some (paramName "~r0" .PPARAMOUT 0),
    some { fmt := GoStr.ofString "main.g",
           kind := .sym (GoStr.ofString "main.g") 0 "" 8 default none none none #[] none },
    some { fmt := GoStr.ofString "int", kind := .type 2 }]

/-- `gst`, the input of `lower`. -/
def gstFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 7
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[7] #[] #[] #[1, 2, 3, 4, 5, 6, 7])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 1 #[] 1),
    some (mkV 2 .SB 4 none p0 1 #[] 1),
    some (mkV 3 .Addr 3 (some 4) p0 2 #[2] 1),
    some (mkVI 4 .Const64 2 5 none p0 1 #[] 1),
    some (mkV 5 .Store 28 (some 5) p0 2 #[3, 4, 1] 1),
    some (mkV 6 .Load 2 none p0 1 #[3, 5] 1),
    some (mkV 7 .MakeResult 33 none p0 1 #[6, 5] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `gst` (the fold's `ptr.Op != OpSB || !Flag_dynlink` reads
`config flagdynlink`). -/
def gstPassEnv : PassEnv :=
  { laPassEnv with funcName := GoStr.ofString "gst", tables := gstTabs,
                   typs := #[("Int", 2), ("Uintptr", 4), ("Mem", 28), ("Void", 31)],
                   config := laPassEnv.config.push ("flagdynlink", #[.word "0"]) }

/-- The global `main.g`, 8 zero bytes. -/
def gstMem : Mem := { blocks := #[(.global "main.g", { data := Array.replicate 8 (.b 0) })] }

theorem gst_generic : gstFunc.lowered = false := by decide +kernel

/-- `gst` has no fused multiply-add shape: its contraction is itself. -/
theorem gst_noFma : GoFV.Opt.FmaContract.contractAll gstFunc = gstFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose `v5` is `MOVDstore {g} v2
v4 v1`, and `gst` returns 5 under `run` of the input and `runL` of the result. -/
theorem gst_checks :
    (lowerChecked gstPassEnv gstFunc).toOption.map (fun o =>
      ((o.func.value? 5).map (fun v => (v.op, v.auxInt, v.aux, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [] gstMem 1) 5)) =
      some (some (.ARM64MOVDstore, 0, some 4, #[2, 4, 1]), true, true) ∧
    returnsInt (run Env.p1 gstTabs gstFunc [] gstMem 1) 5 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a global's address
folded into a store: on `gst`, the checked lower stores at `{g}` directly (`MOVDstore {g} v2 v4
v1`), and every returning or panicking `run` of `gst` is, up to refinement, a `runL` of the
result. -/
theorem gst_lower :
    ∃ out, lowerChecked gstPassEnv gstFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 5).map (fun v => (v.op, v.auxInt, v.aux, v.args)) =
        some (.ARM64MOVDstore, 0, some 4, #[2, 4, 1]) ∧
      (∃ f', GoFV.Proof.Low.Contract gstFunc f' ∧
        RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func gstPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem fuel, (run env gstTabs gstFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env gstTabs gstFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := gst_checks
  cases hc : lowerChecked gstPassEnv gstFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h5, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h5, GoFV.Proof.Low.lower_refines hc gst_generic,
      fun env hE args mem fuel hd => GoFV.Proof.Low.lower_refines_run hc gst_generic gst_noFma hE hd⟩

end GoFV.Proof.Witness
