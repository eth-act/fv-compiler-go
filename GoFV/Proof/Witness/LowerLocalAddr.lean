import GoFV.Proof.Witness.LowerLoadStore

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower` on frame addresses: `lad` (hand-written, issue #385)

`lad() int { var x int; var y *int; x = 5; y = &x; return *y }` as `lower` sees it (one block:
`v4 = LocalAddr <*int> {x} v2 v1` and `v6 = LocalAddr <**int> {y} v2 v5` of `v2 = SP`, the stores
`v5 = Store {int} v4 v3 v1` of `v3 = Const64 [5]` and `v7 = Store {*int} v6 v4 v5`, the loads
`v8 = Load <*int> v6 v7` and `v9 = Load <int> v8 v7`, returned by `v10 = MakeResult v9 v7`). The
checked lower with the proven `ARM64.rules` fires `(LocalAddr <t> {sym} base _) &&
!t.Elem().HasPointers() => (MOVDaddr {sym} base)` (310) at `v4` and `(LocalAddr <t> {sym} base mem)
&& t.Elem().HasPointers() => (MOVDaddr {sym} (SPanchored base mem))` (309) at `v6` (a fresh
`v11 = SPanchored v2 v5`), atoms the validator pairs by `addrLower`, besides the stores, loads and
the constant. The frame addresses then fold into the stores (`v5 = MOVDstore {x} v2 v3 v1`, `v7 =
MOVDstore {y} v11 v4 v5`) and into the load `v8 = MOVDload {y} v11 v7` (`frameFold`), so `v6` is
dead. The validator accepts the log, and by `lower_refines` every returning or panicking `run` of
`lad` is, up to refinement, a `runL` of the result; both return 5.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

-- `DecidableEq` of the nested options of tuples below exceeds the default instance size.
set_option synthInstance.maxSize 1024

/-- `abiInfo` of `lad`: no parameters, one integer result. -/
def ladABI : CallABI :=
  { abi := 1, nin := 0, nout := 1, spillOff := 0, spillSize := 0, inRegs := 0, outRegs := 1,
    params := #[{ out := true, index := 0, type := 2, name := some 3, regs := #[0],
                  offset := -1 }] }

/-- The definition tables: `int` (type 2), `*int` (3), `uintptr` (4), `**int` (5), `mem` (28), the
results tuple (33), the `AuxCall` of `lad`, its result name, the frame variables `x` (4) and `y`
(5), and the `Store`s' type auxes (6, 7). -/
def ladTabs : Tables where
  types :=
    let t := Array.replicate 34 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func() int" (.func 0 0 1 #[])))
    let t := t.set! 2 (some (mkT .INT (some 8) "int"))
    let t := t.set! 3 (some { mkT .PTR (some 8) "*int" (.elem 2) with flags := { hasptr := true } })
    let t := t.set! 4 (some (mkT .UINTPTR (some 8) "uintptr"))
    let t := t.set! 5 (some { mkT .PTR (some 8) "**int" (.elem 3) with flags := { hasptr := true } })
    let t := t.set! 28 (some (mkT .SSA none "mem"))
    let t := t.set! 31 (some (mkT .SSA none "void"))
    t.set! 33 (some (mkT .RESULTS none "int,mem" (.results #[2, 28])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.lad}", kind := .call (some 2) (some ladABI) },
    some { fmt := GoStr.ofString "main.lad",
           kind := .sym (GoStr.ofString "main.lad") 1 "" 0 default none none none #[] none },
    some (paramName "~r0" .PPARAMOUT 0),
    some (paramNameT "x" .PAUTO 2 (-8)),
    some (paramNameT "y" .PAUTO 3 (-16)),
    some { fmt := GoStr.ofString "int", kind := .type 2 },
    some { fmt := GoStr.ofString "*int", kind := .type 3 }]

/-- `lad`, the input of `lower`. -/
def ladFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 10
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[10] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 2 #[] 1),
    some (mkV 2 .SP 4 none p0 2 #[] 1),
    some (mkVI 3 .Const64 2 5 none p0 1 #[] 1),
    some (mkV 4 .LocalAddr 3 (some 4) p0 2 #[2, 1] 1),
    some (mkV 5 .Store 28 (some 6) p0 2 #[4, 3, 1] 1),
    some (mkV 6 .LocalAddr 5 (some 5) p0 2 #[2, 5] 1),
    some (mkV 7 .Store 28 (some 7) p0 3 #[6, 4, 5] 1),
    some (mkV 8 .Load 3 none p0 1 #[6, 7] 1),
    some (mkV 9 .Load 2 none p0 1 #[8, 7] 1),
    some (mkV 10 .MakeResult 33 none p0 1 #[9, 7] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` (arm64, the export's fixed configuration; `typ.Uintptr` is
type 4). -/
def ladPassEnv : PassEnv :=
  { laPassEnv with funcName := GoStr.ofString "lad", tables := ladTabs,
                   typs := #[("Int", 2), ("Uintptr", 4), ("Mem", 28), ("Void", 31)] }

theorem lad_generic : ladFunc.lowered = false := by decide +kernel

/-- `lad` has no fused multiply-add shape: its contraction is itself. -/
theorem lad_noFma : GoFV.Opt.FmaContract.contractAll ladFunc = ladFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose `v4` is `MOVDaddr`, whose
`v8` loads `{y}` from the fresh `v11 = SPanchored` (the frame address `v6` folded in), and `lad`
returns 5 under `run` of the input and `runL` of the result. -/
theorem lad_checks :
    (lowerChecked ladPassEnv ladFunc).toOption.map (fun o =>
      ((o.func.value? 4).map (·.op), (o.func.value? 8).map (fun v => (v.op, v.args, v.aux)),
        (o.func.value? 11).map (·.op), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [] {} 1) 5)) =
      some (some .ARM64MOVDaddr, some (.ARM64MOVDload, #[11, 7], some 5), some .SPanchored, true,
        true) ∧
    returnsInt (run Env.p1 ladTabs ladFunc [] {} 1) 5 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on frame addresses: on
`lad`, the checked lower lowers `v4` to `MOVDaddr` and folds `y`'s address into the load `v8` (on a
fresh `SPanchored`), and every returning or panicking `run` of `lad` is, up to refinement, a `runL`
of the result. -/
theorem lad_lower :
    ∃ out, lowerChecked ladPassEnv ladFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 4).map (·.op) = some .ARM64MOVDaddr ∧
      (out.func.value? 8).map (fun v => (v.op, v.args, v.aux)) =
        some (.ARM64MOVDload, #[11, 7], some 5) ∧
      (out.func.value? 11).map (·.op) = some .SPanchored ∧
      (∃ f', GoFV.Proof.Low.Contract ladFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.RewriteCheck.roSyms ladPassEnv.tables ladFunc) env mem)
        out.tables out.func ladPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.RewriteCheck.roSyms ladPassEnv.tables ladFunc) env mem → ∀ fuel,
        (run env ladTabs ladFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env ladTabs ladFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := lad_checks
  cases hc : lowerChecked ladPassEnv ladFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h4, h6, h11, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h4, h6, h11, GoFV.Proof.Low.lower_refines hc lad_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc lad_generic lad_noFma hE hro hd⟩

end GoFV.Proof.Witness
