import GoFV.Proof.Witness.LowerLoadStore

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower` on an indexed load: `ldx` (hand-written, issue #385)

`ldx(p *int, i int) int { return *(*int)(unsafe.Add(p, i)) }` as `lower` sees it (one block:
`v4 = AddPtr <*int> v2 v3` of the register arguments, `v5 = Load <int> v4 v1`, returned by
`v6 = MakeResult v5 v1`). The checked lower with the proven `ARM64.rules` fires `(AddPtr ...) =>
(ADD ...)` (5; the validator checks that the index is a 64-bit integer, `setArgsOK`),
`(Load <t> ptr mem) && (is64BitInt(t) || isPtr(t)) => (MOVDload ptr mem)` (320) and `(MOVDload [off] {sym} (ADD ptr idx) mem) && off == 0 && sym == nil => (MOVDloadidx ptr idx
mem)` (695), so `v5` becomes `MOVDloadidx v2 v3 v1`, a lowered term; the validator accepts the
log, and by `lower_refines` every returning or panicking `run` of `ldx` is, up to refinement, a
`runL` of the result; on a 16-byte heap block holding 7 at offset 8 and `i = 8` both return 7.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- `abiInfo` of `ldx`: a pointer and an integer register parameter, one integer result. -/
def ldxABI : CallABI :=
  { abi := 1, nin := 2, nout := 1, spillOff := 8, spillSize := 16, inRegs := 2, outRegs := 1,
    params := #[{ out := false, index := 0, type := 3, name := some 3, regs := #[0], offset := 0 },
                { out := false, index := 1, type := 2, name := some 4, regs := #[1], offset := 8 },
                { out := true, index := 0, type := 2, name := some 5, regs := #[0],
                  offset := -1 }] }

/-- The definition tables: `int` (type 2), `*int` (3), `mem` (28), the results tuple (33), the
`AuxCall` of `ldx`, its parameter names and the `nameOff` auxes of the register arguments. -/
def ldxTabs : Tables where
  types :=
    let t := Array.replicate 34 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(*int, int) int" (.func 0 2 1 #[])))
    let t := t.set! 2 (some (mkT .INT (some 8) "int"))
    let t := t.set! 3 (some (mkT .PTR (some 8) "*int" (.elem 2)))
    let t := t.set! 28 (some (mkT .SSA none "mem"))
    let t := t.set! 31 (some (mkT .SSA none "void"))
    t.set! 33 (some (mkT .RESULTS none "int,mem" (.results #[2, 28])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.ldx}", kind := .call (some 2) (some ldxABI) },
    some { fmt := GoStr.ofString "main.ldx",
           kind := .sym (GoStr.ofString "main.ldx") 1 "" 0 default none none none #[] none },
    some (paramNameT "p" .PPARAM 3 0), some (paramName "i" .PPARAM 8),
    some (paramName "~r0" .PPARAMOUT 0),
    some { fmt := GoStr.ofString "p+0", kind := .nameOff 3 0 },
    some { fmt := GoStr.ofString "i+0", kind := .nameOff 4 0 }]

/-- `ldx`, the input of `lower`. -/
def ldxFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 6
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[6] #[] #[] #[1, 2, 3, 4, 5, 6])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 2 #[] 1),
    some (mkVI 2 .ArgIntReg 3 0 (some 6) p0 1 #[] 1),
    some (mkVI 3 .ArgIntReg 2 1 (some 7) p0 1 #[] 1),
    some (mkV 4 .AddPtr 3 none p0 1 #[2, 3] 1),
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

/-- The pass environment of `lower` on `ldx`. -/
def ldxPassEnv : PassEnv :=
  { laPassEnv with funcName := GoStr.ofString "ldx", tables := ldxTabs }

/-- A 16-byte heap block holding 7 at offset 8. -/
def ldxMem : Mem :=
  { blocks := #[(.heap 0, { data := (Array.replicate 16 (.b 0)).set! 8 (.b 7) })], nextHeap := 1 }

/-- The pointer to it and the index 8. -/
def ldxArgs : List Val := [.ptr ⟨.heap 0, 0⟩, .int .w64 8]

theorem ldx_generic : ldxFunc.lowered = false := by decide +kernel

/-- `ldx` has no fused multiply-add shape: its contraction is itself. -/
theorem ldx_noFma : GoFV.Opt.FmaContract.contractAll ldxFunc = ldxFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose `v5` is `MOVDloadidx v2
v3 v1`, and `ldx` returns 7 under `run` of the input and `runL` of the result. -/
theorem ldx_checks :
    (lowerChecked ldxPassEnv ldxFunc).toOption.map (fun o =>
      ((o.func.value? 5).map (fun v => (v.op, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func ldxArgs ldxMem 1) 7)) =
      some (some (.ARM64MOVDloadidx, #[2, 3, 1]), true, true) ∧
    returnsInt (run Env.p1 ldxTabs ldxFunc ldxArgs ldxMem 1) 7 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on an indexed load: on
`ldx`, the checked lower lowers the load of an `AddPtr` to `MOVDloadidx v2 v3 v1`, and every
returning or panicking `run` of `ldx` is, up to refinement, a `runL` of the result. -/
theorem ldx_lower :
    ∃ out, lowerChecked ldxPassEnv ldxFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 5).map (fun v => (v.op, v.args)) = some (.ARM64MOVDloadidx, #[2, 3, 1]) ∧
      (∃ f', GoFV.Proof.Low.Contract ldxFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.LowerCheck.roPre ldxPassEnv.tables ldxFunc) env mem)
        out.tables out.func ldxPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.LowerCheck.roPre ldxPassEnv.tables ldxFunc) env mem → ∀ fuel,
        (run env ldxTabs ldxFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env ldxTabs ldxFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := ldx_checks
  cases hc : lowerChecked ldxPassEnv ldxFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h5, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h5, GoFV.Proof.Low.lower_refines hc ldx_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc ldx_generic ldx_noFma hE hro hd⟩

end GoFV.Proof.Witness
