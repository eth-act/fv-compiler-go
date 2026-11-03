import GoFV.Proof.Witness.LowerLoadFold

/-!
# Witness function for `lower` copying across pointer shapes: `cpy` (hand-written, issue #385)

`cpy(p *[2]int) int { return p[0] }` as `lower` sees it (one block: `v3 = OffPtr <*int> [0] v2` of
the register argument `v2 : *[2]int`, `v4 = Load <int> v3 v1`, returned by `v5 = MakeResult v4
v1`). The checked lower with the proven `ARM64.rules` fires `(OffPtr [off] ptr) => (ADDconst [off]
ptr)` (306) and then `(ADDconst [0] x) => x` (1201): `v3` becomes a `Copy` of `v2`, a value of
another pointer shape (`*[2]int` for `*int`, which `copyShapeOK` admits, `copyCompat`); the load
then reads `v2` (`MOVDload v2 v1`, 320). By `lower_refines` every returning or panicking `run` of
`cpy` is, up to refinement, a `runL` of the result; on `ldo`'s 16-byte heap block (7 at offset
8, 0 at offset 0) both return 0.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- `abiInfo` of `cpy`: one `*[2]int` register parameter, one integer result. -/
def cpyABI : CallABI :=
  { abi := 1, nin := 1, nout := 1, spillOff := 8, spillSize := 8, inRegs := 1, outRegs := 1,
    params := #[{ out := false, index := 0, type := 8, name := some 3, regs := #[0], offset := 0 },
                { out := true, index := 0, type := 2, name := some 4, regs := #[0],
                  offset := -1 }] }

/-- The tables of `ldst` with `[2]int` (type 7) and `*[2]int` (8) for the parameter. -/
def cpyTabs : Tables where
  types :=
    let t := ldsTabs.types
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(*[2]int) int" (.func 0 1 1 #[])))
    let t := t.set! 7 (some (mkT .ARRAY (some 16) "[2]int" (.array 2 2)))
    t.set! 8 (some (mkT .PTR (some 8) "*[2]int" (.elem 7)))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.cpy}", kind := .call (some 2) (some cpyABI) },
    some { fmt := GoStr.ofString "main.cpy",
           kind := .sym (GoStr.ofString "main.cpy") 1 "" 0 default none none none #[] none },
    some (paramNameT "p" .PPARAM 8 0), some (paramName "~r0" .PPARAMOUT 0),
    some { fmt := GoStr.ofString "p+0", kind := .nameOff 3 0 },
    some { fmt := GoStr.ofString "int", kind := .type 2 }]

/-- `cpy`, the input of `lower`. -/
def cpyFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 5
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[5] #[] #[] #[1, 2, 3, 4, 5])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 2 #[] 1),
    some (mkVI 2 .ArgIntReg 8 0 (some 5) p0 1 #[] 1),
    some (mkVI 3 .OffPtr 3 0 none p0 1 #[2] 1),
    some (mkV 4 .Load 2 none p0 1 #[3, 1] 1),
    some (mkV 5 .MakeResult 33 none p0 1 #[4, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` for `cpy`. -/
def cpyPassEnv : PassEnv :=
  { laPassEnv with funcName := GoStr.ofString "cpy", tables := cpyTabs }

theorem cpy_generic : cpyFunc.lowered = false := by decide +kernel

/-- `cpy` has no fused multiply-add shape: its contraction is itself. -/
theorem cpy_noFma : GoFV.Opt.FmaContract.contractAll cpyFunc = cpyFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose `v4` is `MOVDload v2 v1`
(the `Copy` `v3` of `v2` read through), and `cpy` returns 0 under `run` of the input and `runL`
of the result. -/
theorem cpy_checks :
    (lowerChecked cpyPassEnv cpyFunc).toOption.map (fun o =>
      ((o.func.value? 4).map (fun v => (v.op, v.auxInt, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func ldsArgs ldoMem 1) 0)) =
      some (some (.ARM64MOVDload, 0, #[2, 1]), true, true) ∧
    returnsInt (run Env.p1 cpyTabs cpyFunc ldsArgs ldoMem 1) 0 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on `ADDconst [0] x => x`
across pointer shapes: on `cpy`, the checked lower copies the `*[2]int` argument for the `*int`
`OffPtr` (`MOVDload v2 v1`), and every returning or panicking `run` of `cpy` is, up to
refinement, a `runL` of the result. -/
theorem cpy_lower :
    ∃ out, lowerChecked cpyPassEnv cpyFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 4).map (fun v => (v.op, v.auxInt, v.args)) =
        some (.ARM64MOVDload, 0, #[2, 1]) ∧
      (∃ f', GoFV.Proof.Low.Contract cpyFunc f' ∧
        RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func cpyPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem fuel, (run env cpyTabs cpyFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env cpyTabs cpyFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := cpy_checks
  cases hc : lowerChecked cpyPassEnv cpyFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h4, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h4, GoFV.Proof.Low.lower_refines hc cpy_generic,
      fun env hE args mem fuel hd => GoFV.Proof.Low.lower_refines_run hc cpy_generic cpy_noFma hE hd⟩

end GoFV.Proof.Witness
