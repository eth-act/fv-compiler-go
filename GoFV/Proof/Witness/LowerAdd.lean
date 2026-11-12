import GoFV.Proof.Low.Lower
import GoFV.Proof.Witness.AddZero
import GoFV.Proof.Witness.ClampL

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower`: `add` (hand-written, issue #385)

`add(x, y int) int` as `lower` sees it (one block: `v4 = Add64 v2 v3` of the register arguments,
returned by `v5 = MakeResult v4 v1`). The checked lower with the proven `ARM64.rules`
(`GoFV.Opt.lowerChecked`) fires `(Add64 ...) => (ADD ...)` (`ARM64.rules:5`), the validator
accepts the log, the result is lowered (`v4 = ARM64ADD v2 v3`), and by `lower_refines` every
returning or panicking `run` of `add` is, up to refinement, a `runL` of the result; `add(3, 4)`
returns 7 under both.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- `abiInfo` of `add`: two integer register parameters, one integer result. -/
def laABI : CallABI :=
  { abi := 1, nin := 2, nout := 1, spillOff := 8, spillSize := 16, inRegs := 2, outRegs := 1,
    params := #[abiParam false 0 3 0, abiParam false 1 4 8, abiParam true 0 5 (-1)] }

/-- The definition tables: `int` (type 2), `mem` (28), the results tuple (33), the `AuxCall` of
`add`, its parameter names and the `nameOff` auxes of the register arguments. -/
def laTabs : Tables where
  types :=
    let t := Array.replicate 34 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(int, int) int" (.func 0 2 1 #[])))
    let t := t.set! 2 (some (mkT .INT (some 8) "int"))
    let t := t.set! 28 (some (mkT .SSA none "mem"))
    let t := t.set! 31 (some (mkT .SSA none "void"))
    t.set! 33 (some (mkT .RESULTS none "int,mem" (.results #[2, 28])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.add}", kind := .call (some 2) (some laABI) },
    some { fmt := GoStr.ofString "main.add",
           kind := .sym (GoStr.ofString "main.add") 1 "" 0 default none none none #[] none },
    some (paramName "x" .PPARAM 0), some (paramName "y" .PPARAM 8),
    some (paramName "~r0" .PPARAMOUT 0),
    some { fmt := GoStr.ofString "x+0", kind := .nameOff 3 0 },
    some { fmt := GoStr.ofString "y+0", kind := .nameOff 4 0 }]

/-- `add`, the input of `lower`. -/
def laFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 5
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[5] #[] #[] #[1, 2, 3, 4, 5])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 1 #[] 1),
    some (mkVI 2 .ArgIntReg 2 0 (some 6) p0 1 #[] 1),
    some (mkVI 3 .ArgIntReg 2 1 (some 7) p0 1 #[] 1),
    some (mkV 4 .Add64 2 none p0 1 #[2, 3] 1),
    some (mkV 5 .MakeResult 33 none p0 1 #[4, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` (arm64, the export's fixed configuration). -/
def laPassEnv : PassEnv where
  passName := "lower"
  pkg := GoStr.ofString "main"
  funcName := GoStr.ofString "add"
  abi := 1
  nosplit := false
  pgohot := false
  config := azPassEnv.config
  typs := #[("Int", 2), ("Mem", 28), ("Void", 31)]
  typeOrder := default
  tables := laTabs

theorem la_generic : laFunc.lowered = false := by decide +kernel

/-- `add` has no fused multiply-add shape: its contraction is itself. -/
theorem la_noFma : GoFV.Opt.FmaContract.contractAll laFunc = laFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose `v4` is `ARM64ADD v2 v3`,
and `add(3, 4) = 7` under `run` of the input and `runL` of the result. -/
theorem la_checks :
    (lowerChecked laPassEnv laFunc).toOption.map (fun o =>
      ((o.func.value? 4).map (fun v => (v.op, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [.int .w64 3, .int .w64 4] {} 1) 7)) =
      some (some (.ARM64ADD, #[2, 3]), true, true) ∧
    returnsInt (run Env.p1 laTabs laFunc [.int .w64 3, .int .w64 4] {} 1) 7 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`): on `add`, the checked
lower lowers `Add64` to `ARM64ADD`, and every returning or panicking `run` of `add` is, up to
refinement, a `runL` of the result. -/
theorem la_lower :
    ∃ out, lowerChecked laPassEnv laFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 4).map (·.op) = some .ARM64ADD ∧
      (∃ f', GoFV.Proof.Low.Contract laFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.LowerCheck.roPre laPassEnv.tables laFunc) env mem)
        out.tables out.func laPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.LowerCheck.roPre laPassEnv.tables laFunc) env mem → ∀ fuel,
        (run env laTabs laFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env laTabs laFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := la_checks
  cases hc : lowerChecked laPassEnv laFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h4, hl, -⟩ := h1
    refine ⟨out, rfl, hl, ?_, GoFV.Proof.Low.lower_refines hc la_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc la_generic la_noFma hE hro hd⟩
    cases hv : out.func.value? 4 with
    | none => rw [hv] at h4; cases h4
    | some v =>
      rw [hv] at h4
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h4
      exact congrArg some h4.1

end GoFV.Proof.Witness
