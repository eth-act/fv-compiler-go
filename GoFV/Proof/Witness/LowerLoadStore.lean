import GoFV.Proof.Low.Lower
import GoFV.Proof.Witness.LowerAdd
import GoFV.Proof.Witness.DecodedLen

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower` on memory: `ldst` (hand-written, issue #385)

`ldst(p *int) int { *p = 5; return *p }` as `lower` sees it (one block: `v4 = Store {int} v2 v3
v1` of the constant `v3 = Const64 [5]` at the register argument `v2`, `v5 = Load <int> v2 v4`,
returned by `v6 = MakeResult v5 v4`). The checked lower with the proven `ARM64.rules` fires
`(Const64 [c]) => (MOVDconst [c])` (182), `(Store {t} ptr val mem) && t.Size() == 8 &&
!t.IsFloat() => (MOVDstore ptr val mem)` (329, an atom the validator pairs by `memLower`) and
`(Load <t> ptr mem) && (is64BitInt(t) || isPtr(t)) => (MOVDload ptr mem)` (320, a lowered term),
the validator accepts the log, and by `lower_refines` every returning or panicking `run` of `ldst`
is, up to refinement, a `runL` of the result; on an 8-byte heap block both return 5.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- `abiInfo` of `ldst`: one pointer register parameter, one integer result. -/
def ldsABI : CallABI :=
  { abi := 1, nin := 1, nout := 1, spillOff := 8, spillSize := 8, inRegs := 1, outRegs := 1,
    params := #[{ out := false, index := 0, type := 3, name := some 3, regs := #[0], offset := 0 },
                { out := true, index := 0, type := 2, name := some 4, regs := #[0],
                  offset := -1 }] }

/-- The definition tables: `int` (type 2), `*int` (3), `mem` (28), the results tuple (33), the
`AuxCall` of `ldst`, its parameter names, the `nameOff` aux of the register argument and the
`Store`'s type aux (6). -/
def ldsTabs : Tables where
  types :=
    let t := Array.replicate 34 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(*int) int" (.func 0 1 1 #[])))
    let t := t.set! 2 (some (mkT .INT (some 8) "int"))
    let t := t.set! 3 (some (mkT .PTR (some 8) "*int" (.elem 2)))
    let t := t.set! 28 (some (mkT .SSA none "mem"))
    let t := t.set! 31 (some (mkT .SSA none "void"))
    t.set! 33 (some (mkT .RESULTS none "int,mem" (.results #[2, 28])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.ldst}", kind := .call (some 2) (some ldsABI) },
    some { fmt := GoStr.ofString "main.ldst",
           kind := .sym (GoStr.ofString "main.ldst") 1 "" 0 default none none none #[] none },
    some (paramNameT "p" .PPARAM 3 0), some (paramName "~r0" .PPARAMOUT 0),
    some { fmt := GoStr.ofString "p+0", kind := .nameOff 3 0 },
    some { fmt := GoStr.ofString "int", kind := .type 2 }]

/-- `ldst`, the input of `lower`. -/
def ldsFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 6
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[6] #[] #[] #[1, 2, 3, 4, 5, 6])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 1 #[] 1),
    some (mkVI 2 .ArgIntReg 3 0 (some 5) p0 2 #[] 1),
    some (mkVI 3 .Const64 2 5 none p0 1 #[] 1),
    some (mkV 4 .Store 28 (some 6) p0 2 #[2, 3, 1] 1),
    some (mkV 5 .Load 2 none p0 1 #[2, 4] 1),
    some (mkV 6 .MakeResult 33 none p0 1 #[5, 4] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` (arm64, the export's fixed configuration). -/
def ldsPassEnv : PassEnv :=
  { laPassEnv with funcName := GoStr.ofString "ldst", tables := ldsTabs }

/-- An 8-byte heap block. -/
def ldsMem : Mem := { blocks := #[(.heap 0, { data := Array.replicate 8 (.b 0) })], nextHeap := 1 }

/-- The pointer to it. -/
def ldsArgs : List Val := [.ptr ⟨.heap 0, 0⟩]

theorem lds_generic : ldsFunc.lowered = false := by decide +kernel

/-- `ldst` has no fused multiply-add shape: its contraction is itself. -/
theorem lds_noFma : GoFV.Opt.FmaContract.contractAll ldsFunc = ldsFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose `v4` is `MOVDstore` and
`v5` is `MOVDload`, and `ldst` returns 5 under `run` of the input and `runL` of the result. -/
theorem lds_checks :
    (lowerChecked ldsPassEnv ldsFunc).toOption.map (fun o =>
      ((o.func.value? 4).map (·.op), (o.func.value? 5).map (·.op), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func ldsArgs ldsMem 1) 5)) =
      some (some .ARM64MOVDstore, some .ARM64MOVDload, true, true) ∧
    returnsInt (run Env.p1 ldsTabs ldsFunc ldsArgs ldsMem 1) 5 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on loads and stores: on
`ldst`, the checked lower lowers `Store` to `MOVDstore` and `Load` to `MOVDload`, and every
returning or panicking `run` of `ldst` is, up to refinement, a `runL` of the result. -/
theorem lds_lower :
    ∃ out, lowerChecked ldsPassEnv ldsFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 4).map (·.op) = some .ARM64MOVDstore ∧
      (out.func.value? 5).map (·.op) = some .ARM64MOVDload ∧
      (∃ f', GoFV.Proof.Low.Contract ldsFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.RewriteCheck.roSyms ldsPassEnv.tables ldsFunc) env mem)
        out.tables out.func ldsPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.RewriteCheck.roSyms ldsPassEnv.tables ldsFunc) env mem → ∀ fuel,
        (run env ldsTabs ldsFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env ldsTabs ldsFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := lds_checks
  cases hc : lowerChecked ldsPassEnv ldsFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h4, h5, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h4, h5, GoFV.Proof.Low.lower_refines hc lds_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc lds_generic lds_noFma hE hro hd⟩

end GoFV.Proof.Witness
