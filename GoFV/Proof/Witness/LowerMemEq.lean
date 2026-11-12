import GoFV.Proof.Witness.LowerAtomic
import GoFV.Proof.Witness.TraceFP

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower` on a memory comparison: `meq` (hand-written, issue #385)

`meq() bool { return g == g }` for a global `g` of an 8-byte array type, as `lower` sees it (one
block: `v3 = Addr <*int> {g} v2` of `v2 = SB`, `v4 = Const64 [8]`, `v5 = MemEq <bool> v3 v3 v4 v1`,
returned by `v6 = MakeResult v5 v1`): the checked lower fires `(Addr {sym} base) => (MOVDaddr {sym}
base)` (308), `(Const64 [c]) => (MOVDconst [c])` (182) and `(MemEq ...) => (LoweredMemEq ...)`
(458; both are terms whose meaning is Phase 1's `memEq`, `pureActOp`). By `lower_refines` every
returning or panicking `run` of `meq` is, up to refinement, a `runL` of the result; both return
`true`.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- The ABI of `meq`: one `bool` result (type 6) in a register. -/
def meqABI : CallABI :=
  { abi := 1, nin := 0, nout := 1, spillOff := 0, spillSize := 0, inRegs := 0, outRegs := 1,
    params := #[{ out := true, index := 0, type := 6, name := some 3, regs := #[0],
                  offset := -1 }] }

/-- The tables of `gst` with `func() bool` (type 1), `bool` (6) and the results `bool,mem` (33). -/
def meqTabs : Tables where
  types := (((gstTabs.types.set! 1 (some (mkT .FUNC (some 8) "func() bool" (.func 0 0 1 #[])))).set!
    6 (some (mkT .BOOL (some 1) "bool"))).set! 33
    (some (mkT .RESULTS none "bool,mem" (.results #[6, 28]))))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.meq}", kind := .call (some 2) (some meqABI) },
    some { fmt := GoStr.ofString "main.meq",
           kind := .sym (GoStr.ofString "main.meq") 1 "" 0 default none none none #[] none },
    some (paramName "~r0" .PPARAMOUT 0),
    some { fmt := GoStr.ofString "main.g",
           kind := .sym (GoStr.ofString "main.g") 0 "" 8 default none none none #[] none }]

/-- `meq`, the input of `lower`. -/
def meqFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 6
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[6] #[] #[] #[1, 2, 3, 4, 5, 6])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 2 #[] 1),
    some (mkV 2 .SB 4 none p0 1 #[] 1),
    some (mkV 3 .Addr 3 (some 4) p0 2 #[2] 1),
    some (mkVI 4 .Const64 2 8 none p0 1 #[] 1),
    some (mkV 5 .MemEq 6 none p0 1 #[3, 3, 4, 1] 1),
    some (mkV 6 .MakeResult 33 none p0 1 #[5, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `meq`. -/
def meqPassEnv : PassEnv :=
  { gstPassEnv with funcName := GoStr.ofString "meq", tables := meqTabs,
                    typs := gstPassEnv.typs.push ("Bool", 6) }

theorem meq_generic : meqFunc.lowered = false := by decide +kernel

/-- `meq` has no fused multiply-add shape: its contraction is itself. -/
theorem meq_noFma : GoFV.Opt.FmaContract.contractAll meqFunc = meqFunc := by decide +kernel

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 200000 in
/-- By kernel evaluation: the checked lower keeps a lowered result whose `v5` is `LoweredMemEq v3
v3 v4 v1`, and `meq` returns `true` under `run` of the input and `runL` of the result (`g = 5`). -/
theorem meq_checks :
    (lowerChecked meqPassEnv meqFunc).toOption.map (fun o =>
      ((o.func.value? 5).map (fun v => (v.op, v.args)), o.func.lowered,
        returnsBool (runL Env.p1 o.tables o.func [] aldMem 1) true)) =
      some (some (.ARM64LoweredMemEq, #[3, 3, 4, 1]), true, true) ∧
    returnsBool (run Env.p1 meqTabs meqFunc [] aldMem 1) true = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on `MemEq`: on `meq`, the
checked lower lowers `MemEq` to `LoweredMemEq`, and every returning or panicking `run` of `meq` is,
up to refinement, a `runL` of the result. -/
theorem meq_lower :
    ∃ out, lowerChecked meqPassEnv meqFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 5).map (fun v => (v.op, v.args)) =
        some (.ARM64LoweredMemEq, #[3, 3, 4, 1]) ∧
      (∃ f', GoFV.Proof.Low.Contract meqFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.LowerCheck.roPre meqPassEnv.tables meqFunc) env mem)
        out.tables out.func meqPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.LowerCheck.roPre meqPassEnv.tables meqFunc) env mem → ∀ fuel,
        (run env meqTabs meqFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env meqTabs meqFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := meq_checks
  cases hc : lowerChecked meqPassEnv meqFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h5, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h5, GoFV.Proof.Low.lower_refines hc meq_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc meq_generic meq_noFma hE hro hd⟩

end GoFV.Proof.Witness
