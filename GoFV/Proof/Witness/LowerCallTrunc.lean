import GoFV.Proof.Witness.LowerTrunc

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower` passing a truncation to a call: `tcl` (hand-written, issue #385)

`tcl() int { return f(int32(g)) }` with a global `g` and `f(int32) int` as `lower` sees it (one
block: `v3 = Addr <*int> {g} v2` of `v2 = SB`, `v4 = Load <int> v3 v1`, `v5 = Trunc64to32 <int32>
v4`, `v6 = StaticCall {f} v5 v1`, `v7 = SelectN [0] v6`, `v8 = SelectN [1] v6`, returned by `v9 =
MakeResult v7 v8`). The checked lower fires `(Trunc64to32 ...) => (Copy ...)` (196) and
`(StaticCall ...) => (CALLstatic ...)`; `applyRewrite` eliminates the `Copy` inline, so the built
`v6` is `CALLstatic {f} v4 v1`: the validator accepts the call's argument, which the narrowing
`Copy` `v5` copies and which keeps the 32 bits of the `int32` leaf the call fits its register
piece at (`truncFitL`, `GoFV.Proof.Low.fitPiece_retypeL`). By `lower_refines` every returning or
panicking `run` of `tcl` is, up to refinement, a `runL` of the result; on `g` holding `2^32 - 5`
and `f` returning its argument, both return `-5`.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- `abiInfo` of `main.f`: one `int32` register parameter, one `int` result. -/
def tclABI : CallABI :=
  { abi := 1, nin := 1, nout := 1, spillOff := 8, spillSize := 8, inRegs := 1, outRegs := 1,
    params := #[{ out := false, index := 0, type := 5, name := none, regs := #[0], offset := 0 },
                { out := true, index := 0, type := 2, name := none, regs := #[0], offset := -1 }] }

/-- The tables of `trc` with the call of `main.f` (aux 6) and its symbol (aux 7). -/
def tclTabs : Tables :=
  { trcTabs with
    auxes := trcTabs.auxes ++
      #[some { fmt := GoStr.ofString "AuxCall{main.f}", kind := .call (some 7) (some tclABI) },
        some { fmt := GoStr.ofString "main.f",
               kind := .sym (GoStr.ofString "main.f") 1 "" 0 default none none none #[] none }] }

/-- `tcl`, the input of `lower`. -/
def tclFunc : Func where
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
    some (mkV 3 .Addr 3 (some 4) p0 1 #[2] 1),
    some (mkV 4 .Load 2 none p0 1 #[3, 1] 1),
    some (mkV 5 .Trunc64to32 5 none p0 1 #[4] 1),
    some (mkV 6 .StaticCall 33 (some 6) p0 2 #[5, 1] 1),
    some (mkVI 7 .SelectN 2 0 none p0 1 #[6] 1),
    some (mkVI 8 .SelectN 28 1 none p0 1 #[6] 1),
    some (mkV 9 .MakeResult 33 none p0 1 #[7, 8] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `tcl`. -/
def tclPassEnv : PassEnv :=
  { gstPassEnv with funcName := GoStr.ofString "tcl", tables := tclTabs }

/-- The environment: `main.f` returns its `int32` argument sign-extended. -/
def tclEnv : Env where
  extern n := if n == "main.f" then some fun args _ m =>
      match args with
      | [.int .w32 x] => .returned [.int .w64 (x.signExtend 64)] m
      | _ => .stuck "main.f"
    else none

theorem tcl_generic : tclFunc.lowered = false := by decide +kernel

/-- `tcl` has no fused multiply-add shape: its contraction is itself. -/
theorem tcl_noFma : GoFV.Opt.FmaContract.contractAll tclFunc = tclFunc := by decide +kernel

set_option synthInstance.maxSize 2048 in
/-- By kernel evaluation: the checked lower keeps a lowered result whose `v6` is
`CALLstatic {f} v4 v1`, and `tcl` returns `-5` under `run` of the input and `runL` of the
result. -/
theorem tcl_checks :
    (lowerChecked tclPassEnv tclFunc).toOption.map (fun o =>
      ((o.func.value? 6).map (fun v => (v.op, v.args)), o.func.lowered,
        returnsInt (runL tclEnv o.tables o.func [] trcMem 1) (-5))) =
      some (some (.ARM64CALLstatic, #[4, 1]), true, true) ∧
    returnsInt (run tclEnv tclTabs tclFunc [] trcMem 1) (-5) = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a call of a
truncation: on `tcl`, the checked lower's `v6` is `CALLstatic {f} v4 v1` (the narrowing `Copy` it
read is gone, `truncFitL`), and every returning or panicking `run` of `tcl` is, up to
refinement, a `runL` of the result. -/
theorem tcl_lower :
    ∃ out, lowerChecked tclPassEnv tclFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 6).map (fun v => (v.op, v.args)) = some (.ARM64CALLstatic, #[4, 1]) ∧
      (∃ f', GoFV.Proof.Low.Contract tclFunc f' ∧
        RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func tclPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem fuel, (run env tclTabs tclFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env tclTabs tclFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := tcl_checks
  cases hc : lowerChecked tclPassEnv tclFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h6, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h6, GoFV.Proof.Low.lower_refines hc tcl_generic,
      fun env hE args mem fuel hd => GoFV.Proof.Low.lower_refines_run hc tcl_generic tcl_noFma hE hd⟩

end GoFV.Proof.Witness
