import GoFV.Proof.Witness.LowerCallTrunc
import GoFV.Proof.Witness.LowerCondSel

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness functions for `lower` reading narrowing copies at narrow shapes: `cpa`, `cpm` (hand-written, issue #385)

`cpa(x, y int) int { var z int32; if x < 0 { z = int32(x) } else { z = int32(y) }; return int(z +
int32(x)) }` as `lower` sees it: entry block `b1` (`v4 = Const64 [0]`, `v5 = Less64 v2 v4` of the
register argument `x`, `v6 = Trunc64to32 <int32> v2`, `v7 = Trunc64to32 <int32> v3` of `y`, `If v5`
to `b2` and `b3`, both jumping to `b4`), then `b4`: `v8 = Phi <int32> v6 v7`, `v9 = Add32 <int32> v8
v6`, `v10 = SignExt32to64 <int> v9`, returned by `v11 = MakeResult v10 v1`. The checked lower fires
`(Trunc64to32 ...) => (Copy ...)` (196) and `(Add32 ...) => (ADD ...)`; `lower` eliminates the
`Copy`s inline, so `v8` is `Phi v2 v3` and `v9` is `ADD v8 v2`: the validator accepts the `Phi`'s
arguments, which the narrowing `Copy`s copy and which keep the 32 bits of the `Phi`'s shape
(`truncFitL`), and the `ADD`'s second, whose low 32 bits `v6` keeps at the `ADD`'s `int32` shape
(`lowReachL`).

`cpm() int32 { return int32(g) }` with a global `g` (`v3 = Addr <*int> {g} v2` of `v2 = SB`, `v4 =
Load <int> v3 v1`, `v5 = Trunc64to32 <int32> v4` returned by `v6 = MakeResult v5 v1`): the lowered
`v6` is `MakeResult v4 v1`, whose result leaf `int32` reads the 32 bits the `Copy` keeps
(`truncFitL`).

By `lower_refines` every returning or panicking `run` of either is, up to refinement, a `runL` of
the result; `cpa(-3, 7)` returns `-6` and `cpa(5, 7)` returns 12, and on `g` holding `2^32 - 5`
`cpm` returns the `int32` `-5`.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- An outcome returning the single `int32` `v`. -/
def returnsI32 : Outcome → BitVec 32 → Bool
  | .returned [.int .w32 x] _, v => x == v
  | _, _ => false

/-- The tables of `smin` with `int32` (type 5). -/
def cpaTabs : Tables :=
  { lcsTabs with types := lcsTabs.types.set! 5 (some (mkT .INT32 (some 4) "int32")) }

/-- `cpa`, the input of `lower`. -/
def cpaFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 11
  bidLast := 4
  blocks := #[1, 2, 3, 4]
  blockTab := #[none,
    some (mkB 1 .If p0 #[5] #[⟨2, 0⟩, ⟨3, 0⟩] #[] #[1, 2, 3, 4, 5, 6, 7]),
    some (mkB 2 .Plain p0 #[] #[⟨4, 0⟩] #[⟨1, 0⟩] #[]),
    some (mkB 3 .Plain p0 #[] #[⟨4, 1⟩] #[⟨1, 1⟩] #[]),
    some (mkB 4 .Ret p0 #[11] #[] #[⟨2, 0⟩, ⟨3, 0⟩] #[8, 9, 10, 11])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 1 #[] 1),
    some (mkVI 2 .ArgIntReg 2 0 (some 6) p0 2 #[] 1),
    some (mkVI 3 .ArgIntReg 2 1 (some 7) p0 1 #[] 1),
    some (mkVI 4 .Const64 2 0 none p0 1 #[] 1),
    some (mkV 5 .Less64 3 none p0 1 #[2, 4] 1),
    some (mkV 6 .Trunc64to32 5 none p0 2 #[2] 1),
    some (mkV 7 .Trunc64to32 5 none p0 1 #[3] 1),
    some (mkV 8 .Phi 5 none p0 1 #[6, 7] 4),
    some (mkV 9 .Add32 5 none p0 1 #[8, 6] 4),
    some (mkV 10 .SignExt32to64 2 none p0 1 #[9] 4),
    some (mkV 11 .MakeResult 33 none p0 1 #[10, 1] 4)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `cpa`. -/
def cpaPassEnv : PassEnv :=
  { lcsPassEnv with funcName := GoStr.ofString "cpa", tables := cpaTabs }

theorem cpa_generic : cpaFunc.lowered = false := by decide +kernel

/-- `cpa` has no fused multiply-add shape: its contraction is itself. -/
theorem cpa_noFma : GoFV.Opt.FmaContract.contractAll cpaFunc = cpaFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose `v8` is `Phi v2 v3` and
whose `v9` is `ADD v8 v2`, and `cpa(-3, 7) = -6`, `cpa(5, 7) = 12` under `run` of the input and
`runL` of the result. -/
theorem cpa_checks :
    (lowerChecked cpaPassEnv cpaFunc).toOption.map (fun o =>
      ((o.func.value? 8).map (fun v => (v.op, v.args)), (o.func.value? 9).map (fun v => (v.op, v.args)),
        o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [.int .w64 (-3), .int .w64 7] {} 3) (-6),
        returnsInt (runL Env.p1 o.tables o.func [.int .w64 5, .int .w64 7] {} 3) 12)) =
      some (some (.Phi, #[2, 3]), some (.ARM64ADD, #[8, 2]), true, true, true) ∧
    returnsInt (run Env.p1 cpaTabs cpaFunc [.int .w64 (-3), .int .w64 7] {} 3) (-6) = true ∧
    returnsInt (run Env.p1 cpaTabs cpaFunc [.int .w64 5, .int .w64 7] {} 3) 12 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a `Phi` and an `ADD`
of truncations: on `cpa`, the checked lower's `v8` is `Phi v2 v3` and its `v9` is `ADD v8 v2` (the
narrowing `Copy`s they read are gone, `truncFitL`, `lowReachL`), and every returning or panicking
`run` of `cpa` is, up to refinement, a `runL` of the result. -/
theorem cpa_lower :
    ∃ out, lowerChecked cpaPassEnv cpaFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 8).map (fun v => (v.op, v.args)) = some (.Phi, #[2, 3]) ∧
      (out.func.value? 9).map (fun v => (v.op, v.args)) = some (.ARM64ADD, #[8, 2]) ∧
      (∃ f', GoFV.Proof.Low.Contract cpaFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.LowerCheck.roPre cpaPassEnv.tables cpaFunc) env mem)
        out.tables out.func cpaPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.LowerCheck.roPre cpaPassEnv.tables cpaFunc) env mem → ∀ fuel,
        (run env cpaTabs cpaFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env cpaTabs cpaFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := cpa_checks
  cases hc : lowerChecked cpaPassEnv cpaFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h6, h7, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h6, h7, GoFV.Proof.Low.lower_refines hc cpa_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc cpa_generic cpa_noFma hE hro hd⟩

/-- The ABI of `cpm`: one `int32` register result. -/
def cpmABI : CallABI :=
  { abi := 1, nin := 0, nout := 1, spillOff := 0, spillSize := 0, inRegs := 0, outRegs := 1,
    params := #[{ out := true, index := 0, type := 5, name := some 3, regs := #[0],
                  offset := -1 }] }

/-- The tables of `trc` with `func() int32` (type 6), the results tuple `int32,mem` (7) and the
`AuxCall` of `cpm` (aux 1). -/
def cpmTabs : Tables :=
  { trcTabs with
    types := (trcTabs.types.set! 6 (some (mkT .FUNC (some 8) "func() int32" (.func 0 0 1 #[])))).set!
      7 (some (mkT .RESULTS none "int32,mem" (.results #[5, 28])))
    auxes := trcTabs.auxes.set! 1
      (some { fmt := GoStr.ofString "AuxCall{main.cpm}", kind := .call (some 2) (some cpmABI) }) }

/-- `cpm`, the input of `lower`. -/
def cpmFunc : Func where
  entry := 1
  type := 6
  ownAux := some 1
  vidLast := 6
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[6] #[] #[] #[1, 2, 3, 4, 5, 6])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 2 #[] 1),
    some (mkV 2 .SB 4 none p0 1 #[] 1),
    some (mkV 3 .Addr 3 (some 4) p0 1 #[2] 1),
    some (mkV 4 .Load 2 none p0 1 #[3, 1] 1),
    some (mkV 5 .Trunc64to32 5 none p0 1 #[4] 1),
    some (mkV 6 .MakeResult 7 none p0 1 #[5, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `cpm`. -/
def cpmPassEnv : PassEnv :=
  { gstPassEnv with funcName := GoStr.ofString "cpm", tables := cpmTabs }

theorem cpm_generic : cpmFunc.lowered = false := by decide +kernel

/-- `cpm` has no fused multiply-add shape: its contraction is itself. -/
theorem cpm_noFma : GoFV.Opt.FmaContract.contractAll cpmFunc = cpmFunc := by decide +kernel

set_option synthInstance.maxSize 2048 in
/-- By kernel evaluation: the checked lower keeps a lowered result whose `v6` is
`MakeResult v4 v1`, and `cpm` returns the `int32` `-5` under `run` of the input and `runL` of the
result. -/
theorem cpm_checks :
    (lowerChecked cpmPassEnv cpmFunc).toOption.map (fun o =>
      ((o.func.value? 6).map (fun v => (v.op, v.args)), o.func.lowered,
        returnsI32 (runL Env.p1 o.tables o.func [] trcMem 1) (-5))) =
      some (some (.MakeResult, #[4, 1]), true, true) ∧
    returnsI32 (run Env.p1 cpmTabs cpmFunc [] trcMem 1) (-5) = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a result through a
truncation: on `cpm`, the checked lower's `v6` is `MakeResult v4 v1` (the narrowing `Copy` it read
is gone, `truncFitL`), and every returning or panicking `run` of `cpm` is, up to refinement, a
`runL` of the result. -/
theorem cpm_lower :
    ∃ out, lowerChecked cpmPassEnv cpmFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 6).map (fun v => (v.op, v.args)) = some (.MakeResult, #[4, 1]) ∧
      (∃ f', GoFV.Proof.Low.Contract cpmFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.LowerCheck.roPre cpmPassEnv.tables cpmFunc) env mem)
        out.tables out.func cpmPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.LowerCheck.roPre cpmPassEnv.tables cpmFunc) env mem → ∀ fuel,
        (run env cpmTabs cpmFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env cpmTabs cpmFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := cpm_checks
  cases hc : lowerChecked cpmPassEnv cpmFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h6, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h6, GoFV.Proof.Low.lower_refines hc cpm_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc cpm_generic cpm_noFma hE hro hd⟩

end GoFV.Proof.Witness
