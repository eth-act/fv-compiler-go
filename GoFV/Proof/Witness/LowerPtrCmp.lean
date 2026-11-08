import GoFV.Proof.Witness.LowerCondSel
import GoFV.Proof.Witness.TraceFP

/-!
# Witness functions for `lower` on pointer compares: `pnn`, `peq` (hand-written, issue #385)

`pnn(p *int) bool { return p != nil }` as `lower` sees it (one block: `v3 = IsNonNil v2` of the
register argument `v2`, returned by `v4 = MakeResult v3 v1`). The checked lower fires `(IsNonNil
ptr) => (NotEqual (CMPconst [0] ptr))` (`ARM64.rules:450`): `v3` becomes `NotEqual v5` of a fresh
`v5 = CMPconst [0] v2`. On the heap pointer `heap 0 + 0` both return `true`; on the nil word 0
both return `false`; on the global pointer `g + 0`, a non-nil pointer without an address, both
return `true` (it has no register, `Arm64.ptrReg`, so `CMPconst [0]` compares it by provenance).
(A pointer outside its window, such as `heap 0 + (2^64 - 2^40)` whose address would be 0, is no
value since #385: `poison` as an argument.)

`peq(p, q *int) bool { return p == q }`: `v4 = EqPtr v2 v3`. The checked lower fires `(EqPtr x y)
=> (Equal (CMP x y))` (`243`, a fresh `v6 = CMP v2 v3`), then `(CMP x y) && canonLessThan(x,y) =>
(InvertFlags (CMP y x))` (`1003`) and `(Equal (InvertFlags x)) => (Equal x)` (`1374`): `v4`
becomes `Equal v7` of `v7 = CMP v3 v2`. On the frame variable `local 0 1` and the frame temporary
`temp 0 1` of the same name, which share an address, both return `false`; on the heap pointer
`heap 0 + 0` and the integer word `2^40` (its address) both return `true`.

By `lower_refines` every returning or panicking `run` of either is, up to refinement, a `runL` of
the result.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

-- `DecidableEq` of the nested options of tuples below exceeds the default instance size.
set_option synthInstance.maxSize 1024

/-- `abiInfo` of `pnn`/`peq`: two `*int` register parameters, one `bool` result. -/
def pcABI : CallABI :=
  { laABI with
    params := #[{ out := false, index := 0, type := 5, name := some 3, regs := #[0], offset := 0 },
      { out := false, index := 1, type := 5, name := some 4, regs := #[1], offset := 8 },
      { out := true, index := 0, type := 3, name := some 5, regs := #[0], offset := -1 }] }

/-- The `AuxCall` of `pnn`/`peq`. -/
def pcCall : AuxDef :=
  { fmt := GoStr.ofString "AuxCall{main.pnn}", kind := .call (some 2) (some pcABI) }

/-- The definition tables of `pnn`/`peq`: `smin`'s, `*int` (type 5), the results tuple `bool,mem`
(32), and the `*int` parameters `p`, `q` and the `bool` result. -/
def pcTabs : Tables :=
  { lcsTabs with
    auxes := (((lcsTabs.auxes.set! 1 (some pcCall)).set! 3
        (some (paramNameT "p" .PPARAM 5 0))).set! 4 (some (paramNameT "q" .PPARAM 5 8))).set! 5
        (some (paramNameT "~r0" .PPARAMOUT 3 0))
    types := ((lcsTabs.types.set! 1 (some (mkT .FUNC (some 8) "func(*int, *int) bool"
        (.func 0 2 1 #[])))).set! 5 (some (mkT .PTR (some 8) "*int" (.elem 2)))).set! 32
      (some (mkT .RESULTS none "bool,mem" (.results #[3, 28]))) }

/-- `pnn`, the input of `lower`. -/
def pnnFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 4
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[4] #[] #[] #[1, 2, 3, 4])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 1 #[] 1),
    some (mkVI 2 .ArgIntReg 5 0 (some 6) p0 1 #[] 1),
    some (mkV 3 .IsNonNil 3 none p0 1 #[2] 1),
    some (mkV 4 .MakeResult 32 none p0 1 #[3, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- `peq`, the input of `lower`. -/
def peqFunc : Func :=
  { pnnFunc with
    vidLast := 5
    blockTab := #[none, some (mkB 1 .Ret p0 #[5] #[] #[] #[1, 2, 3, 4, 5])]
    valueTab := #[none,
      some (mkV 1 .InitMem 28 none p0 1 #[] 1),
      some (mkVI 2 .ArgIntReg 5 0 (some 6) p0 1 #[] 1),
      some (mkVI 3 .ArgIntReg 5 1 (some 7) p0 1 #[] 1),
      some (mkV 4 .EqPtr 3 none p0 1 #[2, 3] 1),
      some (mkV 5 .MakeResult 32 none p0 1 #[4, 1] 1)] }

/-- The pass environment of `lower` on `pnn`/`peq`. -/
def pcPassEnv : PassEnv :=
  { lcsPassEnv with funcName := GoStr.ofString "pnn", tables := pcTabs }

/-- The heap pointer `heap 0 + 0` (address `2^40`). -/
def pcHeap : Ptr := ⟨.heap 0, 0⟩

/-- The global pointer `g + 0`: not nil, no address. -/
def pcGlob : Ptr := ⟨.global "g", 0⟩

theorem pnn_generic : pnnFunc.lowered = false := by decide +kernel

theorem peq_generic : peqFunc.lowered = false := by decide +kernel

/-- `pnn` has no fused multiply-add shape: its contraction is itself. -/
theorem pnn_noFma : GoFV.Opt.FmaContract.contractAll pnnFunc = pnnFunc := by decide +kernel

/-- `peq` has no fused multiply-add shape: its contraction is itself. -/
theorem peq_noFma : GoFV.Opt.FmaContract.contractAll peqFunc = peqFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose `v3` is `NotEqual v5` and
`v5` `CMPconst [0] v2`, and `pnn` returns `true` on `heap 0 + 0`, `false` on the word 0 and `true`
on `g + 0` under `run` of the input and `runL` of the result. -/
theorem pnn_checks :
    (lowerChecked pcPassEnv pnnFunc).toOption.map (fun o =>
      ((o.func.value? 3).map (fun v => (v.op, v.args)),
        (o.func.value? 5).map (fun v => (v.op, v.auxInt, v.args)), o.func.lowered,
        returnsBool (runL Env.p1 o.tables o.func [.ptr pcHeap, .int .w64 0] {} 1) true,
        returnsBool (runL Env.p1 o.tables o.func [.int .w64 0, .int .w64 0] {} 1) false,
        returnsBool (runL Env.p1 o.tables o.func [.ptr pcGlob, .int .w64 0] {} 1) true)) =
      some (some (.ARM64NotEqual, #[5]), some (.ARM64CMPconst, 0, #[2]), true, true, true, true) ∧
    returnsBool (run Env.p1 pcTabs pnnFunc [.ptr pcHeap, .int .w64 0] {} 1) true = true ∧
    returnsBool (run Env.p1 pcTabs pnnFunc [.int .w64 0, .int .w64 0] {} 1) false = true ∧
    returnsBool (run Env.p1 pcTabs pnnFunc [.ptr pcGlob, .int .w64 0] {} 1) true = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on `IsNonNil`
(`ARM64.rules:450`): on `pnn`, the checked lower tests the pointer by `NotEqual (CMPconst [0] p)`,
and every returning or panicking `run` of `pnn` is, up to refinement, a `runL` of the result. -/
theorem pnn_lower :
    ∃ out, lowerChecked pcPassEnv pnnFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 3).map (fun v => (v.op, v.args)) = some (.ARM64NotEqual, #[5]) ∧
      (out.func.value? 5).map (fun v => (v.op, v.auxInt, v.args)) =
        some (.ARM64CMPconst, 0, #[2]) ∧
      (∃ f', GoFV.Proof.Low.Contract pnnFunc f' ∧
        RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func pcPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem fuel, (run env pcTabs pnnFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env pcTabs pnnFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := pnn_checks
  cases hc : lowerChecked pcPassEnv pnnFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h3, h5, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h3, h5, GoFV.Proof.Low.lower_refines hc pnn_generic,
      fun env hE args mem fuel hd => GoFV.Proof.Low.lower_refines_run hc pnn_generic pnn_noFma hE hd⟩

/-- By kernel evaluation: the checked lower keeps a lowered result whose `v4` is `Equal v7` and
`v7` `CMP v3 v2`, and `peq` returns `false` on `local 0 1 + 0` and `temp 0 1 + 0` (one address)
and `true` on `heap 0 + 0` and the word `2^40` under `run` of the input and `runL` of the
result. -/
theorem peq_checks :
    (lowerChecked pcPassEnv peqFunc).toOption.map (fun o =>
      ((o.func.value? 4).map (fun v => (v.op, v.args)),
        (o.func.value? 7).map (fun v => (v.op, v.args)), o.func.lowered,
        returnsBool (runL Env.p1 o.tables o.func [.ptr ⟨.local 0 1, 0⟩, .ptr ⟨.temp 0 1, 0⟩] {} 1)
          false,
        returnsBool (runL Env.p1 o.tables o.func [.ptr pcHeap, .int .w64 (2 ^ 40)] {} 1) true)) =
      some (some (.ARM64Equal, #[7]), some (.ARM64CMP, #[3, 2]), true, true, true) ∧
    returnsBool (run Env.p1 pcTabs peqFunc [.ptr ⟨.local 0 1, 0⟩, .ptr ⟨.temp 0 1, 0⟩] {} 1)
      false = true ∧
    returnsBool (run Env.p1 pcTabs peqFunc [.ptr pcHeap, .int .w64 (2 ^ 40)] {} 1) true = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on `EqPtr`
(`ARM64.rules:243`): on `peq`, the checked lower compares the pointers by `Equal (CMP q p)`, and
every returning or panicking `run` of `peq` is, up to refinement, a `runL` of the result. -/
theorem peq_lower :
    ∃ out, lowerChecked pcPassEnv peqFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 4).map (fun v => (v.op, v.args)) = some (.ARM64Equal, #[7]) ∧
      (out.func.value? 7).map (fun v => (v.op, v.args)) = some (.ARM64CMP, #[3, 2]) ∧
      (∃ f', GoFV.Proof.Low.Contract peqFunc f' ∧
        RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func pcPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem fuel, (run env pcTabs peqFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env pcTabs peqFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := peq_checks
  cases hc : lowerChecked pcPassEnv peqFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h4, h7, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h4, h7, GoFV.Proof.Low.lower_refines hc peq_generic,
      fun env hE args mem fuel hd => GoFV.Proof.Low.lower_refines_run hc peq_generic peq_noFma hE hd⟩

end GoFV.Proof.Witness
