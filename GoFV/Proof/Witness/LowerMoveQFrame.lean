import GoFV.Proof.Witness.LowerMoveQ
import GoFV.Proof.Witness.LowerLocalAddr

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower` on 128-bit copies of a frame variable: `lmqf` (hand-written, #385)

`lmqf() int { var x [4]int; x[0] = 5; h = x; k = [2]int(x[:2]); return k[0] }` with globals `h`
of type `[4]int` and `k` of type `[2]int` as `lower` sees it (one block: `v4 = LocalAddr <*[4]int>
{x} v2 v1` of `v2 = SP`, `v6 = Store {int} v4 v5 v1` of `v5 = Const64 [5]`, `v7`, `v9 = Addr {h|k}
v3` of `v3 = SB`, `v8 = Move {[4]int} [32] v7 v4 v6`, `v10 = Move {[2]int} [16] v9 v4 v8`, `v11 =
Load <int> v9 v10`, returned by `v12 = MakeResult v11 v10`). The checked lower lowers `v4` to the
frame address `MOVDaddr {x} v2` (310) and the `Move`s to `FSTPQ` of an `FLDPQ` (426) and to
`FMOVQstore` of an `FMOVQload` (418); the frame address then folds into the 128-bit loads (`874`,
`870`: `v14 = FLDPQ {x} v2 v6`, `v16 = FMOVQload {x} v2 v8`; `frameFold`,
`GoFV.Proof.Low.Val.ldQVal_frameFold`). By `lower_refines` every returning or panicking `run` of
`lmqf` is, up to refinement, a `runL` of the result; both return 5.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- The definition tables: `int` (type 2), `uintptr` (4), `[4]int` (5), `[2]int` (6), `*[4]int`
(7), `*[2]int` (8), `mem` (28), the results tuple (33); the `AuxCall` of `lmqf` (aux 1), its
symbol, its result name, the frame variable `x` (4), the globals `main.h` (5) and `main.k` (6), and
the type auxes of `int`, `[4]int` and `[2]int` (7, 8, 9). -/
def lmqfTabs : Tables where
  types :=
    let t := Array.replicate 34 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func() int" (.func 0 0 1 #[])))
    let t := t.set! 2 (some (mkT .INT (some 8) "int"))
    let t := t.set! 4 (some (mkT .UINTPTR (some 8) "uintptr"))
    let t := t.set! 5 (some { mkT .ARRAY (some 32) "[4]int" (.array 2 4) with align := some 8 })
    let t := t.set! 6 (some { mkT .ARRAY (some 16) "[2]int" (.array 2 2) with align := some 8 })
    let t := t.set! 7 (some (mkT .PTR (some 8) "*[4]int" (.elem 5)))
    let t := t.set! 8 (some (mkT .PTR (some 8) "*[2]int" (.elem 6)))
    let t := t.set! 28 (some (mkT .SSA none "mem"))
    let t := t.set! 31 (some (mkT .SSA none "void"))
    t.set! 33 (some (mkT .RESULTS none "int,mem" (.results #[2, 28])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.lmqf}", kind := .call (some 2) (some ladABI) },
    some { fmt := GoStr.ofString "main.lmqf",
           kind := .sym (GoStr.ofString "main.lmqf") 1 "" 0 default none none none #[] none },
    some (paramName "~r0" .PPARAMOUT 0),
    some (paramNameT "x" .PAUTO 5 (-32)),
    some (mvqG "main.h" 32),
    some (mvqG "main.k" 16),
    some { fmt := GoStr.ofString "int", kind := .type 2 },
    some { fmt := GoStr.ofString "[4]int", kind := .type 5 },
    some { fmt := GoStr.ofString "[2]int", kind := .type 6 }]

/-- `lmqf`, the input of `lower`. -/
def lmqfFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 12
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[12] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 2 #[] 1),
    some (mkV 2 .SP 4 none p0 1 #[] 1),
    some (mkV 3 .SB 4 none p0 2 #[] 1),
    some (mkV 4 .LocalAddr 7 (some 4) p0 3 #[2, 1] 1),
    some (mkVI 5 .Const64 2 5 none p0 1 #[] 1),
    some (mkV 6 .Store 28 (some 7) p0 1 #[4, 5, 1] 1),
    some (mkV 7 .Addr 7 (some 5) p0 1 #[3] 1),
    some (mkVI 8 .Move 28 32 (some 8) p0 1 #[7, 4, 6] 1),
    some (mkV 9 .Addr 8 (some 6) p0 2 #[3] 1),
    some (mkVI 10 .Move 28 16 (some 9) p0 2 #[9, 4, 8] 1),
    some (mkV 11 .Load 2 none p0 1 #[9, 10] 1),
    some (mkV 12 .MakeResult 33 none p0 1 #[11, 10] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `lmqf` (`gst`'s, with `flagdynlink` for the folds). -/
def lmqfPassEnv : PassEnv :=
  { gstPassEnv with funcName := GoStr.ofString "lmqf", tables := lmqfTabs }

/-- The globals `main.h` and `main.k`, zero. -/
def lmqfMem : Mem :=
  { blocks := #[(.global "main.h", { data := Array.replicate 32 (.b 0) }),
      (.global "main.k", { data := Array.replicate 16 (.b 0) })] }

/-- The loads of `lmqf`'s lowered result (op, offset, aux, arguments), at every value ID. -/
def lmqfLoads (f : Func) : List (ID × Op × Int64 × Option AuxRef × Array ID) :=
  (List.range (f.vidLast + 1)).filterMap fun i => (f.value? i).bind fun v =>
    if v.op == .ARM64FLDPQ || v.op == .ARM64FMOVQload then some (i, v.op, v.auxInt, v.aux, v.args)
    else none

/-- What `lmqfLoads` gives on the checked lower's result: the frame variable `x` folded into both
128-bit loads, `v14 = FLDPQ {x} v2 v6` and `v16 = FMOVQload {x} v2 v8`. -/
def lmqfOut : List (ID × Op × Int64 × Option AuxRef × Array ID) :=
  [(14, .ARM64FLDPQ, 0, some 4, #[2, 6]), (16, .ARM64FMOVQload, 0, some 4, #[2, 8])]

theorem lmqf_generic : lmqfFunc.lowered = false := by decide +kernel

/-- `lmqf` has no fused multiply-add shape: its contraction is itself. -/
theorem lmqf_noFma : GoFV.Opt.FmaContract.contractAll lmqfFunc = lmqfFunc := by decide +kernel

set_option synthInstance.maxSize 2048 in
/-- By kernel evaluation: the checked lower keeps a lowered result whose 128-bit loads read the
frame variable `x` through their aux (`lmqfOut`), and `lmqf` returns 5 under `run` of the input
and `runL` of the result. -/
theorem lmqf_checks :
    (lowerChecked lmqfPassEnv lmqfFunc).toOption.map (fun o =>
      (lmqfLoads o.func, o.func.lowered, returnsInt (runL Env.p1 o.tables o.func [] lmqfMem 1) 5)) =
      some (lmqfOut, true, true) ∧
    returnsInt (run Env.p1 lmqfTabs lmqfFunc [] lmqfMem 1) 5 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a frame variable's
address folded into 128-bit loads (`ARM64.rules:874`, `870`; `frameFold`): on `lmqf`, the checked
lower reads `x` by `FLDPQ {x}` and `FMOVQload {x}`, and every returning or panicking `run` of `lmqf`
is, up to refinement, a `runL` of the result. -/
theorem lmqf_lower :
    ∃ out, lowerChecked lmqfPassEnv lmqfFunc = .ok out ∧ out.func.lowered = true ∧
      lmqfLoads out.func = lmqfOut ∧
      (∃ f', GoFV.Proof.Low.Contract lmqfFunc f' ∧
        RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func lmqfPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem fuel, (run env lmqfTabs lmqfFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env lmqfTabs lmqfFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := lmqf_checks
  cases hc : lowerChecked lmqfPassEnv lmqfFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h5, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h5, GoFV.Proof.Low.lower_refines hc lmqf_generic,
      fun env hE args mem fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc lmqf_generic lmqf_noFma hE hd⟩

end GoFV.Proof.Witness
