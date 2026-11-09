import GoFV.Proof.Witness.LowerStoreSym

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower` on a `Move`: `mvw` (hand-written, issue #385)

`mvw() int { h = g; return h[0] }` with globals `g`, `h` of type `[9]int` as `lower` sees it (one
block: `v3 = Addr <*int> {g} v2` and `v4 = Addr <*int> {h} v2` of `v2 = SB`, `v5 = Move {[9]int}
[72] v4 v3 v1`, `v6 = Load <int> v4 v5`, returned by `v7 = MakeResult v6 v5`). The checked lower
fires `(Addr {sym} base) => (MOVDaddr {sym} base)` (308) and `(Move [s] dst src mem) && s > 64 &&
s < 192 && logLargeCopy(v, s) => (LoweredMove [s] dst src mem)` (438): `v5` becomes `LoweredMove
[72] v4 v3 v1`, which is not a root of lowered SSA (the validator compares the order of `f`'s
roots, `atomsOKL`, and pairs it with the `Move`, `bulkLower`). By `lower_refines` every returning
or panicking `run` of `mvw` is, up to refinement, a `runL` of the result; on `g` holding 7 in its
first word both return 7.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- A global of 72 bytes. -/
def mvwG (n : String) : AuxDef :=
  { fmt := GoStr.ofString n,
    kind := .sym (GoStr.ofString n) 0 "" 72 default none none none #[] none }

/-- The tables of `gst` with `[9]int` (type 5), the globals `main.g` (aux 4) and `main.h` (aux
6) of 72 bytes and the `Move`'s type aux (7). -/
def mvwTabs : Tables :=
  { gstTabs with
    types := gstTabs.types.set! 5 (some { mkT .ARRAY (some 72) "[9]int" (.array 2 9) with
      align := some 8 })
    auxes := ((gstTabs.auxes.set! 4 (some (mvwG "main.g"))).push (some (mvwG "main.h"))).push
      (some { fmt := GoStr.ofString "[9]int", kind := .type 5 }) }

/-- `mvw`, the input of `lower`. -/
def mvwFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 7
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[7] #[] #[] #[1, 2, 3, 4, 5, 6, 7])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 1 #[] 1),
    some (mkV 2 .SB 4 none p0 2 #[] 1),
    some (mkV 3 .Addr 3 (some 4) p0 1 #[2] 1),
    some (mkV 4 .Addr 3 (some 6) p0 2 #[2] 1),
    some (mkVI 5 .Move 28 72 (some 7) p0 2 #[4, 3, 1] 1),
    some (mkV 6 .Load 2 none p0 1 #[4, 5] 1),
    some (mkV 7 .MakeResult 33 none p0 1 #[6, 5] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `mvw`. -/
def mvwPassEnv : PassEnv :=
  { gstPassEnv with funcName := GoStr.ofString "mvw", tables := mvwTabs }

/-- The globals: `main.g` with 7 in its first word, `main.h` zero. -/
def mvwMem : Mem :=
  { blocks := #[(.global "main.g", { data := #[.b 7] ++ Array.replicate 71 (.b 0) }),
      (.global "main.h", { data := Array.replicate 72 (.b 0) })] }

theorem mvw_generic : mvwFunc.lowered = false := by decide +kernel

/-- `mvw` has no fused multiply-add shape: its contraction is itself. -/
theorem mvw_noFma : GoFV.Opt.FmaContract.contractAll mvwFunc = mvwFunc := by decide +kernel

set_option synthInstance.maxSize 2048 in
/-- By kernel evaluation: the checked lower keeps a lowered result whose `v5` is `LoweredMove [72]
v4 v3 v1`, and `mvw` returns 7 under `run` of the input and `runL` of the result. -/
theorem mvw_checks :
    (lowerChecked mvwPassEnv mvwFunc).toOption.map (fun o =>
      ((o.func.value? 5).map (fun v => (v.op, v.auxInt, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [] mvwMem 1) 7)) =
      some (some (.ARM64LoweredMove, 72, #[4, 3, 1]), true, true) ∧
    returnsInt (run Env.p1 mvwTabs mvwFunc [] mvwMem 1) 7 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a `Move`: on `mvw`, the
checked lower lowers `Move [72]` to `LoweredMove [72]`, and every returning or panicking `run` of
`mvw` is, up to refinement, a `runL` of the result. -/
theorem mvw_lower :
    ∃ out, lowerChecked mvwPassEnv mvwFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 5).map (fun v => (v.op, v.auxInt, v.args)) =
        some (.ARM64LoweredMove, 72, #[4, 3, 1]) ∧
      (∃ f', GoFV.Proof.Low.Contract mvwFunc f' ∧
        RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func mvwPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem fuel, (run env mvwTabs mvwFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env mvwTabs mvwFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := mvw_checks
  cases hc : lowerChecked mvwPassEnv mvwFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h5, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h5, GoFV.Proof.Low.lower_refines hc mvw_generic,
      fun env hE args mem fuel hd => GoFV.Proof.Low.lower_refines_run hc mvw_generic mvw_noFma hE hd⟩

end GoFV.Proof.Witness
