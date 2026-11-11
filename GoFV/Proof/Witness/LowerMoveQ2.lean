import GoFV.Proof.Witness.LowerMoveQ

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower` on `Move [48]`: `mvq2` (hand-written, issue #385)

`mvq2() int { h = g; return h[0] }` with globals `g`, `h` of type `[6]int` as `lower` sees it (one
block: `v3`, `v4 = Addr <*int> {g|h} v2` of `v2 = SB`, `v5 = Move {[6]int} [48] v4 v3 v1`,
`v6 = Load <int> v4 v5`, returned by `v7 = MakeResult v6 v5`). The checked lower fires
`(Addr {sym} base) => (MOVDaddr {sym} base)` (308) and `(Move [s] dst src mem) && s > 40 && s <= 48
=> (FMOVQstore [s-16] dst (FMOVQload [s-16] src mem) (FSTPQ dst (Select0 (FLDPQ src mem)) (Select1
(FLDPQ src mem)) mem))` (431), then folds the symbols into both 128-bit stores (909, 913): `v5`
becomes the outer `FMOVQstore {h} [32] v2 v8 v9` on the inner `FSTPQ {h} v2 v10 v12 v1` at the
fresh `v9`, paired with the `Move` (`moveQ2Lower`; `GoFV.Proof.Low.Sim.moveQ2_inner_eval`,
`moveQ2_outer_eval`). By `lower_refines` every returning or panicking `run` of `mvq2` is, up to
refinement, a `runL` of the result; on `g` holding 7 in its first word both return 7.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- The tables of `gst` with `[6]int` (type 5), the globals `main.g` (aux 4) and `main.h` (aux 6)
of 48 bytes and the `Move`'s type aux (7). -/
def mvq2Tabs : Tables :=
  { gstTabs with
    types := gstTabs.types.set! 5 (some { mkT .ARRAY (some 48) "[6]int" (.array 2 6) with
      align := some 8 })
    auxes := ((gstTabs.auxes.set! 4 (some (mvqG "main.g" 48))).push
      (some (mvqG "main.h" 48))).push
      (some { fmt := GoStr.ofString "[6]int", kind := .type 5 }) }

/-- `mvq2`, the input of `lower`. -/
def mvq2Func : Func where
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
    some (mkVI 5 .Move 28 48 (some 7) p0 2 #[4, 3, 1] 1),
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

/-- The pass environment of `lower` on `mvq2`. -/
def mvq2PassEnv : PassEnv :=
  { gstPassEnv with funcName := GoStr.ofString "mvq2", tables := mvq2Tabs }

/-- The globals: `main.g` with 7 in its first word, `main.h` zero. -/
def mvq2Mem : Mem :=
  { blocks := #[(.global "main.g", { data := #[.b 7] ++ Array.replicate 47 (.b 0) }),
      (.global "main.h", { data := Array.replicate 48 (.b 0) })] }

/-- The two 128-bit stores of `mvq2`'s lowered result (op, offset, aux, arguments): the outer at
the `Move`'s ID `v5`, the inner at `v9`. -/
def mvq2Show (f : Func) : List (Option (Op × Int64 × Option AuxRef × Array ID)) :=
  [5, 9].map fun i => (f.value? i).map fun v => (v.op, v.auxInt, v.aux, v.args)

/-- What `mvq2Show` gives on the checked lower's result: `FMOVQstore {h} [32] v2 v8 v9` of the
`FMOVQload {g} [32]` `v8` on the inner `FSTPQ {h} v2 v10 v12 v1` of the two halves `v10`, `v12`
of one `FLDPQ {g}`. -/
def mvq2Out : List (Option (Op × Int64 × Option AuxRef × Array ID)) :=
  [some (.ARM64FMOVQstore, 32, some 6, #[2, 8, 9]), some (.ARM64FSTPQ, 0, some 6, #[2, 10, 12, 1])]

theorem mvq2_generic : mvq2Func.lowered = false := by decide +kernel

/-- `mvq2` has no fused multiply-add shape: its contraction is itself. -/
theorem mvq2_noFma : GoFV.Opt.FmaContract.contractAll mvq2Func = mvq2Func := by decide +kernel

set_option synthInstance.maxSize 2048 in
/-- By kernel evaluation: the checked lower keeps a lowered result whose `v5` and `v9` are the
128-bit stores `FMOVQstore {h} [32] v2 v8 v9` and `FSTPQ {h} v2 v10 v12 v1`, and `mvq2` returns 7
under `run` of the input and `runL` of the result. -/
theorem mvq2_checks :
    (lowerChecked mvq2PassEnv mvq2Func).toOption.map (fun o =>
      (mvq2Show o.func, o.func.lowered, returnsInt (runL Env.p1 o.tables o.func [] mvq2Mem 1) 7)) =
      some (mvq2Out, true, true) ∧
    returnsInt (run Env.p1 mvq2Tabs mvq2Func [] mvq2Mem 1) 7 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on `Move [48]`: on `mvq2`,
the checked lower lowers it to two 128-bit stores, `FMOVQstore [32]` on `FSTPQ`
(`ARM64.rules:431`, `GoFV.Proof.Low.Rules.r_ARM64_431_sound`), with the globals' symbols folded in
(`909`, `913`), and every returning or panicking `run` of `mvq2` is, up to refinement, a `runL` of
the result. -/
theorem mvq2_lower :
    ∃ out, lowerChecked mvq2PassEnv mvq2Func = .ok out ∧ out.func.lowered = true ∧
      mvq2Show out.func = mvq2Out ∧
      (∃ f', GoFV.Proof.Low.Contract mvq2Func f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.LowerCheck.roPre mvq2PassEnv.tables mvq2Func) env mem)
        out.tables out.func mvq2PassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.LowerCheck.roPre mvq2PassEnv.tables mvq2Func) env mem → ∀ fuel,
        (run env mvq2Tabs mvq2Func args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env mvq2Tabs mvq2Func args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := mvq2_checks
  cases hc : lowerChecked mvq2PassEnv mvq2Func with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h5, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h5, GoFV.Proof.Low.lower_refines hc mvq2_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc mvq2_generic mvq2_noFma hE hro hd⟩

end GoFV.Proof.Witness
