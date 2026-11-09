import GoFV.Proof.Witness.LowerStoreSym

/-!
# Witness function for `lower` on `Move [32]` and `Move [16]`: `mvq` (hand-written, issue #385)

`mvq() int { h = g; k = [2]int(h[:2]); return k[0] }` with globals `g`, `h` of type `[4]int` and
`k` of type `[2]int` as `lower` sees it (one block: `v3`, `v4`, `v5 = Addr <*int> {g|h|k} v2` of
`v2 = SB`, `v6 = Move {[4]int} [32] v4 v3 v1`, `v7 = Move {[2]int} [16] v5 v4 v6`, `v8 = Load <int>
v5 v7`, returned by `v9 = MakeResult v8 v7`). The checked lower fires `(Addr {sym} base) =>
(MOVDaddr {sym} base)` (308), `(Move [32] dst src mem) => (FSTPQ dst (Select0 (FLDPQ src mem))
(Select1 (FLDPQ src mem)) mem)` (426) and `(Move [16] dst src mem) => (FMOVQstore dst (FMOVQload
src mem) mem)` (418), then folds the symbols into the 128-bit stores (913, 909): `v6` becomes
`FSTPQ {h} v2 …` and `v7` `FMOVQstore {k} v2 …`, paired with the `Move`s
(`moveQLower`, `GoFV.Proof.Low.Sim.moveQ_lower_eval`). By `lower_refines` every returning or
panicking `run` of `mvq` is, up to refinement, a `runL` of the result; on `g` holding 7 in its first
word both return 7.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- A global of `n` bytes. -/
def mvqG (s : String) (n : Nat) : AuxDef :=
  { fmt := GoStr.ofString s,
    kind := .sym (GoStr.ofString s) 0 "" n default none none none #[] none }

/-- The tables of `gst` with `[4]int` (type 5) and `[2]int` (type 6), the globals `main.g` (aux
4), `main.h` (aux 6) of 32 bytes and `main.k` (aux 7) of 16 bytes and the `Move`s' type auxes (8,
9). -/
def mvqTabs : Tables :=
  { gstTabs with
    types := (gstTabs.types.set! 5 (some { mkT .ARRAY (some 32) "[4]int" (.array 2 4) with
      align := some 8 })).set! 6 (some { mkT .ARRAY (some 16) "[2]int" (.array 2 2) with
      align := some 8 })
    auxes := ((((gstTabs.auxes.set! 4 (some (mvqG "main.g" 32))).push
      (some (mvqG "main.h" 32))).push (some (mvqG "main.k" 16))).push
      (some { fmt := GoStr.ofString "[4]int", kind := .type 5 })).push
      (some { fmt := GoStr.ofString "[2]int", kind := .type 6 }) }

/-- `mvq`, the input of `lower`. -/
def mvqFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 9
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[9] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8, 9])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 1 #[] 1),
    some (mkV 2 .SB 4 none p0 3 #[] 1),
    some (mkV 3 .Addr 3 (some 4) p0 1 #[2] 1),
    some (mkV 4 .Addr 3 (some 6) p0 2 #[2] 1),
    some (mkV 5 .Addr 3 (some 7) p0 2 #[2] 1),
    some (mkVI 6 .Move 28 32 (some 8) p0 1 #[4, 3, 1] 1),
    some (mkVI 7 .Move 28 16 (some 9) p0 2 #[5, 4, 6] 1),
    some (mkV 8 .Load 2 none p0 1 #[5, 7] 1),
    some (mkV 9 .MakeResult 33 none p0 1 #[8, 7] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `mvq`. -/
def mvqPassEnv : PassEnv :=
  { gstPassEnv with funcName := GoStr.ofString "mvq", tables := mvqTabs }

/-- The globals: `main.g` with 7 in its first word, `main.h` and `main.k` zero. -/
def mvqMem : Mem :=
  { blocks := #[(.global "main.g", { data := #[.b 7] ++ Array.replicate 31 (.b 0) }),
      (.global "main.h", { data := Array.replicate 32 (.b 0) }),
      (.global "main.k", { data := Array.replicate 16 (.b 0) })] }

/-- The `Move`s of `mvq`'s lowered result (op, offset, aux, arguments). -/
def mvqShow (f : Func) : List (Option (Op × Int64 × Option AuxRef × Array ID)) :=
  [6, 7].map fun i => (f.value? i).map fun v => (v.op, v.auxInt, v.aux, v.args)

/-- What `mvqShow` gives on the checked lower's result: `FSTPQ {h} v2 v10 v12 v1` of the two
halves `v10`, `v12` of one `FLDPQ` of `g`, and `FMOVQstore {k} v2 v13 v6` of an `FMOVQload` `v13`
of `h`. -/
def mvqOut : List (Option (Op × Int64 × Option AuxRef × Array ID)) :=
  [some (.ARM64FSTPQ, 0, some 6, #[2, 10, 12, 1]), some (.ARM64FMOVQstore, 0, some 7, #[2, 13, 6])]

theorem mvq_generic : mvqFunc.lowered = false := by decide +kernel

/-- `mvq` has no fused multiply-add shape: its contraction is itself. -/
theorem mvq_noFma : GoFV.Opt.FmaContract.contractAll mvqFunc = mvqFunc := by decide +kernel

set_option synthInstance.maxSize 2048 in
/-- By kernel evaluation: the checked lower keeps a lowered result whose `v6` and `v7` are the
128-bit stores `FSTPQ {h} v2 v10 v12 v1` and `FMOVQstore {k} v2 v13 v6`, and `mvq` returns 7
under `run` of the input and `runL` of the result. -/
theorem mvq_checks :
    (lowerChecked mvqPassEnv mvqFunc).toOption.map (fun o =>
      (mvqShow o.func, o.func.lowered, returnsInt (runL Env.p1 o.tables o.func [] mvqMem 1) 7)) =
      some (mvqOut, true, true) ∧
    returnsInt (run Env.p1 mvqTabs mvqFunc [] mvqMem 1) 7 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on `Move [32]` and `Move
[16]`: on `mvq`, the checked lower lowers them to `FSTPQ` and `FMOVQstore` (`ARM64.rules:426`,
`418`, `GoFV.Proof.Low.Rules.r_ARM64_426_sound`, `r_ARM64_418_sound`) with the globals' symbols
folded in (`913`, `909`), and every returning or panicking `run` of `mvq` is, up to refinement, a
`runL` of the result. -/
theorem mvq_lower :
    ∃ out, lowerChecked mvqPassEnv mvqFunc = .ok out ∧ out.func.lowered = true ∧
      mvqShow out.func = mvqOut ∧
      (∃ f', GoFV.Proof.Low.Contract mvqFunc f' ∧
        RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func mvqPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem fuel, (run env mvqTabs mvqFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env mvqTabs mvqFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := mvq_checks
  cases hc : lowerChecked mvqPassEnv mvqFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h5, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h5, GoFV.Proof.Low.lower_refines hc mvq_generic,
      fun env hE args mem fuel hd => GoFV.Proof.Low.lower_refines_run hc mvq_generic mvq_noFma hE hd⟩

end GoFV.Proof.Witness
