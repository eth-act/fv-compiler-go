import GoFV.Proof.Witness.LowerStoreSym

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness functions for `lower` folding a global's or a frame variable's address, or an offset of
the stack pointer, into a load: `gld`, `fra`, `fr0`, `spo` (hand-written, issue #385)

`gld() int { return g[1] }` with a global `g [2]int` as `lower` sees it (one block: `v3 = Addr
<*int> {g} v2` of `v2 = SB`, `v4 = OffPtr <*int> [8] v3`, `v5 = Load <int> v4 v1`, returned by `v6 =
MakeResult v5 v1`). The checked lower fires `(Addr {sym} base) => (MOVDaddr {sym} base)` (308),
`(OffPtr [off] ptr) => (ADDconst [off] ptr)` (306), `(ADDconst [off1] (MOVDaddr [off2] {sym} ptr))
&& is32Bit(off1+int64(off2)) => (MOVDaddr [int32(off1)+off2] {sym} ptr)` (650), so `v4` becomes
`MOVDaddr [8] {g} v2`, then lowers the load and folds the symbol into it (`(MOVDload [off1] {sym1}
(MOVDaddr [off2] {sym2} ptr) mem) && canMergeSym(sym1,sym2) … => (MOVDload [off1+off2]
{mergeSym(sym1,sym2)} ptr mem)`, 856): `v5` becomes `MOVDload [8] {g} v2 v1`, and `v3`, `v4` are
dead. On a `g` holding `[0, 7]` both return 7.

`fra() int { var a [2]int; a[1] = 7; return a[1] }` as `lower` sees it (one block: `v4 =
LocalAddr <*[2]int> {a} v2 v1` of `v2 = SP`, `v5 = OffPtr <*int> [8] v4`, `v6 = Store {int} v5 v3
v1` of `v3 = Const64 [7]`, `v7 = Load <int> v5 v6`, returned by `v8 = MakeResult v7 v6`). The checked
lower lowers `v4` to the frame address `MOVDaddr {a} v2` (310, an atom), folds it into the offset
(650 on a frame variable: `v5` becomes the term `MOVDaddr [8] {a} v2`, the validator's
`frameFold`), into the store (893: `MOVDstore [8] {a} v2 v3 v1`) and into the load (856: `MOVDload
[8] {a} v2 v6`); `v4` and `v5` are dead. Both return 7.

`fr0() int { var a [2]int; a[0] = 7; return a[0] }`: `fra` with `v5 = OffPtr <*int> [0] v4`. 650 at
offset 0 makes `v5` the frame address `MOVDaddr {a} v2`, an atom, which the validator replays as
no change (`addrFoldEv`: `v5` stays `ADDconst [0] v4`); the store and the load fold the address
through it (`frameAddr`: `MOVDstore {a} v2 v3 v1`, `MOVDload {a} v2 v6`), and `lower` deletes the
dead `v4` and `v5`. Both return 7.

`spo` stores 7 to the outgoing-arguments area (16 bytes: its tables describe a call with a stack
argument at offset 8) and reads it back (one block: `v2 = SP`, `v3 =
Const64 [7]`, `v4 = OffPtr <*int> [8] v2`, `v5 = Store {int} v4 v3 v1`, `v6 = Load <int> v4 v5`,
returned by `v7 = MakeResult v6 v5`). `(OffPtr [off] ptr:(SP)) && is32Bit(off) => (MOVDaddr
[int32(off)] ptr)` (305) makes `v4` `MOVDaddr [8] v2`, which the validator replays as no change
(`spFoldEv`: `v4` stays `OffPtr [8] v2`); the store folds it as an offset (893, `stFold`: `MOVDstore
[8] v2 v3 v1`), the load as the load of `v2` at 8 (856, `ldOffFold`: `MOVDload [8] v2 v5`), and
`lower` deletes the dead `v4`. Both return 7.

By `lower_refines` every returning or panicking `run` of each is, up to refinement, a `runL` of
the result.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

-- `DecidableEq` of the nested options of tuples below exceeds the default instance size.
set_option synthInstance.maxSize 1024

/-- The definition tables of `gld`: `gst`'s, the global `main.g` (aux 4) of 16 bytes. -/
def gldTabs : Tables :=
  { gstTabs with
    auxes := gstTabs.auxes.set! 4 (some
      { fmt := GoStr.ofString "main.g",
        kind := .sym (GoStr.ofString "main.g") 0 "" 16 default none none none #[] none }) }

/-- `gld`, the input of `lower`. -/
def gldFunc : Func where
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
    some (mkV 3 .Addr 3 (some 4) p0 1 #[2] 1),
    some (mkVI 4 .OffPtr 3 8 none p0 1 #[3] 1),
    some (mkV 5 .Load 2 none p0 1 #[4, 1] 1),
    some (mkV 6 .MakeResult 33 none p0 1 #[5, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `gld`. -/
def gldPassEnv : PassEnv :=
  { gstPassEnv with funcName := GoStr.ofString "gld", tables := gldTabs }

/-- The global `main.g` holding `[0, 7]`. -/
def gldMem : Mem :=
  { blocks := #[(.global "main.g",
      { data := Array.replicate 8 (.b 0) ++ #[.b 7] ++ Array.replicate 7 (.b 0) })] }

theorem gld_generic : gldFunc.lowered = false := by decide +kernel

/-- `gld` has no fused multiply-add shape: its contraction is itself. -/
theorem gld_noFma : GoFV.Opt.FmaContract.contractAll gldFunc = gldFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose `v5` is `MOVDload [8] {g}
v2 v1` and whose `v4` is dead, and `gld` returns 7 under `run` of the input and `runL` of the
result. -/
theorem gld_checks :
    (lowerChecked gldPassEnv gldFunc).toOption.map (fun o =>
      ((o.func.value? 4).isSome,
        (o.func.value? 5).map (fun v => (v.op, v.auxInt, v.aux, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [] gldMem 1) 7)) =
      some (false, some (.ARM64MOVDload, 8, some 4, #[2, 1]), true, true) ∧
    returnsInt (run Env.p1 gldTabs gldFunc [] gldMem 1) 7 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on an offset folded into a
global's address and the global's address folded into a load: on `gld`, the checked lower loads
at `{g}` directly (`MOVDload [8] {g} v2 v1`), and every returning or panicking `run` of `gld` is,
up to refinement, a `runL` of the result. -/
theorem gld_lower :
    ∃ out, lowerChecked gldPassEnv gldFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 4).isSome = false ∧
      (out.func.value? 5).map (fun v => (v.op, v.auxInt, v.aux, v.args)) =
        some (.ARM64MOVDload, 8, some 4, #[2, 1]) ∧
      (∃ f', GoFV.Proof.Low.Contract gldFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.RewriteCheck.roSyms gldPassEnv.tables gldFunc) env mem)
        out.tables out.func gldPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.RewriteCheck.roSyms gldPassEnv.tables gldFunc) env mem → ∀ fuel,
        (run env gldTabs gldFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env gldTabs gldFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := gld_checks
  cases hc : lowerChecked gldPassEnv gldFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h4, h5, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h4, h5, GoFV.Proof.Low.lower_refines hc gld_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc gld_generic gld_noFma hE hro hd⟩

/-- The definition tables of `fra`: `gst`'s, `[2]int` (type 5), `*[2]int` (6), and the frame
variable `a` (aux 4) of type `[2]int`. -/
def fraTabs : Tables :=
  { gstTabs with
    types := (gstTabs.types.set! 5 (some (mkT .ARRAY (some 16) "[2]int" (.array 2 2)))).set! 6
      (some (mkT .PTR (some 8) "*[2]int" (.elem 5)))
    auxes := gstTabs.auxes.set! 4 (some (paramNameT "a" .PAUTO 5 (-16))) }

/-- `fra`, the input of `lower`. -/
def fraFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 8
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[8] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 2 #[] 1),
    some (mkV 2 .SP 4 none p0 1 #[] 1),
    some (mkVI 3 .Const64 2 7 none p0 1 #[] 1),
    some (mkV 4 .LocalAddr 6 (some 4) p0 1 #[2, 1] 1),
    some (mkVI 5 .OffPtr 3 8 none p0 2 #[4] 1),
    some (mkV 6 .Store 28 (some 5) p0 2 #[5, 3, 1] 1),
    some (mkV 7 .Load 2 none p0 1 #[5, 6] 1),
    some (mkV 8 .MakeResult 33 none p0 1 #[7, 6] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `fra`. -/
def fraPassEnv : PassEnv :=
  { gstPassEnv with funcName := GoStr.ofString "fra", tables := fraTabs }

theorem fra_generic : fraFunc.lowered = false := by decide +kernel

/-- `fra` has no fused multiply-add shape: its contraction is itself. -/
theorem fra_noFma : GoFV.Opt.FmaContract.contractAll fraFunc = fraFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose store `v6` is `MOVDstore
[8] {a} v2 v3 v1` and load `v7` `MOVDload [8] {a} v2 v6`, and `fra` returns 7 under `run` of the
input and `runL` of the result. -/
theorem fra_checks :
    (lowerChecked fraPassEnv fraFunc).toOption.map (fun o =>
      ((o.func.value? 6).map (fun v => (v.op, v.auxInt, v.aux, v.args)),
        (o.func.value? 7).map (fun v => (v.op, v.auxInt, v.aux, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [] {} 1) 7)) =
      some (some (.ARM64MOVDstore, 8, some 4, #[2, 3, 1]),
        some (.ARM64MOVDload, 8, some 4, #[2, 6]), true, true) ∧
    returnsInt (run Env.p1 fraTabs fraFunc [] {} 1) 7 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a frame variable's
address folded into an offset, a store and a load: on `fra`, the checked lower stores and loads at
`[8] {a}` directly, and every returning or panicking `run` of `fra` is, up to refinement, a `runL`
of the result. -/
theorem fra_lower :
    ∃ out, lowerChecked fraPassEnv fraFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 6).map (fun v => (v.op, v.auxInt, v.aux, v.args)) =
        some (.ARM64MOVDstore, 8, some 4, #[2, 3, 1]) ∧
      (out.func.value? 7).map (fun v => (v.op, v.auxInt, v.aux, v.args)) =
        some (.ARM64MOVDload, 8, some 4, #[2, 6]) ∧
      (∃ f', GoFV.Proof.Low.Contract fraFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.RewriteCheck.roSyms fraPassEnv.tables fraFunc) env mem)
        out.tables out.func fraPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.RewriteCheck.roSyms fraPassEnv.tables fraFunc) env mem → ∀ fuel,
        (run env fraTabs fraFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env fraTabs fraFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := fra_checks
  cases hc : lowerChecked fraPassEnv fraFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h6, h7, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h6, h7, GoFV.Proof.Low.lower_refines hc fra_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc fra_generic fra_noFma hE hro hd⟩

/-- `fr0`, the input of `lower`: `fra` with the offset 0. -/
def fr0Func : Func :=
  { fraFunc with
    valueTab := fraFunc.valueTab.set! 5 (some (mkVI 5 .OffPtr 3 0 none p0 2 #[4] 1)) }

/-- The pass environment of `lower` on `fr0`. -/
def fr0PassEnv : PassEnv :=
  { fraPassEnv with funcName := GoStr.ofString "fr0" }

theorem fr0_generic : fr0Func.lowered = false := by decide +kernel

/-- `fr0` has no fused multiply-add shape: its contraction is itself. -/
theorem fr0_noFma : GoFV.Opt.FmaContract.contractAll fr0Func = fr0Func := by decide +kernel

set_option synthInstance.maxSize 2048 in
/-- By kernel evaluation: the checked lower keeps a lowered result without `v4` and `v5`, whose
store `v6` is `MOVDstore {a} v2 v3 v1` and load `v7` `MOVDload {a} v2 v6`, and `fr0` returns 7
under `run` of the input and `runL` of the result. -/
theorem fr0_checks :
    (lowerChecked fr0PassEnv fr0Func).toOption.map (fun o =>
      ((o.func.value? 4).isSome, (o.func.value? 5).isSome,
        (o.func.value? 6).map (fun v => (v.op, v.auxInt, v.aux, v.args)),
        (o.func.value? 7).map (fun v => (v.op, v.auxInt, v.aux, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [] {} 1) 7)) =
      some (false, false, some (.ARM64MOVDstore, 0, some 4, #[2, 3, 1]),
        some (.ARM64MOVDload, 0, some 4, #[2, 6]), true, true) ∧
    returnsInt (run Env.p1 fraTabs fr0Func [] {} 1) 7 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a frame variable's
address at offset 0 (`ARM64.rules:650` replayed as no change, `addrFoldEv`) folded into a store and
a load: on `fr0`, the checked lower stores and loads at `{a}` directly, and every returning or
panicking `run` of `fr0` is, up to refinement, a `runL` of the result. -/
theorem fr0_lower :
    ∃ out, lowerChecked fr0PassEnv fr0Func = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 5).isSome = false ∧
      (out.func.value? 6).map (fun v => (v.op, v.auxInt, v.aux, v.args)) =
        some (.ARM64MOVDstore, 0, some 4, #[2, 3, 1]) ∧
      (out.func.value? 7).map (fun v => (v.op, v.auxInt, v.aux, v.args)) =
        some (.ARM64MOVDload, 0, some 4, #[2, 6]) ∧
      (∃ f', GoFV.Proof.Low.Contract fr0Func f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.RewriteCheck.roSyms fr0PassEnv.tables fr0Func) env mem)
        out.tables out.func fr0PassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.RewriteCheck.roSyms fr0PassEnv.tables fr0Func) env mem → ∀ fuel,
        (run env fraTabs fr0Func args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env fraTabs fr0Func args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := fr0_checks
  cases hc : lowerChecked fr0PassEnv fr0Func with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨-, h5, h6, h7, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h5, h6, h7, GoFV.Proof.Low.lower_refines hc fr0_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc fr0_generic fr0_noFma hE hro hd⟩

/-- The ABI of `spo`'s `AuxCall`: one `int` argument on the stack at offset 8. -/
def spoABI : CallABI :=
  { abi := 0, nin := 1, nout := 0, spillOff := 16, spillSize := 0, inRegs := 0, outRegs := 0,
    params := #[{ out := false, index := 0, type := 2, name := none, regs := #[], offset := 8 }] }

/-- The definition tables of `spo`: `fra`'s, and an `AuxCall` (aux 6, `spoABI`), so the
outgoing-arguments area holds 16 bytes (`outargsSize`). -/
def spoTabs : Tables :=
  { fraTabs with
    auxes := fraTabs.auxes.push (some
      { fmt := GoStr.ofString "AuxCall{main.f}", kind := .call none (some spoABI) }) }

/-- `spo`, the input of `lower`. -/
def spoFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 7
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[7] #[] #[] #[1, 2, 3, 4, 5, 6, 7])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 1 #[] 1),
    some (mkV 2 .SP 4 none p0 1 #[] 1),
    some (mkVI 3 .Const64 2 7 none p0 1 #[] 1),
    some (mkVI 4 .OffPtr 3 8 none p0 2 #[2] 1),
    some (mkV 5 .Store 28 (some 5) p0 2 #[4, 3, 1] 1),
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

/-- The pass environment of `lower` on `spo`. -/
def spoPassEnv : PassEnv :=
  { fraPassEnv with funcName := GoStr.ofString "spo", tables := spoTabs }

theorem spo_generic : spoFunc.lowered = false := by decide +kernel

/-- `spo` has no fused multiply-add shape: its contraction is itself. -/
theorem spo_noFma : GoFV.Opt.FmaContract.contractAll spoFunc = spoFunc := by decide +kernel

set_option synthInstance.maxSize 2048 in
/-- By kernel evaluation: the checked lower keeps a lowered result without `v4`, whose store `v5`
is `MOVDstore [8] v2 v3 v1` and load `v6` `MOVDload [8] v2 v5`, and `spo` returns 7 under `run` of
the input and `runL` of the result. -/
theorem spo_checks :
    (lowerChecked spoPassEnv spoFunc).toOption.map (fun o =>
      ((o.func.value? 4).isSome,
        (o.func.value? 5).map (fun v => (v.op, v.auxInt, v.aux, v.args)),
        (o.func.value? 6).map (fun v => (v.op, v.auxInt, v.aux, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [] {} 1) 7)) =
      some (false, some (.ARM64MOVDstore, 8, none, #[2, 3, 1]),
        some (.ARM64MOVDload, 8, none, #[2, 5]), true, true) ∧
    returnsInt (run Env.p1 spoTabs spoFunc [] {} 1) 7 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on an offset of the stack
pointer (`ARM64.rules:305` replayed as no change, `spFoldEv`) folded into a store (`stFold`) and a
load (`ldOffFold`): on `spo`, the checked lower stores and loads at `[8]` of `SP` directly, and every
returning or panicking `run` of `spo` is, up to refinement, a `runL` of the result. -/
theorem spo_lower :
    ∃ out, lowerChecked spoPassEnv spoFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 4).isSome = false ∧
      (out.func.value? 5).map (fun v => (v.op, v.auxInt, v.aux, v.args)) =
        some (.ARM64MOVDstore, 8, none, #[2, 3, 1]) ∧
      (out.func.value? 6).map (fun v => (v.op, v.auxInt, v.aux, v.args)) =
        some (.ARM64MOVDload, 8, none, #[2, 5]) ∧
      (∃ f', GoFV.Proof.Low.Contract spoFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.RewriteCheck.roSyms spoPassEnv.tables spoFunc) env mem)
        out.tables out.func spoPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.RewriteCheck.roSyms spoPassEnv.tables spoFunc) env mem → ∀ fuel,
        (run env spoTabs spoFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env spoTabs spoFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := spo_checks
  cases hc : lowerChecked spoPassEnv spoFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h4, h5, h6, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h4, h5, h6, GoFV.Proof.Low.lower_refines hc spo_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc spo_generic spo_noFma hE hro hd⟩

end GoFV.Proof.Witness
