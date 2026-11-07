import GoFV.Proof.Witness.LowerTrunc

/-!
# Witness functions for `lower` reading narrow arguments: `nsel`, `nchn`, `ntst`, `nand` (hand-written, issue #385)

Four functions of a global `g` as `lower` sees them (one block each, `v3 = Addr {g} v2` of
`v2 = SB`, `v4` the load of `g`, the result returned by a `MakeResult`):

* `nsel() int { u := uint8(g); return int(u >> u) }`: `v5 = Trunc64to8 <uint8> v4`, `v6 = Rsh8Ux8
  <uint8> v5 v5`, `v7 = ZeroExt8to64 <int> v6`. `lower` builds `CSEL [LessThanU] (SRL …)
  (MOVDconst [0]) (CMPconst …)` at the `uint8` shape and folds it into `CSEL0` (`ARM64.rules:1188`),
  which the validator admits since `CSEL` reads its arms at the result's width (`armReadW`).
* `nchn() int { return int(uint8(int32(g))) }`: `v5 = Trunc64to32 <int32> v4`, `v6 = Trunc32to8
  <uint8> v5`, `v7 = ZeroExt8to64 <int> v6`; the output's `v7` is `MOVBUreg v4`, through a chain of
  two narrowing copies (`narrowReachL`).
* `ntst() int { if uint8(g)&2 != 0 { return 1 }; return 0 }` as a boolean: `v5 = Trunc64to8 <uint8>
  v4`, `v7 = And8 v5 (Const8 [2])`, `v9 = Neq8 v7 (Const8 [0])`, `v11 = ZeroExt8to64
  (CvtBoolToUint8 v9)`; `v9` becomes `NotEqual (TSTWconst [2] v4)`, which reads two bits of the
  narrowing copy's source (`tstReadW`).
* `nand() int { return int(uint8(int32(g) & 127)) }` with a 32-bit load `v4`: `v6 = And32 v4 (Const32
  [127])`, `v7 = Trunc32to8 <uint8> v6`, `v8 = ZeroExt8to64 <int> v7`; `lower` gives `MOVBUreg` the
  copy's source `v6` (the replay follows it, `copyFixL`), then folds `(MOVBUreg (ANDconst [127]
  v4))` into `ANDconst [127] v4` (`ARM64.rules:1247`).

By `lower_refines` every returning or panicking `run` of each is, up to refinement, a `runL` of the
result; on `g` holding `0x1_0000_019a` they return 0, 154, 1 and 26.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- The tables of `trc` with `uint8` (type 6), `bool` (7), `*int32` (8), `uint64` (9), `uint32`
(10), `uint16` (11), `int64` (12) and `flags` (29). -/
def narTabs : Tables :=
  { trcTabs with
    types :=
      let t := trcTabs.types
      let t := t.set! 6 (some (mkT .UINT8 (some 1) "uint8"))
      let t := t.set! 7 (some (mkT .BOOL (some 1) "bool"))
      let t := t.set! 8 (some (mkT .PTR (some 8) "*int32" (.elem 5)))
      let t := t.set! 9 (some (mkT .UINT64 (some 8) "uint64"))
      let t := t.set! 10 (some (mkT .UINT32 (some 4) "uint32"))
      let t := t.set! 11 (some (mkT .UINT16 (some 2) "uint16"))
      let t := t.set! 12 (some (mkT .INT64 (some 8) "int64"))
      t.set! 29 (some (mkT .SSA none "flags")) }

/-- A one-block function of `g` returning its value `ret`. -/
def narFunc (last ret : ID) (vals : Array (Option Value)) : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := last
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[ret] #[] #[] ((List.range last).map (· + 1)).toArray)]
  valueTab := vals
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on the functions of `narTabs`. -/
def narPassEnv (name : String) : PassEnv :=
  { gstPassEnv with funcName := GoStr.ofString name, tables := narTabs
                    typs := #[("Int", 2), ("Uintptr", 4), ("Int32", 5), ("UInt8", 6), ("Bool", 7),
                      ("UInt64", 9), ("UInt32", 10), ("UInt16", 11), ("Int64", 12), ("Mem", 28),
                      ("Flags", 29), ("Void", 31)] }

/-- The global `main.g` holding `0x1_0000_019a`. -/
def narMem : Mem :=
  { blocks := #[(.global "main.g", { data := #[.b 0x9a, .b 0x01, .b 0, .b 0, .b 1, .b 0, .b 0,
      .b 0] })] }

/-- `nsel`. -/
def nselFunc : Func := narFunc 8 8 #[none,
  some (mkV 1 .InitMem 28 none p0 2 #[] 1),
  some (mkV 2 .SB 4 none p0 1 #[] 1),
  some (mkV 3 .Addr 3 (some 4) p0 1 #[2] 1),
  some (mkV 4 .Load 2 none p0 1 #[3, 1] 1),
  some (mkV 5 .Trunc64to8 6 none p0 2 #[4] 1),
  some (mkV 6 .Rsh8Ux8 6 none p0 1 #[5, 5] 1),
  some (mkV 7 .ZeroExt8to64 2 none p0 1 #[6] 1),
  some (mkV 8 .MakeResult 33 none p0 1 #[7, 1] 1)]

/-- `nchn`. -/
def nchnFunc : Func := narFunc 8 8 #[none,
  some (mkV 1 .InitMem 28 none p0 2 #[] 1),
  some (mkV 2 .SB 4 none p0 1 #[] 1),
  some (mkV 3 .Addr 3 (some 4) p0 1 #[2] 1),
  some (mkV 4 .Load 2 none p0 1 #[3, 1] 1),
  some (mkV 5 .Trunc64to32 5 none p0 1 #[4] 1),
  some (mkV 6 .Trunc32to8 6 none p0 1 #[5] 1),
  some (mkV 7 .ZeroExt8to64 2 none p0 1 #[6] 1),
  some (mkV 8 .MakeResult 33 none p0 1 #[7, 1] 1)]

/-- `ntst`. -/
def ntstFunc : Func := narFunc 12 12 #[none,
  some (mkV 1 .InitMem 28 none p0 2 #[] 1),
  some (mkV 2 .SB 4 none p0 1 #[] 1),
  some (mkV 3 .Addr 3 (some 4) p0 1 #[2] 1),
  some (mkV 4 .Load 2 none p0 1 #[3, 1] 1),
  some (mkV 5 .Trunc64to8 6 none p0 1 #[4] 1),
  some (mkVI 6 .Const8 6 2 none p0 1 #[] 1),
  some (mkV 7 .And8 6 none p0 1 #[5, 6] 1),
  some (mkVI 8 .Const8 6 0 none p0 1 #[] 1),
  some (mkV 9 .Neq8 7 none p0 1 #[7, 8] 1),
  some (mkV 10 .CvtBoolToUint8 6 none p0 1 #[9] 1),
  some (mkV 11 .ZeroExt8to64 2 none p0 1 #[10] 1),
  some (mkV 12 .MakeResult 33 none p0 1 #[11, 1] 1)]

/-- `nand`. -/
def nandFunc : Func := narFunc 9 9 #[none,
  some (mkV 1 .InitMem 28 none p0 2 #[] 1),
  some (mkV 2 .SB 4 none p0 1 #[] 1),
  some (mkV 3 .Addr 8 (some 4) p0 1 #[2] 1),
  some (mkV 4 .Load 5 none p0 1 #[3, 1] 1),
  some (mkVI 5 .Const32 5 127 none p0 1 #[] 1),
  some (mkV 6 .And32 5 none p0 1 #[4, 5] 1),
  some (mkV 7 .Trunc32to8 6 none p0 1 #[6] 1),
  some (mkV 8 .ZeroExt8to64 2 none p0 1 #[7] 1),
  some (mkV 9 .MakeResult 33 none p0 1 #[8, 1] 1)]

theorem nsel_generic : nselFunc.lowered = false := by decide +kernel
theorem nchn_generic : nchnFunc.lowered = false := by decide +kernel
theorem ntst_generic : ntstFunc.lowered = false := by decide +kernel
theorem nand_generic : nandFunc.lowered = false := by decide +kernel

/-- The four functions have no fused multiply-add shape: their contraction is themselves. -/
theorem nsel_noFma : GoFV.Opt.FmaContract.contractAll nselFunc = nselFunc := by decide +kernel
theorem nchn_noFma : GoFV.Opt.FmaContract.contractAll nchnFunc = nchnFunc := by decide +kernel
theorem ntst_noFma : GoFV.Opt.FmaContract.contractAll ntstFunc = ntstFunc := by decide +kernel
theorem nand_noFma : GoFV.Opt.FmaContract.contractAll nandFunc = nandFunc := by decide +kernel

set_option synthInstance.maxSize 2048 in
/-- By kernel evaluation: the checked lower keeps a lowered result of `nsel` whose `v6` is `CSEL0`,
and `nsel` returns 0 under `run` of the input and `runL` of the result. -/
theorem nsel_checks :
    (lowerChecked (narPassEnv "nsel") nselFunc).toOption.map (fun o =>
      ((o.func.value? 6).map (·.op), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [] narMem 1) 0)) =
      some (some .ARM64CSEL0, true, true) ∧
    returnsInt (run Env.p1 narTabs nselFunc [] narMem 1) 0 = true := by
  decide +kernel

set_option synthInstance.maxSize 2048 in
/-- By kernel evaluation: the checked lower keeps a lowered result of `nchn` whose `v7` is
`MOVBUreg v4`, and `nchn` returns 154 under `run` of the input and `runL` of the result. -/
theorem nchn_checks :
    (lowerChecked (narPassEnv "nchn") nchnFunc).toOption.map (fun o =>
      ((o.func.value? 7).map (fun v => (v.op, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [] narMem 1) 154)) =
      some (some (.ARM64MOVBUreg, #[4]), true, true) ∧
    returnsInt (run Env.p1 narTabs nchnFunc [] narMem 1) 154 = true := by
  decide +kernel

set_option synthInstance.maxSize 2048 in
/-- By kernel evaluation: the checked lower keeps a lowered result of `ntst` whose `v9` is
`NotEqual v18` and `v18` `TSTWconst [2] v4`, and `ntst` returns 1 under `run` of the input and
`runL` of the result. -/
theorem ntst_checks :
    (lowerChecked (narPassEnv "ntst") ntstFunc).toOption.map (fun o =>
      ((o.func.value? 9).map (fun v => (v.op, v.args)),
        (o.func.value? 18).map (fun v => (v.op, v.auxInt, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [] narMem 1) 1)) =
      some (some (.ARM64NotEqual, #[18]), some (.ARM64TSTWconst, 2, #[4]), true, true) ∧
    returnsInt (run Env.p1 narTabs ntstFunc [] narMem 1) 1 = true := by
  decide +kernel

set_option synthInstance.maxSize 2048 in
/-- By kernel evaluation: the checked lower keeps a lowered result of `nand` whose `v8` is
`ANDconst [127] v4`, and `nand` returns 26 under `run` of the input and `runL` of the result. -/
theorem nand_checks :
    (lowerChecked (narPassEnv "nand") nandFunc).toOption.map (fun o =>
      ((o.func.value? 8).map (fun v => (v.op, v.auxInt, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [] narMem 1) 26)) =
      some (some (.ARM64ANDconst, 127, #[4]), true, true) ∧
    returnsInt (run Env.p1 narTabs nandFunc [] narMem 1) 26 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a conditional select
at a narrow shape: on `nsel`, the checked lower's `v6` is `CSEL0` (rule 1188 on `uint8` arms,
`armReadW`), and every returning or panicking `run` of `nsel` is, up to refinement, a `runL` of the
result. -/
theorem nsel_lower :
    ∃ out, lowerChecked (narPassEnv "nsel") nselFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 6).map (·.op) = some .ARM64CSEL0 ∧
      (∃ f', GoFV.Proof.Low.Contract nselFunc f' ∧
        RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func (narPassEnv "nsel").tables f') ∧
      ∀ env, env.Mono → ∀ args mem fuel, (run env narTabs nselFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env narTabs nselFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := nsel_checks
  cases hc : lowerChecked (narPassEnv "nsel") nselFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h6, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h6, GoFV.Proof.Low.lower_refines hc nsel_generic,
      fun env hE args mem fuel hd => GoFV.Proof.Low.lower_refines_run hc nsel_generic nsel_noFma hE hd⟩

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) through two narrowing
copies: on `nchn`, the checked lower's `v7` is `MOVBUreg v4` (`narrowReachL`), and every returning
or panicking `run` of `nchn` is, up to refinement, a `runL` of the result. -/
theorem nchn_lower :
    ∃ out, lowerChecked (narPassEnv "nchn") nchnFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 7).map (fun v => (v.op, v.args)) = some (.ARM64MOVBUreg, #[4]) ∧
      (∃ f', GoFV.Proof.Low.Contract nchnFunc f' ∧
        RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func (narPassEnv "nchn").tables f') ∧
      ∀ env, env.Mono → ∀ args mem fuel, (run env narTabs nchnFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env narTabs nchnFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := nchn_checks
  cases hc : lowerChecked (narPassEnv "nchn") nchnFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h7, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h7, GoFV.Proof.Low.lower_refines hc nchn_generic,
      fun env hE args mem fuel hd => GoFV.Proof.Low.lower_refines_run hc nchn_generic nchn_noFma hE hd⟩

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on `TSTWconst` of a
narrowing copy's source: on `ntst`, the checked lower's `v18` is `TSTWconst [2] v4` (`tstReadW`),
and every returning or panicking `run` of `ntst` is, up to refinement, a `runL` of the result. -/
theorem ntst_lower :
    ∃ out, lowerChecked (narPassEnv "ntst") ntstFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 18).map (fun v => (v.op, v.auxInt, v.args)) =
        some (.ARM64TSTWconst, 2, #[4]) ∧
      (∃ f', GoFV.Proof.Low.Contract ntstFunc f' ∧
        RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func (narPassEnv "ntst").tables f') ∧
      ∀ env, env.Mono → ∀ args mem fuel, (run env narTabs ntstFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env narTabs ntstFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := ntst_checks
  cases hc : lowerChecked (narPassEnv "ntst") ntstFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨-, h18, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h18, GoFV.Proof.Low.lower_refines hc ntst_generic,
      fun env hE args mem fuel hd => GoFV.Proof.Low.lower_refines_run hc ntst_generic ntst_noFma hE hd⟩

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a rule matching through
a narrowing copy `lower` eliminated: on `nand`, the checked lower's `v8` is `ANDconst [127] v4`
(`copyFixL`, rule 1247), and every returning or panicking `run` of `nand` is, up to refinement, a
`runL` of the result. -/
theorem nand_lower :
    ∃ out, lowerChecked (narPassEnv "nand") nandFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 8).map (fun v => (v.op, v.auxInt, v.args)) =
        some (.ARM64ANDconst, 127, #[4]) ∧
      (∃ f', GoFV.Proof.Low.Contract nandFunc f' ∧
        RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func (narPassEnv "nand").tables f') ∧
      ∀ env, env.Mono → ∀ args mem fuel, (run env narTabs nandFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env narTabs nandFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := nand_checks
  cases hc : lowerChecked (narPassEnv "nand") nandFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h8, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h8, GoFV.Proof.Low.lower_refines hc nand_generic,
      fun env hE args mem fuel hd => GoFV.Proof.Low.lower_refines_run hc nand_generic nand_noFma hE hd⟩

end GoFV.Proof.Witness
