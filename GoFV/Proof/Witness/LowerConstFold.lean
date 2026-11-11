import GoFV.Proof.Witness.LowerStoreSym

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower` folding an extension of a constant: `zxc` (hand-written, issue #385)

`zxc() uint64 { var b int8 = -1; return uint64(uint8(b)) }` as `lower` sees it (one block: `v2 =
Const8 [-1]`, `v3 = ZeroExt8to64 v2`, returned by `v4 = MakeResult v3 v1`). The checked lower fires
`(Const8 [val]) => (MOVDconst [int64(val)])` (182), `(ZeroExt8to64 ...) => (MOVBUreg ...)` (202)
and `(MOVBUreg (MOVDconst [c])) => (MOVDconst [int64(uint8(c))])` (1255), so `v3` becomes
`MOVDconst [255]` and `v2` is dead. Both return 255; by `lower_refines` every returning or
panicking `run` of `zxc` is, up to refinement, a `runL` of the result.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

-- `DecidableEq` of the nested options of tuples below exceeds the default instance size.
set_option synthInstance.maxSize 1024

/-- The definition tables of `zxc`: `gst`'s and `int8` (type 5). -/
def zxcTabs : Tables :=
  { gstTabs with types := gstTabs.types.set! 5 (some (mkT .INT8 (some 1) "int8")) }

/-- `zxc`, the input of `lower`. -/
def zxcFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 4
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[4] #[] #[] #[1, 2, 3, 4])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 1 #[] 1),
    some (mkVI 2 .Const8 5 (-1) none p0 1 #[] 1),
    some (mkV 3 .ZeroExt8to64 2 none p0 1 #[2] 1),
    some (mkV 4 .MakeResult 33 none p0 1 #[3, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `zxc`. -/
def zxcPassEnv : PassEnv :=
  { gstPassEnv with funcName := GoStr.ofString "zxc", tables := zxcTabs }

theorem zxc_generic : zxcFunc.lowered = false := by decide +kernel

/-- `zxc` has no fused multiply-add shape: its contraction is itself. -/
theorem zxc_noFma : GoFV.Opt.FmaContract.contractAll zxcFunc = zxcFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result without `v2` whose `v3` is
`MOVDconst [255]`, and `zxc` returns 255 under `run` of the input and `runL` of the result. -/
theorem zxc_checks :
    (lowerChecked zxcPassEnv zxcFunc).toOption.map (fun o =>
      ((o.func.value? 2).isSome, (o.func.value? 3).map (fun v => (v.op, v.auxInt, v.args)),
        o.func.lowered, returnsInt (runL Env.p1 o.tables o.func [] {} 1) 255)) =
      some (false, some (.ARM64MOVDconst, 255, #[]), true, true) ∧
    returnsInt (run Env.p1 zxcTabs zxcFunc [] {} 1) 255 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on an extension of a
constant folded into the constant (`ARM64.rules:1255`): on `zxc`, the checked lower returns
`MOVDconst [255]`, and every returning or panicking `run` of `zxc` is, up to refinement, a `runL`
of the result. -/
theorem zxc_lower :
    ∃ out, lowerChecked zxcPassEnv zxcFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 3).map (fun v => (v.op, v.auxInt, v.args)) =
        some (.ARM64MOVDconst, 255, #[]) ∧
      (∃ f', GoFV.Proof.Low.Contract zxcFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.RewriteCheck.roSyms zxcPassEnv.tables zxcFunc) env mem)
        out.tables out.func zxcPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.RewriteCheck.roSyms zxcPassEnv.tables zxcFunc) env mem → ∀ fuel,
        (run env zxcTabs zxcFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env zxcTabs zxcFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := zxc_checks
  cases hc : lowerChecked zxcPassEnv zxcFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨-, h3, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h3, GoFV.Proof.Low.lower_refines hc zxc_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc zxc_generic zxc_noFma hE hro hd⟩

end GoFV.Proof.Witness
