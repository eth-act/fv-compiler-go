import GoFV.Proof.Witness.LowerAtomic

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for `lower` on an atomic read-modify-write: `aad` (hand-written, issue #385)

`aad() int { return int(atomic.AddInt64(&g, 5)) }` with a global `g` as `lower` sees it (one
block: `v3 = Addr <*int> {g} v2` of `v2 = SB`, `v4 = Const64 [5]`, `v5 = AtomicAdd64 <(int,mem)>
v3 v4 v1`, its selectors `v6`/`v7`, returned by `v8 = MakeResult v6 v7`): the checked lower fires
`(Addr {sym} base) => (MOVDaddr {sym} base)` (308), the constant's lowering and
`(AtomicAdd(32|64) ...) => (LoweredAtomicAdd(32|64) ...)` (493): `v5` becomes `LoweredAtomicAdd64
v3 v4 v1`, an atom the validator pairs with the `AtomicAdd64` (`renameOp`, `Arm64.atomicOf`),
which `runL` runs as that atomic on its operands fitted to the location (`Sem.atomicArgs`). By
`lower_refines` every returning or panicking `run` of `aad` is, up to refinement, a `runL` of the
result; with `g = 2` both return 7.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- `aad`, the input of `lower` (on `ald`'s tables: the tuple `(int,mem)` is type 30). -/
def aadFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 8
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[8] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8])]
  valueTab := #[none,
    some (mkV 1 .InitMem 28 none p0 1 #[] 1),
    some (mkV 2 .SB 4 none p0 1 #[] 1),
    some (mkV 3 .Addr 3 (some 4) p0 1 #[2] 1),
    some (mkVI 4 .Const64 2 5 none p0 1 #[] 1),
    some (mkV 5 .AtomicAdd64 30 none p0 2 #[3, 4, 1] 1),
    some (mkV 6 .Select0 2 none p0 1 #[5] 1),
    some (mkV 7 .Select1 28 none p0 1 #[5] 1),
    some (mkV 8 .MakeResult 33 none p0 1 #[6, 7] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `aad`. -/
def aadPassEnv : PassEnv :=
  { aldPassEnv with funcName := GoStr.ofString "aad" }

/-- The global `main.g` holding 2. -/
def aadMem : Mem :=
  { blocks := #[(.global "main.g", { data := #[.b 2, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0, .b 0] })] }

theorem aad_generic : aadFunc.lowered = false := by decide +kernel

/-- `aad` has no fused multiply-add shape: its contraction is itself. -/
theorem aad_noFma : GoFV.Opt.FmaContract.contractAll aadFunc = aadFunc := by decide +kernel

set_option synthInstance.maxSize 2048 in
set_option synthInstance.maxHeartbeats 200000 in
/-- By kernel evaluation: the checked lower keeps a lowered result whose `v5` is
`LoweredAtomicAdd64 v3 v4 v1`, and `aad` returns 7 under `run` of the input and `runL` of the
result. -/
theorem aad_checks :
    (lowerChecked aadPassEnv aadFunc).toOption.map (fun o =>
      ((o.func.value? 5).map (fun v => (v.op, v.auxInt, v.aux, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [] aadMem 1) 7)) =
      some (some (.ARM64LoweredAtomicAdd64, 0, none, #[3, 4, 1]), true, true) ∧
    returnsInt (run Env.p1 aldTabs aadFunc [] aadMem 1) 7 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on an atomic
read-modify-write: on `aad`, the checked lower lowers `AtomicAdd64` to `LoweredAtomicAdd64`, and
every returning or panicking `run` of `aad` is, up to refinement, a `runL` of the result. -/
theorem aad_lower :
    ∃ out, lowerChecked aadPassEnv aadFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 5).map (fun v => (v.op, v.auxInt, v.aux, v.args)) =
        some (.ARM64LoweredAtomicAdd64, 0, none, #[3, 4, 1]) ∧
      (∃ f', GoFV.Proof.Low.Contract aadFunc f' ∧
        RefinesLFrom (fun env _ mem => env.Mono ∧
          GoFV.SSA.Sem.RoImage (GoFV.Opt.LowerCheck.roPre aadPassEnv.tables aadFunc) env mem)
        out.tables out.func aadPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem,
        GoFV.SSA.Sem.RoImage
          (GoFV.Opt.LowerCheck.roPre aadPassEnv.tables aadFunc) env mem → ∀ fuel,
        (run env aldTabs aadFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env aldTabs aadFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := aad_checks
  cases hc : lowerChecked aadPassEnv aadFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h5, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h5, GoFV.Proof.Low.lower_refines hc aad_generic,
      fun env hE args mem hro fuel hd =>
        GoFV.Proof.Low.lower_refines_run hc aad_generic aad_noFma hE hro hd⟩

end GoFV.Proof.Witness
