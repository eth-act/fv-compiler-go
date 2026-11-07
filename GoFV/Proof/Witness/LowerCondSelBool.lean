import GoFV.Proof.Witness.LowerAdd
import GoFV.Proof.Witness.NotIf

/-!
# Witness function for `lower` on a `CondSelect` of a boolean argument: `bsel` (hand-written, issue #385)

`bsel(b bool) int { x := 1; if b { x = 2 }; return x }` after branchelim, as `lower` sees it
(one block: `v2 = ArgIntReg <bool>` the register argument, `v3`/`v4` the constants 1 and 2,
`v5 = CondSelect <int> v4 v3 v2`, returned by `v6 = MakeResult v5 v1`). The boolean is no
condition op, so `flagArg(v2)` is `nil` and the checked lower fires `(CondSelect x y boolval) &&
flagArg(boolval) == nil => (CSEL [OpARM64NotEqual] x y (TSTWconst [1] boolval))`
(`ARM64.rules:303`): `v5` becomes `CSEL [NotEqual] v4 v3 v7` of a fresh `v7 = TSTWconst [1] v2`.
By `lower_refines` every returning or panicking `run` of `bsel` is, up to refinement, a `runL`
of the result; `bsel(true)` returns 2 and `bsel(false)` returns 1 under both.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

-- `DecidableEq` of the nested options of tuples below exceeds the default instance size.
set_option synthInstance.maxSize 1024

/-- The definition tables of `bsel`: `notIf`'s (`func(bool) int`, `int` type 2, `bool` 4, `mem`
29, the results tuple 35), `flags` (30) and the `nameOff` aux of the register argument (5). -/
def lcbTabs : Tables :=
  { niTabs with
    types := niTabs.types.set! 30 (some (mkT .SSA none "flags"))
    auxes := niTabs.auxes.push (some { fmt := GoStr.ofString "b+0", kind := .nameOff 3 0 }) }

/-- `bsel`, the input of `lower`. -/
def lcbFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 6
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[6] #[] #[] #[1, 2, 3, 4, 5, 6])]
  valueTab := #[none,
    some (mkV 1 .InitMem 29 none p0 1 #[] 1),
    some (mkVI 2 .ArgIntReg 4 0 (some 5) p0 1 #[] 1),
    some (mkVI 3 .Const64 2 1 none p0 1 #[] 1),
    some (mkVI 4 .Const64 2 2 none p0 1 #[] 1),
    some (mkV 5 .CondSelect 2 none p0 1 #[4, 3, 2] 1),
    some (mkV 6 .MakeResult 35 none p0 1 #[5, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The pass environment of `lower` on `bsel` (`typ.Flags` is type 30). -/
def lcbPassEnv : PassEnv :=
  { laPassEnv with funcName := GoStr.ofString "bsel", tables := lcbTabs,
                   typs := #[("Int", 2), ("Bool", 4), ("Mem", 29), ("Flags", 30), ("Void", 31)] }

theorem lcb_generic : lcbFunc.lowered = false := by decide +kernel

/-- `bsel` has no fused multiply-add shape: its contraction is itself. -/
theorem lcb_noFma : GoFV.Opt.FmaContract.contractAll lcbFunc = lcbFunc := by decide +kernel

/-- By kernel evaluation: the checked lower keeps a lowered result whose `v5` is `CSEL [NotEqual]
v4 v3 v7`, `v7` `TSTWconst [1] v2`, and `bsel(true) = 2`, `bsel(false) = 1` under `run` of the
input and `runL` of the result. -/
theorem lcb_checks :
    (lowerChecked lcbPassEnv lcbFunc).toOption.map (fun o =>
      ((o.func.value? 5).map (fun v => (v.op, v.auxInt, v.args)),
        (o.func.value? 7).map (fun v => (v.op, v.auxInt, v.args)), o.func.lowered,
        returnsInt (runL Env.p1 o.tables o.func [.bool true] {} 1) 2,
        returnsInt (runL Env.p1 o.tables o.func [.bool false] {} 1) 1)) =
      some (some (.ARM64CSEL, Int64.ofNat Op.ARM64NotEqual.goNum, #[4, 3, 7]),
        some (.ARM64TSTWconst, 1, #[2]), true, true, true) ∧
    returnsInt (run Env.p1 lcbTabs lcbFunc [.bool true] {} 1) 2 = true ∧
    returnsInt (run Env.p1 lcbTabs lcbFunc [.bool false] {} 1) 1 = true := by
  decide +kernel

/-- **Pass execution witness** for `lower_refines` (`lower_refines_run`) on a `CondSelect` of a
boolean that is no condition (`ARM64.rules:303`): on `bsel`, the checked lower selects by `CSEL
[NotEqual]` on `TSTWconst [1]` of the argument, and every returning or panicking `run` of `bsel`
is, up to refinement, a `runL` of the result. -/
theorem lcb_lower :
    ∃ out, lowerChecked lcbPassEnv lcbFunc = .ok out ∧ out.func.lowered = true ∧
      (out.func.value? 5).map (fun v => (v.op, v.auxInt, v.args)) =
        some (.ARM64CSEL, Int64.ofNat Op.ARM64NotEqual.goNum, #[4, 3, 7]) ∧
      (out.func.value? 7).map (fun v => (v.op, v.auxInt, v.args)) =
        some (.ARM64TSTWconst, 1, #[2]) ∧
      (∃ f', GoFV.Proof.Low.Contract lcbFunc f' ∧
        RefinesLFrom (fun env _ _ => env.Mono) out.tables out.func lcbPassEnv.tables f') ∧
      ∀ env, env.Mono → ∀ args mem fuel, (run env lcbTabs lcbFunc args mem fuel).Defined →
        ∃ fuel', OutcomeRefines 0 (run env lcbTabs lcbFunc args mem fuel)
          (runL env out.tables out.func args mem fuel') := by
  obtain ⟨h1, -⟩ := lcb_checks
  cases hc : lowerChecked lcbPassEnv lcbFunc with
  | error e => rw [hc] at h1; cases h1
  | ok out =>
    rw [hc] at h1
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨h5, h7, hl, -⟩ := h1
    exact ⟨out, rfl, hl, h5, h7, GoFV.Proof.Low.lower_refines hc lcb_generic,
      fun env hE args mem fuel hd => GoFV.Proof.Low.lower_refines_run hc lcb_generic lcb_noFma hE hd⟩

end GoFV.Proof.Witness
