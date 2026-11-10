import GoFV.Proof.Witness.FwdGrow

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for the length register of a post-`expand calls` `growslice` call (`generic.rules:2131`, issue #69)

```go
func grow(p, t *int) int {
	s := growslice(p, 3, 0, 3, t) // v7 = StaticCall {runtime.growslice} v2 v3 v4 v3 v6 v1
	return len(s)                 // v8 = SelectN [1] v7
}
```

as one block, after `expand calls`: the call passes its arguments' register pieces and yields its
slice result's register pieces (pointer, length, capacity), then the memory. The checked rewrite
pass with `{:2131}` (a forwarding, `RuleSet.loads`) turns the length register `v8` into a copy of
the call's constant length argument `v3`: the validator relates `SelectN [1] c` to `c`'s second
argument (`RewriteCheck.growPOK`), which the callee gets in one register and `runtime.growslice`
returns as the slice's length (`Sem.Env.GrowLen`). The result's `MakeResult` takes `v3`.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- The definition tables of `grTabs`, with `*int,int,int,mem` (type 33) the type of the
post-`expand calls` call. -/
def gpTabs : Tables :=
  { grTabs with
    types := grTabs.types.set! 33 (some (mkT .RESULTS none "*int,int,int,mem" (.results #[3, 2, 2, 29]))) }

/-- `grow` after `expand calls`, the input of `late opt`. -/
def gpFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 10
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[10] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 1 #[] 1),
    some (mkV 2 .Arg 3 (some 3) p0 1 #[] 1),
    some (mkVi 3 .Const64 2 3 p0 2 #[] 1),
    some (mkVi 4 .Const64 2 0 p0 1 #[] 1),
    some (mkVi 5 .Const64 2 1 p0 0 #[] 1),
    some (mkV 6 .Arg 3 (some 4) p0 1 #[] 1),
    some (mkV 7 .StaticCall 33 (some 6) p0 2 #[2, 3, 4, 3, 6, 1] 1),
    some (mkVi 8 .SelectN 2 1 p0 1 #[7] 1),
    some (mkVi 9 .SelectN 29 3 p0 1 #[7] 1),
    some (mkVi 10 .MakeResult 35 0 p0 1 #[8, 9] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The rule set `{generic.rules:2131}`, as a forwarding. -/
def gpRules : RuleSet where
  name := "generic"
  values := []
  blocks := []
  loads := [Generated.Generic.r_generic_2131]

theorem gpRules_allSound : gpRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of trivial trivial

def gpPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "grow", typs := slTyps, tables := gpTabs }

def gpCheckEnv : CheckEnv := { tabs := gpTabs, typs := slTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result, which
passes `check`, whose `MakeResult` takes the length argument `v3`. -/
theorem gp_checks :
    (check gpCheckEnv gpFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet gpRules) gpPassEnv gpFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := slTyps } o.func).toBool,
        (o.func.value? 10).map (·.args))) =
      some (true, some #[3, 9]) := by
  decide +kernel

/-- **Pass execution witness** for the length register of a post-`expand calls` `growslice` call
(`generic.rules:2131`): on `grow` after `expand calls`, the checked rewrite pass returns the
length argument (`v10 = MakeResult v3 v9`), and the result refines the input under `RwPre`
(`checkedRewrite_refines`, through `LoadFwd.fwd_refines` under `Env.GrowLen`). -/
theorem gp_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet gpRules) gpPassEnv gpFunc = .ok out ∧
      (out.func.value? 10).map (·.args) = some #[3, 9] ∧
      check gpCheckEnv gpFunc = .ok () ∧
      check { tabs := out.tables, typs := slTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre gpPassEnv.tables gpPassEnv.frontend gpFunc)
        out.tables out.func gpPassEnv.tables gpFunc := by
  obtain ⟨h1, h2⟩ := gp_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet gpRules) gpPassEnv gpFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h11⟩ := h2
    exact ⟨out, rfl, h11, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := gpRules) (penv := gpPassEnv)
        (f := gpFunc) (out := out) gpRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

/-- **Non-vacuity of `gp_checkedRewrite`'s precondition**: `RwPre` holds on `Env.p1` (which has
no `growslice` contract) for pointer arguments from an empty memory; `Env.GrowLen` also holds of
the runtime model (`Env.runtime_growLen`). -/
theorem gp_rwPre :
    GoFV.Proof.Pass.Rewrite.RwPre gpPassEnv.tables gpPassEnv.frontend gpFunc Env.p1
      [.ptr ⟨.heap 0, 0⟩, .ptr ⟨.heap 1, 0⟩] {} ∧ Env.runtime.GrowLen :=
  ⟨GoFV.Proof.Pass.Rewrite.RwPre.p1 (by decide +kernel) (by decide +kernel)
    (GoFV.Proof.Pass.Rewrite.initAvoids_empty (fun v hv _ _ => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with rfl | rfl <;> intro h <;> cases h) rfl),
    Env.runtime_growLen⟩

end GoFV.Proof.Witness
