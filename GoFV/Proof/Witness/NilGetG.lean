import GoFV.Proof.Witness.LoadFwd
import GoFV.Proof.Rules.NilElim

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for the `GetG` nil-check elimination: `curg` (hand-written, issue #151)

```go
// package runtime
func curg() *g {
	gp := getg()
	_ = *gp // nil check
	return gp
}
```

as the SSA `opt` sees it (one block: `v2 = GetG v1`, `v3 = NilCheck v2 v1`, `v4 = MakeResult v3
v1`; the `g` type stands in as `*int`), and the one-rule set `{generic.rules:1062}` (as a nil-check
elimination, `RuleSet.nilChecks`): `(NilCheck ptr:(GetG mem) mem) => ptr`. `checkedRewrite` fires
the rule (`v3` becomes `Copy v2`, copy elimination makes the result `MakeResult v2 v1`) and the
validator accepts the event: the input with the elimination applied (`RewriteCheck.nilPre`) is
related to the input by nilcheckelim's checker (`NilCheck.nrel`: `GetG` is a `safePtr` seed, its
value the environment's `g` allocation) and passes `check`.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `abiInfo` of `curg`: no parameters, one pointer result. -/
def ggABI : CallABI :=
  { abi := 1, nin := 0, nout := 1, spillOff := 0, spillSize := 0, inRegs := 0, outRegs := 1,
    params := #[{ out := true, index := 0, type := 3, name := some 3, regs := #[0],
                  offset := -1 }] }

/-- The definition tables: `*int` (type 3) stands in for `*g`. -/
def ggTabs : Tables where
  types :=
    let t := Array.replicate 36 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func() *int" (.func 0 0 1 #[])))
    let t := t.set! 2 (some (mkT .INT (some 8) "int"))
    let t := t.set! 3 (some (mkT .PTR (some 8) "*int" (.elem 2)))
    let t := t.set! 29 (some (mkT .SSA none "mem"))
    let t := t.set! 31 (some (mkT .SSA none "void"))
    t.set! 35 (some (mkT .RESULTS none "*int,mem" (.results #[3, 29])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{runtime.curg}", kind := .call (some 2) (some ggABI) },
    some { fmt := GoStr.ofString "runtime.curg",
           kind := .sym (GoStr.ofString "runtime.curg") 1 "" 0 default none none none #[] none },
    some (paramNameT "~r0" .PPARAMOUT 3 0)]

/-- `curg`, the input of `opt`. -/
def ggFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 4
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[4] #[] #[] #[1, 2, 3, 4])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 3 #[] 1),
    some (mkVi 2 .GetG 3 0 p0 1 #[1] 1),
    some (mkVi 3 .NilCheck 3 0 p0 1 #[2, 1] 1),
    some (mkVi 4 .MakeResult 35 0 p0 1 #[3, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The one-rule set `{generic.rules:1062}`, as a nil-check elimination. -/
def ggRules : RuleSet where
  name := "generic"
  values := []
  blocks := []
  nilChecks := [Generated.Generic.r_generic_1062]

/-- The pass environment of `opt` (`azPassEnv`'s configuration). -/
def ggPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "curg", typs := slTyps, tables := ggTabs }

def ggCheckEnv : CheckEnv := { tabs := ggTabs, typs := slTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result whose
`MakeResult` returns the `GetG` (`v2`) instead of the nil check, which passes `check`. -/
theorem gg_checks :
    (check ggCheckEnv ggFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet ggRules) ggPassEnv ggFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := slTyps } o.func).toBool,
        (o.func.value? 4).map (·.args))) =
      some (true, some #[2, 1]) := by
  decide +kernel

/-- The one-rule set is sound (no value or block rules; its nil-check elimination is validated
per instance). -/
theorem ggRules_allSound : ggRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of trivial trivial

/-- **Pass execution witness** for `generic.rules:1062`: on `curg`, the checked rewrite pass
removes the nil check of `GetG` (`v4 = MakeResult v2 v1`), and the result refines the input
(`checkedRewrite_refines`, through `Nil.refines_of_rel` with the `GetG` seed of `safePtr`). -/
theorem gg_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet ggRules) ggPassEnv ggFunc = .ok out ∧
      (out.func.value? 4).map (·.args) = some #[2, 1] ∧
      check ggCheckEnv ggFunc = .ok () ∧
      check { tabs := out.tables, typs := slTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre ggPassEnv.tables ggPassEnv.frontend ggFunc)
      out.tables out.func ggPassEnv.tables ggFunc := by
  obtain ⟨h1, h2⟩ := gg_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet ggRules) ggPassEnv ggFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h4⟩ := h2
    exact ⟨out, rfl, h4, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := ggRules) (penv := ggPassEnv)
        (f := ggFunc) (out := out) ggRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

end GoFV.Proof.Witness
