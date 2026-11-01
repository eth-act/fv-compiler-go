import GoFV.Proof.Witness.ConstString
import GoFV.Proof.Rules.LoadFwd

/-!
# Witness function for Load-of-Store forwarding: `storeLoad` (hand-written, issue #151)

```go
func storeLoad(p *int, x int) int {
	*p = x
	return *p
}
```

as the SSA `opt` sees it (one block, `p` and `x` integer register parameters), and the one-rule
set `{generic.rules:800}` (as a forwarding, `RuleSet.loads`): `(Load <t1> p1 (Store {t2} p2 x
_)) && isSamePtr(p1, p2) && … => x`. `checkedRewrite` fires the rule (`v5 = Load v2 v4` becomes
`Copy v3`), copy elimination makes the result `MakeResult v3 v4`, and the validator accepts it:
the input with the forwarding applied is related to the input by `RewriteCheck.fwdRel` (the
`Store` `v4` writes `v3` at the Load's pointer `v2`, at the integer shape) and the output is
validated against it with the remaining events.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `abiInfo` of `storeLoad`: two integer register parameters, one result. -/
def slABI : CallABI :=
  { abi := 1, nin := 2, nout := 1, spillOff := 8, spillSize := 16, inRegs := 2, outRegs := 1,
    params := #[{ out := false, index := 0, type := 3, name := some 3, regs := #[0], offset := 0 },
                { out := false, index := 1, type := 2, name := some 4, regs := #[1], offset := 8 },
                { out := true, index := 0, type := 2, name := some 5, regs := #[0],
                  offset := -1 }] }

/-- The definition tables: `Store {int}` names its type by aux 6. -/
def slTabs : Tables where
  types :=
    let t := Array.replicate 36 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(*int, int) int" (.func 0 2 1 #[])))
    let t := t.set! 2 (some (mkT .INT (some 8) "int"))
    let t := t.set! 3 (some (mkT .PTR (some 8) "*int" (.elem 2)))
    let t := t.set! 29 (some (mkT .SSA none "mem"))
    let t := t.set! 31 (some (mkT .SSA none "void"))
    t.set! 35 (some (mkT .RESULTS none "int,mem" (.results #[2, 29])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.storeLoad}", kind := .call (some 2) (some slABI) },
    some { fmt := GoStr.ofString "main.storeLoad",
           kind := .sym (GoStr.ofString "main.storeLoad") 1 "" 0 default none none none #[] none },
    some (paramNameT "p" .PPARAM 3 0), some (paramNameT "x" .PPARAM 2 8),
    some (paramNameT "~r0" .PPARAMOUT 2 0),
    some { fmt := GoStr.ofString "int", kind := .type 2 }]

/-- `storeLoad`, the input of `opt`. -/
def slFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 6
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[6] #[] #[] #[1, 2, 3, 4, 5, 6])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 1 #[] 1),
    some (mkV 2 .Arg 3 (some 3) p0 2 #[] 1),
    some (mkV 3 .Arg 2 (some 4) p0 1 #[] 1),
    some (mkV 4 .Store 29 (some 6) p0 2 #[2, 3, 1] 1),
    some (mkVi 5 .Load 2 0 p0 1 #[2, 4] 1),
    some (mkVi 6 .MakeResult 35 0 p0 1 #[5, 4] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The one-rule set `{generic.rules:800}`, as a forwarding. -/
def slRules : RuleSet where
  name := "generic"
  values := []
  blocks := []
  loads := [Generated.Generic.r_generic_800]

def slTyps : Array (String × TypeRef) := #[("Int", 2), ("Mem", 29), ("Void", 31)]

/-- The pass environment of `opt` (`azPassEnv`'s configuration). -/
def slPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "storeLoad", typs := slTyps, tables := slTabs }

def slCheckEnv : CheckEnv := { tabs := slTabs, typs := slTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result whose
`MakeResult` reads `x` (`v3`) instead of the Load, which passes `check`. -/
theorem sl_checks :
    (check slCheckEnv slFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet slRules) slPassEnv slFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := slTyps } o.func).toBool,
        (o.func.value? 6).map (·.args))) =
      some (true, some #[3, 4]) := by
  decide +kernel

/-- The one-rule set is sound (no value or block rules; its forwarding is validated per
instance). -/
theorem slRules_allSound : slRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of trivial trivial

/-- **Pass execution witness**: on `storeLoad`, the checked rewrite pass with
`{generic.rules:800}` forwards the stored `x` to the `return` (`v6 = MakeResult v3 v4`), and the
result refines the input (`checkedRewrite_refines`, through `LoadFwd.fwd_refines`). -/
theorem sl_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet slRules) slPassEnv slFunc = .ok out ∧
      (out.func.value? 6).map (·.args) = some #[3, 4] ∧
      check slCheckEnv slFunc = .ok () ∧ check { tabs := out.tables, typs := slTyps } out.func = .ok () ∧
      RefinesUnder Env.Mono out.tables out.func slPassEnv.tables slFunc := by
  obtain ⟨h1, h2⟩ := sl_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet slRules) slPassEnv slFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h6⟩ := h2
    exact ⟨out, rfl, h6, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := slRules) (penv := slPassEnv)
        (f := slFunc) (out := out) slRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

end GoFV.Proof.Witness
