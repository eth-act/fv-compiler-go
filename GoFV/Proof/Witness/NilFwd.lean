import GoFV.Proof.Witness.NilMalloc

/-!
# Witness function for a nil check of a forwarded `Load` (issue #151)

```go
func reload(pp **int) *int {
	*pp = new(int) // runtime.newobject
	q := *pp       // forwarded: the newobject result (generic.rules:800)
	_ = *q         // nil check of the newobject result (generic.rules:1367)
	return q
}
```

as the SSA `opt` sees it (one block: `v2 = Arg {pp}`, `v3 = StaticLECall {runtime.newobject}
v2 v1`, `v4 = SelectN [0] v3`, `v5 = SelectN [1] v3`, `v6 = Store {*int} v2 v4 v5`,
`v7 = Load v2 v6`, `v8 = NilCheck v7 v6`, `v9 = MakeResult v8 v6`; `pp` stands in as the
`newobject` argument), and the rule set `{generic.rules:800}` (forwarding) and `{:1367}` (nil-check
elimination). The rewrite forwards `v7` to `v4`, after which `:1367` removes the nil check of
`v4`. In the input the nil check's pointer is the `Load`, which `NilCheck.safePtr` does not take
as non-nil: the validator's layers (`RewriteCheck.layers`) apply the forwarding first (`v7`
becomes `Copy v4`) and the nil-check elimination after it, where `safePtr` takes the `Copy` of the
`newobject` result as non-nil.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `abiInfo` of `reload`: one pointer parameter, one pointer result. -/
def nfABI : CallABI :=
  { abi := 1, nin := 1, nout := 1, spillOff := 8, spillSize := 8, inRegs := 1, outRegs := 1,
    params := #[{ out := false, index := 0, type := 4, name := some 3, regs := #[0], offset := 0 },
                { out := true, index := 0, type := 3, name := some 4, regs := #[0],
                  offset := -1 }] }

/-- The definition tables: `Store {*int}` names its type by aux 7. -/
def nfTabs : Tables where
  types :=
    let t := Array.replicate 36 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(**int) *int" (.func 0 1 1 #[])))
    let t := t.set! 2 (some (mkT .INT (some 8) "int"))
    let t := t.set! 3 (some (mkT .PTR (some 8) "*int" (.elem 2)))
    let t := t.set! 4 (some (mkT .PTR (some 8) "**int" (.elem 3)))
    let t := t.set! 29 (some (mkT .SSA none "mem"))
    let t := t.set! 31 (some (mkT .SSA none "void"))
    t.set! 35 (some (mkT .RESULTS none "*int,mem" (.results #[3, 29])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.reload}", kind := .call (some 2) (some nfABI) },
    some { fmt := GoStr.ofString "main.reload",
           kind := .sym (GoStr.ofString "main.reload") 1 "" 0 default none none none #[] none },
    some (paramNameT "pp" .PPARAM 4 0),
    some (paramNameT "~r0" .PPARAMOUT 3 0),
    some { fmt := GoStr.ofString "AuxCall{runtime.newobject}",
           kind := .call (some 6) (some nmNewABI) },
    some { fmt := GoStr.ofString "runtime.newobject",
           kind := .sym (GoStr.ofString "runtime.newobject") 1 "" 0 default none none none #[]
             none },
    some { fmt := GoStr.ofString "*int", kind := .type 3 }]

/-- `reload`, the input of `opt`. -/
def nfFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 9
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[9] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8, 9])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 1 #[] 1),
    some (mkV 2 .Arg 4 (some 3) p0 3 #[] 1),
    some (mkV 3 .StaticLECall 35 (some 5) p0 2 #[2, 1] 1),
    some (mkVi 4 .SelectN 3 0 p0 1 #[3] 1),
    some (mkVi 5 .SelectN 29 1 p0 1 #[3] 1),
    some (mkV 6 .Store 29 (some 7) p0 3 #[2, 4, 5] 1),
    some (mkVi 7 .Load 3 0 p0 1 #[2, 6] 1),
    some (mkVi 8 .NilCheck 3 0 p0 1 #[7, 6] 1),
    some (mkVi 9 .MakeResult 35 0 p0 1 #[8, 6] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The rule set `{generic.rules:800}` (a forwarding) and `{:1367}` (a nil-check elimination). -/
def nfRules : RuleSet where
  name := "generic"
  values := []
  blocks := []
  nilChecks := [Generated.Generic.r_generic_1367]
  loads := [Generated.Generic.r_generic_800]

/-- The pass environment of `opt` (`azPassEnv`'s configuration). -/
def nfPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "reload", typs := slTyps, tables := nfTabs }

def nfCheckEnv : CheckEnv := { tabs := nfTabs, typs := slTyps }

/-- By kernel evaluation: the input passes `check`, the nil check's pointer in the input is not a
`safePtr true` seed, and `checkedRewrite` keeps a result whose `MakeResult` returns the
`newobject` result (`v4`) and in which no nil check is left, which passes `check`. -/
theorem nf_checks :
    (check nfCheckEnv nfFunc).toBool = true ∧
    NilCheck.safePtr true nfTabs nfFunc nfFunc.valueTab.size 7 = false ∧
    (checkedRewrite (Interp.Table.ofRuleSet nfRules) nfPassEnv nfFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := slTyps } o.func).toBool,
        (o.func.value? 9).map (·.args),
        (o.func.value? 8).all (·.op != .NilCheck))) =
      some (true, some #[4, 6], true) := by
  decide +kernel

/-- `reload` has no dictionary parameters. -/
theorem nf_dictParams : NilCheck.dictParams nfTabs nfFunc = [] := by decide +kernel

/-- The rule set is sound (no value or block rules; its forwarding and nil-check elimination are
validated per instance). -/
theorem nfRules_allSound : nfRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of trivial trivial

/-- **Pass execution witness** for a nil check of a forwarded `Load`: on `reload`, the checked
rewrite pass forwards the stored `newobject` result and removes its nil check
(`v9 = MakeResult v4 v6`), and the result refines the input under `RwPre`
(`checkedRewrite_refines`: the forwarding layer, `LoadFwd.fwd_refines`, then the nil-check layer,
`Nil.refinesFrom_of_rel`, `chain_refines`), which holds on `Env.p1` (`RwPre.p1`). -/
theorem nf_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet nfRules) nfPassEnv nfFunc = .ok out ∧
      (out.func.value? 9).map (·.args) = some #[4, 6] ∧
      check nfCheckEnv nfFunc = .ok () ∧
      check { tabs := out.tables, typs := slTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre nfPassEnv.tables nfPassEnv.frontend nfFunc)
        out.tables out.func nfPassEnv.tables nfFunc ∧
      ∀ args mem,
        GoFV.Proof.Pass.Rewrite.RwPre nfPassEnv.tables nfPassEnv.frontend nfFunc Env.p1 args mem := by
  obtain ⟨h1, -, h2⟩ := nf_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet nfRules) nfPassEnv nfFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h9, -⟩ := h2
    exact ⟨out, rfl, h9, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := nfRules) (penv := nfPassEnv)
        (f := nfFunc) (out := out) nfRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg),
      fun args mem => GoFV.Proof.Pass.Rewrite.RwPre.p1 nf_dictParams
        (by decide +kernel) args mem⟩

end GoFV.Proof.Witness
