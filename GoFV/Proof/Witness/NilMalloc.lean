import GoFV.Proof.Witness.NilGetG

/-!
# Witness function for the malloc-result and dictionary nil-check eliminations (issue #151)

```go
// a generic function's shape instance: `.dict` is its dictionary parameter
func newInt(.dict *int) *int {
	_ = *.dict    // nil check of the dictionary (generic.rules:1384)
	p := new(int) // runtime.newobject
	_ = *p        // nil check of the malloc result (generic.rules:1367)
	return p
}
```

as the SSA `opt` sees it (one block: `v2 = Arg {.dict}`, `v3 = NilCheck v2 v1`,
`v4 = StaticLECall {runtime.newobject} v2 v1`, `v5 = SelectN [0] v4`, `v6 = SelectN [1] v4`,
`v7 = NilCheck v5 v6`, `v8 = MakeResult v7 v6`; the dictionary stands in as the `newobject`
argument), and the rule set `{generic.rules:1367, :1384}` (nil-check eliminations). `checkedRewrite`
fires both rules and the validator accepts them: nilcheckelim's checker with the rewrite passes'
seeds (`NilCheck.nrel true`) takes the `SelectN [0]` of the `newobject` call (`mallocCall`) and
the `.dict` argument (`dictArg`) as non-nil. The result refines the input under `RwPre`
(`checkedRewrite_refines`), which holds, e.g., on `Env.p1` with a non-nil dictionary
(`nm_rwPre`); the runtime's allocators satisfy `Env.AllocNonNil` (`Env.runtime_allocNonNil`).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `abiInfo` of `newInt`: one pointer parameter (`.dict`), one pointer result. -/
def nmABI : CallABI :=
  { abi := 1, nin := 1, nout := 1, spillOff := 8, spillSize := 8, inRegs := 1, outRegs := 1,
    params := #[{ out := false, index := 0, type := 3, name := some 3, regs := #[0], offset := 0 },
                { out := true, index := 0, type := 3, name := some 4, regs := #[0],
                  offset := -1 }] }

/-- `abiInfo` of `runtime.newobject`: one pointer parameter, one pointer result. -/
def nmNewABI : CallABI :=
  { abi := 1, nin := 1, nout := 1, spillOff := 8, spillSize := 8, inRegs := 1, outRegs := 1,
    params := #[{ out := false, index := 0, type := 3, name := none, regs := #[0], offset := 0 },
                { out := true, index := 0, type := 3, name := none, regs := #[0], offset := -1 }] }

/-- The definition tables. -/
def nmTabs : Tables where
  types :=
    let t := Array.replicate 36 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(*int) *int" (.func 0 1 1 #[])))
    let t := t.set! 2 (some (mkT .INT (some 8) "int"))
    let t := t.set! 3 (some (mkT .PTR (some 8) "*int" (.elem 2)))
    let t := t.set! 29 (some (mkT .SSA none "mem"))
    let t := t.set! 31 (some (mkT .SSA none "void"))
    t.set! 35 (some (mkT .RESULTS none "*int,mem" (.results #[3, 29])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.newInt}", kind := .call (some 2) (some nmABI) },
    some { fmt := GoStr.ofString "main.newInt",
           kind := .sym (GoStr.ofString "main.newInt") 1 "" 0 default none none none #[] none },
    some (paramNameT ".dict" .PPARAM 3 0),
    some (paramNameT "~r0" .PPARAMOUT 3 0),
    some { fmt := GoStr.ofString "AuxCall{runtime.newobject}",
           kind := .call (some 6) (some nmNewABI) },
    some { fmt := GoStr.ofString "runtime.newobject",
           kind := .sym (GoStr.ofString "runtime.newobject") 1 "" 0 default none none none #[]
             none }]

/-- `newInt`, the input of `opt`. -/
def nmFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 8
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[8] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 2 #[] 1),
    some (mkV 2 .Arg 3 (some 3) p0 2 #[] 1),
    some (mkVi 3 .NilCheck 3 0 p0 0 #[2, 1] 1),
    some (mkV 4 .StaticLECall 35 (some 5) p0 2 #[2, 1] 1),
    some (mkVi 5 .SelectN 3 0 p0 1 #[4] 1),
    some (mkVi 6 .SelectN 29 1 p0 2 #[4] 1),
    some (mkVi 7 .NilCheck 3 0 p0 1 #[5, 6] 1),
    some (mkVi 8 .MakeResult 35 0 p0 1 #[7, 6] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The rule set `{generic.rules:1367, :1384}`, as nil-check eliminations. -/
def nmRules : RuleSet where
  name := "generic"
  values := []
  blocks := []
  nilChecks := [Generated.Generic.r_generic_1367, Generated.Generic.r_generic_1384]

/-- The pass environment of `opt` (`azPassEnv`'s configuration). -/
def nmPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "newInt", typs := slTyps, tables := nmTabs }

def nmCheckEnv : CheckEnv := { tabs := nmTabs, typs := slTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result whose
`MakeResult` returns the `newobject` result (`v5`) instead of its nil check and in which neither
nil check is left, which passes `check`. -/
theorem nm_checks :
    (check nmCheckEnv nmFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet nmRules) nmPassEnv nmFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := slTyps } o.func).toBool,
        (o.func.value? 8).map (·.args),
        [3, 7].all fun x => (o.func.value? x).all (·.op != .NilCheck))) =
      some (true, some #[5, 6], true) := by
  decide +kernel

/-- `newInt`'s dictionary parameter is its first input. -/
theorem nm_dictParams : NilCheck.dictParams nmTabs nmFunc = [0] := by decide +kernel

/-- The rule set is sound (no value or block rules; its nil-check eliminations are validated
per instance). -/
theorem nmRules_allSound : nmRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of trivial trivial

/-- **Pass execution witness** for `generic.rules:1367` and `:1384`: on `newInt`, the checked
rewrite pass removes the nil checks of the `newobject` result and of the dictionary
(`v8 = MakeResult v5 v6`), and the result refines the input under `RwPre`
(`checkedRewrite_refines`, through `Nil.refinesFrom_of_rel` with the seeds of `safePtr true`). -/
theorem nm_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet nmRules) nmPassEnv nmFunc = .ok out ∧
      (out.func.value? 8).map (·.args) = some #[5, 6] ∧
      check nmCheckEnv nmFunc = .ok () ∧
      check { tabs := out.tables, typs := slTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre nmPassEnv.tables nmPassEnv.frontend nmFunc)
        out.tables out.func
        nmPassEnv.tables nmFunc := by
  obtain ⟨h1, h2⟩ := nm_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet nmRules) nmPassEnv nmFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h8, -⟩ := h2
    exact ⟨out, rfl, h8, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := nmRules) (penv := nmPassEnv)
        (f := nmFunc) (out := out) nmRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

/-- **Non-vacuity of `RwPre` with a dictionary**: monotone contracts without allocators or memory
runtime calls (`Env.p1`) and a non-nil `.dict` argument. -/
theorem nm_rwPre :
    GoFV.Proof.Pass.Rewrite.RwPre nmTabs nmPassEnv.frontend nmFunc Env.p1 [.ptr ⟨.heap 0, 0⟩] {} := by
  refine ⟨Env.p1_mono, ⟨Env.p1_allocNonNil, ?_⟩, Env.p1_memOps, Env.p1_allocZero, ?_,
    GoFV.Proof.Pass.Rewrite.initAvoids_empty (fun v hv _ _ => by
      simp only [List.mem_singleton] at hv; subst hv; intro h; cases h) rfl, Env.p1_growLen,
    Env.p1_ifaceEq _⟩
  · rw [nm_dictParams]
    intro i hi
    simp only [List.mem_singleton] at hi
    subst hi
    exact ⟨_, rfl, nofun⟩
  · rw [show GoFV.Opt.RewriteCheck.roPass nmTabs nmPassEnv.frontend nmFunc = [] by decide +kernel]
    exact RoImage.nil Env.p1_keepsRo _

end GoFV.Proof.Witness
