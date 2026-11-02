import GoFV.Proof.Witness.StructLoad
import GoFV.Proof.Rules.StructStore

/-!
# Witness function for struct-store splits: `storeS` (hand-written, issue #151)

```go
type P struct{ a, b int }

func storeS(p *P, x, y int) int {
	*p = P{x, y}
	return x
}
```

as the SSA `opt` sees it (one block: `v5 = StructMake <P> v3 v4`, `v6 = Store {P} v2 v5 v1`), and
the one-rule set `{generic.rules:975}` (as a struct-store split, `RuleSet.structStores`):
`(Store _ (StructMake ___) _) => rewriteStructStore(v)`. `checkedRewrite` fires the rule (`v6`
becomes `Copy` of the second of two field `Store`s at `OffPtr [0] v2` and `OffPtr [8] v2`) and the
validator accepts it: the input with the split applied is related to the input by
`RewriteCheck.ssRel` and the output is validated against it with the remaining events.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `abiInfo` of `storeS`: three register parameters, one integer result. -/
def ssABI : CallABI :=
  { abi := 1, nin := 3, nout := 1, spillOff := 8, spillSize := 24, inRegs := 3, outRegs := 1,
    params := #[{ out := false, index := 0, type := 3, name := some 3, regs := #[0], offset := 0 },
                { out := false, index := 1, type := 2, name := some 4, regs := #[1], offset := 8 },
                { out := false, index := 2, type := 2, name := some 5, regs := #[2], offset := 16 },
                { out := true, index := 0, type := 2, name := some 6, regs := #[0],
                  offset := -1 }] }

/-- The definition tables: `P` (type 4) is `struct { a, b int }`, `*int` (type 5) exists;
`Store {P}` names its type by aux 7. -/
def ssTabs : Tables where
  types :=
    let t := Array.replicate 36 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(*P, int, int) int" (.func 0 3 1 #[])))
    let t := t.set! 2 (some (mkT .INT (some 8) "int"))
    let t := t.set! 3 (some (mkT .PTR (some 8) "*P" (.elem 4)))
    let t := t.set! 4 (some (mkT .STRUCT (some 16) "P" (.struct #[lfField "a" 0, lfField "b" 8])))
    let t := t.set! 5 (some (mkT .PTR (some 8) "*int" (.elem 2)))
    let t := t.set! 29 (some (mkT .SSA none "mem"))
    let t := t.set! 31 (some (mkT .SSA none "void"))
    t.set! 35 (some (mkT .RESULTS none "int,mem" (.results #[2, 29])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.storeS}", kind := .call (some 2) (some ssABI) },
    some { fmt := GoStr.ofString "main.storeS",
           kind := .sym (GoStr.ofString "main.storeS") 1 "" 0 default none none none #[] none },
    some (paramNameT "p" .PPARAM 3 0), some (paramNameT "x" .PPARAM 2 8),
    some (paramNameT "y" .PPARAM 2 16), some (paramNameT "~r0" .PPARAMOUT 2 0),
    some { fmt := GoStr.ofString "P", kind := .type 4 }]

/-- `storeS`, the input of `opt`. -/
def ssFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 7
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[7] #[] #[] #[1, 2, 3, 4, 5, 6, 7])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 1 #[] 1),
    some (mkV 2 .Arg 3 (some 3) p0 1 #[] 1),
    some (mkV 3 .Arg 2 (some 4) p0 2 #[] 1),
    some (mkV 4 .Arg 2 (some 5) p0 1 #[] 1),
    some (mkVi 5 .StructMake 4 0 p0 1 #[3, 4] 1),
    some (mkV 6 .Store 29 (some 7) p0 1 #[2, 5, 1] 1),
    some (mkVi 7 .MakeResult 35 0 p0 1 #[3, 6] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The one-rule set `{generic.rules:975}`, as a struct-store split. -/
def ssRules : RuleSet where
  name := "generic"
  values := []
  blocks := []
  structStores := [Generated.Generic.r_generic_975]

def ssPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "storeS", typs := slTyps, tables := ssTabs }

def ssCheckEnv : CheckEnv := { tabs := ssTabs, typs := slTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result in which
the result's memory is a field `Store` of `y` (`v4`), which passes `check`. -/
theorem ss_checks :
    (check ssCheckEnv ssFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet ssRules) ssPassEnv ssFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := slTyps } o.func).toBool,
        ((o.func.value? 7).bind fun r => r.args[1]?).bind fun m =>
          (o.func.value? m).map fun v => (v.op, v.args[1]?))) =
      some (true, some (.Store, some 4)) := by
  decide +kernel

/-- The one-rule set is sound (no value or block rules; its struct-store split is validated per
instance). -/
theorem ssRules_allSound : ssRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of trivial trivial

/-- **Pass execution witness** for `generic.rules:975`: on `storeS`, the checked rewrite pass
splits the struct `Store` `v6` into field `Store`s (the result's memory is the `Store` of `y`),
and the result refines the input (`checkedRewrite_refines`, through `StructStore.ss_refines`). -/
theorem ss_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet ssRules) ssPassEnv ssFunc = .ok out ∧
      (((out.func.value? 7).bind fun r => r.args[1]?).bind fun m =>
        (out.func.value? m).map fun v => (v.op, v.args[1]?)) = some (.Store, some 4) ∧
      check ssCheckEnv ssFunc = .ok () ∧
      check { tabs := out.tables, typs := slTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre ssPassEnv.tables ssFunc) out.tables out.func ssPassEnv.tables ssFunc := by
  obtain ⟨h1, h2⟩ := ss_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet ssRules) ssPassEnv ssFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h3⟩ := h2
    exact ⟨out, rfl, h3, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := ssRules) (penv := ssPassEnv)
        (f := ssFunc) (out := out) ssRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

/-! ## Consecutive splits: `storeS2` (a chain starting at another split's last store)

```go
func storeS2(p *P, x, y int) int {
	*p = P{x, y}
	*p = P{y, x}
	return x
}
```

as one block: `v6 = Store {P} v2 v5 v1`, `v8 = Store {P} v2 v7 v6` (`v5`, `v7` the two
`StructMake`s). The rewrite splits `v6` first; copy elimination then gives the second split's
chain the first chain's last store as its memory, which `v8`'s memory `v6` (a `Store` in the
input) does not reach through copies: `RewriteCheck.ssStart` takes it as the last store of the
split `v6`'s chain (`ss2_start`). -/

/-- `storeS2`, the input of `opt`. -/
def ss2Func : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 9
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[9] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8, 9])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 1 #[] 1),
    some (mkV 2 .Arg 3 (some 3) p0 2 #[] 1),
    some (mkV 3 .Arg 2 (some 4) p0 3 #[] 1),
    some (mkV 4 .Arg 2 (some 5) p0 2 #[] 1),
    some (mkVi 5 .StructMake 4 0 p0 1 #[3, 4] 1),
    some (mkV 6 .Store 29 (some 7) p0 1 #[2, 5, 1] 1),
    some (mkVi 7 .StructMake 4 0 p0 1 #[4, 3] 1),
    some (mkV 8 .Store 29 (some 7) p0 1 #[2, 7, 6] 1),
    some (mkVi 9 .MakeResult 35 0 p0 1 #[3, 8] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result in which
the result's memory is a field `Store` of `x` (`v3`, the second struct's last field), which
passes `check`. -/
theorem ss2_checks :
    (check ssCheckEnv ss2Func).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet ssRules) ssPassEnv ss2Func).toOption.map
      (fun o => ((check { tabs := o.tables, typs := slTyps } o.func).toBool,
        ((o.func.value? 9).bind fun r => r.args[1]?).bind fun m =>
          (o.func.value? m).map fun v => (v.op, v.args[1]?))) =
      some (true, some (.Store, some 3)) := by
  decide +kernel

/-- The second split's chain starts at a store that `v8`'s memory does not reach through copies
in the input: the last store of `v6`'s chain (`ssStart`'s second case). -/
theorem ss2_start :
    (GoFV.Rules.rewriteRun (Interp.Table.ofRuleSet ssRules) true true ssPassEnv ss2Func).toOption.map
      (fun r => let g := (RewriteCheck.ssPre (Interp.Table.ofRuleSet ssRules) ss2Func r.2.2).1
        let m0 := (RewriteCheck.ssWalk g 2 ((g.value? 8).bind (·.args[0]?) |>.getD 0)).2
        (RewriteCheck.copyReach ssTabs ss2Func.valueTab ss2Func.valueTab.size 6 m0,
          RewriteCheck.ssStart ssTabs ss2Func g 1 6 m0)) =
      some (false, true) := by
  decide +kernel

/-- **Pass execution witness** for consecutive splits: on `storeS2`, the checked rewrite pass
splits both struct `Store`s, the second chain starting at the first chain's last store, and the
result refines the input (`checkedRewrite_refines`, through `StructStore.ss_refines`). -/
theorem ss2_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet ssRules) ssPassEnv ss2Func = .ok out ∧
      (((out.func.value? 9).bind fun r => r.args[1]?).bind fun m =>
        (out.func.value? m).map fun v => (v.op, v.args[1]?)) = some (.Store, some 3) ∧
      check ssCheckEnv ss2Func = .ok () ∧
      check { tabs := out.tables, typs := slTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre ssPassEnv.tables ss2Func) out.tables out.func
        ssPassEnv.tables ss2Func := by
  obtain ⟨h1, h2⟩ := ss2_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet ssRules) ssPassEnv ss2Func with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h3⟩ := h2
    exact ⟨out, rfl, h3, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := ssRules) (penv := ssPassEnv)
        (f := ss2Func) (out := out) ssRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

/-! ## A one-element array: `storeA` (`generic.rules:997`)

```go
func storeA(p *[1]int, x int) int {
	*p = [1]int{x}
	return x
}
```

as one block: `v4 = ArrayMake1 <[1]int> v3`, `v5 = Store {[1]int} v2 v4 v1`, and the one-rule set
`{generic.rules:997}` (`(Store dst (ArrayMake1 e) mem) => (Store {e.Type} dst e mem)`, an in-place
split): `v5` becomes `Store {int} v2 v3 v1`. -/

/-- `abiInfo` of `storeA`: two register parameters, one integer result. -/
def saABI : CallABI :=
  { abi := 1, nin := 2, nout := 1, spillOff := 8, spillSize := 16, inRegs := 2, outRegs := 1,
    params := #[{ out := false, index := 0, type := 3, name := some 3, regs := #[0], offset := 0 },
                { out := false, index := 1, type := 2, name := some 4, regs := #[1], offset := 8 },
                { out := true, index := 0, type := 2, name := some 5, regs := #[0],
                  offset := -1 }] }

/-- The definition tables: `[1]int` (type 4); `Store {[1]int}` names its type by aux 6. -/
def saTabs : Tables where
  types :=
    let t := Array.replicate 36 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(*[1]int, int) int" (.func 0 2 1 #[])))
    let t := t.set! 2 (some (mkT .INT (some 8) "int"))
    let t := t.set! 3 (some (mkT .PTR (some 8) "*[1]int" (.elem 4)))
    let t := t.set! 4 (some (mkT .ARRAY (some 8) "[1]int" (.array 2 1)))
    let t := t.set! 29 (some (mkT .SSA none "mem"))
    let t := t.set! 31 (some (mkT .SSA none "void"))
    t.set! 35 (some (mkT .RESULTS none "int,mem" (.results #[2, 29])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.storeA}", kind := .call (some 2) (some saABI) },
    some { fmt := GoStr.ofString "main.storeA",
           kind := .sym (GoStr.ofString "main.storeA") 1 "" 0 default none none none #[] none },
    some (paramNameT "p" .PPARAM 3 0), some (paramNameT "x" .PPARAM 2 8),
    some (paramNameT "~r0" .PPARAMOUT 2 0),
    some { fmt := GoStr.ofString "[1]int", kind := .type 4 }]

/-- `storeA`, the input of `opt`. -/
def saFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 6
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[6] #[] #[] #[1, 2, 3, 4, 5, 6])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 1 #[] 1),
    some (mkV 2 .Arg 3 (some 3) p0 1 #[] 1),
    some (mkV 3 .Arg 2 (some 4) p0 2 #[] 1),
    some (mkVi 4 .ArrayMake1 4 0 p0 1 #[3] 1),
    some (mkV 5 .Store 29 (some 6) p0 1 #[2, 4, 1] 1),
    some (mkVi 6 .MakeResult 35 0 p0 1 #[3, 5] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The one-rule set `{generic.rules:997}`, as a struct-store split. -/
def saRules : RuleSet where
  name := "generic"
  values := []
  blocks := []
  structStores := [Generated.Generic.r_generic_997]

def saPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "storeA", typs := slTyps, tables := saTabs }

def saCheckEnv : CheckEnv := { tabs := saTabs, typs := slTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result whose
memory `v5` is a `Store` of `x` (`v3`) itself, which passes `check`. -/
theorem sa_checks :
    (check saCheckEnv saFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet saRules) saPassEnv saFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := slTyps } o.func).toBool,
        (o.func.value? 5).map fun v => (v.op, v.args[1]?))) =
      some (true, some (.Store, some 3)) := by
  decide +kernel

theorem saRules_allSound : saRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of trivial trivial

/-- **Pass execution witness** for `generic.rules:997`: on `storeA`, the checked rewrite pass
stores the array's element instead of the `ArrayMake1`, and the result refines the input
(`checkedRewrite_refines`, through `StructStore.ss_refines`). -/
theorem sa_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet saRules) saPassEnv saFunc = .ok out ∧
      (out.func.value? 5).map (fun v => (v.op, v.args[1]?)) = some (.Store, some 3) ∧
      check saCheckEnv saFunc = .ok () ∧
      check { tabs := out.tables, typs := slTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre saPassEnv.tables saFunc) out.tables out.func
        saPassEnv.tables saFunc := by
  obtain ⟨h1, h2⟩ := sa_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet saRules) saPassEnv saFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h3⟩ := h2
    exact ⟨out, rfl, h3, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := saRules) (penv := saPassEnv)
        (f := saFunc) (out := out) saRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

end GoFV.Proof.Witness
