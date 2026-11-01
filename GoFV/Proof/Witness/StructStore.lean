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
      RefinesUnder Env.Mono out.tables out.func ssPassEnv.tables ssFunc := by
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

end GoFV.Proof.Witness
