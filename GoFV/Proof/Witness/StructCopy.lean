import GoFV.Proof.Witness.StructStore

/-!
# Witness function for a split `Store` of an expanded `Load`: `copyP` (hand-written, issue #151)

```go
type P struct{ a, b int }

func copyP(p, q *P) {
	*p = *q
}
```

as the SSA `opt` sees it (one block: `v4 = Load <P> v3 v1`, `v5 = Store {P} v2 v4 v1`), and the
rule set `{generic.rules:974}` (a struct-load expansion) and `{:975}` (a struct-store split).
`checkedRewrite` expands the `Load` (`v4` becomes `StructMake` of field `Load`s at `OffPtr [0] v3`
and `OffPtr [8] v3`) and then splits the `Store` of it into field `Store`s of the field `Load`s.
In the input the stored value is a `Load`, which the split relation (`RewriteCheck.ssSplit?`)
does not take: the validator's struct-load layer (`RewriteCheck.slPre`, related to its input by
`validate` with the expansion alone) applies the expansion before the split layer.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `abiInfo` of `copyP`: two pointer register parameters, no result. -/
def scABI : CallABI :=
  { abi := 1, nin := 2, nout := 0, spillOff := 8, spillSize := 16, inRegs := 2, outRegs := 0,
    params := #[{ out := false, index := 0, type := 3, name := some 3, regs := #[0], offset := 0 },
                { out := false, index := 1, type := 3, name := some 4, regs := #[1],
                  offset := 8 }] }

/-- The definition tables: `P` (type 4) is `struct { a, b int }`, `*int` (type 5) exists;
`Store {P}` names its type by aux 5. -/
def scTabs : Tables where
  types :=
    let t := Array.replicate 36 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(*P, *P)" (.func 0 2 0 #[])))
    let t := t.set! 2 (some (mkT .INT (some 8) "int"))
    let t := t.set! 3 (some (mkT .PTR (some 8) "*P" (.elem 4)))
    let t := t.set! 4 (some (mkT .STRUCT (some 16) "P" (.struct #[lfField "a" 0, lfField "b" 8])))
    let t := t.set! 5 (some (mkT .PTR (some 8) "*int" (.elem 2)))
    let t := t.set! 29 (some (mkT .SSA none "mem"))
    let t := t.set! 31 (some (mkT .SSA none "void"))
    t.set! 35 (some (mkT .RESULTS none "mem" (.results #[29])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.copyP}", kind := .call (some 2) (some scABI) },
    some { fmt := GoStr.ofString "main.copyP",
           kind := .sym (GoStr.ofString "main.copyP") 1 "" 0 default none none none #[] none },
    some (paramNameT "p" .PPARAM 3 0), some (paramNameT "q" .PPARAM 3 8),
    some { fmt := GoStr.ofString "P", kind := .type 4 }]

/-- `copyP`, the input of `opt`. -/
def scFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 6
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[6] #[] #[] #[1, 2, 3, 4, 5, 6])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 2 #[] 1),
    some (mkV 2 .Arg 3 (some 3) p0 1 #[] 1),
    some (mkV 3 .Arg 3 (some 4) p0 1 #[] 1),
    some (mkVi 4 .Load 4 0 p0 1 #[3, 1] 1),
    some (mkV 5 .Store 29 (some 5) p0 1 #[2, 4, 1] 1),
    some (mkVi 6 .MakeResult 35 0 p0 1 #[5] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The rule set `{generic.rules:974}` (a struct-load expansion) and `{:975}` (a struct-store
split). -/
def scRules : RuleSet where
  name := "generic"
  values := []
  blocks := []
  structLoads := [Generated.Generic.r_generic_974]
  structStores := [Generated.Generic.r_generic_975]

def scPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "copyP", typs := slTyps, tables := scTabs }

def scCheckEnv : CheckEnv := { tabs := scTabs, typs := slTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result in which
the result's memory is a field `Store` of a field `Load`, which passes `check`. -/
theorem sc_checks :
    (check scCheckEnv scFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet scRules) scPassEnv scFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := slTyps } o.func).toBool,
        ((o.func.value? 6).bind fun r => r.args[0]?).bind fun m =>
          (o.func.value? m).bind fun v => (v.args[1]?.bind o.func.value?).map fun x => (v.op, x.op))) =
      some (true, some (.Store, .Load)) := by
  decide +kernel

/-- The rule set is sound (no value or block rules; its struct-load expansion and struct-store
split are validated per instance). -/
theorem scRules_allSound : scRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of trivial trivial

/-- **Pass execution witness** for a split `Store` of an expanded `Load`: on `copyP`, the checked
rewrite pass expands `*q` (`generic.rules:974`) and splits the `Store` of it (`:975`) into field
`Store`s of field `Load`s, and the result refines the input (`checkedRewrite_refines`: the
struct-load layer by the validator and the atom simulation, then the split layer,
`StructStore.ss_refines`; `chain_refines`). -/
theorem sc_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet scRules) scPassEnv scFunc = .ok out ∧
      (((out.func.value? 6).bind fun r => r.args[0]?).bind fun m =>
        (out.func.value? m).bind fun v => (v.args[1]?.bind out.func.value?).map fun x =>
          (v.op, x.op)) = some (.Store, .Load) ∧
      check scCheckEnv scFunc = .ok () ∧
      check { tabs := out.tables, typs := slTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre scPassEnv.tables scPassEnv.frontend scFunc)
      out.tables out.func
        scPassEnv.tables scFunc := by
  obtain ⟨h1, h2⟩ := sc_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet scRules) scPassEnv scFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h3⟩ := h2
    exact ⟨out, rfl, h3, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := scRules) (penv := scPassEnv)
        (f := scFunc) (out := out) scRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

end GoFV.Proof.Witness
