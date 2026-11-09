import GoFV.Proof.Witness.IMakeSM
import GoFV.Proof.Rules.IDataSel

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for a selection of an interface's data word: `unbox` (hand-written, issue #69)

```go
type S struct{ p *int }

func unbox(e any) *int { return e.(S).p } // after the type check: the struct in the data word
```

as opt sees it: `v3 = IData <S> v2` of the interface argument `v2`, `v4 = StructSelect [0] <*int>
v3` is returned. The one-rule set `{generic.rules:982}` (`(StructSelect (IData x)) &&
v.Type.Size() > 0 => (IData x)`, `Rule.Sound` with `idataArgOk`): `checkedRewrite` makes `v4`
the data word `IData <*int> v2`, and the result refines the input.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `abiInfo` of `unbox`: an interface parameter in two registers, one pointer result. -/
def idABI : CallABI :=
  { abi := 1, nin := 1, nout := 1, spillOff := 8, spillSize := 16, inRegs := 2, outRegs := 1,
    params := #[{ out := false, index := 0, type := 23, name := some 3, regs := #[0, 1], offset := 0 },
                { out := true, index := 0, type := 20, name := some 4, regs := #[0],
                  offset := -1 }] }

/-- The definition tables of `box` (`bxTabs`) with `unbox`'s function type and results. -/
def idTabs : Tables where
  types :=
    let t := bxTabs.types.push none
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(interface {}) *int" (.func 0 1 1 #[])))
    t.set! 36 (some (mkT .RESULTS none "*int,mem" (.results #[20, 29])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.unbox}", kind := .call (some 2) (some idABI) },
    some { fmt := GoStr.ofString "main.unbox",
           kind := .sym (GoStr.ofString "main.unbox") 1 "" 0 default none none none #[] none },
    some (paramNameT "e" .PPARAM 23 0), some (paramNameT "~r0" .PPARAMOUT 20 0)]

/-- `unbox`, the input of opt. -/
def idFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 5
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[5] #[] #[] #[1, 2, 3, 4, 5])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 1 #[] 1),
    some (mkV 2 .Arg 23 (some 3) p0 1 #[] 1),
    some (mkVi 3 .IData 22 0 p0 1 #[2] 1),
    some (mkVi 4 .StructSelect 20 0 p0 1 #[3] 1),
    some (mkVi 5 .MakeResult 36 0 p0 1 #[4, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The one-rule set `{generic.rules:982}`. -/
def idRules : RuleSet where
  name := "generic"
  values := [(.StructSelect, [Generated.Generic.r_generic_982])]
  blocks := []

def idPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "unbox", typs := slTyps, tables := idTabs }

def idCheckEnv : CheckEnv := { tabs := idTabs, typs := slTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result in which
`v4` is `IData v2`, which passes `check`. -/
theorem id_checks :
    (check idCheckEnv idFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet idRules) idPassEnv idFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := slTyps } o.func).toBool,
        (o.func.value? 4).map (fun v => (v.op, v.args)))) =
      some (true, some (.IData, #[2])) := by
  decide +kernel

theorem idRules_allSound : idRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of
    ⟨⟨Proof.Rules.Rule.checked_of_sound Proof.Rules.r_generic_982_sound rfl, trivial⟩, trivial⟩
    trivial

/-- **Pass execution witness** for a selection of an interface's data word
(`generic.rules:982`): on `unbox`, the checked rewrite pass returns the data word itself
(`v4 = IData v2`), and the result refines the input (`checkedRewrite_refines`). -/
theorem idsel_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet idRules) idPassEnv idFunc = .ok out ∧
      (out.func.value? 4).map (fun v => (v.op, v.args)) = some (.IData, #[2]) ∧
      check idCheckEnv idFunc = .ok () ∧
      check { tabs := out.tables, typs := slTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre idPassEnv.tables idPassEnv.frontend idFunc)
      out.tables out.func idPassEnv.tables idFunc := by
  obtain ⟨h1, h2⟩ := id_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet idRules) idPassEnv idFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h3⟩ := h2
    exact ⟨out, rfl, h3, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := idRules) (penv := idPassEnv)
        (f := idFunc) (out := out) idRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

end GoFV.Proof.Witness
