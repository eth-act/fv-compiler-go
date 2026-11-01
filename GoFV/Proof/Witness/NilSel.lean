import GoFV.Proof.Witness.NilGetG
import GoFV.Proof.Witness.ConstString
import GoFV.Proof.Rules.DecMakeSel

/-!
# Witness functions for the `StringPtr`/`StructSelect` seeds of `safePtr` (hand-written, issue #151)

```go
func strData() *byte {
	s := "hi"
	p := unsafe.StringData(s)
	_ = *p // nil check
	return p
}

type S struct{ p *g }

func selG() *g {
	s := S{getg()}
	p := s.p
	_ = *p // nil check
	return p
}
```

as the SSA `opt` sees them. In `strData` the nil check's pointer is `StringPtr` of the constant
`"hi"`; the rule set `{generic.rules:1022, :1011, :1375}` turns the constant into a `StringMake` of
an `Addr` (`:1022`), the `StringPtr` into that `Addr` (`:1011`) and drops the nil check of the
`Addr` (`:1375`). In `selG` the pointer is `StructSelect [0]` of a `StructMake` of `GetG`; the rule
set `{generic.rules:973, :1062}` turns the selection into `Copy` of the `GetG` (`:973`) and drops
the nil check of `GetG` (`:1062`). In both, the nil-check layer runs on the input, where the
pointer is the `StringPtr`/`StructSelect`: `NilCheck.safePtr` accepts it only through the
`nonEmptyStr`/`ptrField` seeds.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `abiInfo` of `strData`: no parameters, one pointer result. -/
def nsABI : CallABI :=
  { abi := 1, nin := 0, nout := 1, spillOff := 0, spillSize := 0, inRegs := 0, outRegs := 1,
    params := #[{ out := true, index := 0, type := 3, name := some 3, regs := #[0],
                  offset := -1 }] }

/-- `hiTabs` with a `func() *uint8` signature: the string constant `"hi"` is aux 4. -/
def nsTabs : Tables where
  types :=
    let t := hiTabs.types
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func() *uint8" (.func 0 0 1 #[])))
    t.set! 35 (some (mkT .RESULTS none "*uint8,mem" (.results #[3, 29])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.strData}", kind := .call (some 2) (some nsABI) },
    some { fmt := GoStr.ofString "main.strData",
           kind := .sym (GoStr.ofString "main.strData") 1 "" 0 default none none none #[] none },
    some (paramNameT "~r0" .PPARAMOUT 3 0),
    some { fmt := GoStr.ofString "\"hi\"",
           kind := .str (GoStr.ofString "hi") (GoStr.ofString "go:string.\"hi\"") }]

/-- `strData`, the input of `opt`. -/
def nsFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 5
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[5] #[] #[] #[1, 2, 3, 4, 5])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 2 #[] 1),
    some (mkV 2 .ConstString 5 (some 4) p0 1 #[] 1),
    some (mkVi 3 .StringPtr 3 0 p0 1 #[2] 1),
    some (mkVi 4 .NilCheck 3 0 p0 1 #[3, 1] 1),
    some (mkVi 5 .MakeResult 35 0 p0 1 #[4, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- `{generic.rules:1022, :1011}` and the nil-check elimination `:1375`. -/
def nsRules : RuleSet where
  name := "generic"
  values := [(.ConstString, [Generated.Generic.r_generic_1022]),
    (.StringPtr, [Generated.Generic.r_generic_1011])]
  blocks := []
  nilChecks := [Generated.Generic.r_generic_1375]

def nsPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "strData", typs := hiTyps, tables := nsTabs }

def nsCheckEnv : CheckEnv := { tabs := nsTabs, typs := hiTyps }

/-- By kernel evaluation: `safePtr` takes the `StringPtr` of `"hi"` as non-nil, the input passes
`check`, and `checkedRewrite` keeps a result whose `MakeResult` returns the `StringPtr` (now the
`Addr` of the string's data) instead of the nil check, which passes `check`. -/
theorem ns_checks :
    NilCheck.safePtr true nsTabs nsFunc nsFunc.valueTab.size 3 = true ∧
    (check nsCheckEnv nsFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet nsRules) nsPassEnv nsFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := hiTyps } o.func).toBool,
        (o.func.value? 5).map (·.args), (o.func.value? 3).map (·.op))) =
      some (true, some #[3, 1], some .Addr) := by
  decide +kernel

theorem nsRules_allSound : nsRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of
    ⟨⟨.inl GoFV.Proof.Rules.r_generic_1022_sound, trivial⟩,
      ⟨.inl GoFV.Proof.Rules.r_generic_1011_sound, trivial⟩, trivial⟩ trivial

/-- **Pass execution witness** for the `StringPtr` seed: on `strData`, the checked rewrite pass
removes the nil check of the string constant's data pointer (`v5 = MakeResult v3 v1`), and the
result refines the input (`checkedRewrite_refines`, through `Nil.refinesFrom_of_rel` with the
`nonEmptyStr` seed of `safePtr`). -/
theorem ns_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet nsRules) nsPassEnv nsFunc = .ok out ∧
      (out.func.value? 5).map (·.args) = some #[3, 1] ∧
      check nsCheckEnv nsFunc = .ok () ∧
      check { tabs := out.tables, typs := hiTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre nsPassEnv.tables nsFunc) out.tables out.func
        nsPassEnv.tables nsFunc := by
  obtain ⟨-, h1, h2⟩ := ns_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet nsRules) nsPassEnv nsFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h4, -⟩ := h2
    exact ⟨out, rfl, h4, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := nsRules) (penv := nsPassEnv)
        (f := nsFunc) (out := out) nsRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

/-- `ggTabs` with `S` (type 4) = `struct { p *int }`. -/
def smTabs : Tables where
  types := ggTabs.types.set! 4 (some (mkT .STRUCT (some 8) "S"
    (.struct #[{ name := GoStr.ofString "p", type := 3, offset := some 0, embedded := false }])))
  auxes := ggTabs.auxes

/-- `selG`, the input of `opt`. -/
def smFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 6
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[6] #[] #[] #[1, 2, 3, 4, 5, 6])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 3 #[] 1),
    some (mkVi 2 .GetG 3 0 p0 1 #[1] 1),
    some (mkVi 3 .StructMake 4 0 p0 1 #[2] 1),
    some (mkVi 4 .StructSelect 3 0 p0 1 #[3] 1),
    some (mkVi 5 .NilCheck 3 0 p0 1 #[4, 1] 1),
    some (mkVi 6 .MakeResult 35 0 p0 1 #[5, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- `{generic.rules:973}` and the nil-check elimination `:1062`. -/
def smRules : RuleSet where
  name := "generic"
  values := [(.StructSelect, [Generated.Generic.r_generic_973])]
  blocks := []
  nilChecks := [Generated.Generic.r_generic_1062]

def smPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "selG", typs := slTyps, tables := smTabs }

def smCheckEnv : CheckEnv := { tabs := smTabs, typs := slTyps }

/-- By kernel evaluation: `safePtr` takes `StructSelect [0]` of the `StructMake` of `GetG` as
non-nil, the input passes `check`, and `checkedRewrite` keeps a result whose `MakeResult` returns
the `GetG`, which passes `check`. -/
theorem sm_checks :
    NilCheck.safePtr true smTabs smFunc smFunc.valueTab.size 4 = true ∧
    (check smCheckEnv smFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet smRules) smPassEnv smFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := slTyps } o.func).toBool,
        (o.func.value? 6).map (·.args))) =
      some (true, some #[2, 1]) := by
  decide +kernel

theorem smRules_allSound : smRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of
    ⟨⟨.inr GoFV.Proof.Rules.r_generic_973_sound, trivial⟩, trivial⟩ trivial

/-- **Pass execution witness** for the `StructSelect` seed: on `selG`, the checked rewrite pass
removes the nil check of the selected field (`v6 = MakeResult v2 v1`), and the result refines
the input (`checkedRewrite_refines`, through `Nil.refinesFrom_of_rel` with the `ptrField` case of
`safePtr`). -/
theorem sm_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet smRules) smPassEnv smFunc = .ok out ∧
      (out.func.value? 6).map (·.args) = some #[2, 1] ∧
      check smCheckEnv smFunc = .ok () ∧
      check { tabs := out.tables, typs := slTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre smPassEnv.tables smFunc) out.tables out.func
        smPassEnv.tables smFunc := by
  obtain ⟨-, h1, h2⟩ := sm_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet smRules) smPassEnv smFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h4⟩ := h2
    exact ⟨out, rfl, h4, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := smRules) (penv := smPassEnv)
        (f := smFunc) (out := out) smRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

end GoFV.Proof.Witness
