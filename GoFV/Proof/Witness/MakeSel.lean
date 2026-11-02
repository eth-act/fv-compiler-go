import GoFV.Proof.Witness.StructLoad
import GoFV.Proof.Witness.DecodedLen
import GoFV.Proof.Rules.DecMakeSel

/-!
# Witness function for selections of a variadic `Make`: `pick` (hand-written, issue #17)

```go
type P struct{ a, b int }

func pick(a, b int) int {
	s := P{a, b}
	return s.b
}
```

as the SSA `opt` sees it (one block: `v4 = StructMake <P> v2 v3`, `v5 = StructSelect [1] v4`),
and the one-rule set `{generic.rules:973}`: `(StructSelect [i] x:(StructMake ___)) =>
x.Args[i]` (`Rule.MakeSel`, the same rule as `dec.rules:106`). `checkedRewrite` fires the rule
(`v5` becomes `Copy v3`, so the result returns `b`) and the validator accepts the event
(`RewriteCheck.makeSelOK`).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `abiInfo` of `pick`: two integer register parameters, one integer result. -/
def mksABI : CallABI :=
  { abi := 1, nin := 2, nout := 1, spillOff := 8, spillSize := 16, inRegs := 2, outRegs := 1,
    params := #[{ out := false, index := 0, type := 2, name := some 3, regs := #[0], offset := 0 },
                { out := false, index := 1, type := 2, name := some 4, regs := #[1], offset := 8 },
                { out := true, index := 0, type := 2, name := some 5, regs := #[0],
                  offset := -1 }] }

/-- The definition tables: `P` (type 4) is `struct { a, b int }`. -/
def mksTabs : Tables where
  types :=
    let t := Array.replicate 36 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(int, int) int" (.func 0 2 1 #[])))
    let t := t.set! 2 (some (mkT .INT (some 8) "int"))
    let t := t.set! 4 (some (mkT .STRUCT (some 16) "P" (.struct #[lfField "a" 0, lfField "b" 8])))
    let t := t.set! 29 (some (mkT .SSA none "mem"))
    let t := t.set! 31 (some (mkT .SSA none "void"))
    t.set! 35 (some (mkT .RESULTS none "int,mem" (.results #[2, 29])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.pick}", kind := .call (some 2) (some mksABI) },
    some { fmt := GoStr.ofString "main.pick",
           kind := .sym (GoStr.ofString "main.pick") 1 "" 0 default none none none #[] none },
    some (paramNameT "a" .PPARAM 2 0), some (paramNameT "b" .PPARAM 2 8),
    some (paramNameT "~r0" .PPARAMOUT 2 0)]

/-- `pick`, the input of `opt`. -/
def mksFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 6
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[6] #[] #[] #[1, 2, 3, 4, 5, 6])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 1 #[] 1),
    some (mkV 2 .Arg 2 (some 3) p0 1 #[] 1),
    some (mkV 3 .Arg 2 (some 4) p0 1 #[] 1),
    some (mkVi 4 .StructMake 4 0 p0 1 #[2, 3] 1),
    some (mkVi 5 .StructSelect 2 1 p0 1 #[4] 1),
    some (mkVi 6 .MakeResult 35 0 p0 1 #[5, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The one-rule set `{generic.rules:973}`. -/
def mksRules : RuleSet where
  name := "generic"
  values := [(.StructSelect, [Generated.Generic.r_generic_973])]
  blocks := []

def mksPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "pick", typs := slTyps, tables := mksTabs }

def mksCheckEnv : CheckEnv := { tabs := mksTabs, typs := slTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result whose
`MakeResult` returns `b` (`v3`), which passes `check`. -/
theorem mks_checks :
    (check mksCheckEnv mksFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet mksRules) mksPassEnv mksFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := slTyps } o.func).toBool,
        (o.func.value? 6).map (·.args))) =
      some (true, some #[3, 1]) := by
  decide +kernel

/-- The one-rule set is sound (its rule is validated per instance, `Rule.MakeSel`). -/
theorem mksRules_allSound : mksRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of
    ⟨⟨.inr (.inl GoFV.Proof.Rules.r_generic_973_sound), trivial⟩, trivial⟩ trivial

/-- **Pass execution witness** for `generic.rules:973` (and `dec.rules:106`): on `pick`, the
checked rewrite pass makes the selection a copy of the `StructMake`'s argument, the result returns
`b`, and it refines the input (`checkedRewrite_refines`, through `MSFacts.step`). -/
theorem mks_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet mksRules) mksPassEnv mksFunc = .ok out ∧
      (out.func.value? 6).map (·.args) = some #[3, 1] ∧
      check mksCheckEnv mksFunc = .ok () ∧
      check { tabs := out.tables, typs := slTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre mksPassEnv.tables mksFunc) out.tables out.func mksPassEnv.tables mksFunc := by
  obtain ⟨h1, h2⟩ := mks_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet mksRules) mksPassEnv mksFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h3⟩ := h2
    exact ⟨out, rfl, h3, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := mksRules) (penv := mksPassEnv)
        (f := mksFunc) (out := out) mksRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

/-! ## `(ITab (IMake itab _)) => itab` with a `uintptr` itab (`dec.rules:82`, issue #17) -/

/-- `uintptr` (type 1), `uint8` (2), `*uint8` (3), `interface {}` (4). -/
def itsTabs : Tables where
  types := #[none, some (mkT .UINTPTR (some 8) "uintptr"), some (mkT .UINT8 (some 1) "uint8"),
    some (mkT .PTR (some 8) "*uint8" (.elem 2)), some (mkT .INTER (some 16) "interface {}")]
  auxes := #[]

/-- `v1 = ArgIntReg <uintptr>`, `v2 = ArgIntReg <*uint8>`, `v3 = IMake <interface {}> v1 v2`,
`v4 = ITab <*uint8> v3`; `v5 = Convert <*uint8> v1 v0`, `v6 = IMake v5 v2`, `v7 = ITab <*uint8> v6`. -/
def itsDefs : RewriteCheck.Defs := #[none,
  some (mkVi 1 .ArgIntReg 1 0 p0 1 #[] 1), some (mkVi 2 .ArgIntReg 3 0 p0 1 #[] 1),
  some (mkVi 3 .IMake 4 0 p0 1 #[1, 2] 1), some (mkVi 4 .ITab 3 0 p0 1 #[3] 1),
  some (mkVi 5 .Convert 3 0 p0 1 #[1, 0] 1), some (mkVi 6 .IMake 4 0 p0 1 #[5, 2] 1),
  some (mkVi 7 .ITab 3 0 p0 1 #[6] 1)]

/-- The validator accepts making a pointer-typed `ITab` a `Copy` of its `IMake`'s itab word: a
`uintptr` (`v4` becomes `Copy <uintptr> v1`), and a `Convert <*uint8>` of one (`v7` becomes
`Copy <*uint8> v5`), both only through `RewriteCheck.intWord` (the itab's `uintptr` shape is not
the `ITab`'s pointer shape, and neither itab is an `Addr`). -/
theorem its_makeSelOK :
    RewriteCheck.makeSelOK itsTabs itsDefs 4 [mkVi 4 .Copy 1 0 p0 1 #[1] 1] = true ∧
    RewriteCheck.makeSelOK itsTabs itsDefs 7 [mkVi 7 .Copy 3 0 p0 1 #[5] 1] = true ∧
    GoFV.Proof.Rules.shapeSub (itsTabs.ty 1) (itsTabs.ty 3) = false ∧
    GoFV.Proof.Rules.shapeSub (itsTabs.ty 3) (itsTabs.ty 1) = false := by
  decide +kernel

/-- `itsDefs` as a function (one block, no terminator values): the input of a `Store` split. -/
def itsFunc : Func where
  entry := 1
  type := 0
  ownAux := none
  vidLast := 7
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Exit p0 #[] #[] #[] #[1, 2, 3, 4, 5, 6, 7])]
  valueTab := itsDefs
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The `Store` split of an `IMake` accepts a `*uint8` itab in the interface's `uintptr` field
when it is a `Convert` of a `uintptr` (`v5`), not when it is a pointer-typed atom (`v2`). -/
theorem its_ssFieldOK :
    RewriteCheck.ssFieldOK itsTabs itsFunc 5 (itsTabs.ty 3) (.int .w64) = true ∧
    RewriteCheck.ssFieldOK itsTabs itsFunc 2 (itsTabs.ty 3) (.int .w64) = false := by
  decide +kernel

/-! ## A dropped `(StructMake x) && x.Type.IsPtrShaped() => x` (`dec.rules:120`, issue #17)

```go
type Q struct{ p *int }

func pick1(p *int) *int {
	s := Q{p}
	return s.p
}
```

as one block (`v4 = StructMake <Q> v2`, `v5 = StructSelect <*int> [0] v4`), and the rule set
`{dec.rules:120, dec.rules:115}`. `checkedRewrite` makes `v4` a `Copy v2` (`:120`, a
`Rule.Drop` event the replay skips, keeping the `StructMake`), then `v5`'s argument `v2` (a copy
replacement the replay skips too) and `v5` a `Copy v2` (`:115`, accepted as a selection of the
kept `StructMake`, `makeSelOK`); the result returns `p` and no longer lists `v4` or `v5`. -/

/-- `abiInfo` of `pick1`: one pointer register parameter, one pointer result. -/
def drpABI : CallABI :=
  { abi := 1, nin := 1, nout := 1, spillOff := 8, spillSize := 8, inRegs := 1, outRegs := 1,
    params := #[{ out := false, index := 0, type := 3, name := some 3, regs := #[0], offset := 0 },
                { out := true, index := 0, type := 3, name := some 4, regs := #[0],
                  offset := -1 }] }

/-- The definition tables: `*int` (type 3), `Q` (type 4) is `struct { p *int }`. -/
def drpTabs : Tables where
  types :=
    let t := Array.replicate 36 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(*int) *int" (.func 0 1 1 #[])))
    let t := t.set! 2 (some (mkT .INT (some 8) "int"))
    let t := t.set! 3 (some (mkT .PTR (some 8) "*int" (.elem 2)))
    let t := t.set! 4 (some (mkT .STRUCT (some 8) "Q"
      (.struct #[{ name := GoStr.ofString "p", type := 3, offset := some 0, embedded := false }])))
    let t := t.set! 29 (some (mkT .SSA none "mem"))
    let t := t.set! 31 (some (mkT .SSA none "void"))
    t.set! 35 (some (mkT .RESULTS none "*int,mem" (.results #[3, 29])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.pick1}", kind := .call (some 2) (some drpABI) },
    some { fmt := GoStr.ofString "main.pick1",
           kind := .sym (GoStr.ofString "main.pick1") 1 "" 0 default none none none #[] none },
    some (paramNameT "p" .PPARAM 3 0), some (paramNameT "~r0" .PPARAMOUT 3 0)]

/-- `pick1`. -/
def drpFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 6
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[6] #[] #[] #[1, 2, 4, 5, 6])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 1 #[] 1),
    some (mkV 2 .Arg 3 (some 3) p0 1 #[] 1),
    none,
    some (mkVi 4 .StructMake 4 0 p0 1 #[2] 1),
    some (mkVi 5 .StructSelect 3 0 p0 1 #[4] 1),
    some (mkVi 6 .MakeResult 35 0 p0 1 #[5, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The rule set `{dec.rules:120, dec.rules:115}`. -/
def drpRules : RuleSet where
  name := "dec"
  values := [(.StructMake, [Generated.Dec.r_dec_120]),
    (.StructSelect, [Generated.Dec.r_dec_115])]
  blocks := []

def drpPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "pick1", typs := slTyps, tables := drpTabs }

def drpCheckEnv : CheckEnv := { tabs := drpTabs, typs := slTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result without
the `StructMake` and its selection whose `MakeResult` returns `p` (`v2`), which passes `check`. -/
theorem drp_checks :
    (check drpCheckEnv drpFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet drpRules) drpPassEnv drpFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := slTyps } o.func).toBool,
        (o.func.value? 4).isNone && (o.func.value? 5).isNone, (o.func.value? 6).map (·.args))) =
      some (true, true, some #[2, 1]) := by
  decide +kernel

/-- The rule set is sound (`:120` is `Rule.Drop`, `:115` `Rule.Sound`). -/
theorem drpRules_allSound : drpRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of
    ⟨⟨.inr (.inr (.inr GoFV.Proof.Rules.r_dec_120_sound)), trivial⟩,
      ⟨GoFV.Proof.Rules.Rule.checked_of_sound GoFV.Proof.Rules.r_dec_115_sound rfl, trivial⟩,
      trivial⟩ trivial

/-- **Pass execution witness** for `dec.rules:120` (`Rule.Drop`): on `pick1`, the checked
rewrite pass removes the one-pointer `StructMake` and its selection, the result returns `p`, and
it refines the input (`checkedRewrite_refines`; the replay skips the dropped event and keeps the
`StructMake`, of which it validates the selection, `makeSelOK`). -/
theorem drp_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet drpRules) drpPassEnv drpFunc = .ok out ∧
      ((out.func.value? 4).isNone && (out.func.value? 5).isNone) = true ∧
      (out.func.value? 6).map (·.args) = some #[2, 1] ∧
      check drpCheckEnv drpFunc = .ok () ∧
      check { tabs := out.tables, typs := slTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre drpPassEnv.tables drpFunc) out.tables out.func
        drpPassEnv.tables drpFunc := by
  obtain ⟨h1, h2⟩ := drp_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet drpRules) drpPassEnv drpFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h4, h3⟩ := h2
    exact ⟨out, rfl, h4, h3, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := drpRules) (penv := drpPassEnv)
        (f := drpFunc) (out := out) drpRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

end GoFV.Proof.Witness
