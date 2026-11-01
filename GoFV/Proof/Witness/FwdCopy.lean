import GoFV.Proof.Witness.LoadFwd

/-!
# Witness functions for forwarding through copies, constant `PtrIndex`es and constants (issue #151)

```go
func storeLoadCopy(p *int, x int) int {
	y := x // a Copy the rewrite pass's copy elimination looks through
	*p = y
	return *p
}

func storeLoadIdx(p *int, x int, y *int) int {
	*(*int)(unsafe.Add(p, 0*8)) = x  // PtrIndex <*int> p [0]
	*(**int)(unsafe.Add(p, 1*8)) = y // PtrIndex <**int> p [1]
	return *(*int)(unsafe.Add(p, 0*8))
}
```

as one block each. In `storeLoadCopy` the `Store` writes `Copy x`; copy elimination replaces that
argument by `x` before `generic.rules:800` matches, so the forwarding's value `x` is reached from
the stored value through a copy (`RewriteCheck.storedOK`). In `storeLoadIdx` the second `Store`
(`:806` reads through it; Go's `disjoint` by `disjointTypes`: an `int` and a `*int`) is at
`PtrIndex p (Const64 [1])` and the read at `PtrIndex p (Const64 [0])`: `ptrBase` takes both to the
base `p` at offsets 0 and 8 (`constIdx?`), which `disjointB` separates.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `storeLoadCopy`, the input of `opt` (`storeLoad`'s tables). -/
def fcFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 7
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[7] #[] #[] #[1, 2, 3, 4, 5, 6, 7])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 1 #[] 1),
    some (mkV 2 .Arg 3 (some 3) p0 2 #[] 1),
    some (mkV 3 .Arg 2 (some 4) p0 1 #[] 1),
    some (mkVi 4 .Copy 2 0 p0 1 #[3] 1),
    some (mkV 5 .Store 29 (some 6) p0 2 #[2, 4, 1] 1),
    some (mkVi 6 .Load 2 0 p0 1 #[2, 5] 1),
    some (mkVi 7 .MakeResult 35 0 p0 1 #[6, 5] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- By kernel evaluation: the `Store`'s value reaches `x` through the copy, the input passes
`check`, and `checkedRewrite` keeps a result whose `MakeResult` reads `x` (`v3`) instead of the
Load, which passes `check`. -/
theorem fc_checks :
    RewriteCheck.storedOK slTabs fcFunc (.int .w64) 4 3 = true ∧
    (check slCheckEnv fcFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet slRules) slPassEnv fcFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := slTyps } o.func).toBool,
        (o.func.value? 7).map (·.args))) =
      some (true, some #[3, 5]) := by
  decide +kernel

/-- **Pass execution witness** for forwarding through a copy: on `storeLoadCopy`, the checked
rewrite pass forwards `x` (`v7 = MakeResult v3 v5`), and the result refines the input
(`checkedRewrite_refines`, through `LoadFwd.fwd_refines`). -/
theorem fc_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet slRules) slPassEnv fcFunc = .ok out ∧
      (out.func.value? 7).map (·.args) = some #[3, 5] ∧
      check slCheckEnv fcFunc = .ok () ∧
      check { tabs := out.tables, typs := slTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre slPassEnv.tables fcFunc) out.tables out.func
        slPassEnv.tables fcFunc := by
  obtain ⟨-, h1, h2⟩ := fc_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet slRules) slPassEnv fcFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h7⟩ := h2
    exact ⟨out, rfl, h7, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := slRules) (penv := slPassEnv)
        (f := fcFunc) (out := out) slRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

/-- `abiInfo` of `storeLoadIdx`: three register parameters (`p *int`, `x int`, `y *int`). -/
def piABI : CallABI :=
  { abi := 1, nin := 3, nout := 1, spillOff := 8, spillSize := 24, inRegs := 3, outRegs := 1,
    params := #[{ out := false, index := 0, type := 3, name := some 3, regs := #[0], offset := 0 },
                { out := false, index := 1, type := 2, name := some 4, regs := #[1], offset := 8 },
                { out := false, index := 2, type := 3, name := some 7, regs := #[2], offset := 16 },
                { out := true, index := 0, type := 2, name := some 5, regs := #[0],
                  offset := -1 }] }

/-- The definition tables: `*int` has pointers (`disjointTypes`), `**int` is type 4,
`Store {*int}` names its type by aux 8. -/
def piTabs : Tables where
  types :=
    let t := sl2Tabs.types
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(*int, int, *int) int" (.func 0 3 1 #[])))
    let t := t.set! 3 (some { mkT .PTR (some 8) "*int" (.elem 2) with flags := { hasptr := true } })
    t.set! 4 (some { mkT .PTR (some 8) "**int" (.elem 3) with flags := { hasptr := true } })
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.storeLoadIdx}", kind := .call (some 2) (some piABI) },
    some { fmt := GoStr.ofString "main.storeLoadIdx",
           kind := .sym (GoStr.ofString "main.storeLoadIdx") 1 "" 0 default none none none #[] none },
    some (paramNameT "p" .PPARAM 3 0), some (paramNameT "x" .PPARAM 2 8),
    some (paramNameT "~r0" .PPARAMOUT 2 0),
    some { fmt := GoStr.ofString "int", kind := .type 2 },
    some (paramNameT "y" .PPARAM 3 16),
    some { fmt := GoStr.ofString "*int", kind := .type 3 }]

/-- `storeLoadIdx`, the input of `opt`. -/
def piFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 12
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[12] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 1 #[] 1),
    some (mkV 2 .Arg 3 (some 3) p0 2 #[] 1),
    some (mkV 3 .Arg 2 (some 4) p0 1 #[] 1),
    some (mkV 4 .Arg 3 (some 7) p0 1 #[] 1),
    some (mkVi 5 .Const64 2 0 p0 1 #[] 1),
    some (mkVi 6 .Const64 2 1 p0 1 #[] 1),
    some (mkVi 7 .PtrIndex 3 0 p0 2 #[2, 5] 1),
    some (mkVi 8 .PtrIndex 4 0 p0 1 #[2, 6] 1),
    some (mkV 9 .Store 29 (some 6) p0 1 #[7, 3, 1] 1),
    some (mkV 10 .Store 29 (some 8) p0 2 #[8, 4, 9] 1),
    some (mkVi 11 .Load 2 0 p0 1 #[7, 10] 1),
    some (mkVi 12 .MakeResult 35 0 p0 1 #[11, 10] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

def piPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "storeLoadIdx", typs := slTyps, tables := piTabs }

def piCheckEnv : CheckEnv := { tabs := piTabs, typs := slTyps }

/-- By kernel evaluation: `ptrBase` takes both `PtrIndex`es to `p`, at offsets 0 and 8, so the
second `Store` is disjoint from the read; the input passes `check`, and `checkedRewrite` keeps a
result whose `MakeResult` reads `x` (`v3`) instead of the Load, which passes `check`. -/
theorem pi_checks :
    RewriteCheck.ptrBase piTabs piFunc 8 7 = (2, 0) ∧
    RewriteCheck.ptrBase piTabs piFunc 8 8 = (2, 8) ∧
    (check piCheckEnv piFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet sl2Rules) piPassEnv piFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := slTyps } o.func).toBool,
        (o.func.value? 12).map (·.args))) =
      some (true, some #[3, 10]) := by
  decide +kernel

/-- **Pass execution witness** for constant `PtrIndex` offsets: on `storeLoadIdx`, the checked
rewrite pass forwards `x` through the `Store` at index 1 (`v12 = MakeResult v3 v10`), and the
result refines the input (`checkedRewrite_refines`, through `LoadFwd.fwd_refines`). -/
theorem pi_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet sl2Rules) piPassEnv piFunc = .ok out ∧
      (out.func.value? 12).map (·.args) = some #[3, 10] ∧
      check piCheckEnv piFunc = .ok () ∧
      check { tabs := out.tables, typs := slTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre piPassEnv.tables piFunc) out.tables out.func
        piPassEnv.tables piFunc := by
  obtain ⟨-, -, h1, h2⟩ := pi_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet sl2Rules) piPassEnv piFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h12⟩ := h2
    exact ⟨out, rfl, h12, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := sl2Rules) (penv := piPassEnv)
        (f := piFunc) (out := out) sl2Rules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

/-! ## A float read back from an integer constant: `storeLoadF` (`generic.rules:830`)

```go
func storeLoadF(p *int) float64 {
	*p = 0x3ff8000000000000 // the bits of 1.5
	return *(*float64)(unsafe.Pointer(p))
}
```

as one block: `v4 = Store {int} v2 (Const64 [bits]) v1`, `v5 = Load <float64> v2 v4`. The rule
makes `v5` the constant `Const64F [1.5]`, which has the stored bits
(`RewriteCheck.fwdConstOK`). -/

/-- `abiInfo` of `storeLoadF`: one pointer register parameter, one result. -/
def cfABI : CallABI :=
  { abi := 1, nin := 1, nout := 1, spillOff := 8, spillSize := 8, inRegs := 1, outRegs := 1,
    params := #[{ out := false, index := 0, type := 3, name := some 3, regs := #[0], offset := 0 },
                { out := true, index := 0, type := 4, name := some 5, regs := #[0],
                  offset := -1 }] }

/-- The definition tables: `float64` is type 4, `Store {int}` names its type by aux 6. -/
def cfTabs : Tables where
  types :=
    let t := slTabs.types
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(*int) float64" (.func 0 1 1 #[])))
    let t := t.set! 4 (some (mkT .FLOAT64 (some 8) "float64"))
    t.set! 35 (some (mkT .RESULTS none "float64,mem" (.results #[4, 29])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.storeLoadF}", kind := .call (some 2) (some cfABI) },
    some { fmt := GoStr.ofString "main.storeLoadF",
           kind := .sym (GoStr.ofString "main.storeLoadF") 1 "" 0 default none none none #[] none },
    some (paramNameT "p" .PPARAM 3 0), none,
    some (paramNameT "~r0" .PPARAMOUT 4 0),
    some { fmt := GoStr.ofString "int", kind := .type 2 }]

/-- `storeLoadF`, the input of `opt`. -/
def cfFunc : Func where
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
    some (mkVi 3 .Const64 2 4609434218613702656 p0 1 #[] 1),
    some (mkV 4 .Store 29 (some 6) p0 2 #[2, 3, 1] 1),
    some (mkVi 5 .Load 4 0 p0 1 #[2, 4] 1),
    some (mkVi 6 .MakeResult 35 0 p0 1 #[5, 4] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The one-rule set `{generic.rules:830}`, as a forwarding. -/
def cfRules : RuleSet where
  name := "generic"
  values := []
  blocks := []
  loads := [Generated.Generic.r_generic_830]

theorem cfRules_allSound : cfRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of trivial trivial

def cfPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "storeLoadF", typs := slTyps, tables := cfTabs }

def cfCheckEnv : CheckEnv := { tabs := cfTabs, typs := slTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result in which
the Load `v5` is `Const64F` of the stored bits, which passes `check`. -/
theorem cf_checks :
    (check cfCheckEnv cfFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet cfRules) cfPassEnv cfFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := slTyps } o.func).toBool,
        (o.func.value? 5).map fun v => (v.op, v.auxInt))) =
      some (true, some (.Const64F, 4609434218613702656)) := by
  decide +kernel

/-- **Pass execution witness** for `generic.rules:830`: on `storeLoadF`, the checked rewrite pass
replaces the float Load by the constant `Const64F` of the stored bits, and the result refines the
input (`checkedRewrite_refines`, through `LoadFwd.fwd_refines`). -/
theorem cf_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet cfRules) cfPassEnv cfFunc = .ok out ∧
      (out.func.value? 5).map (fun v => (v.op, v.auxInt)) = some (.Const64F, 4609434218613702656) ∧
      check cfCheckEnv cfFunc = .ok () ∧
      check { tabs := out.tables, typs := slTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre cfPassEnv.tables cfFunc) out.tables out.func
        cfPassEnv.tables cfFunc := by
  obtain ⟨h1, h2⟩ := cf_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet cfRules) cfPassEnv cfFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h5⟩ := h2
    exact ⟨out, rfl, h5, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := cfRules) (penv := cfPassEnv)
        (f := cfFunc) (out := out) cfRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

end GoFV.Proof.Witness
