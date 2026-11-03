import GoFV.Proof.Witness.FwdFixed

/-!
# Witness function for a fixed load through an interface's itab word (issue #69)

```go
func itabEntry(t *int) *[2]int {
	// v4 = Addr {main..dict.f} SB, v5 = IMake v4 t: an interface whose itab word is &main..dict.f
	// v8 = Load <*[2]int> (OffPtr [8] (ITab v5)) mem  (generic.rules:2257: isFixedLoad)
}
```

as one block (`ffFunc` with the pointer `OffPtr [8] (ITab (IMake (Addr {main..dict.f} SB) t))`).
The checked rewrite pass with `{:2257}` turns the `Load` into `Addr {main.T} SB`: `ptrBase` follows
the `ITab` of the `IMake` to the `Addr` (`RewriteCheck.wordStep?`; the itab word is the `Addr`'s
word retyped as the interface's first field and then as a pointer, `LoadFwd.wordStep_den`).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `ffTabs` with `interface {}` as type 7. -/
def fiTabs : Tables where
  types := ffTabs.types.set! 7 (some (mkT .INTER (some 16) "interface {}"))
  auxes := ffTabs.auxes

/-- `itabEntry`, the input of `opt`. -/
def fiFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 9
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[9] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8, 9])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 2 #[] 1),
    some (mkV 2 .Arg 3 (some 3) p0 1 #[] 1),
    some (mkV 3 .SB 15 none p0 1 #[] 1),
    some (mkV 4 .Addr 3 (some 9) p0 1 #[3] 1),
    some (mkVi 5 .IMake 7 0 p0 1 #[4, 2] 1),
    some (mkVi 6 .ITab 3 0 p0 1 #[5] 1),
    some (mkVi 7 .OffPtr 3 8 p0 1 #[6] 1),
    some (mkV 8 .Load 5 none p0 1 #[7, 1] 1),
    some (mkVi 9 .MakeResult 35 0 p0 1 #[8, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The rule set `{generic.rules:2257}`, as a forwarding. -/
def fiRules : RuleSet where
  name := "generic"
  values := []
  blocks := []
  loads := [Generated.Generic.r_generic_2257]

theorem fiRules_allSound : fiRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of trivial trivial

def fiPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "itabEntry", typs := fnTyps, tables := fiTabs }

def fiCheckEnv : CheckEnv := { tabs := fiTabs, typs := fnTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result, which
passes `check`, where the `Load` `v8` became an `Addr` of the `SB` `v3`. -/
theorem fi_checks :
    (check fiCheckEnv fiFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet fiRules) fiPassEnv fiFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := fnTyps } o.func).toBool,
        (o.func.value? 8).map fun v => (v.op, v.args))) =
      some (true, some (.Addr, #[3])) := by
  decide +kernel

/-- **Pass execution witness** for a fixed load through an itab word (`generic.rules:2257`): on
`itabEntry`, the checked rewrite pass replaces the `Load` by the `Addr` of the relocation target
(`v8 = Addr {main.T} v3`), and the result refines the input (`checkedRewrite_refines`, through
`LoadFwd.fwd_refines` under `RoImage`, `ptrBase_den`'s `wordStep_den`). -/
theorem fi_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet fiRules) fiPassEnv fiFunc = .ok out ∧
      (out.func.value? 8).map (fun v => (v.op, v.args)) = some (.Addr, #[3]) ∧
      check fiCheckEnv fiFunc = .ok () ∧
      check { tabs := out.tables, typs := fnTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre fiPassEnv.tables fiPassEnv.frontend fiFunc)
      out.tables out.func
        fiPassEnv.tables fiFunc := by
  obtain ⟨h1, h2⟩ := fi_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet fiRules) fiPassEnv fiFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h8⟩ := h2
    exact ⟨out, rfl, h8, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := fiRules) (penv := fiPassEnv)
        (f := fiFunc) (out := out) fiRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

end GoFV.Proof.Witness
