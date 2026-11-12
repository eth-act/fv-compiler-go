import GoFV.Proof.Witness.FwdZeroLoad

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for a `Load` through a disjoint `Store` to a `Zero` (`generic.rules:842`, issue #69)

```go
func zeroStoreLoad(p *[2]int, x int) int {
	*p = [2]int{} // v4 = Zero {[2]int} [16] v2 v1
	p[0] = x      // v5 = Store {int} v2 v3 v4
	return p[1]   // v7 = Load <int> (v6 = OffPtr [8] v2) v5
}
```

as one block (`zlTabs`). The checked rewrite pass with `{:842}` (a forwarding, `RuleSet.loads`)
builds `Load <int> (OffPtr [8] v2) v4` in the `Zero`'s block and makes `v7` a `Copy` of it: the
validator reads the Load's bytes through the `Store` at offset 0, disjoint from the read at
offset 8 (`RewriteCheck.fwdSepOK`, `sepChain`), and the fresh `OffPtr` is the Load's pointer
(`LoadFwd.sep_den`).
-/

namespace GoFV.Proof.Witness.FwdZeroStore

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `zeroStoreLoad`, the input of `opt`. -/
def zsFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 8
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[8] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 1 #[] 1),
    some (mkV 2 .Arg 3 (some 3) p0 3 #[] 1),
    some (mkV 3 .Arg 2 (some 4) p0 1 #[] 1),
    some { mkV 4 .Zero 29 (some 7) p0 1 #[2, 1] 1 with auxInt := 16 },
    some (mkV 5 .Store 29 (some 6) p0 2 #[2, 3, 4] 1),
    some (mkVi 6 .OffPtr 3 8 p0 1 #[2] 1),
    some (mkVi 7 .Load 2 0 p0 1 #[6, 5] 1),
    some (mkVi 8 .MakeResult 35 0 p0 1 #[7, 5] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The rule set `{generic.rules:842}`, as a forwarding. -/
def zsRules : RuleSet where
  name := "generic"
  values := []
  blocks := []
  loads := [Generated.Generic.r_generic_842]

theorem zsRules_allSound : zsRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of trivial trivial

def zsPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "zeroStoreLoad", typs := slTyps, tables := zlTabs }

def zsCheckEnv : CheckEnv := { tabs := zlTabs, typs := slTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result whose
`MakeResult` reads the fresh `Load` `v9` of `OffPtr [8] p` (`v10`) in the `Zero`'s memory `v4`,
which passes `check`. -/
theorem zs_checks :
    (check zsCheckEnv zsFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet zsRules) zsPassEnv zsFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := slTyps } o.func).toBool,
        (o.func.value? 8).map (·.args),
        (o.func.value? 9).map (·.args) == some #[10, 4] &&
        (o.func.value? 10).any (fun v => v.op == .OffPtr && v.auxInt == 8 && v.args == #[2]))) =
      some (true, some #[9, 5], true) := by
  decide +kernel

/-- **Pass execution witness** for `generic.rules:842`: on `zeroStoreLoad`, the checked rewrite
pass reads `p[1]` in the memory of the `Zero`, before the `Store` to `p[0]` (`v8 = MakeResult v9
v5`, `v9 = Load (OffPtr [8] v2) v4`), and the result refines the input under `RwPre`
(`checkedRewrite_refines`, through `LoadFwd.fwd_refines`, `move_den`'s `fwdSepOK` case). -/
theorem zs_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet zsRules) zsPassEnv zsFunc = .ok out ∧
      (out.func.value? 8).map (·.args) = some #[9, 5] ∧
      check zsCheckEnv zsFunc = .ok () ∧
      check { tabs := out.tables, typs := slTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre zsPassEnv.tables zsPassEnv.frontend zsFunc)
        out.tables out.func zsPassEnv.tables zsFunc := by
  obtain ⟨h1, h2⟩ := zs_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet zsRules) zsPassEnv zsFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h8, -⟩ := h2
    exact ⟨out, rfl, h8, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := zsRules) (penv := zsPassEnv)
        (f := zsFunc) (out := out) zsRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

/-- **Non-vacuity of `zs_checkedRewrite`'s precondition**: `RwPre` holds on `Env.p1` for a pointer
and an integer argument from an empty memory. -/
theorem zs_rwPre :
    GoFV.Proof.Pass.Rewrite.RwPre zsPassEnv.tables zsPassEnv.frontend zsFunc Env.p1
      [.ptr ⟨.heap 0, 0⟩, .i64 0] {} :=
  GoFV.Proof.Pass.Rewrite.RwPre.p1 (by decide +kernel) (by decide +kernel)
    (GoFV.Proof.Pass.Rewrite.initAvoids_empty (fun v hv _ _ => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with rfl | rfl
      · intro h; cases h
      · trivial) rfl (fun _ h => nomatch h))

end GoFV.Proof.Witness.FwdZeroStore
