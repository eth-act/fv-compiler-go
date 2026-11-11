import GoFV.Proof.Witness.LoadFwd

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for a `Load` of a `Zero` (`generic.rules:882`–`:902`, issue #69)

```go
func zeroLoad(p *[2]int) int {
	*p = [2]int{} // v3 = Zero {[2]int} [16] v2 v1
	return p[1]   // v5 = Load <int> (v4 = OffPtr [8] v2) v3
}
```

as one block (`slTabs`' signature; the parameter `x` is unused). The checked rewrite pass with
`{:902}` (a forwarding, `RuleSet.loads`) turns the `Load` `v5` into `Const64 [0]`: the validator
reads zero bytes at the Load's pointer through its memory (`RewriteCheck.fwdZeroOK`, `zeroChain`:
the `Zero` clears offsets 0 to 16 of `v2`, the read is at offset 8 for 8 bytes), and
`LoadFwd.zeroLd_load` decodes them as the constant.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `slTabs` with `[2]int` as type 7 (aux 7). -/
def zlTabs : Tables where
  types := slTabs.types.set! 7 (some (mkT .ARRAY (some 16) "[2]int" (.array 2 2)))
  auxes := slTabs.auxes.push (some { fmt := GoStr.ofString "[2]int", kind := .type 7 })

/-- `zeroLoad`, the input of `opt`. -/
def zlFunc : Func where
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
    some { mkV 3 .Zero 29 (some 7) p0 2 #[2, 1] 1 with auxInt := 16 },
    some (mkVi 4 .OffPtr 3 8 p0 1 #[2] 1),
    some (mkVi 5 .Load 2 0 p0 1 #[4, 3] 1),
    some (mkVi 6 .MakeResult 35 0 p0 1 #[5, 3] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The rule set `{generic.rules:902}`, as a forwarding. -/
def zlRules : RuleSet where
  name := "generic"
  values := []
  blocks := []
  loads := [Generated.Generic.r_generic_902]

theorem zlRules_allSound : zlRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of trivial trivial

def zlPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "zeroLoad", typs := slTyps, tables := zlTabs }

def zlCheckEnv : CheckEnv := { tabs := zlTabs, typs := slTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result, which
passes `check`, in which the `Load` `v5` is `Const64 [0]`. -/
theorem zl_checks :
    (check zlCheckEnv zlFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet zlRules) zlPassEnv zlFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := slTyps } o.func).toBool,
        (o.func.value? 5).map fun v => (v.op, v.auxInt, v.args))) =
      some (true, some (.Const64, 0, #[])) := by
  decide +kernel

/-- **Pass execution witness** for a `Load` of a `Zero` (`generic.rules:902`): on `zeroLoad` the
checked rewrite pass turns `v5 = Load (OffPtr [8] v2) v3` into `Const64 [0]`, and the result
refines the input under `RwPre` (`checkedRewrite_refines`, through `LoadFwd.fwd_refines`,
`fwd_den`'s `fwdZeroOK` case). -/
theorem zl_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet zlRules) zlPassEnv zlFunc = .ok out ∧
      (out.func.value? 5).map (fun v => (v.op, v.auxInt, v.args)) = some (.Const64, 0, #[]) ∧
      check zlCheckEnv zlFunc = .ok () ∧
      check { tabs := out.tables, typs := slTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre zlPassEnv.tables zlPassEnv.frontend zlFunc)
        out.tables out.func zlPassEnv.tables zlFunc := by
  obtain ⟨h1, h2⟩ := zl_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet zlRules) zlPassEnv zlFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h5⟩ := h2
    exact ⟨out, rfl, h5, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := zlRules) (penv := zlPassEnv)
        (f := zlFunc) (out := out) zlRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

/-- **Non-vacuity of `zl_checkedRewrite`'s precondition**: `RwPre` holds on `Env.p1` for a pointer
and an integer argument from an empty memory. -/
theorem zl_rwPre :
    GoFV.Proof.Pass.Rewrite.RwPre zlPassEnv.tables zlPassEnv.frontend zlFunc Env.p1
      [.ptr ⟨.heap 0, 0⟩, .i64 0] {} :=
  GoFV.Proof.Pass.Rewrite.RwPre.p1 (by decide +kernel) (by decide +kernel)
    (GoFV.Proof.Pass.Rewrite.initAvoids_empty (fun v hv _ _ => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with rfl | rfl
      · intro h; cases h
      · trivial) rfl)

end GoFV.Proof.Witness
