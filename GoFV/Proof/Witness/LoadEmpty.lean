import GoFV.Proof.Witness.LoadFwd
import GoFV.Proof.Rules.ArrayLoad

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for a `Load` of a zero-size type (`generic.rules:1004`, issue #69)

```go
func zeroLoad(p *struct{}, x int) int {
	*p = *p  // v4 = Load <struct {}> v2 v1; v5 = Store {struct {}} v2 v4 v1
	return x
}
```

as one block (`slTabs`' signature with `p` a `*struct {}`). The checked rewrite pass with
`{generic.rules:1004}` (`(Load <t> _ _) && t.Size() == 0 => (Empty)`, a value rule under
`Rule.SoundT`) turns the `Load` `v4` into `Empty`: the validator checks that `t` has the empty
shape (`RewriteCheck.condFrameOK`'s `size0Vars`, `FrameOK`) and that the matched `Load` has its
type's shape (`loadTop`: `loadShape .empty`).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `slTabs` with `struct {}` as type 7 (aux 6), `p` a `*struct {}` (type 3). -/
def leTabs : Tables where
  types := (slTabs.types.set! 3 (some (mkT .PTR (some 8) "*struct {}" (.elem 7)))).set! 7
    (some (mkT .STRUCT (some 0) "struct {}" (.struct #[])))
  auxes := slTabs.auxes.set! 6 (some { fmt := GoStr.ofString "struct {}", kind := .type 7 })

/-- `zeroLoad`, the input of `opt`. -/
def leFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 6
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[6] #[] #[] #[1, 2, 3, 4, 5, 6])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 2 #[] 1),
    some (mkV 2 .Arg 3 (some 3) p0 2 #[] 1),
    some (mkV 3 .Arg 2 (some 4) p0 1 #[] 1),
    some (mkVi 4 .Load 7 0 p0 1 #[2, 1] 1),
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

/-- The one-rule set `{generic.rules:1004}`. -/
def leRules : RuleSet where
  name := "generic"
  values := [(.Load, [Generated.Generic.r_generic_1004])]
  blocks := []

/-- The one-rule set is sound (`r_generic_1004_sound`, `Rule.SoundT`). -/
theorem leRules_allSound : leRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of
    ⟨⟨GoFV.Proof.Rules.Rule.checked_of_soundT GoFV.Proof.Rules.r_generic_1004_sound, trivial⟩,
      trivial⟩
    trivial

def lePassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "zeroLoad", typs := slTyps, tables := leTabs }

def leCheckEnv : CheckEnv := { tabs := leTabs, typs := slTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result, which
passes `check`, in which the `Load` `v4` is `Empty`. -/
theorem le_checks :
    (check leCheckEnv leFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet leRules) lePassEnv leFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := slTyps } o.func).toBool,
        (o.func.value? 4).map fun v => (v.op, v.args))) =
      some (true, some (.Empty, #[])) := by
  decide +kernel

/-- **Pass execution witness** for a `Load` of a zero-size type (`generic.rules:1004`): on
`zeroLoad` the checked rewrite pass turns `v4 = Load <struct {}> v2 v1` into `Empty`, and the
result refines the input under `RwPre` (`checkedRewrite_refines`). -/
theorem le_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet leRules) lePassEnv leFunc = .ok out ∧
      (out.func.value? 4).map (fun v => (v.op, v.args)) = some (.Empty, #[]) ∧
      check leCheckEnv leFunc = .ok () ∧
      check { tabs := out.tables, typs := slTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre lePassEnv.tables lePassEnv.frontend leFunc)
        out.tables out.func lePassEnv.tables leFunc := by
  obtain ⟨h1, h2⟩ := le_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet leRules) lePassEnv leFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h4⟩ := h2
    exact ⟨out, rfl, h4, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := leRules) (penv := lePassEnv)
        (f := leFunc) (out := out) leRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

/-- **Non-vacuity of `le_checkedRewrite`'s precondition**: `RwPre` holds on `Env.p1` for a
pointer and an integer argument from an empty memory. -/
theorem le_rwPre :
    GoFV.Proof.Pass.Rewrite.RwPre lePassEnv.tables lePassEnv.frontend leFunc Env.p1
      [.ptr ⟨.heap 0, 0⟩, .i64 0] {} :=
  GoFV.Proof.Pass.Rewrite.RwPre.p1 (by decide +kernel) (by decide +kernel)
    (GoFV.Proof.Pass.Rewrite.initAvoids_empty (fun v hv _ _ => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with rfl | rfl
      · intro h; cases h
      · trivial) rfl)

end GoFV.Proof.Witness
