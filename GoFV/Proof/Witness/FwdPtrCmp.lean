import GoFV.Proof.Witness.AddrCmp

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for pointer comparisons of frame variables (`generic.rules:1673`, `:1655`, issue #69)

```go
var a int

func ptrCmp() bool {
	var t [2]int // a frame variable (PAUTO)
	return &t[0] != &a || &t[0] == &t[1]
}
```

as opt sees it: `v4 = LocalAddr {t} SP mem`, `v5 = Addr {main.a} SB`, `v6 = NeqPtr v4 v5`
(`:1673`, a frame variable is no global: `true`), `v7 = OffPtr [8] v4`, `v8 = EqPtr v4 v7`
(`:1655`, one variable at offsets 0 and 8: `false`), `v9 = OrB v6 v8` is returned. The rule set
`{:1655, :1673}` (forwardings, `RuleSet.loads`): `checkedRewrite` makes `v6` the constant `true`
and `v8` the constant `false`; the validator tells each comparison (`RewriteCheck.ptrCmp?`: `v4`
and `v5` start the different allocations `baseBlk?` names, `v4` and `v7` share the base `v4` at
offsets 0 and 8), and `LoadFwd.ptrCmp_den` proves it under the forwarding layer's `MemAtoms`.
-/

namespace GoFV.Proof.Witness.FwdPtrCmp

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `acTabs` with `[2]int` (type 21), `*[2]int` (type 22) and the frame variable `t` (aux 6). -/
def pcTabs : Tables where
  types :=
    let t := acTabs.types.set! 21 (some (mkT .ARRAY (some 16) "[2]int" (.array 2 2)))
    t.set! 22 (some (mkT .PTR (some 8) "*[2]int" (.elem 21)))
  auxes := acTabs.auxes.push (some (paramNameT "t" .PAUTO 21 0))

/-- `ptrCmp`, the input of opt. -/
def pcFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 10
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[10] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 2 #[] 1),
    some (mkV 2 .SP 15 none p0 1 #[] 1),
    some (mkV 3 .SB 15 none p0 1 #[] 1),
    some (mkV 4 .LocalAddr 22 (some 6) p0 3 #[2, 1] 1),
    some (mkV 5 .Addr 20 (some 3) p0 1 #[3] 1),
    some (mkVi 6 .NeqPtr 6 0 p0 1 #[4, 5] 1),
    some (mkVi 7 .OffPtr 20 8 p0 1 #[4] 1),
    some (mkVi 8 .EqPtr 6 0 p0 1 #[4, 7] 1),
    some (mkVi 9 .OrB 6 0 p0 1 #[6, 8] 1),
    some (mkVi 10 .MakeResult 35 0 p0 1 #[9, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The rule set `{generic.rules:1655, :1673}`, as forwardings. -/
def pcRules : RuleSet where
  name := "generic"
  values := []
  blocks := []
  loads := [Generated.Generic.r_generic_1655, Generated.Generic.r_generic_1673]

theorem pcRules_allSound : pcRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of trivial trivial

def pcPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "ptrCmp", typs := acTyps, tables := pcTabs }

def pcCheckEnv : CheckEnv := { tabs := pcTabs, typs := acTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result, which
passes `check`, in which `v6` is the constant `true`. -/
theorem pc_checks :
    (check pcCheckEnv pcFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet pcRules) pcPassEnv pcFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := acTyps } o.func).toBool,
        (o.func.value? 6).map (fun v => (v.op, v.auxInt, v.args)))) =
      some (true, some (.ConstBool, 1, #[])) := by
  decide +kernel

/-- By kernel evaluation: in `checkedRewrite`'s result `v8` is the constant `false`. -/
theorem pc_checks8 :
    (checkedRewrite (Interp.Table.ofRuleSet pcRules) pcPassEnv pcFunc).toOption.map
      (fun o => (o.func.value? 8).map (fun v => (v.op, v.auxInt, v.args))) =
      some (some (.ConstBool, 0, #[])) := by
  decide +kernel

/-- **Pass execution witness** for pointer comparisons folded in the forwarding layer
(`RewriteCheck.ptrCmpOK`): on `ptrCmp`, the checked rewrite pass folds `&t[0] != &a` to `true`
and `&t[0] == &t[1]` to `false`, and the result refines the input under `RwPre`
(`checkedRewrite_refines`, through `LoadFwd.fwd_refines`, `fwd_den`'s `ptrCmpOK` case). -/
theorem pc_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet pcRules) pcPassEnv pcFunc = .ok out ∧
      (out.func.value? 6).map (fun v => (v.op, v.auxInt, v.args)) = some (.ConstBool, 1, #[]) ∧
      (out.func.value? 8).map (fun v => (v.op, v.auxInt, v.args)) = some (.ConstBool, 0, #[]) ∧
      check pcCheckEnv pcFunc = .ok () ∧
      check { tabs := out.tables, typs := acTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre pcPassEnv.tables pcPassEnv.frontend pcFunc)
        out.tables out.func pcPassEnv.tables pcFunc := by
  obtain ⟨h1, h2⟩ := pc_checks
  have h3 := pc_checks8
  cases hc : checkedRewrite (Interp.Table.ofRuleSet pcRules) pcPassEnv pcFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2 h3
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2 h3
    obtain ⟨hg, h6⟩ := h2
    have h8 := h3
    exact ⟨out, rfl, h6, h8, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := pcRules) (penv := pcPassEnv)
        (f := pcFunc) (out := out) pcRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

/-- **Non-vacuity of `pc_checkedRewrite`'s precondition**: `RwPre` holds on `Env.p1` for no
arguments from an empty memory. -/
theorem pc_rwPre :
    GoFV.Proof.Pass.Rewrite.RwPre pcPassEnv.tables pcPassEnv.frontend pcFunc Env.p1 [] {} :=
  GoFV.Proof.Pass.Rewrite.RwPre.p1 (by decide +kernel) (by decide +kernel)
    (GoFV.Proof.Pass.Rewrite.initAvoids_empty (fun v hv _ _ => by simp at hv) rfl
      (fun _ h => nomatch h))

end GoFV.Proof.Witness.FwdPtrCmp
