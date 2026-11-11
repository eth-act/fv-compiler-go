import GoFV.Proof.Witness.FwdMalloc

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for the length of a `growslice` result (`generic.rules:2128`, issue #69)

```go
func grow(p, t *int) int {
	s := growslice(p, 3, 0, 3, t) // v7 = StaticLECall {runtime.growslice} v2 v3 v4 v3 v6 v1
	return len(s)                 // v10 = SliceLen (SelectN [0] v7)
}
```

as one block (the parameter `t` stands in for the type descriptor argument; the call is the
expansion of `append` to an empty slice). The checked rewrite pass with `{:2128}` (a
forwarding, `RuleSet.loads`) turns the length `v10` into a copy of the call's length argument
`v3`: the validator relates `SliceLen (SelectN [0] c)` to `c`'s second argument
(`RewriteCheck.growOK`), which `runtime.growslice` returns as the slice's length
(`Sem.Env.GrowLen`; `Env.runtime_growLen` for the runtime model's contract). The result's
`MakeResult` takes `v3`.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `abiInfo` of `grow`: two pointer register parameters, one integer result. -/
def grABI : CallABI :=
  { abi := 1, nin := 2, nout := 1, spillOff := 8, spillSize := 16, inRegs := 2, outRegs := 1,
    params := #[{ out := false, index := 0, type := 3, name := some 3, regs := #[0], offset := 0 },
                { out := false, index := 1, type := 3, name := some 4, regs := #[1], offset := 8 },
                { out := true, index := 0, type := 2, name := some 5, regs := #[0],
                  offset := -1 }] }

/-- `abiInfo` of `runtime.growslice`: the old pointer, the new length, the old capacity, the
number of added elements and the type descriptor in registers, one slice result. -/
def grGrowABI : CallABI :=
  { abi := 1, nin := 5, nout := 1, spillOff := 8, spillSize := 40, inRegs := 5, outRegs := 3,
    params := #[{ out := false, index := 0, type := 3, name := none, regs := #[0], offset := 0 },
                { out := false, index := 1, type := 2, name := none, regs := #[1], offset := 8 },
                { out := false, index := 2, type := 2, name := none, regs := #[2], offset := 16 },
                { out := false, index := 3, type := 2, name := none, regs := #[3], offset := 24 },
                { out := false, index := 4, type := 3, name := none, regs := #[4], offset := 32 },
                { out := true, index := 0, type := 7, name := none, regs := #[0, 1, 2],
                  offset := -1 }] }

/-- The definition tables: `[]int` is type 7, `[]int,mem` (type 34) the type of the call,
`int,mem` (type 35) that of the result. -/
def grTabs : Tables where
  types :=
    let t := slTabs.types
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(*int, *int) int" (.func 0 2 1 #[])))
    let t := t.set! 7 (some (mkT .SLICE (some 24) "[]int" (.elem 2)))
    t.set! 34 (some (mkT .RESULTS none "[]int,mem" (.results #[7, 29])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.grow}", kind := .call (some 2) (some grABI) },
    some { fmt := GoStr.ofString "main.grow",
           kind := .sym (GoStr.ofString "main.grow") 1 "" 0 default none none none #[] none },
    some (paramNameT "p" .PPARAM 3 0),
    some (paramNameT "t" .PPARAM 3 8),
    some (paramNameT "~r0" .PPARAMOUT 2 0),
    some { fmt := GoStr.ofString "AuxCall{runtime.growslice}",
           kind := .call (some 7) (some grGrowABI) },
    some { fmt := GoStr.ofString "runtime.growslice",
           kind := .sym (GoStr.ofString "runtime.growslice") 1 "" 0 default none none none #[]
             none }]

/-- `grow`, the input of `opt`. -/
def grFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 11
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[11] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 1 #[] 1),
    some (mkV 2 .Arg 3 (some 3) p0 1 #[] 1),
    some (mkVi 3 .Const64 2 3 p0 2 #[] 1),
    some (mkVi 4 .Const64 2 0 p0 1 #[] 1),
    some (mkVi 5 .Const64 2 1 p0 0 #[] 1),
    some (mkV 6 .Arg 3 (some 4) p0 1 #[] 1),
    some (mkV 7 .StaticLECall 34 (some 6) p0 2 #[2, 3, 4, 3, 6, 1] 1),
    some (mkVi 8 .SelectN 7 0 p0 1 #[7] 1),
    some (mkVi 9 .SelectN 29 1 p0 1 #[7] 1),
    some (mkVi 10 .SliceLen 2 0 p0 1 #[8] 1),
    some (mkVi 11 .MakeResult 35 0 p0 1 #[10, 9] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The rule set `{generic.rules:2128}`, as a forwarding. -/
def grRules : RuleSet where
  name := "generic"
  values := []
  blocks := []
  loads := [Generated.Generic.r_generic_2128]

theorem grRules_allSound : grRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of trivial trivial

def grPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "grow", typs := slTyps, tables := grTabs }

def grCheckEnv : CheckEnv := { tabs := grTabs, typs := slTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result, which
passes `check`, whose `MakeResult` takes the length argument `v3`. -/
theorem gr_checks :
    (check grCheckEnv grFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet grRules) grPassEnv grFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := slTyps } o.func).toBool,
        (o.func.value? 11).map (·.args))) =
      some (true, some #[3, 9]) := by
  decide +kernel

/-- **Pass execution witness** for the length of a `growslice` result (`generic.rules:2128`): on
`grow`, the checked rewrite pass returns the length argument (`v11 = MakeResult v3 v9`), and the
result refines the input under `RwPre` (`checkedRewrite_refines`, through `LoadFwd.fwd_refines`
under `Env.GrowLen`). -/
theorem gr_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet grRules) grPassEnv grFunc = .ok out ∧
      (out.func.value? 11).map (·.args) = some #[3, 9] ∧
      check grCheckEnv grFunc = .ok () ∧
      check { tabs := out.tables, typs := slTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre grPassEnv.tables grPassEnv.frontend grFunc)
        out.tables out.func grPassEnv.tables grFunc := by
  obtain ⟨h1, h2⟩ := gr_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet grRules) grPassEnv grFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h11⟩ := h2
    exact ⟨out, rfl, h11, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := grRules) (penv := grPassEnv)
        (f := grFunc) (out := out) grRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

/-- **Non-vacuity of `gr_checkedRewrite`'s precondition**: `RwPre` holds on `Env.p1` (which has
no `growslice` contract) for pointer arguments from an empty memory; `Env.GrowLen` also holds of
the runtime model (`Env.runtime_growLen`). -/
theorem gr_rwPre :
    GoFV.Proof.Pass.Rewrite.RwPre grPassEnv.tables grPassEnv.frontend grFunc Env.p1
      [.ptr ⟨.heap 0, 0⟩, .ptr ⟨.heap 1, 0⟩] {} ∧ Env.runtime.GrowLen :=
  ⟨GoFV.Proof.Pass.Rewrite.RwPre.p1 (by decide +kernel) (by decide +kernel)
    (GoFV.Proof.Pass.Rewrite.initAvoids_empty (fun v hv _ _ => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with rfl | rfl <;> intro h <;> cases h) rfl (fun _ h => nomatch h)),
    Env.runtime_growLen⟩

end GoFV.Proof.Witness
