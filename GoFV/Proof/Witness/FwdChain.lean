import GoFV.Proof.Witness.FwdMalloc

/-!
# Witness function for a chain of writes dropped in one layer (issue #69)

```go
func newArr(t *int) *[2]int {
	p := new([2]int) // v5 = StaticLECall {runtime.mallocgcSmallNoScanSC2} 16 t true mem
	*p = [2]int{}    // v8 = Zero {[2]int} [16] (SelectN [0] v5) (SelectN [1] v5)  (generic.rules:1352)
	p[1] = 0         // v11 = Store {int} (OffPtr [8] (SelectN [0] v5)) 0 v8     (:1362)
	p[0] = 0         // v13 = Store {int} (SelectN [0] v5) 0 v11                 (:1357)
	return p
}
```

as one block. The checked rewrite pass with `{:1352, :1357, :1362}` drops all three writes: the
first forwarding layer the `Zero` (the only one valid in its input), the second both `Store`s,
each rewritten to `Copy v7` (copy elimination ran on the rule's memory argument). `v13`'s memory
argument `v11` is a `Store` in that layer's input, so its `Copy v7` is reached only through the
layer's output, where `v11` is `Copy v7` (`RewriteCheck.memCopyReach`, `memReach`).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `newArr` with a third write, the input of `opt`. -/
def fzFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 13
  bidLast := 1
  blocks := #[1]
  blockTab := #[none,
    some (mkB 1 .Ret p0 #[12] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 12])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 1 #[] 1),
    some (mkV 2 .Arg 3 (some 3) p0 1 #[] 1),
    some (mkVi 3 .Const64 2 16 p0 1 #[] 1),
    some (mkVi 4 .ConstBool 6 1 p0 1 #[] 1),
    some (mkV 5 .StaticLECall 35 (some 5) p0 2 #[3, 2, 4, 1] 1),
    some (mkVi 6 .SelectN 5 0 p0 4 #[5] 1),
    some (mkVi 7 .SelectN 29 1 p0 1 #[5] 1),
    some { mkV 8 .Zero 29 (some 7) p0 1 #[6, 7] 1 with auxInt := 16 },
    some (mkVi 9 .OffPtr 3 8 p0 1 #[6] 1),
    some (mkVi 10 .Const64 2 0 p0 2 #[] 1),
    some (mkV 11 .Store 29 (some 8) p0 1 #[9, 10, 8] 1),
    some (mkVi 12 .MakeResult 35 0 p0 1 #[6, 13] 1),
    some (mkV 13 .Store 29 (some 8) p0 1 #[6, 10, 11] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The rule set `{generic.rules:1352, :1357, :1362}`, as forwardings. -/
def fzRules : RuleSet where
  name := "generic"
  values := []
  blocks := []
  loads := [Generated.Generic.r_generic_1357, Generated.Generic.r_generic_1362,
    Generated.Generic.r_generic_1352]

theorem fzRules_allSound : fzRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of trivial trivial

def fzPassEnv : PassEnv := { fmPassEnv with funcName := GoStr.ofString "newArr" }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result, which
passes `check`, whose `MakeResult` takes the call's memory `v7`, with no `Store` or `Zero` left in
the block. -/
theorem fz_checks :
    (check fmCheckEnv fzFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet fzRules) fzPassEnv fzFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := slTyps } o.func).toBool,
        (o.func.value? 12).map (·.args),
        ((o.func.block? 1).map fun b => b.values.toList.filter fun x =>
          (o.func.value? x).any fun v => v.op == .Store || v.op == .Zero))) =
      some (true, some #[6, 7], some []) := by
  decide +kernel

/-- **Pass execution witness** for a chain of writes dropped in one forwarding layer
(`generic.rules:1352`, `:1357`, `:1362`): on `newArr` with three writes, the checked rewrite pass
returns the memory of the allocation (`v12 = MakeResult v6 v7`), and the result refines the input
(`checkedRewrite_refines`, through `LoadFwd.fwd_refines`, `drop_den`'s `memCopyReach` case). -/
theorem fz_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet fzRules) fzPassEnv fzFunc = .ok out ∧
      (out.func.value? 12).map (·.args) = some #[6, 7] ∧
      check fmCheckEnv fzFunc = .ok () ∧
      check { tabs := out.tables, typs := slTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre fzPassEnv.tables fzPassEnv.frontend fzFunc)
      out.tables out.func
        fzPassEnv.tables fzFunc := by
  obtain ⟨h1, h2⟩ := fz_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet fzRules) fzPassEnv fzFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h12, -⟩ := h2
    exact ⟨out, rfl, h12, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := fzRules) (penv := fzPassEnv)
        (f := fzFunc) (out := out) fzRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

end GoFV.Proof.Witness
