import GoFV.Proof.Witness.FwdCopy

/-!
# Witness function for dropped identity writes (issue #151)

```go
func zeroDrop(p *[2]int) int {
	*(*struct{})(p) = struct{}{} // v4 = Store {struct{}} p (Empty) mem    (generic.rules:1005)
	*p = [2]int{}                // v5 = Zero {[2]int} [16] p v4
	*p = [2]int{}                // v6 = Zero {[2]int} [16] p v5          (:2158)
	p[1] = 0                     // v9 = Store {int} (OffPtr [8] p) 0 v6  (:943)
	return 0
}
```

as one block. The checked rewrite pass with `{:943, :1005, :2158}` (forwardings,
`RuleSet.loads`) turns the three writes into copies of their memories (`RewriteCheck.dropOK`): a
`Store` of a zero-sized type, a `Zero` of an equal `Zero`, and a `Store` of `0` into bytes the
`Zero` cleared (validated in the second forwarding layer, where its memory `v6` is already
`Copy v5`: `zeroChain` reads through the copy); the result's `MakeResult` takes the first
`Zero`'s memory.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `abiInfo` of `zeroDrop`: one pointer register parameter, one result. -/
def zdABI : CallABI :=
  { abi := 1, nin := 1, nout := 1, spillOff := 8, spillSize := 8, inRegs := 1, outRegs := 1,
    params := #[{ out := false, index := 0, type := 5, name := some 3, regs := #[0], offset := 0 },
                { out := true, index := 0, type := 2, name := some 4, regs := #[0],
                  offset := -1 }] }

/-- The definition tables: `[2]int` is type 4 (aux 5), `*[2]int` type 5, `int` aux 6, `struct {}`
type 6 (aux 7). -/
def zdTabs : Tables where
  types :=
    let t := mlTabs.types
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(*[2]int) int" (.func 0 1 1 #[])))
    t.set! 6 (some (mkT .STRUCT (some 0) "struct {}" (.struct #[])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.zeroDrop}", kind := .call (some 2) (some zdABI) },
    some { fmt := GoStr.ofString "main.zeroDrop",
           kind := .sym (GoStr.ofString "main.zeroDrop") 1 "" 0 default none none none #[] none },
    some (paramNameT "p" .PPARAM 5 0),
    some (paramNameT "~r0" .PPARAMOUT 2 0),
    some { fmt := GoStr.ofString "[2]int", kind := .type 4 },
    some { fmt := GoStr.ofString "int", kind := .type 2 },
    some { fmt := GoStr.ofString "struct {}", kind := .type 6 }]

/-- `zeroDrop`, the input of `opt`. -/
def zdFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 10
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[10] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 1 #[] 1),
    some (mkV 2 .Arg 5 (some 3) p0 4 #[] 1),
    some (mkVi 3 .Empty 6 0 p0 1 #[] 1),
    some (mkV 4 .Store 29 (some 7) p0 1 #[2, 3, 1] 1),
    some { mkV 5 .Zero 29 (some 5) p0 1 #[2, 4] 1 with auxInt := 16 },
    some { mkV 6 .Zero 29 (some 5) p0 1 #[2, 5] 1 with auxInt := 16 },
    some (mkVi 7 .OffPtr 3 8 p0 1 #[2] 1),
    some (mkVi 8 .Const64 2 0 p0 2 #[] 1),
    some (mkV 9 .Store 29 (some 6) p0 1 #[7, 8, 6] 1),
    some (mkVi 10 .MakeResult 35 0 p0 1 #[8, 9] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The rule set `{generic.rules:943, :1005, :2158}`, as forwardings. -/
def zdRules : RuleSet where
  name := "generic"
  values := []
  blocks := []
  loads := [Generated.Generic.r_generic_943, Generated.Generic.r_generic_1005,
    Generated.Generic.r_generic_2158]

theorem zdRules_allSound : zdRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of trivial trivial

def zdPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "zeroDrop", typs := slTyps, tables := zdTabs }

def zdCheckEnv : CheckEnv := { tabs := zdTabs, typs := slTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result, which
passes `check`, whose `MakeResult` takes the first `Zero`'s memory `v3`, with no `Store` and one
`Zero` left in the block. -/
theorem zd_checks :
    (check zdCheckEnv zdFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet zdRules) zdPassEnv zdFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := slTyps } o.func).toBool,
        (o.func.value? 10).map (·.args),
        ((o.func.block? 1).map fun b => b.values.toList.filter fun x =>
          (o.func.value? x).any fun v => v.op == .Store || v.op == .Zero))) =
      some (true, some #[8, 5], some [5]) := by
  decide +kernel

/-- **Pass execution witness** for dropped identity writes (`generic.rules:943`, `:1005`,
`:2158`): on `zeroDrop`, the checked rewrite pass returns the memory of the first `Zero`
(`v10 = MakeResult v8 v5`), and the result refines the input (`checkedRewrite_refines`, through
`LoadFwd.fwd_refines`). -/
theorem zd_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet zdRules) zdPassEnv zdFunc = .ok out ∧
      (out.func.value? 10).map (·.args) = some #[8, 5] ∧
      check zdCheckEnv zdFunc = .ok () ∧
      check { tabs := out.tables, typs := slTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre zdPassEnv.tables zdFunc) out.tables out.func
        zdPassEnv.tables zdFunc := by
  obtain ⟨h1, h2⟩ := zd_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet zdRules) zdPassEnv zdFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h7, -⟩ := h2
    exact ⟨out, rfl, h7, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := zdRules) (penv := zdPassEnv)
        (f := zdFunc) (out := out) zdRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

end GoFV.Proof.Witness
