import GoFV.Proof.Witness.FwdDrop

/-!
# Witness function for a chain segment (issue #151)

```go
func zeroPair(p *[2]int, x int) int {
	*p = [2]int{}  // v4 = Zero {[2]int} [16] p mem
	p[0] = x       // v6 = Store {int} (OffPtr [0] p) x v4
	p[1] = x       // v8 = Store {int} (OffPtr [8] p) x v6     (generic.rules:1833)
	return x
}
```

as one block. The checked rewrite pass with `{:1833}` (a segment rule, `RuleSet.segs`) makes the
anchor `v8` store over a fresh `Store` of `p[0]` on the input memory: the `Zero` and the first
`Store` are dropped, as the two stores tile its 16 bytes (`RewriteCheck.chainSeg?`). The segment
layer validates it (`RewriteCheck.segRel`) and `Seg.seg_refines` proves it.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `abiInfo` of `zeroPair`: a pointer and an integer register parameter, one result. -/
def zpABI : CallABI :=
  { abi := 1, nin := 2, nout := 1, spillOff := 8, spillSize := 16, inRegs := 2, outRegs := 1,
    params := #[{ out := false, index := 0, type := 5, name := some 3, regs := #[0], offset := 0 },
                { out := false, index := 1, type := 2, name := some 4, regs := #[1], offset := 8 },
                { out := true, index := 0, type := 2, name := some 5, regs := #[0],
                  offset := -1 }] }

/-- The definition tables: `[2]int` is type 4 (aux 6), `*[2]int` type 5, `int` aux 7. -/
def zpTabs : Tables where
  types :=
    let t := mlTabs.types
    t.set! 1 (some (mkT .FUNC (some 8) "func(*[2]int, int) int" (.func 0 2 1 #[])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.zeroPair}", kind := .call (some 2) (some zpABI) },
    some { fmt := GoStr.ofString "main.zeroPair",
           kind := .sym (GoStr.ofString "main.zeroPair") 1 "" 0 default none none none #[] none },
    some (paramNameT "p" .PPARAM 5 0), some (paramNameT "x" .PPARAM 2 8),
    some (paramNameT "~r0" .PPARAMOUT 2 0),
    some { fmt := GoStr.ofString "[2]int", kind := .type 4 },
    some { fmt := GoStr.ofString "int", kind := .type 2 }]

/-- `zeroPair`, the input of `opt`. -/
def zpFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 9
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[9] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8, 9])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 1 #[] 1),
    some (mkV 2 .Arg 5 (some 3) p0 3 #[] 1),
    some (mkV 3 .Arg 2 (some 4) p0 3 #[] 1),
    some { mkV 4 .Zero 29 (some 6) p0 1 #[2, 1] 1 with auxInt := 16 },
    some (mkVi 5 .OffPtr 3 0 p0 1 #[2] 1),
    some (mkV 6 .Store 29 (some 7) p0 1 #[5, 3, 4] 1),
    some (mkVi 7 .OffPtr 3 8 p0 1 #[2] 1),
    some (mkV 8 .Store 29 (some 7) p0 1 #[7, 3, 6] 1),
    some (mkVi 9 .MakeResult 35 0 p0 1 #[3, 8] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The one-rule set `{generic.rules:1833}`, as a segment rule. -/
def zpRules : RuleSet where
  name := "generic"
  values := []
  blocks := []
  segs := [Generated.Generic.r_generic_1833]

theorem zpRules_allSound : zpRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of trivial trivial

def zpPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "zeroPair", typs := slTyps, tables := zpTabs }

def zpCheckEnv : CheckEnv := { tabs := zpTabs, typs := slTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result, which
passes `check`, whose anchor `v8` stores `p[1]` over a fresh `Store` `v10` of `p[0]` on the input
memory `v1`, with neither the `Zero` nor the first `Store` left in the block. -/
theorem zp_checks :
    (check zpCheckEnv zpFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet zpRules) zpPassEnv zpFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := slTyps } o.func).toBool,
        (o.func.value? 8).map (·.args), (o.func.value? 10).map (·.args),
        ((o.func.block? 1).map fun b => b.values.toList.filter fun x =>
          (o.func.value? x).any fun v => v.op == .Store || v.op == .Zero))) =
      some (true, some #[7, 3, 10], some #[5, 3, 1], some [8, 10]) := by
  decide +kernel

/-- **Pass execution witness** for a chain segment (`generic.rules:1833`): on `zeroPair`, the
checked rewrite pass drops the `Zero` and the first `Store` (`v8 = Store (OffPtr [8] p) x v10`,
`v10 = Store (OffPtr [0] p) x v1`), and the result refines the input (`checkedRewrite_refines`,
through `Seg.seg_refines`). -/
theorem zp_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet zpRules) zpPassEnv zpFunc = .ok out ∧
      (out.func.value? 8).map (·.args) = some #[7, 3, 10] ∧
      check zpCheckEnv zpFunc = .ok () ∧
      check { tabs := out.tables, typs := slTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre zpPassEnv.tables zpPassEnv.frontend zpFunc)
      out.tables out.func
        zpPassEnv.tables zpFunc := by
  obtain ⟨h1, h2⟩ := zp_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet zpRules) zpPassEnv zpFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h8, -⟩ := h2
    exact ⟨out, rfl, h8, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := zpRules) (penv := zpPassEnv)
        (f := zpFunc) (out := out) zpRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

end GoFV.Proof.Witness
