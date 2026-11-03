import GoFV.Proof.Witness.FwdChain

/-!
# Witness function for a dropped write of a zero composite (issue #69)

```go
func newStr(t *int) *string {
	p := new(string) // v5 = StaticLECall {runtime.mallocgcSmallNoScanSC2} 16 t true mem
	*p = ""          // v8 = Zero {string} [16] (SelectN [0] v5) (SelectN [1] v5)       (generic.rules:1352)
	*p = ""          // v13 = Store {string} (SelectN [0] v5) (StringMake (ConstNil) 0) v8   (:1357)
	return p
}
```

as one block (the call's type and result are `newArr`'s). The checked rewrite pass with
`{:1352, :1357, :1362}` drops both writes: the stored `StringMake (ConstNil) (Const64 [0])` is the
empty string, a composite of zero words (`RewriteCheck.zeroVal`). The unused `v14 = StringLen
(StringMake t (Const64 [0]))` is a zero term only through its selection (`zeroAt`'s selection and
make cases; it is no constant term).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `fmTabs` with `string` as type 7 (aux 9). -/
def zsTabs : Tables where
  types := fmTabs.types.set! 7 (some (mkT .STRING (some 16) "string"))
  auxes := fmTabs.auxes.push (some { fmt := GoStr.ofString "string", kind := .type 7 })

/-- `newStr`, the input of `opt`. -/
def zsFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 15
  bidLast := 1
  blocks := #[1]
  blockTab := #[none,
    some (mkB 1 .Ret p0 #[12] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 12])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 1 #[] 1),
    some (mkV 2 .Arg 3 (some 3) p0 2 #[] 1),
    some (mkVi 3 .Const64 2 16 p0 1 #[] 1),
    some (mkVi 4 .ConstBool 6 1 p0 1 #[] 1),
    some (mkV 5 .StaticLECall 35 (some 5) p0 2 #[3, 2, 4, 1] 1),
    some (mkVi 6 .SelectN 5 0 p0 3 #[5] 1),
    some (mkVi 7 .SelectN 29 1 p0 1 #[5] 1),
    some { mkV 8 .Zero 29 (some 9) p0 1 #[6, 7] 1 with auxInt := 16 },
    some (mkVi 9 .ConstNil 3 0 p0 1 #[] 1),
    some (mkVi 10 .Const64 2 0 p0 2 #[] 1),
    some (mkVi 11 .StringMake 7 0 p0 1 #[9, 10] 1),
    some (mkVi 12 .MakeResult 35 0 p0 1 #[6, 13] 1),
    some (mkV 13 .Store 29 (some 9) p0 1 #[6, 11, 8] 1),
    some (mkVi 14 .StringLen 2 0 p0 0 #[15] 1),
    some (mkVi 15 .StringMake 7 0 p0 1 #[2, 10] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- `v14 = StringLen (StringMake t (Const64 [0]))` is a zero term (`zeroConst`) that is no
constant term: through the selection of component 1 of the make. -/
example : RewriteCheck.zeroConst zsTabs zsFunc 14 = true ∧
    RewriteCheck.termConst zsTabs zsFunc 4 14 = none := by decide +kernel

def zsPassEnv : PassEnv :=
  { fmPassEnv with funcName := GoStr.ofString "newStr", tables := zsTabs }

def zsCheckEnv : CheckEnv := { tabs := zsTabs, typs := slTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result, which
passes `check`, whose `MakeResult` takes the call's memory `v7`, with no `Store` or `Zero` left in
the block. -/
theorem zs_checks :
    (check zsCheckEnv zsFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet fzRules) zsPassEnv zsFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := slTyps } o.func).toBool,
        (o.func.value? 12).map (·.args),
        ((o.func.block? 1).map fun b => b.values.toList.filter fun x =>
          (o.func.value? x).any fun v => v.op == .Store || v.op == .Zero))) =
      some (true, some #[6, 7], some []) := by
  decide +kernel

/-- **Pass execution witness** for a dropped write of the empty string (`generic.rules:1357`,
`zeroVal` of a composite): on `newStr` the checked rewrite pass returns the memory of the
allocation (`v12 = MakeResult v6 v7`), and the result refines the input (`checkedRewrite_refines`,
through `LoadFwd.fwd_refines`, `drop_den`'s `zeroConst_den`). -/
theorem zs_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet fzRules) zsPassEnv zsFunc = .ok out ∧
      (out.func.value? 12).map (·.args) = some #[6, 7] ∧
      check zsCheckEnv zsFunc = .ok () ∧
      check { tabs := out.tables, typs := slTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre zsPassEnv.tables zsPassEnv.frontend zsFunc)
      out.tables out.func
        zsPassEnv.tables zsFunc := by
  obtain ⟨h1, h2⟩ := zs_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet fzRules) zsPassEnv zsFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h12, -⟩ := h2
    exact ⟨out, rfl, h12, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := fzRules) (penv := zsPassEnv)
        (f := zsFunc) (out := out) fzRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

end GoFV.Proof.Witness
