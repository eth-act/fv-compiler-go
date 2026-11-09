import GoFV.Proof.Witness.StructLoad
import GoFV.Proof.Rules.DecLoad

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for the dec `Load` splits: `strLen` (hand-written, issue #17)

```go
func strLen(p *string) int {
	return len(*p)
}
```

as decompose builtin sees it (one block: `v3 = Load <string> v2 v1`, `v4 = StringLen v3`), and
the one-rule set `{dec.rules:45}`: `(Load <t> ptr mem) && t.IsString() => (StringMake (Load
<typ.BytePtr> ptr mem) (Load <typ.Int> (OffPtr <typ.IntPtr> [config.PtrSize] ptr) mem))`
(`r_dec_45_sound`). `checkedRewrite` fires the rule (`v3` becomes a `StringMake` of two `Load`s),
the validator accepts the event (`ruleOK`) and the result refines the input.

`lc_checkedRewrite`: the same for `dec.rules:16` (`r_dec_16_sound`) on
`func realOf(p *complex64) float32 { return real(*p) }`: the `complex64` `Load` becomes a
`ComplexMake` of the `Load`s of its two `float32` halves.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `abiInfo` of `strLen`: one pointer register parameter, one integer result. -/
def lsABI : CallABI :=
  { abi := 1, nin := 1, nout := 1, spillOff := 8, spillSize := 8, inRegs := 1, outRegs := 1,
    params := #[{ out := false, index := 0, type := 3, name := some 3, regs := #[0], offset := 0 },
                { out := true, index := 0, type := 2, name := some 4, regs := #[0],
                  offset := -1 }] }

/-- The definition tables: `*string` (3), `string` (4), `*int` (5), `uint8` (6), `*uint8` (7). -/
def lsTabs : Tables where
  types :=
    let t := Array.replicate 36 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(*string) int" (.func 0 1 1 #[])))
    let t := t.set! 2 (some (mkT .INT (some 8) "int"))
    let t := t.set! 3 (some (mkT .PTR (some 8) "*string" (.elem 4)))
    let t := t.set! 4 (some (mkT .STRING (some 16) "string"))
    let t := t.set! 5 (some (mkT .PTR (some 8) "*int" (.elem 2)))
    let t := t.set! 6 (some (mkT .UINT8 (some 1) "uint8"))
    let t := t.set! 7 (some (mkT .PTR (some 8) "*uint8" (.elem 6)))
    let t := t.set! 29 (some (mkT .SSA none "mem"))
    let t := t.set! 31 (some (mkT .SSA none "void"))
    t.set! 35 (some (mkT .RESULTS none "int,mem" (.results #[2, 29])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.strLen}", kind := .call (some 2) (some lsABI) },
    some { fmt := GoStr.ofString "main.strLen",
           kind := .sym (GoStr.ofString "main.strLen") 1 "" 0 default none none none #[] none },
    some (paramNameT "p" .PPARAM 3 0),
    some (paramNameT "~r0" .PPARAMOUT 2 0)]

/-- `strLen`, the input of the rewrite step. -/
def lsFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 5
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[5] #[] #[] #[1, 2, 3, 4, 5])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 2 #[] 1),
    some (mkV 2 .Arg 3 (some 3) p0 1 #[] 1),
    some (mkVi 3 .Load 4 0 p0 1 #[2, 1] 1),
    some (mkVi 4 .StringLen 2 0 p0 1 #[3] 1),
    some (mkVi 5 .MakeResult 35 0 p0 1 #[4, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The one-rule set `{dec.rules:45}`. -/
def lsRules : RuleSet where
  name := "dec"
  values := [(.Load, [Generated.Dec.r_dec_45])]
  blocks := []

def lsTyps : Array (String × TypeRef) :=
  #[("Int", 2), ("IntPtr", 5), ("BytePtr", 7), ("Mem", 29), ("Void", 31)]

def lsPassEnv : PassEnv :=
  { azPassEnv with
    passName := "decompose builtin"
    funcName := GoStr.ofString "strLen"
    typs := lsTyps
    tables := lsTabs }

def lsCheckEnv : CheckEnv := { tabs := lsTabs, typs := lsTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result in which
the `Load` `v3` is a `StringMake` of two values, which passes `check`. -/
theorem ls_checks :
    (check lsCheckEnv lsFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet lsRules) lsPassEnv lsFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := lsTyps } o.func).toBool,
        (o.func.value? 3).map fun v => (v.op, v.args.size))) =
      some (true, some (.StringMake, 2)) := by
  decide +kernel

/-- The one-rule set is sound (`r_dec_45_sound`). -/
theorem lsRules_allSound : lsRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of
    ⟨⟨GoFV.Proof.Rules.Rule.checked_of_sound GoFV.Proof.Rules.r_dec_45_sound rfl, trivial⟩,
      trivial⟩ trivial

/-- **Pass execution witness** for `dec.rules:45`: on `strLen`, the checked rewrite pass splits
the string `Load` `v3` into a `StringMake` of its pointer and length `Load`s, and the result
refines the input (`checkedRewrite_refines`, through `r_dec_45_sound`). -/
theorem ls_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet lsRules) lsPassEnv lsFunc = .ok out ∧
      (out.func.value? 3).map (fun v => (v.op, v.args.size)) = some (.StringMake, 2) ∧
      check lsCheckEnv lsFunc = .ok () ∧
      check { tabs := out.tables, typs := lsTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre lsPassEnv.tables lsPassEnv.frontend lsFunc)
      out.tables out.func lsPassEnv.tables lsFunc := by
  obtain ⟨h1, h2⟩ := ls_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet lsRules) lsPassEnv lsFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h3⟩ := h2
    exact ⟨out, rfl, h3, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := lsRules) (penv := lsPassEnv)
        (f := lsFunc) (out := out) lsRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

/-- `abiInfo` of `realOf`: one pointer register parameter, one `float32` result. -/
def lcABI : CallABI :=
  { abi := 1, nin := 1, nout := 1, spillOff := 8, spillSize := 8, inRegs := 1, outRegs := 1,
    params := #[{ out := false, index := 0, type := 3, name := some 3, regs := #[0], offset := 0 },
                { out := true, index := 0, type := 2, name := some 4, regs := #[16],
                  offset := -1 }] }

/-- The definition tables: `float32` (2), `*complex64` (3), `complex64` (4), `*float32` (5). -/
def lcTabs : Tables where
  types :=
    let t := Array.replicate 36 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(*complex64) float32" (.func 0 1 1 #[])))
    let t := t.set! 2 (some (mkT .FLOAT32 (some 4) "float32"))
    let t := t.set! 3 (some (mkT .PTR (some 8) "*complex64" (.elem 4)))
    let t := t.set! 4 (some (mkT .COMPLEX64 (some 8) "complex64"))
    let t := t.set! 5 (some (mkT .PTR (some 8) "*float32" (.elem 2)))
    let t := t.set! 29 (some (mkT .SSA none "mem"))
    let t := t.set! 31 (some (mkT .SSA none "void"))
    t.set! 35 (some (mkT .RESULTS none "float32,mem" (.results #[2, 29])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.realOf}", kind := .call (some 2) (some lcABI) },
    some { fmt := GoStr.ofString "main.realOf",
           kind := .sym (GoStr.ofString "main.realOf") 1 "" 0 default none none none #[] none },
    some (paramNameT "p" .PPARAM 3 0),
    some (paramNameT "~r0" .PPARAMOUT 2 0)]

/-- `realOf`, the input of the rewrite step. -/
def lcFunc : Func :=
  { lsFunc with
    valueTab := #[none,
      some (mkVi 1 .InitMem 29 0 p0 2 #[] 1),
      some (mkV 2 .Arg 3 (some 3) p0 1 #[] 1),
      some (mkVi 3 .Load 4 0 p0 1 #[2, 1] 1),
      some (mkVi 4 .ComplexReal 2 0 p0 1 #[3] 1),
      some (mkVi 5 .MakeResult 35 0 p0 1 #[4, 1] 1)] }

/-- The one-rule set `{dec.rules:16}`. -/
def lcRules : RuleSet where
  name := "dec"
  values := [(.Load, [Generated.Dec.r_dec_16])]
  blocks := []

def lcTyps : Array (String × TypeRef) :=
  #[("Float32", 2), ("Float32Ptr", 5), ("Mem", 29), ("Void", 31)]

def lcPassEnv : PassEnv :=
  { lsPassEnv with funcName := GoStr.ofString "realOf", typs := lcTyps, tables := lcTabs }

def lcCheckEnv : CheckEnv := { tabs := lcTabs, typs := lcTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result in which
the `Load` `v3` is a `ComplexMake` of two values, which passes `check`. -/
theorem lc_checks :
    (check lcCheckEnv lcFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet lcRules) lcPassEnv lcFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := lcTyps } o.func).toBool,
        (o.func.value? 3).map fun v => (v.op, v.args.size))) =
      some (true, some (.ComplexMake, 2)) := by
  decide +kernel

/-- The one-rule set is sound (`r_dec_16_sound`). -/
theorem lcRules_allSound : lcRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of
    ⟨⟨GoFV.Proof.Rules.Rule.checked_of_sound GoFV.Proof.Rules.r_dec_16_sound rfl, trivial⟩,
      trivial⟩ trivial

/-- **Pass execution witness** for `dec.rules:16`: on `realOf`, the checked rewrite pass splits
the `complex64` `Load` `v3` into a `ComplexMake` of its halves' `Load`s, and the result refines
the input (`checkedRewrite_refines`, through `r_dec_16_sound`). -/
theorem lc_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet lcRules) lcPassEnv lcFunc = .ok out ∧
      (out.func.value? 3).map (fun v => (v.op, v.args.size)) = some (.ComplexMake, 2) ∧
      check lcCheckEnv lcFunc = .ok () ∧
      check { tabs := out.tables, typs := lcTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre lcPassEnv.tables lcPassEnv.frontend lcFunc)
      out.tables out.func lcPassEnv.tables lcFunc := by
  obtain ⟨h1, h2⟩ := lc_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet lcRules) lcPassEnv lcFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h3⟩ := h2
    exact ⟨out, rfl, h3, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := lcRules) (penv := lcPassEnv)
        (f := lcFunc) (out := out) lcRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

end GoFV.Proof.Witness
