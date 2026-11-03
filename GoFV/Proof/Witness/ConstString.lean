import GoFV.Proof.Witness.AddZero
import GoFV.Proof.Pass.Rewrite
import GoFV.Proof.Rules.ConstString

/-!
# Witness function for frame-value rules: `hi` (hand-written, issue #151)

```go
func hi() string {
	return "hi"
}
```

as the SSA `opt` sees it (one block, the string result in two integer registers), and the
one-rule set `{generic.rules:1022}`: `(ConstString {str}) && str != "" => (StringMake (Addr
<typ.BytePtr> {fe.StringData(str)} (SB)) (Const64 <typ.Int> [int64(len(str))]))`. `checkedRewrite`
fires the rule: `v2` becomes `StringMake` of a new `Addr` of the string's data symbol, which
`fe.StringData` appends to the tables (aux 5), and a `Const64 [2]`. The validator accepts the log
in the extended tables (the built `Addr` names the string's data symbol, its `Const64` the
string's length: `FrameOK`), and the input cannot tell them from its own (`tabsAgree`).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `abiInfo` of `hi`: no parameters, a string result in two integer registers. -/
def hiABI : CallABI :=
  { abi := 1, nin := 0, nout := 1, spillOff := 0, spillSize := 0, inRegs := 0, outRegs := 2,
    params := #[{ out := true, index := 0, type := 5, name := some 3, regs := #[0, 1],
                  offset := -1 }] }

/-- The definition tables: the string constant `"hi"` (aux 4) names its data symbol. -/
def hiTabs : Tables where
  types :=
    let t := Array.replicate 36 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func() string" (.func 0 0 1 #[])))
    let t := t.set! 2 (some (mkT .UINT8 (some 1) "uint8"))
    let t := t.set! 3 (some (mkT .PTR (some 8) "*uint8" (.elem 2)))
    let t := t.set! 4 (some (mkT .UINTPTR (some 8) "uintptr"))
    let t := t.set! 5 (some { mkT .STRING (some 16) "string" with align := some 8 })
    let t := t.set! 6 (some (mkT .INT (some 8) "int"))
    let t := t.set! 29 (some (mkT .SSA none "mem"))
    let t := t.set! 31 (some (mkT .SSA none "void"))
    t.set! 35 (some (mkT .RESULTS none "string,mem" (.results #[5, 29])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.hi}", kind := .call (some 2) (some hiABI) },
    some { fmt := GoStr.ofString "main.hi",
           kind := .sym (GoStr.ofString "main.hi") 1 "" 0 default none none none #[] none },
    some (paramNameT "~r0" .PPARAMOUT 5 0),
    some { fmt := GoStr.ofString "\"hi\"",
           kind := .str (GoStr.ofString "hi") (GoStr.ofString "go:string.\"hi\"") }]

/-- `hi`, the input of `opt`. -/
def hiFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 3
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[3] #[] #[] #[1, 2, 3])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 1 #[] 1),
    some (mkV 2 .ConstString 5 (some 4) p0 1 #[] 1),
    some (mkVi 3 .MakeResult 35 0 p0 1 #[2, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The one-rule set `{generic.rules:1022}`. -/
def hiRules : RuleSet where
  name := "generic"
  values := [(.ConstString, [Generated.Generic.r_generic_1022])]
  blocks := []

def hiTyps : Array (String × TypeRef) :=
  #[("BytePtr", 3), ("Uintptr", 4), ("Int", 6), ("Mem", 29), ("Void", 31)]

/-- The pass environment of `opt` (`azPassEnv`'s configuration). -/
def hiPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "hi", typs := hiTyps, tables := hiTabs }

def hiCheckEnv : CheckEnv := { tabs := hiTabs, typs := hiTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` turns `v2` into a
`StringMake`, appends one aux (`go:string."hi"`), and its result passes `check` in the result's
tables. -/
theorem hi_checks :
    (check hiCheckEnv hiFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet hiRules) hiPassEnv hiFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := hiTyps } o.func).toBool,
        (o.func.value? 2).map (·.op), o.tables.auxes.size)) =
      some (true, some .StringMake, 6) := by
  decide +kernel

/-- The one-rule set is sound (`r_generic_1022_sound`, `Rule.SoundT`). -/
theorem hiRules_allSound : hiRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of
    ⟨⟨GoFV.Proof.Rules.Rule.checked_of_soundT GoFV.Proof.Rules.r_generic_1022_sound, trivial⟩,
      trivial⟩
    trivial

/-- By kernel evaluation: the rewrite of `hi` logs no phi elimination. -/
private theorem hi_noPhi : ∀ r, rewriteRun (Interp.Table.ofRuleSet hiRules) true true
    hiPassEnv hiFunc = .ok r → RewriteCheck.noPhiElim r.2.2 = true := by
  intro r hr
  have h : (rewriteRun (Interp.Table.ofRuleSet hiRules) true true hiPassEnv hiFunc).toOption.map
      (fun r => RewriteCheck.noPhiElim r.2.2) = some true := by decide +kernel
  rw [hr] at h
  simpa [Except.toOption] using h

/-- **Pass execution witness**: on `hi`, the checked rewrite pass with `{generic.rules:1022}`
rewrites the constant string (`v2 = StringMake …`) in tables extended by its data symbol, the
validator accepted the result against the input and the log, and the result refines the input
(`checkedRewrite_refines`). -/
theorem hi_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet hiRules) hiPassEnv hiFunc = .ok out ∧
      (out.func.value? 2).map (·.op) = some .StringMake ∧ out.tables.auxes.size = 6 ∧
      tabsAgree hiPassEnv.tables out.tables hiFunc = true ∧
      (∃ log, RewriteCheck.validate out.tables (Interp.Table.ofRuleSet hiRules) hiFunc out.func
        log = true) ∧
      check hiCheckEnv hiFunc = .ok () ∧ check { tabs := out.tables, typs := hiTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre hiPassEnv.tables hiPassEnv.frontend hiFunc)
      out.tables out.func hiPassEnv.tables hiFunc := by
  obtain ⟨h1, h2⟩ := hi_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet hiRules) hiPassEnv hiFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h5, hn⟩ := h2
    rcases GoFV.Proof.Pass.Rewrite.checkedRewrite_cases_noNil rfl rfl rfl rfl rfl rfl
        (by decide +kernel) hi_noPhi hc
      with ⟨he, -⟩ | ⟨ht, hv⟩
    · rw [he] at h5; exact absurd h5 (by decide +kernel)
    · exact ⟨out, rfl, h5, hn, ht, hv, ok_of_toBool h1, ok_of_toBool hg,
        GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := hiRules) (penv := hiPassEnv)
          (f := hiFunc) (out := out) hiRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

end GoFV.Proof.Witness
