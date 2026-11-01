import GoFV.Proof.Witness.LoadFwd
import GoFV.Proof.Rules.StructLoad

/-!
# Witness function for struct-load expansions: `loadField` (hand-written, issue #151)

```go
type P struct{ a, b int }

func loadField(p *P) int {
	s := *p
	return s.a
}
```

as the SSA `opt` sees it (one block: `v3 = Load <P> v2 v1`, `v4 = StructSelect [0] v3`), and the
one-rule set `{generic.rules:974}` (as a struct-load expansion, `RuleSet.structLoads`):
`(Load <t> _ _) && t.IsStruct() && … => rewriteStructLoad(v)`. `checkedRewrite` fires the rule
(`v3` becomes `StructMake` of `Load <int> (OffPtr [0] v2) v1` and `Load <int> (OffPtr [8] v2)
v1`) and the validator accepts the event (`RewriteCheck.structLoadOK`).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `abiInfo` of `loadField`: one pointer register parameter, one integer result. -/
def lfABI : CallABI :=
  { abi := 1, nin := 1, nout := 1, spillOff := 8, spillSize := 8, inRegs := 1, outRegs := 1,
    params := #[{ out := false, index := 0, type := 3, name := some 3, regs := #[0], offset := 0 },
                { out := true, index := 0, type := 2, name := some 4, regs := #[0],
                  offset := -1 }] }

def lfField (name : String) (off : Int) : SSA.Field :=
  { name := GoStr.ofString name, type := 2, offset := some off, embedded := false }

/-- The definition tables: `P` (type 4) is `struct { a, b int }`, `*int` (type 5) exists. -/
def lfTabs : Tables where
  types :=
    let t := Array.replicate 36 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(*P) int" (.func 0 1 1 #[])))
    let t := t.set! 2 (some (mkT .INT (some 8) "int"))
    let t := t.set! 3 (some (mkT .PTR (some 8) "*P" (.elem 4)))
    let t := t.set! 4 (some (mkT .STRUCT (some 16) "P" (.struct #[lfField "a" 0, lfField "b" 8])))
    let t := t.set! 5 (some (mkT .PTR (some 8) "*int" (.elem 2)))
    let t := t.set! 29 (some (mkT .SSA none "mem"))
    let t := t.set! 31 (some (mkT .SSA none "void"))
    t.set! 35 (some (mkT .RESULTS none "int,mem" (.results #[2, 29])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.loadField}", kind := .call (some 2) (some lfABI) },
    some { fmt := GoStr.ofString "main.loadField",
           kind := .sym (GoStr.ofString "main.loadField") 1 "" 0 default none none none #[] none },
    some (paramNameT "p" .PPARAM 3 0),
    some (paramNameT "~r0" .PPARAMOUT 2 0)]

/-- `loadField`, the input of `opt`. -/
def lfFunc : Func where
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
    some (mkVi 4 .StructSelect 2 0 p0 1 #[3] 1),
    some (mkVi 5 .MakeResult 35 0 p0 1 #[4, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The one-rule set `{generic.rules:974}`, as a struct-load expansion. -/
def lfRules : RuleSet where
  name := "generic"
  values := []
  blocks := []
  structLoads := [Generated.Generic.r_generic_974]

def lfPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "loadField", typs := slTyps, tables := lfTabs }

def lfCheckEnv : CheckEnv := { tabs := lfTabs, typs := slTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result in which
the `Load` `v3` is a `StructMake` of two fields, which passes `check`. -/
theorem lf_checks :
    (check lfCheckEnv lfFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet lfRules) lfPassEnv lfFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := slTyps } o.func).toBool,
        (o.func.value? 3).map fun v => (v.op, v.args.size))) =
      some (true, some (.StructMake, 2)) := by
  decide +kernel

/-- The one-rule set is sound (no value or block rules; its struct-load expansion is validated
per instance). -/
theorem lfRules_allSound : lfRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of trivial trivial

/-- **Pass execution witness** for `generic.rules:974`: on `loadField`, the checked rewrite pass
expands the struct `Load` `v3` into a `StructMake` of its two field `Load`s, and the result
refines the input (`checkedRewrite_refines`, through `SLFacts.step`). -/
theorem lf_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet lfRules) lfPassEnv lfFunc = .ok out ∧
      (out.func.value? 3).map (fun v => (v.op, v.args.size)) = some (.StructMake, 2) ∧
      check lfCheckEnv lfFunc = .ok () ∧
      check { tabs := out.tables, typs := slTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre lfPassEnv.tables lfFunc) out.tables out.func lfPassEnv.tables lfFunc := by
  obtain ⟨h1, h2⟩ := lf_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet lfRules) lfPassEnv lfFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h3⟩ := h2
    exact ⟨out, rfl, h3, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := lfRules) (penv := lfPassEnv)
        (f := lfFunc) (out := out) lfRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

end GoFV.Proof.Witness
