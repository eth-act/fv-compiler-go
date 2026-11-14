import GoFV.Proof.Witness.AddrCmp

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for a devirtualised interface call (`generic.rules:1733`, issue #69)

```go
type I interface{ M() int }
type T struct{}

func (T) M() int { return 1 }

func callM() int {
	var i I = T{}
	return i.M() // v4 = InterLECall {AuxCall{nil}} (Addr {main.T.M} SB) mem    (generic.rules:1733)
}
```

as `opt` sees it once the fixed loads have folded the itab's method word to `Addr {main.T.M} SB`
(the receiver, of size zero, passes no argument). The checked rewrite pass with `{:1733}` (a
`loads` rule, `RewriteCheck.dvShapeOK`) turns `v4` into `StaticLECall {AuxCall{main.T.M}} mem`
and redefines the call's shared aux (aux 4) to call `main.T.M`. The dv layer accepts it
(`RewriteCheck.dvRel`: the code pointer is an `Addr` of the global the redefined aux's callee
names, `dvOK`), and the input runs alike in the result's tables (`tabsAgreeDv`: an `InterLECall`
reads its aux only through its call ABI, `callAgree`).
-/

namespace GoFV.Proof.Witness.FwdDevirt

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `abiInfo` of `callM` and of the method `main.T.M`: no parameters, one `int` result. -/
def dvABI (name : Option AuxRef) : CallABI :=
  { abi := 1, nin := 0, nout := 1, spillOff := 0, spillSize := 0, inRegs := 0, outRegs := 1,
    params := #[{ out := true, index := 0, type := 2, name, regs := #[0], offset := -1 }] }

/-- A function symbol. -/
def dvFn (s : String) : AuxDef :=
  { fmt := GoStr.ofString s,
    kind := .sym (GoStr.ofString s) 1 "" 0 default none none none #[] none }

/-- The definition tables: `int` (type 2), `uintptr` (15), `int,mem` (35, the call's and the
result's type); `callM` (aux 2), the method `main.T.M` (aux 3), the interface call's `*AuxCall`
without a callee (aux 4). -/
def dvTabs : Tables where
  types :=
    let t := acTabs.types
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func() int" (.func 0 0 1 #[])))
    t.set! 35 (some (mkT .RESULTS none "int,mem" (.results #[2, 29])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.callM}", kind := .call (some 2) (some (dvABI (some 5))) },
    some (dvFn "main.callM"),
    some (dvFn "main.T.M"),
    some { fmt := GoStr.ofString "AuxCall{nil}", kind := .call none (some (dvABI none)) },
    some (paramNameT "~r0" .PPARAMOUT 2 0)]

/-- `callM`, the input of `opt`. -/
def dvFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 7
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[7] #[] #[] #[1, 2, 3, 4, 5, 6, 7])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 1 #[] 1),
    some (mkV 2 .SB 15 none p0 1 #[] 1),
    some (mkV 3 .Addr 15 (some 3) p0 1 #[2] 1),
    some (mkV 4 .InterLECall 35 (some 4) p0 2 #[3, 1] 1),
    some (mkVi 5 .SelectN 2 0 p0 1 #[4] 1),
    some (mkVi 6 .SelectN 29 1 p0 1 #[4] 1),
    some (mkVi 7 .MakeResult 35 0 p0 1 #[5, 6] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The rule set `{generic.rules:1733}`, as a `loads` rule. -/
def dvRules : RuleSet where
  name := "generic"
  values := []
  blocks := []
  loads := [Generated.Generic.r_generic_1733]

theorem dvRules_allSound : dvRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of trivial trivial

def dvPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "callM", typs := acTyps, tables := dvTabs }

def dvCheckEnv : CheckEnv := { tabs := dvTabs, typs := acTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result, which
passes `check`, in which `v4` is the `StaticLECall` of its memory alone, its aux now calls
`main.T.M`, and the input's tables call nothing through it. -/
theorem dv_checks :
    (check dvCheckEnv dvFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet dvRules) dvPassEnv dvFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := acTyps } o.func).toBool, o.tables.callee? 4)) =
      some (true, some "main.T.M") ∧
    (checkedRewrite (Interp.Table.ofRuleSet dvRules) dvPassEnv dvFunc).toOption.map
      (fun o => (o.func.value? 4).map (fun v => (v.op, v.aux, v.args))) =
      some (some (.StaticLECall, some 4, #[1])) ∧
    dvTabs.callee? 4 = none := by
  decide +kernel

/-- **Pass execution witness** for a devirtualised interface call (`generic.rules:1733`): on
`callM`, the checked rewrite pass turns the interface call into the static call of `main.T.M`,
and the result refines the input (`checkedRewrite_refines`, through `Devirt.dv_refines` and
`refinesFrom_of_tabsAgreeDv`). -/
theorem dv_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet dvRules) dvPassEnv dvFunc = .ok out ∧
      (out.func.value? 4).map (fun v => (v.op, v.aux, v.args)) =
        some (.StaticLECall, some 4, #[1]) ∧
      out.tables.callee? 4 = some "main.T.M" ∧
      check dvCheckEnv dvFunc = .ok () ∧
      check { tabs := out.tables, typs := acTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre dvPassEnv.tables dvPassEnv.frontend dvFunc)
        out.tables out.func dvPassEnv.tables dvFunc := by
  obtain ⟨h1, h2, h3, -⟩ := dv_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet dvRules) dvPassEnv dvFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2 h3
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2 h3
    obtain ⟨hg, hcal⟩ := h2
    exact ⟨out, rfl, h3, hcal, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := dvRules) (penv := dvPassEnv)
        (f := dvFunc) (out := out) dvRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

/-- **Non-vacuity of `dv_checkedRewrite`'s precondition**: `RwPre` holds on `Env.p1` for no
arguments from an empty memory. -/
theorem dv_rwPre :
    GoFV.Proof.Pass.Rewrite.RwPre dvPassEnv.tables dvPassEnv.frontend dvFunc Env.p1 [] {} :=
  GoFV.Proof.Pass.Rewrite.RwPre.p1 (by decide +kernel) (by decide +kernel)
    (GoFV.Proof.Pass.Rewrite.initAvoids_empty (fun _ hv => by simp at hv) rfl
      (fun _ h => nomatch h))

end GoFV.Proof.Witness.FwdDevirt
