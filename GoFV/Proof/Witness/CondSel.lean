import GoFV.Proof.Witness.StructStore
import GoFV.Proof.Rules.CondSelect

/-!
# Witness function for `CondSelect` tops: `pick` (hand-written, issue #69)

`pick(x, y int) int` after branchelim selected its result by a condition that later became the
constant `true`, as late opt sees it (one block: `v4 = ConstBool [true]`,
`v5 = CondSelect <int> v2 v3 v4`), and the one-rule set `{generic.rules:292}`:
`(CondSelect x _ (ConstBool [true])) => x`. A `CondSelect`'s value is one of its arms (or
`poison`), so the checker accepts it as the top of a match when its arms' shapes are its own
(`RewriteCheck.condTop`); `checkedRewrite` fires the rule (`v5` becomes `Copy v2`, the result
returns `x`) and the result
refines the input.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `abiInfo` of `pick`: two integer register parameters, one integer result. -/
def csABI : CallABI :=
  { abi := 1, nin := 2, nout := 1, spillOff := 8, spillSize := 16, inRegs := 2, outRegs := 1,
    params := #[{ out := false, index := 0, type := 2, name := some 3, regs := #[0], offset := 0 },
                { out := false, index := 1, type := 2, name := some 4, regs := #[1], offset := 8 },
                { out := true, index := 0, type := 2, name := some 5, regs := #[0],
                  offset := -1 }] }

/-- The definition tables: `int` (type 2), `bool` (type 6). -/
def csTabs : Tables where
  types :=
    let t := Array.replicate 36 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(int, int) int" (.func 0 2 1 #[])))
    let t := t.set! 2 (some (mkT .INT (some 8) "int"))
    let t := t.set! 6 (some (mkT .BOOL (some 1) "bool"))
    let t := t.set! 29 (some (mkT .SSA none "mem"))
    let t := t.set! 31 (some (mkT .SSA none "void"))
    t.set! 35 (some (mkT .RESULTS none "int,mem" (.results #[2, 29])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.pick}", kind := .call (some 2) (some csABI) },
    some { fmt := GoStr.ofString "main.pick",
           kind := .sym (GoStr.ofString "main.pick") 1 "" 0 default none none none #[] none },
    some (paramNameT "x" .PPARAM 2 0), some (paramNameT "y" .PPARAM 2 8),
    some (paramNameT "~r0" .PPARAMOUT 2 0)]

/-- `pick`, the input of late opt. -/
def csFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 6
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[6] #[] #[] #[1, 2, 3, 4, 5, 6])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 1 #[] 1),
    some (mkV 2 .Arg 2 (some 3) p0 1 #[] 1),
    some (mkV 3 .Arg 2 (some 4) p0 1 #[] 1),
    some (mkVi 4 .ConstBool 6 1 p0 1 #[] 1),
    some (mkVi 5 .CondSelect 2 0 p0 1 #[2, 3, 4] 1),
    some (mkVi 6 .MakeResult 35 0 p0 1 #[5, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The one-rule set `{generic.rules:292}`. -/
def csRules : RuleSet where
  name := "generic"
  values := [(.CondSelect, [Generated.Generic.r_generic_292])]
  blocks := []

def csPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "pick", typs := slTyps, tables := csTabs }

def csCheckEnv : CheckEnv := { tabs := csTabs, typs := slTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result in which
the result returns `x` (`v6 = MakeResult v2 v1`: `v5` became `Copy v2`, which copy
elimination removed), which passes `check`. -/
theorem cs_checks :
    (check csCheckEnv csFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet csRules) csPassEnv csFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := slTyps } o.func).toBool,
        (o.func.value? 6).map (·.args))) =
      some (true, some #[2, 1]) := by
  decide +kernel

theorem csRules_allSound : csRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of
    ⟨⟨Proof.Rules.Rule.checked_of_sound Proof.Rules.r_generic_292_sound rfl, trivial⟩, trivial⟩
    trivial

/-- **Pass execution witness** for a `CondSelect` top (`RewriteCheck.condTop`): on `pick`, the
checked rewrite pass folds `CondSelect <int> x y (ConstBool [true])` to `x` (the result returns
`x`), and the result
refines the input (`checkedRewrite_refines`). -/
theorem cs_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet csRules) csPassEnv csFunc = .ok out ∧
      (out.func.value? 6).map (·.args) = some #[2, 1] ∧
      check csCheckEnv csFunc = .ok () ∧
      check { tabs := out.tables, typs := slTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre csPassEnv.tables csPassEnv.frontend csFunc)
      out.tables out.func csPassEnv.tables csFunc := by
  obtain ⟨h1, h2⟩ := cs_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet csRules) csPassEnv csFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h3⟩ := h2
    exact ⟨out, rfl, h3, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := csRules) (penv := csPassEnv)
        (f := csFunc) (out := out) csRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

end GoFV.Proof.Witness
