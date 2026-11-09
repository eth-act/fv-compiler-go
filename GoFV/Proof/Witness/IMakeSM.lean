import GoFV.Proof.Witness.CondSel
import GoFV.Proof.Rules.IMakeSM

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for an `IMake` of a `StructMake`: `box` (hand-written, issue #69)

```go
type S struct{ p *int }

func box(t uintptr, p *int) *uint8 // the data word of `any(S{p})` with type word `t`
```

as opt sees it: `v4 = StructMake <S> p`, `v5 = IMake <any> t v4`, `v6 = IData <*uint8> v5` is
returned. The one-rule set `{generic.rules:981}` (`(IMake _typ (StructMake ___)) =>
imakeOfStructMake(v)`, `Rule.IMakeSM`): `checkedRewrite` makes `v5` a copy of a fresh
`v8 = IMake <any> t p`, which copy elimination puts into `v6`; the validator checks the event per
instance (`RewriteCheck.imsOK`), and the result refines the input.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `abiInfo` of `box`: two integer register parameters, one pointer result. -/
def bxABI : CallABI :=
  { abi := 1, nin := 2, nout := 1, spillOff := 8, spillSize := 16, inRegs := 2, outRegs := 1,
    params := #[{ out := false, index := 0, type := 15, name := some 3, regs := #[0], offset := 0 },
                { out := false, index := 1, type := 20, name := some 4, regs := #[1], offset := 8 },
                { out := true, index := 0, type := 24, name := some 5, regs := #[0],
                  offset := -1 }] }

/-- The definition tables: `int` (type 2), `uintptr` (15), `*int` (20), `S` (22), `any` (23),
`*uint8` (24), `uint8` (25). -/
def bxTabs : Tables where
  types :=
    let t := Array.replicate 36 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(uintptr, *int) *uint8" (.func 0 2 1 #[])))
    let t := t.set! 2 (some (mkT .INT (some 8) "int"))
    let t := t.set! 15 (some (mkT .UINTPTR (some 8) "uintptr"))
    let t := t.set! 20 (some (mkT .PTR (some 8) "*int" (.elem 2)))
    let t := t.set! 22 (some (mkT .STRUCT (some 8) "S"
      (.struct #[{ name := GoStr.ofString "p", type := 20, offset := some 0, embedded := false }])))
    let t := t.set! 23 (some (mkT .INTER (some 16) "interface {}"))
    let t := t.set! 24 (some (mkT .PTR (some 8) "*uint8" (.elem 25)))
    let t := t.set! 25 (some (mkT .UINT8 (some 1) "uint8"))
    let t := t.set! 29 (some (mkT .SSA none "mem"))
    let t := t.set! 31 (some (mkT .SSA none "void"))
    t.set! 35 (some (mkT .RESULTS none "*uint8,mem" (.results #[24, 29])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.box}", kind := .call (some 2) (some bxABI) },
    some { fmt := GoStr.ofString "main.box",
           kind := .sym (GoStr.ofString "main.box") 1 "" 0 default none none none #[] none },
    some (paramNameT "t" .PPARAM 15 0), some (paramNameT "p" .PPARAM 20 8),
    some (paramNameT "~r0" .PPARAMOUT 24 0)]

/-- `box`, the input of opt. -/
def bxFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 7
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[7] #[] #[] #[1, 2, 3, 4, 5, 6, 7])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 1 #[] 1),
    some (mkV 2 .Arg 15 (some 3) p0 1 #[] 1),
    some (mkV 3 .Arg 20 (some 4) p0 1 #[] 1),
    some (mkVi 4 .StructMake 22 0 p0 1 #[3] 1),
    some (mkVi 5 .IMake 23 0 p0 1 #[2, 4] 1),
    some (mkVi 6 .IData 24 0 p0 1 #[5] 1),
    some (mkVi 7 .MakeResult 35 0 p0 1 #[6, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The one-rule set `{generic.rules:981}`. -/
def bxRules : RuleSet where
  name := "generic"
  values := [(.IMake, [Generated.Generic.r_generic_981])]
  blocks := []

def bxPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "box", typs := slTyps, tables := bxTabs }

def bxCheckEnv : CheckEnv := { tabs := bxTabs, typs := slTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result in which
`v6` reads the fresh `v8 = IMake v2 v3`, which passes `check`. -/
theorem bx_checks :
    (check bxCheckEnv bxFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet bxRules) bxPassEnv bxFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := slTyps } o.func).toBool,
        (o.func.value? 6).map (·.args),
        (o.func.value? 8).map (fun v => (v.op, v.args)))) =
      some (true, some #[8], some (.IMake, #[2, 3])) := by
  decide +kernel

theorem bxRules_allSound : bxRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of
    ⟨⟨Proof.Rules.Rule.checked_of_ims Proof.Rules.r_generic_981_sound, trivial⟩, trivial⟩ trivial

/-- **Pass execution witness** for an `IMake` of a `StructMake` (`RewriteCheck.imsOK`): on `box`,
the checked rewrite pass puts the struct's pointer field into the interface (`v6` reads the fresh
`IMake t p`), and the result refines the input (`checkedRewrite_refines`). -/
theorem ims_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet bxRules) bxPassEnv bxFunc = .ok out ∧
      (out.func.value? 6).map (·.args) = some #[8] ∧
      (out.func.value? 8).map (fun v => (v.op, v.args)) = some (.IMake, #[2, 3]) ∧
      check bxCheckEnv bxFunc = .ok () ∧
      check { tabs := out.tables, typs := slTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre bxPassEnv.tables bxPassEnv.frontend bxFunc)
      out.tables out.func bxPassEnv.tables bxFunc := by
  obtain ⟨h1, h2⟩ := bx_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet bxRules) bxPassEnv bxFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h3, h4⟩ := h2
    exact ⟨out, rfl, h3, h4, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := bxRules) (penv := bxPassEnv)
        (f := bxFunc) (out := out) bxRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

end GoFV.Proof.Witness
