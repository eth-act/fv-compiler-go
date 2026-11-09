import GoFV.Proof.Witness.IMakeSM
import GoFV.Proof.Rules.AddrCmp

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for a comparison of symbol addresses: `same` (hand-written, issue #69)

```go
var a, b int

func same() bool { return &a == &b }
```

as opt sees it: `v3 = Addr {main.a} SB`, `v4 = Addr {main.b} SB`, `v5 = EqPtr <bool> v3 v4` is
returned. The one-rule set `{generic.rules:1648}` (`(EqPtr (Addr {x} _) (Addr {y} _)) =>
(ConstBool [x == y])`, `Rule.AddrCmp`): `checkedRewrite` makes `v5` the constant `false`; the
validator checks the event per instance (`RewriteCheck.addrCmpOK`: the two `Addr`s name different
global blocks), and the result refines the input.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `abiInfo` of `same`: no parameters, one boolean result. -/
def acABI : CallABI :=
  { abi := 1, nin := 0, nout := 1, spillOff := 0, spillSize := 0, inRegs := 0, outRegs := 1,
    params := #[{ out := true, index := 0, type := 6, name := some 5, regs := #[0],
                  offset := -1 }] }

/-- A data symbol of 8 bytes. -/
def acSym (s : String) : AuxDef :=
  { fmt := GoStr.ofString s,
    kind := .sym (GoStr.ofString s) 0 "SNOPTRBSS" 8 default none none none #[] none }

/-- The definition tables: `int` (type 2), `bool` (6), `uintptr` (15), `*int` (20); the symbols
`main.a` (aux 3) and `main.b` (aux 4). -/
def acTabs : Tables where
  types :=
    let t := Array.replicate 36 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func() bool" (.func 0 0 1 #[])))
    let t := t.set! 2 (some (mkT .INT (some 8) "int"))
    let t := t.set! 6 (some (mkT .BOOL (some 1) "bool"))
    let t := t.set! 15 (some (mkT .UINTPTR (some 8) "uintptr"))
    let t := t.set! 20 (some (mkT .PTR (some 8) "*int" (.elem 2)))
    let t := t.set! 29 (some (mkT .SSA none "mem"))
    let t := t.set! 31 (some (mkT .SSA none "void"))
    t.set! 35 (some (mkT .RESULTS none "bool,mem" (.results #[6, 29])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.same}", kind := .call (some 2) (some acABI) },
    some { fmt := GoStr.ofString "main.same",
           kind := .sym (GoStr.ofString "main.same") 1 "" 0 default none none none #[] none },
    some (acSym "main.a"), some (acSym "main.b"),
    some (paramNameT "~r0" .PPARAMOUT 6 0)]

/-- `same`, the input of opt. -/
def acFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 6
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[6] #[] #[] #[1, 2, 3, 4, 5, 6])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 1 #[] 1),
    some (mkV 2 .SB 15 none p0 2 #[] 1),
    some (mkV 3 .Addr 20 (some 3) p0 1 #[2] 1),
    some (mkV 4 .Addr 20 (some 4) p0 1 #[2] 1),
    some (mkVi 5 .EqPtr 6 0 p0 1 #[3, 4] 1),
    some (mkVi 6 .MakeResult 35 0 p0 1 #[5, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The one-rule set `{generic.rules:1648}`. -/
def acRules : RuleSet where
  name := "generic"
  values := [(.EqPtr, [Generated.Generic.r_generic_1648])]
  blocks := []

def acTyps : Array (String × TypeRef) :=
  #[("Int", 2), ("Bool", 6), ("Mem", 29), ("Void", 31), ("Uintptr", 15)]

def acPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "same", typs := acTyps, tables := acTabs }

def acCheckEnv : CheckEnv := { tabs := acTabs, typs := acTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result in which
`v5` is the constant `false`, which passes `check`. -/
theorem ac_checks :
    (check acCheckEnv acFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet acRules) acPassEnv acFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := acTyps } o.func).toBool,
        (o.func.value? 5).map (fun v => (v.op, v.auxInt, v.args)))) =
      some (true, some (.ConstBool, 0, #[])) := by
  decide +kernel

theorem acRules_allSound : acRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of
    ⟨⟨Proof.Rules.Rule.checked_of_addrCmp Proof.Rules.r_generic_1648_sound, trivial⟩, trivial⟩
    trivial

/-- **Pass execution witness** for a comparison of symbol addresses (`RewriteCheck.addrCmpOK`): on
`same`, the checked rewrite pass folds `&a == &b` to `false`, and the result refines the input
(`checkedRewrite_refines`). -/
theorem ac_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet acRules) acPassEnv acFunc = .ok out ∧
      (out.func.value? 5).map (fun v => (v.op, v.auxInt, v.args)) = some (.ConstBool, 0, #[]) ∧
      check acCheckEnv acFunc = .ok () ∧
      check { tabs := out.tables, typs := acTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre acPassEnv.tables acPassEnv.frontend acFunc)
      out.tables out.func acPassEnv.tables acFunc := by
  obtain ⟨h1, h2⟩ := ac_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet acRules) acPassEnv acFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h3⟩ := h2
    exact ⟨out, rfl, h3, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := acRules) (penv := acPassEnv)
        (f := acFunc) (out := out) acRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

end GoFV.Proof.Witness
