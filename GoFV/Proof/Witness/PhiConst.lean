import GoFV.Proof.Witness.CondSel
import GoFV.Proof.Rules.PhiSel

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for constant `Phi`s: `five` (hand-written, issue #69)

```go
func five(b bool) int {
	x := 5
	if b {
		x = 5
	}
	return x
}
```

as opt sees it: the entry `b1` holds both constants (`v3`, `v4`, `Const64 [5]`) and branches on
`b` to `b2` and `b3`, which jump to `b4`, where `v5 = Phi v3 v4` is returned. The one-rule set
`{generic.rules:785}` (`(Phi (Const64 [c]) (Const64 [c])) => (Const64 [c])`, a `phiSels` rule):
`checkedRewrite` turns `v5` into `Const64 [5]`, the validator's constant-`Phi` layer
(`RewriteCheck.pcRel`) accepts it, and the result refines the input.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `abiInfo` of `five`: one boolean register parameter, one integer result. -/
def fvABI : CallABI :=
  { abi := 1, nin := 1, nout := 1, spillOff := 8, spillSize := 8, inRegs := 1, outRegs := 1,
    params := #[{ out := false, index := 0, type := 6, name := some 3, regs := #[0], offset := 0 },
                { out := true, index := 0, type := 2, name := some 4, regs := #[0],
                  offset := -1 }] }

/-- The definition tables: `int` (type 2), `bool` (type 6). -/
def fvTabs : Tables where
  types :=
    let t := Array.replicate 36 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(bool) int" (.func 0 1 1 #[])))
    let t := t.set! 2 (some (mkT .INT (some 8) "int"))
    let t := t.set! 6 (some (mkT .BOOL (some 1) "bool"))
    let t := t.set! 29 (some (mkT .SSA none "mem"))
    let t := t.set! 31 (some (mkT .SSA none "void"))
    t.set! 35 (some (mkT .RESULTS none "int,mem" (.results #[2, 29])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.five}", kind := .call (some 2) (some fvABI) },
    some { fmt := GoStr.ofString "main.five",
           kind := .sym (GoStr.ofString "main.five") 1 "" 0 default none none none #[] none },
    some (paramNameT "b" .PPARAM 6 0), some (paramNameT "~r0" .PPARAMOUT 2 0)]

/-- `five`, the input of opt. -/
def fvFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 6
  bidLast := 4
  blocks := #[1, 2, 3, 4]
  blockTab := #[none,
    some (mkB 1 .If p0 #[2] #[⟨2, 0⟩, ⟨3, 0⟩] #[] #[1, 2, 3, 4]),
    some (mkB 2 .Plain p0 #[] #[⟨4, 0⟩] #[⟨1, 0⟩] #[]),
    some (mkB 3 .Plain p0 #[] #[⟨4, 1⟩] #[⟨1, 1⟩] #[]),
    some (mkB 4 .Ret p0 #[6] #[] #[⟨2, 0⟩, ⟨3, 0⟩] #[5, 6])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 1 #[] 1),
    some (mkV 2 .Arg 6 (some 3) p0 1 #[] 1),
    some (mkVi 3 .Const64 2 5 p0 1 #[] 1),
    some (mkVi 4 .Const64 2 5 p0 1 #[] 1),
    some (mkVi 5 .Phi 2 0 p0 1 #[3, 4] 4),
    some (mkVi 6 .MakeResult 35 0 p0 1 #[5, 1] 4)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The one-rule set `{generic.rules:785}`, a `Phi` rule validated per instance. -/
def fvRules : RuleSet where
  name := "generic"
  values := []
  blocks := []
  phiSels := [Generated.Generic.r_generic_785]

def fvPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "five", typs := slTyps, tables := fvTabs }

def fvCheckEnv : CheckEnv := { tabs := fvTabs, typs := slTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result in which
`v5` is `Const64 [5]`, which passes `check`. -/
theorem fv_checks :
    (check fvCheckEnv fvFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet fvRules) fvPassEnv fvFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := slTyps } o.func).toBool,
        (o.func.value? 5).map (fun v => (v.op, v.auxInt, v.args)))) =
      some (true, some (.Const64, 5, #[])) := by
  decide +kernel

theorem fvRules_allSound : fvRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of trivial trivial

/-- **Pass execution witness** for a constant `Phi` (`RewriteCheck.pcRel`, `PhiConst.pc_refines`):
on `five`, the checked rewrite pass turns `Phi (Const64 [5]) (Const64 [5])` into `Const64 [5]`,
and the result refines the input (`checkedRewrite_refines`). -/
theorem pc_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet fvRules) fvPassEnv fvFunc = .ok out ∧
      (out.func.value? 5).map (fun v => (v.op, v.auxInt, v.args)) = some (.Const64, 5, #[]) ∧
      check fvCheckEnv fvFunc = .ok () ∧
      check { tabs := out.tables, typs := slTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre fvPassEnv.tables fvPassEnv.frontend fvFunc)
      out.tables out.func fvPassEnv.tables fvFunc := by
  obtain ⟨h1, h2⟩ := fv_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet fvRules) fvPassEnv fvFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h3⟩ := h2
    exact ⟨out, rfl, h3, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := fvRules) (penv := fvPassEnv)
        (f := fvFunc) (out := out) fvRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

/-- The rule of the witness is a constant-`Phi` rule: the layer that validates it is `pcRel`'s. -/
example : GoFV.Opt.RewriteCheck.pcShapeOK Generated.Generic.r_generic_785 = true := rfl

end GoFV.Proof.Witness
