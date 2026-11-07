import GoFV.Proof.Witness.PhiConst

/-!
# Witness function for `Phi`s of `Not`s: `nsel` (hand-written, issue #69)

```go
func nsel(b, x, y bool) bool {
	var r bool
	if b {
		r = !x
	} else {
		r = !y
	}
	return r
}
```

as opt sees it: the entry `b1` branches on `b` to `b2` (`v5 = Not x`) and `b3` (`v6 = Not y`),
which jump to `b4`, where `v7 = Phi v5 v6` is returned. The one-rule set `{generic.rules:1068}`
(`(Phi <t> nx:(Not x) ny:(Not y)) && nx.Uses == 1 && ny.Uses == 1 => (Not (Phi <t> x y))`, a
`phiSels` rule): `checkedRewrite` turns `v7` into `Not v9` of a fresh `v9 = Phi x y`, the
validator's `Phi`-of-`Not`s layer (`RewriteCheck.pnRel`) accepts it, and the result refines the
input.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `abiInfo` of `nsel`: three boolean register parameters, one boolean result. -/
def nsABI : CallABI :=
  { abi := 1, nin := 3, nout := 1, spillOff := 8, spillSize := 8, inRegs := 3, outRegs := 1,
    params := #[{ out := false, index := 0, type := 6, name := some 3, regs := #[0], offset := 0 },
                { out := false, index := 1, type := 6, name := some 4, regs := #[1], offset := 1 },
                { out := false, index := 2, type := 6, name := some 5, regs := #[2], offset := 2 },
                { out := true, index := 0, type := 6, name := some 6, regs := #[0],
                  offset := -1 }] }

/-- The definition tables: `bool` (type 6). -/
def nsTabs : Tables where
  types :=
    let t := Array.replicate 36 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(bool, bool, bool) bool" (.func 0 3 1 #[])))
    let t := t.set! 6 (some (mkT .BOOL (some 1) "bool"))
    let t := t.set! 29 (some (mkT .SSA none "mem"))
    let t := t.set! 31 (some (mkT .SSA none "void"))
    t.set! 35 (some (mkT .RESULTS none "bool,mem" (.results #[6, 29])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.nsel}", kind := .call (some 2) (some nsABI) },
    some { fmt := GoStr.ofString "main.nsel",
           kind := .sym (GoStr.ofString "main.nsel") 1 "" 0 default none none none #[] none },
    some (paramNameT "b" .PPARAM 6 0), some (paramNameT "x" .PPARAM 6 1),
    some (paramNameT "y" .PPARAM 6 2), some (paramNameT "~r0" .PPARAMOUT 6 0)]

/-- `nsel`, the input of opt. -/
def nsFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 8
  bidLast := 4
  blocks := #[1, 2, 3, 4]
  blockTab := #[none,
    some (mkB 1 .If p0 #[2] #[⟨2, 0⟩, ⟨3, 0⟩] #[] #[1, 2, 3, 4]),
    some (mkB 2 .Plain p0 #[] #[⟨4, 0⟩] #[⟨1, 0⟩] #[5]),
    some (mkB 3 .Plain p0 #[] #[⟨4, 1⟩] #[⟨1, 1⟩] #[6]),
    some (mkB 4 .Ret p0 #[8] #[] #[⟨2, 0⟩, ⟨3, 0⟩] #[7, 8])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 1 #[] 1),
    some (mkV 2 .Arg 6 (some 3) p0 1 #[] 1),
    some (mkV 3 .Arg 6 (some 4) p0 1 #[] 1),
    some (mkV 4 .Arg 6 (some 5) p0 1 #[] 1),
    some (mkVi 5 .Not 6 0 p0 1 #[3] 2),
    some (mkVi 6 .Not 6 0 p0 1 #[4] 3),
    some (mkVi 7 .Phi 6 0 p0 1 #[5, 6] 4),
    some (mkVi 8 .MakeResult 35 0 p0 1 #[7, 1] 4)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The one-rule set `{generic.rules:1068}`, a `Phi` rule validated per instance. -/
def nsRules : RuleSet where
  name := "generic"
  values := []
  blocks := []
  phiSels := [Generated.Generic.r_generic_1068]

def nsPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "nsel", typs := slTyps, tables := nsTabs }

def nsCheckEnv : CheckEnv := { tabs := nsTabs, typs := slTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result in which
`v7` is `Not v9` and `v9` is `Phi v3 v4`, which passes `check`. -/
theorem ns_checks :
    (check nsCheckEnv nsFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet nsRules) nsPassEnv nsFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := slTyps } o.func).toBool,
        (o.func.value? 7).map (fun v => (v.op, v.args)),
        (o.func.value? 9).map (fun v => (v.op, v.args)))) =
      some (true, some (.Not, #[9]), some (.Phi, #[3, 4])) := by
  decide +kernel

theorem nsRules_allSound : nsRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of trivial trivial

/-- **Pass execution witness** for a `Phi` of `Not`s (`RewriteCheck.pnRel`, `PhiNot.pn_refines`):
on `nsel`, the checked rewrite pass turns `Phi (Not x) (Not y)` into `Not (Phi x y)`, and the
result refines the input (`checkedRewrite_refines`). -/
theorem pn_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet nsRules) nsPassEnv nsFunc = .ok out ∧
      (out.func.value? 7).map (fun v => (v.op, v.args)) = some (.Not, #[9]) ∧
      (out.func.value? 9).map (fun v => (v.op, v.args)) = some (.Phi, #[3, 4]) ∧
      check nsCheckEnv nsFunc = .ok () ∧
      check { tabs := out.tables, typs := slTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre nsPassEnv.tables nsPassEnv.frontend nsFunc)
      out.tables out.func nsPassEnv.tables nsFunc := by
  obtain ⟨h1, h2⟩ := ns_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet nsRules) nsPassEnv nsFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h3, h4⟩ := h2
    exact ⟨out, rfl, h3, h4, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := nsRules) (penv := nsPassEnv)
        (f := nsFunc) (out := out) nsRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

/-- The rule of the witness is a `Phi`-of-`Not`s rule: the layer that validates it is
`pnRel`'s. -/
example : GoFV.Opt.RewriteCheck.pnShapeOK Generated.Generic.r_generic_1068 = true := rfl

end GoFV.Proof.Witness
