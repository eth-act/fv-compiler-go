import GoFV.Proof.Pass.Rewrite
import GoFV.Proof.Witness.AddZero

/-!
# Non-vacuity witness: a phi elimination in the checked rewrite pass (hand-written, issue #69)

```go
func pz() int64 {
	x := int64(5)
	if true {
	} else {
		x = 0 + x
	}
	return x
}
```

as SSA before `opt`: the entry `b1` branches on `ConstBool [true]` to `b2` and `b3`, both jump to
`b4`, where `v6 = Phi v3 v5` (`Const64 [5]` from `b2`, `v5 = Add64 (Const64 [0]) v3` from `b3`) is
returned. With the one-rule set `{generic.rules:646, Add64 instance}` (`azRules`), `v5` becomes
`Copy v3`, copy elimination makes the `Phi`'s arguments `v3 v3`, and `phielimValue` turns it into
`Copy v3` (a `phielim` event, so the validator checks the log in two segments, `segsOK`); the
result returns `v3` directly. The validator accepts it and input and output pass `check` (kernel
evaluation), so `checkedRewrite_refines` applies.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- `abiInfo` of `pz`: no parameters, one result. -/
def peABI : CallABI :=
  { abi := 1, nin := 0, nout := 1, spillOff := 8, spillSize := 0, inRegs := 0, outRegs := 1,
    params := #[{ out := true, index := 0, type := 10, name := some 3, regs := #[0],
                  offset := -1 }] }

/-- The definition tables. -/
def peTabs : Tables where
  types :=
    let t := Array.replicate 41 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func() int64" (.func 0 0 1 #[])))
    let t := t.set! 6 (some (mkT .BOOL (some 1) "bool"))
    let t := t.set! 10 (some (mkT .INT64 (some 8) "int64"))
    let t := t.set! 31 (some (mkT .SSA none "mem"))
    let t := t.set! 32 (some (mkT .SSA none "void"))
    t.set! 40 (some (mkT .RESULTS none "int64,mem" (.results #[10, 31])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.pz}", kind := .call (some 2) (some peABI) },
    some { fmt := GoStr.ofString "main.pz",
           kind := .sym (GoStr.ofString "main.pz") 1 "" 0 default none none none #[] none },
    some (paramNameT "~r0" .PPARAMOUT 10 0)]

/-- The values, by ID. -/
def peValues : Array (Option Value) := #[none,
  some (mkVi 1 .InitMem 31 0 p0 1 #[] 1),
  some (mkVi 2 .ConstBool 6 1 p0 1 #[] 1),
  some (mkVi 3 .Const64 10 5 p0 2 #[] 1),
  some (mkVi 4 .Const64 10 0 p0 1 #[] 1),
  some (mkVi 5 .Add64 10 0 p0 1 #[4, 3] 3),
  some (mkVi 6 .Phi 10 0 p0 1 #[3, 5] 4),
  some (mkVi 7 .MakeResult 40 0 p0 1 #[6, 1] 4)]

/-- The blocks, by ID. -/
def peBlocks : Array (Option Block) := #[none,
  some (mkB 1 .If p0 #[2] #[⟨2, 0⟩, ⟨3, 0⟩] #[] #[1, 2, 3, 4]),
  some (mkB 2 .Plain p0 #[] #[⟨4, 0⟩] #[⟨1, 0⟩] #[]),
  some (mkB 3 .Plain p0 #[] #[⟨4, 1⟩] #[⟨1, 1⟩] #[5]),
  some (mkB 4 .Ret p0 #[7] #[] #[⟨2, 0⟩, ⟨3, 0⟩] #[6, 7])]

/-- `pz`, the input of `opt`. -/
def pz : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 7
  bidLast := 4
  blocks := #[1, 2, 3, 4]
  blockTab := peBlocks
  valueTab := peValues
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[(1, #[2]), (5, #[3]), (0, #[4])]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

def peTyps : Array (String × TypeRef) := #[("Bool", 6), ("Int64", 10), ("Mem", 31), ("Void", 32)]

def peCheckEnv : CheckEnv := { tabs := peTabs, typs := peTyps }

/-- The pass environment of `opt` (arm64, the export's fixed configuration). -/
def pePassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "pz", typs := peTyps, tables := peTabs }

/-- By kernel evaluation: the input passes `check`; the rewrite logs a phi elimination;
`checkedRewrite` keeps a result that returns `v3` directly and passes `check`. -/
theorem pz_checks :
    (check peCheckEnv pz).toBool = true ∧
    (rewriteRun (Interp.Table.ofRuleSet azRules) true true pePassEnv pz).toOption.map
      (fun r => RewriteCheck.noPhiElim r.2.2) = some false ∧
    (checkedRewrite (Interp.Table.ofRuleSet azRules) pePassEnv pz).toOption.map
      (fun o => ((check peCheckEnv o.func).toBool, (o.func.value? 7).map (·.args))) =
      some (true, some #[3, 1]) := by
  decide +kernel

/-- **Witness of `segs_refines`** (through `checkedRewrite_refines`): on `pz`, the rewrite logs a
phi elimination, the checked pass keeps its result (`MakeResult v3 v1`: the `Phi` is gone), and
the result refines the input. -/
theorem pz_checkedRewrite :
    (∃ r, rewriteRun (Interp.Table.ofRuleSet azRules) true true pePassEnv pz = .ok r ∧
      RewriteCheck.noPhiElim r.2.2 = false) ∧
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet azRules) pePassEnv pz = .ok out ∧
      (out.func.value? 7).map (·.args) = some #[3, 1] ∧
      RefinesFrom (Pass.Rewrite.RwPre pePassEnv.tables pz) out.tables out.func pePassEnv.tables pz := by
  obtain ⟨h1, hl, h2⟩ := pz_checks
  refine ⟨?_, ?_⟩
  · cases hr : rewriteRun (Interp.Table.ofRuleSet azRules) true true pePassEnv pz with
    | error e => rw [hr] at hl; cases hl
    | ok r =>
      rw [hr] at hl
      simp only [Except.toOption, Option.map_some, Option.some.injEq] at hl
      exact ⟨r, rfl, hl⟩
  cases hc : checkedRewrite (Interp.Table.ofRuleSet azRules) pePassEnv pz with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h7⟩ := h2
    refine ⟨out, rfl, h7, ?_⟩
    exact Pass.Rewrite.checkedRewrite_refines (s := azRules) (penv := pePassEnv) (f := pz)
      (out := out) azRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)

end GoFV.Proof.Witness
