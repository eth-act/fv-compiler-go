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

/-! ## A `Phi <uintptr>` of a `*uint8` `Addr` turned copy (issue #17)

`pa` returns the itab-like word `uintptr(unsafe.Pointer(&g))` through a branch: `v6 = Phi
<uintptr> v4 v4` of `v4 = Addr <*uint8> {main.g} SB` in `b4` (as decompose builtin leaves the
itab component of an interface `Phi` whose `IMake`s share one itab symbol). `phielimValue` turns
it into `Copy <uintptr> v4`; the copy changes no value: the two word shapes retype alike
(`retypeEqB` of `*uint8` and `uintptr` is true, #290), so `CopyCheck.copyOK` accepts it. -/

/-- `abiInfo` of `pa`: no parameters, one `uintptr` result. -/
def peaABI : CallABI :=
  { peABI with params := #[{ out := true, index := 0, type := 10, name := some 3, regs := #[0],
                             offset := -1 }] }

/-- The definition tables: `uintptr` (10), `*uint8` (12), the data symbol `main.g` (aux 4). -/
def peaTabs : Tables where
  types :=
    let t := Array.replicate 41 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func() uintptr" (.func 0 0 1 #[])))
    let t := t.set! 6 (some (mkT .BOOL (some 1) "bool"))
    let t := t.set! 10 (some (mkT .UINTPTR (some 8) "uintptr"))
    let t := t.set! 11 (some (mkT .UINT8 (some 1) "uint8"))
    let t := t.set! 12 (some (mkT .PTR (some 8) "*uint8" (.elem 11)))
    let t := t.set! 31 (some (mkT .SSA none "mem"))
    let t := t.set! 32 (some (mkT .SSA none "void"))
    t.set! 40 (some (mkT .RESULTS none "uintptr,mem" (.results #[10, 31])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.pa}", kind := .call (some 2) (some peaABI) },
    some { fmt := GoStr.ofString "main.pa",
           kind := .sym (GoStr.ofString "main.pa") 1 "" 0 default none none none #[] none },
    some (paramNameT "~r0" .PPARAMOUT 10 0),
    some { fmt := GoStr.ofString "main.g",
           kind := .sym (GoStr.ofString "main.g") 0 "SNOPTRBSS" 8 default none none none #[]
             none }]

/-- `pa`, the input of the rewrite pass. -/
def pa : Func :=
  { pz with
    vidLast := 7
    blockTab := #[none,
      some (mkB 1 .If p0 #[2] #[⟨2, 0⟩, ⟨3, 0⟩] #[] #[1, 2, 3, 4]),
      some (mkB 2 .Plain p0 #[] #[⟨4, 0⟩] #[⟨1, 0⟩] #[]),
      some (mkB 3 .Plain p0 #[] #[⟨4, 1⟩] #[⟨1, 1⟩] #[]),
      some (mkB 4 .Ret p0 #[7] #[] #[⟨2, 0⟩, ⟨3, 0⟩] #[6, 7])]
    valueTab := #[none,
      some (mkVi 1 .InitMem 31 0 p0 1 #[] 1),
      some (mkVi 2 .ConstBool 6 1 p0 1 #[] 1),
      some (mkV 3 .SB 10 none p0 1 #[] 1),
      some (mkV 4 .Addr 12 (some 4) p0 2 #[3] 1),
      none,
      some (mkVi 6 .Phi 10 0 p0 1 #[4, 4] 4),
      some (mkVi 7 .MakeResult 40 0 p0 1 #[6, 1] 4)]
    consts := #[(1, #[2])] }

def peaTyps : Array (String × TypeRef) :=
  #[("Bool", 6), ("Uintptr", 10), ("BytePtr", 12), ("Mem", 31), ("Void", 32)]

def peaCheckEnv : CheckEnv := { tabs := peaTabs, typs := peaTyps }

def peaPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "pa", typs := peaTyps, tables := peaTabs }

/-- By kernel evaluation: the input passes `check`; the rewrite logs a phi elimination;
`checkedRewrite` keeps a result that returns `v4` directly and passes `check`; the `Addr`'s and
the `Phi`'s shapes retype alike. -/
theorem pa_checks :
    (check peaCheckEnv pa).toBool = true ∧
    (rewriteRun (Interp.Table.ofRuleSet azRules) true true peaPassEnv pa).toOption.map
      (fun r => RewriteCheck.noPhiElim r.2.2) = some false ∧
    (checkedRewrite (Interp.Table.ofRuleSet azRules) peaPassEnv pa).toOption.map
      (fun o => ((check peaCheckEnv o.func).toBool, (o.func.value? 7).map (·.args))) =
      some (true, some #[4, 1]) ∧
    CopyElim.retypeEqB (peaTabs.ty 12) (peaTabs.ty 10) = true := by
  decide +kernel

/-- **Witness of a phi elimination across the word shapes** (`CopyElim.CopyRel`'s `copyShape`
through `checkedRewrite_refines`): on `pa`, the rewrite turns the `Phi <uintptr>` of a `*uint8`
`Addr` into a copy of it, the checked pass keeps its result (`MakeResult v4 v1`), and the
result refines the input. -/
theorem pa_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet azRules) peaPassEnv pa = .ok out ∧
      (out.func.value? 7).map (·.args) = some #[4, 1] ∧
      RefinesFrom (Pass.Rewrite.RwPre peaPassEnv.tables pa) out.tables out.func
        peaPassEnv.tables pa := by
  obtain ⟨h1, -, h2, -⟩ := pa_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet azRules) peaPassEnv pa with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h7⟩ := h2
    exact ⟨out, rfl, h7, Pass.Rewrite.checkedRewrite_refines (s := azRules) (penv := peaPassEnv)
      (f := pa) (out := out) azRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

end GoFV.Proof.Witness
