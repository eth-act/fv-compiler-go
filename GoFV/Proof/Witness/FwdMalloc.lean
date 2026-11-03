import GoFV.Proof.Witness.FwdDrop

/-!
# Witness function for the malloc-cluster dropped writes (issue #69)

```go
func newArr(t *int) *[2]int {
	p := new([2]int) // v5 = StaticLECall {runtime.mallocgcSmallNoScanSC2} 16 t true mem
	*p = [2]int{}    // v8 = Zero {[2]int} [16] (SelectN [0] v5) (SelectN [1] v5)  (generic.rules:1352)
	p[1] = 0         // v11 = Store {int} (OffPtr [8] (SelectN [0] v5)) 0 v8     (:1362)
	return p
}
```

as one block (the parameter `t` stands in for the type descriptor argument). The checked rewrite
pass with `{:1352, :1362}` (forwardings, `RuleSet.loads`) turns both writes into copies of the
call's memory: the size-specialised allocator asked for zeroed memory (`RewriteCheck.freshCall`:
a positive `Const64` size, `needzero` `ConstBool [1]`), so its result block is all zero in its
memory (`Sem.Env.AllocZero`), and neither write changes a byte (`RewriteCheck.dropOK` through
`zeroChain`'s malloc case). The result's `MakeResult` takes the call's memory `v7`.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `abiInfo` of `newArr`: one pointer register parameter, one pointer result. -/
def fmABI : CallABI :=
  { abi := 1, nin := 1, nout := 1, spillOff := 8, spillSize := 8, inRegs := 1, outRegs := 1,
    params := #[{ out := false, index := 0, type := 3, name := some 3, regs := #[0], offset := 0 },
                { out := true, index := 0, type := 5, name := some 4, regs := #[0],
                  offset := -1 }] }

/-- `abiInfo` of `runtime.mallocgcSmallNoScanSC2`: an integer size, a pointer type descriptor and
a `bool` `needzero` in registers, one pointer result. -/
def fmMallocABI : CallABI :=
  { abi := 1, nin := 3, nout := 1, spillOff := 8, spillSize := 24, inRegs := 3, outRegs := 1,
    params := #[{ out := false, index := 0, type := 2, name := none, regs := #[0], offset := 0 },
                { out := false, index := 1, type := 3, name := none, regs := #[1], offset := 8 },
                { out := false, index := 2, type := 6, name := none, regs := #[2], offset := 16 },
                { out := true, index := 0, type := 5, name := none, regs := #[0], offset := -1 }] }

/-- The definition tables: `[2]int` is type 4 (aux 7), `*[2]int` type 5, `bool` type 6, `int` aux
8; `*[2]int,mem` (type 35) is the type of the call and of the result. -/
def fmTabs : Tables where
  types :=
    let t := mlTabs.types
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(*int) *[2]int" (.func 0 1 1 #[])))
    let t := t.set! 6 (some (mkT .BOOL (some 1) "bool"))
    t.set! 35 (some (mkT .RESULTS none "*[2]int,mem" (.results #[5, 29])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.newArr}", kind := .call (some 2) (some fmABI) },
    some { fmt := GoStr.ofString "main.newArr",
           kind := .sym (GoStr.ofString "main.newArr") 1 "" 0 default none none none #[] none },
    some (paramNameT "t" .PPARAM 3 0),
    some (paramNameT "~r0" .PPARAMOUT 5 0),
    some { fmt := GoStr.ofString "AuxCall{runtime.mallocgcSmallNoScanSC2}",
           kind := .call (some 6) (some fmMallocABI) },
    some { fmt := GoStr.ofString "runtime.mallocgcSmallNoScanSC2",
           kind := .sym (GoStr.ofString "runtime.mallocgcSmallNoScanSC2") 1 "" 0 default none none
             none #[] none },
    some { fmt := GoStr.ofString "[2]int", kind := .type 4 },
    some { fmt := GoStr.ofString "int", kind := .type 2 }]

/-- `newArr`, the input of `opt`. -/
def fmFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 12
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[12] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 1 #[] 1),
    some (mkV 2 .Arg 3 (some 3) p0 1 #[] 1),
    some (mkVi 3 .Const64 2 16 p0 1 #[] 1),
    some (mkVi 4 .ConstBool 6 1 p0 1 #[] 1),
    some (mkV 5 .StaticLECall 35 (some 5) p0 2 #[3, 2, 4, 1] 1),
    some (mkVi 6 .SelectN 5 0 p0 3 #[5] 1),
    some (mkVi 7 .SelectN 29 1 p0 1 #[5] 1),
    some { mkV 8 .Zero 29 (some 7) p0 1 #[6, 7] 1 with auxInt := 16 },
    some (mkVi 9 .OffPtr 3 8 p0 1 #[6] 1),
    some (mkVi 10 .Const64 2 0 p0 1 #[] 1),
    some (mkV 11 .Store 29 (some 8) p0 1 #[9, 10, 8] 1),
    some (mkVi 12 .MakeResult 35 0 p0 1 #[6, 11] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The rule set `{generic.rules:1352, :1362}`, as forwardings. -/
def fmRules : RuleSet where
  name := "generic"
  values := []
  blocks := []
  loads := [Generated.Generic.r_generic_1362, Generated.Generic.r_generic_1352]

theorem fmRules_allSound : fmRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of trivial trivial

def fmPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "newArr", typs := slTyps, tables := fmTabs }

def fmCheckEnv : CheckEnv := { tabs := fmTabs, typs := slTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result, which
passes `check`, whose `MakeResult` takes the call's memory `v7`, with no `Store` or `Zero` left in
the block. -/
theorem fm_checks :
    (check fmCheckEnv fmFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet fmRules) fmPassEnv fmFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := slTyps } o.func).toBool,
        (o.func.value? 12).map (·.args),
        ((o.func.block? 1).map fun b => b.values.toList.filter fun x =>
          (o.func.value? x).any fun v => v.op == .Store || v.op == .Zero))) =
      some (true, some #[6, 7], some []) := by
  decide +kernel

/-- **Pass execution witness** for the malloc-cluster dropped writes (`generic.rules:1352`,
`:1362`): on `newArr`, the checked rewrite pass returns the memory of the allocation
(`v12 = MakeResult v6 v7`), and the result refines the input (`checkedRewrite_refines`, through
`LoadFwd.fwd_refines` under `Env.AllocZero`). -/
theorem fm_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet fmRules) fmPassEnv fmFunc = .ok out ∧
      (out.func.value? 12).map (·.args) = some #[6, 7] ∧
      check fmCheckEnv fmFunc = .ok () ∧
      check { tabs := out.tables, typs := slTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre fmPassEnv.tables fmPassEnv.frontend fmFunc)
      out.tables out.func
        fmPassEnv.tables fmFunc := by
  obtain ⟨h1, h2⟩ := fm_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet fmRules) fmPassEnv fmFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h12, -⟩ := h2
    exact ⟨out, rfl, h12, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := fmRules) (penv := fmPassEnv)
        (f := fmFunc) (out := out) fmRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

end GoFV.Proof.Witness
