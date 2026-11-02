import GoFV.Proof.Witness.FwdMalloc

/-!
# Witness function for writes into a `runtime.newobject` result (issue #69)

```go
func newArr(t *int) *[2]int {
	p := new([2]int) // v5 = StaticLECall {runtime.newobject} (Addr {type:[2]int} SB) mem
	*p = [2]int{}    // v8 = Zero {[2]int} [16] (SelectN [0] v5) (SelectN [1] v5)  (generic.rules:1352)
	p[1] = 0         // v11 = Store {int} (OffPtr [8] (SelectN [0] v5)) 0 v8     (:1362)
	return p
}
```

as one block, where `type:[2]int` is a type descriptor (as the export writes them: no `SRODATA`
bytes, `typeinfo` and an `rtype` line with size 16 and no pointer bytes), whose image in the
global memory is `Sem.typeDescAlloc`. The checked rewrite pass with `{:1352, :1362}`
(forwardings, `RuleSet.loads`) turns both writes into copies of the call's memory: the call's type
argument is an `Addr` of one of the input's read-only symbols (`RewriteCheck.roSyms`) whose type
descriptor has a positive size (`RewriteCheck.freshNew`, `fwdRoOK`), so under
`Sem.Env.AllocZero` from a memory holding the descriptor (`Sem.RoImage`) the result block is all
zero in its memory, and neither write changes a byte. The precondition `RwPre` holds on `Env.p1`
with the descriptor in the global image (`fn_rwPre`).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `abiInfo` of `runtime.newobject`: a pointer type descriptor in a register, one pointer
result. -/
def fnNewABI : CallABI :=
  { abi := 1, nin := 1, nout := 1, spillOff := 8, spillSize := 8, inRegs := 1, outRegs := 1,
    params := #[{ out := false, index := 0, type := 3, name := none, regs := #[0], offset := 0 },
                { out := true, index := 0, type := 5, name := none, regs := #[0], offset := -1 }] }

/-- The `rtype` line of `type:[2]int`: size 16, no pointer bytes. -/
def fnRType : RType :=
  { size := some 16, ptrdata := some 0, hash := some 0, abiKind := some 17,
    gcdata := GoStr.ofString "", elemSym := GoStr.ofString "" }

/-- The type descriptor symbol `type:[2]int` (of the type `[2]int`, type 4). -/
def fnSym : AuxDef :=
  { fmt := GoStr.ofString "type:[2]int",
    kind := .sym (GoStr.ofString "type:[2]int") 0 "" 0 default (some 4) none none #[]
      (some fnRType) }

/-- The call aux of `runtime.newobject`. -/
def fnNewCall : AuxDef :=
  { fmt := GoStr.ofString "AuxCall{runtime.newobject}", kind := .call (some 6) (some fnNewABI) }

/-- The symbol aux of `runtime.newobject`. -/
def fnNewSym : AuxDef :=
  { fmt := GoStr.ofString "runtime.newobject",
    kind := .sym (GoStr.ofString "runtime.newobject") 1 "" 0 default none none none #[] none }

/-- `fmTabs` with the callee `runtime.newobject` (auxes 5, 6), `uintptr` (type 15, the type of
`SB`) and the symbol `type:[2]int` (aux 9). -/
def fnTabs : Tables where
  types := fmTabs.types.set! 15 (some (mkT .UINTPTR (some 8) "uintptr"))
  auxes := ((fmTabs.auxes.set! 5 (some fnNewCall)).set! 6 (some fnNewSym)).push (some fnSym)

/-- `newArr`, the input of `opt`. -/
def fnFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 12
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[12] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 1 #[] 1),
    some (mkV 2 .Arg 3 (some 3) p0 0 #[] 1),
    some (mkV 3 .SB 15 none p0 1 #[] 1),
    some (mkV 4 .Addr 3 (some 9) p0 1 #[3] 1),
    some (mkV 5 .StaticLECall 35 (some 5) p0 2 #[4, 1] 1),
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

/-- `slTyps` with `uintptr` (type 15, the type of `SB`). -/
def fnTyps : Array (String × TypeRef) := slTyps.push ("Uintptr", 15)

def fnPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "newArr", typs := fnTyps, tables := fnTabs }

def fnCheckEnv : CheckEnv := { tabs := fnTabs, typs := fnTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result, which
passes `check`, whose `MakeResult` takes the call's memory `v7`, with no `Store` or `Zero` left in
the block. -/
theorem fn_checks :
    (check fnCheckEnv fnFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet fmRules) fnPassEnv fnFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := fnTyps } o.func).toBool,
        (o.func.value? 12).map (·.args),
        ((o.func.block? 1).map fun b => b.values.toList.filter fun x =>
          (o.func.value? x).any fun v => v.op == .Store || v.op == .Zero))) =
      some (true, some #[6, 7], some []) := by
  decide +kernel

/-- **Pass execution witness** for writes into a `newobject` result (`generic.rules:1352`,
`:1362`): on `newArr`, the checked rewrite pass returns the memory of the allocation
(`v12 = MakeResult v6 v7`), and the result refines the input (`checkedRewrite_refines`, through
`LoadFwd.fwd_refines` under `Env.AllocZero` and `RoImage`). -/
theorem fn_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet fmRules) fnPassEnv fnFunc = .ok out ∧
      (out.func.value? 12).map (·.args) = some #[6, 7] ∧
      check fnCheckEnv fnFunc = .ok () ∧
      check { tabs := out.tables, typs := fnTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre fnPassEnv.tables fnFunc) out.tables out.func
        fnPassEnv.tables fnFunc := by
  obtain ⟨h1, h2⟩ := fn_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet fmRules) fnPassEnv fnFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h12, -⟩ := h2
    exact ⟨out, rfl, h12, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := fmRules) (penv := fnPassEnv)
        (f := fnFunc) (out := out) fmRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

/-- `Env.p1` with the global image's allocation of `type:[2]int` (`Sem.globalImage`'s
`typeDescAlloc`). -/
def fnEnv : Env :=
  { Env.p1 with globals := [("type:[2]int", typeDescAlloc fnTabs 4 (some fnRType))] }

theorem fn_roSyms : RewriteCheck.roSyms fnTabs fnFunc =
    [("type:[2]int", typeDescAlloc fnTabs 4 (some fnRType))] := by
  decide +kernel

/-- **Non-vacuity of `RwPre` with the type descriptor**: on `Env.p1` with the descriptor in the
global image and an empty memory, `newArr`'s read-only symbol holds its image. -/
theorem fn_rwPre (args : List Val) :
    GoFV.Proof.Pass.Rewrite.RwPre fnTabs fnFunc fnEnv args {} := by
  refine ⟨fun n c h => Env.p1_mono n c h, ⟨fun n c hm h => Env.p1_allocNonNil n c hm h, ?_⟩,
    ⟨fun c h => Env.p1_memOps.1 c h, fun c h => Env.p1_memOps.2 c h⟩,
    fun n c hm h => Env.p1_allocZero n c hm h, fun n c h => Env.p1_keepsRo n c h, ?_⟩
  · rw [show NilCheck.dictParams fnTabs fnFunc = [] by decide +kernel]
    exact DictArgs.nil args
  · rw [fn_roSyms]
    intro n a h
    simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by decide +kernel⟩

end GoFV.Proof.Witness
