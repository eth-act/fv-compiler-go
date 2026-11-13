import GoFV.Proof.Witness.FwdDrop

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for a write-back of a narrow `Load` (`generic.rules:919`, issue #69)

```go
func writeBack(p *int32) int {
	*p = *p // v3 = Load <int32> p mem; v4 = Store {int32} p v3 mem    (generic.rules:919)
	return 0
}
```

as one block. The checked rewrite pass with `{:919}` (a forwarding, `RuleSet.loads`) turns the
`Store` into a copy of its memory (`RewriteCheck.dropOK`'s `writeBackOK`: the stored value is a
`Load` of the `Store`'s own memory at the same pointer and shape, `int32`); the result's
`MakeResult` takes the function's initial memory.
-/

namespace GoFV.Proof.Witness.FwdWriteBack

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `abiInfo` of `writeBack`: one pointer register parameter, one result. -/
def wbABI : CallABI :=
  { abi := 1, nin := 1, nout := 1, spillOff := 8, spillSize := 8, inRegs := 1, outRegs := 1,
    params := #[{ out := false, index := 0, type := 5, name := some 3, regs := #[0], offset := 0 },
                { out := true, index := 0, type := 2, name := some 4, regs := #[0],
                  offset := -1 }] }

/-- The definition tables: `int32` is type 4 (aux 5), `*int32` type 5. -/
def wbTabs : Tables where
  types :=
    let t := mlTabs.types
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(*int32) int" (.func 0 1 1 #[])))
    let t := t.set! 4 (some (mkT .INT32 (some 4) "int32"))
    t.set! 5 (some (mkT .PTR (some 8) "*int32" (.elem 4)))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.writeBack}", kind := .call (some 2) (some wbABI) },
    some { fmt := GoStr.ofString "main.writeBack",
           kind := .sym (GoStr.ofString "main.writeBack") 1 "" 0 default none none none #[] none },
    some (paramNameT "p" .PPARAM 5 0),
    some (paramNameT "~r0" .PPARAMOUT 2 0),
    some { fmt := GoStr.ofString "int32", kind := .type 4 }]

/-- `writeBack`, the input of `opt`. -/
def wbFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 6
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[6] #[] #[] #[1, 2, 3, 4, 5, 6])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 2 #[] 1),
    some (mkV 2 .Arg 5 (some 3) p0 2 #[] 1),
    some (mkVi 3 .Load 4 0 p0 1 #[2, 1] 1),
    some (mkV 4 .Store 29 (some 5) p0 1 #[2, 3, 1] 1),
    some (mkVi 5 .Const64 2 0 p0 1 #[] 1),
    some (mkVi 6 .MakeResult 35 0 p0 1 #[5, 4] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The rule set `{generic.rules:919}`, as a forwarding. -/
def wbRules : RuleSet where
  name := "generic"
  values := []
  blocks := []
  loads := [Generated.Generic.r_generic_919]

theorem wbRules_allSound : wbRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of trivial trivial

def wbPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "writeBack", typs := slTyps, tables := wbTabs }

def wbCheckEnv : CheckEnv := { tabs := wbTabs, typs := slTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result, which
passes `check`, whose `MakeResult` takes the initial memory `v1`, with no `Store` left in the
block. -/
theorem wb_checks :
    (check wbCheckEnv wbFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet wbRules) wbPassEnv wbFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := slTyps } o.func).toBool,
        (o.func.value? 6).map (·.args),
        ((o.func.block? 1).map fun b => b.values.toList.filter fun x =>
          (o.func.value? x).any fun v => v.op == .Store))) =
      some (true, some #[5, 1], some []) := by
  decide +kernel

/-- **Pass execution witness** for the write-back of a narrow `Load` (`generic.rules:919`): on
`writeBack`, the checked rewrite pass returns the initial memory (`v6 = MakeResult v5 v1`), and the
result refines the input (`checkedRewrite_refines`, through `LoadFwd.fwd_refines` and
`LoadFwd.writeBack_bytes`). -/
theorem wb_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet wbRules) wbPassEnv wbFunc = .ok out ∧
      (out.func.value? 6).map (·.args) = some #[5, 1] ∧
      check wbCheckEnv wbFunc = .ok () ∧
      check { tabs := out.tables, typs := slTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre wbPassEnv.tables wbPassEnv.frontend wbFunc)
        out.tables out.func wbPassEnv.tables wbFunc := by
  obtain ⟨h1, h2⟩ := wb_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet wbRules) wbPassEnv wbFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h6, -⟩ := h2
    exact ⟨out, rfl, h6, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := wbRules) (penv := wbPassEnv)
        (f := wbFunc) (out := out) wbRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

/-- **Non-vacuity of `wb_checkedRewrite`'s precondition**: `RwPre` holds on `Env.p1` for a
pointer argument from an empty memory. -/
theorem wb_rwPre :
    GoFV.Proof.Pass.Rewrite.RwPre wbPassEnv.tables wbPassEnv.frontend wbFunc Env.p1
      [.ptr ⟨.heap 0, 0⟩] {} :=
  GoFV.Proof.Pass.Rewrite.RwPre.p1 (by decide +kernel) (by decide +kernel)
    (GoFV.Proof.Pass.Rewrite.initAvoids_empty (fun v hv _ _ => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
      subst hv
      intro h; cases h) rfl (fun _ h => nomatch h))

/-- **Non-vacuity of `LoadFwd.writeBack_bytes`' conclusion at concrete bytes**: an `int32` read
from the concrete bytes `1 2 3 4` encodes back to them (`encode_decodeLoad_wb`'s first case). -/
theorem wb_encode_concrete :
    encode (.int .w32) ((decodeLoad #[.b 1, .b 2, .b 3, .b 4] 0 (.int .w32)).retype (.int .w32)) =
      #[.b 1, .b 2, .b 3, .b 4] := by
  decide +kernel

end GoFV.Proof.Witness.FwdWriteBack
