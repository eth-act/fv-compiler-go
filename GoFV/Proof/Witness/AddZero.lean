import GoFV.Proof.Witness.DecodedLen
import GoFV.Opt.Opt
import GoFV.SSA.Check
import GoFV.Proof.Pass.RewriteCases
import GoFV.Proof.Rules.Add6
import GoFV.Proof.Rules.AllSound
import GoFV.Proof.Witness.Util

/-!
# Witness function for the rewrite passes: `addZero` (hand-written)

```go
func addZero(n int) int {
	return 0 + n
}
```

as the SSA `opt` sees it (one block, `n` an integer register parameter), and the one-rule set
`{generic.rules:646, Add64 instance}`: `(Add64 (Const64 [0]) x) => x`. `checkedRewrite` with
this rule set fires the rule (`v4` becomes `Copy v2`), copy elimination makes the result
`MakeResult v2 v1`, dead-value removal drops `v3` and `v4`, and the validator accepts the log.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `abiInfo` of `addZero`: one integer register parameter, one result. -/
def azABI : CallABI :=
  { abi := 1, nin := 1, nout := 1, spillOff := 8, spillSize := 8, inRegs := 1, outRegs := 1,
    params := #[{ out := false, index := 0, type := 2, name := some 3, regs := #[0], offset := 0 },
                { out := true, index := 0, type := 2, name := some 4, regs := #[0],
                  offset := -1 }] }

/-- The definition tables. -/
def azTabs : Tables where
  types :=
    let t := Array.replicate 36 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(int) int" (.func 0 1 1 #[])))
    let t := t.set! 2 (some (mkT .INT (some 8) "int"))
    let t := t.set! 29 (some (mkT .SSA none "mem"))
    let t := t.set! 31 (some (mkT .SSA none "void"))
    t.set! 35 (some (mkT .RESULTS none "int,mem" (.results #[2, 29])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.addZero}", kind := .call (some 2) (some azABI) },
    some { fmt := GoStr.ofString "main.addZero",
           kind := .sym (GoStr.ofString "main.addZero") 1 "" 0 default none none none #[] none },
    some (paramNameT "n" .PPARAM 2 0), some (paramNameT "~r0" .PPARAMOUT 2 0)]

/-- The values, by ID. -/
def azValues : Array (Option Value) := #[none,
  some (mkVi 1 .InitMem 29 0 p0 1 #[] 1),
  some (mkV 2 .Arg 2 (some 3) p0 1 #[] 1),
  some (mkVi 3 .Const64 2 0 p0 1 #[] 1),
  some (mkVi 4 .Add64 2 0 p0 1 #[3, 2] 1),
  some (mkVi 5 .MakeResult 35 0 p0 1 #[4, 1] 1)]

/-- `addZero`, the input of `opt`. -/
def addZero : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 5
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[5] #[] #[] #[1, 2, 3, 4, 5])]
  valueTab := azValues
  names := #[(1, #[2])]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[(0, #[3])]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The one-rule set: the `Add64` instance of `generic.rules:646`. -/
def azRules : RuleSet where
  name := "generic"
  values := [(.Add64, [Generated.Generic.r_generic_646_3])]
  blocks := []

/-- The pass environment of `opt` (arm64, the export's fixed configuration). -/
def azPassEnv : PassEnv where
  passName := "opt"
  pkg := GoStr.ofString "main"
  funcName := GoStr.ofString "addZero"
  abi := 1
  nosplit := false
  pgohot := false
  config := #[("arch", #[.word "arm64"]), ("ptrsize", #[.word "8"]), ("regsize", #[.word "8"]),
    ("bigendian", #[.word "0"]), ("race", #[.word "0"]), ("archalign", #[.word "1"]),
    ("debugnil", #[.word "0"]), ("zerobase", #[.str (GoStr.ofString "runtime.zerobase")]),
    ("rttype.Size_", #[.word "0:UINTPTR:8"]), ("rttype.PtrBytes", #[.word "8:UINTPTR:8"]),
    ("rttype.Hash", #[.word "16:UINT32:4"]), ("rttype.Kind_", #[.word "23:UINT8:1"]),
    ("rttype.GCData", #[.word "32:PTR:8"]), ("rttype.PtrType.Elem", #[.word "48:PTR:8"])]
  typs := #[("Int", 2), ("Mem", 29), ("Void", 31)]
  typeOrder := default
  tables := azTabs

def azCheckEnv : CheckEnv := { tabs := azTabs, typs := #[("Int", 2), ("Mem", 29)] }

/-- Tables are equal when their four arrays are. -/
private theorem tables_eq {a b : Tables} (h : a.posBases = b.posBases ∧ a.types = b.types ∧
    a.auxes = b.auxes ∧ a.slots = b.slots) : a = b := by
  cases a; cases b; simp_all

/-- By kernel evaluation: the input passes `check`, `checkedRewrite` fires the rule and keeps
its result (`v5 = MakeResult v2 v1`, `v4` dropped) with unchanged tables, the result passes
`check`, and `addZero(7) = 7` in one block entry. -/
theorem addZero_checks :
    (check azCheckEnv addZero).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet azRules) azPassEnv addZero).toOption.map
      (fun o => ((check azCheckEnv o.func).toBool,
        (o.func.value? 5).map (·.args), (o.func.block? 1).map (·.values),
        decide (o.tables.posBases = azTabs.posBases ∧ o.tables.types = azTabs.types ∧
          o.tables.auxes = azTabs.auxes ∧ o.tables.slots = azTabs.slots))) =
      some (true, some #[2, 1], some #[1, 2, 5], true) ∧
    returnsInt (run Env.p1 azTabs addZero [.i64 7] {} 1) 7 = true := by
  decide +kernel


/-- The one-rule set is sound (`generic.rules:646`'s `Add64` lemma). -/
theorem azRules_allSound : azRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of
    ⟨⟨GoFV.Proof.Rules.Rule.checked_of_sound GoFV.Proof.Rules.r_generic_646_3_sound rfl, trivial⟩,
      trivial⟩ trivial

/-- **Pass execution witness**: on `addZero`, the checked rewrite pass with the sound one-rule
set changes the function (`v5 = MakeResult v2 v1`: `0 + n` became `n`), the validator accepted
the result (it is not the input), and input and output pass `check`: the premises of
`GoFV.Proof.Pass.Rewrite.checkedRewrite_refines` hold on a run that rewrites. -/
theorem addZero_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet azRules) azPassEnv addZero = .ok out ∧
      out.tables = azTabs ∧ (out.func.value? 5).map (·.args) = some #[2, 1] ∧
      (∃ log, RewriteCheck.validate azTabs (Interp.Table.ofRuleSet azRules) addZero out.func log =
        true) ∧
      check azCheckEnv addZero = .ok () ∧ check azCheckEnv out.func = .ok () := by
  obtain ⟨h1, h2, -⟩ := addZero_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet azRules) azPassEnv addZero with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h5, -, ht⟩ := h2
    have ht := tables_eq (of_decide_eq_true ht)
    refine ⟨out, rfl, ht, h5, ?_, ok_of_toBool h1, ok_of_toBool hg⟩
    rcases GoFV.Proof.Pass.Rewrite.checkedRewrite_cases_noNil rfl rfl rfl rfl hc with ⟨he, -⟩ | ⟨-, hv⟩
    · rw [he] at h5; exact absurd h5 (by decide +kernel)
    · rw [← ht]; exact hv

end GoFV.Proof.Witness
