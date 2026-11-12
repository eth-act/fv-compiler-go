import GoFV.Proof.Witness.AddZero
import GoFV.Proof.Rules.BlockIf
import GoFV.Proof.Pass.Rewrite

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness of `checkedRewrite_refines` on a block rule: `notIf` (hand-written)

```go
func notIf(b bool) int {
	if !b {
		return 1
	}
	return 2
}
```

as the SSA `opt` sees it (entry `If (Not b)`, two `Ret` blocks), and the one-block-rule set
`{generic.rules:1064}`: `(If (Not cond) yes no) => (If cond no yes)`. `checkedRewrite` fires the
block rule (the entry becomes `If v2` with its successors swapped), dead-value removal drops the
`Not`, and the validator accepts the log (it replays the terminator: the control rule
`(Not cond) => (Not cond)` fires at `v3`). By `checkedRewrite_refines` the output returns
`notIf(false) = 1`, as the source does.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- `abiInfo` of `notIf`: one boolean register parameter, one integer result. -/
def niABI : CallABI :=
  { abi := 1, nin := 1, nout := 1, spillOff := 8, spillSize := 8, inRegs := 1, outRegs := 1,
    params := #[{ out := false, index := 0, type := 4, name := some 3, regs := #[0], offset := 0 },
                { out := true, index := 0, type := 2, name := some 4, regs := #[0],
                  offset := -1 }] }

/-- The definition tables. -/
def niTabs : Tables where
  types :=
    let t := Array.replicate 36 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(bool) int" (.func 0 1 1 #[])))
    let t := t.set! 2 (some (mkT .INT (some 8) "int"))
    let t := t.set! 4 (some (mkT .BOOL (some 1) "bool"))
    let t := t.set! 29 (some (mkT .SSA none "mem"))
    let t := t.set! 31 (some (mkT .SSA none "void"))
    t.set! 35 (some (mkT .RESULTS none "int,mem" (.results #[2, 29])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.notIf}", kind := .call (some 2) (some niABI) },
    some { fmt := GoStr.ofString "main.notIf",
           kind := .sym (GoStr.ofString "main.notIf") 1 "" 0 default none none none #[] none },
    some (paramNameT "b" .PPARAM 4 0), some (paramNameT "~r0" .PPARAMOUT 2 0)]

/-- The values, by ID. -/
def niValues : Array (Option Value) := #[none,
  some (mkVi 1 .InitMem 29 0 p0 2 #[] 1),
  some (mkV 2 .Arg 4 (some 3) p0 1 #[] 1),
  some (mkVi 3 .Not 4 0 p0 1 #[2] 1),
  some (mkVi 4 .Const64 2 1 p0 1 #[] 2),
  some (mkVi 5 .MakeResult 35 0 p0 1 #[4, 1] 2),
  some (mkVi 6 .Const64 2 2 p0 1 #[] 3),
  some (mkVi 7 .MakeResult 35 0 p0 1 #[6, 1] 3)]

/-- `notIf`, the input of `opt`. -/
def notIf : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 7
  bidLast := 3
  blocks := #[1, 2, 3]
  blockTab := #[none,
    some (mkB 1 .If p0 #[3] #[⟨2, 0⟩, ⟨3, 0⟩] #[] #[1, 2, 3]),
    some (mkB 2 .Ret p0 #[5] #[] #[⟨1, 0⟩] #[4, 5]),
    some (mkB 3 .Ret p0 #[7] #[] #[⟨1, 1⟩] #[6, 7])]
  valueTab := niValues
  names := #[(1, #[2])]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[(1, #[4]), (2, #[6])]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The one-block-rule set: `generic.rules:1064`. -/
def niRules : RuleSet where
  name := "generic"
  values := []
  blocks := [(.If, [Generated.Generic.r_generic_1064])]

/-- The pass environment of `opt` (as `azPassEnv`, with `notIf`'s tables). -/
def niPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "notIf",
                   typs := #[("Bool", 4), ("Int", 2), ("Mem", 29), ("Void", 31)],
                   tables := niTabs }

def niCheckEnv : CheckEnv := { tabs := niTabs, typs := #[("Int", 2), ("Mem", 29)] }

/-- By kernel evaluation: the input passes `check`, `checkedRewrite` fires the block rule (the
entry block is `If v2` with successors `b3, b2`; `v3` is dropped), the result passes `check`,
and `notIf(false) = 1`. -/
theorem notIf_checks :
    (check niCheckEnv notIf).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet niRules) niPassEnv notIf).toOption.map
      (fun o => ((check niCheckEnv o.func).toBool,
        (o.func.block? 1).map (fun b => (b.controls, b.succs.map (·.b))))) =
      some (true, some (#[2], #[3, 2])) ∧
    (checkedRewrite (Interp.Table.ofRuleSet niRules) niPassEnv notIf).toOption.map
      (fun o => (o.func.block? 1).map (fun b => (b.kind, b.values))) =
      some (some (.If, #[1, 2])) ∧
    returnsInt (run Env.p1 niTabs notIf [.bool false] {} 2) 1 = true := by
  decide +kernel

/-- The one-block-rule set is sound (`generic.rules:1064`'s lemma). -/
theorem niRules_allSound : niRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of trivial
    ⟨⟨GoFV.Proof.Rules.r_generic_1064_sound, trivial⟩, trivial⟩

/-- **Block-rule witness**: on `notIf`, the checked rewrite pass with the sound one-block-rule
set swaps the entry's successors onto `If v2` (the validator accepted a result that is not the
input), and by `checkedRewrite_refines` the output returns `notIf(false) = 1`. -/
theorem notIf_refines :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet niRules) niPassEnv notIf = .ok out ∧
      (out.func.block? 1).map (fun b => (b.controls, b.succs.map (·.b))) =
        some (#[2], #[3, 2]) ∧
      RefinesFrom (Pass.Rewrite.RwPre niTabs niPassEnv.frontend notIf) out.tables out.func
        niTabs notIf ∧
      ∃ fuel m, run Env.p1 out.tables out.func [.bool false] {} fuel = .returned [.i64 1] m := by
  obtain ⟨h1, h2, -, h3⟩ := notIf_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet niRules) niPassEnv notIf with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, hb⟩ := h2
    have hR := GoFV.Proof.Pass.Rewrite.checkedRewrite_refines niRules_allSound hc
      (ok_of_toBool h1) (ok_of_toBool hg)
    rw [show niPassEnv.tables = niTabs from rfl] at hR
    refine ⟨out, rfl, ?_, hR, ?_⟩
    · revert hb
      cases out.func.block? 1 <;> simp_all
    · obtain ⟨m, hm⟩ := returnsInt_iff.1 h3
      obtain ⟨fuel', ho⟩ := hR Env.p1 [.bool false] {}
        (Pass.Rewrite.RwPre.p1 (by decide +kernel) (by decide +kernel)
          (Pass.Rewrite.initAvoids_empty (fun v hv _ _ => by
            simp only [List.mem_singleton] at hv; subst hv; trivial) rfl (fun _ h => nomatch h)))
              2 (by rw [hm]; trivial)
      rw [hm] at ho
      refine ⟨fuel', ?_⟩
      generalize run Env.p1 out.tables out.func [.bool false] {} fuel' = o at ho ⊢
      cases ho with
      | returned hl =>
        cases hl with
        | cons h1 t =>
          cases t
          cases h1
          exact ⟨_, rfl⟩

end GoFV.Proof.Witness
