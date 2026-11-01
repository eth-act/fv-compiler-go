import GoFV.Proof.Witness.FwdDrop

/-!
# Witness function for a changed `Move` source (issue #151)

```go
func moveVia() {
	var s, t, d [2]int // frame variables (PAUTO)
	s = [2]int{}       // v4 = Zero {[2]int} [16] &s mem
	t = s              // v6 = Move {[2]int} [16] &t &s v4
	                   // v7 = VarDef {d} v6
	d = t              // v9 = Move {[2]int} [16] &d &t v7   (generic.rules:2155)
}
```

as one block. The checked rewrite pass with `{:2155}` (a forwarding, `RuleSet.loads`) makes `v9`
copy from `s` instead of `t`: `t` holds `s`'s bytes after `v6`, `s` and `t` are separate frame
variables, and the `VarDef` poisons `d`, neither of them (`RewriteCheck.moveSrcOK`). The
forwarding layer validates it (`fwdRel`) and `LoadFwd.fwd_refines` proves it (a changed root of the
atom simulation, `AtomSim.ChgRefP`, `LoadFwd.moveSrc_chgRef`).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `abiInfo` of `moveVia`: no parameters, no results. -/
def mvABI : CallABI :=
  { abi := 1, nin := 0, nout := 0, spillOff := 8, spillSize := 0, inRegs := 0, outRegs := 0,
    params := #[] }

/-- The definition tables: `[2]int` is type 4 (aux 3), `*[2]int` type 5, `uintptr` type 15, the
frame variables `s`, `t`, `d` auxes 4, 5, 6; the results type 32 (`mem`). -/
def mvTabs : Tables where
  types :=
    let t := mlTabs.types
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func()" (.func 0 0 0 #[])))
    let t := t.set! 15 (some (mkT .UINTPTR (some 8) "uintptr"))
    t.set! 32 (some (mkT .RESULTS none "mem" (.results #[29])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.moveVia}", kind := .call (some 2) (some mvABI) },
    some { fmt := GoStr.ofString "main.moveVia",
           kind := .sym (GoStr.ofString "main.moveVia") 1 "" 0 default none none none #[] none },
    some { fmt := GoStr.ofString "[2]int", kind := .type 4 },
    some (paramNameT "s" .PAUTO 4 0), some (paramNameT "t" .PAUTO 4 0),
    some (paramNameT "d" .PAUTO 4 0)]

/-- `moveVia`, the input of `opt`. -/
def mvFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 10
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[10] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 2 #[] 1),
    some (mkVi 2 .SP 15 0 p0 3 #[] 1),
    some (mkV 3 .LocalAddr 5 (some 4) p0 2 #[2, 1] 1),
    some { mkV 4 .Zero 29 (some 3) p0 2 #[3, 1] 1 with auxInt := 16 },
    some (mkV 5 .LocalAddr 5 (some 5) p0 2 #[2, 4] 1),
    some { mkV 6 .Move 29 (some 3) p0 1 #[5, 3, 4] 1 with auxInt := 16 },
    some (mkV 7 .VarDef 29 (some 6) p0 2 #[6] 1),
    some (mkV 8 .LocalAddr 5 (some 6) p0 1 #[2, 7] 1),
    some { mkV 9 .Move 29 (some 3) p0 1 #[8, 5, 7] 1 with auxInt := 16 },
    some (mkVi 10 .MakeResult 32 0 p0 1 #[9] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

def mvTyps : Array (String × TypeRef) :=
  #[("Int", 2), ("Uintptr", 15), ("Mem", 29), ("Void", 31)]

/-- The one-rule set `{generic.rules:2155}`, as a forwarding. -/
def mvRules : RuleSet where
  name := "generic"
  values := []
  blocks := []
  loads := [Generated.Generic.r_generic_2155]

theorem mvRules_allSound : mvRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of trivial trivial

def mvPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "moveVia", typs := mvTyps, tables := mvTabs }

def mvCheckEnv : CheckEnv := { tabs := mvTabs, typs := mvTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result, which
passes `check`, whose last `Move` `v9` copies from `s` (`v3`) in the `VarDef`'s memory `v7`. -/
theorem mv_checks :
    (check mvCheckEnv mvFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet mvRules) mvPassEnv mvFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := mvTyps } o.func).toBool,
        (o.func.value? 9).map (·.args))) =
      some (true, some #[8, 3, 7]) := by
  decide +kernel

/-- **Pass execution witness** for a changed `Move` source (`generic.rules:2155`): on `moveVia`,
the checked rewrite pass makes `d = t` copy from `s` (`v9 = Move {[2]int} [16] v8 v3 v7`), and the
result refines the input (`checkedRewrite_refines`, through `LoadFwd.fwd_refines`). -/
theorem mv_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet mvRules) mvPassEnv mvFunc = .ok out ∧
      (out.func.value? 9).map (·.args) = some #[8, 3, 7] ∧
      check mvCheckEnv mvFunc = .ok () ∧
      check { tabs := out.tables, typs := mvTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre mvPassEnv.tables mvFunc) out.tables out.func
        mvPassEnv.tables mvFunc := by
  obtain ⟨h1, h2⟩ := mv_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet mvRules) mvPassEnv mvFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h9⟩ := h2
    exact ⟨out, rfl, h9, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := mvRules) (penv := mvPassEnv)
        (f := mvFunc) (out := out) mvRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

end GoFV.Proof.Witness
