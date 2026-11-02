import GoFV.Proof.Witness.MakeSel
import GoFV.Proof.Witness.DecStore

/-!
# Witness function for selections of dropped nested `Make`s: `nest` (hand-written, issue #17)

```go
type Q struct{ p *int }
type R struct{ q Q }

func nest(p *int) *int {
	r := R{Q{p}}
	s := R{Q{r.q.p}}
	return s.q.p
}
```

as decompose builtin sees it (one block, listed in the order `v3 = StructMake <Q> v2`,
`v4 = StructMake <R> v3`, `v5 = StructSelect <Q> [0] v4`, `v6 = StructSelect <*int> [0] v5`,
`v8 = StructMake <R> v7`, `v7 = StructMake <Q> v6`, `v9 = StructSelect <Q> [0] v8`,
`v10 = StructSelect <*int> [0] v9`, `v11 = MakeResult v10 v1`). The proven dec rules drop the
one-pointer `StructMake`s `v3`, `v4`, `v7` (`dec.rules:120`, `Rule.Drop`: the replay keeps them).
Go then rewrites `v5`, whose argument it replaced by `p`, by `dec.rules:115` to `Copy <Q> v2`,
which the replay does not validate and skips (`lax`); `v6` is accepted as a selection of `v3`
through the kept selection `v5` of `v4` (`RewriteCheck.selRes`), `v10` through the copy `v9` of
`v7` (`:106`). The output keeps the dead `v8 = StructMake <R> v7` with `v7 = Copy v2`: `v7`
differs from its replayed definition, but only the unread `v8` reads it (`RewriteCheck.liveOK`).
The checks of `main` before issue #17's class 3 reject this run.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.Decompose GoFV.Proof GoFV.Proof.Decompose GoFV.Rules

/-- The definition tables: `drpTabs` (`*int` type 3, `Q` type 4) and `R` (type 5) is
`struct { q Q }`. -/
def nstTabs : Tables :=
  { drpTabs with types := drpTabs.types.set! 5 (some (mkT .STRUCT (some 8) "R"
      (.struct #[{ name := GoStr.ofString "q", type := 4, offset := some 0, embedded := false }]))) }

/-- `nest`. -/
def nstFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 11
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[11] #[] #[] #[1, 2, 3, 4, 5, 6, 8, 7, 9, 10, 11])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 1 #[] 1),
    some (mkV 2 .Arg 3 (some 3) p0 1 #[] 1),
    some (mkVi 3 .StructMake 4 0 p0 1 #[2] 1),
    some (mkVi 4 .StructMake 5 0 p0 1 #[3] 1),
    some (mkVi 5 .StructSelect 4 0 p0 1 #[4] 1),
    some (mkVi 6 .StructSelect 3 0 p0 1 #[5] 1),
    some (mkVi 7 .StructMake 4 0 p0 1 #[6] 1),
    some (mkVi 8 .StructMake 5 0 p0 1 #[7] 1),
    some (mkVi 9 .StructSelect 4 0 p0 1 #[8] 1),
    some (mkVi 10 .StructSelect 3 0 p0 1 #[9] 1),
    some (mkVi 11 .MakeResult 35 0 p0 1 #[10, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

def nstPassEnv : PassEnv :=
  { azPassEnv with passName := "decompose builtin", funcName := GoStr.ofString "nest",
                   typs := slTyps, tables := nstTabs }

/-- The block's values of `g` as (ID, op, arguments). -/
def nstShape (g : Func) : List (ID × Op × List ID) :=
  (g.block? 1).elim [] fun b => b.values.toList.filterMap fun x =>
    (g.value? x).map fun v => (v.id, v.op, v.args.toList)

/-- By kernel evaluation: the input passes `check`; the proven dec rules' rewrite leaves the dead
`StructMake <R> v7` over `v7 = Copy v2` and returns `p`, and the decompose builtin stage checks
accept it (with the input as its own phi stage: it has no `Phi`). -/
theorem nst_stages :
    (check { tabs := nstTabs, typs := slTyps } nstFunc).toBool = true ∧
    (match Rules.rewriteRun decProvenTable false true nstPassEnv nstFunc with
      | .ok (o, _, log) =>
        decBuiltinStagesOK nstPassEnv nstFunc nstFunc o.func log o &&
          nstShape o.func == [(1, .InitMem, []), (2, .Arg, []), (8, .StructMake, [7]),
            (7, .Copy, [2]), (11, .MakeResult, [2, 1])]
      | .error _ => false) = true := by
  decide +kernel

/-- **Pass execution witness** for selections of dropped nested `Make`s (issue #17, class 3): on
`nest`, the proven dec rules' rewrite returns `p`, keeping a dead `StructMake` over a dropped
one, and the result refines the input for `DecPre` (`refinesFrom_of_decBuiltinStagesOK`, through
`Pass.Rewrite.validate_termRef`: the `lax` replay, `selRes` in `makeSelOK`, `liveOK` in
`finalOK`). -/
theorem decNested_witness :
    ∃ o n log, Rules.rewriteRun decProvenTable false true nstPassEnv nstFunc = .ok (o, n, log) ∧
      nstShape o.func = [(1, .InitMem, []), (2, .Arg, []), (8, .StructMake, [7]),
        (7, .Copy, [2]), (11, .MakeResult, [2, 1])] ∧
      RefinesFrom DecPre o.tables o.func nstTabs nstFunc := by
  obtain ⟨hcf, h⟩ := nst_stages
  cases hr : Rules.rewriteRun decProvenTable false true nstPassEnv nstFunc with
  | error e => rw [hr] at h; cases h
  | ok r =>
    obtain ⟨o, n, log⟩ := r
    rw [hr] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hok, hs⟩ := h
    have r := refinesFrom_of_decBuiltinStagesOK hok (ok_of_toBool hcf)
    rw [show nstPassEnv.tables = nstTabs from rfl] at r
    exact ⟨o, n, log, rfl, hs, r⟩

end GoFV.Proof.Witness
