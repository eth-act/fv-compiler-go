import GoFV.Proof.Witness.VarDefS3

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness: `generic.rules:2159`, `Zero` over `VarDef (Zero …)` of a result

`f10z2` is `f10vd` (`VarDefS3.lean`) with the result `~r0` (a `PPARAMOUT`) cleared a second time
over the `VarDef`, as `zeroResults`' `VarDef r; Zero r` followed by a clearing assignment:

```go
// v8 = Zero {[2]*S} [16] v5 v7; v9 = VarDef {~r0} v8; v10 = Zero {[2]*S} [16] v5 v9
func f10z2(s *S) (r [2]*S) { r = [2]*S{}; r = [2]*S{}; return }
```

The checked rewrite pass with `{:2159}` (a forwarding, `RuleSet.loads`) turns `v10` into
`Copy v9`, which copy elimination and deadcode then remove: the result is `MakeResult v9`, after
one `Zero`. The `VarDef` of a `PPARAMOUT` is the identity on memory (`Sem.varDefMem`), so `v9`'s
memory holds zeros at `v5` (`RewriteCheck.zeroChain`). The forwarding layer validates it
(`dropOK`) and `LoadFwd.fwd_refines` proves it (`zeroChain_read`). The input returns 16 zero bytes.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules GoFV.Proof

/-- `f10vd` with `v10 = Zero {[2]*S} [16] v5 v9` returned. -/
def f10z2 : Func :=
  { f10vd with
    valueTab := ((f10vd.valueTab.set! 5 (some (mkVa 5 .LocalAddr 37 0 (some 4) p0 2 #[2, 1]))).set!
      10 (some (mkVa 10 .Zero 31 16 (some 5) (pos 2 55 24 1) 1 #[5, 9]))).set!
      23 (some (mkVa 23 .MakeResult 35 0 none (pos 2 55 24 0) 1 #[10]))
    blockTab := #[none, some (mkB 1 .Ret (pos 2 55 24 1) #[23] #[] #[] #[1, 2, 6, 5, 7, 8, 9, 10, 23])]
    freeValues := [12, 17, 21, 22, 24, 3, 4, 14, 18, 13, 11, 15, 16, 19, 20]
    cache := { lineStarts := some #[{ index := 2, bounds := some (55, 55), pending := #[] }] } }

/-- The one-rule set `{generic.rules:2159}`, as a forwarding. -/
def z2Rules : RuleSet where
  name := "generic"
  values := []
  blocks := []
  loads := [Generated.Generic.r_generic_2159]

theorem z2Rules_allSound : z2Rules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of trivial trivial

def z2PassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "f10", typs := f10CheckEnv.typs, tables := f10Tabs }

/-- By kernel evaluation: the input passes `check` and returns 16 zero bytes, and
`checkedRewrite` keeps a result, which passes `check`, whose returned memory is `v9` (the
`VarDef`) and whose only `Zero` is `v8`. -/
theorem z2_checks :
    (check f10CheckEnv f10z2).toBool = true ∧
    returnsBlob (run Env.p1 f10Tabs f10z2 f10Args {} 1) (List.replicate 16 (.b 0)) = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet z2Rules) z2PassEnv f10z2).toOption.map
      (fun o => ((check { tabs := o.tables, typs := f10CheckEnv.typs } o.func).toBool,
        (o.func.value? 23).map (·.args),
        ((o.func.block? 1).map fun b => b.values.toList.filter fun x =>
          (o.func.value? x).any fun v => v.op == .Zero))) =
      some (true, some #[9], some [8]) := by
  decide +kernel

/-- **Pass execution witness** for `generic.rules:2159`: on `f10z2`, the checked rewrite pass
drops the second clearing of the result (the result is `MakeResult v9`, `v8` the only `Zero`),
and the result refines the input (`checkedRewrite_refines`, through `LoadFwd.fwd_refines`). -/
theorem z2_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet z2Rules) z2PassEnv f10z2 = .ok out ∧
      (out.func.value? 23).map (·.args) = some #[9] ∧
      ((out.func.block? 1).map fun b => b.values.toList.filter fun x =>
        (out.func.value? x).any fun v => v.op == .Zero) = some [8] ∧
      check f10CheckEnv f10z2 = .ok () ∧
      check { tabs := out.tables, typs := f10CheckEnv.typs } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre z2PassEnv.tables z2PassEnv.frontend f10z2)
      out.tables out.func z2PassEnv.tables f10z2 := by
  obtain ⟨h1, -, h2⟩ := z2_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet z2Rules) z2PassEnv f10z2 with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h23, hz⟩ := h2
    exact ⟨out, rfl, h23, hz, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := z2Rules) (penv := z2PassEnv)
        (f := f10z2) (out := out) z2Rules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

/-- **Non-vacuity of `z2_checkedRewrite`'s precondition**: `RwPre` holds on `Env.p1` for `f10`'s
pointer argument from an empty memory. -/
theorem z2_rwPre :
    GoFV.Proof.Pass.Rewrite.RwPre z2PassEnv.tables z2PassEnv.frontend f10z2 Env.p1 f10Args {} :=
  GoFV.Proof.Pass.Rewrite.RwPre.p1 (by decide +kernel) (by decide +kernel)
    (GoFV.Proof.Pass.Rewrite.initAvoids_empty (fun v hv _ _ => by
      simp only [f10Args, List.mem_cons, List.mem_nil_iff, or_false] at hv
      subst hv
      intro h; cases h) rfl (fun _ h => nomatch h))

end GoFV.Proof.Witness
