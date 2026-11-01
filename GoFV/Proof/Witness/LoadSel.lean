import GoFV.Proof.Witness.LoadSplit
import GoFV.Proof.Rules.DecLoadSel

/-!
# Witness functions for the dec extractors of a `Load` (hand-written, issue #17)

`strLen` (`GoFV.Proof.Witness.LoadSplit`: `v4 = StringLen (Load <string> v2 v1)`) with the
one-rule set `{dec.rules:136}`: `(StringLen x:(Load <t> ptr mem)) && t.IsString() => @x.Block
(Load <typ.Int> (OffPtr <typ.IntPtr> [config.PtrSize] ptr) mem)` (`r_dec_136_sound`, an `@b`
result: `v4` becomes a copy of a fresh `Load`, `RewriteCheck.blockTopOK`), and `loadField`
(`GoFV.Proof.Witness.StructLoad`: `v4 = StructSelect [0] (Load <P> v2 v1)`) with
`{dec.rules:141}`: `(StructSelect [i] x:(Load <t> ptr mem)) => @x.Block (Load <v.Type> (OffPtr
<v.Type.PtrTo()> [t.FieldOff(int(i))] ptr) mem)` (`Rule.LoadSel`, validated per instance by
`RewriteCheck.loadSelOK`). In both, `checkedRewrite` fires the rule, the validator accepts the
event and the result refines the input.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- The one-rule set `{dec.rules:136}`. -/
def xsRules : RuleSet where
  name := "dec"
  values := [(.StringLen, [Generated.Dec.r_dec_136])]
  blocks := []

/-- By kernel evaluation: `checkedRewrite` keeps a result whose `MakeResult` returns a fresh `Load`, which passes
`check`. -/
theorem xs_checks :
    (checkedRewrite (Interp.Table.ofRuleSet xsRules) lsPassEnv lsFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := lsTyps } o.func).toBool,
        (((o.func.value? 5).bind (·.args[0]?)).bind o.func.value?).map (·.op == Op.Load))) =
      some (true, some true) := by
  decide +kernel

theorem xsRules_allSound : xsRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of
    ⟨⟨GoFV.Proof.Rules.Rule.checked_of_sound GoFV.Proof.Rules.r_dec_136_sound rfl, trivial⟩,
      trivial⟩ trivial

/-- **Pass execution witness** for `dec.rules:136` (an `@x.Block` result): on `strLen`, the
checked rewrite pass makes `len(*p)` a copy of a fresh `Load` of the length word, and the result
refines the input (`checkedRewrite_refines`, through `r_dec_136_sound` and `blockTopOK`). -/
theorem xs_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet xsRules) lsPassEnv lsFunc = .ok out ∧
      (((out.func.value? 5).bind (·.args[0]?)).bind out.func.value?).map (·.op == Op.Load) =
        some true ∧
      check { tabs := out.tables, typs := lsTyps } out.func = .ok () ∧
      RefinesUnder Env.Mono out.tables out.func lsPassEnv.tables lsFunc := by
  have h1 := ls_checks.1
  have h2 := xs_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet xsRules) lsPassEnv lsFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h3⟩ := h2
    exact ⟨out, rfl, h3, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := xsRules) (penv := lsPassEnv)
        (f := lsFunc) (out := out) xsRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

/-- The one-rule set `{dec.rules:141}`. -/
def lselRules : RuleSet where
  name := "dec"
  values := [(.StructSelect, [Generated.Dec.r_dec_141])]
  blocks := []

/-- By kernel evaluation: `checkedRewrite` keeps a result whose `MakeResult` returns a fresh `Load`, which passes
`check`. -/
theorem lsel_checks :
    (checkedRewrite (Interp.Table.ofRuleSet lselRules) lfPassEnv lfFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := slTyps } o.func).toBool,
        (((o.func.value? 5).bind (·.args[0]?)).bind o.func.value?).map (·.op == Op.Load))) =
      some (true, some true) := by
  decide +kernel

theorem lselRules_allSound : lselRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of
    ⟨⟨.inr (.inr GoFV.Proof.Rules.r_dec_141_sound), trivial⟩, trivial⟩ trivial

/-- **Pass execution witness** for `dec.rules:141`: on `loadField`, the checked rewrite pass
makes `(*p).a` a copy of a fresh `Load <int>` at the field's offset, and the result refines the
input (`checkedRewrite_refines`, through `LSFacts.step`). -/
theorem lsel_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet lselRules) lfPassEnv lfFunc = .ok out ∧
      (((out.func.value? 5).bind (·.args[0]?)).bind out.func.value?).map (·.op == Op.Load) =
        some true ∧
      check { tabs := out.tables, typs := slTyps } out.func = .ok () ∧
      RefinesUnder Env.Mono out.tables out.func lfPassEnv.tables lfFunc := by
  have h1 := lf_checks.1
  have h2 := lsel_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet lselRules) lfPassEnv lfFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h3⟩ := h2
    exact ⟨out, rfl, h3, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := lselRules) (penv := lfPassEnv)
        (f := lfFunc) (out := out) lselRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

end GoFV.Proof.Witness
