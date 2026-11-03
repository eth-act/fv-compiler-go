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
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre lsPassEnv.tables lsPassEnv.frontend lsFunc)
      out.tables out.func
        lsPassEnv.tables lsFunc := by
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
    ⟨⟨.inr (.inr (.inl GoFV.Proof.Rules.r_dec_141_sound)), trivial⟩, trivial⟩ trivial

/-- **Pass execution witness** for `dec.rules:141`: on `loadField`, the checked rewrite pass
makes `(*p).a` a copy of a fresh `Load <int>` at the field's offset, and the result refines the
input (`checkedRewrite_refines`, through `LSFacts.step`). -/
theorem lsel_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet lselRules) lfPassEnv lfFunc = .ok out ∧
      (((out.func.value? 5).bind (·.args[0]?)).bind out.func.value?).map (·.op == Op.Load) =
        some true ∧
      check { tabs := out.tables, typs := slTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre lfPassEnv.tables lfPassEnv.frontend lfFunc)
      out.tables out.func
        lfPassEnv.tables lfFunc := by
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

/-! ## `(ITab x:(Load <t> ptr mem))` typed `*uint8` (`dec.rules:144`, issue #17)

`itabOf` as decompose builtin sees it (one block: `v3 = Load <interface {}> v2 v1`,
`v4 = ITab <*uint8> v3`, the itab word of `*p` as Go's type switches read it) with the one-rule
set `{dec.rules:144}`: `(ITab x:(Load <t> ptr mem)) && t.IsInterface() => @x.Block (Load
<typ.Uintptr> ptr mem)`. The interface's itab word has the `uintptr` shape `.int .w64`, not the
`ITab`'s pointer shape; a 64-bit integer has every pointer shape (`Val.hasTy`), so the top check
accepts it (`RewriteCheck.compSub`, `selTop`). -/

/-- `abiInfo` of `itabOf`: one pointer register parameter, one pointer result. -/
def itaABI : CallABI :=
  { abi := 1, nin := 1, nout := 1, spillOff := 8, spillSize := 8, inRegs := 1, outRegs := 1,
    params := #[{ out := false, index := 0, type := 3, name := some 3, regs := #[0], offset := 0 },
                { out := true, index := 0, type := 6, name := some 4, regs := #[0],
                  offset := -1 }] }

/-- The definition tables: `uintptr` (2), `*interface {}` (3), `interface {}` (4), `uint8` (5),
`*uint8` (6). -/
def itaTabs : Tables where
  types :=
    let t := Array.replicate 36 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(*interface {}) *uint8" (.func 0 1 1 #[])))
    let t := t.set! 2 (some (mkT .UINTPTR (some 8) "uintptr"))
    let t := t.set! 3 (some (mkT .PTR (some 8) "*interface {}" (.elem 4)))
    let t := t.set! 4 (some (mkT .INTER (some 16) "interface {}"))
    let t := t.set! 5 (some (mkT .UINT8 (some 1) "uint8"))
    let t := t.set! 6 (some (mkT .PTR (some 8) "*uint8" (.elem 5)))
    let t := t.set! 29 (some (mkT .SSA none "mem"))
    let t := t.set! 31 (some (mkT .SSA none "void"))
    t.set! 35 (some (mkT .RESULTS none "*uint8,mem" (.results #[6, 29])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.itabOf}", kind := .call (some 2) (some itaABI) },
    some { fmt := GoStr.ofString "main.itabOf",
           kind := .sym (GoStr.ofString "main.itabOf") 1 "" 0 default none none none #[] none },
    some (paramNameT "p" .PPARAM 3 0),
    some (paramNameT "~r0" .PPARAMOUT 6 0)]

/-- `itabOf`, the input of the rewrite step. -/
def itaFunc : Func :=
  { lsFunc with
    valueTab := #[none,
      some (mkVi 1 .InitMem 29 0 p0 2 #[] 1),
      some (mkV 2 .Arg 3 (some 3) p0 1 #[] 1),
      some (mkVi 3 .Load 4 0 p0 1 #[2, 1] 1),
      some (mkVi 4 .ITab 6 0 p0 1 #[3] 1),
      some (mkVi 5 .MakeResult 35 0 p0 1 #[4, 1] 1)] }

/-- The one-rule set `{dec.rules:144}`. -/
def itaRules : RuleSet where
  name := "dec"
  values := [(.ITab, [Generated.Dec.r_dec_144])]
  blocks := []

def itaTyps : Array (String × TypeRef) :=
  #[("Uintptr", 2), ("BytePtr", 6), ("Mem", 29), ("Void", 31)]

def itaPassEnv : PassEnv :=
  { lsPassEnv with funcName := GoStr.ofString "itabOf", typs := itaTyps, tables := itaTabs }

def itaCheckEnv : CheckEnv := { tabs := itaTabs, typs := itaTyps }

/-- By kernel evaluation: the input passes `check`; `checkedRewrite` keeps a result whose
`MakeResult` returns a fresh `Load` (the `ITab`'s copy of it is gone), which passes `check`; the
itab word's shape is not the `ITab`'s (`shapeSub`), only `compSub` relates them. -/
theorem ita_checks :
    (check itaCheckEnv itaFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet itaRules) itaPassEnv itaFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := itaTyps } o.func).toBool,
        (((o.func.value? 5).bind (·.args[0]?)).bind o.func.value?).map (·.op == Op.Load))) =
      some (true, some true) ∧
    GoFV.Proof.Rules.shapeSub (.int .w64) (itaTabs.ty 6) = false ∧
    RewriteCheck.compSub (.int .w64) (itaTabs.ty 6) = true := by
  decide +kernel

theorem itaRules_allSound : itaRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of
    ⟨⟨GoFV.Proof.Rules.Rule.checked_of_sound GoFV.Proof.Rules.r_dec_144_sound rfl, trivial⟩,
      trivial⟩ trivial

/-- **Pass execution witness** for `dec.rules:144` at a pointer-typed `ITab`: on `itabOf`, the
checked rewrite pass makes the `ITab <*uint8>` of `*p` a copy of a fresh `Load <uintptr>` of the
itab word, which the result returns, and the result refines the input (`checkedRewrite_refines`,
through `r_dec_144_sound`, `selTop` by `compSub`, and `blockTopOK`). -/
theorem ita_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet itaRules) itaPassEnv itaFunc = .ok out ∧
      (((out.func.value? 5).bind (·.args[0]?)).bind out.func.value?).map (·.op == Op.Load) =
        some true ∧
      check itaCheckEnv itaFunc = .ok () ∧
      check { tabs := out.tables, typs := itaTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre itaPassEnv.tables itaPassEnv.frontend itaFunc)
      out.tables out.func
        itaPassEnv.tables itaFunc := by
  obtain ⟨h1, h2, -⟩ := ita_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet itaRules) itaPassEnv itaFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h3⟩ := h2
    exact ⟨out, rfl, h3, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := itaRules) (penv := itaPassEnv)
        (f := itaFunc) (out := out) itaRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

end GoFV.Proof.Witness
