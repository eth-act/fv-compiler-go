import GoFV.Proof.Witness.FwdGrow

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for a folded `runtime.ifaceeq` call (`generic.rules:2287`, `:1343`, #69, #189)

```go
func eqIface(p, x, y *int) bool {
	// v7 = IMake <error> (Addr {go:itab.*int,error} SB) p: an interface whose itab word is the
	// itab of `*int` (direct-interface and comparable)
	// v9 = StaticLECall {runtime.ifaceeq} (ITab v7) x y mem
	return ifaceeq(ITab(v7), x, y) // v12 = MakeResult (SelectN [0] v9) (SelectN [1] v9)
}
```

as one block, hand-written as opt sees it. The checked rewrite pass with `{:2287, :1343}`
(forwardings, `RuleSet.loads`) folds the call into `MakeResult (EqPtr x y) mem` and its
selections into the `EqPtr` and the memory: the validator accepts the fold because the call's
descriptor is, statically, the start of the itab symbol `go:itab.*int,error`, whose type the
tables mark direct-interface and comparable (`RewriteCheck.eqCallOK`, `eqDescW`, `eqSymOK`),
and a symbol of the precondition's list (`RewriteCheck.eqPass`, `ie_eqPass`); the selections are
checked per instance (`RewriteCheck.selMROK`). The result returns `v13 = EqPtr v4 v5` and the
input memory, and refines the input under `RwPre` (`Sem.Env.IfaceEq`: on such a symbol the call
returns the pointer equality of its data words and its memory). The precondition holds on
`Env.ifaceEqDemo`, which has the call (`ie_rwPre`).
-/

namespace GoFV.SSA.Sem

/-- The contract of a direct-interface comparable `ifaceeq`/`efaceeq` is monotone: the pointer
equality of refined data words is refined (`PtrOps.eqPtr_mono`). -/
theorem Runtime.ifaceEqDirect_mono : Runtime.ifaceEqDirect.Mono := by
  intro args args' clo clo' m m' _ _ ha _ hm
  cases ha with
  | nil => exact .stuck _ _
  | cons h0 t0 =>
    cases t0 with
    | nil => exact .stuck _ _
    | cons h1 t1 =>
      cases t1 with
      | nil => exact .stuck _ _
      | cons h2 t2 =>
        cases t2 with
        | nil => exact .returned (.cons (PtrOps.eqPtr_mono false (.cons h1 (.cons h2 .nil))) .nil) hm
        | cons _ _ => exact .stuck _ _

/-- It returns its memory and a boolean or `poison`. -/
theorem Runtime.ifaceEqDirect_keeps (R : Mem → Mem → Prop) (hR : ∀ m, R m m) :
    Runtime.ifaceEqDirect.Keeps R := by
  intro args clo m rs m' h
  unfold Runtime.ifaceEqDirect at h
  split at h
  · next x y =>
    cases h
    refine ⟨hR _, fun r hr => ?_⟩
    rw [List.mem_singleton] at hr
    subst hr
    simp only [PtrOps.eqPtr]
    split <;> rfl
  · cases h

/-- `Env.ifaceEqDemo` is `Env.p1` but for `runtime.ifaceeq` and `runtime.efaceeq`. -/
theorem Env.ifaceEqDemo_extern_of {n : String}
    (h : ¬(n = "runtime.ifaceeq" ∨ n = "runtime.efaceeq")) :
    Env.ifaceEqDemo.extern n = Env.p1.extern n := ite_eq_right h

theorem Env.ifaceEqDemo_mono : Env.ifaceEqDemo.Mono := by
  intro name c h
  simp only [Env.ifaceEqDemo] at h
  split at h
  · cases h; exact Runtime.ifaceEqDirect_mono
  · exact Env.p1_mono name c h

theorem Env.ifaceEqDemo_keepsRo : Env.ifaceEqDemo.KeepsRo := by
  intro name c h
  simp only [Env.ifaceEqDemo] at h
  split at h
  · cases h; exact Runtime.ifaceEqDirect_keeps _ Mem.KeepsRo.refl
  · exact Env.p1_keepsRo name c h

theorem Env.ifaceEqDemo_allocNonNil : Env.ifaceEqDemo.AllocNonNil := by
  intro name c hm hc
  simp only [Env.ifaceEqDemo] at hc
  split at hc
  · next hn => rcases hn with rfl | rfl <;> exact absurd hm (by decide +kernel)
  · exact Env.p1_allocNonNil name c hm hc

theorem Env.ifaceEqDemo_allocZero : Env.ifaceEqDemo.AllocZero := by
  intro name c hm hc
  simp only [Env.ifaceEqDemo] at hc
  split at hc
  · next hn => rcases hn with rfl | rfl <;> exact absurd hm (by decide +kernel)
  · exact Env.p1_allocZero name c hm hc

theorem Env.ifaceEqDemo_memOps : Env.ifaceEqDemo.MemOps :=
  ⟨fun c h => Env.p1_memOps.1 c (by rwa [Env.ifaceEqDemo_extern_of (by decide +kernel)] at h),
    fun c h => Env.p1_memOps.2 c (by rwa [Env.ifaceEqDemo_extern_of (by decide +kernel)] at h)⟩

theorem Env.ifaceEqDemo_growLen : Env.ifaceEqDemo.GrowLen := fun name c hn hc =>
  Env.p1_growLen name c hn (by
    rcases hn with rfl | rfl <;> rwa [Env.ifaceEqDemo_extern_of (by decide +kernel)] at hc)

end GoFV.SSA.Sem

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- `abiInfo` of `eqIface`: three pointer register parameters, one `bool` result. -/
def ieABI : CallABI :=
  { abi := 1, nin := 3, nout := 1, spillOff := 8, spillSize := 24, inRegs := 3, outRegs := 1,
    params := #[{ out := false, index := 0, type := 3, name := some 3, regs := #[0], offset := 0 },
                { out := false, index := 1, type := 3, name := some 4, regs := #[1], offset := 8 },
                { out := false, index := 2, type := 3, name := some 5, regs := #[2], offset := 16 },
                { out := true, index := 0, type := 4, name := some 6, regs := #[0],
                  offset := -1 }] }

/-- `abiInfo` of `runtime.ifaceeq`: the itab and the two data words in registers, one `bool`
result in a register. -/
def ieCallABI : CallABI :=
  { abi := 1, nin := 3, nout := 1, spillOff := 8, spillSize := 24, inRegs := 3, outRegs := 1,
    params := #[{ out := false, index := 0, type := 24, name := none, regs := #[0], offset := 0 },
                { out := false, index := 1, type := 24, name := none, regs := #[1], offset := 8 },
                { out := false, index := 2, type := 24, name := none, regs := #[2], offset := 16 },
                { out := true, index := 0, type := 4, name := none, regs := #[0],
                  offset := -1 }] }

/-- The itab symbol `go:itab.*int,error` (its type `*int`, type 3). -/
def ieItab : AuxDef :=
  { fmt := GoStr.ofString "go:itab.*int,error",
    kind := .sym (GoStr.ofString "go:itab.*int,error") 0 "SRODATA" 32 default none (some 3) none
      #[] none }

/-- The definition tables: `int` (type 2), `*int` (3, direct-interface and comparable), `bool`
(4), `error` (7), `uintptr` (15), `*uint8` (24), `uint8` (25), `bool,mem` (34); the itab
symbol is aux 9. -/
def ieTabs : Tables where
  types :=
    let t := Array.replicate 36 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(*int, *int, *int) bool" (.func 0 3 1 #[])))
    let t := t.set! 2 (some (mkT .INT (some 8) "int"))
    let t := t.set! 3 (some { mkT .PTR (some 8) "*int" (.elem 2) with
      flags := { direct := true, comparable := true } })
    let t := t.set! 4 (some (mkT .BOOL (some 1) "bool"))
    let t := t.set! 7 (some (mkT .INTER (some 16) "error"))
    let t := t.set! 15 (some (mkT .UINTPTR (some 8) "uintptr"))
    let t := t.set! 24 (some (mkT .PTR (some 8) "*uint8" (.elem 25)))
    let t := t.set! 25 (some (mkT .UINT8 (some 1) "uint8"))
    let t := t.set! 29 (some (mkT .SSA none "mem"))
    let t := t.set! 31 (some (mkT .SSA none "void"))
    t.set! 34 (some (mkT .RESULTS none "bool,mem" (.results #[4, 29])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.eqIface}", kind := .call (some 2) (some ieABI) },
    some { fmt := GoStr.ofString "main.eqIface",
           kind := .sym (GoStr.ofString "main.eqIface") 1 "" 0 default none none none #[] none },
    some (paramNameT "p" .PPARAM 3 0), some (paramNameT "x" .PPARAM 3 8),
    some (paramNameT "y" .PPARAM 3 16), some (paramNameT "~r0" .PPARAMOUT 4 0),
    some { fmt := GoStr.ofString "AuxCall{runtime.ifaceeq}",
           kind := .call (some 8) (some ieCallABI) },
    some { fmt := GoStr.ofString "runtime.ifaceeq",
           kind := .sym (GoStr.ofString "runtime.ifaceeq") 1 "" 0 default none none none #[]
             none },
    some ieItab]

/-- `eqIface`, the input of `opt`. -/
def ieFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 12
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[12] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 1 #[] 1),
    some (mkV 2 .SB 15 none p0 1 #[] 1),
    some (mkV 3 .Arg 3 (some 3) p0 1 #[] 1),
    some (mkV 4 .Arg 3 (some 4) p0 1 #[] 1),
    some (mkV 5 .Arg 3 (some 5) p0 1 #[] 1),
    some (mkV 6 .Addr 24 (some 9) p0 1 #[2] 1),
    some (mkVi 7 .IMake 7 0 p0 1 #[6, 3] 1),
    some (mkVi 8 .ITab 24 0 p0 1 #[7] 1),
    some (mkV 9 .StaticLECall 34 (some 7) p0 2 #[8, 4, 5, 1] 1),
    some (mkVi 10 .SelectN 4 0 p0 1 #[9] 1),
    some (mkVi 11 .SelectN 29 1 p0 1 #[9] 1),
    some (mkVi 12 .MakeResult 34 0 p0 1 #[10, 11] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The rule set `{generic.rules:2287, :1343}`, as forwardings. -/
def ieRules : RuleSet where
  name := "generic"
  values := []
  blocks := []
  loads := [Generated.Generic.r_generic_2287, Generated.Generic.r_generic_1343]

theorem ieRules_allSound : ieRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of trivial trivial

def ieTyps : Array (String × TypeRef) :=
  #[("Int", 2), ("Bool", 4), ("Mem", 29), ("Void", 31), ("Uintptr", 15)]

def iePassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "eqIface", typs := ieTyps, tables := ieTabs }

def ieCheckEnv : CheckEnv := { tabs := ieTabs, typs := ieTyps }

/-- The precondition's descriptor symbols on `eqIface`'s pass: the itab symbol. -/
theorem ie_eqPass :
    RewriteCheck.eqPass iePassEnv.tables iePassEnv.frontend = (["go:itab.*int,error"], []) := by
  decide +kernel

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result, which
passes `check`, that returns `v13 = EqPtr v4 v5` and the input memory. -/
theorem ie_checks :
    (check ieCheckEnv ieFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet ieRules) iePassEnv ieFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := ieTyps } o.func).toBool,
        (o.func.value? 12).map (·.args),
        (o.func.value? 13).map (fun v => (v.op, v.args)))) =
      some (true, some #[13, 1], some (.EqPtr, #[4, 5])) := by
  decide +kernel

/-- **Pass execution witness** for a folded `runtime.ifaceeq` call (`generic.rules:2287`,
`:1343`): on `eqIface`, the checked rewrite pass returns `v13 = EqPtr v4 v5` and the input memory
(`v12 = MakeResult v13 v1`), and the result refines the input under `RwPre`
(`checkedRewrite_refines`, through `LoadFwd.fwd_refines` under `Env.IfaceEq`). -/
theorem ie_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet ieRules) iePassEnv ieFunc = .ok out ∧
      (out.func.value? 12).map (·.args) = some #[13, 1] ∧
      (out.func.value? 13).map (fun v => (v.op, v.args)) = some (.EqPtr, #[4, 5]) ∧
      check ieCheckEnv ieFunc = .ok () ∧
      check { tabs := out.tables, typs := ieTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre iePassEnv.tables iePassEnv.frontend ieFunc)
        out.tables out.func iePassEnv.tables ieFunc := by
  obtain ⟨h1, h2⟩ := ie_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet ieRules) iePassEnv ieFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h12, h13⟩ := h2
    exact ⟨out, rfl, h12, h13, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := ieRules) (penv := iePassEnv)
        (f := ieFunc) (out := out) ieRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

/-- **Non-vacuity of `ie_checkedRewrite`'s precondition**: `RwPre` holds on `Env.ifaceEqDemo`
(`Env.p1` with `runtime.ifaceeq` and `runtime.efaceeq` returning the pointer equality of their
data words, `Env.ifaceEqDemo_ifaceEq`) for pointer arguments from an empty memory. -/
theorem ie_rwPre :
    GoFV.Proof.Pass.Rewrite.RwPre iePassEnv.tables iePassEnv.frontend ieFunc Env.ifaceEqDemo
      [.ptr ⟨.heap 0, 0⟩, .ptr ⟨.heap 1, 0⟩, .ptr ⟨.heap 1, 0⟩] {} :=
  ⟨Env.ifaceEqDemo_mono,
    ⟨Env.ifaceEqDemo_allocNonNil, by
      rw [show NilCheck.dictParams iePassEnv.tables ieFunc = [] by decide +kernel]
      exact DictArgs.nil _⟩,
    Env.ifaceEqDemo_memOps, Env.ifaceEqDemo_allocZero,
    by
      rw [show RewriteCheck.roPass iePassEnv.tables iePassEnv.frontend ieFunc = [] by
        decide +kernel]
      exact RoImage.nil Env.ifaceEqDemo_keepsRo {},
    GoFV.Proof.Pass.Rewrite.initAvoids_empty (fun v hv _ _ => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
      rcases hv with rfl | rfl | rfl <;> intro h <;> cases h) rfl,
    Env.ifaceEqDemo_growLen, Env.ifaceEqDemo_ifaceEq _⟩

end GoFV.Proof.Witness
