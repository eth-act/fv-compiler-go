import GoFV.Proof.Witness.FwdFixed

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for a load from a read-only symbol (issue #69)

```go
func roHalf(t *int) int {
	// v4 = Addr {go:string."ab"} SB: 2 bytes of SRODATA, no relocations
	// v5 = Load <int16> v4 mem  (generic.rules:1572: symIsRO)
	return int(*(*int16)(unsafe.Pointer(unsafe.StringData("ab"))))
	// v6 = SignExt16to64 <int> v5
}
```

as one block. The checked rewrite pass with `{:1572}` (forwardings, `RuleSet.loads`) turns the
`Load` into `Const16 [0x6261]` (`read16` of the symbol's bytes, little-endian): the Load's pointer
is an `Addr` of one of the input's read-only symbols (`RewriteCheck.roSyms`) at offset 0, and the
read there from the symbol's allocation alone (`Sem.rodataAlloc`) is the constant's value
(`RewriteCheck.fixedOK`). The precondition `RwPre` holds on `Env.p1` with the symbol in the
global image (`fr_rwPre`).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- The `SRODATA` symbol `go:string."ab"`: the bytes `0x61 0x62`, no relocations. -/
def frSym : AuxDef :=
  { fmt := GoStr.ofString "go:string.\"ab\"",
    kind := .sym (GoStr.ofString "go:string.\"ab\"") 0 "SRODATA" 2 default none none
      (some (ByteArray.mk #[0x61, 0x62])) #[] none }

/-- `ffTabs` with `int16` (type 16) and the symbol `go:string."ab"` as aux 9. -/
def frTabs : Tables where
  types := ffTabs.types.set! 16 (some (mkT .INT16 (some 2) "int16"))
  auxes := ffTabs.auxes.set! 9 (some frSym)

/-- `fnTyps` with `int16` (type 16, `typ.Int16`). -/
def frTyps : Array (String × TypeRef) := fnTyps.push ("Int16", 16)

/-- `roHalf`, the input of `opt`. -/
def frFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 7
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[7] #[] #[] #[1, 2, 3, 4, 5, 6, 7])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 2 #[] 1),
    some (mkV 2 .Arg 3 (some 3) p0 0 #[] 1),
    some (mkV 3 .SB 15 none p0 1 #[] 1),
    some (mkV 4 .Addr 3 (some 9) p0 1 #[3] 1),
    some (mkV 5 .Load 16 none p0 1 #[4, 1] 1),
    some (mkV 6 .SignExt16to64 2 none p0 1 #[5] 1),
    some (mkVi 7 .MakeResult 35 0 p0 1 #[6, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The rule set `{generic.rules:1572}`, as a forwarding. -/
def frRules : RuleSet where
  name := "generic"
  values := []
  blocks := []
  loads := [Generated.Generic.r_generic_1572]

theorem frRules_allSound : frRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of trivial trivial

def frPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "roHalf", typs := frTyps, tables := frTabs }

def frCheckEnv : CheckEnv := { tabs := frTabs, typs := frTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result, which
passes `check`, where the `Load` `v5` became `Const16 [0x6261]`. -/
theorem fr_checks :
    (check frCheckEnv frFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet frRules) frPassEnv frFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := frTyps } o.func).toBool,
        (o.func.value? 5).map fun v => (v.op, v.auxInt, v.args.size))) =
      some (true, some (.Const16, 0x6261, 0)) := by
  decide +kernel

/-- **Pass execution witness** for a load from a read-only symbol (`generic.rules:1572`): on
`roHalf`, the checked rewrite pass replaces the `Load` by the constant the symbol's bytes hold
(`v5 = Const16 [0x6261]`), and the result refines the input (`checkedRewrite_refines`, through
`LoadFwd.fwd_refines` under `RoImage`). -/
theorem fr_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet frRules) frPassEnv frFunc = .ok out ∧
      (out.func.value? 5).map (fun v => (v.op, v.auxInt, v.args.size)) =
        some (.Const16, 0x6261, 0) ∧
      check frCheckEnv frFunc = .ok () ∧
      check { tabs := out.tables, typs := frTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre frPassEnv.tables frPassEnv.frontend frFunc)
        out.tables out.func
        frPassEnv.tables frFunc := by
  obtain ⟨h1, h2⟩ := fr_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet frRules) frPassEnv frFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h5⟩ := h2
    exact ⟨out, rfl, h5, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := frRules) (penv := frPassEnv)
        (f := frFunc) (out := out) frRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

/-- The global image's allocation of `go:string."ab"` (`Sem.globalImage`'s `rodataAlloc`). -/
def frAlloc : Alloc := rodataAlloc (ByteArray.mk #[0x61, 0x62]) 2 #[]

/-- `Env.p1` with the global image's allocation of `go:string."ab"`. -/
def frEnv : Env := { Env.p1 with globals := [("go:string.\"ab\"", frAlloc)] }

theorem fr_roPass :
    RewriteCheck.roPass frTabs frPassEnv.frontend frFunc = [("go:string.\"ab\"", frAlloc)] := by
  decide +kernel

/-- **Non-vacuity of `RwPre` with the read-only symbol**: on `Env.p1` with the symbol in the
global image and an empty memory, `roHalf`'s read-only symbol holds its image. -/
theorem fr_rwPre (args : List Val) (hargs : ∀ v ∈ args, ∀ a n, v.Avoids (· = .temp a n)) :
    GoFV.Proof.Pass.Rewrite.RwPre frTabs frPassEnv.frontend frFunc frEnv args {} := by
  refine ⟨fun n c h => Env.p1_mono n c h, ⟨fun n c hm h => Env.p1_allocNonNil n c hm h, ?_⟩,
    ⟨fun c h => Env.p1_memOps.1 c h, fun c h => Env.p1_memOps.2 c h⟩,
    fun n c hm h => Env.p1_allocZero n c hm h, ⟨fun n c h => Env.p1_keepsRo n c h, ?_⟩,
    GoFV.Proof.Pass.Rewrite.initAvoids_empty hargs (by decide +kernel) (fun _ h => nomatch h),
    fun n c hn h => Env.p1_growLen n c hn h, fun n c h => Env.p1_ifaceEq _ n c h⟩
  · rw [show NilCheck.dictParams frTabs frFunc = [] by decide +kernel]
    exact DictArgs.nil args
  · rw [fr_roPass]
    intro n a h
    simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by decide +kernel⟩

end GoFV.Proof.Witness
