import GoFV.Proof.Witness.FwdNew

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function for a fixed load from a read-only symbol (issue #69)

```go
func dictEntry(t *int) *[2]int {
	// v4 = Addr {main..dict.f} SB: 16 bytes of SRODATA, an R_ADDR relocation to main.T at 8
	return *(**[2]int)(unsafe.Add(unsafe.Pointer(&main..dict.f), 8))
	// v6 = Load <*[2]int> (OffPtr [8] v4) mem  (generic.rules:2255: isFixedLoad)
}
```

as one block. The checked rewrite pass with `{:2255}` (forwardings, `RuleSet.loads`) turns the
`Load` into `Addr {main.T} SB` (`rewriteFixedLoad`): the Load's pointer is an `Addr` of one of the
input's read-only symbols (`RewriteCheck.roSyms`) at offset 8, and the read there from the
symbol's allocation alone (`Sem.rodataAlloc`: the relocation as a pointer to `main.T`) is the
`Addr`'s value (`RewriteCheck.fixedOK`). The precondition `RwPre` holds on `Env.p1` with the
symbol in the global image (`ff_rwPre`).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- The relocation of `main..dict.f` at offset 8 to `main.T`. -/
def ffReloc : Reloc :=
  { off := 8, siz := 8, type := "R_ADDR", add := 0, target := GoStr.ofString "main.T",
    targetAbi := 0 }

/-- The `SRODATA` symbol `main..dict.f`: 16 zero bytes, the relocation at 8. -/
def ffSym : AuxDef :=
  { fmt := GoStr.ofString "main..dict.f",
    kind := .sym (GoStr.ofString "main..dict.f") 0 "SRODATA" 16 default none none
      (some (ByteArray.mk (Array.replicate 16 0))) #[ffReloc] none }

/-- `fnTabs` with the symbol `main..dict.f` as aux 9. -/
def ffTabs : Tables where
  types := fnTabs.types
  auxes := fnTabs.auxes.set! 9 (some ffSym)

/-- `dictEntry`, the input of `opt`. -/
def ffFunc : Func where
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
    some (mkVi 5 .OffPtr 3 8 p0 1 #[4] 1),
    some (mkV 6 .Load 5 none p0 1 #[5, 1] 1),
    some (mkVi 7 .MakeResult 35 0 p0 1 #[6, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The rule set `{generic.rules:2255}`, as a forwarding. -/
def ffRules : RuleSet where
  name := "generic"
  values := []
  blocks := []
  loads := [Generated.Generic.r_generic_2255]

theorem ffRules_allSound : ffRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of trivial trivial

def ffPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "dictEntry", typs := fnTyps, tables := ffTabs }

def ffCheckEnv : CheckEnv := { tabs := ffTabs, typs := fnTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result, which
passes `check`, where the `Load` `v6` became an `Addr` of the `SB` `v3`. -/
theorem ff_checks :
    (check ffCheckEnv ffFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet ffRules) ffPassEnv ffFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := fnTyps } o.func).toBool,
        (o.func.value? 6).map fun v => (v.op, v.args))) =
      some (true, some (.Addr, #[3])) := by
  decide +kernel

/-- **Pass execution witness** for a fixed load (`generic.rules:2255`): on `dictEntry`, the
checked rewrite pass replaces the `Load` by the `Addr` of the relocation target
(`v6 = Addr {main.T} v3`), and the result refines the input (`checkedRewrite_refines`, through
`LoadFwd.fwd_refines` under `RoImage`). -/
theorem ff_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet ffRules) ffPassEnv ffFunc = .ok out ∧
      (out.func.value? 6).map (fun v => (v.op, v.args)) = some (.Addr, #[3]) ∧
      check ffCheckEnv ffFunc = .ok () ∧
      check { tabs := out.tables, typs := fnTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre ffPassEnv.tables ffPassEnv.frontend ffFunc)
        out.tables out.func
        ffPassEnv.tables ffFunc := by
  obtain ⟨h1, h2⟩ := ff_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet ffRules) ffPassEnv ffFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h6⟩ := h2
    exact ⟨out, rfl, h6, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := ffRules) (penv := ffPassEnv)
        (f := ffFunc) (out := out) ffRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

/-- The global image's allocation of `main..dict.f` (`Sem.globalImage`'s `rodataAlloc`). -/
def ffAlloc : Alloc := rodataAlloc (ByteArray.mk (Array.replicate 16 0)) 16 #[ffReloc]

/-- `Env.p1` with the global image's allocation of `main..dict.f`. -/
def ffEnv : Env := { Env.p1 with globals := [("main..dict.f", ffAlloc)] }

theorem ff_roPass :
    RewriteCheck.roPass ffTabs ffPassEnv.frontend ffFunc = [("main..dict.f", ffAlloc)] := by
  decide +kernel

/-- **Non-vacuity of `RwPre` with the read-only symbol**: on `Env.p1` with the symbol in the
global image and an empty memory, `dictEntry`'s read-only symbol holds its image. -/
theorem ff_rwPre (args : List Val) (hargs : ∀ v ∈ args, ∀ a n, v.Avoids (· = .temp a n)) :
    GoFV.Proof.Pass.Rewrite.RwPre ffTabs ffPassEnv.frontend ffFunc ffEnv args {} := by
  refine ⟨fun n c h => Env.p1_mono n c h, ⟨fun n c hm h => Env.p1_allocNonNil n c hm h, ?_⟩,
    ⟨fun c h => Env.p1_memOps.1 c h, fun c h => Env.p1_memOps.2 c h⟩,
    fun n c hm h => Env.p1_allocZero n c hm h, ⟨fun n c h => Env.p1_keepsRo n c h, ?_⟩,
    GoFV.Proof.Pass.Rewrite.initAvoids_empty hargs (by decide +kernel),
    fun n c hn h => Env.p1_growLen n c hn h, fun n c h => Env.p1_ifaceEq _ n c h⟩
  · rw [show NilCheck.dictParams ffTabs ffFunc = [] by decide +kernel]
    exact DictArgs.nil args
  · rw [ff_roPass]
    intro n a h
    simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by decide +kernel⟩

/-! ## A fixed load from a symbol only the frontend defines (#372)

```go
func dictChain(t *int) *[2]int {
	// v6 = Load <*[2]int> (OffPtr [8] (Addr {main..dict.f} SB)) mem: Addr {main.T} SB
	// v8 = Load <*[2]int> (OffPtr [8] v6) mem: main.T's relocation at 8, Addr {main.U} SB
}
```

`main.T` is no symbol of the input (`roSyms` lacks it): the pass takes it from the frontend
(`PassEnv.frontend`, `symAux`) when the first fixed load gives `v6 = Addr {main.T} SB`, and the
second fixed load reads its relocation. The validator takes the frontend's read-only symbols
(`RewriteCheck.roAll`, through `RewriteCheck.roPass`) as read-only, and the precondition pins
them (`RwPre`'s `RoImage (roPass tabs fe f)`; `fg_rwPre` with both symbols in the global image).
-/

/-- The relocation of `main.T` at offset 8 to `main.U`. -/
def fgReloc : Reloc := { ffReloc with target := GoStr.ofString "main.U" }

/-- The frontend's `SRODATA` symbol `main.T`: 16 zero bytes, the relocation at 8. -/
def fgSymT : AuxDef :=
  { fmt := GoStr.ofString "main.T",
    kind := .sym (GoStr.ofString "main.T") 0 "SRODATA" 16 default none none
      (some (ByteArray.mk (Array.replicate 16 0))) #[fgReloc] none }

/-- The frontend's tables: `main.T`. -/
def fgFrontend : Tables where
  auxes := #[none, some fgSymT]

/-- `dictChain`, the input of `opt`. -/
def fgFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 9
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[9] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8, 9])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 3 #[] 1),
    some (mkV 2 .Arg 3 (some 3) p0 0 #[] 1),
    some (mkV 3 .SB 15 none p0 1 #[] 1),
    some (mkV 4 .Addr 3 (some 9) p0 1 #[3] 1),
    some (mkVi 5 .OffPtr 3 8 p0 1 #[4] 1),
    some (mkV 6 .Load 5 none p0 1 #[5, 1] 1),
    some (mkVi 7 .OffPtr 3 8 p0 1 #[6] 1),
    some (mkV 8 .Load 5 none p0 1 #[7, 1] 1),
    some (mkVi 9 .MakeResult 35 0 p0 1 #[8, 1] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

def fgPassEnv : PassEnv :=
  { ffPassEnv with funcName := GoStr.ofString "dictChain", frontend := fgFrontend }

/-- The symbol name of the `Addr` `v8` of `o`'s function. -/
def fgAddr (o : PassOut) : Option String :=
  (o.func.value? 8).bind fun v => WBCheck.symName? o.tables v.aux

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result, which
passes `check`, where the second `Load` became an `Addr` of `main.U` on the `SB` `v3` (the first
one's `Addr {main.T}` and its `OffPtr` are dead and gone). -/
theorem fg_checks :
    (check ffCheckEnv fgFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet ffRules) fgPassEnv fgFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := fnTyps } o.func).toBool &&
        fgAddr o == some "main.U",
        (o.func.value? 8).map (fun v => (v.op, v.args)))) =
      some (true, some (.Addr, #[3])) := by
  decide +kernel

/-- **Pass execution witness** for a fixed load from a frontend-only symbol (`generic.rules:2255`
twice): on `dictChain`, the checked rewrite pass replaces the second `Load`, from `main.T`, which
only the frontend defines, by `Addr {main.U} v3`, and the result refines the input under `RwPre`
with the frontend's tables (`checkedRewrite_refines`). -/
theorem fg_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet ffRules) fgPassEnv fgFunc = .ok out ∧
      (out.func.value? 8).map (fun v => (v.op, v.args)) = some (.Addr, #[3]) ∧
      fgAddr out = some "main.U" ∧
      check ffCheckEnv fgFunc = .ok () ∧
      check { tabs := out.tables, typs := fnTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre fgPassEnv.tables fgPassEnv.frontend fgFunc)
        out.tables out.func fgPassEnv.tables fgFunc := by
  obtain ⟨h1, h2⟩ := fg_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet ffRules) fgPassEnv fgFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h8⟩ := h2
    rw [Bool.and_eq_true] at hg
    obtain ⟨hg, hn⟩ := hg
    have hn : fgAddr out = some "main.U" := beq_iff_eq.1 hn
    exact ⟨out, rfl, h8, hn, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := ffRules) (penv := fgPassEnv)
        (f := fgFunc) (out := out) ffRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

/-- The global image's allocation of `main.T`. -/
def fgAllocT : Alloc := rodataAlloc (ByteArray.mk (Array.replicate 16 0)) 16 #[fgReloc]

/-- `Env.p1` with the global image's allocations of `main..dict.f` and `main.T`. -/
def fgEnv : Env := { Env.p1 with globals := [("main..dict.f", ffAlloc), ("main.T", fgAllocT)] }

theorem fg_roPass :
    RewriteCheck.roPass ffTabs fgPassEnv.frontend fgFunc =
      [("main..dict.f", ffAlloc), ("main.T", fgAllocT)] := by
  decide +kernel

/-- **Non-vacuity of `RwPre` with a frontend symbol**: on `Env.p1` with both symbols in the
global image and an empty memory, the input's and the frontend's read-only symbols hold their
images. -/
theorem fg_rwPre (args : List Val) (hargs : ∀ v ∈ args, ∀ a n, v.Avoids (· = .temp a n)) :
    GoFV.Proof.Pass.Rewrite.RwPre ffTabs fgPassEnv.frontend fgFunc fgEnv args {} := by
  refine ⟨fun n c h => Env.p1_mono n c h, ⟨fun n c hm h => Env.p1_allocNonNil n c hm h, ?_⟩,
    ⟨fun c h => Env.p1_memOps.1 c h, fun c h => Env.p1_memOps.2 c h⟩,
    fun n c hm h => Env.p1_allocZero n c hm h, ⟨fun n c h => Env.p1_keepsRo n c h, ?_⟩,
    GoFV.Proof.Pass.Rewrite.initAvoids_empty hargs (by decide +kernel),
    fun n c hn h => Env.p1_growLen n c hn h, fun n c h => Env.p1_ifaceEq _ n c h⟩
  · rw [show NilCheck.dictParams ffTabs fgFunc = [] by decide +kernel]
    exact DictArgs.nil args
  · rw [fg_roPass]
    intro n a h
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨rfl, by decide +kernel⟩
    · exact ⟨rfl, by decide +kernel⟩

end GoFV.Proof.Witness
