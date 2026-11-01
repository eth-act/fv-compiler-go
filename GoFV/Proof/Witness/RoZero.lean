import GoFV.Proof.Witness.Seg

/-!
# Witness function for a read-only segment (issue #151)

```go
func copyZero(p *[2]int, x int) int {
	*p = zero2  // v6 = Move {[2]int} [16] p (Addr {main..stmp_0} SB) mem   (generic.rules:1743)
	return x
}
```

as one block, where `main..stmp_0` is a read-only (`SRODATA`) symbol of 16 zero bytes. The
checked rewrite pass with `{:1743}` (a segment rule, `RuleSet.segs`) redefines `v6` as
`Zero [16] p mem`; the segment layer validates it (`RewriteCheck.roSeg?`, `roSegsOK`: the symbol
is one of the input's read-only symbols, `RewriteCheck.roSyms`, and its bytes are zero) and
`Seg.seg_refines` proves it. The precondition `RwPre` holds on `Env.p1` with the symbol's
allocation in the global image (`zr_rwPre`).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Rules

/-- The read-only symbol `main..stmp_0`: 16 zero bytes. -/
def zrSym : AuxDef :=
  { fmt := GoStr.ofString "main..stmp_0",
    kind := .sym (GoStr.ofString "main..stmp_0") 0 "SRODATA" 16 default none none
      (some (ByteArray.mk (Array.replicate 16 0))) #[] none }

/-- `zpTabs` with `uintptr` (type 15) and the symbol `main..stmp_0` (aux 8). -/
def zrTabs : Tables :=
  { zpTabs with
    types := zpTabs.types.set! 15 (some (mkT .UINTPTR (some 8) "uintptr"))
    auxes := zpTabs.auxes.push (some zrSym) }

/-- `copyZero`, the input of `opt`. -/
def zrFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 7
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[7] #[] #[] #[1, 2, 3, 4, 5, 6, 7])]
  valueTab := #[none,
    some (mkVi 1 .InitMem 29 0 p0 1 #[] 1),
    some (mkV 2 .Arg 5 (some 3) p0 1 #[] 1),
    some (mkV 3 .Arg 2 (some 4) p0 1 #[] 1),
    some (mkV 4 .SB 15 none p0 1 #[] 1),
    some (mkV 5 .Addr 5 (some 8) p0 1 #[4] 1),
    some { mkV 6 .Move 29 (some 6) p0 1 #[2, 5, 1] 1 with auxInt := 16 },
    some (mkVi 7 .MakeResult 35 0 p0 1 #[3, 6] 1)]
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := { lineStarts := some #[] }

/-- The one-rule set `{generic.rules:1743}`, as a segment rule. -/
def zrRules : RuleSet where
  name := "generic"
  values := []
  blocks := []
  segs := [Generated.Generic.r_generic_1743]

theorem zrRules_allSound : zrRules.AllSound :=
  GoFV.Proof.Rules.RuleSet.allSound_of trivial trivial

/-- `slTyps` with `uintptr` (type 15, the type of `SB`). -/
def zrTyps : Array (String × TypeRef) := slTyps.push ("Uintptr", 15)

def zrPassEnv : PassEnv :=
  { azPassEnv with funcName := GoStr.ofString "copyZero", typs := zrTyps, tables := zrTabs }

def zrCheckEnv : CheckEnv := { tabs := zrTabs, typs := zrTyps }

/-- By kernel evaluation: the input passes `check`, and `checkedRewrite` keeps a result, which
passes `check`, in which `v6` is `Zero [16] v2 v1`. -/
theorem zr_checks :
    (check zrCheckEnv zrFunc).toBool = true ∧
    (checkedRewrite (Interp.Table.ofRuleSet zrRules) zrPassEnv zrFunc).toOption.map
      (fun o => ((check { tabs := o.tables, typs := zrTyps } o.func).toBool,
        (o.func.value? 6).map fun v => (v.op, v.auxInt, v.args))) =
      some (true, some (.Zero, 16, #[2, 1])) := by
  decide +kernel

/-- **Pass execution witness** for a read-only segment (`generic.rules:1743`): on `copyZero`, the
checked rewrite pass turns the `Move` from the zero symbol into `Zero [16] p mem`, and the result
refines the input (`checkedRewrite_refines`, through `Seg.seg_refines`). -/
theorem zr_checkedRewrite :
    ∃ out, checkedRewrite (Interp.Table.ofRuleSet zrRules) zrPassEnv zrFunc = .ok out ∧
      (out.func.value? 6).map (fun v => (v.op, v.auxInt, v.args)) = some (.Zero, 16, #[2, 1]) ∧
      check zrCheckEnv zrFunc = .ok () ∧
      check { tabs := out.tables, typs := zrTyps } out.func = .ok () ∧
      RefinesFrom (GoFV.Proof.Pass.Rewrite.RwPre zrPassEnv.tables zrFunc) out.tables out.func
        zrPassEnv.tables zrFunc := by
  obtain ⟨h1, h2⟩ := zr_checks
  cases hc : checkedRewrite (Interp.Table.ofRuleSet zrRules) zrPassEnv zrFunc with
  | error e => rw [hc] at h2; cases h2
  | ok out =>
    rw [hc] at h2
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
    obtain ⟨hg, h6⟩ := h2
    exact ⟨out, rfl, h6, ok_of_toBool h1, ok_of_toBool hg,
      GoFV.Proof.Pass.Rewrite.checkedRewrite_refines (s := zrRules) (penv := zrPassEnv)
        (f := zrFunc) (out := out) zrRules_allSound hc (ok_of_toBool h1) (ok_of_toBool hg)⟩

/-- `Env.p1` with the global image's allocation of `main..stmp_0`. -/
def zrEnv : Env :=
  { Env.p1 with globals := [("main..stmp_0", rodataAlloc (ByteArray.mk (Array.replicate 16 0)) 16 #[])] }

theorem zr_roSyms : RewriteCheck.roSyms zrTabs zrFunc =
    [("main..stmp_0", rodataAlloc (ByteArray.mk (Array.replicate 16 0)) 16 #[])] := by
  decide +kernel

/-- **Non-vacuity of `RwPre` with a read-only symbol**: on `Env.p1` with the symbol in the global
image and an empty memory, `copyZero`'s read-only symbol holds its exported bytes. -/
theorem zr_rwPre (args : List Val) : GoFV.Proof.Pass.Rewrite.RwPre zrTabs zrFunc zrEnv args {} := by
  refine ⟨fun n c h => Env.p1_mono n c h, ⟨fun n c hm h => Env.p1_allocNonNil n c hm h, ?_⟩,
    ⟨fun c h => Env.p1_memOps.1 c h, fun c h => Env.p1_memOps.2 c h⟩,
    fun n c h => Env.p1_keepsRo n c h, ?_⟩
  · rw [show NilCheck.dictParams zrTabs zrFunc = [] by decide +kernel]
    exact DictArgs.nil args
  · rw [zr_roSyms]
    intro n a h
    simp only [List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by decide +kernel⟩

end GoFV.Proof.Witness
