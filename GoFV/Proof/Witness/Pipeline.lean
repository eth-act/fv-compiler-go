import GoFV.Proof.Pass.Pipeline
import GoFV.Proof.Witness.DAE
import GoFV.Proof.Witness.WriteBarrier
import GoFV.Proof.Witness.TabsAgreeMod

/-!
# Non-vacuity witness: the verified pipeline on `f0` of `test/stack`, with a global store

`plF` is `f0` of `test/stack` at `dead auto elim` (`stackF0`: two inlined results `~r0`, frame
temporaries cleared by `VarDef` and `Zero [3000]` and never read) with a store of `5` to the global
`main.g` (`Addr {main.g} SB`, so that `expand calls`, which adds an `SB` to an entry block
without one, leaves it unchanged), as the input of the whole pipeline (`number lines` …
`writebarrier`; the export's `config` of `test/stack`). By compiled evaluation (`native_decide`,
listed in `scripts/axioms-allowlist.txt`: `decide +kernel` gets stuck comparing the pass
results' CFG caches), `verifiedPipeline` returns a `verified` state: every pass run is proven or
the identity, and `dead auto elim` and `generic deadcode` removed the `Zero`s (`v8` is gone).
By kernel
evaluation, the input returns (no results) with an environment holding `main.g` and a
read-only `runtime.writeBarrier` flag; the environment's contracts are monotone, frame-safe and
keep the flag, and the empty memory holds no pointer, so `verifiedPipeline_refines` gives that
the output returns too.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.Verified GoFV.Proof GoFV.Proof.Pipeline

/-- `stackF0`'s tables with `*int` (`t36`), the symbol `main.g` (`a6`) and the type aux `int`
(`a7`), and the slot table as `decompose` pads it. -/
def plTabs : Tables :=
  { stackF0Tabs with
    types := stackF0Tabs.types.push (some (mkTy .PTR (some 8) (some 8) (some 8) true true true false
      "*int" "*int" (.elem 11)))
    auxes := stackF0Tabs.auxes ++ #[
      some { fmt := GoStr.ofString "main.g",
             kind := .sym (GoStr.ofString "main.g") 0 "SNOPTRBSS" 8 default none none none #[] none },
      some { fmt := GoStr.ofString "int", kind := .type 11 }] }

/-- `stackF0`'s values, then `v15 = SB`, `v16 = Addr {main.g} v15`, `v17 = Const64 [5]`,
`v18 = Store {int} v16 v17 v12`, and the result `v14 = MakeResult v18`. -/
def plValues : Array (Option Value) :=
  (stackF0Values.set! 14 (some (mkV3 14 .MakeResult 32 0 none (pos 2 39 1 1) 1 #[18]))) ++ #[
  some (mkV3 15 .SB 15 0 none p0 1 #[]),
  some (mkV3 16 .Addr 36 0 (some 6) (pos 2 39 1 0) 1 #[15]),
  some (mkV3 17 .Const64 11 5 none (pos 2 39 1 0) 1 #[]),
  some (mkV3 18 .Store 28 0 (some 7) (pos 2 39 1 0) 1 #[16, 17, 12])]

def plBlocks : Array (Option Block) := #[none, none, none,
  some (mkB 3 .Ret (pos 2 39 1 0) #[14] #[] #[] #[1, 2, 4, 6, 7, 8, 10, 11, 12, 15, 16, 17, 18, 14])]

/-- The witness function. -/
def plF : Func :=
  { stackF0 with vidLast := 18, valueTab := plValues, blockTab := plBlocks, consts := #[(5, #[17])] }

/-- `Config.Types` of `test/stack`. -/
def plTyps : Array (String × TypeRef) := #[("Bool", 2), ("Int8", 3), ("Int16", 4), ("Int32", 5), ("Int64", 6), ("UInt8", 7), ("UInt16", 8), ("UInt32", 9), ("UInt64", 10), ("Int", 11), ("Float32", 12), ("Float64", 13), ("UInt", 14), ("Uintptr", 15), ("String", 16), ("BytePtr", 17), ("Int32Ptr", 18), ("UInt32Ptr", 19), ("IntPtr", 20), ("UintptrPtr", 21), ("Float32Ptr", 22), ("Float64Ptr", 23), ("BytePtrPtr", 24), ("Complex64", 25), ("Complex128", 26), ("UnsafePtr", 27), ("Mem", 28), ("Flags", 29), ("Void", 30), ("Int128", 31), ("ResultMem", 32)]

/-- The pipeline's environment: `test/stack`'s `config` lines. -/
def plEnv : PassEnv :=
  { stackF0PassEnv with
    passName := "", typs := plTyps, tables := plTabs
    config := #[
    ("arch", #[.word "arm64"]),
    ("goos", #[.word "linux"]),
    ("ptrsize", #[.word "8"]),
    ("regsize", #[.word "8"]),
    ("bigendian", #[.word "0"]),
    ("unalignedok", #[.word "1"]),
    ("havecondselect", #[.word "1"]),
    ("havebswap64", #[.word "1"]),
    ("havebswap32", #[.word "1"]),
    ("havebswap16", #[.word "1"]),
    ("hasgreg", #[.word "1"]),
    ("softfloat", #[.word "0"]),
    ("race", #[.word "0"]),
    ("optimize", #[.word "1"]),
    ("fixedframesize", #[.word "8"]),
    ("archalign", #[.word "1"]),
    ("flagshared", #[.word "0"]),
    ("flagdynlink", #[.word "0"]),
    ("usewb", #[.word "1"]),
    ("debugnil", #[.word "0"]),
    ("checkenabled", #[.word "0"]),
    ("localpkg", #[.str (GoStr.ofString "main")]),
    ("exp.cgocheck2", #[.word "0"]),
    ("exp.preemptibleloops", #[.word "0"]),
    ("exp.simd", #[.word "0"]),
    ("abi0", #[.word "0:0:8"]),
    ("abi1", #[.word "16:16:8"]),
    ("abiself", #[.word "1"]),
    ("abidefault", #[.word "1"]),
    ("syslook.writeBarrier", #[.str (GoStr.ofString "runtime.writeBarrier")]),
    ("syslook.wbZero", #[.str (GoStr.ofString "runtime.wbZero")]),
    ("syslook.wbMove", #[.str (GoStr.ofString "runtime.wbMove")]),
    ("syslook.cgoCheckPtrWrite", #[.str (GoStr.ofString "runtime.cgoCheckPtrWrite")]),
    ("syslook.cgoCheckMemmove", #[.str (GoStr.ofString "runtime.cgoCheckMemmove")]),
    ("syslook.goschedguarded", #[.str (GoStr.ofString "runtime.goschedguarded")]),
    ("zerobase", #[.str (GoStr.ofString "runtime.zerobase")]),
    ("rttype.Size_", #[.word "0:UINTPTR:8"]),
    ("rttype.PtrBytes", #[.word "8:UINTPTR:8"]),
    ("rttype.Hash", #[.word "16:UINT32:4"]),
    ("rttype.Kind_", #[.word "23:UINT8:1"]),
    ("rttype.GCData", #[.word "32:PTR:8"]),
    ("rttype.PtrType.Elem", #[.word "48:PTR:8"])] }

/-- `Env.p1` with the global `main.g` (8 zero bytes) and a read-only, zero
`runtime.writeBarrier` flag. -/
def plRunEnv : Env :=
  { Env.p1 with
    globals := [("main.g", { data := Array.replicate 8 (.b 0) }),
      ("runtime.writeBarrier", { data := #[.b 0, .b 0, .b 0, .b 0], writable := false })] }

/-! ## Certificates -/

/-- The pipeline returns a verified state without `v8` (compiled evaluation). -/
theorem plF_pipeline :
    ((verifiedPipeline plEnv plF).toOption.map fun r => r.verified && (r.func.value? 8).isNone) =
      some true := by
  native_decide

theorem plF_run : returnsNil (run plRunEnv plTabs plF [] {} 1) = true := by
  decide +kernel

theorem plF_v8 : (plF.value? 8).map (·.op) = some .Zero := by
  decide +kernel

theorem plRunEnv_initAvoids : InitAvoids plRunEnv [] {} := by
  intro a n
  refine ⟨fun _ h => absurd h List.not_mem_nil, fun _ _ h => ?_, rfl, fun g hg x hx => ?_⟩
  · simp at h
  · simp only [plRunEnv, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · simp only [Array.toList_replicate, List.mem_replicate] at hx
      rw [hx.2]
      trivial
    · simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hx
      rw [hx]
      trivial

theorem plF_dict : GoFV.Opt.NilCheck.dictParams plEnv.tables plF = [] := by decide +kernel

theorem plRunEnv_wbPre : WB.WbPre plRunEnv [] {} := by
  refine ⟨⟨⟨{ data := #[.b 0, .b 0, .b 0, .b 0], writable := false }, by decide +kernel,
    rfl, by decide, fun i hi => ?_⟩, by decide +kernel⟩, ?_⟩
  · match i, hi with
    | 0, _ => exact ⟨0, rfl⟩
    | 1, _ => exact ⟨0, rfl⟩
    | 2, _ => exact ⟨0, rfl⟩
    | 3, _ => exact ⟨0, rfl⟩
  · intro name c hc args clo m _ _ _
    simp only [plRunEnv, Env.p1] at hc
    split at hc <;> cases hc <;> trivial

theorem plRunEnv_vpre : VPre (GoFV.Opt.NilCheck.dictParams plEnv.tables plF) plRunEnv [] {} :=
  ⟨Env.p1_mono, p1_frameSafe, plRunEnv_initAvoids, Env.p1_allocNonNil,
    by rw [plF_dict]; exact DictArgs.nil [], plRunEnv_wbPre, p1_tempOblivious, Env.p1_memOps⟩

/-! ## The witness -/

/-- **Non-vacuity of `verifiedPipeline_refines`**: the whole verified pipeline on `plF` returns a
verified state in which the dead `Zero` `v8` is gone, and its function returns, as `plF` does. -/
theorem verifiedPipeline_witness :
    ∃ r, verifiedPipeline plEnv plF = .ok r ∧ r.verified = true ∧
      (plF.value? 8).map (·.op) = some .Zero ∧ r.func.value? 8 = none ∧
      ∃ fuel m, run plRunEnv r.tables r.func [] {} fuel = .returned [] m := by
  have hp := plF_pipeline
  cases hpe : verifiedPipeline plEnv plF with
  | error e => rw [hpe] at hp; cases hp
  | ok r =>
    rw [hpe] at hp
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Bool.and_eq_true,
      Option.isNone_iff_eq_none] at hp
    obtain ⟨hv, h8⟩ := hp
    refine ⟨r, rfl, hv, plF_v8, h8, ?_⟩
    have hr := verifiedPipeline_refines hpe hv
    have hrun := plF_run
    generalize hs : run plRunEnv plTabs plF [] {} 1 = o at hrun
    match o, hrun with
    | .returned [] m, _ =>
      obtain ⟨fuel', ho⟩ := hr plRunEnv [] {} plRunEnv_vpre 1
        (by rw [show plEnv.tables = plTabs from rfl, hs]; trivial)
      rw [show plEnv.tables = plTabs from rfl, hs] at ho
      refine ⟨fuel', ?_⟩
      generalize run plRunEnv r.tables r.func [] {} fuel' = o' at ho ⊢
      cases ho with
      | @returned _ rs' _ m' hl _ =>
        cases hl
        exact ⟨m', rfl⟩

end GoFV.Proof.Witness
