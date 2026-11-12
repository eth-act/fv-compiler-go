import GoFV.Proof.Pass.PipelineFull
import GoFV.Proof.Witness.Pipeline
import GoFV.Proof.Witness.TraceFP
import GoFV.Proof.RunLFCases

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: the verified pipeline through `trim` on `isNaN`

`examples/floats/main/isNaN,1.ssa`, section 0 (`start`), of the corpus
`gofv-corpus/2aae1000ea1d/quick-v7/plain`, transcribed (every definition of the section, the
`config`, `typs`, `typeorder`, `ptrcache` and `typelink` lines of the file):

```go
func isNaN(f float64) bool {
	return f != f
}
```

By compiled evaluation (`native_decide`, listed in `scripts/axioms-allowlist.txt`, as for
`verifiedPipeline_witness`), `verifiedPipelineFull` from `number lines` through `trim` returns a
`fullyVerified` state, and the input of its `schedule` run has no memory op or nil check (so it
cannot fault in the nil page, `noNilFault_of_noAct`). By kernel evaluation the input returns `true`
for a NaN argument in `plRunEnv` (Phase 1's witness environment, which satisfies `VPre`), so
`verifiedPipelineFull_refines` gives that the allocated function after `trim` returns `true` under
`runLoc`.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.Verified GoFV.Proof GoFV.Proof.Pipeline
  GoFV.Proof.PipelineFull

/-- `abiInfo` of `isNaN`: one `float64` parameter in `F0` (`RegIndex` 16), one `bool` result in
`R0`. -/
def pfABI : CallABI :=
  { abi := 1, nin := 1, nout := 1, spillOff := 8, spillSize := 8, inRegs := 1, outRegs := 1,
    params := #[{ out := false, index := 0, type := 2, name := some 3, regs := #[16], offset := 0 },
                { out := true, index := 0, type := 3, name := some 4, regs := #[0], offset := -1 }] }

/-- The definitions of section 0. -/
def pfTabs : Tables where
  posBases := #[none, none, some { file := GoStr.ofString "./main.go", line := 1, col := 1, inl := -1 }]
  types :=
    let t := Array.replicate 35 (none : Option TypeDef)
    let t := t.set! 1 (some (mkTy .FUNC (some 8) (some 8) (some 8) true true false false
      "func(float64) bool" "func(float64) bool" (.func 0 1 1 #[{ name := GoStr.ofString "f", type := 2, offset := none, embedded := false },
        { name := GoStr.ofString "", type := 3, offset := none, embedded := false }])))
    let t := t.set! 2 (some (mkTy .FLOAT64 (some 8) (some 8) (some 0) false false true true
      "float64" "float64"))
    let t := t.set! 3 (some (mkTy .BOOL (some 1) (some 1) (some 0) false false true true
      "bool" "bool"))
    let t := t.set! 4 (some (mkTy .INT8 (some 1) (some 1) (some 0) false false true true
      "int8" "int8"))
    let t := t.set! 5 (some (mkTy .INT16 (some 2) (some 2) (some 0) false false true true
      "int16" "int16"))
    let t := t.set! 6 (some (mkTy .INT32 (some 4) (some 4) (some 0) false false true true
      "int32" "int32"))
    let t := t.set! 7 (some (mkTy .INT64 (some 8) (some 8) (some 0) false false true true
      "int64" "int64"))
    let t := t.set! 8 (some (mkTy .UINT8 (some 1) (some 1) (some 0) false false true true
      "uint8" "uint8"))
    let t := t.set! 9 (some (mkTy .UINT16 (some 2) (some 2) (some 0) false false true true
      "uint16" "uint16"))
    let t := t.set! 10 (some (mkTy .UINT32 (some 4) (some 4) (some 0) false false true true
      "uint32" "uint32"))
    let t := t.set! 11 (some (mkTy .UINT64 (some 8) (some 8) (some 0) false false true true
      "uint64" "uint64"))
    let t := t.set! 12 (some (mkTy .INT (some 8) (some 8) (some 0) false false true true
      "int" "int"))
    let t := t.set! 13 (some (mkTy .FLOAT32 (some 4) (some 4) (some 0) false false true true
      "float32" "float32"))
    let t := t.set! 14 (some (mkTy .UINT (some 8) (some 8) (some 0) false false true true
      "uint" "uint"))
    let t := t.set! 15 (some (mkTy .UINTPTR (some 8) (some 8) (some 0) false false true true
      "uintptr" "uintptr"))
    let t := t.set! 16 (some (mkTy .STRING (some 16) (some 8) (some 8) true false true true
      "string" "string"))
    let t := t.set! 17 (some (mkTy .PTR (some 8) (some 8) (some 8) true true true false
      "*uint8" "*uint8" (.elem 8)))
    let t := t.set! 18 (some (mkTy .PTR (some 8) (some 8) (some 8) true true true false
      "*int32" "*int32" (.elem 6)))
    let t := t.set! 19 (some (mkTy .PTR (some 8) (some 8) (some 8) true true true false
      "*uint32" "*uint32" (.elem 10)))
    let t := t.set! 20 (some (mkTy .PTR (some 8) (some 8) (some 8) true true true false
      "*int" "*int" (.elem 12)))
    let t := t.set! 21 (some (mkTy .PTR (some 8) (some 8) (some 8) true true true false
      "*uintptr" "*uintptr" (.elem 15)))
    let t := t.set! 22 (some (mkTy .PTR (some 8) (some 8) (some 8) true true true false
      "*float32" "*float32" (.elem 13)))
    let t := t.set! 23 (some (mkTy .PTR (some 8) (some 8) (some 8) true true true false
      "*float64" "*float64" (.elem 2)))
    let t := t.set! 24 (some (mkTy .PTR (some 8) (some 8) (some 8) true true true false
      "**uint8" "**uint8" (.elem 17)))
    let t := t.set! 25 (some (mkTy .COMPLEX64 (some 8) (some 4) (some 0) false false true true
      "complex64" "complex64"))
    let t := t.set! 26 (some (mkTy .COMPLEX128 (some 16) (some 8) (some 0) false false true true
      "complex128" "complex128"))
    let t := t.set! 27 (some (mkTy .UNSAFEPTR (some 8) (some 8) (some 8) true true true true
      "unsafe.Pointer" "unsafe.Pointer"))
    let t := t.set! 28 (some (mkTy .SSA none none none false false false false
      "mem" ""))
    let t := t.set! 29 (some (mkTy .SSA none none none false false false false
      "flags" ""))
    let t := t.set! 30 (some (mkTy .SSA none none none false false false false
      "void" ""))
    let t := t.set! 31 (some (mkTy .SSA (some 16) (some 8) none false false false false
      "int128" ""))
    let t := t.set! 32 (some (mkTy .RESULTS none none none false false false false
      "mem" "" (.results #[28])))
    let t := t.set! 33 (some (mkTy .PTR (some 8) (some 8) (some 8) true true true false
      "*bool" "*bool" (.elem 3)))
    let t := t.set! 34 (some (mkTy .RESULTS none none none false false false false
      "bool,mem" "" (.results #[3, 28])))
    t
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.isNaN}", kind := .call (some 2) (some pfABI) },
    some { fmt := GoStr.ofString "main.isNaN",
           kind := .sym (GoStr.ofString "main.isNaN") 1 "" 0 default none none none #[] none },
    some { fmt := GoStr.ofString "f",
           kind := .name (GoStr.ofString "f") .PPARAM 2 0 1 { used := true } (pos 2 17 12 0) },
    some { fmt := GoStr.ofString "~r0",
           kind := .name (GoStr.ofString "~r0") .PPARAMOUT 3 0 1 {} (pos 2 17 23 0) }]
  slots := #[none, some { name := 3, type := 2, off := 0, splitOf := none, splitOffset := 0 }]

/-- `v<id> <op> t<type> [<auxInt>] {<aux>}` with position `p`, use count and arguments, in `b1`. -/
def pfV (id : ID) (op : Op) (t : TypeRef) (auxInt : Int64) (aux : Option AuxRef) (p : Pos)
    (uses : Nat) (args : Array ID) : Value :=
  { id, op, type := t, auxInt, aux, pos := p, uses, args, block := 1 }

/-- The values of section 0, by ID. -/
def pfValues : Array (Option Value) := #[none,
  some (pfV 1 .InitMem 28 0 none p0 3 #[]),
  some (pfV 2 .SP 15 0 none p0 2 #[]),
  some (pfV 3 .SB 15 0 none p0 0 #[]),
  some (pfV 4 .LocalAddr 23 0 (some 3) p0 0 #[2, 1]),
  some (pfV 5 .LocalAddr 33 0 (some 4) p0 0 #[2, 1]),
  some (pfV 6 .Arg 2 0 (some 3) (pos 2 17 6 2) 2 #[]),
  some (pfV 7 .ConstBool 3 0 none p0 0 #[]),
  some (pfV 8 .Neq64F 3 0 none (pos 2 17 39 0) 1 #[6, 6]),
  some (pfV 9 .MakeResult 34 0 none (pos 2 17 30 0) 1 #[8, 1])]

/-- `isNaN`, section 0. -/
def pfF : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 9
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret (pos 2 17 39 1) #[9] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8, 9])]
  valueTab := pfValues
  names := #[(1, #[6])]
  namedx := #[]
  splits := #[]
  canon := #[({ name := 3, type := 2, off := 0, splitOf := none, splitOffset := 0 }, 1)]
  consts := #[(0, #[7])]
  freeValues := []
  freeBlocks := []
  cache := {}

/-- `Config.Types` of the file. -/
def pfTyps : Array (String × TypeRef) := #[("Bool", 3), ("Int8", 4), ("Int16", 5), ("Int32", 6),
  ("Int64", 7), ("UInt8", 8), ("UInt16", 9), ("UInt32", 10), ("UInt64", 11), ("Int", 12),
  ("Float32", 13), ("Float64", 2), ("UInt", 14), ("Uintptr", 15), ("String", 16), ("BytePtr", 17),
  ("Int32Ptr", 18), ("UInt32Ptr", 19), ("IntPtr", 20), ("UintptrPtr", 21), ("Float32Ptr", 22),
  ("Float64Ptr", 23), ("BytePtrPtr", 24), ("Complex64", 25), ("Complex128", 26), ("UnsafePtr", 27),
  ("Mem", 28), ("Flags", 29), ("Void", 30), ("Int128", 31), ("ResultMem", 32)]

/-- The pipeline's environment: the file's `config` lines, `typs`, type order, `ptrcache` and
`typelink` groups; the frontend is empty. -/
def pfEnv : PassEnv where
  passName := ""
  pkg := GoStr.ofString "main"
  funcName := GoStr.ofString "isNaN"
  abi := 1
  nosplit := false
  pgohot := false
  typs := pfTyps
  typeOrder := TypeOrder.ofGroups #[#[4], #[8], #[5], #[9], #[6], #[10], #[7], #[11], #[12], #[14], #[15], #[25], #[26], #[13], #[2], #[3],
    #[17], #[18], #[19], #[20], #[21], #[22], #[23], #[33], #[24], #[1], #[16], #[27], #[28], #[30], #[29], #[31],
    #[32], #[34]]
  tables := pfTabs
  ptrCache := fun t => [2, 5, 6, 7, 8, 10, 12, 13, 15, 16, 17, 24].contains t
  typeLink := fun t => if t == 32 then 28 else t
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
    ("rttype.PtrType.Elem", #[.word "48:PTR:8"]),
    ("registers", #[.word "R0:8192,R1:8193,R2:8194,R3:8195,R4:8196,R5:8197,R6:8198,R7:8199,R8:8200,R9:8201,R10:8202,R11:8203,R12:8204,R13:8205,R14:8206,R15:8207,R16:8208,R17:8209,R19:8211,R20:8212,R21:8213,R22:8214,R23:8215,R24:8216,R25:8217,R26:8218,g:8220,R29:8221,R30:8222,ZERO:8223,SP:8383,F0:8224,F1:8225,F2:8226,F3:8227,F4:8228,F5:8229,F6:8230,F7:8231,F8:8232,F9:8233,F10:8234,F11:8235,F12:8236,F13:8237,F14:8238,F15:8239,F16:8240,F17:8241,F18:8242,F19:8243,F20:8244,F21:8245,F22:8246,F23:8247,F24:8248,F25:8249,F26:8250,F27:8251,F28:8252,F29:8253,F30:8254,F31:8255,SB:0"]),
    ("gpregmask", #[.word "13ffffff"]),
    ("fpregmask", #[.word "7fffffff80000000"]),
    ("fp32regmask", #[.word "0"]),
    ("fp64regmask", #[.word "0"]),
    ("simdregmask", #[.word "7fffffff80000000"]),
    ("specialregmask", #[.word "0"]),
    ("intparamregs", #[.word "0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15"]),
    ("floatparamregs", #[.word "31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46"]),
    ("fpreg", #[.word "-1"]),
    ("linkreg", #[.word "28"]),
    ("framepointer", #[.word "1"]),
    ("clobberdeadreg", #[.word "0"]),
    ("flagN", #[.word "0"]),
    ("fmahash", #[.word "0"])]

/-- The NaN argument (the bits of `math.NaN()`). -/
def pfArgs : List Val := [.int .w64 0x7FF8000000000001]

/-- No value of `f` is a memory op or a nil check (`noNilFault_of_noAct`). -/
def noActB (f : Func) : Bool :=
  f.valueTab.all (fun o => o.all fun v => !GoFV.Opt.ScheduleCheck.actOp v.op)

/-- No value of `f` (in `tabs`) is a pointer-shaped register piece of a parameter
(`argPtrsOK_of_none`). -/
def noArgPtrB (tabs : Tables) (f : Func) : Bool :=
  (List.range f.valueTab.size).all
    (fun x => !GoFV.Opt.ScheduleCheck.argPtr tabs (Ctx.makeL tabs f).params (Ctx.makeL tabs f).tys f x)

/-- No nil check of `f` (in `tabs`) checks a pointer-shaped value (`nilPtrsOK_of_none`). -/
def noNilPtrB (tabs : Tables) (f : Func) : Bool :=
  f.valueTab.all (fun o => o.all fun v => !v.op.nilCheck ||
    (v.args[0]?.all fun q => !GoFV.Opt.ScheduleCheck.ptrShape
      ((Ctx.makeL tabs f).tys[q]?.getD .other)))

/-- The pipeline returns a `fullyVerified` state whose `schedule` inputs have no memory op, no
pointer-shaped parameter piece and no checked pointer-shaped value (compiled evaluation). -/
theorem pfF_pipeline :
    ((verifiedPipelineFull pfEnv pfF).toOption.map fun r =>
      r.fullyVerified &&
        r.nnf.all (fun x => noActB x.2 && noArgPtrB x.1 x.2 && noNilPtrB x.1 x.2)) = some true := by
  native_decide

theorem pfF_run : returnsBool (run plRunEnv pfTabs pfF pfArgs {} 1) true = true := by
  decide +kernel

theorem pfF_dict : GoFV.Opt.NilCheck.dictParams pfEnv.tables pfF = [] := by decide +kernel

theorem pfF_ro : GoFV.Opt.Verified.pipelineRo pfEnv pfF = [] := by decide +kernel

theorem pfRunEnv_initAvoids : InitAvoids plRunEnv pfArgs {} := by
  intro a n
  refine ⟨fun v h => ?_, fun _ _ h => ?_, rfl, fun g hg x hx => ?_, fun _ h => nomatch h⟩
  · simp only [pfArgs, List.mem_cons, List.not_mem_nil, or_false] at h
    subst h
    trivial
  · simp at h
  · simp only [plRunEnv, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · simp only [Array.toList_replicate, List.mem_replicate] at hx
      rw [hx.2]
      trivial
    · simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hx
      rw [hx]
      trivial

theorem pfRunEnv_vpre : VPre (GoFV.Opt.NilCheck.dictParams pfEnv.tables pfF)
    (GoFV.Opt.Verified.pipelineRo pfEnv pfF) (GoFV.Opt.Verified.pipelineEq pfEnv)
    plRunEnv pfArgs {} :=
  ⟨plRunEnv_mono, plRunEnv_frameSafe, pfRunEnv_initAvoids, plRunEnv_allocNonNil,
    by rw [pfF_dict]; exact DictArgs.nil pfArgs, plRunEnv_wbPre, plRunEnv_tempOblivious,
    plRunEnv_memOps,
    by rw [pfF_ro]; exact RoImage.nil (env := plRunEnv) (plRunEnv_keeps Mem.KeepsRo.refl) {},
    plRunEnv_keeps Mem.KeepsFrame.refl, plRunEnv_allocZero, plRunEnv_growLen, plRunEnv_ifaceEq _⟩

/-- **Non-vacuity of `verifiedPipelineFull_refines`**: the verified pipeline from `number lines`
through `trim` on `isNaN` returns a `fullyVerified` (allocated) state, and for a NaN argument
the allocated function returns `true` under `runLoc`, as the input does under `run`. -/
theorem verifiedPipelineFull_witness :
    ∃ r, verifiedPipelineFull pfEnv pfF = .ok r ∧ r.fullyVerified = true ∧
      (∃ m, run plRunEnv pfTabs pfF pfArgs {} 1 = .returned [.bool true] m) ∧
      ∃ fuel m, runLoc plRunEnv r.st.tables r.st.func pfArgs {} fuel = .returned [.bool true] m := by
  have hp := pfF_pipeline
  cases hpe : verifiedPipelineFull pfEnv pfF with
  | error e => rw [hpe] at hp; cases hp
  | ok r =>
    rw [hpe] at hp
    simp only [Except.toOption, Option.map_some, Option.some.injEq, Bool.and_eq_true] at hp
    obtain ⟨hv, hn⟩ := hp
    obtain ⟨m, hm⟩ := returnsBool_iff.1 pfF_run
    refine ⟨r, rfl, hv, ⟨m, hm⟩, ?_⟩
    have hx2 : ∀ x ∈ r.nnf,
        (noActB x.2 = true ∧ noArgPtrB x.1 x.2 = true) ∧ noNilPtrB x.1 x.2 = true := fun x hx => by
      have := List.all_eq_true.1 hn x hx
      simpa only [Bool.and_eq_true] using this
    have hnn : ∀ x ∈ r.nnf, NoNilFault x.1 x.2 plRunEnv pfArgs {} := fun x hx =>
      noNilFault_of_noAct (hx2 x hx).1.1 plRunEnv pfArgs {}
    have hap : ∀ x ∈ r.nnf, ArgPtrsOK x.1 x.2 plRunEnv pfArgs {} := fun x hx =>
      argPtrsOK_of_none (hx2 x hx).1.2 plRunEnv pfArgs {} (fun _ h => nomatch h)
    have hnp : ∀ x ∈ r.nnf, NilPtrsOK x.1 x.2 plRunEnv pfArgs {} := fun x hx =>
      nilPtrsOK_of_none (hx2 x hx).2 plRunEnv pfArgs {}
    obtain ⟨fuel', ho⟩ := verifiedPipelineFull_refines hpe hv pfRunEnv_vpre hnn hap hnp
      (fuel := 1) (by rw [show pfEnv.tables = pfTabs from rfl, hm]; trivial)
    rw [show pfEnv.tables = pfTabs from rfl, hm] at ho
    refine ⟨fuel', ?_⟩
    generalize runLoc plRunEnv r.st.tables r.st.func pfArgs {} fuel' = o at ho ⊢
    cases ho with
    | @returned _ rs' _ m' hl _ =>
      cases hl with
      | cons h1 t =>
        cases t
        cases h1
        exact ⟨m', rfl⟩

end GoFV.Proof.Witness
