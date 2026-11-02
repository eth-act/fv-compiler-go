import GoFV.Proof.Pass.WBSim
import GoFV.Proof.Witness.Clamp
import GoFV.Proof.Witness.InitF10
import GoFV.Proof.Witness.Util

/-!
# Non-vacuity witness: writebarrier on `runtime/pprof.runtime_setProfLabel`

`std/std/runtime/runtime_setProfLabel,1.ssa`, the output of section 31 (`memcombine`, the input
of `writebarrier`), of the corpus `gofv-corpus/2aae1000ea1d/quick-v3`, with the definition tables
of the sections before it that the pass and `check` read, transcribed by hand:

```go
func runtime_setProfLabel(labels unsafe.Pointer) {
	getg().labels = labels // the field at offset 352 of the current `g`
}
```

One block: `v9 = Store {unsafe.Pointer} (OffPtr [352] (GetG v1)) v5 v1` stores the pointer
argument `v5` into a heap slot, which needs a write barrier. writebarrier splits the block on the
flag `Neq32 (Load (Addr {runtime.writeBarrier} SB) v1) (Const32 [0])`: the buffer block records
the new and the old pointer (`WB [2]`, two buffer `Store`s), the end block merges the memory
(`Phi`), re-emits the store and ends in the `WBend` marker made from `v9`. The checker
`WBCheck.wbOK` accepts the result, input and output pass `check` (kernel evaluation), so
`writebarrier_refines` applies; its precondition `WbPre` holds, e.g., on `Env.p1` with the
write-barrier helpers (`withWbHelpers`) and a read-only `runtime.writeBarrier` flag
(`wbPre_witness`). `writebarrier_call_witness`: a run with a `runtime.wbMove` call (a `Move` of a
pointer-holding struct, `copyPair`). `writebarrier_multi_witness`: a buffer block with two `WB`s
(nine barrier stores, `fill9`).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof

/-- `abiInfo` of `runtime_setProfLabel`: one pointer parameter in a register, no result. -/
def spABI : CallABI :=
  { abi := 1, nin := 1, nout := 0, spillOff := 8, spillSize := 8, inRegs := 1, outRegs := 0,
    params := #[{ out := false, index := 0, type := 2, name := some 3, regs := #[0],
                  offset := 0 }] }

/-- A pointer type (`hasptr,direct,comparable`) to `elem`. -/
def spPtr (str symName : String) (elem : TypeRef) : TypeDef :=
  mkTy .PTR (some 8) (some 8) (some 8) true true true false str symName (.elem elem)

/-- A scalar type (`comparable,named`). -/
def spScalar (kind : TypeKind) (size : Int) (s : String) : TypeDef :=
  mkTy kind (some size) (some size) (some 0) false false true true s s

/-- An SSA pseudo-type. -/
def spPseudo (kind : TypeKind) (s : String) (tail : TypeTail := .none) : TypeDef :=
  mkTy kind none none none false false false false s "" tail

/-- The definition tables of sections 0–31 that `writebarrier`, its checker and `check` read. -/
def spTabs : Tables where
  posBases := (Array.replicate 172 (none : Option PosBase)).set! 171
    (some { file := GoStr.ofString "runtime/proflabel.go", line := 1, col := 1, inl := -1 })
  types :=
    let t := Array.replicate 36 (none : Option TypeDef)
    let t := t.set! 1 (some (mkTy .FUNC (some 8) (some 8) (some 8) true true false false
      "func(unsafe.Pointer)" "func(unsafe.Pointer)"
      (.func 0 1 0 #[f10Field "labels" 2 none])))
    let t := t.set! 2 (some (mkTy .UNSAFEPTR (some 8) (some 8) (some 8) true true true true
      "unsafe.Pointer" "unsafe.Pointer"))
    let t := t.set! 3 (some (spScalar .BOOL 1 "bool"))
    let t := t.set! 10 (some (spScalar .UINT32 4 "uint32"))
    let t := t.set! 16 (some (spScalar .UINTPTR 8 "uintptr"))
    let t := t.set! 20 (some (spPtr "*uint32" "*uint32" 10))
    let t := t.set! 22 (some (spPtr "*uintptr" "*uintptr" 16))
    let t := t.set! 28 (some (spPseudo .SSA "mem"))
    let t := t.set! 32 (some (spPseudo .RESULTS "mem" (.results #[28])))
    let t := t.set! 33 (some (spPtr "*unsafe.Pointer" "*unsafe.Pointer" 2))
    t.set! 34 (some (spPtr "*g" "*runtime.g" 35))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{runtime/pprof.runtime_setProfLabel}",
           kind := .call (some 2) (some spABI) },
    some { fmt := GoStr.ofString "runtime/pprof.runtime_setProfLabel",
           kind := .sym (GoStr.ofString "runtime/pprof.runtime_setProfLabel") 1 "-" 0 {} none
             none none #[] none },
    some { fmt := GoStr.ofString "labels",
           kind := .name (GoStr.ofString "labels") .PPARAM 2 0 1 { used := true }
             (pos 171 20 27 0) },
    some { fmt := GoStr.ofString "unsafe.Pointer", kind := .type 2 },
    some { fmt := GoStr.ofString "labels+0", kind := .nameOff 3 0 }]
  slots := #[none, some { name := 3, type := 2, off := 0, splitOf := none, splitOffset := 0 }]

/-- A value of `runtime_setProfLabel`. -/
def spV (id : ID) (op : Op) (t : TypeRef) (auxInt : Int64) (aux : Option AuxRef) (p : Pos)
    (uses : Nat) (args : Array ID) : Value :=
  { id, op, type := t, auxInt, aux, pos := p, uses, args, block := 1 }

/-- The values of section 31, by ID. -/
def spValues : Array (Option Value) :=
  let t := Array.replicate 11 (none : Option Value)
  let t := t.set! 1 (some (spV 1 .InitMem 28 0 none p0 2 #[]))
  let t := t.set! 5 (some (spV 5 .ArgIntReg 2 0 (some 5) (pos 171 43 1 0) 1 #[]))
  let t := t.set! 6 (some (spV 6 .GetG 34 0 none (pos 171 42 6 1) 1 #[1]))
  let t := t.set! 8 (some (spV 8 .OffPtr 33 352 none (pos 171 42 8 0) 1 #[6]))
  let t := t.set! 9 (some (spV 9 .Store 28 0 (some 4) (pos 171 42 16 0) 1 #[8, 5, 1]))
  t.set! 10 (some (spV 10 .MakeResult 32 0 none (pos 171 43 1 1) 1 #[9]))

/-- `runtime_setProfLabel`, section 31 (the input of `writebarrier`). -/
def spFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 10
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret (pos 171 43 1 0) #[10] #[] #[] #[1, 5, 6, 8, 9, 10])]
  valueTab := spValues
  names := #[(1, #[5])]
  namedx := #[]
  splits := #[]
  canon := #[({ name := 3, type := 2, off := 0, splitOf := none, splitOffset := 0 }, 1)]
  consts := #[]
  freeValues := [3, 4, 7, 2]
  freeBlocks := []
  cache := { postorder := some #[1], idom := some #[none, none],
             sdom := some #[{ parent := none, child := none, sibling := none, entry := 0, exit := 0 },
               { parent := none, child := none, sibling := none, entry := 2, exit := 5 }],
             auxmap := some #[(some 3, 1), (none, 2)],
             lineStarts := some #[⟨171, some (42, 43), #[]⟩] }

/-- `Config.Types` (the `typs` line of section 0). -/
def spTyps : Array (String × TypeRef) :=
  #[("Bool", 3), ("Int8", 4), ("Int16", 5), ("Int32", 6), ("Int64", 7), ("UInt8", 8),
    ("UInt16", 9), ("UInt32", 10), ("UInt64", 11), ("Int", 12), ("Float32", 13), ("Float64", 14),
    ("UInt", 15), ("Uintptr", 16), ("String", 17), ("BytePtr", 18), ("Int32Ptr", 19),
    ("UInt32Ptr", 20), ("IntPtr", 21), ("UintptrPtr", 22), ("Float32Ptr", 23),
    ("Float64Ptr", 24), ("BytePtrPtr", 25), ("Complex64", 26), ("Complex128", 27),
    ("UnsafePtr", 2), ("Mem", 28), ("Flags", 29), ("Void", 30), ("Int128", 31),
    ("ResultMem", 32)]

def spCheckEnv : CheckEnv := { tabs := spTabs, typs := spTyps }

/-- What `writebarrier` reads of the export's environment. -/
def spPassEnv : PassEnv where
  passName := "writebarrier"
  pkg := GoStr.ofString "runtime"
  funcName := GoStr.ofString "runtime_setProfLabel"
  abi := 1
  nosplit := false
  pgohot := false
  config := #[("arch", #[.word "arm64"]), ("ptrsize", #[.word "8"]), ("regsize", #[.word "8"]),
    ("usewb", #[.word "1"]), ("localpkg", #[.str (GoStr.ofString "runtime")]),
    ("exp.cgocheck2", #[.word "0"]), ("abi0", #[.word "0:0:8"]), ("abi1", #[.word "16:16:8"]),
    ("abidefault", #[.word "1"]),
    ("syslook.writeBarrier", #[.str (GoStr.ofString "runtime.writeBarrier")]),
    ("syslook.wbZero", #[.str (GoStr.ofString "runtime.wbZero")]),
    ("syslook.wbMove", #[.str (GoStr.ofString "runtime.wbMove")])]
  typs := spTyps
  typeOrder := default
  tables := spTabs

/-! ## Kernel evaluation -/

theorem sp_check : (check spCheckEnv spFunc).toBool = true := by decide +kernel

/-- The pass succeeds, the checker accepts its result, which differs from the input and passes
`check`. -/
theorem sp_pass :
    (match writebarrierChecked spPassEnv spFunc with
      | .ok out => out.func != spFunc &&
          (check { tabs := out.tables, typs := spTyps } out.func).toBool
      | .error _ => false) = true := by
  decide +kernel

/-! ## The witness -/

/-- **Non-vacuity of `writebarrier_refines`**: writebarrier expands the barrier store of
`runtime_setProfLabel`, the checker accepts it, both functions pass `check`, and the result
refines the input on `WbPre` inputs. -/
theorem writebarrier_witness :
    ∃ out, writebarrierChecked spPassEnv spFunc = .ok out ∧ out.func ≠ spFunc ∧
      check spCheckEnv spFunc = .ok () ∧
      check { tabs := out.tables, typs := spTyps } out.func = .ok () ∧
      RefinesFrom WB.WbPre out.tables out.func spPassEnv.tables spFunc := by
  have hpc := sp_pass
  cases h : writebarrierChecked spPassEnv spFunc with
  | error e => rw [h] at hpc; cases hpc
  | ok out =>
    rw [h] at hpc
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hpc
    obtain ⟨hne, hc⟩ := hpc
    have hg : check { tabs := out.tables, typs := spTyps } out.func = .ok () := ok_of_toBool hc
    have hf : check spCheckEnv spFunc = .ok () := ok_of_toBool sp_check
    exact ⟨out, rfl, hne, hf, hg, GoFV.Proof.writebarrier_refines h hf hg⟩

/-- `env` with the runtime's write-barrier helpers (`Runtime.wbHelper`), which do not spill into
their caller's frame (`Env.noSpill`). -/
def withWbHelpers (env : Env) : Env :=
  { env with
    extern := fun name =>
      if name = "runtime.wbZero" ∨ name = "runtime.wbMove" then some Runtime.wbHelper
      else env.extern name
    noSpill := fun name => name == "runtime.wbZero" || name == "runtime.wbMove" || env.noSpill name }

theorem withWbHelpers_extern {env : Env} {name : String} {c : Contract}
    (h : (withWbHelpers env).extern name = some c) :
    c = Runtime.wbHelper ∨ env.extern name = some c := by
  simp only [withWbHelpers] at h
  split at h
  · exact .inl (Option.some.inj h).symm
  · exact .inr h

theorem withWbHelpers_wbHelpers (env : Env) : WB.WbHelpers (withWbHelpers env) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [withWbHelpers]

/-- `env`'s contracts keep `P` (`MemInv.ContractsOK`) with the write-barrier helpers too: these
return the memory they are given. -/
theorem withWbHelpers_contractsOK {P : Mem → Prop} {env : Env} (h : MemInv.ContractsOK P env) :
    MemInv.ContractsOK P (withWbHelpers env) := by
  intro name c hc args clo m ha hcl hm
  rcases withWbHelpers_extern hc with rfl | hc
  · exact ⟨hm, fun r hr => absurd hr List.not_mem_nil⟩
  · exact h name c hc args clo m ha hcl hm

/-- `Env.p1` with the write-barrier helpers and a read-only, zero `runtime.writeBarrier` flag. -/
def spEnv : Env :=
  { withWbHelpers Env.p1 with
    globals := [("runtime.writeBarrier", { data := #[.b 0, .b 0, .b 0, .b 0], writable := false })] }

/-- **Non-vacuity of `WbPre`**: `spEnv` (whose contracts panic or are the write-barrier helpers)
on the empty memory. -/
theorem wbPre_witness : WB.WbPre spEnv [.ptr ⟨.heap 0, 0⟩] {} := by
  refine ⟨⟨⟨{ data := #[.b 0, .b 0, .b 0, .b 0], writable := false }, by decide +kernel,
    rfl, by decide, fun i hi => ?_⟩, by decide +kernel⟩, ?_, withWbHelpers_wbHelpers Env.p1⟩
  · match i, hi with
    | 0, _ => exact ⟨0, rfl⟩
    | 1, _ => exact ⟨0, rfl⟩
    | 2, _ => exact ⟨0, rfl⟩
    | 3, _ => exact ⟨0, rfl⟩
  · refine withWbHelpers_contractsOK (env := Env.p1) ?_
    intro name c hc args clo m _ _ _
    simp only [Env.p1] at hc
    split at hc <;> cases hc <;> trivial

/-! ## A run with a helper call

A synthetic input in the shape of the corpus' `regexp.(*Regexp).Copy` (whose `Move` of a
160-byte `Regexp` is the smallest accepted run with a helper call of `quick-v4`), with a smaller
type:

```go
type pair struct{ a, b unsafe.Pointer }

func copyPair(p, q *pair) { *p = *q } // v4 = Move {pair} [16] p q mem
```

writebarrier expands the `Move` (a pointer-holding type, to a pointer argument) into the split on
the flag, the buffer block's `runtime.wbMove(type:main.pair, p, q)` call (`v13`, with the type
address `v12` in the split block and its memory `SelectN` as the `Phi`'s second argument) and the
re-emitted `Move` in the end block. -/

/-- `abiInfo` of `copyPair`: two pointer parameters in registers, no result. -/
def wcABI : CallABI :=
  { abi := 1, nin := 2, nout := 0, spillOff := 8, spillSize := 16, inRegs := 2, outRegs := 0,
    params := #[{ out := false, index := 0, type := 36, name := some 3, regs := #[0], offset := 0 },
                { out := false, index := 1, type := 36, name := some 4, regs := #[1],
                  offset := 8 }] }

/-- The definition tables: `pair` is type 35 (aux 5), `*pair` type 36, the parameters `p`, `q`
auxes 3, 4; the base types at `spTabs`' numbers. -/
def wcTabs : Tables where
  posBases := #[]
  types :=
    let t := Array.replicate 37 (none : Option TypeDef)
    let t := t.set! 1 (some (mkTy .FUNC (some 8) (some 8) (some 8) true true false false
      "func(*pair, *pair)" "func(*main.pair, *main.pair)"
      (.func 0 2 0 #[f10Field "p" 36 none, f10Field "q" 36 none])))
    let t := t.set! 2 (some (mkTy .UNSAFEPTR (some 8) (some 8) (some 8) true true true true
      "unsafe.Pointer" "unsafe.Pointer"))
    let t := t.set! 3 (some (spScalar .BOOL 1 "bool"))
    let t := t.set! 10 (some (spScalar .UINT32 4 "uint32"))
    let t := t.set! 16 (some (spScalar .UINTPTR 8 "uintptr"))
    let t := t.set! 20 (some (spPtr "*uint32" "*uint32" 10))
    let t := t.set! 22 (some (spPtr "*uintptr" "*uintptr" 16))
    let t := t.set! 28 (some (spPseudo .SSA "mem"))
    let t := t.set! 32 (some (spPseudo .RESULTS "mem" (.results #[28])))
    let t := t.set! 35 (some (mkTy .STRUCT (some 16) (some 8) (some 16) true false true true
      "pair" "main.pair" (.struct #[f10Field "a" 2 (some 0), f10Field "b" 2 (some 8)])))
    t.set! 36 (some (spPtr "*pair" "*main.pair" 35))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.copyPair}", kind := .call (some 2) (some wcABI) },
    some { fmt := GoStr.ofString "main.copyPair",
           kind := .sym (GoStr.ofString "main.copyPair") 1 "-" 0 {} none none none #[] none },
    some { fmt := GoStr.ofString "p",
           kind := .name (GoStr.ofString "p") .PPARAM 36 0 1 { used := true } p0 },
    some { fmt := GoStr.ofString "q",
           kind := .name (GoStr.ofString "q") .PPARAM 36 8 1 { used := true } p0 },
    some { fmt := GoStr.ofString "pair", kind := .type 35 },
    some { fmt := GoStr.ofString "p+0", kind := .nameOff 3 0 },
    some { fmt := GoStr.ofString "q+0", kind := .nameOff 4 0 }]
  slots := #[none, some { name := 3, type := 36, off := 0, splitOf := none, splitOffset := 0 },
    some { name := 4, type := 36, off := 0, splitOf := none, splitOffset := 0 }]

/-- `copyPair`, the input of `writebarrier`. -/
def wcFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 5
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[5] #[] #[] #[1, 2, 3, 4, 5])]
  valueTab := #[none,
    some (spV 1 .InitMem 28 0 none p0 1 #[]),
    some (spV 2 .ArgIntReg 36 0 (some 6) p0 1 #[]),
    some (spV 3 .ArgIntReg 36 1 (some 7) p0 1 #[]),
    some (spV 4 .Move 28 16 (some 5) p0 1 #[2, 3, 1]),
    some (spV 5 .MakeResult 32 0 none p0 1 #[4])]
  names := #[(1, #[2]), (2, #[3])]
  namedx := #[]
  splits := #[]
  canon := #[({ name := 3, type := 36, off := 0, splitOf := none, splitOffset := 0 }, 1),
    ({ name := 4, type := 36, off := 0, splitOf := none, splitOffset := 0 }, 2)]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := {}

def wcCheckEnv : CheckEnv := { tabs := wcTabs, typs := spTyps }

/-- What `writebarrier` reads of the environment: `spPassEnv`'s configuration. -/
def wcPassEnv : PassEnv where
  passName := "writebarrier"
  pkg := GoStr.ofString "main"
  funcName := GoStr.ofString "copyPair"
  abi := 1
  nosplit := false
  pgohot := false
  config := spPassEnv.config
  typs := spTyps
  typeOrder := default
  tables := wcTabs

theorem wc_check : (check wcCheckEnv wcFunc).toBool = true := by decide +kernel

/-- The pass succeeds, the checker accepts its result, whose value 13 calls `runtime.wbMove`, and
which passes `check`. -/
theorem wc_pass :
    (match writebarrierChecked wcPassEnv wcFunc with
      | .ok out => (out.func.value? 13).any (fun v => v.op == .StaticCall &&
            v.aux.bind out.tables.callee? == some "runtime.wbMove") &&
          (check { tabs := out.tables, typs := spTyps } out.func).toBool
      | .error _ => false) = true := by
  decide +kernel

/-- **Non-vacuity of `writebarrier_refines` for a run with a helper call**: writebarrier expands
the `Move` of `copyPair` into a run that calls `runtime.wbMove`, the checker accepts it, both
functions pass `check`, and the result refines the input on `WbPre` inputs (`wbPre_witness`). -/
theorem writebarrier_call_witness :
    ∃ out, writebarrierChecked wcPassEnv wcFunc = .ok out ∧
      (∃ v, out.func.value? 13 = some v ∧ v.op = .StaticCall ∧
        v.aux.bind out.tables.callee? = some "runtime.wbMove") ∧
      check wcCheckEnv wcFunc = .ok () ∧
      check { tabs := out.tables, typs := spTyps } out.func = .ok () ∧
      RefinesFrom WB.WbPre out.tables out.func wcPassEnv.tables wcFunc := by
  have hpc := wc_pass
  cases h : writebarrierChecked wcPassEnv wcFunc with
  | error e => rw [h] at hpc; cases hpc
  | ok out =>
    rw [h] at hpc
    simp only [Bool.and_eq_true] at hpc
    obtain ⟨hcall, hc⟩ := hpc
    obtain ⟨v, hv, hcv⟩ := (Option.any_eq_true _ _).1 hcall
    simp only [Bool.and_eq_true, beq_iff_eq] at hcv
    have hg : check { tabs := out.tables, typs := spTyps } out.func = .ok () := ok_of_toBool hc
    have hf : check wcCheckEnv wcFunc = .ok () := ok_of_toBool wc_check
    exact ⟨out, rfl, ⟨v, hv, hcv⟩, hf, hg, GoFV.Proof.writebarrier_refines h hf hg⟩

/-! ## Several `WB`s in one buffer block

A synthetic input that fills more than one write-barrier buffer:

```go
func fill9(p *[9]unsafe.Pointer, q unsafe.Pointer) {
	p[0], p[1], p[2], p[3], p[4], p[5], p[6], p[7], p[8] = q, q, q, q, q, q, q, q, q
}
```

Nine barrier stores (`v12` to `p`, `v13`–`v20` to `OffPtr [8(k+1)] p`) in one run record the new
pointer `q` once and the nine old pointers, ten buffer entries: writebarrier allocates `WB [8]`
(`v35`, on the run's input memory) and, after its eight buffer `Store`s, `WB [2]` (`v56`, on the
buffer `Store` `v53`). -/

/-- `abiInfo` of `fill9`: two pointer parameters in registers, no result. -/
def mwABI : CallABI :=
  { abi := 1, nin := 2, nout := 0, spillOff := 8, spillSize := 16, inRegs := 2, outRegs := 0,
    params := #[{ out := false, index := 0, type := 36, name := some 3, regs := #[0], offset := 0 },
                { out := false, index := 1, type := 2, name := some 4, regs := #[1],
                  offset := 8 }] }

/-- The definition tables: `[9]unsafe.Pointer` is type 35, `*[9]unsafe.Pointer` type 36, the
parameters `p`, `q` auxes 3, 4; the base types at `spTabs`' numbers. -/
def mwTabs : Tables where
  posBases := #[]
  types :=
    let t := Array.replicate 37 (none : Option TypeDef)
    let t := t.set! 1 (some (mkTy .FUNC (some 8) (some 8) (some 8) true true false false
      "func(*[9]unsafe.Pointer, unsafe.Pointer)" "func(*[9]unsafe.Pointer, unsafe.Pointer)"
      (.func 0 2 0 #[f10Field "p" 36 none, f10Field "q" 2 none])))
    let t := t.set! 2 (some (mkTy .UNSAFEPTR (some 8) (some 8) (some 8) true true true true
      "unsafe.Pointer" "unsafe.Pointer"))
    let t := t.set! 3 (some (spScalar .BOOL 1 "bool"))
    let t := t.set! 10 (some (spScalar .UINT32 4 "uint32"))
    let t := t.set! 16 (some (spScalar .UINTPTR 8 "uintptr"))
    let t := t.set! 20 (some (spPtr "*uint32" "*uint32" 10))
    let t := t.set! 22 (some (spPtr "*uintptr" "*uintptr" 16))
    let t := t.set! 28 (some (spPseudo .SSA "mem"))
    let t := t.set! 32 (some (spPseudo .RESULTS "mem" (.results #[28])))
    let t := t.set! 33 (some (spPtr "*unsafe.Pointer" "*unsafe.Pointer" 2))
    let t := t.set! 35 (some (mkTy .ARRAY (some 72) (some 8) (some 72) true false true false
      "[9]unsafe.Pointer" "[9]unsafe.Pointer" (.array 2 9)))
    t.set! 36 (some (spPtr "*[9]unsafe.Pointer" "*[9]unsafe.Pointer" 35))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.fill9}", kind := .call (some 2) (some mwABI) },
    some { fmt := GoStr.ofString "main.fill9",
           kind := .sym (GoStr.ofString "main.fill9") 1 "-" 0 {} none none none #[] none },
    some { fmt := GoStr.ofString "p",
           kind := .name (GoStr.ofString "p") .PPARAM 36 0 1 { used := true } p0 },
    some { fmt := GoStr.ofString "q",
           kind := .name (GoStr.ofString "q") .PPARAM 2 8 1 { used := true } p0 },
    some { fmt := GoStr.ofString "unsafe.Pointer", kind := .type 2 },
    some { fmt := GoStr.ofString "p+0", kind := .nameOff 3 0 },
    some { fmt := GoStr.ofString "q+0", kind := .nameOff 4 0 }]
  slots := #[none, some { name := 3, type := 36, off := 0, splitOf := none, splitOffset := 0 },
    some { name := 4, type := 2, off := 0, splitOf := none, splitOffset := 0 }]

/-- `fill9`, the input of `writebarrier`: `v12` stores `q` to `p`, `v(13+k)` to
`v(4+k) = OffPtr [8(k+1)] p`, each on the previous store's memory. -/
def mwFunc : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 21
  bidLast := 1
  blocks := #[1]
  blockTab := #[none, some (mkB 1 .Ret p0 #[21] #[] #[] (Array.range' 1 21))]
  valueTab := #[none,
    some (spV 1 .InitMem 28 0 none p0 1 #[]),
    some (spV 2 .ArgIntReg 36 0 (some 6) p0 9 #[]),
    some (spV 3 .ArgIntReg 2 1 (some 7) p0 9 #[])] ++
    ((List.range 8).map fun k =>
      some (spV (4 + k) .OffPtr 33 (Int64.ofNat (8 * (k + 1))) none p0 1 #[2])).toArray ++
    #[some (spV 12 .Store 28 0 (some 5) p0 1 #[2, 3, 1])] ++
    ((List.range 8).map fun k =>
      some (spV (13 + k) .Store 28 0 (some 5) p0 1 #[4 + k, 3, 12 + k])).toArray ++
    #[some (spV 21 .MakeResult 32 0 none p0 1 #[20])]
  names := #[(1, #[2]), (2, #[3])]
  namedx := #[]
  splits := #[]
  canon := #[({ name := 3, type := 36, off := 0, splitOf := none, splitOffset := 0 }, 1),
    ({ name := 4, type := 2, off := 0, splitOf := none, splitOffset := 0 }, 2)]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := {}

def mwCheckEnv : CheckEnv := { tabs := mwTabs, typs := spTyps }

/-- What `writebarrier` reads of the environment: `spPassEnv`'s configuration. -/
def mwPassEnv : PassEnv where
  passName := "writebarrier"
  pkg := GoStr.ofString "main"
  funcName := GoStr.ofString "fill9"
  abi := 1
  nosplit := false
  pgohot := false
  config := spPassEnv.config
  typs := spTyps
  typeOrder := default
  tables := mwTabs

theorem mw_check : (check mwCheckEnv mwFunc).toBool = true := by decide +kernel

/-- The pass succeeds, the checker accepts its result, whose values 35 and 56 are `WB [8]` and
`WB [2]`, the second on the memory of a buffer `Store` (value 53) of the first, and which passes
`check`. -/
theorem mw_pass :
    (match writebarrierChecked mwPassEnv mwFunc with
      | .ok out =>
          (out.func.value? 35).any (fun v => v.op == Op.WB && v.auxInt == 8) &&
          (out.func.value? 56).any (fun v => v.op == Op.WB && v.auxInt == 2 &&
            v.args == #[53]) &&
          (out.func.value? 53).any (fun v => v.op == Op.Store) &&
          (check { tabs := out.tables, typs := spTyps } out.func).toBool
      | .error _ => false) = true := by
  decide +kernel

/-- **Non-vacuity of `writebarrier_refines` for several `WB`s in one buffer block**: writebarrier
expands the nine barrier stores of `fill9` into a run whose buffer block allocates `WB [8]` and,
on a buffer `Store`'s memory, `WB [2]`; the checker accepts it, both functions pass `check`, and
the result refines the input on `WbPre` inputs (`wbPre_witness`). -/
theorem writebarrier_multi_witness :
    ∃ out, writebarrierChecked mwPassEnv mwFunc = .ok out ∧
      (∃ v, out.func.value? 35 = some v ∧ v.op = .WB ∧ v.auxInt = 8) ∧
      (∃ v, out.func.value? 56 = some v ∧ v.op = .WB ∧ v.auxInt = 2 ∧ v.args = #[53]) ∧
      (∃ v, out.func.value? 53 = some v ∧ v.op = .Store) ∧
      check mwCheckEnv mwFunc = .ok () ∧
      check { tabs := out.tables, typs := spTyps } out.func = .ok () ∧
      RefinesFrom WB.WbPre out.tables out.func mwPassEnv.tables mwFunc := by
  have hpc := mw_pass
  cases h : writebarrierChecked mwPassEnv mwFunc with
  | error e => rw [h] at hpc; cases hpc
  | ok out =>
    rw [h] at hpc
    simp only [Bool.and_eq_true] at hpc
    obtain ⟨⟨⟨h35, h56⟩, h53⟩, hc⟩ := hpc
    obtain ⟨v, hv, hv'⟩ := (Option.any_eq_true _ _).1 h35
    obtain ⟨w, hw, hw'⟩ := (Option.any_eq_true _ _).1 h56
    obtain ⟨s, hs, hs'⟩ := (Option.any_eq_true _ _).1 h53
    simp only [Bool.and_eq_true, beq_iff_eq] at hv' hw' hs'
    have hg : check { tabs := out.tables, typs := spTyps } out.func = .ok () := ok_of_toBool hc
    have hf : check mwCheckEnv mwFunc = .ok () := ok_of_toBool mw_check
    exact ⟨out, rfl, ⟨v, hv, hv'⟩, ⟨w, hw, hw'.1.1, hw'.1.2, hw'.2⟩, ⟨s, hs, hs'⟩, hf, hg,
      GoFV.Proof.writebarrier_refines h hf hg⟩

end GoFV.Proof.Witness
