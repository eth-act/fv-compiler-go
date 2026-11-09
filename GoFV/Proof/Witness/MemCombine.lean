import GoFV.Proof.Pass.MemCombine
import GoFV.Proof.Witness.Clamp
import GoFV.Proof.Witness.Util

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: memcombine on `encoding/binary.littleEndian.Uint16`

`std/std/encoding/binary/littleEndian.Uint16,1.ssa`, the output of section 30 (`dse`, the input
of `memcombine`), of the corpus `gofv-corpus/2aae1000ea1d/quick-v1`, with the definition tables
of the sections before it, transcribed by hand:

```go
func (littleEndian) Uint16(b []byte) uint16 {
	_ = b[1] // bounds check hint to compiler; see golang.org/issue/14808
	return uint16(b[0]) | uint16(b[1])<<8
}
```

memcombine combines the two byte loads `v28` (`b[0]`) and `v38` (`b[1]`) into one 2-byte load
`v34` and makes their `Or16` `v42` a `Copy v34`. The checker `mcOK` accepts the result, input and
output pass `check` (kernel evaluation), so `memcombine_refines` applies: on `b = [1, 2]` the
output returns `0x0201`, as the source does.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof

/-- `abiInfo` of `littleEndian.Uint16`: the empty receiver, the slice `b` in three integer
registers, the result in one. -/
def leU16ABI : CallABI :=
  { abi := 1, nin := 2, nout := 1, spillOff := 8, spillSize := 24, inRegs := 3, outRegs := 1,
    params := #[{ out := false, index := 0, type := 2, name := some 3, regs := #[], offset := 8 },
                { out := false, index := 1, type := 3, name := some 4, regs := #[0, 1, 2],
                  offset := 0 },
                { out := true, index := 0, type := 5, name := some 5, regs := #[0],
                  offset := -1 }] }

/-- `t` with alignment `a` and flags `fl`. -/
def leU16Ty (t : TypeDef) (a : Int) (fl : TypeFlags) : TypeDef := { t with align := some a, flags := fl }

/-- A scalar type (`comparable,named`). -/
def leU16Scalar (kind : TypeKind) (size : Int) (s : String) : TypeDef :=
  leU16Ty (mkT kind (some size) s) size { comparable := true, named := true }

/-- The definition tables of sections 0–30. -/
def leU16Tabs : Tables where
  posBases := #[none, none,
    some { file := GoStr.ofString "encoding/binary/binary.go", line := 1, col := 1, inl := -1 }]
  types :=
    let t := Array.replicate 41 (none : Option TypeDef)
    let t := t.set! 1 (some (leU16Ty (mkT .FUNC (some 8) "method(littleEndian) func([]byte) uint16"
      (.func 1 1 1 #[])) 8 { hasptr := true, direct := true }))
    let t := t.set! 2 (some (leU16Ty (mkT .STRUCT (some 0) "littleEndian") 1
      { comparable := true, named := true }))
    let t := t.set! 3 (some (leU16Ty (mkT .SLICE (some 24) "[]byte" (.elem 4)) 8 { hasptr := true }))
    let t := t.set! 4 (some (leU16Scalar .UINT8 1 "byte"))
    let t := t.set! 5 (some (leU16Scalar .UINT16 2 "uint16"))
    let t := t.set! 6 (some (leU16Scalar .BOOL 1 "bool"))
    let t := t.set! 11 (some (leU16Scalar .UINT8 1 "uint8"))
    let t := t.set! 12 (some (leU16Scalar .UINT32 4 "uint32"))
    let t := t.set! 13 (some (leU16Scalar .UINT64 8 "uint64"))
    let t := t.set! 14 (some (leU16Scalar .INT 8 "int"))
    let t := t.set! 17 (some (leU16Scalar .UINT 8 "uint"))
    let t := t.set! 18 (some (leU16Scalar .UINTPTR 8 "uintptr"))
    let t := t.set! 31 (some (mkT .SSA none "mem"))
    let t := t.set! 39 (some (leU16Ty (mkT .PTR (some 8) "*byte" (.elem 4)) 8
      { hasptr := true, direct := true, comparable := true }))
    t.set! 40 (some (mkT .RESULTS none "uint16,mem" (.results #[5, 31])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{encoding/binary.littleEndian.Uint16}",
           kind := .call (some 2) (some leU16ABI) },
    some { fmt := GoStr.ofString "encoding/binary.littleEndian.Uint16",
           kind := .sym (GoStr.ofString "encoding/binary.littleEndian.Uint16") 1 "" 0 default none
             none none #[] none },
    some { fmt := GoStr.ofString "~p0",
           kind := .name (GoStr.ofString "~p0") .PPARAM 2 0 1 {} (pos 2 69 7 0) },
    some { fmt := GoStr.ofString "b",
           kind := .name (GoStr.ofString "b") .PPARAM 3 0 1 { used := true } (pos 2 69 28 0) },
    some { fmt := GoStr.ofString "~r0",
           kind := .name (GoStr.ofString "~r0") .PPARAMOUT 5 0 1 {} (pos 2 69 38 0) },
    some { fmt := GoStr.ofString "b+0", kind := .nameOff 4 0 },
    some { fmt := GoStr.ofString "b+8", kind := .nameOff 4 8 },
    some { fmt := GoStr.ofString "b+16", kind := .nameOff 4 16 }]
  slots := #[none,
    some { name := 3, type := 2, off := 0, splitOf := none, splitOffset := 0 },
    some { name := 4, type := 3, off := 0, splitOf := none, splitOffset := 0 },
    some { name := 4, type := 39, off := 0, splitOf := none, splitOffset := 0 },
    some { name := 4, type := 14, off := 8, splitOf := none, splitOffset := 0 },
    some { name := 4, type := 14, off := 16, splitOf := none, splitOffset := 0 }]

/-- A value of `littleEndian.Uint16`. -/
def leU16V (id : ID) (op : Op) (t : TypeRef) (auxInt : Int64) (aux : Option AuxRef) (p : Pos)
    (uses : Nat) (args : Array ID) (blk : ID) : Value :=
  { id, op, type := t, auxInt, aux, pos := p, uses, args, block := blk }

/-- The values of section 30, by ID. -/
def leU16Values : Array (Option Value) :=
  let t := Array.replicate 44 (none : Option Value)
  let t := t.set! 1 (some (leU16V 1 .InitMem 31 0 none p0 4 #[] 1))
  let t := t.set! 10 (some (leU16V 10 .Const64 14 1 none p0 2 #[] 1))
  let t := t.set! 40 (some (leU16V 40 .Const64 17 8 none p0 1 #[] 1))
  let t := t.set! 12 (some (leU16V 12 .IsInBounds 6 0 none (pos 2 70 7 1) 1 #[10, 21] 1))
  let t := t.set! 31 (some (leU16V 31 .ArgIntReg 39 0 (some 6) (pos 2 70 8 2) 2 #[] 1))
  let t := t.set! 21 (some (leU16V 21 .ArgIntReg 14 1 (some 7) (pos 2 70 8 2) 2 #[] 1))
  let t := t.set! 14 (some (leU16V 14 .PanicBounds 31 0 none (pos 2 70 7 0) 1 #[10, 21, 1] 3))
  let t := t.set! 28 (some (leU16V 28 .Load 4 0 none (pos 2 71 17 1) 1 #[31, 1] 6))
  let t := t.set! 29 (some (leU16V 29 .ZeroExt8to16 5 0 none (pos 2 71 17 0) 1 #[28] 6))
  let t := t.set! 36 (some (leU16V 36 .OffPtr 39 1 none (pos 2 71 32 0) 1 #[31] 6))
  let t := t.set! 38 (some (leU16V 38 .Load 4 0 none (pos 2 71 32 0) 1 #[36, 1] 6))
  let t := t.set! 39 (some (leU16V 39 .ZeroExt8to16 5 0 none (pos 2 71 32 0) 1 #[38] 6))
  let t := t.set! 41 (some (leU16V 41 .Lsh16x64 5 1 none (pos 2 71 36 0) 1 #[39, 40] 6))
  let t := t.set! 42 (some (leU16V 42 .Or16 5 0 none (pos 2 71 22 0) 1 #[29, 41] 6))
  t.set! 43 (some (leU16V 43 .MakeResult 40 0 none (pos 2 71 2 0) 1 #[42, 1] 6))

/-- The blocks of section 30, by ID. -/
def leU16Blocks : Array (Option Block) := #[none,
  some { mkB 1 .If (pos 2 70 8 0) #[12] #[⟨6, 0⟩, ⟨3, 0⟩] #[] #[1, 10, 40, 12, 31, 21] with
    likely := .likely },
  some (mkB 2 .Invalid (pos 2 71 18 1) #[] #[] #[] #[]),
  some (mkB 3 .Exit (pos 2 70 8 0) #[14] #[] #[⟨1, 1⟩] #[14]),
  some (mkB 4 .Invalid (pos 2 71 33 0) #[] #[] #[] #[]),
  none,
  some (mkB 6 .Ret (pos 2 71 38 1) #[43] #[] #[⟨1, 0⟩] #[28, 29, 36, 38, 39, 41, 42, 43])]

/-- `littleEndian.Uint16`, section 30 (the input of `memcombine`). -/
def leU16 : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 43
  bidLast := 7
  blocks := #[1, 2, 3, 4, 6]
  blockTab := leU16Blocks
  valueTab := leU16Values
  names := #[(3, #[31]), (4, #[21])]
  namedx := #[]
  splits := #[(⟨2, 0, 39⟩, 3), (⟨2, 8, 14⟩, 4), (⟨2, 16, 14⟩, 5)]
  canon := #[({ name := 3, type := 2, off := 0, splitOf := none, splitOffset := 0 }, 1),
    ({ name := 4, type := 3, off := 0, splitOf := none, splitOffset := 0 }, 2)]
  consts := #[(1, #[10]), (8, #[40])]
  freeValues := [34, 24, 20, 23, 30, 32, 35, 22, 8, 25, 11, 37, 33, 26, 27, 13, 19, 18, 17, 16, 15,
    9, 7, 6, 5, 4, 3, 2]
  freeBlocks := [7, 5]
  cache := { auxmap := some #[(some 4, 1), (none, 2)],
             lineStarts := some #[⟨2, some (70, 71), #[]⟩] }

/-- `Config.Types` (the `typs` line of section 0). -/
def leU16Typs : Array (String × TypeRef) :=
  #[("Bool", 6), ("UInt8", 11), ("UInt16", 5), ("UInt32", 12), ("UInt64", 13), ("Int", 14),
    ("UInt", 17), ("Uintptr", 18), ("BytePtr", 20), ("Mem", 31)]

def leU16CheckEnv : CheckEnv := { tabs := leU16Tabs, typs := leU16Typs }

/-- What `memcombine` reads of the export's environment. -/
def leU16PassEnv : PassEnv where
  passName := "memcombine"
  pkg := GoStr.ofString "encoding/binary"
  funcName := GoStr.ofString "littleEndian.Uint16"
  abi := 1
  nosplit := false
  pgohot := false
  config := #[("arch", #[.word "arm64"]), ("ptrsize", #[.word "8"]), ("regsize", #[.word "8"]),
    ("bigendian", #[.word "0"]), ("unalignedok", #[.word "1"]), ("havebswap64", #[.word "1"]),
    ("havebswap32", #[.word "1"]), ("havebswap16", #[.word "1"])]
  typs := leU16Typs
  typeOrder := default
  tables := leU16Tabs

/-- A heap slice of the two bytes `1, 2`. -/
def leU16Mem : Mem :=
  { blocks := #[(.heap 0, { data := #[.b 1, .b 2] })], nextHeap := 1 }

/-- The empty receiver and `b = [1, 2]` (data pointer, length, capacity). -/
def leU16Args : List Val := [.agg [], .agg [.ptr ⟨.heap 0, 0⟩, .i64 2, .i64 2]]

/-- The outcome returns the single `uint16` result `v`. -/
def returnsU16 : Outcome → BitVec 16 → Bool
  | .returned [.int .w16 x] _, v => x == v
  | _, _ => false

theorem returnsU16_iff {o : Outcome} {v : BitVec 16} :
    returnsU16 o v = true ↔ ∃ m, o = .returned [.int .w16 v] m := by
  constructor
  · intro h
    match o, h with
    | .returned [.int .w16 x] m, h =>
      simp only [returnsU16, beq_iff_eq] at h
      exact ⟨m, by rw [h]⟩
  · rintro ⟨m, rfl⟩
    simp [returnsU16]

/-! ## Kernel evaluation -/

theorem leU16_check : (check leU16CheckEnv leU16).toBool = true := by decide +kernel

/-- The pass succeeds, the checker accepts its result (`v42` becomes `Copy v34`, `v34` a 2-byte
`Load`), and the result passes `check`. -/
theorem leU16_pass :
    (match memcombineChecked leU16PassEnv leU16 with
      | .ok out => out.func != leU16 && (check leU16CheckEnv out.func).toBool &&
          (out.func.value? 42).map (fun v => (v.op, v.args)) == some (.Copy, #[34]) &&
          (out.func.value? 34).map (fun v => (v.op, v.type, v.args)) == some (.Load, 5, #[31, 1])
      | .error _ => false) = true := by
  decide +kernel

/-- `Uint16([1, 2]) = 0x0201`, with fuel 2 (the entry, then the `Ret`). -/
theorem leU16_run : returnsU16 (run Env.p1 leU16Tabs leU16 leU16Args leU16Mem 2) 0x0201 = true := by
  decide +kernel

/-! ## The witness -/

/-- **Non-vacuity of `memcombine_refines`**: memcombine combines `Uint16`'s two byte loads (`v42`
becomes `Copy v34` of a 2-byte `Load`), and the output returns the source's result. -/
theorem memcombine_witness :
    ∃ out, memcombineChecked leU16PassEnv leU16 = .ok out ∧ out.func ≠ leU16 ∧
      (out.func.value? 42).map (fun v => (v.op, v.args)) = some (.Copy, #[34]) ∧
      ∃ fuel m, run Env.p1 out.tables out.func leU16Args leU16Mem fuel =
        .returned [.int .w16 0x0201] m := by
  have hpc := leU16_pass
  cases h : memcombineChecked leU16PassEnv leU16 with
  | error e => rw [h] at hpc; cases hpc
  | ok out =>
    rw [h] at hpc
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hpc
    obtain ⟨⟨⟨hne, hc⟩, h42⟩, -⟩ := hpc
    have hg : check leU16CheckEnv out.func = .ok () := ok_of_toBool hc
    have hf : check leU16CheckEnv leU16 = .ok () := ok_of_toBool leU16_check
    have hr := GoFV.Proof.MemCombine.memcombine_refines h hf hg
    obtain ⟨m, hm⟩ := returnsU16_iff.1 leU16_run
    have hm' : run Env.p1 leU16PassEnv.tables leU16 leU16Args leU16Mem 2 =
        .returned [.int .w16 0x0201] m := hm
    obtain ⟨fuel', ho⟩ := hr Env.p1 Env.p1_mono leU16Args leU16Mem 2 (by rw [hm']; trivial)
    rw [hm'] at ho
    refine ⟨out, rfl, hne, h42, fuel', ?_⟩
    generalize run Env.p1 out.tables out.func leU16Args leU16Mem fuel' = o at ho ⊢
    cases ho with
    | returned hl =>
      cases hl with
      | cons h1 t =>
        cases t
        cases h1
        exact ⟨_, rfl⟩

end GoFV.Proof.Witness
