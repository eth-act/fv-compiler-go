import GoFV.Proof.Pass.MemCombine
import GoFV.Proof.Witness.Clamp
import GoFV.Proof.Witness.Util
import GoFV.Proof.Witness.MemCombine

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: memcombine combines the stores of `encoding/binary.littleEndian.PutUint16`

`std/std/encoding/binary/littleEndian.PutUint16,1.ssa`, the output of section 30 (`dse`, the
input of `memcombine`), of the corpus `gofv-corpus/2aae1000ea1d/quick-v3`, with the definition
tables of the sections before it, transcribed by hand:

```go
func (littleEndian) PutUint16(b []byte, v uint16) {
	_ = b[1] // early bounds check to guarantee safety of writes below
	b[0] = byte(v)
	b[1] = byte(v >> 8)
}
```

memcombine combines the byte stores `v30` (`b[0] = Trunc16to8 v9`) and `v43` (`b[1] =
Trunc16to8 (Rsh16Ux64 v9 8)`) into one 2-byte store: `v43` becomes `Store {uint16} v36 v9 v1`
(its aux a new `type` aux), `v30` becomes `Invalid`. The checker `mcOK` accepts the result, input
and output pass `check` (kernel evaluation), so `memcombine_refines` applies: on `b = [0, 0]`,
`v = 0x0201` the output writes the bytes `1, 2`, as the source does.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof

/-- `abiInfo` of `littleEndian.PutUint16`: the empty receiver, the slice `b` in three integer
registers, `v` in the fourth. -/
def lePut16ABI : CallABI :=
  { abi := 1, nin := 3, nout := 0, spillOff := 8, spillSize := 32, inRegs := 4, outRegs := 0,
    params := #[{ out := false, index := 0, type := 2, name := some 3, regs := #[], offset := 8 },
                { out := false, index := 1, type := 3, name := some 4, regs := #[0, 1, 2],
                  offset := 0 },
                { out := false, index := 2, type := 5, name := some 5, regs := #[3],
                  offset := 24 }] }

/-- The definition tables of sections 0–30. -/
def lePut16Tabs : Tables where
  posBases := #[none, none,
    some { file := GoStr.ofString "encoding/binary/binary.go", line := 1, col := 1, inl := -1 }]
  types :=
    let t := Array.replicate 40 (none : Option TypeDef)
    let t := t.set! 1 (some (leU16Ty (mkT .FUNC (some 8) "method(littleEndian) func([]byte, uint16)"
      (.func 1 2 0 #[])) 8 { hasptr := true, direct := true }))
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
    let t := t.set! 35 (some (mkT .RESULTS none "mem" (.results #[31])))
    t.set! 39 (some (leU16Ty (mkT .PTR (some 8) "*byte" (.elem 4)) 8
      { hasptr := true, direct := true, comparable := true }))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{encoding/binary.littleEndian.PutUint16}",
           kind := .call (some 2) (some lePut16ABI) },
    some { fmt := GoStr.ofString "encoding/binary.littleEndian.PutUint16",
           kind := .sym (GoStr.ofString "encoding/binary.littleEndian.PutUint16") 1 "" 0 default
             none none none #[] none },
    some { fmt := GoStr.ofString "~p0",
           kind := .name (GoStr.ofString "~p0") .PPARAM 2 0 1 {} (pos 2 75 7 0) },
    some { fmt := GoStr.ofString "b",
           kind := .name (GoStr.ofString "b") .PPARAM 3 0 1 { used := true } (pos 2 75 31 0) },
    some { fmt := GoStr.ofString "v",
           kind := .name (GoStr.ofString "v") .PPARAM 5 24 1 { used := true } (pos 2 75 41 0) },
    some { fmt := GoStr.ofString "byte", kind := .type 4 },
    some { fmt := GoStr.ofString "v+0", kind := .nameOff 5 0 },
    some { fmt := GoStr.ofString "b+0", kind := .nameOff 4 0 },
    some { fmt := GoStr.ofString "b+8", kind := .nameOff 4 8 },
    some { fmt := GoStr.ofString "b+16", kind := .nameOff 4 16 }]
  slots := #[none,
    some { name := 3, type := 2, off := 0, splitOf := none, splitOffset := 0 },
    some { name := 4, type := 3, off := 0, splitOf := none, splitOffset := 0 },
    some { name := 5, type := 5, off := 0, splitOf := none, splitOffset := 0 },
    some { name := 4, type := 39, off := 0, splitOf := none, splitOffset := 0 },
    some { name := 4, type := 14, off := 8, splitOf := none, splitOffset := 0 },
    some { name := 4, type := 14, off := 16, splitOf := none, splitOffset := 0 }]

/-- The values of section 30, by ID. -/
def lePut16Values : Array (Option Value) :=
  let t := Array.replicate 45 (none : Option Value)
  let t := t.set! 1 (some (leU16V 1 .InitMem 31 0 none p0 2 #[] 1))
  let t := t.set! 9 (some (leU16V 9 .ArgIntReg 5 3 (some 7) (pos 2 76 8 0) 2 #[] 1))
  let t := t.set! 10 (some (leU16V 10 .Const64 14 1 none p0 2 #[] 1))
  let t := t.set! 32 (some (leU16V 32 .Const64 17 8 none p0 1 #[] 1))
  let t := t.set! 12 (some (leU16V 12 .IsInBounds 6 0 none (pos 2 76 7 1) 1 #[10, 23] 1))
  let t := t.set! 36 (some (leU16V 36 .ArgIntReg 39 0 (some 8) (pos 2 76 8 2) 2 #[] 1))
  let t := t.set! 23 (some (leU16V 23 .ArgIntReg 14 1 (some 9) (pos 2 76 8 2) 2 #[] 1))
  let t := t.set! 14 (some (leU16V 14 .PanicBounds 31 0 none (pos 2 76 7 0) 1 #[10, 23, 1] 3))
  let t := t.set! 20 (some (leU16V 20 .Trunc16to8 4 0 none (pos 2 77 14 1) 1 #[9] 6))
  let t := t.set! 33 (some (leU16V 33 .Rsh16Ux64 5 1 none (pos 2 78 16 1) 1 #[9, 32] 6))
  let t := t.set! 30 (some (leU16V 30 .Store 31 0 (some 6) (pos 2 77 7 0) 1 #[36, 20, 1] 6))
  let t := t.set! 34 (some (leU16V 34 .Trunc16to8 4 0 none (pos 2 78 16 0) 1 #[33] 6))
  let t := t.set! 41 (some (leU16V 41 .OffPtr 39 1 none (pos 2 78 3 0) 1 #[36] 6))
  let t := t.set! 43 (some (leU16V 43 .Store 31 0 (some 6) (pos 2 78 7 0) 1 #[41, 34, 30] 6))
  t.set! 44 (some (leU16V 44 .MakeResult 35 0 none (pos 2 79 1 1) 1 #[43] 6))

/-- The blocks of section 30, by ID. -/
def lePut16Blocks : Array (Option Block) := #[none,
  some { mkB 1 .If (pos 2 76 8 0) #[12] #[⟨6, 0⟩, ⟨3, 0⟩] #[] #[1, 9, 10, 32, 12, 36, 23] with
    likely := .likely },
  some (mkB 2 .Invalid (pos 2 77 4 0) #[] #[] #[] #[]),
  some (mkB 3 .Exit (pos 2 76 8 0) #[14] #[] #[⟨1, 1⟩] #[14]),
  some (mkB 4 .Invalid (pos 2 78 4 0) #[] #[] #[] #[]),
  none,
  some (mkB 6 .Ret (pos 2 79 1 0) #[44] #[] #[⟨1, 0⟩] #[20, 33, 30, 34, 41, 43, 44])]

/-- `littleEndian.PutUint16`, section 30 (the input of `memcombine`). -/
def lePut16 : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 44
  bidLast := 7
  blocks := #[1, 2, 3, 4, 6]
  blockTab := lePut16Blocks
  valueTab := lePut16Values
  names := #[(3, #[9]), (4, #[36]), (5, #[23])]
  namedx := #[]
  splits := #[(⟨2, 0, 39⟩, 4), (⟨2, 8, 14⟩, 5), (⟨2, 16, 14⟩, 6)]
  canon := #[({ name := 3, type := 2, off := 0, splitOf := none, splitOffset := 0 }, 1),
    ({ name := 4, type := 3, off := 0, splitOf := none, splitOffset := 0 }, 2),
    ({ name := 5, type := 5, off := 0, splitOf := none, splitOffset := 0 }, 3)]
  consts := #[(1, #[10]), (8, #[32])]
  freeValues := [39, 26, 22, 25, 35, 37, 40, 24, 8, 27, 11, 42, 38, 28, 31, 29, 13, 21, 19, 18, 17,
    16, 15, 7, 6, 5, 4, 3, 2]
  freeBlocks := [7, 5]
  cache := { auxmap := some #[(some 4, 1), (some 5, 2), (none, 3)],
             lineStarts := some #[⟨2, some (76, 79), #[]⟩] }

def lePut16CheckEnv : CheckEnv := { tabs := lePut16Tabs, typs := leU16Typs }

/-- What `memcombine` reads of the export's environment. -/
def lePut16PassEnv : PassEnv :=
  { leU16PassEnv with funcName := GoStr.ofString "littleEndian.PutUint16", tables := lePut16Tabs }

/-- A heap slice of two zero bytes. -/
def lePut16Mem : Mem :=
  { blocks := #[(.heap 0, { data := #[.b 0, .b 0] })], nextHeap := 1 }

/-- The empty receiver, `b = [0, 0]` (data pointer, length, capacity) and `v = 0x0201`. -/
def lePut16Args : List Val :=
  [.agg [], .agg [.ptr ⟨.heap 0, 0⟩, .i64 2, .i64 2], .int .w16 0x0201]

/-- The outcome returns no result and the slice holds `1, 2`. -/
def wrote12 : Outcome → Bool
  | .returned [] m => m.read ⟨.heap 0, 0⟩ 2 == some #[.b 1, .b 2]
  | _ => false

theorem wrote12_iff {o : Outcome} :
    wrote12 o = true ↔ ∃ m, o = .returned [] m ∧ m.read ⟨.heap 0, 0⟩ 2 = some #[.b 1, .b 2] := by
  constructor
  · intro h
    match o, h with
    | .returned [] m, h =>
      simp only [wrote12, beq_iff_eq] at h
      exact ⟨m, rfl, h⟩
  · rintro ⟨m, rfl, h⟩
    simp only [wrote12]
    exact beq_iff_eq.2 h

/-! ## Kernel evaluation -/

theorem lePut16_check : (check lePut16CheckEnv lePut16).toBool = true := by decide +kernel

/-- The pass succeeds, the checker accepts its result (`v43` becomes a 2-byte `Store` of `v9`),
and the result passes `check` in its tables. -/
theorem lePut16_pass :
    (match memcombineChecked lePut16PassEnv lePut16 with
      | .ok out => out.func != lePut16 &&
          (check { lePut16CheckEnv with tabs := out.tables } out.func).toBool &&
          (out.func.value? 43).map (fun v => (v.op, v.args)) == some (.Store, #[36, 9, 1])
      | .error _ => false) = true := by
  decide +kernel

/-- `PutUint16([0, 0], 0x0201)` writes `1, 2`, with fuel 2 (the entry, then the `Ret`). -/
theorem lePut16_run : wrote12 (run Env.p1 lePut16Tabs lePut16 lePut16Args lePut16Mem 2) = true := by
  decide +kernel

/-! ## The witness -/

/-- **Non-vacuity of `memcombine_refines` for stores**: memcombine combines `PutUint16`'s two
byte stores (`v43` becomes a 2-byte `Store` of `v9`), and the output writes the source's bytes. -/
theorem memcombine_store_witness :
    ∃ out, memcombineChecked lePut16PassEnv lePut16 = .ok out ∧ out.func ≠ lePut16 ∧
      (out.func.value? 43).map (fun v => (v.op, v.args)) = some (.Store, #[36, 9, 1]) ∧
      ∃ fuel m, run Env.p1 out.tables out.func lePut16Args lePut16Mem fuel = .returned [] m ∧
        m.read ⟨.heap 0, 0⟩ 2 = some #[.b 1, .b 2] := by
  have hpc := lePut16_pass
  cases h : memcombineChecked lePut16PassEnv lePut16 with
  | error e => rw [h] at hpc; cases hpc
  | ok out =>
    rw [h] at hpc
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hpc
    obtain ⟨⟨hne, hc⟩, h43⟩ := hpc
    have hg := ok_of_toBool hc
    have hf : check lePut16CheckEnv lePut16 = .ok () := ok_of_toBool lePut16_check
    have hr := GoFV.Proof.MemCombine.memcombine_refines h hf hg
    obtain ⟨m, hm, hrd⟩ := wrote12_iff.1 lePut16_run
    have hm' : run Env.p1 lePut16PassEnv.tables lePut16 lePut16Args lePut16Mem 2 =
        .returned [] m := hm
    obtain ⟨fuel', ho⟩ := hr Env.p1 Env.p1_mono lePut16Args lePut16Mem 2 (by rw [hm']; trivial)
    rw [hm'] at ho
    refine ⟨out, rfl, hne, h43, fuel', ?_⟩
    generalize run Env.p1 out.tables out.func lePut16Args lePut16Mem fuel' = o at ho ⊢
    cases ho with
    | returned hl hmm =>
      cases hl
      obtain ⟨bs', hrd', hb⟩ := hmm.read hrd
      refine ⟨_, rfl, ?_⟩
      rw [hrd', ← hb.eq (by decide)]

end GoFV.Proof.Witness
