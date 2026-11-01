import GoFV.Proof.Witness.DecodedLen

/-!
# Witness function: `runtime.tracefpunwindoff` from the corpus

`std/std/runtime/tracefpunwindoff,1.ssa`, the output of section 10 (`generic cse`, the input
of `phiopt`), of the corpus `gofv-corpus/2aae1000ea1d/plain` (quick-v1), transcribed by hand
(the tables: the definitions `check`, `phiopt` and `run` read; the struct type of
`runtime.debug`, `t35`, is kept to its size):

```go
func tracefpunwindoff() bool {
	return debug.tracefpunwindoff != 0 || (goarch.ArchFamily != goarch.AMD64 && goarch.ArchFamily != goarch.ARM64)
}
```

On arm64 the second disjunct is `false`, so the result is the `Phi` of `true` (from the `If`)
and `false` (through `b3`); phiopt rewrites it to `Copy v10` (the `If`'s control).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem

/-- `abiInfo` of `tracefpunwindoff`: no parameters, one result. -/
def tfABI : CallABI :=
  { abi := 1, nin := 0, nout := 1, spillOff := 8, spillSize := 0, inRegs := 0, outRegs := 1,
    params := #[{ out := true, index := 0, type := 2, name := some 3, regs := #[0],
                  offset := -1 }] }

/-- The definition tables `check`, `phiopt` and `run` read. -/
def tfTabs : Tables where
  types :=
    let t := Array.replicate 39 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func() bool" (.func 0 0 1 #[])))
    let t := t.set! 2 (some (mkT .BOOL (some 1) "bool"))
    let t := t.set! 5 (some (mkT .INT32 (some 4) "int32"))
    let t := t.set! 7 (some (mkT .UINT8 (some 1) "uint8"))
    let t := t.set! 15 (some (mkT .UINTPTR (some 8) "uintptr"))
    let t := t.set! 18 (some (mkT .PTR (some 8) "*int32" (.elem 5)))
    let t := t.set! 28 (some (mkT .SSA none "mem"))
    let t := t.set! 34 (some (mkT .PTR (some 8) "*struct { … }" (.elem 35)))
    let t := t.set! 35 (some (mkT .STRUCT (some 136) "struct { … }"))
    t.set! 38 (some (mkT .RESULTS none "bool,mem" (.results #[2, 28])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{runtime.tracefpunwindoff}",
           kind := .call (some 2) (some tfABI) },
    some { fmt := GoStr.ofString "runtime.tracefpunwindoff",
           kind := .sym (GoStr.ofString "runtime.tracefpunwindoff") 1 "" 0 default none none
             none #[] none },
    some (paramNameT "~r0" .PPARAMOUT 2 0),
    some { fmt := GoStr.ofString "runtime.debug",
           kind := .sym (GoStr.ofString "runtime.debug") 0 "" 0 default none none none #[]
             none }]

/-- The values, by ID. -/
def tfValues : Array (Option Value) := #[none,
  some (mkVi 1 .InitMem 28 0 p0 2 #[] 1),
  none,
  some (mkVi 3 .SB 15 0 p0 1 #[] 1),
  none,
  some (mkVi 5 .ConstBool 2 0 p0 1 #[] 1),
  some (mkV 6 .Addr 34 (some 4) p0 1 #[3] 1),
  some (mkVi 7 .OffPtr 18 88 (pos 203 260 14 0) 1 #[6] 1),
  some (mkVi 8 .Load 5 0 (pos 203 260 14 1) 1 #[7, 1] 1),
  some (mkVi 9 .Const32 5 0 p0 1 #[] 1),
  some (mkVi 10 .Neq32 2 0 (pos 203 260 32 0) 1 #[8, 9] 1),
  some (mkVi 11 .Phi 2 0 (pos 203 260 2 0) 1 #[12, 5] 2),
  some (mkVi 12 .ConstBool 2 1 p0 1 #[] 1),
  some (mkVi 13 .MakeResult 38 0 (pos 203 260 2 0) 1 #[11, 1] 2)]

/-- The blocks, by ID. -/
def tfBlocks : Array (Option Block) := #[none,
  some (mkB 1 .If (pos 203 260 37 0) #[10] #[⟨2, 0⟩, ⟨3, 0⟩] #[] #[1, 3, 5, 6, 7, 8, 9, 10, 12]),
  some (mkB 2 .Ret (pos 203 260 2 1) #[13] #[] #[⟨1, 0⟩, ⟨3, 0⟩] #[11, 13]),
  some (mkB 3 .Plain (pos 203 260 14 0) #[] #[⟨2, 1⟩] #[⟨1, 1⟩] #[])]

/-- `tracefpunwindoff`, the input of `phiopt`. -/
def tracefp : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 13
  bidLast := 3
  blocks := #[1, 2, 3]
  blockTab := tfBlocks
  valueTab := tfValues
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[(0, #[5, 9]), (1, #[12])]
  freeValues := [4, 2]
  freeBlocks := []
  cache := {}

/-- A memory holding `runtime.debug` (136 bytes) with `debug.tracefpunwindoff` (offset 88)
set to `d`. -/
def tfMem (d : BitVec 8) : Mem :=
  { blocks := #[(.global "runtime.debug",
      { data := (Array.replicate 136 (Byte.b 0)).set! 88 (Byte.b d) })] }

/-- The outcome returns the single `bool` result `b`. -/
def returnsBool : Outcome → Bool → Bool
  | .returned [.bool x] _, b => x == b
  | _, _ => false

theorem returnsBool_iff {o : Outcome} {b : Bool} :
    returnsBool o b = true ↔ ∃ m, o = .returned [.bool b] m := by
  constructor
  · intro h
    match o, h with
    | .returned [.bool x] m, h =>
      simp only [returnsBool, beq_iff_eq] at h
      exact ⟨m, by rw [h]⟩
  · rintro ⟨m, rfl⟩
    simp [returnsBool]

/-- `tracefpunwindoff()` is `true` with `debug.tracefpunwindoff = 1` and `false` with `0`, with
fuel 2 (entry, then `b2`) and 3 (entry, `b3`, `b2`). -/
theorem tracefp_run :
    returnsBool (run Env.p1 tfTabs tracefp [] (tfMem 1) 2) true = true ∧
    returnsBool (run Env.p1 tfTabs tracefp [] (tfMem 0) 3) false = true := by
  decide +kernel

end GoFV.Proof.Witness
