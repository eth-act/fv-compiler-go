import GoFV.Proof.Witness.Clamp

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function: `slices.nextPowerOfTwo` from the corpus

`std/std/slices/nextPowerOfTwo,1.ssa`, section 26 (`sccp`, the input of `generic deadcode`), of
the corpus `gofv-corpus/2aae1000ea1d/plain`, transcribed by hand (the tables: the definitions
`check`, `deadcode` and `run` read):

```go
func nextPowerOfTwo(length int) uint {
	shift := bits.Len(uint(length))
	return uint(1) << shift
}
```

The entry block is a `First` block whose second successor is the never-taken `Exit` of the
shift's `panicshift` call: `generic deadcode` removes that block and the call, and turns the
entry into a `Plain` block (`GoFV.Proof.Witness.Deadcode`).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem

def np2ABI : CallABI :=
  { abi := 1, nin := 1, nout := 1, spillOff := 8, spillSize := 8, inRegs := 1, outRegs := 1,
    params := #[{ out := false, index := 0, type := 2, name := some 3, regs := #[0], offset := 0 },
                { out := true, index := 0, type := 3, name := some 4, regs := #[0],
                  offset := -1 }] }

def panicshiftABI : CallABI :=
  { abi := 1, nin := 0, nout := 0, spillOff := 8, spillSize := 0, inRegs := 0, outRegs := 0,
    params := #[] }

def symDef (s : String) : AuxDef :=
  { fmt := GoStr.ofString s,
    kind := .sym (GoStr.ofString s) 1 "" 0 default none none none #[] none }

/-- The definition tables of sections 0–26. -/
def np2Tabs : Tables where
  types :=
    let t := Array.replicate 35 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(int) uint" (.func 0 1 1 #[])))
    let t := t.set! 2 (some (mkT .INT (some 8) "int"))
    let t := t.set! 3 (some (mkT .UINT (some 8) "uint"))
    let t := t.set! 4 (some (mkT .BOOL (some 1) "bool"))
    let t := t.set! 15 (some (mkT .UINTPTR (some 8) "uintptr"))
    let t := t.set! 28 (some (mkT .SSA none "mem"))
    let t := t.set! 32 (some (mkT .RESULTS none "mem" (.results #[28])))
    t.set! 34 (some (mkT .RESULTS none "uint,mem" (.results #[3, 28])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{slices.nextPowerOfTwo}",
           kind := .call (some 2) (some np2ABI) },
    some (symDef "slices.nextPowerOfTwo"),
    some (paramName "length" .PPARAM 0),
    some { fmt := GoStr.ofString "~r0",
           kind := .name (GoStr.ofString "~r0") .PPARAMOUT 3 0 1 {} p0 },
    some { fmt := GoStr.ofString "AuxCall{runtime.panicshift}",
           kind := .call (some 6) (some panicshiftABI) },
    some (symDef "runtime.panicshift"),
    some { fmt := GoStr.ofString "length+0", kind := .nameOff 3 0 }]

/-- The values of section 26, by ID. -/
def np2Values : Array (Option Value) :=
  let t := Array.replicate 19 (none : Option Value)
  let t := t.set! 1 (some (mkV 1 .InitMem 28 none p0 2 #[] 1))
  let t := t.set! 6 (some (mkV 6 .ArgIntReg 2 (some 7) (pos 2 189 9 0) 1 #[] 1))
  let t := t.set! 9 (some (mkV 9 .BitLen64 2 none (pos 2 189 22 1) 1 #[6] 1))
  let t := t.set! 10 (some { mkV 10 .Const64 3 none p0 1 #[] 1 with auxInt := 1 })
  let t := t.set! 14 (some (mkV 14 .StaticCall 32 (some 5) (pos 2 189 11 0) 1 #[1] 3))
  let t := t.set! 16 (some (mkV 16 .Lsh64x64 3 none (pos 2 189 11 0) 1 #[10, 9] 2))
  t.set! 18 (some (mkV 18 .MakeResult 34 none (pos 2 189 2 0) 1 #[16, 1] 2))

/-- The blocks of section 26, by ID. -/
def np2Blocks : Array (Option Block) := #[none,
  some { mkB 1 .First (pos 2 189 9 0) #[] #[⟨2, 0⟩, ⟨3, 0⟩] #[] #[1, 6, 10, 9] with
    likely := .likely },
  some (mkB 2 .Ret (pos 2 189 9 1) #[18] #[] #[⟨1, 0⟩] #[16, 18]),
  some (mkB 3 .Exit (pos 2 189 9 0) #[14] #[] #[⟨1, 1⟩] #[14])]

/-- `nextPowerOfTwo`, section 26 (of the analysis caches only `linestarts`, which deadcode reads). -/
def np2 : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 18
  bidLast := 3
  blocks := #[1, 2, 3]
  blockTab := np2Blocks
  valueTab := np2Values
  names := #[(1, #[6])]
  namedx := #[]
  splits := #[]
  canon := #[(⟨3, 2, 0, none, 0⟩, 1)]
  consts := #[(1, #[10])]
  freeValues := [13, 15, 11, 12, 17, 8, 7, 5, 4, 3, 2]
  freeBlocks := []
  cache := { lineStarts := some #[⟨2, some (189, 189), #[]⟩] }

/-- `nextPowerOfTwo(5) = 8`, `nextPowerOfTwo(0) = 1`, with fuel 2 (entry, then the `Ret`). -/
theorem np2_run :
    returnsInt (run Env.p1 np2Tabs np2 [.i64 5] {} 2) 8 = true ∧
    returnsInt (run Env.p1 np2Tabs np2 [.i64 0] {} 2) 1 = true := by
  decide +kernel

end GoFV.Proof.Witness
