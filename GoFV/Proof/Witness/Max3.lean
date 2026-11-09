import GoFV.Proof.Witness.Clamp

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function: `max3` from the corpus

`examples/loops/main/max3,1.ssa`, section 22 (after `softfloat`, the input of `branchelim`), of
the corpus `gofv-corpus/2aae1000ea1d/plain`, transcribed by hand (the cached postorder kept,
the other analysis caches and the name tables omitted: no pass in scope reads them here):

```go
func max3(a, b, c int) int {
	m := a
	if a < b {
		m = b
	}
	if m < c {
		m = c
	}
	return m
}
```

Two nested if-triangles whose joins hold one `Phi` each: branchelim merges both (`v15` and
`v18` become `CondSelect`s) and the function becomes a single `Ret` block. After `expand calls`
its parameters are `ArgIntReg`s and its result a register piece of the `MakeResult`.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem

/-- `abiInfo` of `max3`: three integer register parameters, one result. -/
def max3ABI : CallABI :=
  { abi := 1, nin := 3, nout := 1, spillOff := 8, spillSize := 24, inRegs := 3, outRegs := 1,
    params := #[abiParam false 0 3 0, abiParam false 1 4 8, abiParam false 2 5 16,
                abiParam true 0 6 (-1)] }

def nameOffDef (s : String) (n : AuxRef) : AuxDef :=
  { fmt := GoStr.ofString s, kind := .nameOff n 0 }

/-- The definition tables in force for section 22 that the pass and `run` read. -/
def max3Tabs : Tables where
  types :=
    let t := Array.replicate 34 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(int, int, int) int" (.func 0 3 1 #[])))
    let t := t.set! 2 (some (mkT .INT (some 8) "int"))
    let t := t.set! 3 (some (mkT .BOOL (some 1) "bool"))
    let t := t.set! 15 (some (mkT .UINTPTR (some 8) "uintptr"))
    let t := t.set! 20 (some (mkT .PTR (some 8) "*int" (.elem 2)))
    let t := t.set! 28 (some (mkT .SSA none "mem"))
    let t := t.set! 30 (some (mkT .SSA none "void"))
    t.set! 33 (some (mkT .RESULTS none "int,mem" (.results #[2, 28])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.max3}", kind := .call (some 2) (some max3ABI) },
    some { fmt := GoStr.ofString "main.max3",
           kind := .sym (GoStr.ofString "main.max3") 1 "" 0 default none none none #[] none },
    some (paramName "a" .PPARAM 0), some (paramName "b" .PPARAM 8),
    some (paramName "c" .PPARAM 16), some (paramName "~r0" .PPARAMOUT 0),
    some (paramName "m" .PAUTO 0),
    some (nameOffDef "a+0" 3), some (nameOffDef "b+0" 4), some (nameOffDef "c+0" 5)]

/-- The values of section 22, by ID. -/
def max3Values : Array (Option Value) := #[none,
  some (mkV 1 .InitMem 28 none p0 2 #[] 1),
  none, none, none, none, none, none,
  some (mkV 8 .ArgIntReg 2 (some 8) (pos 2 42 7 0) 2 #[] 1),
  some (mkV 9 .ArgIntReg 2 (some 9) (pos 2 42 7 0) 2 #[] 1),
  some (mkV 10 .ArgIntReg 2 (some 10) (pos 2 42 7 0) 2 #[] 1),
  none,
  some (mkV 12 .Less64 3 none (pos 2 42 7 1) 1 #[8, 9] 1),
  some (mkV 13 .OffPtr 20 none p0 0 #[19] 1),
  none,
  some (mkV 15 .Phi 2 none (pos 2 45 2 0) 2 #[8, 9] 2),
  some (mkV 16 .Less64 3 none (pos 2 45 7 1) 1 #[15, 10] 2),
  some (mkV 17 .SB 15 none p0 0 #[] 1),
  some (mkV 18 .Phi 2 none (pos 2 48 2 0) 1 #[15, 10] 4),
  some (mkV 19 .SP 15 none p0 2 #[] 1),
  some (mkV 20 .MakeResult 33 none (pos 2 48 2 1) 1 #[18, 1] 4),
  some (mkV 21 .LocalAddr 20 (some 6) (pos 2 48 2 1) 0 #[19, 1] 4)]

/-- The blocks of section 22, by ID. -/
def max3Blocks : Array (Option Block) := #[none,
  some (mkB 1 .If (pos 2 42 7 0) #[12] #[⟨3, 0⟩, ⟨2, 0⟩] #[] #[1, 8, 9, 10, 12, 17, 19, 13]),
  some (mkB 2 .If (pos 2 45 7 0) #[16] #[⟨5, 0⟩, ⟨4, 0⟩] #[⟨1, 1⟩, ⟨3, 0⟩] #[15, 16]),
  some (mkB 3 .Plain (pos 2 43 5 1) #[] #[⟨2, 1⟩] #[⟨1, 0⟩] #[]),
  some (mkB 4 .Ret (pos 2 48 2 1) #[20] #[] #[⟨2, 1⟩, ⟨5, 0⟩] #[18, 20, 21]),
  some (mkB 5 .Plain (pos 2 46 5 1) #[] #[⟨4, 1⟩] #[⟨2, 0⟩] #[])]

/-- `max3`, section 22. -/
def max3 : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 21
  bidLast := 5
  blocks := #[1, 2, 3, 4, 5]
  blockTab := max3Blocks
  valueTab := max3Values
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[(0, #[13])]
  freeValues := [14, 11, 7, 6, 5, 4, 3, 2]
  freeBlocks := []
  cache := { postorder := some #[4, 5, 2, 3, 1] }

/-- The arguments of the witness run: `max3(1, 7, 4)`. -/
def max3Args : List Val := [.i64 1, .i64 7, .i64 4]

/-- `max3(1, 7, 4) = 7`, with fuel 4 (`b1`, `b3`, `b2`, `b4`). -/
theorem max3_run : returnsInt (run Env.p1 max3Tabs max3 max3Args {} 4) 7 = true := by
  decide +kernel

end GoFV.Proof.Witness
