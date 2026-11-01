import GoFV.Proof.Witness.Clamp

/-!
# Witness function: `decodedLen` from the corpus

`std/std/encoding/base64/decodedLen,1.ssa`, the output of section 7 (`opt`, the input of
`zero arg cse`), of the corpus `gofv-corpus/2aae1000ea1d/plain`, transcribed by hand:

```go
func decodedLen(n int, padChar rune) int {
	if padChar == NoPadding {
		// Unpadded data may end with partial block of 2-3 characters.
		return n/4*3 + n%4*6/8
	}
	// Padded base64 should always be a multiple of 4 characters in length.
	return n / 4 * 3
}
```

opt rewrote `n%4` to `n - n/4*4` with a fresh `Const64 [4]` (`v28`) outside the entry block;
zero arg cse merges it into the entry's `Const64 [4]` (`v13`), redirecting `v12` and `v23`.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem

def mkVi (id : ID) (op : Op) (t : TypeRef) (auxInt : Int64) (p : Pos) (uses : Nat)
    (args : Array ID) (blk : ID) : Value :=
  { id, op, type := t, auxInt, aux := none, pos := p, uses, args, block := blk }

def paramNameT (s : String) (cls : NameClass) (t : TypeRef) (off : Int) : AuxDef :=
  { fmt := GoStr.ofString s, kind := .name (GoStr.ofString s) cls t off 1 {} p0 }

/-- `abiInfo` of `decodedLen`: two integer register parameters, one result. -/
def dlABI : CallABI :=
  { abi := 1, nin := 2, nout := 1, spillOff := 8, spillSize := 16, inRegs := 2, outRegs := 1,
    params := #[{ out := false, index := 0, type := 2, name := some 3, regs := #[0], offset := 0 },
                { out := false, index := 1, type := 3, name := some 4, regs := #[1], offset := 8 },
                { out := true, index := 0, type := 2, name := some 5, regs := #[0],
                  offset := -1 }] }

/-- The definition tables `run` and `check` read. -/
def dlTabs : Tables where
  types :=
    let t := Array.replicate 36 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(int, rune) int" (.func 0 2 1 #[])))
    let t := t.set! 2 (some (mkT .INT (some 8) "int"))
    let t := t.set! 3 (some (mkT .INT32 (some 4) "rune"))
    let t := t.set! 4 (some (mkT .BOOL (some 1) "bool"))
    let t := t.set! 29 (some (mkT .SSA none "mem"))
    t.set! 35 (some (mkT .RESULTS none "int,mem" (.results #[2, 29])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{encoding/base64.decodedLen}",
           kind := .call (some 2) (some dlABI) },
    some { fmt := GoStr.ofString "encoding/base64.decodedLen",
           kind := .sym (GoStr.ofString "encoding/base64.decodedLen") 1 "" 0 default none none
             none #[] none },
    some (paramNameT "n" .PPARAM 2 0), some (paramNameT "padChar" .PPARAM 3 8),
    some (paramNameT "~r0" .PPARAMOUT 2 0)]

/-- The values, by ID. -/
def dlValues : Array (Option Value) := #[none,
  some (mkVi 1 .InitMem 29 0 p0 2 #[] 1),
  none, none, none, none, none,
  some (mkV 7 .Arg 2 (some 3) (pos 2 653 6 2) 4 #[] 1),
  some (mkV 8 .Arg 3 (some 4) (pos 2 653 6 2) 1 #[] 1),
  none,
  some (mkVi 10 .Const32 3 (-1) p0 1 #[] 1),
  some (mkVi 11 .Eq32 4 0 (pos 2 654 13 1) 1 #[8, 10] 1),
  some (mkVi 12 .Div64 2 0 (pos 2 656 19 0) 1 #[7, 28] 3),
  some (mkVi 13 .Const64 2 4 p0 2 #[] 1),
  some (mkVi 14 .Div64 2 0 (pos 2 656 11 1) 1 #[7, 13] 3),
  some (mkVi 15 .Const64 2 3 p0 2 #[] 1),
  some (mkVi 16 .Mul64 2 0 (pos 2 656 13 0) 1 #[14, 15] 3),
  some (mkVi 17 .Sub64 2 0 (pos 2 656 19 0) 1 #[7, 23] 3),
  some (mkVi 18 .Const64 2 6 p0 1 #[] 1),
  some (mkVi 19 .Mul64 2 0 (pos 2 656 21 0) 1 #[17, 18] 3),
  some (mkVi 20 .Const64 2 8 p0 1 #[] 1),
  some (mkVi 21 .Div64 2 0 (pos 2 656 23 0) 1 #[19, 20] 3),
  some (mkVi 22 .Add64 2 0 (pos 2 656 16 0) 1 #[16, 21] 3),
  some (mkVi 23 .Mul64 2 0 (pos 2 656 19 0) 1 #[12, 28] 3),
  some (mkVi 24 .MakeResult 35 0 (pos 2 656 3 0) 1 #[22, 1] 3),
  none,
  some (mkVi 26 .Div64 2 0 (pos 2 659 11 1) 1 #[7, 13] 2),
  some (mkVi 27 .Mul64 2 0 (pos 2 659 15 0) 1 #[26, 15] 2),
  some (mkVi 28 .Const64 2 4 (pos 2 656 19 0) 2 #[] 3),
  some (mkVi 29 .MakeResult 35 0 (pos 2 659 2 0) 1 #[27, 1] 2)]

/-- The blocks, by ID. -/
def dlBlocks : Array (Option Block) := #[none,
  some (mkB 1 .If (pos 2 654 16 0) #[11] #[⟨3, 0⟩, ⟨2, 0⟩] #[] #[1, 7, 8, 10, 11, 13, 15, 18, 20]),
  some (mkB 2 .Ret (pos 2 659 17 1) #[29] #[] #[⟨1, 1⟩] #[26, 27, 29]),
  some (mkB 3 .Ret (pos 2 656 24 1) #[24] #[] #[⟨1, 0⟩]
    #[14, 16, 17, 19, 21, 22, 24, 23, 12, 28])]

/-- `decodedLen`, the input of `zero arg cse`. -/
def decodedLen : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 29
  bidLast := 3
  blocks := #[1, 2, 3]
  blockTab := dlBlocks
  valueTab := dlValues
  names := #[(1, #[7]), (2, #[8])]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[(-1, #[10]), (3, #[15]), (4, #[13]), (6, #[18]), (8, #[20])]
  freeValues := [25, 9, 6, 5, 4, 3, 2]
  freeBlocks := []
  cache := {}

/-- The arguments of the witness run: `decodedLen(10, NoPadding)`. -/
def dlArgs : List Val := [.i64 10, .i32 (-1)]

/-- `decodedLen(10, NoPadding) = 10/4*3 + 10%4*6/8 = 7`, with fuel 2 (entry, then `b3`). -/
theorem decodedLen_run :
    returnsInt (run Env.p1 dlTabs decodedLen dlArgs {} 2) 7 = true := by
  decide +kernel

end GoFV.Proof.Witness
