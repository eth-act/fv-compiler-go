import GoFV.Proof.Witness.InitF10

/-!
# Witness function: `strconv.FormatBool` at `decompose builtin`

`std/strconv/FormatBool,1.ssa`, the output of section 20 (`expand calls`, the input of
`decompose builtin`), of the corpus `gofv-corpus/2aae1000ea1d/quick-v3/plain`, with the
definition tables of sections 0–20, transcribed by hand (position bases and the analysis caches
left empty; `check` and the phi stage do not read them):

```go
func FormatBool(b bool) string {
	if b {
		return "true"
	}
	return "false"
}
```

The result is the string `Phi` `v11 = Phi v9 v10` of `b4` (`v9`, `v10`: `StringMake`s of the
literals' data and lengths in `b1`); the phi stage of decompose builtin splits it into
`StringMake` of a pointer `Phi` and a length `Phi` over `StringPtr`/`StringLen` extractors in
`b1`.

`formatBoolOut`: the phi stage's output (in the same tables), printed by the stage and checked
against it in `GoFVTest/Proof/DecPhisStage.lean` (the stage's state uses `Std.HashMap`, which the
kernel does not evaluate).

`pairTabs`/`pair`/`pairOut`: the same function with a two-field struct `struct{ p *uint8; n int }` (`t37`)
in place of `string` (`StructMake`, `StructSelect`), the input of decompose user's phi stage.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt

def fbField (name : String) (t : TypeRef) (off : Option Int) : Field :=
  { name := GoStr.ofString name, type := t, offset := off, embedded := false }

/-- `abiInfo` of `FormatBool` with result type `rt`: `b` in one register, the result in two. -/
def fbABI (rt : TypeRef) : CallABI :=
  { abi := 1, nin := 1, nout := 1, spillOff := 8, spillSize := 8, inRegs := 1, outRegs := 2,
    params := #[{ out := false, index := 0, type := 2, name := some 3, regs := #[0], offset := 0 },
                { out := true, index := 0, type := rt, name := some 4, regs := #[0, 1],
                  offset := -1 }] }

/-- A read-only string data symbol. -/
def fbStrSym (s : String) : AuxDef :=
  let n := GoStr.ofString s!"go:string.\"{s}\""
  { fmt := n, kind := .sym n 0 "SRODATA" s.utf8ByteSize
      { dupok := true, «local» := true, contentaddressable := true } none none
      (some s.toUTF8) #[] none }

/-- The definition tables of sections 0–20, the result type `rt` (`t3`: `string`). -/
def fbTabs (rt : TypeRef) (extra : Array (Option TypeDef) → Array (Option TypeDef) := id) :
    Tables where
  posBases := #[]
  types :=
    let t := Array.replicate 38 (none : Option TypeDef)
    let t := t.set! 1 (some (mkTy .FUNC (some 8) (some 8) (some 8) true true false false
      "func(bool) string" "func(bool) string"
      (.func 0 1 1 #[fbField "b" 2 none, fbField "" 3 none])))
    let t := t.set! 2 (some (mkTy .BOOL (some 1) (some 1) (some 0) false false true true
      "bool" "bool"))
    let t := t.set! 3 (some (mkTy .STRING (some 16) (some 8) (some 8) true false true true
      "string" "string"))
    let t := t.set! 6 (some (mkTy .INT32 (some 4) (some 4) (some 0) false false true true
      "int32" "int32"))
    let t := t.set! 8 (some (mkTy .UINT8 (some 1) (some 1) (some 0) false false true true
      "uint8" "uint8"))
    let t := t.set! 10 (some (mkTy .UINT32 (some 4) (some 4) (some 0) false false true true
      "uint32" "uint32"))
    let t := t.set! 12 (some (mkTy .INT (some 8) (some 8) (some 0) false false true true
      "int" "int"))
    let t := t.set! 13 (some (mkTy .FLOAT32 (some 4) (some 4) (some 0) false false true true
      "float32" "float32"))
    let t := t.set! 14 (some (mkTy .FLOAT64 (some 8) (some 8) (some 0) false false true true
      "float64" "float64"))
    let t := t.set! 16 (some (mkTy .UINTPTR (some 8) (some 8) (some 0) false false true true
      "uintptr" "uintptr"))
    let t := t.set! 17 (some (mkTy .PTR (some 8) (some 8) (some 8) true true true false
      "*uint8" "*uint8" (.elem 8)))
    let t := t.set! 28 (some (mkTy .SSA none none none false false false false "mem" ""))
    let t := t.set! 30 (some (mkTy .SSA none none none false false false false "void" ""))
    let t := t.set! 32 (some (mkTy .RESULTS none none none false false false false "mem" ""
      (.results #[28])))
    let t := t.set! 33 (some (mkTy .PTR (some 8) (some 8) (some 8) true true true false
      "*bool" "*bool" (.elem 2)))
    let t := t.set! 34 (some (mkTy .PTR (some 8) (some 8) (some 8) true true true false
      "*string" "*string" (.elem 3)))
    let t := t.set! 35 (some (mkTy .RESULTS none none none false false false false "string,mem"
      "" (.results #[3, 28])))
    let t := t.set! 36 (some (mkTy .RESULTS none none none false false false false
      "*uint8,int,mem" "" (.results #[17, 12, 28])))
    extra t
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{strconv.FormatBool}", kind := .call (some 2) (some (fbABI rt)) },
    some { fmt := GoStr.ofString "strconv.FormatBool",
           kind := .sym (GoStr.ofString "strconv.FormatBool") 1 "-" 0 default none none none #[]
             none },
    some { fmt := GoStr.ofString "b",
           kind := .name (GoStr.ofString "b") .PPARAM 2 0 1 { used := true } (pos 3 28 17 0) },
    some { fmt := GoStr.ofString "~r0",
           kind := .name (GoStr.ofString "~r0") .PPARAMOUT rt 0 1 {} (pos 3 28 25 0) },
    some { fmt := GoStr.ofString "", kind := .str (GoStr.ofString "") (GoStr.ofString "go:string.\"\"") },
    some { fmt := GoStr.ofString "true",
           kind := .str (GoStr.ofString "true") (GoStr.ofString "go:string.\"true\"") },
    some { fmt := GoStr.ofString "false",
           kind := .str (GoStr.ofString "false") (GoStr.ofString "go:string.\"false\"") },
    some { fmt := GoStr.ofString "strconv.b",
           kind := .name (GoStr.ofString "b") .PAUTO 2 0 1 { used := true } (pos 46 21 17 0) },
    some { fmt := GoStr.ofString "~r0",
           kind := .name (GoStr.ofString "~r0") .PAUTO rt 0 1 {} (pos 46 21 25 0) },
    some (fbStrSym "true"),
    some (fbStrSym "false"),
    some { fmt := GoStr.ofString "b+0", kind := .nameOff 3 0 }]
  slots := #[none, some { name := 3, type := 2, off := 0, splitOf := none, splitOffset := 0 },
    some { name := 8, type := 2, off := 0, splitOf := none, splitOffset := 0 },
    some { name := 9, type := rt, off := 0, splitOf := none, splitOffset := 0 }]

/-- A value of `FormatBool`. -/
def fbV (id : ID) (op : Op) (t : TypeRef) (auxInt : Int64) (aux : Option AuxRef) (p : Pos)
    (uses : Nat) (args : Array ID) (blk : ID) : Value :=
  { id, op, type := t, auxInt, aux, pos := p, uses, args, block := blk }

/-- The values, by ID; `rt` the result type, `mk`/`sel0`/`sel1`/`ai0`/`ai1` its `Make` and
extractors. -/
def fbValues (rt : TypeRef) (mk sel0 sel1 : Op) (ai0 ai1 : Int64) : Array (Option Value) := #[none,
  some (fbV 1 .InitMem 28 0 none p0 3 #[] 1),
  some (fbV 2 .Const64 12 5 none p0 1 #[] 1),
  some (fbV 3 .SP 16 0 none p0 2 #[] 1),
  some (fbV 4 .Addr 17 0 (some 11) p0 1 #[7] 1),
  some (fbV 5 .Const64 12 4 none p0 1 #[] 1),
  some (fbV 6 .ArgIntReg 2 0 (some 12) (pos 46 22 2 1) 1 #[] 1),
  some (fbV 7 .SB 16 0 none p0 2 #[] 1),
  some (fbV 8 .InlMark 30 18 none (pos 3 29 27 1) 0 #[1] 1),
  some (fbV 9 mk rt 0 none p0 1 #[12, 5] 1),
  some (fbV 10 mk rt 0 none p0 1 #[4, 2] 1),
  some (fbV 11 .Phi rt 0 none (pos 3 29 2 0) 2 #[9, 10] 4),
  some (fbV 12 .Addr 17 0 (some 10) p0 1 #[7] 1),
  some (fbV 13 .MakeResult 36 0 none (pos 3 29 2 0) 1 #[16, 17, 1] 4),
  some (fbV 14 .OffPtr 33 0 none p0 0 #[3] 1),
  some (fbV 15 .LocalAddr 34 0 (some 4) (pos 3 29 2 0) 0 #[3, 1] 4),
  some (fbV 16 sel0 17 ai0 none (pos 3 29 2 0) 1 #[11] 4),
  some (fbV 17 sel1 12 ai1 none (pos 3 29 2 2) 1 #[11] 4)]

/-- The blocks, by ID. -/
def fbBlocks : Array (Option Block) := #[none,
  some (mkB 1 .If (pos 46 22 2 1) #[6] #[⟨3, 0⟩, ⟨2, 0⟩] #[]
    #[1, 2, 5, 6, 7, 4, 8, 12, 9, 10, 3, 14]),
  some (mkB 2 .Plain (pos 3 29 27 1) #[] #[⟨4, 1⟩] #[⟨1, 1⟩] #[]),
  some (mkB 3 .Plain (pos 3 29 27 1) #[] #[⟨4, 0⟩] #[⟨1, 0⟩] #[]),
  some (mkB 4 .Ret (pos 3 29 2 1) #[13] #[] #[⟨3, 0⟩, ⟨2, 0⟩] #[11, 13, 15, 16, 17])]

/-- The function with result type `rt` (its `Make` and extractors). -/
def fbFunc (rt : TypeRef) (mk sel0 sel1 : Op) (ai0 ai1 : Int64) : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 17
  bidLast := 4
  blocks := #[1, 2, 3, 4]
  blockTab := fbBlocks
  valueTab := fbValues rt mk sel0 sel1 ai0 ai1
  names := #[(1, #[6]), (2, #[6]), (3, #[9, 10, 11])]
  namedx := #[]
  splits := #[]
  canon := #[({ name := 3, type := 2, off := 0, splitOf := none, splitOffset := 0 }, 1),
    ({ name := 8, type := 2, off := 0, splitOf := none, splitOffset := 0 }, 2),
    ({ name := 9, type := rt, off := 0, splitOf := none, splitOffset := 0 }, 3)]
  consts := #[(0, #[14])]
  freeValues := []
  freeBlocks := []
  cache := {}

/-- `FormatBool`, the input of decompose builtin. -/
def formatBool : Func := fbFunc 3 .StringMake .StringPtr .StringLen 0 0

/-- The `typs` of the export. -/
def fbTyps : Array (String × TypeRef) :=
  #[("Bool", 2), ("Int32", 6), ("UInt8", 8), ("UInt32", 10), ("Int", 12), ("Float32", 13),
    ("Float64", 14), ("Uintptr", 16), ("String", 3), ("BytePtr", 17), ("Mem", 28), ("Void", 30),
    ("ResultMem", 32)]

/-- What decompose reads of the export's environment (`pass` names the section's pass). -/
def fbPassEnv (pass : String) (tabs : Tables) : PassEnv where
  passName := pass
  pkg := GoStr.ofString "strconv"
  funcName := GoStr.ofString "FormatBool"
  abi := 1
  nosplit := false
  pgohot := false
  config := #[("ptrsize", #[.word "8"]), ("regsize", #[.word "8"]), ("bigendian", #[.word "0"]),
    ("exp.simd", #[.word "0"])]
  typs := fbTyps
  typeOrder := default
  tables := tabs

/-- The tables of `FormatBool`. -/
def formatBoolTabs : Tables := fbTabs 3

/-- The struct `struct{ p *uint8; n int }` (`t37`). -/
def pairTy : TypeDef :=
  mkTy .STRUCT (some 16) (some 8) (some 8) true false true false "struct { p *uint8; n int }"
    "struct { p *uint8; n int }" (.struct #[fbField "p" 17 (some 0), fbField "n" 12 (some 8)])

/-- The tables of the struct variant. -/
def pairTabs : Tables := fbTabs 37 (·.set! 37 (some pairTy))

/-- The struct variant: `StructMake`, `StructSelect [0]`/`[1]`. -/
def pair : Func := fbFunc 37 .StructMake .StructSelect .StructSelect 0 1

/-! ## The phi stage's output -/

/-- The function after the phi stage: `v11` becomes `mk v18 v19` of the component `Phi`s
`v18`/`v19` over the extractors `v20`–`v23` (components 0 and 1 of `v9` and `v10`, in `b1`). -/
def fbOut (rt : TypeRef) (mk sel0 sel1 : Op) (ai0 ai1 : Int64) : Func :=
  let f := fbFunc rt mk sel0 sel1 ai0 ai1
  { f with
    vidLast := 23
    blockTab := #[none,
      some (mkB 1 .If (pos 46 22 2 1) #[6] #[⟨3, 0⟩, ⟨2, 0⟩] #[]
        #[1, 2, 5, 6, 7, 4, 8, 12, 9, 10, 3, 14, 20, 21, 22, 23]),
      some (mkB 2 .Plain (pos 3 29 27 1) #[] #[⟨4, 1⟩] #[⟨1, 1⟩] #[]),
      some (mkB 3 .Plain (pos 3 29 27 1) #[] #[⟨4, 0⟩] #[⟨1, 0⟩] #[]),
      some (mkB 4 .Ret (pos 3 29 2 1) #[13] #[] #[⟨3, 0⟩, ⟨2, 0⟩] #[11, 13, 15, 16, 17, 18, 19])]
    valueTab :=
      (((fbValues rt mk sel0 sel1 ai0 ai1).set! 9 (some (fbV 9 mk rt 0 none p0 2 #[12, 5] 1))).set!
        10 (some (fbV 10 mk rt 0 none p0 2 #[4, 2] 1))).set!
        11 (some (fbV 11 mk rt 0 none (pos 3 29 2 0) 2 #[18, 19] 4)) ++ #[
      some (fbV 18 .Phi 17 0 none (pos 3 29 2 2) 1 #[20, 22] 4),
      some (fbV 19 .Phi 12 0 none (pos 3 29 2 2) 1 #[21, 23] 4),
      some (fbV 20 sel0 17 ai0 none (pos 3 29 2 0) 1 #[9] 1),
      some (fbV 21 sel1 12 ai1 none (pos 3 29 2 0) 1 #[9] 1),
      some (fbV 22 sel0 17 ai0 none (pos 3 29 2 0) 1 #[10] 1),
      some (fbV 23 sel1 12 ai1 none (pos 3 29 2 0) 1 #[10] 1)] }

/-- `FormatBool` after decompose builtin's phi stage. -/
def formatBoolOut : Func := fbOut 3 .StringMake .StringPtr .StringLen 0 0

/-- `pair` after decompose user's phi stage. -/
def pairOut : Func := fbOut 37 .StructMake .StructSelect .StructSelect 0 1

end GoFV.Proof.Witness
