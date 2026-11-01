import GoFV.Proof.Witness.InitF10
import GoFV.Opt.ExpandCallsCheck

/-!
# Witness function: `sumOf[int]` of `examples/generics` at `expand calls`

`examples/generics/main/sumOf%5Bint%5D,1.ssa`, the output of section 19 (`early fuse`, the input
of `expand calls`), of the corpus `gofv-corpus/2aae1000ea1d/quick-v1/plain`, with the definition
tables of section 0, transcribed by hand:

```go
func sumOf[T int | float64](xs []T) (s T) { … }   // the instantiation for int
```

`sumOf[int]` is the dictionary wrapper of the shaped body: it calls
`sumOf[go.shape.int](&.dict.sumOf[int], xs)` (`v9`, a `StaticLECall`) and returns its result.
expand calls splits the slice parameter `xs` (`v6`, an `Arg`) into three `ArgIntReg`s and a
`SliceMake`, passes the slice to the call as `SlicePtr`/`SliceLen`/`SliceCap` (the call becomes
a `StaticCall` of four register arguments) and creates the `xs+0`/`xs+8`/`xs+16` name offsets
(`a8`–`a10`), the `SP` `v7` and the result address `v17`; the output is section 20.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt

/-- `abiInfo` of `sumOf[int]`: the slice `xs` in three integer registers, the result `s` in
one. -/
def sumOfABI : CallABI :=
  { abi := 1, nin := 1, nout := 1, spillOff := 8, spillSize := 24, inRegs := 3, outRegs := 1,
    params := #[{ out := false, index := 0, type := 2, name := some 3, regs := #[0, 1, 2],
                  offset := 0 },
                { out := true, index := 0, type := 3, name := some 4, regs := #[0],
                  offset := -1 }] }

/-- `abiInfo` of the callee `sumOf[go.shape.int]`: the dictionary pointer and the slice in four
integer registers, the result in one. -/
def sumOfCalleeABI : CallABI :=
  { abi := 1, nin := 2, nout := 1, spillOff := 8, spillSize := 32, inRegs := 4, outRegs := 1,
    params := #[{ out := false, index := 0, type := 35, name := none, regs := #[0], offset := 0 },
                { out := false, index := 1, type := 39, name := none, regs := #[1, 2, 3],
                  offset := 8 },
                { out := true, index := 0, type := 37, name := none, regs := #[0],
                  offset := -1 }] }

/-- A scalar type of section 0 (`comparable,named`, no pointers). -/
def sumOfScalar (kind : TypeKind) (size : Int) (s : String) : TypeDef :=
  mkTy kind (some size) (some size) (some 0) false false true true s s

/-- A pointer type of section 0 (`hasptr,direct,comparable`). -/
def sumOfPtr (s : String) (e : TypeRef) : TypeDef :=
  mkTy .PTR (some 8) (some 8) (some 8) true true true false s s (.elem e)

/-- A pseudo-type of the SSA backend (`SSA`, no size). -/
def sumOfSSATy (s : String) : TypeDef :=
  mkTy .SSA none none none false false false false s ""

/-- A `RESULTS` type. -/
def sumOfResults (s : String) (ts : Array TypeRef) : TypeDef :=
  mkTy .RESULTS none none none false false false false s "" (.results ts)

/-- `reloc` lines. -/
def sumOfReloc (off siz : Int) (ty : String) (target : String) : Reloc :=
  { off, siz, type := ty, add := 0, target := GoStr.ofString target, targetAbi := 0 }

/-- The definition tables of section 0 (no later section before `expand calls` defines any). -/
def sumOfTabs : Tables where
  posBases := #[none, none,
    some { file := GoStr.ofString "./main.go", line := 1, col := 1, inl := -1 }]
  types := #[none,
    /- t1 -/ some (mkTy .FUNC (some 8) (some 8) (some 8) true true false false
      "func([]int) int" "func([]int) int"
      (.func 0 1 1 #[{ name := GoStr.ofString "xs", type := 2, offset := none, embedded := false },
                     { name := GoStr.ofString "s", type := 3, offset := none, embedded := false }])),
    /- t2 -/ some (mkTy .SLICE (some 24) (some 8) (some 8) true false false false
      "[]int" "[]int" (.elem 3)),
    /- t3 -/ some (sumOfScalar .INT 8 "int"),
    /- t4 -/ some (sumOfScalar .BOOL 1 "bool"),
    /- t5 -/ some (sumOfScalar .INT8 1 "int8"),
    /- t6 -/ some (sumOfScalar .INT16 2 "int16"),
    /- t7 -/ some (sumOfScalar .INT32 4 "int32"),
    /- t8 -/ some (sumOfScalar .INT64 8 "int64"),
    /- t9 -/ some (sumOfScalar .UINT8 1 "uint8"),
    /- t10 -/ some (sumOfScalar .UINT16 2 "uint16"),
    /- t11 -/ some (sumOfScalar .UINT32 4 "uint32"),
    /- t12 -/ some (sumOfScalar .UINT64 8 "uint64"),
    /- t13 -/ some (sumOfScalar .FLOAT32 4 "float32"),
    /- t14 -/ some (sumOfScalar .FLOAT64 8 "float64"),
    /- t15 -/ some (sumOfScalar .UINT 8 "uint"),
    /- t16 -/ some (sumOfScalar .UINTPTR 8 "uintptr"),
    /- t17 -/ some (mkTy .STRING (some 16) (some 8) (some 8) true false true true
      "string" "string"),
    /- t18 -/ some (sumOfPtr "*uint8" 9),
    /- t19 -/ some (sumOfPtr "*int32" 7),
    /- t20 -/ some (sumOfPtr "*uint32" 11),
    /- t21 -/ some (sumOfPtr "*int" 3),
    /- t22 -/ some (sumOfPtr "*uintptr" 16),
    /- t23 -/ some (sumOfPtr "*float32" 13),
    /- t24 -/ some (sumOfPtr "*float64" 14),
    /- t25 -/ some (sumOfPtr "**uint8" 18),
    /- t26 -/ some (mkTy .COMPLEX64 (some 8) (some 4) (some 0) false false true true
      "complex64" "complex64"),
    /- t27 -/ some (mkTy .COMPLEX128 (some 16) (some 8) (some 0) false false true true
      "complex128" "complex128"),
    /- t28 -/ some (mkTy .UNSAFEPTR (some 8) (some 8) (some 8) true true true true
      "unsafe.Pointer" "unsafe.Pointer"),
    /- t29 -/ some (sumOfSSATy "mem"),
    /- t30 -/ some (sumOfSSATy "flags"),
    /- t31 -/ some (sumOfSSATy "void"),
    /- t32 -/ some (mkTy .SSA (some 16) (some 8) none false false false false "int128" ""),
    /- t33 -/ some (sumOfResults "mem" #[29]),
    /- t34 -/ some (sumOfPtr "*[]int" 2),
    /- t35 -/ some (sumOfPtr "*[3]uintptr" 36),
    /- t36 -/ some (mkTy .ARRAY (some 24) (some 8) (some 0) false false true false
      "[3]uintptr" "[3]uintptr" (.array 16 3)),
    /- t37 -/ some { sumOfScalar .INT 8 "go.shape.int" with
      flags := { comparable := true, named := true, shape := true } },
    /- t38 -/ some (sumOfResults "go.shape.int,mem" #[37, 29]),
    /- t39 -/ some (mkTy .SLICE (some 24) (some 8) (some 8) true false false false
      "[]go.shape.int" "[]go.shape.int" (.elem 37)),
    /- t40 -/ some (sumOfResults "int,mem" #[3, 29])]
  auxes := #[none,
    /- a1 -/ some { fmt := GoStr.ofString "AuxCall{main.sumOf[int]}",
                    kind := .call (some 2) (some sumOfABI) },
    /- a2 -/ some { fmt := GoStr.ofString "main.sumOf[int]",
                    kind := .sym (GoStr.ofString "main.sumOf[int]") 1 "-" 0 default none none none
                      #[] none },
    /- a3 -/ some { fmt := GoStr.ofString "xs",
                    kind := .name (GoStr.ofString "xs") .PPARAM 2 0 1 { used := true }
                      (pos 2 13 19 0) },
    /- a4 -/ some { fmt := GoStr.ofString "s",
                    kind := .name (GoStr.ofString "s") .PPARAMOUT 3 0 1 {} (pos 2 13 28 0) },
    /- a5 -/ some { fmt := GoStr.ofString "main..dict.sumOf[int]",
                    kind := .sym (GoStr.ofString "main..dict.sumOf[int]") 0 "SRODATA" 24
                      { dupok := true } none none (some ⟨Array.replicate 16 0⟩)
                      #[sumOfReloc 0 8 "R_ADDR" "type:[]int", sumOfReloc 0 0 "R_USEIFACE" "type:[]int",
                        sumOfReloc 8 8 "R_ADDR" "type:int", sumOfReloc 0 0 "R_USEIFACE" "type:int",
                        sumOfReloc 0 0 "R_USEIFACE" "type:int",
                        sumOfReloc 0 0 "R_USEIFACE" "type:int"]
                      none },
    /- a6 -/ some { fmt := GoStr.ofString "AuxCall{main.sumOf[go.shape.int]}",
                    kind := .call (some 7) (some sumOfCalleeABI) },
    /- a7 -/ some { fmt := GoStr.ofString "main.sumOf[go.shape.int]",
                    kind := .sym (GoStr.ofString "main.sumOf[go.shape.int]") 1 "-" 0 default none
                      none none #[] none }]
  slots := #[none, some { name := 3, type := 2, off := 0, splitOf := none, splitOffset := 0 }]

/-- A value of `b1`. -/
def sumOfV (id : ID) (op : Op) (t : TypeRef) (auxInt : Int64) (aux : Option AuxRef) (p : Pos)
    (uses : Nat) (args : Array ID) : Value :=
  { id, op, type := t, auxInt, aux, pos := p, uses, args, block := 1 }

/-- The values of section 19, by ID. -/
def sumOfValues : Array (Option Value) := #[none,
  some (sumOfV 1 .InitMem 29 0 none p0 1 #[]),
  none,
  some (sumOfV 3 .SB 16 0 none p0 1 #[]),
  none, none,
  some (sumOfV 6 .Arg 2 0 (some 3) (pos 2 13 6 2) 1 #[]),
  none,
  some (sumOfV 8 .Addr 35 0 (some 5) p0 1 #[3]),
  some (sumOfV 9 .StaticLECall 38 32 (some 6) (pos 2 13 6 1) 2 #[8, 6, 1]),
  some (sumOfV 10 .SelectN 29 1 none (pos 2 13 6 0) 1 #[9]),
  some (sumOfV 11 .SelectN 37 0 none (pos 2 13 6 0) 1 #[9]),
  some (sumOfV 12 .MakeResult 40 0 none (pos 2 13 6 0) 1 #[11, 10])]

/-- The blocks of section 19, by ID. -/
def sumOfBlocks : Array (Option Block) := #[none,
  some (mkB 1 .Ret (pos 2 13 6 1) #[12] #[] #[] #[1, 3, 6, 8, 9, 10, 11, 12])]

/-- The `LocalSlot` of `xs` (`s1`). -/
def sumOfXsSlot : SlotKey := { name := 3, type := 2, off := 0, splitOf := none, splitOffset := 0 }

/-- `sumOf[int]`, section 19 (the input of `expand calls`). -/
def sumOf : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 12
  bidLast := 1
  blocks := #[1]
  blockTab := sumOfBlocks
  valueTab := sumOfValues
  names := #[(1, #[6])]
  namedx := #[]
  splits := #[]
  canon := #[(sumOfXsSlot, 1)]
  consts := #[]
  freeValues := [7, 5, 4, 2]
  freeBlocks := []
  cache :=
    { postorder := some #[1]
      idom := some #[none, none]
      sdom := some #[default, { parent := none, child := none, sibling := none, entry := 2,
                                exit := 5 }]
      auxmap := some #[(none, 1), (some 3, 2), (some 5, 3)]
      lineStarts := some #[{ index := 2, bounds := some (13, 13), pending := #[] }] }

/-- `Config.Types` (the `typs` line of section 0). -/
def sumOfTyps : Array (String × TypeRef) :=
  #[("Bool", 4), ("Int8", 5), ("Int16", 6), ("Int32", 7), ("Int64", 8), ("UInt8", 9),
    ("UInt16", 10), ("UInt32", 11), ("UInt64", 12), ("Int", 3), ("Float32", 13), ("Float64", 14),
    ("UInt", 15), ("Uintptr", 16), ("String", 17), ("BytePtr", 18), ("Int32Ptr", 19),
    ("UInt32Ptr", 20), ("IntPtr", 21), ("UintptrPtr", 22), ("Float32Ptr", 23),
    ("Float64Ptr", 24), ("BytePtrPtr", 25), ("Complex64", 26), ("Complex128", 27),
    ("UnsafePtr", 28), ("Mem", 29), ("Flags", 30), ("Void", 31), ("Int128", 32),
    ("ResultMem", 33)]

/-- `check`'s environment for the input. -/
def sumOfCheckEnv : CheckEnv := { tabs := sumOfTabs, typs := sumOfTyps }

/-- What `expand calls` reads of the export's environment (the configuration entries it and
`check` read; no type order: the pass creates no types and compares none). -/
def sumOfPassEnv : PassEnv where
  passName := "expand calls"
  pkg := GoStr.ofString "main"
  funcName := GoStr.ofString "sumOf[int]"
  abi := 1
  nosplit := false
  pgohot := false
  config := #[("arch", #[.word "arm64"]), ("ptrsize", #[.word "8"]), ("regsize", #[.word "8"]),
    ("bigendian", #[.word "0"]), ("fixedframesize", #[.word "8"]),
    ("abi0", #[.word "0:0:8"]), ("abi1", #[.word "16:16:8"])]
  typs := sumOfTyps
  typeOrder := default
  tables := sumOfTabs

end GoFV.Proof.Witness
