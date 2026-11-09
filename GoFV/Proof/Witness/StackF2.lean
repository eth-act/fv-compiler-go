import GoFV.Proof.Witness.HasWaitingReaders

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function: `f2` of `test/stack` at `expand calls`

`test/stack/main/f2,1.ssa`, the output of section 19 (`early fuse`, the input of
`expand calls`), of the corpus `gofv-corpus/2aae1000ea1d/quick-v4/plain`, with the definition
tables of section 0, transcribed by hand:

```go
func f2() (r [3000]byte) { … }   // returns its zeroed result
```

The result `~r0` (a `[3000]byte`, a byte blob) is on the stack. The function clears its slot
(`v5 = Zero [3000] (LocalAddr {~r0}) …`) and returns the slot's contents (`v10 = MakeResult v9
v5`, `v9 = Dereference v4 v5` of the same slot): a **self-move**. expand calls stores nothing,
invalidates the `Dereference` and returns only the memory (`v10 = MakeResult v5`); the output is
section 20.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt

/-- `abiInfo` of `f2`: no parameters, the result `~r0` on the stack. -/
def sf2ABI : CallABI :=
  { abi := 1, nin := 0, nout := 1, spillOff := 3008, spillSize := 0, inRegs := 0, outRegs := 0,
    params := #[{ out := true, index := 0, type := 2, name := some 3, regs := #[], offset := 8 }] }

/-- The definition tables of section 0 (no later section before `expand calls` defines any). -/
def sf2Tabs : Tables where
  posBases := #[none, none,
    some { file := GoStr.ofString "./stack.go", line := 1, col := 1, inl := -1 }]
  types := #[none,
    /- t1 -/ some (mkTy .FUNC (some 8) (some 8) (some 8) true true false false
      "func() [3000]byte" "func() [3000]uint8" (.func 0 0 1 #[hwrField "" 2 none])),
    /- t2 -/ some (mkTy .ARRAY (some 3000) (some 1) (some 0) false false true false
      "[3000]byte" "[3000]uint8" (.array 3 3000)),
    /- t3 -/ some (hwrScalar .UINT8 1 "byte"),
    /- t4 -/ some (hwrScalar .BOOL 1 "bool"),
    /- t5 -/ some (hwrScalar .INT8 1 "int8"),
    /- t6 -/ some (hwrScalar .INT16 2 "int16"),
    /- t7 -/ some (hwrScalar .INT32 4 "int32"),
    /- t8 -/ some (hwrScalar .INT64 8 "int64"),
    /- t9 -/ some (hwrScalar .UINT8 1 "uint8"),
    /- t10 -/ some (hwrScalar .UINT16 2 "uint16"),
    /- t11 -/ some (hwrScalar .UINT32 4 "uint32"),
    /- t12 -/ some (hwrScalar .UINT64 8 "uint64"),
    /- t13 -/ some (hwrScalar .INT 8 "int"),
    /- t14 -/ some (hwrScalar .FLOAT32 4 "float32"),
    /- t15 -/ some (hwrScalar .FLOAT64 8 "float64"),
    /- t16 -/ some (hwrScalar .UINT 8 "uint"),
    /- t17 -/ some (hwrScalar .UINTPTR 8 "uintptr"),
    /- t18 -/ some (mkTy .STRING (some 16) (some 8) (some 8) true false true true
      "string" "string"),
    /- t19 -/ some (hwrPtr "*uint8" "*uint8" 9),
    /- t20 -/ some (hwrPtr "*int32" "*int32" 7),
    /- t21 -/ some (hwrPtr "*uint32" "*uint32" 11),
    /- t22 -/ some (hwrPtr "*int" "*int" 13),
    /- t23 -/ some (hwrPtr "*uintptr" "*uintptr" 17),
    /- t24 -/ some (hwrPtr "*float32" "*float32" 14),
    /- t25 -/ some (hwrPtr "*float64" "*float64" 15),
    /- t26 -/ some (hwrPtr "**uint8" "**uint8" 19),
    /- t27 -/ some (mkTy .COMPLEX64 (some 8) (some 4) (some 0) false false true true
      "complex64" "complex64"),
    /- t28 -/ some (mkTy .COMPLEX128 (some 16) (some 8) (some 0) false false true true
      "complex128" "complex128"),
    /- t29 -/ some (mkTy .UNSAFEPTR (some 8) (some 8) (some 8) true true true true
      "unsafe.Pointer" "unsafe.Pointer"),
    /- t30 -/ some (hwrSSATy "mem"),
    /- t31 -/ some (hwrSSATy "flags"),
    /- t32 -/ some (hwrSSATy "void"),
    /- t33 -/ some (mkTy .SSA (some 16) (some 8) none false false false false "int128" ""),
    /- t34 -/ some (hwrResults "mem" #[30]),
    /- t35 -/ some (hwrPtr "*[3000]byte" "*[3000]uint8" 2),
    /- t36 -/ some (hwrResults "[3000]byte,mem" #[2, 30])]
  auxes := #[none,
    /- a1 -/ some { fmt := GoStr.ofString "AuxCall{main.f2}", kind := .call (some 2) (some sf2ABI) },
    /- a2 -/ some { fmt := GoStr.ofString "main.f2",
                    kind := .sym (GoStr.ofString "main.f2") 1 "-" 0 default none none none #[]
                      none },
    /- a3 -/ some { fmt := GoStr.ofString "~r0",
                    kind := .name (GoStr.ofString "~r0") .PPARAMOUT 2 0 1 {} (pos 2 55 11 0) },
    /- a4 -/ some { fmt := GoStr.ofString "[3000]byte", kind := .type 2 }]

/-- The values of section 19, by ID. -/
def sf2Values : Array (Option Value) := #[none,
  some (hwrV 1 .InitMem 30 0 none p0 2 #[]),
  some (hwrV 2 .SP 17 0 none p0 1 #[]),
  none,
  some (hwrV 4 .LocalAddr 35 0 (some 3) p0 2 #[2, 1]),
  some (hwrV 5 .Zero 30 3000 (some 4) (pos 2 55 6 1) 2 #[4, 1]),
  none, none, none,
  some (hwrV 9 .Dereference 2 0 none (pos 2 57 2 1) 1 #[4, 5]),
  some (hwrV 10 .MakeResult 36 0 none (pos 2 57 2 0) 1 #[9, 5])]

/-- The blocks of section 19, by ID. -/
def sf2Blocks : Array (Option Block) := #[none,
  some (mkB 1 .Ret (pos 2 57 2 1) #[10] #[] #[] #[1, 2, 4, 5, 9, 10])]

/-- `f2`, section 19 (the input of `expand calls`). -/
def sf2 : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 10
  bidLast := 1
  blocks := #[1]
  blockTab := sf2Blocks
  valueTab := sf2Values
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := [8, 7, 6, 3]
  freeBlocks := []
  cache :=
    { postorder := some #[1]
      idom := some #[none, none]
      sdom := some #[default, { parent := none, child := none, sibling := none, entry := 2,
                                exit := 5 }]
      auxmap := some #[(none, 1), (some 3, 2)]
      lineStarts := some #[{ index := 2, bounds := some (55, 57), pending := #[] }] }

/-- `Config.Types` (the `typs` line of section 0). -/
def sf2Typs : Array (String × TypeRef) :=
  #[("Bool", 4), ("Int8", 5), ("Int16", 6), ("Int32", 7), ("Int64", 8), ("UInt8", 9),
    ("UInt16", 10), ("UInt32", 11), ("UInt64", 12), ("Int", 13), ("Float32", 14), ("Float64", 15),
    ("UInt", 16), ("Uintptr", 17), ("String", 18), ("BytePtr", 19), ("Int32Ptr", 20),
    ("UInt32Ptr", 21), ("IntPtr", 22), ("UintptrPtr", 23), ("Float32Ptr", 24),
    ("Float64Ptr", 25), ("BytePtrPtr", 26), ("Complex64", 27), ("Complex128", 28),
    ("UnsafePtr", 29), ("Mem", 30), ("Flags", 31), ("Void", 32), ("Int128", 33),
    ("ResultMem", 34)]

/-- `check`'s environment for the input. -/
def sf2CheckEnv : CheckEnv := { tabs := sf2Tabs, typs := sf2Typs }

/-- What `expand calls` reads of the export's environment (the configuration entries it and
`check` read). -/
def sf2PassEnv : PassEnv where
  passName := "expand calls"
  pkg := GoStr.ofString "main"
  funcName := GoStr.ofString "f2"
  abi := 1
  nosplit := false
  pgohot := false
  config := #[("arch", #[.word "arm64"]), ("ptrsize", #[.word "8"]), ("regsize", #[.word "8"]),
    ("bigendian", #[.word "0"]), ("fixedframesize", #[.word "8"]),
    ("abi0", #[.word "0:0:8"]), ("abi1", #[.word "16:16:8"])]
  typs := sf2Typs
  typeOrder := default
  tables := sf2Tabs

end GoFV.Proof.Witness
