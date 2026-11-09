import GoFV.Proof.Witness.StackF2

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function: `uuid.New` at `expand calls`

`stdall/std/uuid/New,1.ssa`, the output of section 19 (`early fuse`, the input of
`expand calls`), of the corpus `gofv-corpus/2aae1000ea1d/full-v5/plain`, with the definition
tables of section 0, transcribed by hand:

```go
func New() UUID { return NewV4() }   // type UUID [16]byte
```

The callee's result (a `[16]byte`, a byte blob) is on the stack. The source reads it by its
address: `v8 = SelectNAddr v6` of the call `v6 = StaticLECall {uuid.NewV4} v5`, copied into a
temporary by `v10 = Move [16] v9 v8 v7`. expand calls turns the call into `StaticCall` and the
address into `v8 = Copy v12` of a new `v12 = OffPtr [8] SP`, the result's slot in the
outgoing-arguments area: `v8` no longer reads the call (**frame-determined**). The function's own
result is a self-move (`v16 = MakeResult v15 v13`, `v15 = Dereference v4 v13` of its slot); the
output is section 20.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt

/-- `abiInfo` of `New` (and of its callee `NewV4`, but for the result's name): no parameters,
the result on the stack at offset 8. -/
def uuidABI (name : Option AuxRef) : CallABI :=
  { abi := 1, nin := 0, nout := 1, spillOff := 24, spillSize := 0, inRegs := 0, outRegs := 0,
    params := #[{ out := true, index := 0, type := 2, name := name, regs := #[], offset := 8 }] }

/-- The definition tables of section 0 (no later section before `expand calls` defines any). -/
def uuidTabs : Tables where
  posBases := #[none, none,
    some { file := GoStr.ofString "uuid/uuid.go", line := 1, col := 1, inl := -1 }]
  types := #[none,
    /- t1 -/ some (mkTy .FUNC (some 8) (some 8) (some 8) true true false false
      "func() UUID" "func() uuid.UUID" (.func 0 0 1 #[hwrField "" 2 none])),
    /- t2 -/ some (mkTy .ARRAY (some 16) (some 1) (some 0) false false true true
      "UUID" "uuid.UUID" (.array 3 16)),
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
    /- t35 -/ some (hwrPtr "*UUID" "*uuid.UUID" 2),
    /- t36 -/ some (hwrResults "UUID,mem" #[2, 30])]
  auxes := #[none,
    /- a1 -/ some { fmt := GoStr.ofString "AuxCall{uuid.New}",
                    kind := .call (some 2) (some (uuidABI (some 3))) },
    /- a2 -/ some { fmt := GoStr.ofString "uuid.New",
                    kind := .sym (GoStr.ofString "uuid.New") 1 "-" 0 default none none none #[]
                      none },
    /- a3 -/ some { fmt := GoStr.ofString "~r0",
                    kind := .name (GoStr.ofString "~r0") .PPARAMOUT 2 0 1 {} (pos 2 66 12 0) },
    /- a4 -/ some { fmt := GoStr.ofString "UUID", kind := .type 2 },
    /- a5 -/ some { fmt := GoStr.ofString "AuxCall{uuid.NewV4}",
                    kind := .call (some 6) (some (uuidABI none)) },
    /- a6 -/ some { fmt := GoStr.ofString "uuid.NewV4",
                    kind := .sym (GoStr.ofString "uuid.NewV4") 1 "-" 0 default none none none #[]
                      none },
    /- a7 -/ some { fmt := GoStr.ofString ".autotmp_1",
                    kind := .name (GoStr.ofString ".autotmp_1") .PAUTO 2 0 3
                      { used := true, autotmp := true } (pos 2 67 14 0) }]

/-- The values of section 19, by ID. -/
def uuidValues : Array (Option Value) := #[none,
  some (hwrV 1 .InitMem 30 0 none p0 2 #[]),
  some (hwrV 2 .SP 17 0 none p0 2 #[]),
  none,
  some (hwrV 4 .LocalAddr 35 0 (some 3) p0 3 #[2, 1]),
  some (hwrV 5 .Zero 30 16 (some 4) (pos 2 66 6 1) 1 #[4, 1]),
  some (hwrV 6 .StaticLECall 36 16 (some 5) (pos 2 67 14 1) 2 #[5]),
  some (hwrV 7 .SelectN 30 1 none (pos 2 67 14 0) 2 #[6]),
  some (hwrV 8 .SelectNAddr 35 0 none (pos 2 67 14 0) 1 #[6]),
  some (hwrV 9 .LocalAddr 35 0 (some 7) (pos 2 67 14 2) 2 #[2, 7]),
  some (hwrV 10 .Move 30 16 (some 4) (pos 2 67 14 0) 1 #[9, 8, 7]),
  none, none,
  some (hwrV 13 .Move 30 16 (some 4) (pos 2 67 2 0) 2 #[4, 9, 10]),
  none,
  some (hwrV 15 .Dereference 2 0 none (pos 2 67 2 0) 1 #[4, 13]),
  some (hwrV 16 .MakeResult 36 0 none (pos 2 67 2 0) 1 #[15, 13])]

/-- The blocks of section 19, by ID. -/
def uuidBlocks : Array (Option Block) := #[none,
  some (mkB 1 .Ret (pos 2 67 2 1) #[16] #[] #[] #[1, 2, 4, 5, 6, 7, 8, 9, 10, 13, 15, 16])]

/-- `New`, section 19 (the input of `expand calls`). -/
def uuidNew : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 16
  bidLast := 1
  blocks := #[1]
  blockTab := uuidBlocks
  valueTab := uuidValues
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := [14, 12, 11, 3]
  freeBlocks := []
  cache :=
    { postorder := some #[1]
      idom := some #[none, none]
      sdom := some #[default, { parent := none, child := none, sibling := none, entry := 2,
                                exit := 5 }]
      auxmap := some #[(none, 1), (some 3, 2), (some 7, 3)]
      lineStarts := some #[{ index := 2, bounds := some (66, 67), pending := #[] }] }

/-- `check`'s environment for the input. -/
def uuidCheckEnv : CheckEnv := { tabs := uuidTabs, typs := sf2Typs }

/-- What `expand calls` reads of the export's environment (the configuration entries it and
`check` read). -/
def uuidPassEnv : PassEnv where
  passName := "expand calls"
  pkg := GoStr.ofString "uuid"
  funcName := GoStr.ofString "New"
  abi := 1
  nosplit := false
  pgohot := false
  config := #[("arch", #[.word "arm64"]), ("ptrsize", #[.word "8"]), ("regsize", #[.word "8"]),
    ("bigendian", #[.word "0"]), ("fixedframesize", #[.word "8"]),
    ("abi0", #[.word "0:0:8"]), ("abi1", #[.word "16:16:8"])]
  typs := sf2Typs
  typeOrder := default
  tables := uuidTabs

end GoFV.Proof.Witness
