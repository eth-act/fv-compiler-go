import GoFV.Proof.Witness.InitF10
import GoFV.Opt.DeadAutosCheck

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function: `f0` of `test/stack` at `dead auto elim`

`test/stack/main/f0,1.ssa`, the output of section 24 (`late opt`, the input of
`dead auto elim`), of the corpus `gofv-corpus/2aae1000ea1d/quick-v1/plain`, transcribed by hand
(the analysis caches left empty; `run`, `check` and the pass do not read them). Found by
`lake exe mem-probe --dae-candidates` (accepted changes of functions without calls):

```go
func f0() { _ = g() }   // g, inlined twice, returns a [3000]byte: var x [3000]byte; return x
```

Each inlined result `~r0` (`a3`, `a5`: `PAUTO`s whose address is not taken, frame temporaries
`Blk.temp`) is cleared by `VarDef` and `Zero [3000]` and never read: dead auto elim turns all
four writes into `Copy`.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt

/-- `abiInfo` of `f0`: no parameters, no results. -/
def stackF0ABI : CallABI :=
  { abi := 1, nin := 0, nout := 0, spillOff := 8, spillSize := 0, inRegs := 0, outRegs := 0,
    params := #[] }

/-- The definition tables (the types of the values and auxes and `typs`' `Int`, `Uintptr`,
`Mem`, `Flags`, `Void`). -/
def stackF0Tabs : Tables where
  posBases := #[]
  types :=
    let t := Array.replicate 36 (none : Option TypeDef)
    let t := t.set! 1 (some (mkTy .FUNC (some 8) (some 8) (some 8) true true false false
      "func()" "func()" (.func 0 0 0 #[])))
    let t := t.set! 11 (some (mkTy .INT (some 8) (some 8) (some 0) false false true true
      "int" "int"))
    let t := t.set! 15 (some (mkTy .UINTPTR (some 8) (some 8) (some 0) false false true true
      "uintptr" "uintptr"))
    let t := t.set! 28 (some (mkTy .SSA none none none false false false false "mem" ""))
    let t := t.set! 29 (some (mkTy .SSA none none none false false false false "flags" ""))
    let t := t.set! 30 (some (mkTy .SSA none none none false false false false "void" ""))
    let t := t.set! 32 (some (mkTy .RESULTS none none none false false false false "mem" ""
      (.results #[28])))
    let t := t.set! 33 (some (mkTy .ARRAY (some 3000) (some 1) (some 0) false false true false
      "[3000]byte" "[3000]uint8" (.array 34 3000)))
    let t := t.set! 34 (some (mkTy .UINT8 (some 1) (some 1) (some 0) false false true true
      "byte" "uint8"))
    t.set! 35 (some (mkTy .PTR (some 8) (some 8) (some 8) true true true false
      "*[3000]byte" "*[3000]uint8" (.elem 33)))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.f0}", kind := .call (some 2) (some stackF0ABI) },
    some { fmt := GoStr.ofString "main.f0",
           kind := .sym (GoStr.ofString "main.f0") 1 "-" 0 default none none none #[] none },
    some { fmt := GoStr.ofString "~r0",
           kind := .name (GoStr.ofString "~r0") .PAUTO 33 0 1 {} (pos 5 55 11 0) },
    some { fmt := GoStr.ofString "[3000]byte", kind := .type 33 },
    some { fmt := GoStr.ofString "~r0",
           kind := .name (GoStr.ofString "~r0") .PAUTO 33 0 1 {} (pos 4 41 11 0) }]
  slots := #[]

def mkV3 (id : ID) (op : Op) (t : TypeRef) (auxInt : Int64) (aux : Option AuxRef) (p : Pos)
    (uses : Nat) (args : Array ID) : Value :=
  { id, op, type := t, auxInt, aux, pos := p, uses, args, block := 3 }

/-- The values, by ID. -/
def stackF0Values : Array (Option Value) := #[none,
  some (mkV3 1 .InitMem 28 0 none p0 2 #[]),
  some (mkV3 2 .SP 15 0 none p0 2 #[]),
  none,
  some (mkV3 4 .InlMark 30 1 none (pos 2 38 4 1) 0 #[1]),
  none,
  some (mkV3 6 .VarDef 28 0 (some 3) (pos 4 51 4 2) 2 #[1]),
  some (mkV3 7 .LocalAddr 35 0 (some 3) (pos 4 51 4 1) 1 #[2, 6]),
  some (mkV3 8 .Zero 28 3000 (some 4) (pos 4 51 4 0) 1 #[7, 6]),
  none,
  some (mkV3 10 .VarDef 28 0 (some 5) (pos 2 38 4 2) 2 #[8]),
  some (mkV3 11 .LocalAddr 35 0 (some 5) (pos 2 38 4 0) 1 #[2, 10]),
  some (mkV3 12 .Zero 28 3000 (some 4) (pos 2 38 4 1) 1 #[11, 10]),
  none,
  some (mkV3 14 .MakeResult 32 0 none (pos 2 39 1 1) 1 #[12])]

/-- The blocks, by ID. -/
def stackF0Blocks : Array (Option Block) := #[none, none, none,
  some (mkB 3 .Ret (pos 2 39 1 0) #[14] #[] #[] #[1, 2, 4, 6, 7, 8, 10, 11, 12, 14])]

/-- `f0`, the input of `dead auto elim`. -/
def stackF0 : Func where
  entry := 3
  type := 1
  ownAux := some 1
  vidLast := 14
  bidLast := 3
  blocks := #[3]
  blockTab := stackF0Blocks
  valueTab := stackF0Values
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := [13, 9, 5, 3]
  freeBlocks := [2, 1]
  cache := {}

/-- `Config.Types` (the part `check` and the pass read). -/
def stackF0Typs : Array (String × TypeRef) :=
  #[("Int", 11), ("Uintptr", 15), ("Mem", 28), ("Flags", 29), ("Void", 30)]

/-- `check`'s environment. -/
def stackF0CheckEnv : CheckEnv := { tabs := stackF0Tabs, typs := stackF0Typs }

/-- What `dead auto elim` reads of the export's environment. -/
def stackF0PassEnv : PassEnv where
  passName := "dead auto elim"
  pkg := GoStr.ofString "main"
  funcName := GoStr.ofString "f0"
  abi := 1
  nosplit := false
  pgohot := false
  config := #[]
  typs := stackF0Typs
  typeOrder := default
  tables := stackF0Tabs

end GoFV.Proof.Witness
