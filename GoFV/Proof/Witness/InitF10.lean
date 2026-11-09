import GoFV.Proof.Witness.Clamp
import GoFV.SSA.Check
import GoFV.Opt.DeadStoreCheck

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function: `f10` of `test/initialize` at `dse`

`test/initialize/main/f10,1.ssa`, the output of section 29 (`check bce`, the input of `dse`), of
the corpus `gofv-corpus/2aae1000ea1d/quick-v1/plain`, transcribed by hand (the analysis caches
left empty; `run`, `check` and `dse` do not read them):

```go
func f10(s *S) [2]*S { return [2]*S{s, s} }
```

The result `~r0` (16 bytes) is on the stack: `v8 = Zero [16] (LocalAddr {~r0}) …` clears it,
then the two `Store`s of `s` at offsets 0 and 8 overwrite every byte. dse turns `v8` into
`Copy v7`.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt

/-- A type definition with the exported flags `hasptr`, `direct`, `comparable`, `named`. -/
def mkTy (kind : TypeKind) (size align ptrdata : Option Int) (hasptr direct comparable named : Bool)
    (str symName : String) (tail : TypeTail := .none) : TypeDef :=
  { kind, size, align, ptrdata, flags := { hasptr, direct, comparable, named },
    str := GoStr.ofString str, symName := GoStr.ofString symName, tail }

def f10Field (name : String) (t : TypeRef) (off : Option Int) : Field :=
  { name := GoStr.ofString name, type := t, offset := off, embedded := false }

/-- `abiInfo` of `f10`: one register parameter, a stack result. -/
def f10ABI : CallABI :=
  { abi := 1, nin := 1, nout := 1, spillOff := 24, spillSize := 8, inRegs := 1, outRegs := 0,
    params := #[{ out := false, index := 0, type := 2, name := some 3, regs := #[0], offset := 0 },
                { out := true, index := 0, type := 5, name := some 4, regs := #[], offset := 8 }] }

/-- The definition tables `run`, `check` and `dse` read (the types of the values and auxes and
`typs`' `Mem`, `Uintptr`, `Int`, `Void`). -/
def f10Tabs : Tables where
  posBases := #[]
  types :=
    let t := Array.replicate 39 (none : Option TypeDef)
    let t := t.set! 1 (some (mkTy .FUNC (some 8) (some 8) (some 8) true true false false
      "func(*S) [2]*S" "func(*main.S) [2]*main.S"
      (.func 0 1 1 #[f10Field "s" 2 none, f10Field "" 5 none])))
    let t := t.set! 2 (some (mkTy .PTR (some 8) (some 8) (some 8) true true true false
      "*S" "*main.S" (.elem 3)))
    let t := t.set! 3 (some (mkTy .STRUCT (some 48) (some 8) (some 0) false false true true
      "S" "main.S" (.struct #[f10Field "A" 4 (some 0), f10Field "B" 4 (some 8),
        f10Field "C" 4 (some 16), f10Field "X" 4 (some 24), f10Field "Y" 4 (some 32),
        f10Field "Z" 4 (some 40)])))
    let t := t.set! 4 (some (mkTy .INT (some 8) (some 8) (some 0) false false true true
      "int" "int"))
    let t := t.set! 5 (some (mkTy .ARRAY (some 16) (some 8) (some 16) true false true false
      "[2]*S" "[2]*main.S" (.array 2 2)))
    let t := t.set! 18 (some (mkTy .UINTPTR (some 8) (some 8) (some 0) false false true true
      "uintptr" "uintptr"))
    let t := t.set! 31 (some (mkTy .SSA none none none false false false false "mem" ""))
    let t := t.set! 33 (some (mkTy .SSA none none none false false false false "void" ""))
    let t := t.set! 35 (some (mkTy .RESULTS none none none false false false false "mem" ""
      (.results #[31])))
    let t := t.set! 36 (some (mkTy .PTR (some 8) (some 8) (some 8) true true true false
      "**S" "**main.S" (.elem 2)))
    t.set! 37 (some (mkTy .PTR (some 8) (some 8) (some 8) true true true false
      "*[2]*S" "*[2]*main.S" (.elem 5)))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.f10}", kind := .call (some 2) (some f10ABI) },
    some { fmt := GoStr.ofString "main.f10",
           kind := .sym (GoStr.ofString "main.f10") 1 "-" 0 default none none none #[] none },
    some { fmt := GoStr.ofString "s",
           kind := .name (GoStr.ofString "s") .PPARAM 2 16 1 { used := true } (pos 2 55 10 0) },
    some { fmt := GoStr.ofString "~r0",
           kind := .name (GoStr.ofString "~r0") .PPARAMOUT 5 0 1 { used := true }
             (pos 2 55 16 0) },
    some { fmt := GoStr.ofString "[2]*S", kind := .type 5 },
    some { fmt := GoStr.ofString "*S", kind := .type 2 },
    some { fmt := GoStr.ofString "s+0", kind := .nameOff 3 0 }]
  slots := #[none, some { name := 3, type := 2, off := 0, splitOf := none, splitOffset := 0 }]

def mkVa (id : ID) (op : Op) (t : TypeRef) (auxInt : Int64) (aux : Option AuxRef) (p : Pos)
    (uses : Nat) (args : Array ID) : Value :=
  { id, op, type := t, auxInt, aux, pos := p, uses, args, block := 1 }

/-- The values, by ID. -/
def f10Values : Array (Option Value) := #[none,
  some (mkVa 1 .InitMem 31 0 none p0 2 #[]),
  some (mkVa 2 .SP 18 0 none p0 1 #[]),
  none, none,
  some (mkVa 5 .LocalAddr 37 0 (some 4) p0 3 #[2, 1]),
  some (mkVa 6 .ArgIntReg 2 0 (some 7) (pos 2 55 24 1) 2 #[]),
  some (mkVa 7 .VarDef 31 0 (some 4) (pos 2 55 6 2) 1 #[1]),
  some (mkVa 8 .Zero 31 16 (some 5) (pos 2 55 6 1) 1 #[5, 7]),
  some (mkVa 9 .VarDef 31 0 (some 4) (pos 2 55 24 2) 1 #[8]),
  none, none, none, none, none,
  some (mkVa 15 .OffPtr 36 0 none (pos 2 55 24 0) 1 #[5]),
  some (mkVa 16 .Store 31 0 (some 6) (pos 2 55 24 0) 1 #[15, 6, 9]),
  none, none,
  some (mkVa 19 .OffPtr 36 8 none (pos 2 55 24 0) 1 #[5]),
  some (mkVa 20 .Store 31 0 (some 6) (pos 2 55 24 0) 1 #[19, 6, 16]),
  none, none,
  some (mkVa 23 .MakeResult 35 0 none (pos 2 55 24 0) 1 #[20]),
  none]

/-- The blocks, by ID. -/
def f10Blocks : Array (Option Block) := #[none,
  some (mkB 1 .Ret (pos 2 55 24 1) #[23] #[] #[] #[1, 2, 6, 5, 7, 8, 15, 19, 9, 16, 20, 23])]

/-- `f10`, the input of `dse`. -/
def f10 : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 24
  bidLast := 1
  blocks := #[1]
  blockTab := f10Blocks
  valueTab := f10Values
  names := #[(1, #[6])]
  namedx := #[]
  splits := #[]
  canon := #[({ name := 3, type := 2, off := 0, splitOf := none, splitOffset := 0 }, 1)]
  consts := #[]
  freeValues := [12, 17, 21, 22, 24, 3, 4, 14, 18, 13, 11, 10]
  freeBlocks := []
  cache := {}

/-- `check`'s environment: the `Config.Types` `run`'s and `check`'s lookups use. -/
def f10CheckEnv : CheckEnv :=
  { tabs := f10Tabs, typs := #[("Int", 4), ("Uintptr", 18), ("Mem", 31), ("Void", 33)] }

/-- What `dse` reads of the export's environment. -/
def f10PassEnv : PassEnv where
  passName := "dse"
  pkg := GoStr.ofString "main"
  funcName := GoStr.ofString "f10"
  abi := 1
  nosplit := false
  pgohot := false
  config := #[]
  typs := #[("Int", 4), ("Uintptr", 18), ("Mem", 31), ("Void", 33)]
  typeOrder := default
  tables := f10Tabs

/-- The argument of the witness run: a pointer `s` (to the start of a heap object). -/
def f10Args : List Val := [.ptr ⟨.heap 0, 0⟩]

/-- The result `[2]*S{s, s}`: a 16-byte array (a blob), the pointer's bytes twice. -/
def f10Result : Val := .blob (ptrBytes ⟨.heap 0, 0⟩ ++ ptrBytes ⟨.heap 0, 0⟩).toList

end GoFV.Proof.Witness
