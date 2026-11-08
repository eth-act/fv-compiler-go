import GoFV.Proof.Witness.Clamp

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness runs: defer and recover (P5, `docs/plans/semantics.md` §9.7)

Two functions in the shape the frontend gives them (section 0, `start`), written by hand after
`tools/semdiff/prog/defers.go`, run with `GoFV.SSA.run` (evaluated by the kernel,
`decide +kernel`) in an environment whose program functions are the deferred ones
(`Env.withFuncs`):

```go
func recoverOpen() (r int) {
	defer recoverer() // open-coded: deferBits |= 1, the closure in slot 0
	r = 7
	panicdivide()     // runtime.panicdivide: the deferred call recovers, r is returned
}

func recoverer() { recover() }

func deferLoop() {
	defer setX()      // deferproc (as for a defer in a loop), then deferreturn at the exit
}

func setX() { x = 42 }
```

`recoverOpen` panics in its last call; `finish` runs its open-coded defer (`runDefers`,
`nextDefer`: the `deferbits` variable's bit 0, the `opendeferslot` closure), whose `gorecover`
recovers the panic, so the run returns the result variable `r = 7`. `deferLoop` registers
`setX` with `runtime.deferproc` (`Env.atAct`), its `Defer` block continues at successor 0, and
`runtime.deferreturn` runs `setX`, so the run returns with `x = 42`.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem

/-- A value with an `auxInt`. -/
def dwV (id : ID) (op : Op) (t : TypeRef) (auxInt : Int64) (aux : Option AuxRef) (uses : Nat)
    (args : Array ID) (blk : ID) : Value :=
  { id, op, type := t, auxInt, aux, pos := p0, uses, args, block := blk }

/-- A symbol aux. -/
def dwSym (s : String) : AuxDef :=
  { fmt := GoStr.ofString s, kind := .sym (GoStr.ofString s) 1 "" 0 default none none none #[] none }

/-- An `AuxCall` of the symbol aux `fn`. -/
def dwCall (s : String) (fn : AuxRef) (abi : Option CallABI) : AuxDef :=
  { fmt := GoStr.ofString s!"AuxCall\{{s}}", kind := .call (some fn) abi }

/-- A frame variable. -/
def dwName (s : String) (cls : NameClass) (t : TypeRef) (off : Int) (fl : NameFlags) : AuxDef :=
  { fmt := GoStr.ofString s, kind := .name (GoStr.ofString s) cls t off 1 fl p0 }

/-- An ABI without parameters. -/
def dwABI0 : CallABI :=
  { abi := 1, nin := 0, nout := 0, spillOff := 0, spillSize := 0, inRegs := 0, outRegs := 0,
    params := #[] }

/-- A function of no parameters. -/
def dwFunc (vidLast bidLast : ID) (blocks : Array ID) (bt : Array (Option Block))
    (vt : Array (Option Value)) : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := vidLast
  bidLast := bidLast
  blocks := blocks
  blockTab := bt
  valueTab := vt
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := {}

/-! ## `recoverer`: `recover()` -/

/-- `runtime.gorecover`'s ABI: one `interface {}` result in two registers. -/
def rcRecoverABI : CallABI :=
  { abi := 1, nin := 0, nout := 1, spillOff := 0, spillSize := 0, inRegs := 0, outRegs := 2,
    params := #[{ out := true, index := 0, type := 2, name := none, regs := #[0, 1],
                  offset := -1 }] }

def rcTabs : Tables where
  types :=
    let t := Array.replicate 34 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func()" (.func 0 0 0 #[])))
    let t := t.set! 2 (some (mkT .INTER (some 16) "interface {}"))
    let t := t.set! 28 (some (mkT .SSA none "mem"))
    let t := t.set! 32 (some (mkT .RESULTS none "mem" (.results #[28])))
    t.set! 33 (some (mkT .RESULTS none "interface {},mem" (.results #[2, 28])))
  auxes := #[none, dwCall "main.recoverer" 2 (some dwABI0), dwSym "main.recoverer",
    dwCall "runtime.gorecover" 4 (some rcRecoverABI), dwSym "runtime.gorecover"]

def recoverer : Func :=
  dwFunc 4 1 #[1]
    #[none, some (mkB 1 .Ret p0 #[4] #[] #[] #[1, 2, 3, 4])]
    #[none,
      some (dwV 1 .InitMem 28 0 none 1 #[] 1),
      some (dwV 2 .StaticLECall 33 0 (some 3) 1 #[1] 1),
      some (dwV 3 .SelectN 28 1 none 1 #[2] 1),
      some (dwV 4 .MakeResult 32 0 none 1 #[3] 1)]

/-! ## `setX`: `x = 42` -/

def sxTabs : Tables where
  types :=
    let t := Array.replicate 34 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func()" (.func 0 0 0 #[])))
    let t := t.set! 2 (some (mkT .INT (some 8) "int"))
    let t := t.set! 7 (some (mkT .PTR (some 8) "*int" (.elem 2)))
    let t := t.set! 8 (some (mkT .UINTPTR (some 8) "uintptr"))
    let t := t.set! 28 (some (mkT .SSA none "mem"))
    t.set! 32 (some (mkT .RESULTS none "mem" (.results #[28])))
  auxes := #[none, dwCall "main.setX" 2 (some dwABI0), dwSym "main.setX", dwSym "main.x",
    some { fmt := GoStr.ofString "int", kind := .type 2 }]

def setX : Func :=
  dwFunc 6 1 #[1]
    #[none, some (mkB 1 .Ret p0 #[6] #[] #[] #[1, 2, 3, 4, 5, 6])]
    #[none,
      some (dwV 1 .InitMem 28 0 none 1 #[] 1),
      some (dwV 2 .SB 8 0 none 1 #[] 1),
      some (dwV 3 .Addr 7 0 (some 3) 1 #[2] 1),
      some (dwV 4 .Const64 2 42 none 1 #[] 1),
      some (dwV 5 .Store 28 0 (some 4) 1 #[3, 4, 1] 1),
      some (dwV 6 .MakeResult 32 0 none 1 #[5] 1)]

/-! ## The environment -/

/-- The deferred functions as program functions. -/
def dwFuncs : String → Option Ctx
  | "main.recoverer" => some (Ctx.make rcTabs recoverer)
  | "main.setX" => some (Ctx.make sxTabs setX)
  | _ => none

/-- A function value's closure: its code pointer (`Addr {f·f}` points to it). -/
def dwClosure (f : String) : Alloc :=
  { data := encode (.ptr none) (.ptr ⟨.global f, 0⟩), writable := false }

/-- `Env.p1` with the closures of the deferred functions and the global `x`, and the deferred
functions as program functions (fuel 4 per activation, one level deep). -/
def dwEnv : Env :=
  Env.withFuncs
    { Env.p1 with
      globals := [("main.recoverer·f", dwClosure "main.recoverer"),
        ("main.setX·f", dwClosure "main.setX"),
        ("main.x", { data := Array.replicate 8 (.b 0), writable := true })] }
    dwFuncs 4 1

/-! ## `recoverOpen`: an open-coded defer that recovers -/

/-- `recoverOpen`'s ABI: the result `r` in a register. -/
def roABI : CallABI :=
  { abi := 1, nin := 0, nout := 1, spillOff := 0, spillSize := 0, inRegs := 0, outRegs := 1,
    params := #[{ out := true, index := 0, type := 2, name := some 5, regs := #[0],
                  offset := -1 }] }

def roTabs : Tables where
  types :=
    let t := Array.replicate 34 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func() int" (.func 0 0 1 #[])))
    let t := t.set! 2 (some (mkT .INT (some 8) "int"))
    let t := t.set! 3 (some (mkT .UINT8 (some 1) "uint8"))
    let t := t.set! 4 (some (mkT .PTR (some 8) "*uint8" (.elem 3)))
    let t := t.set! 5 (some (mkT .FUNC (some 8) "func()" (.func 0 0 0 #[])))
    let t := t.set! 6 (some (mkT .PTR (some 8) "*func()" (.elem 5)))
    let t := t.set! 7 (some (mkT .PTR (some 8) "*int" (.elem 2)))
    let t := t.set! 8 (some (mkT .UINTPTR (some 8) "uintptr"))
    let t := t.set! 28 (some (mkT .SSA none "mem"))
    t.set! 32 (some (mkT .RESULTS none "mem" (.results #[28])))
  auxes := #[none, dwCall "main.recoverOpen" 2 (some roABI), dwSym "main.recoverOpen",
    dwName ".autotmp_1" .PAUTO 3 0 { used := true, autotmp := true, deferbits := true },
    dwName ".autotmp_2" .PAUTO 5 0 { used := true, autotmp := true, opendeferslot := true },
    dwName "r" .PPARAMOUT 2 0 { used := true },
    some { fmt := GoStr.ofString "uint8", kind := .type 3 },
    some { fmt := GoStr.ofString "func()", kind := .type 5 },
    some { fmt := GoStr.ofString "int", kind := .type 2 },
    dwSym "main.recoverer·f",
    dwCall "runtime.panicdivide" 11 none, dwSym "runtime.panicdivide"]

def recoverOpen : Func :=
  dwFunc 14 1 #[1]
    #[none, some (mkB 1 .Exit p0 #[14] #[] #[] #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14])]
    #[none,
      some (dwV 1 .InitMem 28 0 none 3 #[] 1),
      some (dwV 2 .SP 8 0 none 3 #[] 1),
      some (dwV 3 .SB 8 0 none 1 #[] 1),
      -- deferBits = 1
      some (dwV 4 .LocalAddr 4 0 (some 3) 1 #[2, 1] 1),
      some (dwV 5 .Const8 3 1 none 1 #[] 1),
      some (dwV 6 .Store 28 0 (some 6) 2 #[4, 5, 1] 1),
      -- the open-coded defer slot 0 = recoverer
      some (dwV 7 .Addr 5 0 (some 9) 1 #[3] 1),
      some (dwV 8 .LocalAddr 6 0 (some 4) 1 #[2, 6] 1),
      some (dwV 9 .Store 28 0 (some 7) 2 #[8, 7, 6] 1),
      -- r = 7
      some (dwV 10 .LocalAddr 7 0 (some 5) 1 #[2, 9] 1),
      some (dwV 11 .Const64 2 7 none 1 #[] 1),
      some (dwV 12 .Store 28 0 (some 8) 1 #[10, 11, 9] 1),
      some (dwV 13 .StaticLECall 32 0 (some 10) 1 #[12] 1),
      some (dwV 14 .SelectN 28 0 none 1 #[13] 1)]

/-- **An open-coded defer that recovers**: `recoverOpen` panics (`runtime.panicdivide`), its
deferred `recoverer` recovers, and the run returns the result variable `r = 7`. -/
theorem recoverOpen_run : returnsInt (run dwEnv roTabs recoverOpen [] {} 4) 7 = true := by
  decide +kernel

/-! ## `deferLoop`: `deferproc` and `deferreturn` -/

/-- `runtime.deferproc`'s ABI: the closure in a register. -/
def dfLoopDeferprocABI : CallABI :=
  { abi := 1, nin := 1, nout := 0, spillOff := 0, spillSize := 8, inRegs := 1, outRegs := 0,
    params := #[{ out := false, index := 0, type := 1, name := none, regs := #[0], offset := 0 }] }

def dfLoopTabs : Tables where
  types :=
    let t := Array.replicate 34 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func()" (.func 0 0 0 #[])))
    let t := t.set! 8 (some (mkT .UINTPTR (some 8) "uintptr"))
    let t := t.set! 28 (some (mkT .SSA none "mem"))
    t.set! 32 (some (mkT .RESULTS none "mem" (.results #[28])))
  auxes := #[none, dwCall "main.deferLoop" 2 (some dwABI0), dwSym "main.deferLoop",
    dwSym "main.setX·f",
    dwCall "runtime.deferproc" 5 (some dfLoopDeferprocABI), dwSym "runtime.deferproc",
    dwCall "runtime.deferreturn" 7 (some dwABI0), dwSym "runtime.deferreturn"]

def deferLoop : Func :=
  dwFunc 11 3 #[1, 2, 3]
    #[none,
      some (mkB 1 .Defer p0 #[5] #[⟨2, 0⟩, ⟨3, 0⟩] #[] #[1, 2, 3, 4, 5]),
      some (mkB 2 .Ret p0 #[8] #[] #[⟨1, 0⟩] #[6, 7, 8]),
      some (mkB 3 .Ret p0 #[11] #[] #[⟨1, 1⟩] #[9, 10, 11])]
    #[none,
      some (dwV 1 .InitMem 28 0 none 1 #[] 1),
      some (dwV 2 .SB 8 0 none 1 #[] 1),
      some (dwV 3 .Addr 1 0 (some 3) 1 #[2] 1),
      some (dwV 4 .StaticLECall 32 0 (some 4) 1 #[3, 1] 1),
      some (dwV 5 .SelectN 28 0 none 3 #[4] 1),
      -- the normal exit
      some (dwV 6 .StaticLECall 32 0 (some 6) 1 #[5] 2),
      some (dwV 7 .SelectN 28 0 none 1 #[6] 2),
      some (dwV 8 .MakeResult 32 0 none 1 #[7] 2),
      -- the recovery edge (`f.DeferReturn`)
      some (dwV 9 .StaticLECall 32 0 (some 6) 1 #[5] 3),
      some (dwV 10 .SelectN 28 0 none 1 #[9] 3),
      some (dwV 11 .MakeResult 32 0 none 1 #[10] 3)]

/-- The outcome returns no result with `x = 42`. -/
def returnsX42 : Outcome → Bool
  | .returned [] m =>
    match m.load (.int .w64) ⟨.global "main.x", 0⟩ with
    | .int .w64 x => x == 42
    | _ => false
  | _ => false

/-- **`deferproc`/`deferreturn`**: `deferLoop` registers `setX`, and `deferreturn` runs it at
the normal exit: the run returns with `x = 42`. -/
theorem deferLoop_run : returnsX42 (run dwEnv dfLoopTabs deferLoop [] {} 4) = true := by
  decide +kernel

end GoFV.Proof.Witness
