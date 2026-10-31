import GoFV.SSA.Sem.Run

/-!
# Witness function: `clamp` from the corpus

`examples/arith/main/clamp,1.ssa`, section 0 (`start`), of the corpus
`gofv-corpus/2aae1000ea1d/plain`, transcribed by hand:

```go
func clamp(x, lo, hi int) int {
	if x < lo {
		return lo
	}
	if hi < x {
		return hi
	}
	return x
}
```

It has what the early passes act on: statement marks (`number lines`), copies (`copyelim`),
dead values (`SP`, `SB`, `LocalAddr`, `Const64`: `deadcode`), and zero-argument values
(`zero arg cse`). The tables hold the definitions `run` reads (types of its values, the
`AuxCall` of the function with its parameter names). The non-vacuity witnesses of the pass
theorems run it with `GoFV.SSA.run` (evaluated by the kernel, `decide +kernel`).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem

/-- `p<index>:<line>:<col>:<stmt>:<xlogue>`. -/
def pos (index line col stmt : Nat) : Pos := ⟨index, line, col, stmt, 0⟩

def mkV (id : ID) (op : Op) (t : TypeRef) (aux : Option AuxRef) (p : Pos) (uses : Nat)
    (args : Array ID) (blk : ID) : Value :=
  { id, op, type := t, auxInt := 0, aux, pos := p, uses, args, block := blk }

def mkT (kind : TypeKind) (size : Option Int) (str : String) (tail : TypeTail := .none) :
    TypeDef :=
  { kind, size, align := size, ptrdata := none, flags := {}, str := GoStr.ofString str,
    symName := GoStr.ofString "", tail }

def p0 : Pos := pos 0 0 0 0

def paramName (s : String) (cls : NameClass) (off : Int) : AuxDef :=
  { fmt := GoStr.ofString s, kind := .name (GoStr.ofString s) cls 2 off 1 {} p0 }

def abiParam (out : Bool) (i : Nat) (n : AuxRef) (off : Int) : ABIParam :=
  { out, index := i, type := 2, name := some n, regs := #[i], offset := off }

/-- `abiInfo` of `clamp`: three integer register parameters, one result. -/
def clampABI : CallABI :=
  { abi := 1, nin := 3, nout := 1, spillOff := 8, spillSize := 24, inRegs := 3, outRegs := 1,
    params := #[abiParam false 0 3 0, abiParam false 1 4 8, abiParam false 2 5 16,
                abiParam true 0 6 (-1)] }

/-- The definition tables of section 0 that `run` reads. -/
def clampTabs : Tables where
  types :=
    let t := Array.replicate 34 (none : Option TypeDef)
    let t := t.set! 1 (some (mkT .FUNC (some 8) "func(int, int, int) int" (.func 0 3 1 #[])))
    let t := t.set! 2 (some (mkT .INT (some 8) "int"))
    let t := t.set! 3 (some (mkT .BOOL (some 1) "bool"))
    let t := t.set! 15 (some (mkT .UINTPTR (some 8) "uintptr"))
    let t := t.set! 20 (some (mkT .PTR (some 8) "*int" (.elem 2)))
    let t := t.set! 28 (some (mkT .SSA none "mem"))
    t.set! 33 (some (mkT .RESULTS none "int,mem" (.results #[2, 28])))
  auxes := #[none,
    some { fmt := GoStr.ofString "AuxCall{main.clamp}", kind := .call (some 2) (some clampABI) },
    some { fmt := GoStr.ofString "main.clamp",
           kind := .sym (GoStr.ofString "main.clamp") 1 "" 0 default none none none #[] none },
    some (paramName "x" .PPARAM 0), some (paramName "lo" .PPARAM 8),
    some (paramName "hi" .PPARAM 16), some (paramName "~r0" .PPARAMOUT 0)]

/-- The values of section 0, by ID. -/
def clampValues : Array (Option Value) := #[none,
  some (mkV 1 .InitMem 28 none p0 7 #[] 1),
  some (mkV 2 .SP 15 none p0 4 #[] 1),
  some (mkV 3 .SB 15 none p0 0 #[] 1),
  some (mkV 4 .LocalAddr 20 (some 3) p0 0 #[2, 1] 1),
  some (mkV 5 .LocalAddr 20 (some 4) p0 0 #[2, 1] 1),
  some (mkV 6 .LocalAddr 20 (some 5) p0 0 #[2, 1] 1),
  some (mkV 7 .LocalAddr 20 (some 6) p0 0 #[2, 1] 1),
  some (mkV 8 .Arg 2 (some 3) (pos 2 21 6 2) 2 #[] 1),
  some (mkV 9 .Arg 2 (some 4) (pos 2 21 6 2) 2 #[] 1),
  some (mkV 10 .Arg 2 (some 5) (pos 2 21 6 2) 1 #[] 1),
  some (mkV 11 .Const64 2 none p0 0 #[] 1),
  some (mkV 12 .Less64 3 none (pos 2 22 7 0) 1 #[8, 9] 1),
  some (mkV 13 .Copy 2 none (pos 2 23 3 2) 1 #[9] 3),
  some (mkV 14 .Copy 28 none (pos 2 23 3 2) 1 #[1] 3),
  some (mkV 15 .MakeResult 33 none (pos 2 23 3 0) 1 #[13, 14] 3),
  some (mkV 16 .Copy 2 none (pos 2 25 7 2) 2 #[8] 2),
  some (mkV 17 .Copy 2 none (pos 2 25 7 2) 2 #[10] 2),
  some (mkV 18 .Less64 3 none (pos 2 25 7 0) 1 #[17, 16] 2),
  some (mkV 19 .Copy 2 none (pos 2 26 3 2) 1 #[17] 5),
  some (mkV 20 .Copy 28 none (pos 2 26 3 2) 1 #[1] 5),
  some (mkV 21 .MakeResult 33 none (pos 2 26 3 0) 1 #[19, 20] 5),
  some (mkV 22 .Copy 2 none (pos 2 28 2 2) 1 #[16] 4),
  some (mkV 23 .Copy 28 none (pos 2 28 2 2) 1 #[1] 4),
  some (mkV 24 .MakeResult 33 none (pos 2 28 2 0) 1 #[22, 23] 4)]

def mkB (id : ID) (kind : BlockKind) (p : Pos) (controls : Array ID) (succs preds : Array Edge)
    (values : Array ID) : Block :=
  { id, kind, pos := p, likely := .unknown, auxInt := 0, aux := none, controls, succs, preds,
    values }

/-- The blocks of section 0, by ID. -/
def clampBlocks : Array (Option Block) := #[none,
  some (mkB 1 .If (pos 2 22 7 0) #[12] #[⟨3, 0⟩, ⟨2, 0⟩] #[] #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12]),
  some (mkB 2 .If (pos 2 25 7 0) #[18] #[⟨5, 0⟩, ⟨4, 0⟩] #[⟨1, 1⟩] #[16, 17, 18]),
  some (mkB 3 .Ret (pos 2 23 3 1) #[15] #[] #[⟨1, 0⟩] #[13, 14, 15]),
  some (mkB 4 .Ret (pos 2 28 2 1) #[24] #[] #[⟨2, 1⟩] #[22, 23, 24]),
  some (mkB 5 .Ret (pos 2 26 3 1) #[21] #[] #[⟨2, 0⟩] #[19, 20, 21])]

/-- `clamp`, section 0. -/
def clamp : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 24
  bidLast := 5
  blocks := #[1, 2, 3, 4, 5]
  blockTab := clampBlocks
  valueTab := clampValues
  names := #[(1, #[8, 16, 22]), (2, #[9, 13]), (3, #[10, 17, 19])]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[(0, #[11])]
  freeValues := []
  freeBlocks := []
  cache := {}

/-- The outcome returns the single `int` result `v`. -/
def returnsInt : Outcome → BitVec 64 → Bool
  | .returned [.int .w64 x] _, v => x == v
  | _, _ => false

theorem returnsInt_iff {o : Outcome} {v : BitVec 64} :
    returnsInt o v = true ↔ ∃ m, o = .returned [.i64 v] m := by
  constructor
  · intro h
    match o, h with
    | .returned [.int .w64 x] m, h =>
      simp only [returnsInt, beq_iff_eq] at h
      exact ⟨m, by rw [h]⟩
  · rintro ⟨m, rfl⟩
    simp [returnsInt]

/-- The arguments of the witness runs: `clamp(5, 0, 10)`, `clamp(-3, 0, 10)`,
`clamp(12, 0, 10)`. -/
def clampArgs (x : BitVec 64) : List Val := [.i64 x, .i64 0, .i64 10]

/-- `clamp(5, 0, 10) = 5`, `clamp(-3, 0, 10) = 0`, `clamp(12, 0, 10) = 10`, with fuel 3 (entry,
then a `Ret`, or the second `If` and a `Ret`). -/
theorem clamp_run :
    returnsInt (run Env.p1 clampTabs clamp (clampArgs 5) {} 3) 5 = true ∧
    returnsInt (run Env.p1 clampTabs clamp (clampArgs (-3)) {} 3) 0 = true ∧
    returnsInt (run Env.p1 clampTabs clamp (clampArgs 12) {} 3) 10 = true := by
  decide +kernel

end GoFV.Proof.Witness
