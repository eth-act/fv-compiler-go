import GoFV.Proof.RefineL
import GoFV.Proof.Witness.Clamp

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function: lowered `clamp`

`examples/arith/main/clamp,1.ssa`, section 48 (`phi tighten`, the input of `likelyadjust`), of
the corpus `gofv-corpus/2aae1000ea1d/quick-v7/plain`, transcribed by hand (`clamp` of
`GoFV.Proof.Witness.Clamp` after `lower` … `phi tighten`):

```
b1: ARM64GT (CMP lo x) -> b3 b2        b2: ARM64LT (CMP hi x) -> b5 b4
b3: Ret lo   b4: Ret x   b5: Ret hi    (x, lo, hi: ArgIntReg)
```

It is lowered (`Func.lowered`: arm64 ops `CMP` and block kinds `GT`/`LT`), so the `runL`
theorems of the lowered passes are exercised on arm64 semantics, not only on `runL_generic`.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem

/-- The definition tables of section 48 that `runL` reads (`clampTabs` plus the `flags` type
and the `nameOff` auxes of the `ArgIntReg`s). -/
def clampLTabs : Tables where
  types :=
    let t := clampTabs.types
    t.set! 29 (some (mkT .SSA none "flags"))
  auxes := clampTabs.auxes ++ #[
    some { fmt := GoStr.ofString "x+0", kind := .nameOff 3 0 },
    some { fmt := GoStr.ofString "lo+0", kind := .nameOff 4 0 },
    some { fmt := GoStr.ofString "hi+0", kind := .nameOff 5 0 }]

/-- `v<id> <op> t<type> <auxInt> <aux>` with position `p` and use count. -/
def mkVI (id : ID) (op : Op) (t : TypeRef) (auxInt : Int64) (aux : Option AuxRef) (p : Pos)
    (uses : Nat) (args : Array ID) (blk : ID) : Value :=
  { id, op, type := t, auxInt, aux, pos := p, uses, args, block := blk }

/-- The values of section 48, by ID. -/
def clampLValues : Array (Option Value) :=
  let t := Array.replicate 25 (none : Option Value)
  let t := t.set! 1 (some (mkV 1 .InitMem 28 none p0 3 #[] 1))
  let t := t.set! 8 (some (mkVI 8 .ArgIntReg 2 0 (some 7) (pos 2 22 7 0) 3 #[] 1))
  let t := t.set! 9 (some (mkVI 9 .ArgIntReg 2 1 (some 8) (pos 2 22 7 0) 2 #[] 1))
  let t := t.set! 10 (some (mkVI 10 .ArgIntReg 2 2 (some 9) (pos 2 22 7 0) 2 #[] 1))
  let t := t.set! 22 (some (mkV 22 .ARM64CMP 29 none (pos 2 22 7 1) 1 #[9, 8] 1))
  let t := t.set! 14 (some (mkV 14 .ARM64CMP 29 none (pos 2 25 7 1) 1 #[10, 8] 2))
  let t := t.set! 15 (some (mkV 15 .MakeResult 33 none (pos 2 23 3 1) 1 #[9, 1] 3))
  let t := t.set! 24 (some (mkV 24 .MakeResult 33 none (pos 2 28 2 1) 1 #[8, 1] 4))
  t.set! 21 (some (mkV 21 .MakeResult 33 none (pos 2 26 3 1) 1 #[10, 1] 5))

/-- The blocks of section 48, by ID. -/
def clampLBlocks : Array (Option Block) := #[none,
  some (mkB 1 .ARM64GT (pos 2 22 7 0) #[22] #[⟨3, 0⟩, ⟨2, 0⟩] #[] #[1, 8, 9, 10, 22]),
  some (mkB 2 .ARM64LT (pos 2 25 7 0) #[14] #[⟨5, 0⟩, ⟨4, 0⟩] #[⟨1, 1⟩] #[14]),
  some (mkB 3 .Ret (pos 2 23 3 1) #[15] #[] #[⟨1, 0⟩] #[15]),
  some (mkB 4 .Ret (pos 2 28 2 1) #[24] #[] #[⟨2, 1⟩] #[24]),
  some (mkB 5 .Ret (pos 2 26 3 1) #[21] #[] #[⟨2, 0⟩] #[21])]

/-- Lowered `clamp`, section 48. -/
def clampL : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 24
  bidLast := 5
  blocks := #[1, 2, 3, 4, 5]
  blockTab := clampLBlocks
  valueTab := clampLValues
  names := #[(1, #[8]), (2, #[9]), (3, #[10])]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := [18, 13, 12, 23, 19, 20, 17, 16, 11, 7, 6, 5, 4, 3, 2]
  freeBlocks := []
  cache := { postorder := some #[3, 5, 4, 2, 1] }

theorem clampL_lowered : clampL.lowered = true := by decide +kernel

/-- Under `runL`: `clamp(5, 0, 10) = 5`, `clamp(-3, 0, 10) = 0`, `clamp(12, 0, 10) = 10`. -/
theorem clampL_run :
    returnsInt (runL Env.p1 clampLTabs clampL (clampArgs 5) {} 3) 5 = true ∧
    returnsInt (runL Env.p1 clampLTabs clampL (clampArgs (-3)) {} 3) 0 = true ∧
    returnsInt (runL Env.p1 clampLTabs clampL (clampArgs 12) {} 3) 10 = true := by
  decide +kernel

theorem clampL_run5 :
    ∃ m, runL Env.p1 clampLTabs clampL (clampArgs 5) {} 3 = .returned [.i64 5] m :=
  returnsInt_iff.1 clampL_run.1

end GoFV.Proof.Witness
