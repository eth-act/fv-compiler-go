import GoFV.Proof.Pass.LoopRotateLoc
import GoFV.Proof.Witness.ClampL

/-!
# Non-vacuity witness: `loop rotate` under `runLoc`

`loopL`: an allocated (L2) countdown loop with the tables and arguments of lowered `clamp`
(`GoFV.Proof.Witness.ClampL`), written by hand in the shape regalloc leaves:

```
b1: v1 (InitMem) v8 (ArgIntReg x, R0)                    Plain -> b2
b2: v30 = Phi v8 v32 (R0)  v31 = CMPconst [0] v30         GT v31 -> b3 b5
b3: v32 = SUBconst [1] v30 (R0)                           Plain -> b2
b5: v34 = ADDconst [7] v30 (R0)                           Plain -> b4
b4: v33 = MakeResult v34 v1                               Ret
```

It returns 7 for `x = 3` under `runLoc` (`loopL_run`). `loop rotate` makes the back edge's
source `b3` the loop's top: the block order `b1 b2 b3 b5 b4` becomes `b1 b3 b2 b5 b4`
(`loopL_pass_facts`, by kernel evaluation), so `loopRotate_refinesLoc` applies to a pass run that
changes the function, and the output returns 7 too (`loopRotateLoc_witness`).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof

/-- The values of `loopL`, by ID. -/
def loopLValues : Array (Option Value) :=
  let t := Array.replicate 35 (none : Option Value)
  let t := t.set! 1 (some (mkV 1 .InitMem 28 none p0 2 #[] 1))
  let t := t.set! 8 (some (mkVI 8 .ArgIntReg 2 0 (some 7) (pos 2 22 7 0) 1 #[] 1))
  let t := t.set! 30 (some (mkV 30 .Phi 2 none (pos 2 23 3 0) 3 #[8, 32] 2))
  let t := t.set! 31 (some (mkVI 31 .ARM64CMPconst 29 0 none (pos 2 23 3 1) 1 #[30] 2))
  let t := t.set! 32 (some (mkVI 32 .ARM64SUBconst 2 1 none (pos 2 24 3 1) 1 #[30] 3))
  let t := t.set! 34 (some (mkVI 34 .ARM64ADDconst 2 7 none (pos 2 26 3 1) 1 #[30] 5))
  t.set! 33 (some (mkV 33 .MakeResult 33 none (pos 2 26 3 1) 1 #[34, 1] 4))

/-- The blocks of `loopL`, by ID. -/
def loopLBlocks : Array (Option Block) := #[none,
  some (mkB 1 .Plain (pos 2 22 7 0) #[] #[⟨2, 0⟩] #[] #[1, 8]),
  some (mkB 2 .ARM64GT (pos 2 23 3 0) #[31] #[⟨3, 0⟩, ⟨5, 0⟩] #[⟨1, 0⟩, ⟨3, 0⟩] #[30, 31]),
  some (mkB 3 .Plain (pos 2 24 3 0) #[] #[⟨2, 1⟩] #[⟨2, 0⟩] #[32]),
  some (mkB 4 .Ret (pos 2 26 3 1) #[33] #[] #[⟨5, 0⟩] #[33]),
  some (mkB 5 .Plain (pos 2 26 3 0) #[] #[⟨4, 0⟩] #[⟨2, 1⟩] #[34])]

/-- An allocated countdown loop (see the module comment). -/
def loopL : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 34
  bidLast := 5
  blocks := #[1, 2, 3, 5, 4]
  blockTab := loopLBlocks
  valueTab := loopLValues
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := {}
  low := { scheduled := true, laidout := true
           regAlloc := some (35, #[(8, .reg 0), (30, .reg 0), (32, .reg 0), (33, .results #[]),
             (34, .reg 0)]) }

/-- A pass environment for `loopL` (`loop rotate`). -/
def loopLPassEnv : PassEnv where
  passName := "loop rotate"
  pkg := GoStr.ofString "main"
  funcName := GoStr.ofString "loop"
  abi := 1
  nosplit := false
  pgohot := false
  config := #[]
  typs := #[]
  typeOrder := default
  tables := clampLTabs

/-- Under `runLoc`: `loop(3, 0, 10)` counts `x` down to 0 and returns `0 + 7`. -/
theorem loopL_run : returnsInt (runLoc Env.p1 clampLTabs loopL (clampArgs 3) {} 20) 7 = true := by
  decide +kernel

/-- `loop rotate` puts the loop's back-edge block `b3` before its header `b2`. -/
theorem loopL_pass_facts :
    ((loopRotate loopLPassEnv loopL).toOption.map (·.blocks)) = some #[1, 3, 2, 5, 4] := by
  decide +kernel

/-- `RefinesLoc` carries a returned integer to the target. -/
private theorem refinesLoc_returned_int {tabs tabs' : Tables} {f f' : Func}
    (h : RefinesLoc tabs' f' tabs f) {env : Env} {args : List Val} {mem m : Mem} {fuel : Nat}
    {w : Width} {x : BitVec w.bits} (hs : runLoc env tabs f args mem fuel = .returned [.int w x] m) :
    ∃ fuel' m', runLoc env tabs' f' args mem fuel' = .returned [.int w x] m' := by
  obtain ⟨fuel', ho⟩ := h env args mem fuel (by rw [hs]; trivial)
  rw [hs] at ho
  refine ⟨fuel', ?_⟩
  generalize runLoc env tabs' f' args mem fuel' = o at ho ⊢
  cases ho with
  | @returned _ _ _ m' hl _ =>
    cases hl with
    | cons h1 t =>
      cases t
      cases h1
      exact ⟨m', rfl⟩

/-- **`loopRotate_refinesLoc` is not vacuous**: `loop rotate` reorders `loopL`'s blocks, and the
output returns 7 under `runLoc`, as `loopL` does. -/
theorem loopRotateLoc_witness :
    ∃ out, loopRotatePass loopLPassEnv loopL = .ok out ∧ out.func.blocks = #[1, 3, 2, 5, 4] ∧
      ∃ fuel m, runLoc Env.p1 out.tables out.func (clampArgs 3) {} fuel = .returned [.i64 7] m := by
  obtain ⟨m, hm⟩ := returnsInt_iff.1 loopL_run
  have hf := loopL_pass_facts
  cases hc : loopRotate loopLPassEnv loopL with
  | error e => rw [hc] at hf; cases hf
  | ok g =>
    rw [hc] at hf
    simp only [Except.toOption, Option.map_some, Option.some.injEq] at hf
    have hp : loopRotatePass loopLPassEnv loopL = .ok { func := g, tables := clampLTabs } := by
      simp only [loopRotatePass, Pass.ofFunc, hc]
      rfl
    refine ⟨_, hp, hf, ?_⟩
    exact refinesLoc_returned_int (loopRotate_refinesLoc hp) hm

end GoFV.Proof.Witness
