import GoFV.Proof.RefineLoc
import GoFV.Proof.Witness.ClampL

open scoped GoFV.SSA.Sem.Fixed

/-!
# Witness function: `clamp` before and after `regalloc`

`examples/arith/main/clamp,1.ssa` of the corpus `gofv-corpus/2aae1000ea1d/quick-v5/plain`,
sections 53 (`flagalloc`, the input of `regalloc`: scheduled, L1) and 54 (`regalloc`, L2),
transcribed by hand on top of `clampL` (`GoFV.Proof.Witness.ClampL`):

```
b1: v8 v9 v10 (ArgIntReg x lo hi) v1 (InitMem) v22 = CMP v9 v8;  GT v22 -> b3 b2
b2: v14 = CMP v10 v8;  LT v14 -> b5 b4
b3: v13 = Copy v9;  v15 = MakeResult v13 v1;  Ret      (regalloc: v13 is new, v15 reads it)
b4: v24 = MakeResult v8 v1;  Ret
b5: v18 = Copy v10; v21 = MakeResult v18 v1;  Ret      (regalloc: v18 is new, v21 reads it)
homes (regalloc): v8 R0, v9 R1, v10 R2, v13 R0, v18 R0, v15 v21 v24 [] (no result registers)
```

`regalloc` moves the returned value into `R0`, the ABI's first result register.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem

/-- The blocks of section 53 (scheduled: `b1`'s values in `schedule`'s order). -/
def clampSBlocks : Array (Option Block) := #[none,
  some (mkB 1 .ARM64GT (pos 2 22 7 0) #[22] #[⟨3, 0⟩, ⟨2, 0⟩] #[] #[8, 9, 10, 1, 22]),
  some (mkB 2 .ARM64LT (pos 2 25 7 0) #[14] #[⟨5, 0⟩, ⟨4, 0⟩] #[⟨1, 1⟩] #[14]),
  some (mkB 3 .Ret (pos 2 23 3 1) #[15] #[] #[⟨1, 0⟩] #[15]),
  some (mkB 4 .Ret (pos 2 28 2 1) #[24] #[] #[⟨2, 1⟩] #[24]),
  some (mkB 5 .Ret (pos 2 26 3 1) #[21] #[] #[⟨2, 0⟩] #[21])]

/-- `clamp` after `flagalloc` (section 53, L1). -/
def clampS : Func := { clampL with blockTab := clampSBlocks }

/-- The values of section 54: the two copies `v13`, `v18`, and the `MakeResult`s reading them. -/
def clampRAValues : Array (Option Value) :=
  let t := clampLValues
  let t := t.set! 13 (some (mkV 13 .Copy 2 none (pos 2 23 3 2) 1 #[9] 3))
  let t := t.set! 18 (some (mkV 18 .Copy 2 none (pos 2 26 3 2) 1 #[10] 5))
  let t := t.set! 15 (some (mkV 15 .MakeResult 33 none (pos 2 23 3 1) 1 #[13, 1] 3))
  t.set! 21 (some (mkV 21 .MakeResult 33 none (pos 2 26 3 1) 1 #[18, 1] 5))

/-- The blocks of section 54. -/
def clampRABlocks : Array (Option Block) := #[none,
  some (mkB 1 .ARM64GT (pos 2 22 7 0) #[22] #[⟨3, 0⟩, ⟨2, 0⟩] #[] #[8, 9, 10, 1, 22]),
  some (mkB 2 .ARM64LT (pos 2 25 7 0) #[14] #[⟨5, 0⟩, ⟨4, 0⟩] #[⟨1, 1⟩] #[14]),
  some (mkB 3 .Ret (pos 2 23 3 1) #[15] #[] #[⟨1, 0⟩] #[13, 15]),
  some (mkB 4 .Ret (pos 2 28 2 1) #[24] #[] #[⟨2, 1⟩] #[24]),
  some (mkB 5 .Ret (pos 2 26 3 1) #[21] #[] #[⟨2, 0⟩] #[18, 21])]

/-- `clamp` after `regalloc` (section 54, L2). -/
def clampRA : Func :=
  { clampL with
    blockTab := clampRABlocks
    valueTab := clampRAValues
    freeValues := [2, 3, 4, 5, 6, 7, 11, 12, 16, 17, 19, 20, 23]
    low := { scheduled := true, laidout := true
             regAlloc := some (25, #[(8, .reg 0), (9, .reg 1), (10, .reg 2), (13, .reg 0),
               (15, .results #[]), (18, .reg 0), (21, .results #[]), (24, .results #[])]) } }

/-- Under `runSched` (L1) and `runLoc` (L2): `clamp(5, 0, 10) = 5`, `clamp(-3, 0, 10) = 0`,
`clamp(12, 0, 10) = 10`. -/
theorem clampRA_run :
    returnsInt (runSched Env.p1 clampLTabs clampS (clampArgs 5) {} 3) 5 = true ∧
    returnsInt (runSched Env.p1 clampLTabs clampS (clampArgs (-3)) {} 3) 0 = true ∧
    returnsInt (runSched Env.p1 clampLTabs clampS (clampArgs 12) {} 3) 10 = true ∧
    returnsInt (runLoc Env.p1 clampLTabs clampRA (clampArgs 5) {} 3) 5 = true ∧
    returnsInt (runLoc Env.p1 clampLTabs clampRA (clampArgs (-3)) {} 3) 0 = true ∧
    returnsInt (runLoc Env.p1 clampLTabs clampRA (clampArgs 12) {} 3) 10 = true := by
  decide +kernel

/-- Non-vacuity of `runLoc_mono`/`runLoc_det` and of `RefinesLoc`: a defined `runLoc`. -/
theorem clampRA_runLoc_defined :
    (runLoc Env.p1 clampLTabs clampRA (clampArgs 5) {} 3).Defined := by
  obtain ⟨m, h⟩ := returnsInt_iff.1 clampRA_run.2.2.2.1
  rw [h]; trivial

theorem clampRA_runLoc_det (fuel : Nat) (h : 3 ≤ fuel) :
    runLoc Env.p1 clampLTabs clampRA (clampArgs 5) {} fuel =
      runLoc Env.p1 clampLTabs clampRA (clampArgs 5) {} 3 :=
  runLoc_mono h clampRA_runLoc_defined

theorem clampS_runSched_defined :
    (runSched Env.p1 clampLTabs clampS (clampArgs 5) {} 3).Defined := by
  obtain ⟨m, h⟩ := returnsInt_iff.1 clampRA_run.1
  rw [h]; trivial

/-- `RefinesLoc.refl` on `clampRA` gives a returning run (`RefinesLoc.backward`). -/
theorem clampRA_refinesLoc_witness :
    OutcomeRefines 0 (runLoc Env.p1 clampLTabs clampRA (clampArgs 5) {} 3)
      (runLoc Env.p1 clampLTabs clampRA (clampArgs 5) {} 7) :=
  (RefinesLoc.refl clampLTabs clampRA).backward clampRA_runLoc_defined
    (by rw [clampRA_runLoc_det 7 (by decide)]; exact clampRA_runLoc_defined)

end GoFV.Proof.Witness
