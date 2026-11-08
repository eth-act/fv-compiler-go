import GoFV.Proof.Pass.LicmL
import GoFV.Proof.Witness.TightenL

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: loop invariant on a lowered loop

`licmLoop` (lowered: arm64 `MOVDconst`, `CMP`, `ADD`, `ADDconst`, block kind `LT`), with `x`, `n`
its first two arguments:

```
b1: v50 = MOVDconst [0]; v57 = CMP v50 n; LT v57 -> b2 b5
b2: v51 = Phi v50 v53; v55 = CMP v51 n; LT v55 -> b3 b4      (loop header)
b3: v52 = ADDconst [1] x; v53 = ADD v51 v52; Plain -> b2     (loop body)
b4: Ret v51               b5: Ret v50
```

`loop invariant` (`licmPass`) hoists the invariant `v52` out of the leaf loop: the header's
outside predecessor `b1` is not `Plain`, so it splits the edge `b1 → b2` with a new `Plain`
preheader `b6` and moves `v52` there. Input and output pass `check`, and so does
`unhoist licmLoop out` (the output's CFG with the input's values); the edge split is validated by
`critRelB`, the move by `moveB`; all by kernel evaluation, so `licm_refinesL` applies: the
output returns 12 for `x = 2, n = 10` (`i` steps by 3 from 0) under `runL`, as the input does.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof GoFV.Proof.MoveL

def licmLoopValues : Array (Option Value) :=
  let t := Array.replicate 59 (none : Option Value)
  let t := t.set! 1 (some (mkV 1 .InitMem 28 none p0 2 #[] 1))
  let t := t.set! 8 (some (mkVI 8 .ArgIntReg 2 0 (some 7) (pos 2 22 7 0) 1 #[] 1))
  let t := t.set! 9 (some (mkVI 9 .ArgIntReg 2 1 (some 8) (pos 2 22 7 0) 2 #[] 1))
  let t := t.set! 50 (some (mkVI 50 .ARM64MOVDconst 2 0 none (pos 2 22 7 0) 3 #[] 1))
  let t := t.set! 57 (some (mkV 57 .ARM64CMP 29 none (pos 2 22 7 1) 1 #[50, 9] 1))
  let t := t.set! 51 (some (mkV 51 .Phi 2 none (pos 2 23 3 1) 3 #[50, 53] 2))
  let t := t.set! 55 (some (mkV 55 .ARM64CMP 29 none (pos 2 23 3 1) 1 #[51, 9] 2))
  let t := t.set! 52 (some (mkVI 52 .ARM64ADDconst 2 1 none (pos 2 24 3 1) 1 #[8] 3))
  let t := t.set! 53 (some (mkV 53 .ARM64ADD 2 none (pos 2 24 3 1) 1 #[51, 52] 3))
  let t := t.set! 56 (some (mkV 56 .MakeResult 33 none (pos 2 25 3 1) 1 #[51, 1] 4))
  t.set! 58 (some (mkV 58 .MakeResult 33 none (pos 2 26 3 1) 1 #[50, 1] 5))

def licmLoopBlocks : Array (Option Block) := #[none,
  some (mkB 1 .ARM64LT (pos 2 22 7 0) #[57] #[⟨2, 0⟩, ⟨5, 0⟩] #[] #[1, 8, 9, 50, 57]),
  some (mkB 2 .ARM64LT (pos 2 23 3 0) #[55] #[⟨3, 0⟩, ⟨4, 0⟩] #[⟨1, 0⟩, ⟨3, 0⟩] #[51, 55]),
  some (mkB 3 .Plain (pos 2 24 3 0) #[] #[⟨2, 1⟩] #[⟨2, 0⟩] #[52, 53]),
  some (mkB 4 .Ret (pos 2 25 3 1) #[56] #[] #[⟨2, 1⟩] #[56]),
  some (mkB 5 .Ret (pos 2 26 3 1) #[58] #[] #[⟨1, 1⟩] #[58])]

/-- A counting loop with an invariant step `x + 1`. -/
def licmLoop : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 58
  bidLast := 5
  blocks := #[1, 2, 3, 4, 5]
  blockTab := licmLoopBlocks
  valueTab := licmLoopValues
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := {}

def licmLoopPassEnv : PassEnv := { clampTLPassEnv with passName := "loop invariant" }

def licmLoopArgs : List Val := [.i64 2, .i64 10, .i64 10]

/-- The kernel-evaluated facts: `licmLoop` passes `check` and returns 12 for `x = 2, n = 10`
under `runL`; licm's output and `unhoist licmLoop out` pass `check`, `critRelB` and `moveB` accept,
and the output lists the hoisted `v52` in the new preheader `b6`. -/
theorem licmLoop_facts :
    (check clampTLCheckEnv licmLoop).toBool = true ∧
    returnsInt (runL Env.p1 clampLTabs licmLoop licmLoopArgs {} 12) 12 = true ∧
    ((licmPass licmLoopPassEnv licmLoop).toOption.map fun o =>
      decide ((check clampTLCheckEnv o.func).toBool = true ∧
        (check clampTLCheckEnv (unhoist licmLoop o.func)).toBool = true ∧
        Crit.critRelB licmLoop (unhoist licmLoop o.func) = true ∧
        moveB (unhoist licmLoop o.func) o.func = true ∧
        (o.func.block? 6).map (·.values) = some #[52])) = some true := by
  decide +kernel

/-- **`loop invariant` on lowered `licmLoop`**: it hoists `v52` into a new preheader, and its output
returns 12 under `runL` (`licm_refinesL`). -/
theorem licmL_witness :
    ∃ out, licmPass licmLoopPassEnv licmLoop = .ok out ∧
      (out.func.block? 6).map (·.values) = some #[52] ∧
      ∃ fuel m, runL Env.p1 out.tables out.func licmLoopArgs {} fuel = .returned [.i64 12] m := by
  obtain ⟨h1, h2, h3⟩ := licmLoop_facts
  obtain ⟨m, hm⟩ := returnsInt_iff.1 h2
  have hf : check clampTLCheckEnv licmLoop = .ok () := by
    revert h1; cases check clampTLCheckEnv licmLoop <;> simp [Except.toBool]
  obtain ⟨out, hp, hg, hu, hc, hmv, h6⟩ := ok_of_toOption h3
  have hg' : check clampTLCheckEnv out.func = .ok () := by
    revert hg; cases check clampTLCheckEnv out.func <;> simp [Except.toBool]
  have hu' : check clampTLCheckEnv (unhoist licmLoop out.func) = .ok () := by
    revert hu; cases check clampTLCheckEnv (unhoist licmLoop out.func) <;> simp [Except.toBool]
  exact ⟨out, hp, h6, RefinesL.returned_int (licm_refinesL hp hf hg' hu' hc hmv) hm⟩

end GoFV.Proof.Witness
