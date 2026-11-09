import GoFV.Proof.Pass.PhiTightenL
import GoFV.Proof.Witness.TightenL

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: phi tighten on a lowered function

`phiTL` (lowered: arm64 `MOVDconst`, `CMPconst`, block kind `EQ`), with `x` its first argument:

```
b1: v30 = MOVDconst [7]; v31 = CMPconst [0] x; EQ v31 -> b2 b4
b2: Plain -> b3            b4: Plain -> b3
b3: v32 = Phi v30 x; Ret v32
```

`phi tighten` (`phiTightenPass`) clones the rematerializeable `v30` into the predecessor `b2`
(`v34`) and makes the `Phi` read it; input and output pass `check` and the value-motion
validator `moveB` accepts the pair, all by kernel evaluation, so `phiTighten_refinesL` applies:
the output returns 7 for `x = 0` under `runL`, as the input does.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof GoFV.Proof.MoveL

def phiTLValues : Array (Option Value) :=
  let t := Array.replicate 34 (none : Option Value)
  let t := t.set! 1 (some (mkV 1 .InitMem 28 none p0 1 #[] 1))
  let t := t.set! 8 (some (mkVI 8 .ArgIntReg 2 0 (some 7) (pos 2 22 7 0) 2 #[] 1))
  let t := t.set! 30 (some (mkVI 30 .ARM64MOVDconst 2 7 none (pos 2 22 7 0) 1 #[] 1))
  let t := t.set! 31 (some (mkV 31 .ARM64CMPconst 29 none (pos 2 22 7 1) 1 #[8] 1))
  let t := t.set! 32 (some (mkV 32 .Phi 2 none (pos 2 23 3 1) 1 #[30, 8] 3))
  t.set! 33 (some (mkV 33 .MakeResult 33 none (pos 2 23 3 1) 1 #[32, 1] 3))

def phiTLBlocks : Array (Option Block) := #[none,
  some (mkB 1 .ARM64EQ (pos 2 22 7 0) #[31] #[⟨2, 0⟩, ⟨4, 0⟩] #[] #[1, 8, 30, 31]),
  some (mkB 2 .Plain (pos 2 22 7 0) #[] #[⟨3, 0⟩] #[⟨1, 0⟩] #[]),
  some (mkB 3 .Ret (pos 2 23 3 1) #[33] #[] #[⟨2, 0⟩, ⟨4, 0⟩] #[32, 33]),
  some (mkB 4 .Plain (pos 2 22 7 0) #[] #[⟨3, 1⟩] #[⟨1, 1⟩] #[])]

/-- A `Phi` of a constant and the argument `x`, after critical edges are split. -/
def phiTL : Func where
  entry := 1
  type := 1
  ownAux := some 1
  vidLast := 33
  bidLast := 4
  blocks := #[1, 2, 4, 3]
  blockTab := phiTLBlocks
  valueTab := phiTLValues
  names := #[]
  namedx := #[]
  splits := #[]
  canon := #[]
  consts := #[]
  freeValues := []
  freeBlocks := []
  cache := {}

def phiTLPassEnv : PassEnv := { clampTLPassEnv with passName := "phi tighten" }

/-- The kernel-evaluated facts: `phiTL` passes `check` and returns 7 for `x = 0` under `runL`;
phi tighten's output passes `check`, `moveB` accepts the pair, the clone `v34` is listed in `b2`
and the `Phi` reads it. -/
theorem phiTL_facts :
    (check clampTLCheckEnv phiTL).toBool = true ∧
    returnsInt (runL Env.p1 clampLTabs phiTL (clampArgs 0) {} 4) 7 = true ∧
    ((phiTightenPass phiTLPassEnv phiTL).toOption.map fun o =>
      decide ((check clampTLCheckEnv o.func).toBool = true ∧ moveB phiTL o.func = true ∧
        (o.func.block? 2).map (·.values) = some #[34] ∧
        (o.func.value? 32).map (·.args) = some #[34, 8])) = some true := by
  decide +kernel

/-- **`phi tighten` on lowered `phiTL`**: it clones the constant into `b2` for the `Phi`, and its
output returns 7 for `x = 0` under `runL` (`phiTighten_refinesL`). -/
theorem phiTightenL_witness :
    ∃ out, phiTightenPass phiTLPassEnv phiTL = .ok out ∧
      (out.func.value? 32).map (·.args) = some #[34, 8] ∧
      ∃ fuel m, runL Env.p1 out.tables out.func (clampArgs 0) {} fuel = .returned [.i64 7] m := by
  obtain ⟨h1, h2, h3⟩ := phiTL_facts
  obtain ⟨m, hm⟩ := returnsInt_iff.1 h2
  have hf : check clampTLCheckEnv phiTL = .ok () := by
    revert h1; cases check clampTLCheckEnv phiTL <;> simp [Except.toBool]
  obtain ⟨out, hp, hg, hmv, -, h32⟩ := ok_of_toOption h3
  have hg' : check clampTLCheckEnv out.func = .ok () := by
    revert hg; cases check clampTLCheckEnv out.func <;> simp [Except.toBool]
  exact ⟨out, hp, h32, RefinesL.returned_int (phiTighten_refinesL hp hf hg' hmv) hm⟩

end GoFV.Proof.Witness
