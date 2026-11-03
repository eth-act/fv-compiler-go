import GoFV.Proof.Pass.TightenL
import GoFV.Proof.Witness.LowCong
import GoFV.Proof.Witness.CopyElim

/-!
# Non-vacuity witness: tighten on lowered `clamp`

`clampTL` is lowered `clamp` (`clampL`) with the comparison `v14 = CMP hi x` of the second test
placed in the entry block `b1` instead of `b2`, its only user (`b2`'s control). `tighten`
(`tightenPass`) moves it to `b2`; input and output pass `check`, and the value-motion validator
`moveB` accepts the pair, all by kernel evaluation, so `refinesL_of_move` and `tighten_refinesL`
apply: the output returns `clamp(12, 0, 10) = 10` under `runL` (through `b2`), as the input does.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof GoFV.Proof.MoveL

/-- The values of `clampTL`: `clampL`'s, `v14` in `b1`. -/
def clampTLValues : Array (Option Value) :=
  clampLValues.set! 14 (some (mkV 14 .ARM64CMP 29 none (pos 2 25 7 1) 1 #[10, 8] 1))

/-- The blocks of `clampTL`: `v14` listed in `b1`, `b2` empty. -/
def clampTLBlocks : Array (Option Block) :=
  let t := clampLBlocks.set! 1
    (some (mkB 1 .ARM64GT (pos 2 22 7 0) #[22] #[⟨3, 0⟩, ⟨2, 0⟩] #[] #[1, 8, 9, 10, 22, 14]))
  t.set! 2 (some (mkB 2 .ARM64LT (pos 2 25 7 0) #[14] #[⟨5, 0⟩, ⟨4, 0⟩] #[⟨1, 1⟩] #[]))

/-- Lowered `clamp` with `v14` hoisted to the entry block. -/
def clampTL : Func := { clampL with valueTab := clampTLValues, blockTab := clampTLBlocks }

/-- `tighten`'s environment: `clampL`'s, with the `Mem`, `Flags` and `Void` pseudo-types. -/
def clampTLPassEnv : PassEnv :=
  { clampLPassEnv "tighten" with typs := #[("Mem", 28), ("Flags", 29), ("Void", 30)] }

def clampTLCheckEnv : CheckEnv := { clampCheckEnv with tabs := clampLTabs }

/-- The kernel-evaluated facts: `clampTL` passes `check` and returns `clamp(12, 0, 10) = 10`
under `runL`; tighten's output passes `check`, `moveB` accepts the pair, and the output lists
`v14` in `b2` (the input in `b1`). -/
theorem clampTL_facts :
    (check clampTLCheckEnv clampTL).toBool = true ∧
    returnsInt (runL Env.p1 clampLTabs clampTL (clampArgs 12) {} 3) 10 = true ∧
    ((tightenPass clampTLPassEnv clampTL).toOption.map fun o =>
      decide ((check clampTLCheckEnv o.func).toBool = true ∧ moveB clampTL o.func = true ∧
        (o.func.block? 2).map (·.values) = some #[14] ∧
        (clampTL.block? 2).map (·.values) = some #[])) = some true := by
  decide +kernel

/-- **`tighten` on lowered `clampTL`**: it moves `v14` into `b2`, and its output returns
`clamp(12, 0, 10) = 10` under `runL` (`tighten_refinesL`, through `refinesL_of_move`). -/
theorem tightenL_witness :
    ∃ out, tightenPass clampTLPassEnv clampTL = .ok out ∧
      (out.func.block? 2).map (·.values) = some #[14] ∧
      ∃ fuel m, runL Env.p1 out.tables out.func (clampArgs 12) {} fuel = .returned [.i64 10] m := by
  obtain ⟨h1, h2, h3⟩ := clampTL_facts
  obtain ⟨m, hm⟩ := returnsInt_iff.1 h2
  have hf : check clampTLCheckEnv clampTL = .ok () := by
    revert h1; cases check clampTLCheckEnv clampTL <;> simp [Except.toBool]
  obtain ⟨out, hp, hg, hmv, hb2, -⟩ := ok_of_toOption h3
  have hg' : check clampTLCheckEnv out.func = .ok () := by
    revert hg; cases check clampTLCheckEnv out.func <;> simp [Except.toBool]
  exact ⟨out, hp, hb2, RefinesL.returned_int (tighten_refinesL hp hf hg' hmv) hm⟩

end GoFV.Proof.Witness
