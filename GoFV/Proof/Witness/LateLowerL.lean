import GoFV.Proof.Pass.LateLowerL
import GoFV.Proof.Witness.LicmL
import GoFV.Proof.Witness.AddZero

/-!
# Non-vacuity witness: `late lower` on a lowered loop

`late lower` (`GoFV.Opt.lateLower`) on `llLoop` (`licmLoop` of `GoFV/Proof/Witness/LicmL.lean`
with the rewrite engine's line cache) rewrites its `v50 = MOVDconst [0]` to `ZERO`
(`ARM64latelower.rules:98`) and `renameB` accepts the result, so `lateLower_refinesL` applies: the
output returns 12 for `x = 2, n = 10` under `runL`, as the input does. All facts by kernel
evaluation.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof GoFV.Proof.LateLowerL

/-- `licmLoop` with an (empty) line cache, which the rewrite engine requires. -/
def llLoop : Func := { licmLoop with cache := { lineStarts := some #[] } }

/-- The pass environment of `late lower` (the export's arm64 configuration). -/
def llLoopPassEnv : PassEnv :=
  { clampTLPassEnv with passName := "late lower", config := azPassEnv.config }

/-- `late lower` makes `llLoop`'s `v50` a `ZERO` and `renameB` accepts. -/
theorem llLoop_lateLower_facts :
    ((lateLower llLoopPassEnv llLoop).toOption.map fun o =>
      decide (LateLowerCheck.renameB llLoopPassEnv.tables o.tables llLoop o.func = true ∧
        (o.func.value? 50).map (·.op) = some .ARM64ZERO)) = some true := by
  decide +kernel

/-- **`lateLower_refinesL` is not vacuous**: `late lower` turns `llLoop`'s `MOVDconst [0]` into
`ZERO`, and its output returns 12 under `runL` (`llLoop` runs as `licmLoop`, `runL_congr`). -/
theorem lateLowerL_witness :
    ∃ out, lateLower llLoopPassEnv llLoop = .ok out ∧
      (out.func.value? 50).map (·.op) = some .ARM64ZERO ∧
      ∃ fuel m, runL Env.p1 out.tables out.func licmLoopArgs {} fuel = .returned [.i64 12] m := by
  obtain ⟨-, h1, -⟩ := licmLoop_facts
  obtain ⟨m, hm⟩ := returnsInt_iff.1 h1
  have hm' : runL Env.p1 llLoopPassEnv.tables llLoop licmLoopArgs {} 12 = .returned [.i64 12] m := by
    exact (runL_congr (f := llLoop) (g := licmLoop) rfl _ _ _ _ _).trans hm
  obtain ⟨out, hp, hv, hz⟩ := ok_of_toOption llLoop_lateLower_facts
  exact ⟨out, hp, hz, RefinesL.returned_int (lateLower_refinesL hp hv) hm'⟩

end GoFV.Proof.Witness
