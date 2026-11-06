import GoFV.Proof.Pass.LateLowerL
import GoFV.Proof.Witness.LicmL
import GoFV.Proof.Witness.AddZero
import GoFV.Proof.Witness.LowerTrunc

/-!
# Non-vacuity witness: `late lower` on a lowered loop

`late lower` (`GoFV.Opt.lateLower`) on `llLoop` (`licmLoop` of `GoFV/Proof/Witness/LicmL.lean`
with the rewrite engine's line cache) rewrites its `v50 = MOVDconst [0]` to `ZERO`
(`ARM64latelower.rules:98`) and `lateB` accepts the result, so `lateLower_refinesL` applies: the
output returns 12 for `x = 2, n = 10` under `runL`, as the input does. All facts by kernel
evaluation.

`llx` (`int(int32(g))` with a 32-bit load: `lower` makes it `v4 = MOVWload {g} v2 v1`, `v5 =
MOVWreg v4`) checks a dropped extension: `late lower` turns `v5` into `MOVDnop v4`
(`ARM64latelower.rules:46`, `(MOVWreg x:(MOVWload _ _)) => (MOVDreg x)`, then line 91), `lateB`
accepts, and the result returns `-5` on `g` holding `2^32 - 5`, as the lowered input does.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof GoFV.Proof.LateLowerL

/-- `licmLoop` with an (empty) line cache, which the rewrite engine requires. -/
def llLoop : Func := { licmLoop with cache := { lineStarts := some #[] } }

/-- The pass environment of `late lower` (the export's arm64 configuration). -/
def llLoopPassEnv : PassEnv :=
  { clampTLPassEnv with passName := "late lower", config := azPassEnv.config }

/-- `late lower` makes `llLoop`'s `v50` a `ZERO` and `lateB` accepts. -/
theorem llLoop_lateLower_facts :
    ((lateLower llLoopPassEnv llLoop).toOption.map fun o =>
      decide (LateLowerCheck.lateB llLoopPassEnv.tables o.tables llLoop o.func = true ∧
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

/-- `int(int32(g))` with a 32-bit load (`trc` with `v4 = Load <int32>`, no `Trunc64to32`), the
input of `lower`. -/
def llxFunc : Func :=
  { trcFunc with
    vidLast := 6
    blockTab := #[none, some (mkB 1 .Ret p0 #[6] #[] #[] #[1, 2, 3, 4, 5, 6])]
    valueTab := #[none,
      some (mkV 1 .InitMem 28 none p0 2 #[] 1),
      some (mkV 2 .SB 4 none p0 1 #[] 1),
      some (mkV 3 .Addr 3 (some 4) p0 1 #[2] 1),
      some (mkV 4 .Load 5 none p0 1 #[3, 1] 1),
      some (mkV 5 .SignExt32to64 2 none p0 1 #[4] 1),
      some (mkV 6 .MakeResult 33 none p0 1 #[5, 1] 1)] }

/-- The pass environment of `late lower` on a result of `lower` with tables `T`. -/
def llxPassEnv (T : Tables) : PassEnv := { llLoopPassEnv with tables := T }

/-- By kernel evaluation: `lower` makes `llx`'s `v5` a `MOVWreg` and the result returns `-5` under
`runL`; `late lower` makes `v5` a `MOVDnop` and `lateB` accepts. -/
theorem llx_lateLower_facts :
    ((lowerChecked trcPassEnv llxFunc).toOption.map fun (o : PassOut) =>
      decide (returnsInt (runL Env.p1 o.tables o.func [] trcMem 1) (-5) = true ∧
        (o.func.value? 5).map (·.op) = some .ARM64MOVWreg ∧
        ((lateLower (llxPassEnv o.tables) o.func).toOption.map fun (o' : PassOut) =>
          decide (LateLowerCheck.lateB o.tables o'.tables o.func o'.func = true ∧
            (o'.func.value? 5).map (·.op) = some .ARM64MOVDnop)) = some true)) = some true := by
  decide +kernel

/-- **`lateLower_refinesL` on a dropped extension**: `late lower` turns the `MOVWreg` of a
`MOVWload` in `lower`'s result for `llx` into `MOVDnop`, and its output returns `-5` under
`runL`. -/
theorem lateLowerExt_witness :
    ∃ o out, lowerChecked trcPassEnv llxFunc = .ok o ∧ lateLower (llxPassEnv o.tables) o.func = .ok out ∧
      (o.func.value? 5).map (·.op) = some .ARM64MOVWreg ∧
      (out.func.value? 5).map (·.op) = some .ARM64MOVDnop ∧
      ∃ fuel m, runL Env.p1 out.tables out.func [] trcMem fuel = .returned [.i64 (-5)] m := by
  obtain ⟨o, ho, hr, h5, hl⟩ := ok_of_toOption llx_lateLower_facts
  obtain ⟨out, hp, hv, hz⟩ := ok_of_toOption hl
  obtain ⟨m, hm⟩ := returnsInt_iff.1 hr
  exact ⟨o, out, ho, hp, h5, hz, RefinesL.returned_int (lateLower_refinesL hp hv) hm⟩

end GoFV.Proof.Witness
