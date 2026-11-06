import GoFV.Proof.Pass.FlagAllocL
import GoFV.Proof.Witness.TightenL

/-!
# Non-vacuity witness: flagalloc on lowered `clamp`

`clampTL` (`GoFV.Proof.Witness.TightenL`) is lowered `clamp` with both comparisons in the entry
block, `v22 = CMP lo x` (`b1`'s control) before `v14 = CMP hi x` (`b2`'s control):

```
b1: [v22 = CMP lo x; v14 = CMP hi x] ARM64GT v22 -> b3 b2      b2: ARM64LT v14 -> b5 b4
```

The flags at the end of `b1` are `v14`'s, so `flagalloc` (`flagallocPass`) recomputes `v22` at
the end of `b1` and `v14` in `b2`, redirects both controls to the clones and drops the
originals. Input and output pass `check`, the validator `flagAllocB` accepts the pair (one clone
of a value of the block, one of a value of the dominator `b1`), and the input returns
`clamp(12, 0, 10) = 10` under `runSched` (all by kernel evaluation), so
`flagalloc_refinesSched` gives a returning run of the output (`flagallocL_witness`).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof GoFV.Proof.FlagAllocL

/-- `flagalloc`'s environment: `tighten`'s on `clampTL`. -/
def clampFLPassEnv : PassEnv := { clampTLPassEnv with passName := "flagalloc" }

/-- The kernel-evaluated facts: `clampTL` passes `check` and returns `clamp(12, 0, 10) = 10`
under `runSched`; flagalloc's output passes `check`, `flagAllocB` accepts the pair, the output
drops `v22` and `v14` and lists one new value in each of `b1` and `b2`. -/
theorem clampFL_facts :
    (check clampTLCheckEnv clampTL).toBool = true ∧
    returnsInt (runSched Env.p1 clampLTabs clampTL (clampArgs 12) {} 3) 10 = true ∧
    ((flagallocPass clampFLPassEnv clampTL).toOption.map fun o =>
      decide ((check clampTLCheckEnv o.func).toBool = true ∧
        flagAllocB clampFLPassEnv.tables clampTL o.func = true ∧
        o.func.value? 22 = none ∧ o.func.value? 14 = none ∧
        ((o.func.block? 1).map (·.values.size)) = some 5 ∧
        ((o.func.block? 2).map (·.values.size)) = some 1)) = some true := by
  decide +kernel

/-- **`flagalloc_refinesSched` is not vacuous**: `flagalloc` recomputes both comparisons of
`clampTL` (dropping the originals), and its output returns `clamp(12, 0, 10) = 10` under
`runSched`. -/
theorem flagallocL_witness :
    ∃ out, flagallocPass clampFLPassEnv clampTL = .ok out ∧ out.func.value? 22 = none ∧
      out.func.value? 14 = none ∧
      ∃ fuel m, runSched Env.p1 out.tables out.func (clampArgs 12) {} fuel = .returned [.i64 10] m := by
  obtain ⟨h1, h2, h3⟩ := clampFL_facts
  obtain ⟨m, hm⟩ := returnsInt_iff.1 h2
  have hf : check clampTLCheckEnv clampTL = .ok () := by
    revert h1; cases check clampTLCheckEnv clampTL <;> simp [Except.toBool]
  obtain ⟨out, hp, -, hv, h22, h14, -⟩ := ok_of_toOption h3
  have htabs : clampFLPassEnv.tables = clampLTabs := rfl
  have hr := flagalloc_refinesSched hp hf hv
  rw [htabs] at hr
  exact ⟨out, hp, h22, h14, hr.returned_int hm⟩

end GoFV.Proof.Witness
