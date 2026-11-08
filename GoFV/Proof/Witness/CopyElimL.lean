import GoFV.Proof.Pass.CopyElimPassL
import GoFV.Proof.Witness.LowCong
import GoFV.Proof.Witness.CopyElim

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: copyelim on lowered `clamp` with a copy

`clampCL` is lowered `clamp` (`clampL`, arm64 `CMP`s and `GT`/`LT` blocks) with
`v25 = Copy <int> v8` (a copy of the argument `x`) read by the `ARM64CMP` `v22` and the
`MakeResult` `v24`. `late phielim and copyelim` (`copyelimPass`) accepts it and makes `v22` and
`v24` read `v8`; input and output pass `check`, are lowered, and are in the fragments
(`CopyFrag`, `EmptyFrag`, `CopyLFrag`), all by kernel evaluation, so `copyelim_refinesL`
applies: the output returns `clamp(5, 0, 10) = 5` under `runL`, as the input does.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof GoFV.Proof.CopyElim

/-- The values of `clampCL`: `clampL`'s, with `v25 = Copy v8` read by `v22` and `v24`. -/
def clampCLValues : Array (Option Value) :=
  let t := clampLValues.push none
  let t := t.set! 8 (some (mkVI 8 .ArgIntReg 2 0 (some 7) (pos 2 22 7 0) 2 #[] 1))
  let t := t.set! 25 (some (mkV 25 .Copy 2 none (pos 2 22 7 0) 2 #[8] 1))
  let t := t.set! 22 (some (mkV 22 .ARM64CMP 29 none (pos 2 22 7 1) 1 #[9, 25] 1))
  t.set! 24 (some (mkV 24 .MakeResult 33 none (pos 2 28 2 1) 1 #[25, 1] 4))

/-- The blocks of `clampCL`: `v25` listed in the entry block. -/
def clampCLBlocks : Array (Option Block) :=
  clampLBlocks.set! 1
    (some (mkB 1 .ARM64GT (pos 2 22 7 0) #[22] #[⟨3, 0⟩, ⟨2, 0⟩] #[] #[1, 8, 9, 10, 25, 22]))

/-- Lowered `clamp` with a copy of `x`. -/
def clampCL : Func :=
  { clampL with vidLast := 25, valueTab := clampCLValues, blockTab := clampCLBlocks }

def clampCLCheckEnv : CheckEnv := { clampCheckEnv with tabs := clampLTabs }

/-- The kernel-evaluated facts: `clampCL` passes `check`, is lowered and in the fragments, returns
`clamp(5, 0, 10) = 5` under `runL`; copyelim's output passes `check`, is lowered, the pair is in
`CopyLFrag`, and the output's `v22`, `v24` read `v8` (the input's read `v25`). -/
theorem clampCL_facts :
    (check clampCLCheckEnv clampCL).toBool = true ∧ clampCL.lowered = true ∧
    emptyFragB clampLTabs clampCL = true ∧ copyFrag clampLTabs clampCL = true ∧
    returnsInt (runL Env.p1 clampLTabs clampCL (clampArgs 5) {} 3) 5 = true ∧
    ((copyelimPass (clampLPassEnv "late phielim and copyelim") clampCL).toOption.map fun o =>
      decide ((check clampCLCheckEnv o.func).toBool = true ∧ o.func.lowered = true ∧
        copyLFragB clampLTabs clampCL o.func = true ∧
        (o.func.value? 22).map (·.args) = some #[9, 8] ∧
        (o.func.value? 24).map (·.args) = some #[8, 1] ∧
        (clampCL.value? 22).map (·.args) = some #[9, 25])) = some true := by
  decide +kernel

/-- **`late phielim and copyelim` on lowered `clampCL`**: it rewrites the copy's readers, and its
output returns `clamp(5, 0, 10) = 5` under `runL` (`copyelim_refinesL`). -/
theorem copyelimL_witness :
    ∃ out, copyelimPass (clampLPassEnv "late phielim and copyelim") clampCL = .ok out ∧
      (out.func.value? 22).map (·.args) = some #[9, 8] ∧
      ∃ fuel m, runL Env.p1 out.tables out.func (clampArgs 5) {} fuel = .returned [.i64 5] m := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := clampCL_facts
  obtain ⟨m, hm⟩ := returnsInt_iff.1 h5
  have hf : check clampCLCheckEnv clampCL = .ok () := by
    revert h1; cases check clampCLCheckEnv clampCL <;> simp [Except.toBool]
  obtain ⟨out, hp, hg, hl, hL, h22, -, -⟩ := ok_of_toOption h6
  have hg' : check clampCLCheckEnv out.func = .ok () := by
    revert hg; cases check clampCLCheckEnv out.func <;> simp [Except.toBool]
  refine ⟨out, hp, h22, ?_⟩
  exact RefinesL.returned_int
    (copyelim_refinesL hp hf hg' (copyFrag_sound h4) (emptyFrag_of h3) (hl.trans h2.symm)
      (copyLFrag_of hL)) hm

end GoFV.Proof.Witness
