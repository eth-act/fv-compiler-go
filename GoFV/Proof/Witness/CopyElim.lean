import GoFV.Proof.Pass.CopyElimPass
import GoFV.Proof.Witness.Early
import GoFV.Proof.Witness.CopyElimRel
import GoFV.Proof.Witness.PhiElim

/-!
# Non-vacuity witness: copyelim on `clamp`

copyelim accepts `clamp`, input and output pass `check`, `clamp` is in both fragments (all by
kernel evaluation), so `copyelim_refines` applies: the output returns `clamp(5, 0, 10) = 5`.

`copyFrag_stable_witness`: `CopyFrag`'s shape condition exempts `Stable` phis. `pzBool` is
`pz` with its `Phi` `v6` typed `bool` while its arguments are `int64`s (`Const64`, `Add64`):
their shapes differ, but the `Phi` is stable (two distinct non-phi arguments), so `copyFrag`
holds.
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof GoFV.Proof.CopyElim

def clampCheckEnv : CheckEnv :=
  { tabs := clampTabs, typs := #[("Uintptr", 15), ("Int", 2), ("Mem", 28), ("Bool", 3)] }

theorem clamp_checks :
    (check clampCheckEnv clamp).toBool = true ∧
    ((copyelim clampTabs clamp).toOption.map (fun g => (check clampCheckEnv g).toBool)) = some true ∧
    emptyFragB clampTabs clamp = true ∧ copyFrag clampTabs clamp = true := by
  decide +kernel

theorem copyelim_witness :
    ∃ out, copyelimPass (clampPassEnv "early phielim and copyelim") clamp = .ok out ∧
      ∃ fuel m, run Env.p1 out.tables out.func (clampArgs 5) {} fuel = .returned [.i64 5] m := by
  obtain ⟨h1, h2, h3, h4⟩ := clamp_checks
  obtain ⟨m, hm⟩ := clamp_run5
  have hf : check clampCheckEnv clamp = .ok () := by
    revert h1; cases check clampCheckEnv clamp <;> simp [Except.toBool]
  cases hc : copyelim clampTabs clamp with
  | error e => rw [hc] at h2; cases h2
  | ok g =>
    rw [hc] at h2
    have hg : check clampCheckEnv g = .ok () := by
      simp only [Except.toOption, Option.map_some, Option.some.injEq] at h2
      revert h2; cases check clampCheckEnv g <;> simp [Except.toBool]
    have hp : copyelimPass (clampPassEnv "early phielim and copyelim") clamp =
        .ok { func := g, tables := clampTabs } := by
      simp only [copyelimPass, Pass.ofFunc, clampPassEnv]
      rw [hc]; rfl
    refine ⟨_, hp, ?_⟩
    obtain ⟨fuel, m', h⟩ := Refines.returned_int
      (copyelim_refines hp hf (ce' := clampCheckEnv) hg (copyFrag_sound h4) (emptyFrag_of h3))
      hm
    exact ⟨fuel, m', h⟩

/-- `pz` with the `Phi` `v6` (arguments `v3`, `v5 : int64`) typed `bool`. -/
def pzBool : Func :=
  { pz with valueTab := peValues.set! 6 (some (mkVi 6 .Phi 6 0 p0 1 #[3, 5] 4)) }

theorem copyFrag_stable_witness :
    copyFrag peTabs pzBool = true ∧ (pzBool.value? 6).any (stableB pzBool) = true ∧
    retypeEqB (peTabs.ty 10) (peTabs.ty 6) = false := by
  decide +kernel

end GoFV.Proof.Witness
