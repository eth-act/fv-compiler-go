import GoFV.Proof.Pass.CopyElimPass
import GoFV.Proof.Witness.Early
import GoFV.Proof.Witness.CopyElimRel
import GoFV.Proof.Witness.PhiElim

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witness: copyelim on `clamp`

copyelim accepts `clamp`, input and output pass `check`, `clamp` is in both fragments (all by
kernel evaluation), so `copyelim_refines` applies: the output returns `clamp(5, 0, 10) = 5`.

`copyFrag_stable_witness`: `CopyFrag`'s shape condition exempts `Stable` phis. `pzBool` is
`pz` with its `Phi` `v6` typed `bool` while its arguments are `int64`s (`Const64`, `Add64`):
their shapes differ, but the `Phi` is stable (two distinct non-phi arguments), so `copyFrag`
holds. `retypeInto_other_witness`: a copy of an `int64` from an argument of shape `other` (whose
values are all `poison`) is accepted (`retypeIntoB`), although the shapes differ.

`copyelim_emptyArg_witness`: `clampE` is `clamp` with an unused `Arg {x} [0]` of type
`struct {}`. phielim turns it into `Empty`; it is `EmptyOK` (shape `empty`, offset 0), so
`emptyFragB` holds and `copyelim_refines` applies although `f` has a zero-size value.
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

/-- `clampTabs` with type 29 = `struct {}`. -/
def clampETabs : Tables :=
  { clampTabs with
    types := clampTabs.types.set! 29 (some (mkT .STRUCT (some 0) "struct {}" (.struct #[]))) }

/-- `clamp` with `v25 = Arg <struct {}> {x} [0]` (unused) in the entry block. -/
def clampE : Func :=
  { clamp with
    vidLast := 25
    valueTab := clampValues.push (some (mkV 25 .Arg 29 (some 3) p0 0 #[] 1))
    blockTab := clampBlocks.set! 1 (some (mkB 1 .If (pos 2 22 7 0) #[12] #[⟨3, 0⟩, ⟨2, 0⟩] #[]
      #[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 25])) }

def clampECheckEnv : CheckEnv := { clampCheckEnv with tabs := clampETabs }

theorem clampE_checks :
    (check clampECheckEnv clampE).toBool = true ∧
    ((copyelim clampETabs clampE).toOption.map (fun g => (check clampECheckEnv g).toBool)) =
      some true ∧
    isOkTrue (zeroSizeAggregate clampETabs 29) = true ∧
    emptyFragB clampETabs clampE = true ∧ copyFrag clampETabs clampE = true ∧
    returnsInt (run Env.p1 clampETabs clampE (clampArgs 5) {} 3) 5 = true := by
  decide +kernel

theorem copyelim_emptyArg_witness :
    ∃ out, copyelimPass { clampPassEnv "early phielim and copyelim" with tables := clampETabs }
        clampE = .ok out ∧
      ∃ fuel m, run Env.p1 out.tables out.func (clampArgs 5) {} fuel = .returned [.i64 5] m := by
  obtain ⟨h1, h2, -, h3, h4, h5⟩ := clampE_checks
  obtain ⟨m, hm⟩ := returnsInt_iff.1 h5
  have hf : check clampECheckEnv clampE = .ok () := by
    revert h1; cases check clampECheckEnv clampE <;> simp [Except.toBool]
  cases hc : copyelim clampETabs clampE with
  | error e => rw [hc] at h2; cases h2
  | ok g =>
    rw [hc] at h2
    have hg : check clampECheckEnv g = .ok () := by
      simp only [Except.toOption, Option.map_some, Option.some.injEq] at h2
      revert h2; cases check clampECheckEnv g <;> simp [Except.toBool]
    have hp : copyelimPass { clampPassEnv "early phielim and copyelim" with tables := clampETabs }
        clampE = .ok { func := g, tables := clampETabs } := by
      simp only [copyelimPass, Pass.ofFunc]
      rw [hc]; rfl
    refine ⟨_, hp, ?_⟩
    exact Refines.returned_int
      (copyelim_refines hp hf (ce' := clampECheckEnv) hg (copyFrag_sound h4) (emptyFrag_of h3)) hm

theorem retypeInto_other_witness :
    retypeIntoB .other (.int .w64) = true ∧ retypeEqB .other (.int .w64) = false := by
  decide +kernel

end GoFV.Proof.Witness
