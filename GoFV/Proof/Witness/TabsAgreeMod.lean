import GoFV.Proof.TabsAgreeMod
import GoFV.Proof.Witness.TabsAgree
import GoFV.Proof.Witness.CopyElimRel

/-!
# Witness: `run_tabsAgreeMod` on `clamp` with an extra frame temporary

`clampTabs` with a new non-addrtaken `PAUTO` variable (what `decompose builtin` adds for the
pieces of a split slot) gives every run of `clamp` an extra frame block `Blk.temp 0 7`;
`tabsAgree` rejects it (`clampTabs_pauto`), `tabsAgreeMod` accepts it (`decide +kernel`).
`Env.p1` cannot tell whether unreachable temporaries exist (its contracts panic on the memory
they are given: `p1_tempOblivious`), and `clamp`'s integer arguments on the empty memory hold no
pointer (`clampArgs_initAvoids`), so `refinesFrom_of_tabsAgreeMod` turns the reflexive
refinement in the extended tables into one from the input tables, and `clamp(5, 0, 10)` still
returns 5 in the extended tables (`clamp_run_pauto`).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof

/-- `clampTabs` with a new `PAUTO` variable `x.ptr` (aux 7, `int`, address not taken). -/
def clampTabsPauto : Tables :=
  { clampTabs with auxes := clampTabs.auxes.push (some (paramName "x.ptr" .PAUTO 0)) }

theorem clampTabsPauto_agreeMod :
    GoFV.Opt.tabsAgreeMod clampTabs clampTabsPauto clamp = true ∧
      GoFV.Opt.tabsAgree clampTabs clampTabsPauto clamp = false ∧
      clampTabsPauto.forgeable 7 = false := by
  decide +kernel

/-- **`Env.p1` cannot tell whether unreachable frame temporaries exist**: its contracts panic on
the memory they are given. -/
theorem p1_tempOblivious : Env.p1.TempOblivious := by
  intro name c hc X _ args clo m m' _ _ hm hmm
  unfold Env.p1 at hc
  simp only at hc
  split at hc
  all_goals first
    | (cases hc; exact ⟨rfl, trivial, hm, hmm⟩)
    | cases hc

theorem clampArgs_initAvoids (x : BitVec 64) : InitAvoids Env.p1 (clampArgs x) {} := by
  intro a n
  refine ⟨fun v hv => ?_, fun _ _ h => ?_, rfl, fun _ h => ?_⟩
  · simp only [clampArgs, List.mem_cons, List.mem_nil_iff, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> trivial
  · simp at h
  · simp [Env.p1] at h

/-- `clamp`'s refinement from the input tables to the tables with the extra temporary. -/
theorem clamp_refinesFrom_pauto :
    RefinesFrom (fun env args mem => env.TempOblivious ∧ InitAvoids env args mem)
      clampTabsPauto clamp clampTabs clamp :=
  refinesFrom_of_tabsAgreeMod (fun _ _ _ h => h) clampTabsPauto_agreeMod.1 clamp_check
    (Refines.from _ (Refines.refl clampTabsPauto clamp))

/-- **Non-vacuity of `run_tabsAgreeMod`/`refinesFrom_of_tabsAgreeMod`**: `clamp(5, 0, 10)`
returns 5 in the tables with the extra frame temporary, by the refinement. -/
theorem clamp_run_pauto :
    ∃ fuel m, run Env.p1 clampTabsPauto clamp (clampArgs 5) {} fuel = .returned [.i64 5] m := by
  have hs := clamp_run.1
  generalize ho : run Env.p1 clampTabs clamp (clampArgs 5) {} 3 = o at hs
  rcases (returnsInt_iff (o := o) (v := 5)).1 hs with ⟨m, rfl⟩
  obtain ⟨fuel', h⟩ := clamp_refinesFrom_pauto Env.p1 (clampArgs 5) {}
    ⟨p1_tempOblivious, clampArgs_initAvoids 5⟩ 3 (by rw [ho]; trivial)
  rw [ho] at h
  refine ⟨fuel', ?_⟩
  generalize run Env.p1 clampTabsPauto clamp (clampArgs 5) {} fuel' = o' at h ⊢
  cases h with
  | @returned _ rs' _ m' hl _ =>
    cases hl with
    | cons h1 t =>
      cases t
      cases h1
      exact ⟨m', rfl⟩

end GoFV.Proof.Witness
