import GoFV.Proof.TabsAgreeModL
import GoFV.Proof.Witness.ClampRA
import GoFV.Proof.Witness.TabsAgreeMod
import GoFV.Proof.Witness.DAE

/-!
# Witness: `runSched_tabsAgreeModL` on `clamp` with a new spill slot

`clampLTabs` with a new non-addrtaken `PAUTO` variable (what `regalloc`'s `stackalloc` adds for a
spill slot, `f.NewLocal`) gives every `runSched` of the scheduled `clampS` (the input of
`regalloc`) an extra frame block; `tabsAgreeL` rejects the tables (`clampSpill_agree`),
`tabsAgreeModL` accepts them (`decide +kernel`). `Env.p1` cannot tell whether unreachable
temporaries exist and keeps frames safe, and `clamp`'s integer arguments on the empty memory hold
no pointer, so `runSched_tabsAgreeModL` relates the runs in the two tables: `clamp(5, 0, 10)` still
returns 5 in the extended tables (`clampS_run_spill`).
-/

namespace GoFV.Proof.Witness

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof

/-- `clampLTabs` with a new `PAUTO` variable `autotmp_0` (`int`, address not taken). -/
def clampLTabsSpill : Tables :=
  { clampLTabs with auxes := clampLTabs.auxes.push (some (paramName "autotmp_0" .PAUTO 0)) }

theorem clampSpill_agree :
    GoFV.Opt.tabsAgreeModL clampLTabs clampLTabsSpill clampS = true ∧
      GoFV.Opt.LowerCheck.tabsAgreeL clampLTabs clampLTabsSpill clampS = false := by
  decide +kernel

/-- **Non-vacuity of `runSched_tabsAgreeModL`**: `clamp(5, 0, 10)` returns 5 under `runSched` in
the tables with the new spill slot, by the theorem. -/
theorem clampS_run_spill :
    ∃ fuel m, runSched Env.p1 clampLTabsSpill clampS (clampArgs 5) {} fuel = .returned [.i64 5] m := by
  have hs := clampRA_run.1
  generalize ho : runSched Env.p1 clampLTabs clampS (clampArgs 5) {} 3 = o at hs
  rcases (returnsInt_iff (o := o) (v := 5)).1 hs with ⟨m, rfl⟩
  have h := runSched_tabsAgreeModL clampSpill_agree.1 p1_tempOblivious p1_frameSafe
    (clampArgs_initAvoids 5) (by rw [ho]; trivial)
  rw [ho] at h
  refine ⟨3, ?_⟩
  generalize runSched Env.p1 clampLTabsSpill clampS (clampArgs 5) {} 3 = o' at h ⊢
  cases h with
  | @returned _ rs' _ m' hl _ =>
    cases hl with
    | cons h1 t =>
      cases t
      cases h1
      exact ⟨m', rfl⟩

end GoFV.Proof.Witness
