import GoFV.Proof.CongL
import GoFV.Proof.CheckFacts
import GoFV.Opt.CheckLower
import GoFV.Opt.Layout
import GoFV.Opt.LikelyAdjust

/-!
# Lowered passes that `runL` cannot see (#385)

`checkLower` (a check; the function is unchanged on success) and `addressing modes` (the
identity on arm64) return their input. `layout`
replaces `f.Blocks` and sets `f.laidout`; `likelyadjust` sets `Likely` of blocks whose
prediction is unknown and fills the CFG caches. None of this is read by `runL` (`eraseFL`,
`runL_congr`), so each output refines its input under `runL`, with no hypothesis on the input.
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.Opt GoFV.Proof.CheckFacts

/-- **`checkLower` refines its input** (`runL`): on success the function is unchanged. -/
theorem checkLower_refinesL {penv : PassEnv} {f : Func} {out : PassOut}
    (h : checkLowerPass penv f = .ok out) : RefinesL out.tables out.func penv.tables f := by
  simp only [checkLowerPass, Pass.ofFunc, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i g hg
    cases h
    split at hg
    · cases hg
    · split at hg
      · cases hg; exact RefinesL.refl _ _
      · cases hg

/-- **`addressing modes` returns its input** on arm64 (`addressingmodes.go:11-18`: the arch
switch has no arm64 case), with the input's tables. -/
theorem addressingModes_eq {penv : PassEnv} {f : Func} {out : PassOut}
    (h : addressingModesPass penv f = .ok out) : out.func = f ∧ out.tables = penv.tables := by
  simp only [addressingModesPass, Pass.ofFunc, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i g hg
    cases h
    split at hg
    · cases hg; exact ⟨rfl, rfl⟩
    · cases hg

/-- **`addressing modes` refines its input** (`runL`): it is the identity. -/
theorem addressingModes_refinesL {penv : PassEnv} {f : Func} {out : PassOut}
    (h : addressingModesPass penv f = .ok out) : RefinesL out.tables out.func penv.tables f := by
  obtain ⟨h1, h2⟩ := addressingModes_eq h
  rw [h1, h2]; exact RefinesL.refl _ _

theorem layout_eraseFL {f g : Func} (h : layout f = .ok g) : eraseFL g = eraseFL f := by
  simp only [layout, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · cases h; rfl

/-- **`layout` refines its input** (`runL`). -/
theorem layout_refinesL {penv : PassEnv} {f : Func} {out : PassOut}
    (h : layoutPass penv f = .ok out) : RefinesL out.tables out.func penv.tables f := by
  simp only [layoutPass, Pass.ofFunc, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i g hg
    cases h
    exact RefinesL.of_eraseFL (layout_eraseFL hg)

theorem likelyadjust_eraseFL {f g : Func} (h : likelyadjust f = .ok g) : eraseFL g = eraseFL f := by
  unfold likelyadjust at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i r hr
    split at h
    · cases h
    · rename_i st hst
      cases h
      have hc0 := (CacheOnly.postorder f).trans (CacheOnly.loopnest hr)
      refine forIn_array_inv (fun _ (s : Array Int × Array Int × Func) => eraseFL s.2.2 = eraseFL f)
        hc0.eraseFL ?_ hst
      intro pre x s s' hI hb
      revert s' hb
      repeat' apply ok_ite
      all_goals intro s' hb
      all_goals first
        | (cases hb; exact ⟨_, rfl, hI⟩)
        | (split at hb
           · cases hb
           · cases hb; first
              | exact ⟨_, rfl, hI⟩
              | (refine ⟨_, rfl, ?_⟩; dsimp only; rw [eraseFL_modB]; exact hI; intro; rfl))

/-- **`likelyadjust` refines its input** (`runL`). -/
theorem likelyadjust_refinesL {penv : PassEnv} {f : Func} {out : PassOut}
    (h : likelyadjustPass penv f = .ok out) : RefinesL out.tables out.func penv.tables f := by
  simp only [likelyadjustPass, Pass.ofFunc, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i g hg
    cases h
    exact RefinesL.of_eraseFL (likelyadjust_eraseFL hg)

end GoFV.Proof
