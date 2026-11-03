import GoFV.Proof.CongLoc
import GoFV.Opt.LoopRotate

/-!
# `loop rotate` refines its input under `runLoc`

`loopRotate` (`GoFV.Opt.loopRotate`, #411) changes only `f.Blocks` (the block order), the
blocks' `Hotness` and, if `f.loopnest` had to build it, the loop-nest cache
(`loopRotate_shape`). `runLoc` reads none of these (block order is not semantic before Phase 3's
fallthrough): the output has the input's `eraseFL`, homes and temporary registers, so it has the
same `runLoc`s (`runLoc_congr`). No hypothesis is needed.
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt

/-- `loopRotate`'s output is its input (with other caches) with another block order and
hotness. -/
theorem loopRotate_shape {penv : PassEnv} {f g : Func} (h : loopRotate penv f = .ok g) :
    ∃ f1, CacheOnly f f1 ∧ eraseFL g = eraseFL f1 ∧ g.low.regAlloc = f1.low.regAlloc ∧
      g.low.tempRegs = f1.low.tempRegs := by
  unfold loopRotate at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i r hr
    obtain ⟨nest, f1⟩ := r
    have hc := CacheOnly.loopnest hr
    dsimp only at h
    split at h
    · cases h
      exact ⟨_, hc, rfl, rfl, rfl⟩
    · repeat (split at h <;> try (cases h; done))
      all_goals (cases h; exact ⟨_, hc, rfl, rfl, rfl⟩)

/-- **`loop rotate` refines its input under `runLoc`.** -/
theorem loopRotate_refinesLoc {penv : PassEnv} {f : Func} {out : PassOut}
    (h : loopRotatePass penv f = .ok out) : RefinesLoc out.tables out.func penv.tables f := by
  simp only [loopRotatePass, Pass.ofFunc, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i g hg
    cases h
    obtain ⟨f1, hc, he, hra, htr⟩ := loopRotate_shape hg
    obtain ⟨c, rfl⟩ := hc
    exact RefinesLoc.of_eraseFL he hra htr

end GoFV.Proof
