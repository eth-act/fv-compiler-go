import GoFV.Proof.Gen.G32
import GoFV.Gen.Check31

variable [GoFV.SSA.Sem.Addrs]

/-!
# The values G31's upper-bit table keeps its entries across are G3's (`docs/plans/proofs3.md` §4)

`vk32_vk3`: a value of G32's kinds (`VK32`) that `keep31` accepts is one of G3's (`VK3`). G31's
table keeps the entries of the registers a value does not write only across `keep31` values, and
G3's kinds are the ones whose register effects G1–G3 describe; this lets G31's proof reuse G3's
step for them.

`keep31_ops` reads `keep31` as the disjunction of its ops (a `MOVDload`/`MOVDstore` without
symbol). Each `VKn` (`n` from 32 down to 4) is a `VK(n-1)` through its `g(n-1)` constructor or
one of the slice's new kinds; every new kind names an op (`v.op = .X`, `f v.op = some …`,
`pbOp v.op = true`, `(Cond.ofOp v.op).isSome = true`) outside `keep31`'s (`refute31`), except
G6's frame-variable accesses (`VK6.var`), whose `MOVDload`/`MOVDstore` carry a symbol
(`FrameVarOK.aux`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check

/-- The ops of `keepOp31`. -/
private theorem keepOp31_ops {o : Op} (h : keepOp31 o = true) :
    o = .Phi ∨ o = .ARM64ZERO ∨ o = .InlMark ∨ o = .Copy ∨ o = .MakeResult ∨
      o = .ARM64MOVDconst ∨ o = .ARM64ADD ∨ o = .ARM64SUB ∨ o = .ARM64ADDconst ∨
      o = .ARM64SUBconst ∨ o = .ARM64CMP ∨ o = .ARM64CMPconst ∨ o = .ARM64CMPW ∨
      o = .ARM64CMPWconst := by
  unfold keepOp31 at h
  split at h <;> first | (exact absurd h Bool.false_ne_true) | simp

/-- The values `keep31` accepts: `keepOp31`'s ops, or `MOVDload`/`MOVDstore` without symbol. -/
private theorem keep31_ops {v : Value} (h : keep31 v = true) :
    v.op = .Phi ∨ v.op = .ARM64ZERO ∨ v.op = .InlMark ∨ v.op = .Copy ∨ v.op = .MakeResult ∨
      v.op = .ARM64MOVDconst ∨ v.op = .ARM64ADD ∨ v.op = .ARM64SUB ∨ v.op = .ARM64ADDconst ∨
      v.op = .ARM64SUBconst ∨ v.op = .ARM64CMP ∨ v.op = .ARM64CMPconst ∨ v.op = .ARM64CMPW ∨
      v.op = .ARM64CMPWconst ∨
      ((v.op = .ARM64MOVDload ∨ v.op = .ARM64MOVDstore) ∧ v.aux = none) := by
  simp only [keep31, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    Option.isNone_iff_eq_none] at h
  rcases h with h | h
  · rcases keepOp31_ops h with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      simp only [h, true_or, or_true]
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
      (.inr h)))))))))))))

/-- Refutes `h'`, a hypothesis naming an op (`v.op = .X`, `f v.op = some …`, …) outside
`keep31`'s, against `hk : keep31 v = true`. -/
local macro "refute31" hk:ident h':ident : tactic => `(tactic|
  (rcases keep31_ops $hk with h | h | h | h | h | h | h | h | h | h | h | h | h | h | ⟨h | h, -⟩ <;>
    (rw [h] at $h':ident; first | cases $h':ident | simp [Cond.ofOp] at $h':ident)))

variable {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2}

private theorem vk4_vk3 (h : VK4 lc g v kd) (hk : keep31 v = true) : VK3 lc g v kd := by
  cases h with
  | g3 _ _ _ _ h => exact h
  | ldp h' => refute31 hk h'
  | stp h' => refute31 hk h'
  | sel h' =>
    rcases h' with ⟨h', -⟩ | ⟨h', -⟩
    · refute31 hk h'
    · refute31 hk h'

private theorem vk5_vk4 (h : VK5 lc g v kd) (hk : keep31 v = true) : VK4 lc g v kd := by
  cases h with
  | g4 _ h => exact h
  | mark h' => refute31 hk h'

private theorem vk6_vk5 (h : VK6 lc g v kd) (hk : keep31 v = true) : VK5 lc g v kd := by
  cases h with
  | g5 h => exact h
  | var hf hv =>
    rcases keep31_ops hk with h | h | h | h | h | h | h | h | h | h | h | h | h | h | ⟨-, ha⟩
    all_goals first
      | (rw [hf.aux] at ha; cases ha)
      | (cases hv with
        | addr h' => rw [h] at h'; cases h'
        | load h' => rw [h] at h'; simp [loadOp?, narrowLoad?] at h'
        | store h' => rw [h] at h'; simp [storeOp?, narrowStore?] at h'
        | ldp h' => rw [h] at h'; cases h'
        | stp h' => rw [h] at h'; cases h')

private theorem vk7_vk6 (h : VK7 lc g v kd) (hk : keep31 v = true) : VK6 lc g v kd := by
  cases h with
  | g6 _ h => exact h
  | nil h' => refute31 hk h'

private theorem vk8_vk7 (h : VK8 lc g v kd) (hk : keep31 v = true) : VK7 lc g v kd := by
  cases h with
  | g7 h => exact h
  | wb h' => refute31 hk h'
  | sel0 h' => refute31 hk h'
  | sel1 h' => refute31 hk h'

private theorem vk9_vk8 (h : VK9 lc g v kd) (hk : keep31 v = true) : VK8 lc g v kd := by
  cases h with
  | g8 _ h => exact h
  | call h' => refute31 hk h'

private theorem vk10_vk9 (h : VK10 lc g v kd) (hk : keep31 v = true) : VK9 lc g v kd := by
  cases h with
  | g9 h => exact h
  | icall h' => refute31 hk h'
  | selMem h' => refute31 hk h'
  | selReg h' => refute31 hk h'

private theorem vk11_vk10 (h : VK11 lc g v kd) (hk : keep31 v = true) : VK10 lc g v kd := by
  cases h with
  | g10 h => exact h
  | clo h' => refute31 hk h'

private theorem vk12_vk11 (h : VK12 lc g v kd) (hk : keep31 v = true) : VK11 lc g v kd := by
  cases h with
  | g11 h => exact h
  | conv h' => refute31 hk h'

private theorem vk13_vk12 (h : VK13 lc g v kd) (hk : keep31 v = true) : VK12 lc g v kd := by
  cases h with
  | g12 h => exact h
  | zero h' => refute31 hk h'

private theorem vk14_vk13 (h : VK14 lc g v kd) (hk : keep31 v = true) : VK13 lc g v kd := by
  cases h with
  | g13 h => exact h
  | idx h' => refute31 hk h'

private theorem vk15_vk14 (h : VK15 lc g v kd) (hk : keep31 v = true) : VK14 lc g v kd := by
  cases h with
  | g14 _ h => exact h
  | call h' => refute31 hk h'

private theorem vk16_vk15 (h : VK16 lc g v kd) (hk : keep31 v = true) : VK15 lc g v kd := by
  cases h with
  | g15 h => exact h
  | addSh h' => refute31 hk h'

private theorem vk17_vk16 (h : VK17 lc g v kd) (hk : keep31 v = true) : VK16 lc g v kd := by
  cases h with
  | g16 h => exact h
  | getG h' => refute31 hk h'

private theorem vk18_vk17 (h : VK18 lc g v kd) (hk : keep31 v = true) : VK17 lc g v kd := by
  cases h with
  | g17 h => exact h
  | stIdx h' => refute31 hk h'

private theorem vk19_vk18 (h : VK19 lc g v kd) (hk : keep31 v = true) : VK18 lc g v kd := by
  cases h with
  | g18 _ h => exact h
  | pb h' => refute31 hk h'

private theorem vk20_vk19 (h : VK20 lc g v kd) (hk : keep31 v = true) : VK19 lc g v kd := by
  cases h with
  | g19 _ h => exact h
  | nop h' => refute31 hk h'

private theorem vk21_vk20 (h : VK21 lc g v kd) (hk : keep31 v = true) : VK20 lc g v kd := by
  cases h with
  | g20 _ h => exact h
  | regSame h' => refute31 hk h'
  | regMov h' => refute31 hk h'

private theorem vk22_vk21 (h : VK22 lc g v kd) (hk : keep31 v = true) : VK21 lc g v kd := by
  cases h with
  | g21 _ h => exact h
  | ldp h' => refute31 hk h'
  | stp h' => refute31 hk h'

private theorem vk23_vk22 (h : VK23 lc g v kd) (hk : keep31 v = true) : VK22 lc g v kd := by
  cases h with
  | g22 _ h => exact h
  | cset h' => refute31 hk h'

private theorem vk24_vk23 (h : VK24 lc g v kd) (hk : keep31 v = true) : VK23 lc g v kd := by
  cases h with
  | g23 _ h => exact h
  | sp h' => refute31 hk h'

private theorem vk25_vk24 (h : VK25 lc g v kd) (hk : keep31 v = true) : VK24 lc g v kd := by
  cases h with
  | g24 _ _ h => exact h
  | csel h' => refute31 hk h'
  | csel0 h' => refute31 hk h'
  | tst h' => refute31 hk h'
  | tstw h' => refute31 hk h'

private theorem vk27_vk25 (h : VK27 lc g v kd) (hk : keep31 v = true) : VK25 lc g v kd := by
  cases h with
  | g25 _ h => exact h
  | logSh h' => refute31 hk h'

private theorem vk28_vk27 (h : VK28 lc g v kd) (hk : keep31 v = true) : VK27 lc g v kd := by
  cases h with
  | g27 _ h => exact h
  | memEq h' => refute31 hk h'

private theorem vk32_vk28 (h : VK32 lc g v kd) (hk : keep31 v = true) : VK28 lc g v kd := by
  cases h with
  | g28 _ _ _ _ _ h => exact h
  | bin h' => refute31 hk h'
  | binK h' => refute31 hk h'
  | un h' => refute31 hk h'
  | csinc h' => refute31 hk h'
  | stlr h' => refute31 hk h'

/-- A value of G32's kinds that G31's table keeps its entries across (`keep31`) is G3's. -/
theorem vk32_vk3 {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (hVK : VK32 lc g v kd)
    (hk : keep31 v = true) : VK3 lc g v kd :=
  vk4_vk3 (vk5_vk4 (vk6_vk5 (vk7_vk6 (vk8_vk7 (vk9_vk8 (vk10_vk9 (vk11_vk10 (vk12_vk11
    (vk13_vk12 (vk14_vk13 (vk15_vk14 (vk16_vk15 (vk17_vk16 (vk18_vk17 (vk19_vk18 (vk20_vk19
    (vk21_vk20 (vk22_vk21 (vk23_vk22 (vk24_vk23 (vk25_vk24 (vk27_vk25 (vk28_vk27
    (vk32_vk28 hVK hk) hk) hk) hk) hk) hk) hk) hk) hk) hk) hk) hk) hk) hk) hk) hk) hk) hk) hk) hk)
    hk) hk) hk) hk) hk

end GoFV.Proof.Gen
