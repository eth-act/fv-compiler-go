import GoFV.Opt.ProveCheck.Check

/-!
# Interval arithmetic of prove's validator (issue #24)

`Rng.Mem r x`: the unsigned and signed readings of `x` lie in `r`. Each operation of
`GoFV.Opt.ProveCheck.Rng` keeps a member a member (`mem_norm`, `mem_excl`, `mem_boundBy_*`, …).
The proofs reduce both readings to `toNat` (`reading`: with `H = 2 ^ (n - 1)`, `toInt` is
`toNat` below `H`, `toNat - 2H` from `H` on) and close by `omega`.
-/

namespace GoFV.Proof.ProveCheck

open GoFV.Opt.ProveCheck

/-- The two readings of an `n`-bit integer, `n ≥ 1`, in terms of `H = 2 ^ (n - 1)`. -/
theorem reading {n : Nat} (hn : 1 ≤ n) (x : BitVec n) :
    ∃ H : Nat, 2 ^ n = 2 * H ∧ 2 ^ (n - 1) = H ∧ (2 : Int) ^ n = 2 * (H : Int) ∧
      (2 : Int) ^ (n - 1) = (H : Int) ∧ 1 ≤ H ∧ x.toNat < 2 * H ∧
      x.toInt = if x.toNat < H then (x.toNat : Int) else (x.toNat : Int) - 2 * H := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  refine ⟨2 ^ m, by rw [Nat.pow_succ]; omega, by simp, by rw [Int.pow_succ]; push_cast; omega,
    by simp, Nat.one_le_two_pow, ?_, ?_⟩
  · have := x.isLt; rw [Nat.pow_succ] at this; omega
  · rw [BitVec.toInt_eq_toNat_cond]
    have h2 : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [Nat.pow_succ]; omega
    rw [h2]
    split <;> split <;> first | rfl | omega | (push_cast; rfl)

section

variable {n : Nat} (hn : 1 ≤ n)
include hn

theorem Rng.mem_top (x : BitVec n) : (Rng.top n).Mem x := by
  obtain ⟨H, h1, h2, h3, h4, h5, h6, h7⟩ := reading hn x
  simp only [Rng.top, Rng.Mem, h1, h2, h4]
  split at h7 <;> omega

theorem Rng.mem_ofU {x : BitVec n} {lo hi : Nat} (h1 : lo ≤ x.toNat) (h2 : x.toNat ≤ hi) :
    (Rng.ofU n lo hi).Mem x := by
  obtain ⟨H, h1, h2, h3, h4, h5, h6, h7⟩ := reading hn x
  simp only [Rng.ofU, Rng.Mem, h4]
  split at h7 <;> omega

theorem Rng.mem_ofS {x : BitVec n} {lo hi : Int} (h1 : lo ≤ x.toInt) (h2 : x.toInt ≤ hi) :
    (Rng.ofS n lo hi).Mem x := by
  obtain ⟨H, h1, h2, h3, h4, h5, h6, h7⟩ := reading hn x
  simp only [Rng.ofS, Rng.Mem, h1]
  omega

theorem Rng.mem_nonneg {x : BitVec n} (h : 0 ≤ x.toInt) : (Rng.nonneg n).Mem x := by
  obtain ⟨H, h1, h2, h3, h4, h5, h6, h7⟩ := reading hn x
  refine Rng.mem_ofS hn h ?_
  rw [h4]; split at h7 <;> omega

theorem Rng.mem_norm {r : Rng} {x : BitVec n} (h : r.Mem x) : (r.norm n).Mem x := by
  obtain ⟨H, h1, h2, h3, h4, h5, h6, h7⟩ := reading hn x
  have m1 : ∀ r : Rng, r.Mem x → (Rng.norm1 n r).Mem x := fun r ⟨a1, a2, a3, a4⟩ => by
    unfold Rng.norm1; rw [h2]; split
    · simp only [Rng.Mem]; split at h7 <;> omega
    · exact ⟨a1, a2, a3, a4⟩
  have m2 : ∀ r : Rng, r.Mem x → (Rng.norm2 n r).Mem x := fun r ⟨a1, a2, a3, a4⟩ => by
    unfold Rng.norm2; rw [h2, h3]; split
    · simp only [Rng.Mem]; split at h7 <;> omega
    · exact ⟨a1, a2, a3, a4⟩
  have m3 : ∀ r : Rng, r.Mem x → (Rng.norm3 r).Mem x := fun r ⟨a1, a2, a3, a4⟩ => by
    unfold Rng.norm3; split
    · simp only [Rng.Mem]; split at h7 <;> omega
    · exact ⟨a1, a2, a3, a4⟩
  have m4 : ∀ r : Rng, r.Mem x → (Rng.norm4 n r).Mem x := fun r ⟨a1, a2, a3, a4⟩ => by
    unfold Rng.norm4; rw [h3]; split
    · simp only [Rng.Mem]; split at h7 <;> omega
    · exact ⟨a1, a2, a3, a4⟩
  exact m4 _ (m3 _ (m2 _ (m1 _ h)))

end

theorem Rng.mem_meet {n : Nat} {a b : Rng} {x : BitVec n} (ha : a.Mem x) (hb : b.Mem x) :
    (a.meet b).Mem x := by
  obtain ⟨a1, a2, a3, a4⟩ := ha
  obtain ⟨b1, b2, b3, b4⟩ := hb
  simp only [Rng.meet, Rng.Mem]
  omega

theorem Rng.mem_point {n : Nat} (x : BitVec n) : (Rng.point x).Mem x := by
  simp [Rng.point, Rng.Mem]

theorem Rng.not_empty {n : Nat} {r : Rng} {x : BitVec n} (h : r.Mem x) : r.empty = false := by
  obtain ⟨a1, a2, a3, a4⟩ := h
  simp only [Rng.empty, Bool.or_eq_false_iff, decide_eq_false_iff_not]
  omega

theorem Rng.mem_of_sub {n : Nat} {ra r : Rng} {x : BitVec n} (hs : ra.sub r = true)
    (h : ra.Mem x) : r.Mem x := by
  have he := not_empty h
  obtain ⟨a1, a2, a3, a4⟩ := h
  simp only [Rng.sub, he, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hs
  simp only [Rng.Mem]
  omega

theorem Rng.mem_excl {n : Nat} {r p : Rng} {x y : BitVec n} (h : r.Mem x) (hp : p.Mem y)
    (hne : x ≠ y) : (r.excl p).Mem x := by
  have hu : x.toNat ≠ y.toNat := fun e => hne (BitVec.eq_of_toNat_eq e)
  have hs : x.toInt ≠ y.toInt := fun e => hne (BitVec.toInt_inj.1 e)
  obtain ⟨a1, a2, a3, a4⟩ := h
  obtain ⟨b1, b2, b3, b4⟩ := hp
  dsimp only [Rng.excl]
  split
  · rename_i hpt
    simp only [Bool.and_eq_true, beq_iff_eq] at hpt
    (repeat' split) <;> simp only [Rng.Mem, beq_iff_eq, Bool.not_eq_true, beq_eq_false_iff_ne,
      ne_eq] at * <;> omega
  · exact ⟨a1, a2, a3, a4⟩

/-- `x ⋈ y` for an order relation: signed (`toInt`) or unsigned (`toNat`), strict or not. -/
def OrdHolds {n : Nat} (signed strict : Bool) (x y : BitVec n) : Prop :=
  if signed then (if strict then x.toInt < y.toInt else x.toInt ≤ y.toInt)
  else (if strict then x.toNat < y.toNat else x.toNat ≤ y.toNat)

theorem mem_boundBy_lt {n : Nat} (hn : 1 ≤ n) {s st : Bool} {ry : Rng} {x y : BitVec n}
    (hy : ry.Mem y) (h : OrdHolds s st x y) : (boundBy n s st true ry).Mem x := by
  obtain ⟨H, h1, h2, h3, h4, h5, h6, h7⟩ := reading hn x
  obtain ⟨b1, b2, b3, b4⟩ := hy
  have hx3 := BitVec.le_toInt x
  have hx4 := (BitVec.toInt_lt (x := x))
  rw [h4] at hx3 hx4
  unfold boundBy OrdHolds at *
  cases s <;> cases st <;> simp only [Rng.ofS, Rng.ofU, Rng.Mem, h1, h2, h4, ite_true,
    Bool.false_eq_true, ite_false] at h ⊢ <;> push_cast <;> omega

theorem mem_boundBy_gt {n : Nat} (hn : 1 ≤ n) {s st : Bool} {ry : Rng} {x y : BitVec n}
    (hy : ry.Mem y) (h : OrdHolds s st y x) : (boundBy n s st false ry).Mem x := by
  obtain ⟨H, h1, h2, h3, h4, h5, h6, h7⟩ := reading hn x
  obtain ⟨b1, b2, b3, b4⟩ := hy
  have hx3 := BitVec.le_toInt x
  have hx4 := (BitVec.toInt_lt (x := x))
  rw [h4] at hx3 hx4
  unfold boundBy OrdHolds at *
  cases s <;> cases st <;> simp only [Rng.ofS, Rng.ofU, Rng.Mem, h1, h2, h4, ite_true,
    Bool.false_eq_true, ite_false] at h ⊢ <;> push_cast <;> omega

end GoFV.Proof.ProveCheck
