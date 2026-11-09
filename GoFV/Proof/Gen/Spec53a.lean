import GoFV.Gen.Check53a
import GoFV.Proof.Gen.Spec50

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `vkind53a` accepted (`GoFV/Gen/Check53a.lean`)

`VK53a`: the value of G53's group A, `LoweredMove [n] dst src mem`, and what it emits: nothing when
`dst` and `src` are in the same register, else `moveTail`'s chunks (`movePats`) when they lie inside
the `n` bytes and cover them (`vkind53a_spec`, `moveCovers_spec`). `vkind53a` is `none` off
`op53a` (`vkind53a_none`), and every `VK53a` value's op is `op53a`'s (`vk53a_op`).
-/

namespace GoFV.Gen.Check

open GoFV.SSA GoFV.SSA.Sem GoFV.Asm

/-- What `vkind53a` accepted, and what it emits. -/
inductive VK53a (lc : LocCtx) (v : Value) : VKind2 → Prop
  /-- `LoweredMove [n] dst src mem`: no code if `dst` and `src` share their register, else
  `moveTail`'s chunks covering the `n` bytes. -/
  | move {rd rs : Int} :
      v.op = .ARM64LoweredMove → v.args.size = 3 → memTy (lc.ty v.id) = true →
      lc.home v.id = none → argObj lc v 0 = .ok (64, rd) → argObj lc v 1 = .ok (64, rs) →
      memArg lc v 2 = .ok () → 16 ≤ v.auxInt.toInt → rd ≠ r25A → rs ≠ r25A →
      moveCovers v.auxInt.toInt.toNat (moveOffs v.auxInt.toInt.toNat) = true →
      VK53a lc v (.progs (if rd == rs then [] else
        (moveOffs v.auxInt.toInt.toNat).flatMap (movePats rs rd)))

/-- What `moveKind` accepted: no temporary, and `VK53a`'s `move`. -/
theorem moveKind_spec {lc : LocCtx} {v : Value} {kd : VKind2}
    (hop : v.op = .ARM64LoweredMove) (h : moveKind lc v = .ok kd) :
    (lc.temps[v.id]?).join = none ∧ VK53a lc v kd := by
  unfold moveKind at h
  obtain ⟨ht, h1⟩ := ex_guard h
  simp only [beq_iff_eq] at ht
  refine ⟨ht, ?_⟩
  obtain ⟨hsh, h2⟩ := ex_guard h1
  simp only [Bool.and_eq_true, beq_iff_eq] at hsh
  obtain ⟨⟨cd, rd⟩, hdo, h3⟩ := ex_bind_eq_ok h2
  obtain ⟨⟨cs, rs⟩, hso, h4⟩ := ex_bind_eq_ok h3
  obtain ⟨⟨⟩, hma, h5⟩ := ex_bind_eq_ok h4
  obtain ⟨hw, h6⟩ := ex_guard h5
  obtain ⟨hcov, h7⟩ := ex_guard h6
  simp only [ex_pure, Except.ok.injEq] at h7
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne, ne_eq] at hw
  obtain ⟨⟨⟨⟨rfl, rfl⟩, h16⟩, hrd⟩, hrs⟩ := hw
  rw [← h7]
  exact .move hop hsh.1.1 hsh.1.2 hsh.2 hdo hso hma h16 hrd hrs hcov

/-- What `vkind53a` accepted: no temporary, and `VK53a`. -/
theorem vkind53a_spec {lc : LocCtx} {v : Value} {kd : VKind2}
    (h : vkind53a lc v = some (.ok kd)) : (lc.temps[v.id]?).join = none ∧ VK53a lc v kd := by
  unfold vkind53a at h
  split at h
  next hc =>
    simp only [Option.some.injEq] at h
    exact moveKind_spec (by simpa using hc) h
  next => cases h

/-- Off the op of G53's group A, `vkind53a` is `none`. -/
theorem vkind53a_none {lc : LocCtx} {v : Value} (h : op53a v.op = false) :
    vkind53a lc v = none := by
  simp only [op53a] at h
  simp only [vkind53a, h, Bool.false_eq_true, ↓reduceIte]

/-- A value `VK53a` accepted has the op of G53's group A. -/
theorem vk53a_op {lc : LocCtx} {v : Value} {kd : VKind2} (h : VK53a lc v kd) :
    op53a v.op = true := by
  cases h with
  | move hop => rw [hop]; rfl

/-- What `moveCovers` decided: every chunk lies inside the `n` bytes, and every byte is covered by
a chunk. -/
theorem moveCovers_spec {n : Nat} {cs : List (Nat × Nat)} (h : moveCovers n cs = true) :
    (∀ c ∈ cs, c.2 + moveW c.1 ≤ n) ∧
      ∀ j, j < n → ∃ c ∈ cs, c.2 ≤ j ∧ j < c.2 + moveW c.1 := by
  simp only [moveCovers, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, List.mem_range,
    List.any_eq_true] at h
  refine ⟨fun c hc => h.1 c hc, fun j hj => ?_⟩
  obtain ⟨c, hc, hcj⟩ := h.2 j hj
  exact ⟨c, hc, hcj⟩

end GoFV.Gen.Check
