import GoFV.SSA.Sem.Val

/-!
# The fixed address assignment of #156 (`Addrs.fixed`)

The semantics takes its concrete addresses as a parameter (`Addrs`, `docs/plans/proofs3.md` §8).
`Addrs.fixed` is the assignment every executable runs (`gofv-ssa-opt`, `sem-difftest`, the
witnesses; `open scoped GoFV.SSA.Sem.Fixed`): `Blk.fixedBase?`, `Ptr.fixedOfAddr`, and the caller's
`SP` of activation `a` just above its frame region, `2^62 + (a + 1)·2^42`. Its admissibility is
the round-trip arithmetic of #156 (`Ptr.fixedOfAddr_addr`, `Ptr.fixedOfAddr_add`).

`Ptr.convertible_fixed`: under `Addrs.fixed`, `Ptr.convertible` is #607's bounds condition
(`Ptr.fixedConvertible`), so the semantics at this instance is the one before the parameter.
-/

namespace GoFV.SSA.Sem

/-- The pointer at an address has that address (`Blk.fixedBase?`). -/
theorem Ptr.fixedOfAddr_addr (x : BitVec 64) :
    (Blk.fixedBase? (Ptr.fixedOfAddr x).blk).map
      (fun b => BitVec.ofNat 64 b + (Ptr.fixedOfAddr x).off) = some x := by
  have hx := x.isLt
  unfold Ptr.fixedOfAddr
  dsimp only
  split
  · simp [Blk.fixedBase?]
  · split
    · rename_i h1 h2
      simp only [Blk.fixedBase?, Option.map_some, Option.some.injEq]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      have : (x.toNat / 2 ^ 40 - 1 + 1) * 2 ^ 40 + x.toNat % 2 ^ 40 = x.toNat := by omega
      omega
    · rename_i h1 h2
      split
      · rename_i hk
        simp only [beq_iff_eq] at hk
        simp only [Blk.fixedBase?, Option.map_some, Option.some.injEq]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        omega
      · simp only [Blk.fixedBase?, Option.map_some, Option.some.injEq]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        omega

/-- The pointer at an address lies inside its block's window. -/
theorem Ptr.fixedOfAddr_inWindow (x : BitVec 64) : (Ptr.fixedOfAddr x).inWindow = true := by
  have hx := x.isLt
  unfold Ptr.fixedOfAddr; dsimp only
  split
  · simp only [Ptr.inWindow, Blk.window?, decide_eq_true_eq]; assumption
  split
  · simp only [Ptr.inWindow, Blk.window?, decide_eq_true_eq, BitVec.toNat_ofNat]; omega
  split <;> (simp only [Ptr.inWindow, Blk.window?, decide_eq_true_eq, BitVec.toNat_ofNat]; omega)

/-- The addresses from `2^62` up are frame blocks (no frame temporary). -/
theorem Ptr.fixedOfAddr_high (x : BitVec 64) (h : 2 ^ 62 ≤ x.toNat) :
    ∃ a, (Ptr.fixedOfAddr x).blk = .outargs a ∨ ∃ k, (Ptr.fixedOfAddr x).blk = .local a k := by
  unfold Ptr.fixedOfAddr
  simp only [show ¬ x.toNat < 2 ^ 40 by omega, show ¬ x.toNat < 2 ^ 62 by omega, ite_false]
  split
  · exact ⟨_, .inl rfl⟩
  · exact ⟨_, .inr ⟨_, rfl⟩⟩

/-- Pointer arithmetic on an address, inside the window of the pointer at it, is that pointer's
arithmetic. -/
theorem Ptr.fixedOfAddr_add {x k : BitVec 64}
    (h : ((Ptr.fixedOfAddr x).add k).inWindow = true) :
    Ptr.fixedOfAddr (x + k) = (Ptr.fixedOfAddr x).add k := by
  have hx := x.isLt
  have hk := k.isLt
  have hs : (x + k).toNat = (x.toNat + k.toNat) % 2 ^ 64 := BitVec.toNat_add x k
  by_cases h1 : x.toNat < 2 ^ 40
  · have e : Ptr.fixedOfAddr x = ⟨.nil, x⟩ := by simp [Ptr.fixedOfAddr, h1]
    rw [e] at h ⊢
    simp only [Ptr.add, Ptr.inWindow, Blk.window?] at h
    unfold Ptr.fixedOfAddr
    rw [if_pos (of_decide_eq_true h)]; rfl
  by_cases h2 : x.toNat < 2 ^ 62
  · have e : Ptr.fixedOfAddr x =
        ⟨.heap (x.toNat / 2 ^ 40 - 1), BitVec.ofNat 64 (x.toNat % 2 ^ 40)⟩ := by
      simp [Ptr.fixedOfAddr, h1, h2]
    rw [e] at h ⊢
    simp only [Ptr.add, Ptr.inWindow, Blk.window?, decide_eq_true_eq, BitVec.toNat_add,
      BitVec.toNat_ofNat] at h
    simp only [Ptr.fixedOfAddr, hs, Ptr.add, show ¬ (x.toNat + k.toNat) % 2 ^ 64 < 2 ^ 40 by omega,
      show (x.toNat + k.toNat) % 2 ^ 64 < 2 ^ 62 by omega, ite_false, ite_true,
      show (x.toNat + k.toNat) % 2 ^ 64 / 2 ^ 40 = x.toNat / 2 ^ 40 by omega, Ptr.mk.injEq, true_and]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  obtain ⟨r, hr⟩ : ∃ r, x.toNat = 2 ^ 62 + r := ⟨x.toNat - 2 ^ 62, by omega⟩
  have hr' : x.toNat - 2 ^ 62 = r := by omega
  by_cases h3 : r % 2 ^ 42 / 2 ^ 24 = 0
  · have e : Ptr.fixedOfAddr x = ⟨.outargs (r / 2 ^ 42), BitVec.ofNat 64 (r % 2 ^ 24)⟩ := by
      simp only [Ptr.fixedOfAddr, h1, h2, ite_false, hr', h3, beq_self_eq_true, ite_true]
    rw [e] at h ⊢
    simp only [Ptr.add, Ptr.inWindow, Blk.window?, decide_eq_true_eq, BitVec.toNat_add,
      BitVec.toNat_ofNat] at h
    simp only [Ptr.fixedOfAddr, hs, Ptr.add, show ¬ (x.toNat + k.toNat) % 2 ^ 64 < 2 ^ 40 by omega,
      show ¬ (x.toNat + k.toNat) % 2 ^ 64 < 2 ^ 62 by omega, ite_false,
      show ((x.toNat + k.toNat) % 2 ^ 64 - 2 ^ 62) % 2 ^ 42 / 2 ^ 24 = 0 by omega,
      show ((x.toNat + k.toNat) % 2 ^ 64 - 2 ^ 62) / 2 ^ 42 = r / 2 ^ 42 by omega,
      beq_self_eq_true, ite_true, Ptr.mk.injEq, true_and]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · have e : Ptr.fixedOfAddr x =
        ⟨.local (r / 2 ^ 42) (r % 2 ^ 42 / 2 ^ 24), BitVec.ofNat 64 (r % 2 ^ 24)⟩ := by
      simp only [Ptr.fixedOfAddr, h1, h2, ite_false, hr', beq_iff_eq, h3]
    rw [e] at h ⊢
    simp only [Ptr.add, Ptr.inWindow, Blk.window?, decide_eq_true_eq, BitVec.toNat_add,
      BitVec.toNat_ofNat] at h
    simp only [Ptr.fixedOfAddr, hs, Ptr.add, show ¬ (x.toNat + k.toNat) % 2 ^ 64 < 2 ^ 40 by omega,
      show ¬ (x.toNat + k.toNat) % 2 ^ 64 < 2 ^ 62 by omega, ite_false,
      show ((x.toNat + k.toNat) % 2 ^ 64 - 2 ^ 62) % 2 ^ 42 / 2 ^ 24 = r % 2 ^ 42 / 2 ^ 24 by omega,
      show ((x.toNat + k.toNat) % 2 ^ 64 - 2 ^ 62) / 2 ^ 42 = r / 2 ^ 42 by omega,
      beq_iff_eq, h3, ite_false, Ptr.mk.injEq, true_and]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- **The fixed address assignment of #156**: `nil` at 0, heap objects at `(n + 1)·2^40`, the
frames of activation `a` from `2^62 + a·2^42` (`Blk.fixedBase?`, decoded by `Ptr.fixedOfAddr`),
the caller's `SP` of activation `a` at the end of its frame region. -/
@[reducible] def Addrs.fixed : Addrs where
  baseOf := Blk.fixedBase?
  decode := Ptr.fixedOfAddr
  callerSP act := BitVec.ofNat 64 (2 ^ 62 + (act + 1) * 2 ^ 42)
  baseOf_nil := rfl
  baseOf_heap _ := rfl
  baseOf_global _ := rfl
  baseOf_wbuf := rfl
  baseOf_none b h := by cases b <;> simp_all [Blk.fixedBase?]
  decode_low _ _ := rfl
  decode_addr := Ptr.fixedOfAddr_addr
  decode_inWindow := Ptr.fixedOfAddr_inWindow
  decode_high := Ptr.fixedOfAddr_high
  decode_add _ _ := Ptr.fixedOfAddr_add

@[simp] theorem Addrs.fixed_baseOf : @Addrs.baseOf Addrs.fixed = Blk.fixedBase? := rfl
@[simp] theorem Addrs.fixed_decode : @Addrs.decode Addrs.fixed = Ptr.fixedOfAddr := rfl
@[simp] theorem Addrs.fixed_callerSP (act : Nat) :
    @Addrs.callerSP Addrs.fixed act = BitVec.ofNat 64 (2 ^ 62 + (act + 1) * 2 ^ 42) := rfl

namespace Fixed

/-- The executables' address assignment (`open scoped GoFV.SSA.Sem.Fixed`). -/
scoped instance : Addrs := Addrs.fixed

end Fixed

/-- #607's definition of `Ptr.convertible` (before the addresses became a parameter): inside its
window, its block's number small enough for the address encoding (heap objects below `2^22 - 1`;
frames of the activations below `3·2^20`, whose addresses end below `2^64`), and not a frame
temporary or a global. -/
def Ptr.fixedConvertible (p : Ptr) : Bool :=
  match p.blk with
  | .nil => decide (p.off.toNat < 2 ^ 40)
  | .heap n => decide (n + 1 < 2 ^ 22) && decide (p.off.toNat < 2 ^ 40)
  | .local a k => decide (0 < k) && decide (k < 2 ^ 18) && decide (a < 3 * 2 ^ 20) &&
      decide (p.off.toNat < 2 ^ 24)
  | .outargs a => decide (a < 3 * 2 ^ 20) && decide (p.off.toNat < 2 ^ 24)
  | .temp _ _ | .global _ | .wbuf => false

/-- A pointer of #607's convertible ones is the pointer at its fixed address. -/
private theorem fixedOfAddr_of_fixedConvertible {p : Ptr} (hc : p.fixedConvertible = true) :
    ∃ b, Blk.fixedBase? p.blk = some b ∧ Ptr.fixedOfAddr (BitVec.ofNat 64 b + p.off) = p := by
  obtain ⟨b, off⟩ := p
  have hoff := off.isLt
  cases b with
  | nil =>
    simp only [Ptr.fixedConvertible, decide_eq_true_eq] at hc
    refine ⟨0, rfl, ?_⟩
    have hx : (BitVec.ofNat 64 0 + off).toNat = off.toNat := by simp
    unfold Ptr.fixedOfAddr; simp only [hx, hc, ite_true]
    simp
  | heap n =>
    simp only [Ptr.fixedConvertible, Bool.and_eq_true, decide_eq_true_eq] at hc
    refine ⟨_, rfl, ?_⟩
    have hx : (BitVec.ofNat 64 ((n + 1) * 2 ^ 40) + off).toNat = (n + 1) * 2 ^ 40 + off.toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      have h3 : (n + 1) * 2 ^ 40 + off.toNat < 2 ^ 64 := by omega
      have h0 : (n + 1) * 2 ^ 40 < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h3
      rw [Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt h3]
    unfold Ptr.fixedOfAddr
    simp only [hx]
    have h1 : ¬ ((n + 1) * 2 ^ 40 + off.toNat < 2 ^ 40) := by omega
    have h2 : (n + 1) * 2 ^ 40 + off.toNat < 2 ^ 62 := by omega
    simp only [h1, h2, ite_false, ite_true, Ptr.mk.injEq, Blk.heap.injEq]
    constructor
    · omega
    · apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      have : ((n + 1) * 2 ^ 40 + off.toNat) % 2 ^ 40 = off.toNat := by omega
      have h4 : off.toNat < 2 ^ 64 := hoff
      rw [this]; exact Nat.mod_eq_of_lt h4
  | «local» a k =>
    simp only [Ptr.fixedConvertible, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hk0, hk⟩, ha'⟩, ho⟩ := hc
    refine ⟨_, rfl, ?_⟩
    have hb : 2 ^ 62 + a * 2 ^ 42 + k * 2 ^ 24 + off.toNat < 2 ^ 64 := by omega
    have hx : (BitVec.ofNat 64 (2 ^ 62 + a * 2 ^ 42 + k * 2 ^ 24) + off).toNat =
        2 ^ 62 + a * 2 ^ 42 + k * 2 ^ 24 + off.toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hb), Nat.mod_eq_of_lt hb]
    unfold Ptr.fixedOfAddr
    simp only [hx]
    have h1 : ¬ (2 ^ 62 + a * 2 ^ 42 + k * 2 ^ 24 + off.toNat < 2 ^ 40) := by omega
    have h2 : ¬ (2 ^ 62 + a * 2 ^ 42 + k * 2 ^ 24 + off.toNat < 2 ^ 62) := by omega
    have e1 : (2 ^ 62 + a * 2 ^ 42 + k * 2 ^ 24 + off.toNat - 2 ^ 62) / 2 ^ 42 = a := by omega
    have e2 : (2 ^ 62 + a * 2 ^ 42 + k * 2 ^ 24 + off.toNat - 2 ^ 62) % 2 ^ 42 / 2 ^ 24 = k := by
      omega
    have e3 : (2 ^ 62 + a * 2 ^ 42 + k * 2 ^ 24 + off.toNat - 2 ^ 62) % 2 ^ 24 = off.toNat := by
      omega
    have hk' : (k == 0) = false := by simp; omega
    simp only [h1, h2, ite_false, e1, e2, e3, hk', Bool.false_eq_true]
    simp
  | outargs a =>
    simp only [Ptr.fixedConvertible, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨ha', ho⟩ := hc
    refine ⟨_, rfl, ?_⟩
    have hb : 2 ^ 62 + a * 2 ^ 42 + off.toNat < 2 ^ 64 := by omega
    have hx : (BitVec.ofNat 64 (2 ^ 62 + a * 2 ^ 42) + off).toNat =
        2 ^ 62 + a * 2 ^ 42 + off.toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hb), Nat.mod_eq_of_lt hb]
    unfold Ptr.fixedOfAddr
    simp only [hx]
    have h1 : ¬ (2 ^ 62 + a * 2 ^ 42 + off.toNat < 2 ^ 40) := by omega
    have h2 : ¬ (2 ^ 62 + a * 2 ^ 42 + off.toNat < 2 ^ 62) := by omega
    have e1 : (2 ^ 62 + a * 2 ^ 42 + off.toNat - 2 ^ 62) / 2 ^ 42 = a := by omega
    have e2 : (2 ^ 62 + a * 2 ^ 42 + off.toNat - 2 ^ 62) % 2 ^ 42 / 2 ^ 24 = 0 := by omega
    have e3 : (2 ^ 62 + a * 2 ^ 42 + off.toNat - 2 ^ 62) % 2 ^ 24 = off.toNat := by omega
    simp only [h1, h2, ite_false, e1, e2, e3, beq_self_eq_true, ite_true]
    simp
  | temp _ _ => simp [Ptr.fixedConvertible] at hc
  | global _ => simp [Ptr.fixedConvertible] at hc
  | wbuf => simp [Ptr.fixedConvertible] at hc

/-- Every pointer at a fixed address is one of #607's convertible ones. -/
private theorem fixedConvertible_fixedOfAddr (x : BitVec 64) :
    (Ptr.fixedOfAddr x).fixedConvertible = true := by
  have hx := x.isLt
  unfold Ptr.fixedOfAddr; dsimp only
  split
  · simp only [Ptr.fixedConvertible, decide_eq_true_eq]; assumption
  split
  · simp only [Ptr.fixedConvertible, Bool.and_eq_true, decide_eq_true_eq, BitVec.toNat_ofNat]
    omega
  split
  · simp only [Ptr.fixedConvertible, Bool.and_eq_true, decide_eq_true_eq, BitVec.toNat_ofNat]
    omega
  · rename_i hk
    simp only [beq_iff_eq] at hk
    simp only [Ptr.fixedConvertible, Bool.and_eq_true, decide_eq_true_eq, BitVec.toNat_ofNat]
    omega

/-- **The specialisation**: under `Addrs.fixed`, `Ptr.convertible` (the round trip) is #607's
bounds condition, so every definition of the semantics at `Addrs.fixed` is the one before the
addresses became a parameter. -/
theorem Ptr.convertible_fixed (p : Ptr) :
    @Ptr.convertible Addrs.fixed p = p.fixedConvertible := by
  rw [Bool.eq_iff_iff]
  constructor
  · intro h
    unfold Ptr.convertible at h
    split at h
    · rename_i x hx
      have he : Ptr.fixedOfAddr x = p := by simpa [Ptr.ofAddr, Addrs.fixed] using h
      rw [← he]; exact fixedConvertible_fixedOfAddr x
    · cases h
  · intro h
    obtain ⟨b, hb, he⟩ := fixedOfAddr_of_fixedConvertible h
    have ha : @Ptr.addr? Addrs.fixed p = some (BitVec.ofNat 64 b + p.off) := by
      simp [Ptr.addr?, Blk.base?, Addrs.fixed, hb]
    unfold Ptr.convertible
    rw [ha]
    simpa [Ptr.ofAddr, Addrs.fixed] using he

/-! ## Every assignment: the nil page and the heap are fixed -/

section

variable [Addrs]

@[simp] theorem Blk.base?_nil : Blk.base? .nil = some 0 := Addrs.baseOf_nil

@[simp] theorem Blk.base?_heap (n : Nat) : Blk.base? (.heap n) = some ((n + 1) * 2 ^ 40) :=
  Addrs.baseOf_heap n

@[simp] theorem Blk.base?_global (s : String) : Blk.base? (.global s) = none :=
  Addrs.baseOf_global s

@[simp] theorem Blk.base?_wbuf : Blk.base? .wbuf = none := Addrs.baseOf_wbuf

attribute [simp] Addrs.baseOf_nil Addrs.baseOf_heap Addrs.baseOf_global Addrs.baseOf_wbuf

/-- Only globals and the write-barrier buffer have no address. -/
theorem Blk.base?_eq_none {b : Blk} (h : Blk.base? b = none) : (∃ s, b = .global s) ∨ b = .wbuf :=
  Addrs.baseOf_none b h

/-- Below `2^62` the decoding is #156's (`Addrs.decode_low`). -/
theorem Ptr.ofAddr_low {x : BitVec 64} (h : x.toNat < 2 ^ 62) :
    Ptr.ofAddr x = Ptr.fixedOfAddr x :=
  Addrs.decode_low x h

/-- A nil-page address is the nil block at that offset. -/
theorem Ptr.ofAddr_small {x : BitVec 64} (h : x.toNat < 2 ^ 40) : Ptr.ofAddr x = ⟨.nil, x⟩ := by
  rw [Ptr.ofAddr_low (by omega)]; simp [Ptr.fixedOfAddr, h]

/-- An address decoded into the nil block is the nil block at that address (`nil` sits at 0). -/
theorem Ptr.ofAddr_eq_nil {x : BitVec 64} (h : (Ptr.ofAddr x).blk = .nil) :
    Ptr.ofAddr x = ⟨.nil, x⟩ := by
  have ha : (Ptr.ofAddr x).addr? = some x := Addrs.decode_addr x
  generalize Ptr.ofAddr x = p at h ha ⊢
  obtain ⟨b, o⟩ := p
  simp only at h; subst h
  simp [Ptr.addr?] at ha
  simp [ha]

/-- The nil block and heap blocks convert exactly as under `Addrs.fixed`: their bases are fixed,
and so is the decoding of their addresses (#156's below `2^62`, a frame block from there up). -/
theorem Ptr.convertible_eq_fixed {p : Ptr} (hb : p.blk = .nil ∨ ∃ n, p.blk = .heap n) :
    p.convertible = @Ptr.convertible Addrs.fixed p := by
  have hbase : Blk.base? p.blk = @Blk.base? Addrs.fixed p.blk := by
    rcases hb with hb | ⟨n, hb⟩ <;> rw [hb]
    · exact Addrs.baseOf_nil
    · exact Addrs.baseOf_heap n
  have hnf : ∀ a, p.blk ≠ .outargs a ∧ ∀ k, p.blk ≠ .local a k := by
    intro a; rcases hb with hb | ⟨n, hb⟩ <;> rw [hb] <;> exact ⟨nofun, fun _ => nofun⟩
  have hdec : ∀ x : BitVec 64, (Ptr.ofAddr x == p) = (@Ptr.ofAddr Addrs.fixed x == p) := by
    intro x
    by_cases hx : x.toNat < 2 ^ 62
    · rw [Ptr.ofAddr_low hx]; rfl
    · have hne : ∀ q : Ptr, (∃ a, q.blk = .outargs a ∨ ∃ k, q.blk = .local a k) →
          (q == p) = false := by
        rintro q ⟨a, hq | ⟨k, hq⟩⟩ <;> rw [beq_eq_false_iff_ne] <;> rintro rfl
        · exact (hnf a).1 hq
        · exact (hnf a).2 k hq
      show (Addrs.decode x == p) = (Ptr.fixedOfAddr x == p)
      rw [hne _ (Addrs.decode_high x (by omega)), hne _ (Ptr.fixedOfAddr_high x (by omega))]
  unfold Ptr.convertible Ptr.addr?
  rw [← hbase]
  cases Blk.base? p.blk with
  | none => rfl
  | some b => exact hdec _

@[simp] theorem Ptr.convertible_nil (o : BitVec 64) :
    (⟨.nil, o⟩ : Ptr).convertible = decide (o.toNat < 2 ^ 40) := by
  rw [Ptr.convertible_eq_fixed (.inl rfl), Ptr.convertible_fixed]; rfl

@[simp] theorem Ptr.convertible_heap (n : Nat) (o : BitVec 64) :
    (⟨.heap n, o⟩ : Ptr).convertible = (decide (n + 1 < 2 ^ 22) && decide (o.toNat < 2 ^ 40)) := by
  rw [Ptr.convertible_eq_fixed (.inr ⟨n, rfl⟩), Ptr.convertible_fixed]; rfl

@[simp] theorem Ptr.convertible_global (s : String) (o : BitVec 64) :
    (⟨.global s, o⟩ : Ptr).convertible = false := by
  simp [Ptr.convertible, Ptr.addr?]

@[simp] theorem Ptr.convertible_wbuf (o : BitVec 64) : (⟨.wbuf, o⟩ : Ptr).convertible = false := by
  simp [Ptr.convertible, Ptr.addr?]

/-- **No integer converts to a `temp` block** (#156's decoding below `2^62`, `decode_high` above). -/
theorem Ptr.ofAddr_ne_temp (x : BitVec 64) (a n : Nat) : (Ptr.ofAddr x).blk ≠ .temp a n := by
  intro h
  by_cases hx : x.toNat < 2 ^ 62
  · rw [Ptr.ofAddr_low hx] at h
    revert h
    unfold Ptr.fixedOfAddr
    by_cases h1 : x.toNat < 2 ^ 40
    · simp [h1]
    · simp only [h1, hx, ite_false, ite_true]; nofun
  · obtain ⟨a', h' | ⟨k, h'⟩⟩ := Addrs.decode_high x (by omega) <;>
      · simp only [Ptr.ofAddr] at h
        rw [h'] at h; cases h

/-- No integer converts to a frame temporary (its addresses decode to other blocks). -/
@[simp] theorem Ptr.convertible_temp (a n : Nat) (o : BitVec 64) :
    (⟨.temp a n, o⟩ : Ptr).convertible = false := by
  unfold Ptr.convertible
  split
  · rename_i x _
    rw [beq_eq_false_iff_ne]
    intro h
    exact Ptr.ofAddr_ne_temp x a n (congrArg Ptr.blk h)
  · rfl

end

end GoFV.SSA.Sem
