import GoFV.SSA.Sem.Ptr

/-!
# Concrete addresses round-trip (#156)

`Ptr.ofAddr_addr`: a pointer that `Convert` turns into an integer (`Ptr.convertible`) is the
pointer `Ptr.ofAddr` gives back, so `Convert (Convert p)` is `p` whenever the inner `Convert`
is defined (`convert_convert`). `Ptr.eq_iff`: pointer equality is block and offset equality.
-/

namespace GoFV.SSA.Sem

theorem Ptr.ofAddr_addr {p : Ptr} {x : BitVec 64} (hc : p.convertible = true)
    (ha : p.addr? = some x) : Ptr.ofAddr x = p := by
  obtain ⟨b, off⟩ := p
  have hoff := off.isLt
  cases b with
  | nil =>
    simp only [Ptr.convertible, decide_eq_true_eq] at hc
    simp only [Ptr.addr?, Blk.base?, Option.map_some, Option.some.injEq] at ha
    subst ha
    have hx : (BitVec.ofNat 64 0 + off).toNat = off.toNat := by simp
    unfold Ptr.ofAddr; simp only [hx, hc, ite_true]
    simp
  | heap n =>
    simp only [Ptr.convertible, Bool.and_eq_true, decide_eq_true_eq] at hc
    simp only [Ptr.addr?, Blk.base?, Option.map_some, Option.some.injEq] at ha
    subst ha
    have hx : (BitVec.ofNat 64 ((n + 1) * 2 ^ 40) + off).toNat = (n + 1) * 2 ^ 40 + off.toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      have h3 : (n + 1) * 2 ^ 40 + off.toNat < 2 ^ 64 := by omega
      have h0 : (n + 1) * 2 ^ 40 < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_add_right _ _) h3
      rw [Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt h3]
    unfold Ptr.ofAddr
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
    simp only [Ptr.convertible, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨⟨hk0, hk⟩, ha'⟩, ho⟩ := hc
    simp only [Ptr.addr?, Blk.base?, Option.map_some, Option.some.injEq] at ha
    subst ha
    have hb : 2 ^ 62 + a * 2 ^ 42 + k * 2 ^ 24 + off.toNat < 2 ^ 64 := by omega
    have hx : (BitVec.ofNat 64 (2 ^ 62 + a * 2 ^ 42 + k * 2 ^ 24) + off).toNat =
        2 ^ 62 + a * 2 ^ 42 + k * 2 ^ 24 + off.toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hb), Nat.mod_eq_of_lt hb]
    unfold Ptr.ofAddr
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
    simp only [Ptr.convertible, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨ha', ho⟩ := hc
    simp only [Ptr.addr?, Blk.base?, Option.map_some, Option.some.injEq] at ha
    subst ha
    have hb : 2 ^ 62 + a * 2 ^ 42 + off.toNat < 2 ^ 64 := by omega
    have hx : (BitVec.ofNat 64 (2 ^ 62 + a * 2 ^ 42) + off).toNat = 2 ^ 62 + a * 2 ^ 42 + off.toNat := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hb), Nat.mod_eq_of_lt hb]
    unfold Ptr.ofAddr
    simp only [hx]
    have h1 : ¬ (2 ^ 62 + a * 2 ^ 42 + off.toNat < 2 ^ 40) := by omega
    have h2 : ¬ (2 ^ 62 + a * 2 ^ 42 + off.toNat < 2 ^ 62) := by omega
    have e1 : (2 ^ 62 + a * 2 ^ 42 + off.toNat - 2 ^ 62) / 2 ^ 42 = a := by omega
    have e2 : (2 ^ 62 + a * 2 ^ 42 + off.toNat - 2 ^ 62) % 2 ^ 42 / 2 ^ 24 = 0 := by omega
    have e3 : (2 ^ 62 + a * 2 ^ 42 + off.toNat - 2 ^ 62) % 2 ^ 24 = off.toNat := by omega
    simp only [h1, h2, ite_false, e1, e2, e3, beq_self_eq_true, ite_true]
    simp
  | temp _ _ => simp [Ptr.convertible] at hc
  | global _ => simp [Ptr.convertible] at hc

/-- **`Convert` round-trips**: converting a pointer to an integer and back gives the pointer,
whenever the first conversion is defined. -/
theorem convert_convert (t t' : Ty) (e : Option Nat) (p : Ptr) (m m' : Val) {x : BitVec 64}
    (h : PtrOps.convert t [.ptr p, m] = .int .w64 x) :
    PtrOps.convert (.ptr e) [.int .w64 x, m'] = .ptr p := by
  have _ := t'
  unfold PtrOps.convert at h
  cases t with
  | int w =>
    cases w with
    | w64 =>
      simp only at h
      cases hc : p.convertible <;> cases ha : p.addr? <;> rw [hc, ha] at h <;> try cases h
      simp only [PtrOps.convert, Ptr.ofAddr_addr hc ha]
    | _ => cases h
  | _ => cases h

theorem Ptr.eq_iff (p q : Ptr) : p.eq q = true ↔ p = q := by
  obtain ⟨b, o⟩ := p; obtain ⟨b', o'⟩ := q
  simp [Ptr.eq]

end GoFV.SSA.Sem
