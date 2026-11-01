import GoFV.SSA.Sem.Ptr

/-!
# cse's memory skips: reads after disjoint writes

`read_write_sep`: a read of `n` bytes at `p` after a write of `bs` at `q` reads what it read
before when the accesses are separate (`Sep`: one is empty, they are in different blocks, or
their byte ranges do not overlap). `encode_size`: a `Store` writes exactly its shape's size.
-/

namespace GoFV.Proof.CSE.Mem

open GoFV.SSA GoFV.SSA.Sem

/-- A read of `n` bytes at `p` and a write of `k` bytes at `q` touch different bytes. -/
def Sep (p : Ptr) (n : Nat) (q : Ptr) (k : Nat) : Prop :=
  n = 0 ∨ k = 0 ∨ p.blk ≠ q.blk ∨ p.off.toNat + n ≤ q.off.toNat ∨ q.off.toNat + k ≤ p.off.toNat

theorem find?_set_ne {l : List (Blk × Alloc)} {i : Nat} {e : Blk × Alloc} {b : Blk}
    (hi : (l[i]?.map (·.1 == b)) ≠ some true) (he : (e.1 == b) = false) :
    (l.set i e).find? (·.1 == b) = l.find? (·.1 == b) := by
  induction l generalizing i with
  | nil => rfl
  | cons x l ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.map_some, ne_eq, Option.some.injEq,
        Bool.not_eq_true] at hi
      simp only [List.set_cons_zero, List.find?_cons, he, hi]
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      simp only [List.set_cons_succ, List.find?_cons, ih hi]

theorem find?_set_eq {l : List (Blk × Alloc)} {i : Nat} {e : Blk × Alloc} {b : Blk}
    (hi : l.findIdx? (·.1 == b) = some i) (he : (e.1 == b) = true) :
    (l.set i e).find? (·.1 == b) = some e := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x l ih =>
    rw [List.findIdx?_cons] at hi
    by_cases hx : (x.1 == b) = true
    · simp only [hx, ite_true, Option.some.injEq] at hi
      subst hi
      simp only [List.set_cons_zero, List.find?_cons, he]
    · simp only [hx, Bool.false_eq_true, ite_false] at hi
      cases hl : List.findIdx? (·.1 == b) l with
      | none => rw [hl] at hi; cases hi
      | some j =>
        rw [hl] at hi
        cases hi
        simp only [List.set_cons_succ, List.find?_cons, hx, ih hl]

/-- `Mem.set b a` changes block `b` only. -/
theorem find?_set (m : Mem) (b : Blk) (a : Alloc) (b' : Blk) :
    (m.set b a).find? b' = if b = b' then some a else m.find? b' := by
  obtain ⟨⟨l⟩, nh⟩ := m
  unfold Mem.set Mem.find?
  simp only [List.findIdx?_toArray]
  cases hl : l.findIdx? (·.1 == b) with
  | some i =>
    simp only [Array.toList_set!, ← Array.find?_toList]
    split
    · subst b'
      rw [find?_set_eq hl (by simp)]; rfl
    · rename_i hne
      rw [find?_set_ne _ (by simpa using hne)]
      obtain ⟨h, h1, _⟩ := List.findIdx?_eq_some_iff_getElem.1 hl
      rw [List.getElem?_eq_getElem h]
      simp only [Option.map_some, ne_eq, Option.some.injEq]
      simp only [beq_iff_eq] at h1
      rw [h1]; simpa using hne
  | none =>
    simp only [← Array.find?_toList, Array.toList_push, List.find?_append]
    have hn : l.find? (·.1 == b) = none := by
      rw [List.find?_eq_none]
      intro x hx
      simp [List.findIdx?_eq_none_iff.1 hl x hx]
    split
    · subst b'; simp [hn]
    · rename_i hne
      simp [hne]

/-- The byte loop of `Mem.write` keeps the size. -/
theorem foldl_set_size (off : Nat) (bs : Array Byte) :
    ∀ (l : List Nat) (d : Array Byte),
      (l.foldl (fun d i => d.set! (off + i) bs[i]!) d).size = d.size
  | [], _ => rfl
  | i :: l, d => by
    rw [List.foldl_cons, foldl_set_size off bs l]
    simp

/-- The byte loop of `Mem.write` keeps the bytes it does not write. -/
theorem foldl_set_get (off : Nat) (bs : Array Byte) (j : Nat) :
    ∀ (l : List Nat) (d : Array Byte), (∀ i ∈ l, off + i ≠ j) →
      (l.foldl (fun d i => d.set! (off + i) bs[i]!) d)[j]? = d[j]?
  | [], _, _ => rfl
  | i :: l, d, h => by
    rw [List.foldl_cons, foldl_set_get off bs j l _ (fun k hk => h k (List.mem_cons_of_mem _ hk))]
    rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (h i List.mem_cons_self)]

theorem extract_congr {a b : Array Byte} {s e : Nat} (hsz : a.size = b.size)
    (h : ∀ j, s ≤ j → j < e → a[j]? = b[j]?) : a.extract s e = b.extract s e := by
  apply Array.ext
  · simp [hsz]
  · intro j h1 h2
    simp only [Array.getElem_extract]
    have hj := h (s + j) (by omega) (by simp at h1; omega)
    rw [Array.getElem?_eq_getElem (by simp at h1; omega),
      Array.getElem?_eq_getElem (by simp at h2; omega)] at hj
    exact Option.some.inj hj

/-- A read is unchanged by a separate write. -/
theorem read_write_sep {m m' : Mem} {p q : Ptr} {bs : Array Byte} {n : Nat}
    (hw : m.write q bs = some m') (hs : Sep p n q bs.size) : m'.read p n = m.read p n := by
  unfold Mem.write at hw
  by_cases he : bs.isEmpty
  · simp only [he, ite_true] at hw
    cases hw; rfl
  simp only [he, Bool.false_eq_true, ite_false] at hw
  cases ha : m.find? q.blk with
  | none => rw [ha] at hw; cases hw
  | some a =>
    rw [ha] at hw
    simp only [Option.bind_eq_bind, Option.bind_some] at hw
    split at hw
    · cases hw
      unfold Mem.read
      by_cases hn : n = 0
      · simp [hn]
      simp only [beq_iff_eq, hn, ite_false]
      rw [find?_set]
      by_cases hb : q.blk = p.blk
      · simp only [hb, ite_true]
        rw [← hb, ha]
        simp only [Option.bind_eq_bind, Option.bind_some, foldl_set_size]
        have hsz : bs.size ≠ 0 := by simpa [Array.isEmpty_iff_size_eq_zero] using he
        have hr : q.off.toNat + bs.size ≤ p.off.toNat ∨ p.off.toNat + n ≤ q.off.toNat := by
          rcases hs with h | h | h | h | h
          · exact absurd h hn
          · exact absurd h hsz
          · exact absurd hb.symm h
          · exact .inr h
          · exact .inl h
        split
        · congr 1
          apply extract_congr (foldl_set_size _ _ _ _)
          intro j h1 h2
          apply foldl_set_get
          intro i hi
          simp only [List.mem_range] at hi
          omega
        · rfl
      · simp only [hb, ite_false]
    · cases hw

/-- `encodeFields` keeps the buffer's size. -/
theorem encodeFields_size : ∀ (buf : Array Byte) (fs : List (Nat × Ty)) (vs : List Val),
    (encodeFields buf fs vs).size = buf.size
  | buf, (o, t) :: fs, v :: vs => by
    rw [encodeFields, encodeFields_size]
    unfold putBytes
    generalize List.range (encode t v).size = l
    induction l generalizing buf with
    | nil => rfl
    | cons i l ih =>
      rw [List.foldl_cons, ih]
      split <;> simp
  | buf, [], _ => by rw [encodeFields]; intros; simp_all
  | buf, _ :: _, [] => by rw [encodeFields]; intros; simp_all

/-- `encode t x` is `t.size` bytes. -/
theorem encode_size (t : Ty) (x : Val) : (encode t x).size = t.size := by
  rw [encode.eq_def]
  split
  · split <;> simp [intBytes, Ty.size]
  · simp [ptrBytes, Ty.size, Width.bytes]; rfl
  · rfl
  · simp [ptrBytes, Ty.size]
  · simp [intBytes, Ty.size]
  · simp [encodeFields_size, Ty.size]
  · split
    · rename_i h; simpa using h
    · simp
  · simp

end GoFV.Proof.CSE.Mem
