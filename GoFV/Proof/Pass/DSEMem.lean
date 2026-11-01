import GoFV.Proof.Pass.CSEMemChain
import GoFV.Opt.DeadStoreCheck

/-!
# dse: memories equal outside a set of bytes

`MemEq Q m m'`: `m'` has `m`'s allocations (in order, with their writability and sizes) and
the same bytes outside `Q` (a set of block offsets). Differences live only in the first
allocation of a block (the one `Mem.find?`, `Mem.read` and `Mem.write` use: `BlocksEq` drops a
block from `Q` after its first entry), so with `Q` empty the memories are equal (`MemEq.eq`).

* `MemEq.write`: the same write on both sides succeeds alike and makes the written bytes equal;
* `MemEq.write_left`: a write on the source side only adds the written bytes to `Q`;
* `MemEq.poison`: `VarDef`'s `poisonBlock` on both sides makes the block equal;
* `MemEq.read`: a read of a block with no byte in `Q` reads alike.

`IvQ P`: the bytes of the pending ranges `P` of dse's checker (allocations at activation 0, as
`Ctx.make` runs); `ivQ_sub`, `ivQ_filter`: removing a written range or a variable keeps every
byte not written.
-/

namespace GoFV.Proof.DSE

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof.CSE.Mem

/-! ## Allocations -/

/-- Same writability and size, the same bytes outside the offsets `Q`. -/
def AllocEq (Q : Nat → Prop) (a a' : Alloc) : Prop :=
  a'.writable = a.writable ∧ a'.data.size = a.data.size ∧ ∀ k, ¬ Q k → a'.data[k]? = a.data[k]?

theorem AllocEq.mono {Q Q' : Nat → Prop} {a a' : Alloc} (h : AllocEq Q a a')
    (hQ : ∀ k, Q k → Q' k) : AllocEq Q' a a' :=
  ⟨h.1, h.2.1, fun k hk => h.2.2 k fun hq => hk (hQ k hq)⟩

theorem AllocEq.refl (Q : Nat → Prop) (a : Alloc) : AllocEq Q a a := ⟨rfl, rfl, fun _ _ => rfl⟩

theorem AllocEq.eq {Q : Nat → Prop} {a a' : Alloc} (h : AllocEq Q a a') (hQ : ∀ k, ¬ Q k) :
    a' = a := by
  obtain ⟨hw, -, hd⟩ := h
  obtain ⟨d, w⟩ := a
  obtain ⟨d', w'⟩ := a'
  simp only at hw hd
  subst hw
  rw [Array.ext_getElem? fun k => hd k (hQ k)]

/-- The allocation lists: same blocks in order, each allocation equal outside `Q` at its
block; a block's later entries outside nothing. -/
def BlocksEq : (Blk → Nat → Prop) → List (Blk × Alloc) → List (Blk × Alloc) → Prop
  | _, [], [] => True
  | Q, e :: l, e' :: l' =>
    e'.1 = e.1 ∧ AllocEq (Q e.1) e.2 e'.2 ∧ BlocksEq (fun b k => Q b k ∧ b ≠ e.1) l l'
  | _, _, _ => False

theorem BlocksEq.mono : ∀ {Q Q' : Blk → Nat → Prop} {l l' : List (Blk × Alloc)},
    BlocksEq Q l l' → (∀ b k, Q b k → Q' b k) → BlocksEq Q' l l'
  | _, _, [], [], _, _ => trivial
  | _, _, _ :: _, _ :: _, ⟨h1, h2, h3⟩, hQ =>
    ⟨h1, h2.mono (hQ _), h3.mono fun b k ⟨hq, hb⟩ => ⟨hQ b k hq, hb⟩⟩
  | _, _, [], _ :: _, h, _ => h.elim
  | _, _, _ :: _, [], h, _ => h.elim

theorem BlocksEq.refl : ∀ (Q : Blk → Nat → Prop) (l : List (Blk × Alloc)), BlocksEq Q l l
  | _, [] => trivial
  | _, _ :: l => ⟨rfl, AllocEq.refl _ _, BlocksEq.refl _ l⟩

theorem BlocksEq.eq : ∀ {Q : Blk → Nat → Prop} {l l' : List (Blk × Alloc)},
    BlocksEq Q l l' → (∀ b k, ¬ Q b k) → l' = l
  | _, [], [], _, _ => rfl
  | _, e :: l, e' :: l', ⟨h1, h2, h3⟩, hQ => by
    have he : e' = e := Prod.ext h1 (h2.eq (hQ _))
    rw [he, h3.eq fun b k h => hQ b k h.1]
  | _, [], _ :: _, h, _ => h.elim
  | _, _ :: _, [], h, _ => h.elim

/-- The allocation `Mem.find?` sees, on related lists. -/
theorem BlocksEq.find : ∀ {Q : Blk → Nat → Prop} {l l' : List (Blk × Alloc)},
    BlocksEq Q l l' → ∀ b,
      ((l.find? (·.1 == b)).map (·.2) = none ∧ (l'.find? (·.1 == b)).map (·.2) = none) ∨
      ∃ a a', (l.find? (·.1 == b)).map (·.2) = some a ∧
        (l'.find? (·.1 == b)).map (·.2) = some a' ∧ AllocEq (Q b) a a'
  | _, [], [], _, _ => .inl ⟨rfl, rfl⟩
  | Q, e :: l, e' :: l', ⟨h1, h2, h3⟩, b => by
    simp only [List.find?_cons, h1]
    by_cases hb : (e.1 == b) = true
    · have := beq_iff_eq.1 hb
      subst this
      simp only [beq_self_eq_true, Option.map_some]
      exact .inr ⟨_, _, rfl, rfl, h2⟩
    · simp only [hb]
      rcases h3.find b with h | ⟨a, a', ha, ha', hA⟩
      · exact .inl h
      · refine .inr ⟨a, a', ha, ha', hA.mono fun k hk => hk.1⟩
  | _, [], _ :: _, h, _ => h.elim
  | _, _ :: _, [], h, _ => h.elim

/-- `Mem.set` on the allocation list. -/
def setL (b : Blk) (a : Alloc) : List (Blk × Alloc) → List (Blk × Alloc)
  | [] => [(b, a)]
  | e :: l => if e.1 == b then (b, a) :: l else e :: setL b a l

theorem setL_eq (b : Blk) (a : Alloc) : ∀ l : List (Blk × Alloc),
    setL b a l = match l.findIdx? (·.1 == b) with
      | some i => l.set i (b, a)
      | none => l ++ [(b, a)]
  | [] => rfl
  | e :: l => by
    rw [setL, List.findIdx?_cons]
    by_cases hb : (e.1 == b) = true
    · simp [hb]
    · simp only [hb, Bool.false_eq_true, ite_false, setL_eq b a l]
      cases l.findIdx? (·.1 == b) <;> rfl

theorem set_toList (m : Mem) (b : Blk) (a : Alloc) :
    (m.set b a).blocks.toList = setL b a m.blocks.toList := by
  obtain ⟨⟨l⟩, nh⟩ := m
  rw [setL_eq]
  unfold Mem.set
  simp only [List.findIdx?_toArray]
  cases l.findIdx? (·.1 == b) <;> simp

theorem set_nextHeap (m : Mem) (b : Blk) (a : Alloc) : (m.set b a).nextHeap = m.nextHeap := by
  unfold Mem.set; split <;> rfl

theorem set_nextAct (m : Mem) (b : Blk) (a : Alloc) : (m.set b a).nextAct = m.nextAct := by
  unfold Mem.set; split <;> rfl

theorem find?_toList (m : Mem) (b : Blk) :
    m.find? b = (m.blocks.toList.find? (·.1 == b)).map (·.2) := by
  simp only [Mem.find?, ← Array.find?_toList]

/-- Restricting `Q` at a block with no allocation changes nothing. -/
theorem BlocksEq.drop_absent {b : Blk} : ∀ {Q : Blk → Nat → Prop} {l l' : List (Blk × Alloc)},
    BlocksEq Q l l' → (l.find? (·.1 == b)).map (·.2) = none →
    BlocksEq (fun b' k => Q b' k ∧ b' ≠ b) l l'
  | _, [], [], _, _ => trivial
  | _, e :: l, e' :: l', ⟨h1, h2, h3⟩, hn => by
    simp only [List.find?_cons] at hn
    cases hb : (e.1 == b) with
    | true => simp [hb] at hn
    | false =>
      simp only [hb] at hn
      have he : e.1 ≠ b := fun h => by simp [h] at hb
      refine ⟨h1, h2.mono fun k hk => ⟨hk, he⟩, (h3.drop_absent hn).mono ?_⟩
      exact fun b' k ⟨⟨hq, hne⟩, hb'⟩ => ⟨⟨hq, hb'⟩, hne⟩
  | _, [], _ :: _, h, _ => h.elim
  | _, _ :: _, [], h, _ => h.elim

/-- Setting a block's allocation on both sides. -/
theorem BlocksEq.set : ∀ {Q Q' : Blk → Nat → Prop} {l l' : List (Blk × Alloc)} {b : Blk}
    {a a' : Alloc}, BlocksEq Q l l' → (∀ b' k, b' ≠ b → Q b' k → Q' b' k) →
    AllocEq (Q' b) a a' → BlocksEq Q' (setL b a l) (setL b a' l')
  | _, _, [], [], _, _, _, _, _, ha => ⟨rfl, ha, trivial⟩
  | Q, Q', e :: l, e' :: l', b, a, a', ⟨h1, h2, h3⟩, hQ, ha => by
    simp only [setL, h1]
    by_cases hb : (e.1 == b) = true
    · have he := beq_iff_eq.1 hb
      simp only [hb, ite_true]
      refine ⟨rfl, ha, h3.mono fun b' k ⟨hq, hne⟩ => ⟨hQ b' k (he ▸ hne) hq, he ▸ hne⟩⟩
    · have he : e.1 ≠ b := fun h => hb (beq_iff_eq.2 h)
      simp only [hb, Bool.false_eq_true, ite_false]
      refine ⟨h1, h2.mono fun k => hQ _ k he, BlocksEq.set h3 ?_ (ha.mono fun k hk => ⟨hk, he.symm⟩)⟩
      exact fun b' k hb' ⟨hq, hne⟩ => ⟨hQ b' k hb' hq, hne⟩
  | _, _, [], _ :: _, _, _, _, h, _, _ => h.elim
  | _, _, _ :: _, [], _, _, _, h, _, _ => h.elim

/-- Setting a block to the allocation `find?` sees changes nothing. -/
theorem setL_self {b : Blk} {a : Alloc} : ∀ {l : List (Blk × Alloc)},
    (l.find? (·.1 == b)).map (·.2) = some a → setL b a l = l
  | [], h => by simp at h
  | e :: l, h => by
    simp only [List.find?_cons] at h
    unfold setL
    cases hb : (e.1 == b) with
    | true =>
      simp only [hb, Option.map_some, Option.some.injEq, ite_true] at h ⊢
      rw [← h, ← beq_iff_eq.1 hb]
    | false =>
      simp only [hb, Bool.false_eq_true, ite_false] at h ⊢
      rw [setL_self h]

/-! ## Memories -/

/-- `m'` is `m` outside the bytes `Q`. -/
def MemEq (Q : Blk → Nat → Prop) (m m' : Mem) : Prop :=
  m'.nextHeap = m.nextHeap ∧ m'.nextAct = m.nextAct ∧ BlocksEq Q m.blocks.toList m'.blocks.toList

theorem MemEq.refl (Q : Blk → Nat → Prop) (m : Mem) : MemEq Q m m :=
  ⟨rfl, rfl, BlocksEq.refl _ _⟩

theorem MemEq.mono {Q Q' : Blk → Nat → Prop} {m m' : Mem} (h : MemEq Q m m')
    (hQ : ∀ b k, Q b k → Q' b k) : MemEq Q' m m' := ⟨h.1, h.2.1, h.2.2.mono hQ⟩

theorem MemEq.eq {Q : Blk → Nat → Prop} {m m' : Mem} (h : MemEq Q m m')
    (hQ : ∀ b k, ¬ Q b k) : m' = m := by
  obtain ⟨hh, ha, hb⟩ := h
  have hl := hb.eq hQ
  obtain ⟨⟨l⟩, nh, na⟩ := m
  obtain ⟨⟨l'⟩, nh', na'⟩ := m'
  simp only at hh ha hl
  rw [hh, ha, hl]

theorem MemEq.find {Q : Blk → Nat → Prop} {m m' : Mem} (h : MemEq Q m m') (b : Blk) :
    (m.find? b = none ∧ m'.find? b = none) ∨
      ∃ a a', m.find? b = some a ∧ m'.find? b = some a' ∧ AllocEq (Q b) a a' := by
  rw [find?_toList, find?_toList]
  exact h.2.2.find b

theorem MemEq.set {Q Q' : Blk → Nat → Prop} {m m' : Mem} (h : MemEq Q m m') {b : Blk}
    {a a' : Alloc} (hQ : ∀ b' k, b' ≠ b → Q b' k → Q' b' k) (ha : AllocEq (Q' b) a a') :
    MemEq Q' (m.set b a) (m'.set b a') := by
  refine ⟨by rw [set_nextHeap, set_nextHeap, h.1], by rw [set_nextAct, set_nextAct, h.2.1], ?_⟩
  rw [set_toList, set_toList]
  exact h.2.2.set hQ ha

theorem set_self {m : Mem} {b : Blk} {a : Alloc} (h : m.find? b = some a) : m.set b a = m := by
  have hl : (m.set b a).blocks.toList = m.blocks.toList := by
    rw [set_toList]; rw [find?_toList] at h; exact setL_self h
  obtain ⟨⟨l⟩, nh, na⟩ := m
  have hn := set_nextHeap ⟨⟨l⟩, nh, na⟩ b a
  have ht := set_nextAct ⟨⟨l⟩, nh, na⟩ b a
  generalize Mem.set ⟨⟨l⟩, nh, na⟩ b a = m' at hl hn ht
  obtain ⟨⟨l'⟩, nh', na'⟩ := m'
  simp only at hl hn ht
  rw [hl, hn, ht]

/-- The bytes a write of `n` bytes at `p` touches. -/
def Region (p : Ptr) (n : Nat) (b : Blk) (k : Nat) : Prop :=
  b = p.blk ∧ p.off.toNat ≤ k ∧ k < p.off.toNat + n

/-- The byte loop of `Mem.write` gives two arrays of one size the same bytes where it writes,
and keeps the others. -/
theorem foldl_set_rel (off : Nat) (bs : Array Byte) (j : Nat) :
    ∀ (l : List Nat) (d d' : Array Byte), d'.size = d.size →
      ((∀ i ∈ l, off + i ≠ j) → d'[j]? = d[j]?) →
      (l.foldl (fun d i => d.set! (off + i) bs[i]!) d')[j]? =
        (l.foldl (fun d i => d.set! (off + i) bs[i]!) d)[j]?
  | [], _, _, _, h => h fun _ h => absurd h List.not_mem_nil
  | i :: l, d, d', hs, h => by
    simp only [List.foldl_cons]
    refine foldl_set_rel off bs j l _ _ (by simp [hs]) fun hl => ?_
    simp only [Array.set!_eq_setIfInBounds]
    by_cases hj : off + i = j
    · subst hj
      simp only [Array.getElem?_setIfInBounds_self, hs]
    · rw [Array.getElem?_setIfInBounds_ne hj, Array.getElem?_setIfInBounds_ne hj]
      exact h fun i' hi' => by
        rcases List.mem_cons.1 hi' with rfl | hi'
        · exact hj
        · exact hl i' hi'

/-- **The same write on both sides.** -/
theorem MemEq.write {Q : Blk → Nat → Prop} {m m' m1 : Mem} (h : MemEq Q m m') {p : Ptr}
    {bs : Array Byte} (hw : m.write p bs = some m1) :
    ∃ m1', m'.write p bs = some m1' ∧
      MemEq (fun b k => Q b k ∧ ¬ Region p bs.size b k) m1 m1' := by
  unfold Mem.write at hw ⊢
  by_cases he : bs.isEmpty = true
  · have hsz : bs.size = 0 := Array.isEmpty_iff_size_eq_zero.1 he
    simp only [he, ite_true] at hw ⊢
    cases hw
    exact ⟨m', rfl, h.mono fun _ _ hq => ⟨hq, fun hr => by have := hr.2; omega⟩⟩
  simp only [he, Bool.false_eq_true, ite_false] at hw ⊢
  rcases h.find p.blk with ⟨h1, -⟩ | ⟨a, a', ha, ha', hA⟩
  · rw [h1] at hw; cases hw
  rw [ha] at hw
  rw [ha']
  simp only [Option.bind_eq_bind, Option.bind_some] at hw ⊢
  rw [hA.1, hA.2.1]
  split at hw
  · rename_i hc
    cases hw
    simp only [hc, ↓reduceIte]
    refine ⟨_, rfl, h.set (fun b' k hb hq => ⟨hq, fun hr => hb hr.1⟩) ⟨rfl, ?_, fun k hk => ?_⟩⟩
    · simp only [foldl_set_size, hA.2.1]
    · simp only
      refine foldl_set_rel _ _ _ _ _ _ hA.2.1 fun hn => hA.2.2 k fun hq => hk ⟨hq, ?_⟩
      rintro ⟨-, h1, h2⟩
      exact hn (k - p.off.toNat) (List.mem_range.2 (by omega)) (by omega)
  · cases hw

/-- **A write on the source side only** (an eliminated store). -/
theorem MemEq.write_left {Q : Blk → Nat → Prop} {m m' m1 : Mem} (h : MemEq Q m m') {p : Ptr}
    {bs : Array Byte} (hw : m.write p bs = some m1) :
    MemEq (fun b k => Q b k ∨ Region p bs.size b k) m1 m' := by
  unfold Mem.write at hw
  by_cases he : bs.isEmpty = true
  · simp only [he, ite_true] at hw
    cases hw
    exact h.mono fun _ _ h => .inl h
  simp only [he, Bool.false_eq_true, ite_false] at hw
  rcases h.find p.blk with ⟨h1, -⟩ | ⟨a, a', ha, ha', hA⟩
  · rw [h1] at hw; cases hw
  rw [ha] at hw
  simp only [Option.bind_eq_bind, Option.bind_some] at hw
  split at hw
  · rename_i hc
    cases hw
    rw [← set_self ha']
    refine h.set (fun b' k _ hq => .inl hq) ⟨hA.1, ?_, fun k hk => ?_⟩
    · simp only [foldl_set_size, hA.2.1]
    · simp only
      rw [foldl_set_get]
      · exact hA.2.2 k fun hq => hk (.inl hq)
      · intro i hi he
        simp only [List.mem_range] at hi
        exact hk (.inr ⟨rfl, by omega, by omega⟩)
  · cases hw

/-- `VarDef`'s `poisonBlock` on both sides. -/
theorem MemEq.poison {Q : Blk → Nat → Prop} {m m' : Mem} (h : MemEq Q m m') (b : Blk) :
    MemEq (fun b' k => Q b' k ∧ b' ≠ b) (m.poisonBlock b) (m'.poisonBlock b) := by
  unfold Mem.poisonBlock
  rcases h.find b with ⟨h1, h2⟩ | ⟨a, a', ha, ha', hA⟩
  · rw [h1, h2]
    refine ⟨h.1, h.2.1, ?_⟩
    rw [find?_toList] at h1
    exact h.2.2.drop_absent h1
  · rw [ha, ha']
    refine h.set (fun b' k hb hq => ⟨hq, hb⟩) ⟨hA.1, by simp [hA.2.1], fun k _ => ?_⟩
    simp only [hA.2.1]

/-- A read of a block with no byte in `Q`. -/
theorem MemEq.read {Q : Blk → Nat → Prop} {m m' : Mem} (h : MemEq Q m m') (p : Ptr) (n : Nat)
    (hQ : ∀ k, ¬ Q p.blk k) : m'.read p n = m.read p n := by
  unfold Mem.read
  rcases h.find p.blk with ⟨h1, h2⟩ | ⟨a, a', ha, ha', hA⟩
  · rw [h1, h2]
  · rw [ha, ha', hA.eq hQ]

/-! ## Pending ranges -/

/-- The bytes of the pending ranges `P`. -/
def IvQ (P : List DSE.Iv) (b : Blk) (k : Nat) : Prop :=
  ∃ iv ∈ P, b = blkOf iv.1 ∧ iv.2.1 ≤ (k : Int) ∧ (k : Int) < iv.2.2

theorem ivQ_nil (b : Blk) (k : Nat) : ¬ IvQ [] b k := fun ⟨_, h, _⟩ => absurd h List.not_mem_nil

theorem ivQ_append {P : List DSE.Iv} {iv : DSE.Iv} {b : Blk} {k : Nat}
    (h : IvQ P b k ∨ (b = blkOf iv.1 ∧ iv.2.1 ≤ (k : Int) ∧ (k : Int) < iv.2.2)) :
    IvQ (P ++ [iv]) b k := by
  rcases h with ⟨iv', hm, h⟩ | h
  · exact ⟨iv', List.mem_append_left _ hm, h⟩
  · exact ⟨iv, by simp, h⟩

/-- Removing a written range keeps the bytes it does not write. -/
theorem ivQ_sub {P : List DSE.Iv} {r : DSE.Iv} {b : Blk} {k : Nat} (h : IvQ P b k)
    (hr : ¬ (b = blkOf r.1 ∧ r.2.1 ≤ (k : Int) ∧ (k : Int) < r.2.2)) :
    IvQ (P.flatMap (DSE.sub r)) b k := by
  obtain ⟨⟨a, lo, hi⟩, hm, hb, h1, h2⟩ := h
  simp only at hb h1 h2
  by_cases ha : a = r.1
  · subst ha
    have hk : (k : Int) < r.2.1 ∨ r.2.2 ≤ (k : Int) := by
      rcases Int.lt_or_le (k : Int) r.2.1 with h | h
      · exact .inl h
      · exact .inr (Int.not_lt.1 fun h' => hr ⟨hb, h, h'⟩)
    rcases hk with hk | hk
    · have hc : lo < min hi r.2.1 := by omega
      refine ⟨(r.1, lo, min hi r.2.1), List.mem_flatMap.2 ⟨_, hm, by simp [DSE.sub, hc]⟩, hb, h1,
        by simp only; omega⟩
    · have hc : max lo r.2.2 < hi := by omega
      refine ⟨(r.1, max lo r.2.2, hi), List.mem_flatMap.2 ⟨_, hm, by simp [DSE.sub, hc]⟩, hb,
        by simp only; omega, h2⟩
  · exact ⟨(a, lo, hi), List.mem_flatMap.2 ⟨_, hm, by simp [DSE.sub, ha]⟩, hb, h1, h2⟩

/-- Removing a variable keeps the bytes of the other blocks. -/
theorem ivQ_filter {P : List DSE.Iv} {n : AuxRef} {b : Blk} {k : Nat} (h : IvQ P b k)
    (hb : b ≠ blkOf (.local n)) : IvQ (P.filter (·.1 != .local n)) b k := by
  obtain ⟨iv, hm, hb', h1, h2⟩ := h
  refine ⟨iv, List.mem_filter.2 ⟨hm, ?_⟩, hb', h1, h2⟩
  simp only [bne_iff_ne, ne_eq]
  intro he
  exact hb (by rw [hb', he])

/-- No pending range in allocation `a`: no pending byte in its block. -/
theorem ivQ_not_alloc {P : List DSE.Iv} {a : CSE.Alloc} (h : P.all (·.1 != a) = true) (k : Nat) :
    ¬ IvQ P (blkOf a) k := by
  rintro ⟨iv, hm, hb, -⟩
  have := List.all_eq_true.1 h iv hm
  simp only [bne_iff_ne, ne_eq] at this
  exact this (blkOf_inj hb).symm

end GoFV.Proof.DSE
