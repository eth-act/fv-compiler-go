import GoFV.SSA.Sem.Mem

/-!
# Byte and memory refinement (`docs/plans/semantics.md` §3.5)

`Byte.Refines`, `BytesRefine`, `Mem.Refines` (`Sem/Val.lean`): a poison byte is refined by any
byte; memories are refined when they have the same allocations and every byte is refined.
Here: transitivity, lengths, and that a poison-free source is equal to its refinement.
-/

namespace GoFV.SSA.Sem

open GoFV.SSA

theorem Byte.Refines.trans {a b c : Byte} : Byte.Refines a b → Byte.Refines b c → Byte.Refines a c
  | .poison _, _ => .poison _
  | .refl _, h => h

theorem Byte.Refines.eq {a b : Byte} (h : Byte.Refines a b) (ha : a ≠ .poison) : a = b := by
  cases h with
  | poison => exact absurd rfl ha
  | refl => rfl

theorem BytesRefine.trans : {a b c : List Byte} → BytesRefine a b → BytesRefine b c →
    BytesRefine a c
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h1 t1, .cons h2 t2 => .cons (h1.trans h2) (BytesRefine.trans t1 t2)

theorem BytesRefine.length_eq : {a b : List Byte} → BytesRefine a b → a.length = b.length
  | _, _, .nil => rfl
  | _, _, .cons _ t => by simp [BytesRefine.length_eq t]

theorem BytesRefine.eq : {a b : List Byte} → BytesRefine a b → (∀ x ∈ a, x ≠ .poison) → a = b
  | _, _, .nil, _ => rfl
  | _, _, .cons h t, hp => by
    rw [h.eq (hp _ List.mem_cons_self), BytesRefine.eq t fun x hx => hp x (List.mem_cons_of_mem _ hx)]

theorem BytesRefine.append : {a b c d : List Byte} → BytesRefine a b → BytesRefine c d →
    BytesRefine (a ++ c) (b ++ d)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons h t, h' => .cons h (BytesRefine.append t h')

theorem BytesRefine.drop : ∀ (n : Nat) {a b : List Byte}, BytesRefine a b →
    BytesRefine (a.drop n) (b.drop n)
  | 0, _, _, h => h
  | _ + 1, _, _, .nil => .nil
  | n + 1, _, _, .cons _ t => BytesRefine.drop n t

theorem BytesRefine.take : ∀ (n : Nat) {a b : List Byte}, BytesRefine a b →
    BytesRefine (a.take n) (b.take n)
  | 0, _, _, _ => .nil
  | _ + 1, _, _, .nil => .nil
  | n + 1, _, _, .cons h t => .cons h (BytesRefine.take n t)

theorem BytesRefine.get? : ∀ (i : Nat) {a b : List Byte}, BytesRefine a b →
    (a[i]? = none ∧ b[i]? = none) ∨ ∃ x y, a[i]? = some x ∧ b[i]? = some y ∧ Byte.Refines x y
  | _, _, _, .nil => .inl ⟨rfl, rfl⟩
  | 0, _, _, .cons h _ => .inr ⟨_, _, rfl, rfl, h⟩
  | i + 1, _, _, .cons _ t => by simpa using BytesRefine.get? i t

theorem BytesRefine.set : ∀ (i : Nat) {a b : List Byte} {x y : Byte}, BytesRefine a b →
    Byte.Refines x y → BytesRefine (a.set i x) (b.set i y)
  | _, _, _, _, _, .nil, _ => .nil
  | 0, _, _, _, _, .cons _ t, hx => .cons hx t
  | i + 1, _, _, _, _, .cons h t, hx => .cons h (BytesRefine.set i t hx)

theorem BytesRefine.replicate_poison : ∀ (n : Nat) {b : List Byte}, b.length = n →
    BytesRefine (List.replicate n .poison) b
  | 0, [], _ => .nil
  | n + 1, _ :: b, h => .cons (.poison _) (BytesRefine.replicate_poison n (by simpa using h))

/-! ## Arrays -/

/-- Byte arrays refined pointwise. -/
abbrev BytesRefineA (a b : Array Byte) : Prop := BytesRefine a.toList b.toList

theorem BytesRefineA.size_eq {a b : Array Byte} (h : BytesRefineA a b) : a.size = b.size := by
  simpa using h.length_eq

theorem BytesRefineA.extract {a b : Array Byte} (h : BytesRefineA a b) (i j : Nat) :
    BytesRefineA (a.extract i j) (b.extract i j) := by
  simp only [BytesRefineA, Array.toList_extract, List.extract_eq_take_drop]
  exact BytesRefine.take _ (BytesRefine.drop _ h)

theorem BytesRefineA.getElem? {a b : Array Byte} (h : BytesRefineA a b) (i : Nat) :
    (a[i]? = none ∧ b[i]? = none) ∨ ∃ x y, a[i]? = some x ∧ b[i]? = some y ∧ Byte.Refines x y := by
  simpa using BytesRefine.get? i h

theorem BytesRefineA.getElem! {a b : Array Byte} (h : BytesRefineA a b) (i : Nat) :
    Byte.Refines a[i]! b[i]! := by
  rcases h.getElem? i with ⟨ha, hb⟩ | ⟨x, y, ha, hb, hxy⟩
  · simp [getElem!_def, ha, hb]; exact .refl _
  · simp [getElem!_def, ha, hb, hxy]

theorem BytesRefineA.set! {a b : Array Byte} (h : BytesRefineA a b) (i : Nat) {x y : Byte}
    (hx : Byte.Refines x y) : BytesRefineA (a.set! i x) (b.set! i y) := by
  simp only [BytesRefineA, Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
  exact BytesRefine.set i h hx

theorem BytesRefineA.eq {a b : Array Byte} (h : BytesRefineA a b) (hp : ∀ x ∈ a.toList, x ≠ .poison) :
    a = b := Array.toList_inj.1 (BytesRefine.eq h hp)

theorem BytesRefineA.replicate_poison (n : Nat) {b : Array Byte} (h : b.size = n) :
    BytesRefineA (Array.replicate n .poison) b := by
  simp only [BytesRefineA, Array.toList_replicate]
  exact BytesRefine.replicate_poison n (by simpa using h)

theorem BytesRefineA.refl (a : Array Byte) : BytesRefineA a a := BytesRefine.refl _

/-! ## Allocations and memories -/

theorem Alloc.Refines.trans {a b c : Alloc} (h1 : Alloc.Refines a b) (h2 : Alloc.Refines b c) :
    Alloc.Refines a c := ⟨h1.writable.trans h2.writable, h1.data.trans h2.data⟩

theorem Alloc.Refines.refl (a : Alloc) : Alloc.Refines a a := ⟨rfl, BytesRefine.refl _⟩

theorem Alloc.Refines.size_eq {a b : Alloc} (h : Alloc.Refines a b) : a.data.size = b.data.size :=
  BytesRefineA.size_eq h.data

theorem AllocsRefine.trans : {a b c : List (Blk × Alloc)} → AllocsRefine a b → AllocsRefine b c →
    AllocsRefine a c
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons _ h1 t1, .cons _ h2 t2 => .cons _ (h1.trans h2) (AllocsRefine.trans t1 t2)

theorem Mem.Refines.trans {a b c : Mem} (h1 : Mem.Refines a b) (h2 : Mem.Refines b c) :
    Mem.Refines a c := ⟨h1.nextHeap.trans h2.nextHeap, h1.blocks.trans h2.blocks⟩

theorem AllocsRefine.keys : {l l' : List (Blk × Alloc)} → AllocsRefine l l' →
    l.map (·.1) = l'.map (·.1)
  | _, _, .nil => rfl
  | _, _, .cons b _ t => by simp [AllocsRefine.keys t]

theorem AllocsRefine.find? (b : Blk) : {l l' : List (Blk × Alloc)} → AllocsRefine l l' →
    ((l.find? (·.1 == b)).map (·.2) = none ∧ (l'.find? (·.1 == b)).map (·.2) = none) ∨
      ∃ a a', (l.find? (·.1 == b)).map (·.2) = some a ∧ (l'.find? (·.1 == b)).map (·.2) = some a' ∧
        Alloc.Refines a a'
  | _, _, .nil => .inl ⟨rfl, rfl⟩
  | _, _, .cons c h t => by
    by_cases hc : c = b
    · subst hc; exact .inr ⟨_, _, by simp, by simp, h⟩
    · have hc' : (c == b) = false := by simpa using hc
      simpa [List.find?_cons, hc'] using AllocsRefine.find? b t

theorem AllocsRefine.set : ∀ (i : Nat) {l l' : List (Blk × Alloc)} (b : Blk) {a a' : Alloc},
    AllocsRefine l l' → Alloc.Refines a a' → (∀ c, (l[i]?.map (·.1)) = some c → c = b) →
    AllocsRefine (l.set i (b, a)) (l'.set i (b, a'))
  | _, _, _, _, _, _, .nil, _, _ => .nil
  | 0, _, _, b, _, _, .cons c _ t, ha, hb => by
    have := hb c (by simp); subst this; exact .cons _ ha t
  | i + 1, _, _, b, _, _, .cons c h t, ha, hb =>
    .cons c h (AllocsRefine.set i b t ha fun c' hc' => hb c' (by simpa using hc'))

theorem AllocsRefine.append {l l' r r' : List (Blk × Alloc)} (h : AllocsRefine l l')
    (h' : AllocsRefine r r') : AllocsRefine (l ++ r) (l' ++ r') := by
  induction h with
  | nil => exact h'
  | cons b ha _ ih => exact .cons b ha ih

theorem AllocsRefine.filter (p : Blk → Bool) : {l l' : List (Blk × Alloc)} → AllocsRefine l l' →
    AllocsRefine (l.filter (fun x => p x.1)) (l'.filter (fun x => p x.1))
  | _, _, .nil => .nil
  | _, _, .cons b h t => by
    by_cases hb : p b <;> simp [hb]
    · exact .cons b h (AllocsRefine.filter p t)
    · exact AllocsRefine.filter p t

namespace Mem.Refines

variable {m m' : Mem}

theorem find? (h : Mem.Refines m m') (b : Blk) :
    (m.find? b = none ∧ m'.find? b = none) ∨
      ∃ a a', m.find? b = some a ∧ m'.find? b = some a' ∧ Alloc.Refines a a' := by
  have := AllocsRefine.find? b h.blocks
  rcases m with ⟨⟨l⟩, n⟩; rcases m' with ⟨⟨l'⟩, n'⟩
  simpa [Mem.find?] using this

theorem find?_some (h : Mem.Refines m m') {b : Blk} {a : Alloc} (ha : m.find? b = some a) :
    ∃ a', m'.find? b = some a' ∧ Alloc.Refines a a' := by
  rcases h.find? b with ⟨h1, _⟩ | ⟨a1, a2, h1, h2, h3⟩
  · rw [h1] at ha; cases ha
  · rw [h1] at ha; cases ha; exact ⟨a2, h2, h3⟩

theorem set (h : Mem.Refines m m') (b : Blk) {a a' : Alloc} (ha : Alloc.Refines a a') :
    Mem.Refines (m.set b a) (m'.set b a') := by
  rcases m with ⟨⟨l⟩, n⟩; rcases m' with ⟨⟨l'⟩, n'⟩
  obtain ⟨hn, hl⟩ := h
  simp only at hn hl
  have hk := hl.keys
  have hidx : l.findIdx? (·.1 == b) = l'.findIdx? (·.1 == b) := by
    have e1 : l.findIdx? (·.1 == b) = (l.map (·.1)).findIdx? (· == b) := by
      rw [List.findIdx?_map]; rfl
    have e2 : l'.findIdx? (·.1 == b) = (l'.map (·.1)).findIdx? (· == b) := by
      rw [List.findIdx?_map]; rfl
    rw [e1, e2, hk]
  unfold Mem.set
  simp only [List.findIdx?_toArray]
  rw [← hidx]
  cases hi : l.findIdx? (·.1 == b) with
  | none => exact ⟨hn, by simpa using hl.append (.cons b ha .nil)⟩
  | some i =>
    refine ⟨hn, ?_⟩
    simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]
    refine AllocsRefine.set i b hl ha fun c hc => ?_
    have := List.findIdx?_eq_some_iff_getElem.1 hi
    obtain ⟨hlt, hp, -⟩ := this
    simp only [List.getElem?_eq_getElem hlt, Option.map_some, Option.some.injEq] at hc
    subst hc; simpa using hp

theorem poisonBlock (h : Mem.Refines m m') (b : Blk) :
    Mem.Refines (m.poisonBlock b) (m'.poisonBlock b) := by
  unfold Mem.poisonBlock
  rcases h.find? b with ⟨h1, h2⟩ | ⟨a, a', h1, h2, ha⟩
  · rw [h1, h2]; exact h
  · rw [h1, h2]
    exact h.set b ⟨ha.writable, by
      simp only [Array.toList_replicate, ha.size_eq]; exact BytesRefine.refl _⟩

theorem free (h : Mem.Refines m m') (b : Blk) : Mem.Refines (m.free b) (m'.free b) := by
  rcases m with ⟨⟨l⟩, n⟩; rcases m' with ⟨⟨l'⟩, n'⟩
  obtain ⟨hn, hl⟩ := h
  exact ⟨hn, by simpa [Mem.free] using hl.filter (· != b)⟩

theorem allocHeap (h : Mem.Refines m m') {d d' : Array Byte} (hd : BytesRefineA d d') :
    (m.allocHeap d).1 = (m'.allocHeap d').1 ∧
      Mem.Refines (m.allocHeap d).2 (m'.allocHeap d').2 := by
  have hs := (h.set (Blk.heap m'.nextHeap) (a := { data := d }) (a' := { data := d' }) ⟨rfl, hd⟩)
  unfold Mem.allocHeap
  simp only [h.nextHeap]
  refine ⟨by simp, ?_, ?_⟩
  · simp
  · exact hs.blocks

theorem read (h : Mem.Refines m m') {p : Ptr} {n : Nat} {bs : Array Byte}
    (hr : m.read p n = some bs) : ∃ bs', m'.read p n = some bs' ∧ BytesRefineA bs bs' := by
  unfold Mem.read at hr ⊢
  by_cases hn : (n == 0) = true
  · simp only [hn, ite_true] at hr ⊢; cases hr; exact ⟨_, rfl, BytesRefine.nil⟩
  · simp only [hn, Bool.false_eq_true, ite_false] at hr ⊢
    cases ha : m.find? p.blk with
    | none => rw [ha] at hr; cases hr
    | some a =>
      obtain ⟨a', ha', har⟩ := h.find?_some ha
      rw [ha] at hr; rw [ha']
      dsimp only [bind, Option.bind] at hr ⊢
      rw [← har.size_eq]
      split at hr
      · next hle =>
        cases hr
        exact ⟨_, by simp [hle], BytesRefineA.extract har.data _ _⟩
      · cases hr

/-- The bytes `write` puts into an allocation. -/
theorem write_fold (off : Nat) {bs bs' : Array Byte} (hb : BytesRefineA bs bs') :
    ∀ (l : List Nat) {d d' : Array Byte}, BytesRefineA d d' →
      BytesRefineA (l.foldl (fun d i => d.set! (off + i) bs[i]!) d)
        (l.foldl (fun d i => d.set! (off + i) bs'[i]!) d')
  | [], _, _, hd => hd
  | i :: l, _, _, hd => write_fold off hb l (hd.set! _ (hb.getElem! i))

theorem write (h : Mem.Refines m m') {p : Ptr} {bs bs' : Array Byte} (hb : BytesRefineA bs bs')
    {m1 : Mem} (hw : m.write p bs = some m1) :
    ∃ m1', m'.write p bs' = some m1' ∧ Mem.Refines m1 m1' := by
  unfold Mem.write at hw ⊢
  have hsz := hb.size_eq
  by_cases he : bs.isEmpty = true
  · have he' : bs'.isEmpty = true := by rw [← he]; unfold Array.isEmpty; rw [hsz]
    simp only [he, he', ite_true] at hw ⊢; cases hw; exact ⟨_, rfl, h⟩
  · have he' : ¬ bs'.isEmpty = true := by rw [show bs'.isEmpty = bs.isEmpty by unfold Array.isEmpty; rw [hsz]]; exact he
    simp only [he, he', Bool.false_eq_true, ite_false] at hw ⊢
    cases ha : m.find? p.blk with
    | none => rw [ha] at hw; cases hw
    | some a =>
      obtain ⟨a', ha', har⟩ := h.find?_some ha
      rw [ha] at hw; rw [ha']
      dsimp only [bind, Option.bind] at hw ⊢
      rw [← har.size_eq, ← har.writable, ← hsz]
      split at hw
      · next hc =>
        cases hw
        let d' := List.foldl (fun d i => d.set! (p.off.toNat + i) bs'[i]!) a'.data
          (List.range bs.size)
        refine ⟨m'.set p.blk { writable := a.writable, data := d' }, by simp [hc, d'], ?_⟩
        exact h.set _ ⟨rfl, write_fold _ hb _ har.data⟩
      · cases hw

end Mem.Refines

end GoFV.SSA.Sem
