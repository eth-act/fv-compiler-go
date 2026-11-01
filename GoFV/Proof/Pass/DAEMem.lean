import GoFV.Proof.Pass.DSEMem
import GoFV.Proof.ValRefine
import GoFV.SSA.Sem.FrameSafe

/-!
# dead auto elim: memories equal outside frame temporaries

`Mem.EqOff U m m'` (`Sem/FrameSafe`) as a relation on the allocation lists (`AllocsRel`): the
same blocks in order, sizes and writability, the same bytes outside the blocks `U`. Lemmas for
the memory operations dead auto elim's simulation meets: the same write on both sides
(`EqOff.write`), a source-only write into a block of `U` (`EqOff.write_left`), `poisonBlock`,
reads and loads of blocks outside `U`, and the frame removal at returns and panics
(`EqOff.freeFrame`, `EqOff.dropFrames`): when `U` holds only frame temporaries of activation 0,
the memories become equal.
-/

namespace GoFV.Proof.DAE

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof.DSE

/-- `U` holds only frame temporaries of activation 0. -/
def TempU (U : Blk → Prop) : Prop := ∀ b, U b → ∃ n, b = .temp 0 n

/-- Entries of one block: the same size and writability, the same bytes outside `U`. -/
def ARel (U : Blk → Prop) (e e' : Blk × Alloc) : Prop :=
  e'.1 = e.1 ∧ e'.2.data.size = e.2.data.size ∧ e'.2.writable = e.2.writable ∧
    (¬ U e.1 → e'.2.data = e.2.data)

theorem ARel.refl (U : Blk → Prop) (e : Blk × Alloc) : ARel U e e :=
  ⟨rfl, rfl, rfl, fun _ => rfl⟩

/-- Allocation lists related entrywise. -/
inductive AllocsRel (U : Blk → Prop) : List (Blk × Alloc) → List (Blk × Alloc) → Prop where
  | nil : AllocsRel U [] []
  | cons {e e' : Blk × Alloc} {l l' : List (Blk × Alloc)} : ARel U e e' → AllocsRel U l l' →
      AllocsRel U (e :: l) (e' :: l')

theorem AllocsRel.refl (U : Blk → Prop) : (l : List (Blk × Alloc)) → AllocsRel U l l
  | [] => .nil
  | e :: l => .cons (ARel.refl U e) (AllocsRel.refl U l)

theorem AllocsRel.length {U : Blk → Prop} : {l l' : List (Blk × Alloc)} → AllocsRel U l l' →
    l'.length = l.length
  | _, _, .nil => rfl
  | _, _, .cons _ t => by simp [t.length]

theorem AllocsRel.get {U : Blk → Prop} : {l l' : List (Blk × Alloc)} → AllocsRel U l l' →
    ∀ (i : Nat) e e', l[i]? = some e → l'[i]? = some e' → ARel U e e'
  | _, _, .nil, _, _, _, h, _ => by simp at h
  | _, _, .cons h t, 0, _, _, h1, h2 => by simp at h1 h2; subst h1 h2; exact h
  | _, _, .cons _ t, i + 1, _, _, h1, h2 => t.get i _ _ (by simpa using h1) (by simpa using h2)

theorem AllocsRel.of_get {U : Blk → Prop} : {l l' : List (Blk × Alloc)} → l'.length = l.length →
    (∀ (i : Nat) e e', l[i]? = some e → l'[i]? = some e' → ARel U e e') → AllocsRel U l l'
  | [], [], _, _ => .nil
  | e :: l, e' :: l', hl, h =>
    .cons (h 0 e e' rfl rfl) (AllocsRel.of_get (by simpa using hl)
      fun i a a' h1 h2 => h (i + 1) a a' (by simpa using h1) (by simpa using h2))
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

/-- `EqOff` on the allocation lists. -/
theorem eqOff_iff {U : Blk → Prop} {m m' : Mem} :
    Mem.EqOff U m m' ↔ m.nextHeap = m'.nextHeap ∧ m.nextAct = m'.nextAct ∧
      AllocsRel U m.blocks.toList m'.blocks.toList := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, h2, AllocsRel.of_get (by simp [h3]) fun i e e' he he' => ?_⟩
    rw [Array.getElem?_toList] at he he'
    obtain ⟨b, a⟩ := e
    obtain ⟨b', a'⟩ := e'
    obtain ⟨hb, hs, hw, hd⟩ := h4 i b b' a a' he he'
    subst hb
    exact ⟨rfl, hs.symm, hw.symm, fun hu => (hd hu).symm⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, h2, by simpa using h3.length.symm, fun i b b' a a' he he' => ?_⟩
    have := h3.get i (b, a) (b', a') (by rw [Array.getElem?_toList]; exact he)
      (by rw [Array.getElem?_toList]; exact he')
    obtain ⟨hb, hs, hw, hd⟩ := this
    simp only at hb hs hw hd
    subst hb
    exact ⟨rfl, hs.symm, hw.symm, fun hu => (hd hu).symm⟩

theorem EqOff.refl (U : Blk → Prop) (m : Mem) : Mem.EqOff U m m :=
  eqOff_iff.2 ⟨rfl, rfl, AllocsRel.refl U _⟩

/-! ## Lists -/

theorem AllocsRel.find {U : Blk → Prop} : {l l' : List (Blk × Alloc)} → AllocsRel U l l' →
    ∀ b, ((l.find? (·.1 == b)).map (·.2) = none ∧ (l'.find? (·.1 == b)).map (·.2) = none) ∨
      ∃ a a', (l.find? (·.1 == b)).map (·.2) = some a ∧
        (l'.find? (·.1 == b)).map (·.2) = some a' ∧ ARel U (b, a) (b, a')
  | _, _, .nil, _ => .inl ⟨rfl, rfl⟩
  | e :: l, e' :: l', .cons h t, b => by
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp only [List.find?_cons, h1]
    by_cases hb : (e.1 == b) = true
    · have := beq_iff_eq.1 hb
      subst this
      simp only [beq_self_eq_true, Option.map_some]
      exact .inr ⟨_, _, rfl, rfl, rfl, h2, h3, h4⟩
    · simp only [hb]
      exact t.find b

theorem AllocsRel.setL {U : Blk → Prop} {b : Blk} {a a' : Alloc} (ha : ARel U (b, a) (b, a')) :
    {l l' : List (Blk × Alloc)} → AllocsRel U l l' → AllocsRel U (setL b a l) (setL b a' l')
  | _, _, .nil => .cons ha .nil
  | e :: l, e' :: l', .cons h t => by
    simp only [DSE.setL, h.1]
    by_cases hb : (e.1 == b) = true
    · simp only [hb, ite_true]; exact .cons ha t
    · simp only [hb, Bool.false_eq_true, ite_false]; exact .cons h (AllocsRel.setL ha t)

theorem AllocsRel.filter {U : Blk → Prop} (F : Blk × Alloc → Bool)
    (hF : ∀ b a a', F (b, a) = F (b, a')) : {l l' : List (Blk × Alloc)} →
    AllocsRel U l l' → AllocsRel U (l.filter F) (l'.filter F)
  | _, _, .nil => .nil
  | e :: l, e' :: l', .cons h t => by
    have he : F e' = F e := by
      obtain ⟨b, a⟩ := e; obtain ⟨b', a'⟩ := e'
      obtain ⟨h1, -⟩ := h; simp only at h1; subst h1; exact hF _ _ _
    simp only [List.filter_cons, he]
    split
    · exact .cons h (t.filter F hF)
    · exact t.filter F hF

theorem AllocsRel.eq {U : Blk → Prop} : {l l' : List (Blk × Alloc)} → AllocsRel U l l' →
    (∀ e ∈ l, ¬ U e.1) → l' = l
  | _, _, .nil, _ => rfl
  | e :: l, e' :: l', .cons h t, hu => by
    obtain ⟨h1, h2, h3, h4⟩ := h
    have hd := h4 (hu e List.mem_cons_self)
    obtain ⟨b, ⟨d, w⟩⟩ := e
    obtain ⟨b', ⟨d', w'⟩⟩ := e'
    simp only at h1 h3 hd
    subst h1 h3 hd
    rw [t.eq fun x hx => hu x (List.mem_cons_of_mem _ hx)]

/-! ## Memories -/

theorem EqOff.find {U : Blk → Prop} {m m' : Mem} (h : Mem.EqOff U m m') (b : Blk) :
    (m.find? b = none ∧ m'.find? b = none) ∨
      ∃ a a', m.find? b = some a ∧ m'.find? b = some a' ∧ ARel U (b, a) (b, a') := by
  rw [find?_toList, find?_toList]
  exact (eqOff_iff.1 h).2.2.find b

theorem EqOff.set {U : Blk → Prop} {m m' : Mem} (h : Mem.EqOff U m m') {b : Blk} {a a' : Alloc}
    (ha : ARel U (b, a) (b, a')) : Mem.EqOff U (m.set b a) (m'.set b a') := by
  obtain ⟨h1, h2, h3⟩ := eqOff_iff.1 h
  refine eqOff_iff.2 ⟨by rw [set_nextHeap, set_nextHeap, h1], by rw [set_nextAct, set_nextAct, h2], ?_⟩
  rw [set_toList, set_toList]
  exact h3.setL ha

/-- **The same write on both sides.** -/
theorem EqOff.write {U : Blk → Prop} {m m' m1 : Mem} (h : Mem.EqOff U m m') {p : Ptr}
    {bs : Array Byte} (hw : m.write p bs = some m1) :
    ∃ m1', m'.write p bs = some m1' ∧ Mem.EqOff U m1 m1' := by
  unfold Mem.write at hw ⊢
  by_cases he : bs.isEmpty = true
  · simp only [he, ite_true] at hw ⊢
    cases hw
    exact ⟨m', rfl, h⟩
  simp only [he, Bool.false_eq_true, ite_false] at hw ⊢
  rcases EqOff.find h p.blk with ⟨h1, -⟩ | ⟨a, a', ha, ha', hA⟩
  · rw [h1] at hw; cases hw
  rw [ha] at hw
  rw [ha']
  simp only [Option.bind_eq_bind, Option.bind_some] at hw ⊢
  obtain ⟨-, hs, hwr, hd⟩ := hA
  simp only at hs hwr hd
  rw [hwr, hs]
  split at hw
  · rename_i hc
    cases hw
    simp only [hc, ↓reduceIte]
    refine ⟨_, rfl, EqOff.set h ⟨rfl, ?_, rfl, fun hu => ?_⟩⟩
    · simp only [CSE.Mem.foldl_set_size, hs]
    · simp only; rw [hd hu]
  · cases hw

/-- Memories with the same allocations have the same writable ranges. -/
theorem EqOff.canWrite {U : Blk → Prop} {m m' : Mem} (h : Mem.EqOff U m m') (p : Ptr) (n : Nat) :
    m'.canWrite p n = m.canWrite p n := by
  unfold Mem.canWrite
  rcases EqOff.find h p.blk with ⟨h1, h2⟩ | ⟨a, a', ha, ha', hA⟩
  · rw [h1, h2]
  · obtain ⟨-, hs, hwr, -⟩ := hA
    rw [ha, ha']; dsimp only at hs hwr ⊢; rw [hs, hwr]

theorem EqOff.outargsOK {U : Blk → Prop} {m m' : Mem} (h : Mem.EqOff U m m') (tabs : Tables)
    (act : Nat) (ps : List ABIParam) : outargsOK tabs act m' ps = outargsOK tabs act m ps := by
  unfold Sem.outargsOK
  simp only [EqOff.canWrite h]

/-- **A source-only write into a block of `U`.** -/
theorem EqOff.write_left {U : Blk → Prop} {m m' m1 : Mem} (h : Mem.EqOff U m m') {p : Ptr}
    {bs : Array Byte} (hw : m.write p bs = some m1) (hu : U p.blk) : Mem.EqOff U m1 m' := by
  unfold Mem.write at hw
  by_cases he : bs.isEmpty = true
  · simp only [he, ite_true] at hw
    cases hw; exact h
  simp only [he, Bool.false_eq_true, ite_false] at hw
  rcases EqOff.find h p.blk with ⟨h1, -⟩ | ⟨a, a', ha, ha', hA⟩
  · rw [h1] at hw; cases hw
  rw [ha] at hw
  simp only [Option.bind_eq_bind, Option.bind_some] at hw
  split at hw
  · cases hw
    rw [← set_self ha']
    obtain ⟨-, hs, hwr, -⟩ := hA
    exact EqOff.set h ⟨rfl, by simp only [CSE.Mem.foldl_set_size]; exact hs, hwr,
      fun hn => absurd hu hn⟩
  · cases hw

/-- `poisonBlock` on both sides. -/
theorem EqOff.poison {U : Blk → Prop} {m m' : Mem} (h : Mem.EqOff U m m') (b : Blk) :
    Mem.EqOff U (m.poisonBlock b) (m'.poisonBlock b) := by
  unfold Mem.poisonBlock
  rcases EqOff.find h b with ⟨h1, h2⟩ | ⟨a, a', ha, ha', hA⟩
  · rw [h1, h2]; exact h
  · rw [ha, ha']
    obtain ⟨-, hs, hwr, -⟩ := hA
    exact EqOff.set h ⟨rfl, by simp [hs], hwr, fun _ => by simp [hs]⟩

/-- `poisonBlock` of a block of `U` on the source side only. -/
theorem EqOff.poison_left {U : Blk → Prop} {m m' : Mem} (h : Mem.EqOff U m m') {b : Blk}
    (hu : U b) : Mem.EqOff U (m.poisonBlock b) m' := by
  unfold Mem.poisonBlock
  rcases EqOff.find h b with ⟨h1, -⟩ | ⟨a, a', ha, ha', hA⟩
  · rw [h1]; exact h
  · rw [ha, ← set_self ha']
    obtain ⟨-, hs, hwr, -⟩ := hA
    exact EqOff.set h ⟨rfl, by simp [hs], hwr, fun hn => absurd hu hn⟩

/-- A read of a block outside `U`. -/
theorem EqOff.read {U : Blk → Prop} {m m' : Mem} (h : Mem.EqOff U m m') (p : Ptr) (n : Nat)
    (hu : ¬ U p.blk) : m'.read p n = m.read p n := by
  unfold Mem.read
  rcases EqOff.find h p.blk with ⟨h1, h2⟩ | ⟨a, a', ha, ha', hA⟩
  · rw [h1, h2]
  · rw [ha, ha']
    obtain ⟨-, -, -, hd⟩ := hA
    simp only at hd
    simp only [Option.bind_eq_bind, Option.bind_some, hd hu]

theorem EqOff.load {U : Blk → Prop} {m m' : Mem} (h : Mem.EqOff U m m') (t : Ty) (p : Ptr)
    (hu : ¬ U p.blk) : m'.load t p = m.load t p := by
  unfold Mem.load
  simp only [EqOff.read h p _ hu]

/-- Filtering the allocations by a block predicate that drops every block of `U`: equal
memories. -/
theorem EqOff.filter_eq {U : Blk → Prop} {m m' : Mem} (h : Mem.EqOff U m m')
    (F : Blk × Alloc → Bool) (hF : ∀ b a a', F (b, a) = F (b, a'))
    (hU : ∀ e, U e.1 → F e = false) :
    ({ m' with blocks := m'.blocks.filter F } : Mem) = { m with blocks := m.blocks.filter F } := by
  obtain ⟨h1, h2, h3⟩ := eqOff_iff.1 h
  have key := (h3.filter F hF).eq fun e he hu => by
    have := (List.mem_filter.1 he).2
    rw [hU e hu] at this; cases this
  obtain ⟨⟨l⟩, nh, na⟩ := m
  obtain ⟨⟨l'⟩, nh', na'⟩ := m'
  simp only at h1 h2 key
  subst h1 h2
  simp only [Mem.mk.injEq, and_true]
  apply Array.toList_inj.1
  simpa using key

/-- The frame removal at a return: equal memories. -/
theorem EqOff.freeFrame {U : Blk → Prop} (hU : TempU U) {m m' : Mem} (h : Mem.EqOff U m m') :
    m'.freeFrame 0 = m.freeFrame 0 := by
  unfold Mem.freeFrame
  refine EqOff.filter_eq h _ (fun _ _ _ => rfl) fun e hu => ?_
  obtain ⟨n, hn⟩ := hU _ hu
  obtain ⟨b, a⟩ := e
  simp only at hn
  subst hn
  rfl

/-- The frame removal at a panic: equal memories. -/
theorem EqOff.dropFrames {U : Blk → Prop} (hU : TempU U) {m m' : Mem} (h : Mem.EqOff U m m') :
    m'.dropFrames 0 = m.dropFrames 0 := by
  unfold Mem.dropFrames
  refine EqOff.filter_eq h _ (fun _ _ _ => rfl) fun e hu => ?_
  obtain ⟨n, hn⟩ := hU _ hu
  obtain ⟨b, a⟩ := e
  simp only at hn
  subst hn
  rfl

end GoFV.Proof.DAE
