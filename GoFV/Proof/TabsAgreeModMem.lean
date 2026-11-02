import GoFV.Proof.Pass.DAEAvoid
import GoFV.Proof.Retype
import GoFV.Proof.Eval

/-!
# Running in tables with extra frame temporaries: memories and registers

`EqX X m m'`: the memories are equal once the blocks `X` are removed (`Mem.erase`). The
source's run (in the input tables) and the target's (the same function in tables with extra
frame temporaries `X`) keep their memories `EqX`: an access to a block outside `X` reads the
same bytes (`EqX.read`, `EqX.load`) and writes alike (`EqX.write`, `EqX.set`), `poisonBlock`
keeps them related at any block (`EqX.poison`), and the frame removal at returns and panics makes
them equal (`EqX.freeFrame`, `EqX.dropFrames`) when `X` holds frame temporaries of activation 0.

`VR X`: related registers (equal, memories `EqX`, tuples componentwise), as `dead auto elim`'s
`DAE.VR` with `EqX` for `Mem.EqOff`.
-/

namespace GoFV.Proof.TabsMod

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof.DSE

/-- The memories are equal without the blocks `X`. -/
def EqX (X : Blk → Bool) (m m' : Mem) : Prop := m.erase X = m'.erase X

/-- `X` holds only frame temporaries of activation 0. -/
def TempX (X : Blk → Bool) : Prop := ∀ b, X b = true → ∃ n, b = .temp 0 n

section
variable {X : Blk → Bool}

theorem tempU_of (hX : TempX X) : DAE.TempU (X · = true) := DAE.TempU0.tempU hX

theorem mem_ext {m m' : Mem} (h1 : m.blocks.toList = m'.blocks.toList)
    (h2 : m.nextHeap = m'.nextHeap) (h3 : m.nextAct = m'.nextAct) : m = m' := by
  obtain ⟨⟨l⟩, nh, na⟩ := m
  obtain ⟨⟨l'⟩, nh', na'⟩ := m'
  simp only at h1 h2 h3
  subst h1 h2 h3
  rfl

theorem erase_toList (m : Mem) :
    (m.erase X).blocks.toList = m.blocks.toList.filter fun e => !X e.1 := by
  simp [Mem.erase]

theorem EqX.refl (X : Blk → Bool) (m : Mem) : EqX X m m := rfl

theorem EqX.trans {a b c : Mem} (h1 : EqX X a b) (h2 : EqX X b c) : EqX X a c := Eq.trans h1 h2

theorem EqX.nextHeap {m m' : Mem} (h : EqX X m m') : m.nextHeap = m'.nextHeap :=
  show (m.erase X).nextHeap = (m'.erase X).nextHeap from congrArg Mem.nextHeap h

theorem EqX.nextAct {m m' : Mem} (h : EqX X m m') : m.nextAct = m'.nextAct :=
  show (m.erase X).nextAct = (m'.erase X).nextAct from congrArg Mem.nextAct h

/-! ## Allocation lists -/

theorem filter_find {b : Blk} (hb : X b = false) : ∀ l : List (Blk × Alloc),
    (l.filter fun e => !X e.1).find? (·.1 == b) = l.find? (·.1 == b)
  | [] => rfl
  | e :: l => by
    by_cases hx : X e.1 = true
    · have hne : (e.1 == b) = false := by
        rw [beq_eq_false_iff_ne]; rintro rfl; rw [hx] at hb; cases hb
      simp only [List.filter_cons, hx, Bool.not_true, Bool.false_eq_true, ite_false,
        List.find?_cons, hne, filter_find hb l]
    · simp only [Bool.not_eq_true] at hx
      simp only [List.filter_cons, hx, Bool.not_false, ite_true, List.find?_cons, filter_find hb l]

theorem filter_setL {b : Blk} {a : Alloc} (hb : X b = false) : ∀ l : List (Blk × Alloc),
    (setL b a l).filter (fun e => !X e.1) = setL b a (l.filter fun e => !X e.1)
  | [] => by simp [setL, hb]
  | e :: l => by
    by_cases he : (e.1 == b) = true
    · obtain ⟨b', a'⟩ := e
      have : b' = b := beq_iff_eq.1 he
      subst this
      simp [setL, hb]
    · by_cases hx : X e.1 = true
      · simp only [setL, he, Bool.false_eq_true, ite_false, List.filter_cons, hx, Bool.not_true,
          filter_setL hb l]
      · simp only [Bool.not_eq_true] at hx
        simp only [setL, he, Bool.false_eq_true, ite_false, List.filter_cons, hx, Bool.not_false,
          ite_true, filter_setL hb l]

theorem filter_setL_X {b : Blk} {a : Alloc} (hb : X b = true) : ∀ l : List (Blk × Alloc),
    (setL b a l).filter (fun e => !X e.1) = l.filter fun e => !X e.1
  | [] => by simp [setL, hb]
  | e :: l => by
    by_cases he : (e.1 == b) = true
    · obtain ⟨b', a'⟩ := e
      have : b' = b := beq_iff_eq.1 he
      subst this
      simp [setL, hb]
    · simp only [setL, he, Bool.false_eq_true, ite_false, List.filter_cons, filter_setL_X hb l]

/-! ## Memory operations -/

theorem erase_find {m : Mem} {b : Blk} (hb : X b = false) : (m.erase X).find? b = m.find? b := by
  rw [find?_toList, find?_toList, erase_toList, filter_find hb]

theorem EqX.find {m m' : Mem} (h : EqX X m m') {b : Blk} (hb : X b = false) :
    m'.find? b = m.find? b := by
  rw [← erase_find hb, ← h, erase_find hb]

theorem erase_set {m : Mem} {b : Blk} {a : Alloc} (hb : X b = false) :
    (m.set b a).erase X = (m.erase X).set b a := by
  refine mem_ext ?_ ?_ ?_
  · rw [erase_toList, set_toList, set_toList, erase_toList, filter_setL hb]
  · show (m.set b a).nextHeap = ((m.erase X).set b a).nextHeap
    rw [set_nextHeap, set_nextHeap]; rfl
  · show (m.set b a).nextAct = ((m.erase X).set b a).nextAct
    rw [set_nextAct, set_nextAct]; rfl

theorem erase_set_X {m : Mem} {b : Blk} {a : Alloc} (hb : X b = true) :
    (m.set b a).erase X = m.erase X := by
  refine mem_ext ?_ ?_ ?_
  · rw [erase_toList, set_toList, erase_toList, filter_setL_X hb]
  · show (m.set b a).nextHeap = m.nextHeap
    rw [set_nextHeap]
  · show (m.set b a).nextAct = m.nextAct
    rw [set_nextAct]

theorem EqX.set {m m' : Mem} (h : EqX X m m') (b : Blk) (a : Alloc) :
    EqX X (m.set b a) (m'.set b a) := by
  cases hb : X b
  · unfold EqX; rw [erase_set hb, erase_set hb, h]
  · unfold EqX; rw [erase_set_X hb, erase_set_X hb, h]

/-- A write to a block outside `X` commutes with the removal of `X`. -/
theorem erase_write {m : Mem} {p : Ptr} (bs : Array Byte) (hb : X p.blk = false) :
    (m.erase X).write p bs = (m.write p bs).map (Mem.erase X) := by
  unfold Mem.write
  by_cases he : bs.isEmpty = true
  · simp only [he, ↓reduceIte]; rfl
  · simp only [he, Bool.false_eq_true, ↓reduceIte]
    rw [erase_find hb]
    cases m.find? p.blk with
    | none => rfl
    | some a =>
      dsimp only [bind, Option.bind]
      split
      · simp only [Option.map_some, erase_set hb]
      · rfl

/-- **The same write on both sides** (outside `X`). -/
theorem EqX.write {m m' m1 : Mem} (h : EqX X m m') {p : Ptr} {bs : Array Byte}
    (hb : X p.blk = false) (hw : m.write p bs = some m1) :
    ∃ m1', m'.write p bs = some m1' ∧ EqX X m1 m1' := by
  have h1 := erase_write (m := m) bs hb
  have h2 := erase_write (m := m') bs hb
  rw [hw] at h1
  rw [← h, h1] at h2
  cases hw' : m'.write p bs with
  | none => rw [hw'] at h2; cases h2
  | some m1' =>
    rw [hw'] at h2
    simp only [Option.map_some, Option.some.injEq] at h2
    exact ⟨m1', rfl, h2⟩

theorem erase_read {m : Mem} {p : Ptr} (n : Nat) (hb : X p.blk = false) :
    (m.erase X).read p n = m.read p n := by
  unfold Mem.read
  rw [erase_find hb]

/-- A read of a block outside `X`. -/
theorem EqX.read {m m' : Mem} (h : EqX X m m') (p : Ptr) (n : Nat) (hb : X p.blk = false) :
    m'.read p n = m.read p n := by
  rw [← erase_read n hb, ← h, erase_read n hb]

theorem EqX.load {m m' : Mem} (h : EqX X m m') (t : Ty) (p : Ptr) (hb : X p.blk = false) :
    m'.load t p = m.load t p := by
  unfold Mem.load
  simp only [EqX.read h p _ hb]

/-- The same writable stack-argument slots (`outargs` is not in `X`). -/
theorem EqX.outargsOK (hX : TempX X) {m m' : Mem} (h : EqX X m m') (tabs : Tables) (act : Nat)
    (ps : List ABIParam) : outargsOK tabs act m' ps = outargsOK tabs act m ps := by
  have hb : X (.outargs act) = false := by
    cases hx : X (.outargs act)
    · rfl
    · obtain ⟨n, hn⟩ := hX _ hx; cases hn
  unfold Sem.outargsOK Mem.canWrite
  simp only [EqX.find h hb]

/-- `poisonBlock` on both sides (any block). -/
theorem EqX.poison {m m' : Mem} (h : EqX X m m') (b : Blk) :
    EqX X (m.poisonBlock b) (m'.poisonBlock b) := by
  cases hb : X b
  · unfold Mem.poisonBlock
    rw [EqX.find h hb]
    cases m.find? b with
    | none => exact h
    | some a => exact EqX.set h b _
  · have key : ∀ m : Mem, (m.poisonBlock b).erase X = m.erase X := by
      intro m
      unfold Mem.poisonBlock
      split
      · exact erase_set_X hb
      · rfl
    unfold EqX
    rw [key, key, h]

/-- `poisonBelow` on both sides (any block). -/
theorem EqX.poisonBelow {m m' : Mem} (h : EqX X m m') (b : Blk) (n : Nat) :
    EqX X (m.poisonBelow b n) (m'.poisonBelow b n) := by
  cases hb : X b
  · unfold Mem.poisonBelow
    rw [EqX.find h hb]
    cases m.find? b with
    | none => exact h
    | some a => exact EqX.set h b _
  · have key : ∀ m : Mem, (m.poisonBelow b n).erase X = m.erase X := by
      intro m
      unfold Mem.poisonBelow
      split
      · exact erase_set_X hb
      · rfl
    unfold EqX
    rw [key, key, h]

/-- Filtering by a block predicate that drops every block of `X` sees through `erase`. -/
theorem filter_erase (F : Blk × Alloc → Bool) (hF : ∀ e, X e.1 = true → F e = false) (m : Mem) :
    ({ m with blocks := (m.erase X).blocks.filter F } : Mem) = { m with blocks := m.blocks.filter F } := by
  refine mem_ext ?_ rfl rfl
  simp only [Array.toList_filter, erase_toList, List.filter_filter]
  apply List.filter_congr
  intro e _
  cases hx : X e.1
  · simp
  · simp [hF e hx]

theorem filter_eq_of {m m' : Mem} (h : EqX X m m') (F : Blk × Alloc → Bool)
    (hF : ∀ e, X e.1 = true → F e = false) :
    ({ m with blocks := m.blocks.filter F } : Mem) = { m' with blocks := m'.blocks.filter F } := by
  rw [← filter_erase F hF m, ← filter_erase F hF m']
  have h1 : (m.erase X).blocks = (m'.erase X).blocks := congrArg Mem.blocks h
  have hn : m.nextHeap = m'.nextHeap := EqX.nextHeap h
  have ha : m.nextAct = m'.nextAct := EqX.nextAct h
  rw [h1]
  exact mem_ext rfl hn ha

/-- The frame removal at a return: equal memories. -/
theorem EqX.freeFrame (hX : TempX X) {m m' : Mem} (h : EqX X m m') :
    m.freeFrame 0 = m'.freeFrame 0 := by
  unfold Mem.freeFrame
  refine filter_eq_of h _ fun e hx => ?_
  obtain ⟨n, hn⟩ := hX _ hx
  obtain ⟨b, a⟩ := e
  simp only at hn
  subst hn
  rfl

/-- The frame removal at a panic: equal memories. -/
theorem EqX.dropFrames (hX : TempX X) {m m' : Mem} (h : EqX X m m') :
    m.dropFrames 0 = m'.dropFrames 0 := by
  unfold Mem.dropFrames
  refine filter_eq_of h _ fun e hx => ?_
  obtain ⟨n, hn⟩ := hX _ hx
  obtain ⟨b, a⟩ := e
  simp only at hn
  subst hn
  rfl

end

/-! ## Related registers -/

mutual
/-- Related registers: equal, memories equal up to the blocks `X`, or tuples related
componentwise. -/
inductive VR (X : Blk → Bool) : Val → Val → Prop where
  | refl (v : Val) : VR X v v
  | mem {m m' : Mem} : EqX X m m' → VR X (.mem m) (.mem m')
  | tuple {vs ws : List Val} : VRL X vs ws → VR X (.tuple vs) (.tuple ws)
/-- Related lists of registers. -/
inductive VRL (X : Blk → Bool) : List Val → List Val → Prop where
  | nil : VRL X [] []
  | cons {a b : Val} {as bs : List Val} : VR X a b → VRL X as bs → VRL X (a :: as) (b :: bs)
end

variable {X : Blk → Bool}

theorem VRL.refl : (vs : List Val) → VRL X vs vs
  | [] => .nil
  | v :: vs => .cons (.refl v) (VRL.refl vs)

theorem VRL.append : {as bs cs ds : List Val} → VRL X as bs → VRL X cs ds →
    VRL X (as ++ cs) (bs ++ ds)
  | _, _, _, _, .nil, h' => h'
  | _, _, _, _, .cons h1 t, h' => .cons h1 (VRL.append t h')

theorem VRL.length : {as bs : List Val} → VRL X as bs → bs.length = as.length
  | _, _, .nil => rfl
  | _, _, .cons _ t => by simp [VRL.length t]

theorem VRL.get : {as bs : List Val} → VRL X as bs →
    ∀ {i : Nat} {a : Val}, as[i]? = some a → ∃ b, bs[i]? = some b ∧ VR X a b
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons h1 _, 0, _, hi => by simp at hi; subst hi; exact ⟨_, rfl, h1⟩
  | _, _, .cons _ t, i + 1, _, hi => VRL.get t (by simpa using hi)

theorem VRL.getD {as bs : List Val} (h : VRL X as bs) (i : Nat) :
    VR X (as.getD i .poison) (bs.getD i .poison) := by
  cases ha : as[i]? with
  | none =>
    have hb : bs[i]? = none := by
      rw [List.getElem?_eq_none_iff] at ha ⊢; rw [h.length]; exact ha
    simp [List.getD, ha, hb]; exact .refl _
  | some a =>
    obtain ⟨b, hb, hab⟩ := h.get ha
    simp [List.getD, ha, hb]; exact hab

theorem VRL.dropLast : {as bs : List Val} → VRL X as bs → VRL X as.dropLast bs.dropLast
  | _, _, .nil => .nil
  | _, _, .cons _ .nil => .nil
  | _, _, .cons h1 (.cons h2 t) => .cons h1 (VRL.dropLast (.cons h2 t))

theorem VRL.getLast? : {as bs : List Val} → VRL X as bs →
    (as.getLast? = none ∧ bs.getLast? = none) ∨
      ∃ a b, as.getLast? = some a ∧ bs.getLast? = some b ∧ VR X a b
  | _, _, .nil => .inl ⟨rfl, rfl⟩
  | _, _, .cons h1 .nil => .inr ⟨_, _, rfl, rfl, h1⟩
  | _, _, .cons _ (.cons h2 t) => by
    rcases VRL.getLast? (.cons h2 t) with ⟨h3, -⟩ | ⟨x, y, hx, hy, hxy⟩
    · simp at h3
    · refine .inr ⟨x, y, ?_, ?_, hxy⟩
      · rw [List.getLast?_cons_cons]; exact hx
      · rw [List.getLast?_cons_cons]; exact hy

/-- A related value that is neither a memory nor a tuple is the source's. -/
theorem VR.eq {a b : Val} (h : VR X a b) (hm : ∀ m, a ≠ .mem m) (ht : ∀ vs, a ≠ .tuple vs) :
    b = a := by
  cases h with
  | refl => rfl
  | mem => exact absurd rfl (hm _)
  | tuple => exact absurd rfl (ht _)

theorem VR.mem_inv {m : Mem} {b : Val} (h : VR X (.mem m) b) :
    ∃ m', b = .mem m' ∧ EqX X m m' := by
  cases h with
  | refl => exact ⟨m, rfl, rfl⟩
  | mem h => exact ⟨_, rfl, h⟩

theorem VR.tuple_inv {vs : List Val} {b : Val} (h : VR X (.tuple vs) b) :
    ∃ ws, b = .tuple ws ∧ VRL X vs ws := by
  cases h with
  | refl => exact ⟨vs, rfl, VRL.refl vs⟩
  | tuple h => exact ⟨_, rfl, h⟩

/-! ## Retyping -/

mutual
theorem VR.retype : {a b : Val} → VR X a b → (t : Ty) → VR X (a.retype t) (b.retype t)
  | _, _, .refl _, _ => .refl _
  | _, _, .mem h, t => by
    cases t with
    | mem => exact .mem h
    | int w => cases w <;> exact .refl _
    | _ => exact .refl _
  | _, _, .tuple (vs := vs) (ws := ws) h, t => by
    cases t with
    | tuple ts =>
      unfold Val.retype
      rcases VRL.retypePre h ts with ⟨h1, h2⟩ | ⟨vs', ws', h1, h2, h3⟩
      · rw [h1, h2]; exact .refl _
      · rw [h1, h2]; exact .tuple h3
    | int w => cases w <;> exact .refl _
    | _ => exact .refl _
theorem VRL.retypePre : {as bs : List Val} → VRL X as bs → (ts : List Ty) →
    (Val.retypePre ts as = none ∧ Val.retypePre ts bs = none) ∨
      ∃ as' bs', Val.retypePre ts as = some as' ∧ Val.retypePre ts bs = some bs' ∧ VRL X as' bs'
  | _, _, h, [] => .inr ⟨_, _, rfl, rfl, h⟩
  | _, _, .nil, _ :: _ => .inl ⟨rfl, rfl⟩
  | _, _, .cons (a := a) (b := b) h1 t, t0 :: ts => by
    simp only [Val.retypePre]
    rcases VRL.retypePre t ts with ⟨h2, h3⟩ | ⟨as', bs', h2, h3, h4⟩
    · rw [h2, h3]; exact .inl ⟨rfl, rfl⟩
    · rw [h2, h3]; exact .inr ⟨_, _, rfl, rfl, .cons (VR.retype h1 t0) h4⟩
end

/-! ## Shapes, encodings, poison -/

mutual
theorem VR.hasTy : {a b : Val} → VR X a b → (t : Ty) → b.hasTy t = a.hasTy t
  | _, _, .refl _, _ => rfl
  | _, _, .mem _, t => by cases t <;> rfl
  | _, _, .tuple h, t => by
    cases t with
    | tuple ts => simp only [Val.hasTy]; exact VRL.hasTyPre h ts
    | _ => rfl
theorem VRL.hasTyPre : {as bs : List Val} → VRL X as bs → (ts : List Ty) →
    Val.hasTyPre bs ts = Val.hasTyPre as ts
  | _, _, _, [] => by simp [Val.hasTyPre]
  | _, _, .nil, _ :: _ => rfl
  | _, _, .cons h t, t0 :: ts => by
    simp only [Val.hasTyPre, VR.hasTy h t0, VRL.hasTyPre t ts]
end

theorem VR.encode {a b : Val} (h : VR X a b) (t : Ty) : encode t b = encode t a := by
  cases h with
  | refl => rfl
  | mem => rw [encode_mem, encode_mem]
  | tuple => rw [encode_tuple, encode_tuple]

mutual
theorem VR.hasPoison : {a b : Val} → VR X a b → b.hasPoison = a.hasPoison
  | _, _, .refl _ => rfl
  | _, _, .mem _ => rfl
  | _, _, .tuple h => by simp only [Val.hasPoison]; exact VRL.anyPoison h
theorem VRL.anyPoison : {as bs : List Val} → VRL X as bs → Val.anyPoison bs = Val.anyPoison as
  | _, _, .nil => rfl
  | _, _, .cons h t => by simp only [Val.anyPoison, VR.hasPoison h, VRL.anyPoison t]
end

end GoFV.Proof.TabsMod
