import GoFV.SSA.Sem.Ptr
import GoFV.SSA.Sem.Layout

/-!
# Concrete addresses round-trip (#156)

`Ptr.ofAddr_addr`: a pointer that `Convert` turns into an integer (`Ptr.convertible`) is the
pointer `Ptr.ofAddr` gives back, so the integer is that pointer wherever a pointer is read
(`convert_asPtrWord`). `Ptr.eq_iff`: pointer equality is block and offset equality.

An integer word at a pointer shape reads as the pointer at its address (§3.3), and pointer
arithmetic on it keeps that reading (`Ptr.ofAddr_add_of_inWindow`): `OffPtr`/`AddPtr`/`PtrIndex`
of any pointer word read as the operand's pointer stepped inside its window (`Ptr.step?`,
`PtrOps.offPtr_asPtrWord`, …).
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
  | wbuf => simp [Ptr.convertible] at hc

/-- **`Convert` round-trips**: a pointer converted to an integer is, wherever a pointer is
read (`Val.asPtrWord`: an integer keeps its word at a pointer shape, so `Convert` back is the
identity on it), the pointer again, whenever the first conversion is defined. -/
theorem convert_asPtrWord (t : Ty) (p : Ptr) (m : Val) {x : BitVec 64}
    (h : PtrOps.convert t [.ptr p, m] = .int .w64 x) :
    (Val.int .w64 x).asPtrWord = some p := by
  unfold PtrOps.convert at h
  cases t with
  | int w =>
    cases w with
    | w64 =>
      simp only at h
      cases hc : p.convertible <;> cases ha : p.addr? <;> rw [hc, ha] at h <;> try cases h
      simp only [Val.asPtrWord, Ptr.ofAddr_addr hc ha]
    | _ => cases h
  | _ => cases h

/-- **Pointer arithmetic on an integer word** (§3.3): where the pointer at address `x` plus `k`
stays inside its block's address window, the integer `x + k` addresses that pointer. -/
theorem Ptr.ofAddr_add_of_inWindow {x k : BitVec 64} (h : ((Ptr.ofAddr x).add k).inWindow = true) :
    Ptr.ofAddr (x + k) = (Ptr.ofAddr x).add k := by
  have hx := x.isLt
  have hk := k.isLt
  have hs : (x + k).toNat = (x.toNat + k.toNat) % 2 ^ 64 := BitVec.toNat_add x k
  by_cases h1 : x.toNat < 2 ^ 40
  · have e : Ptr.ofAddr x = ⟨.nil, x⟩ := by simp [Ptr.ofAddr, h1]
    rw [e] at h ⊢
    simp only [Ptr.add, Ptr.inWindow, Blk.window?] at h
    unfold Ptr.ofAddr
    rw [if_pos (of_decide_eq_true h)]; rfl
  by_cases h2 : x.toNat < 2 ^ 62
  · have e : Ptr.ofAddr x = ⟨.heap (x.toNat / 2 ^ 40 - 1), BitVec.ofNat 64 (x.toNat % 2 ^ 40)⟩ := by
      simp [Ptr.ofAddr, h1, h2]
    rw [e] at h ⊢
    simp only [Ptr.add, Ptr.inWindow, Blk.window?, decide_eq_true_eq, BitVec.toNat_add,
      BitVec.toNat_ofNat] at h
    simp only [Ptr.ofAddr, hs, Ptr.add, show ¬ (x.toNat + k.toNat) % 2 ^ 64 < 2 ^ 40 by omega,
      show (x.toNat + k.toNat) % 2 ^ 64 < 2 ^ 62 by omega, ite_false, ite_true,
      show (x.toNat + k.toNat) % 2 ^ 64 / 2 ^ 40 = x.toNat / 2 ^ 40 by omega, Ptr.mk.injEq, true_and]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  obtain ⟨r, hr⟩ : ∃ r, x.toNat = 2 ^ 62 + r := ⟨x.toNat - 2 ^ 62, by omega⟩
  have hr' : x.toNat - 2 ^ 62 = r := by omega
  by_cases h3 : r % 2 ^ 42 / 2 ^ 24 = 0
  · have e : Ptr.ofAddr x = ⟨.outargs (r / 2 ^ 42), BitVec.ofNat 64 (r % 2 ^ 24)⟩ := by
      simp only [Ptr.ofAddr, h1, h2, ite_false, hr', h3, beq_self_eq_true, ite_true]
    rw [e] at h ⊢
    simp only [Ptr.add, Ptr.inWindow, Blk.window?, decide_eq_true_eq, BitVec.toNat_add,
      BitVec.toNat_ofNat] at h
    simp only [Ptr.ofAddr, hs, Ptr.add, show ¬ (x.toNat + k.toNat) % 2 ^ 64 < 2 ^ 40 by omega,
      show ¬ (x.toNat + k.toNat) % 2 ^ 64 < 2 ^ 62 by omega, ite_false,
      show ((x.toNat + k.toNat) % 2 ^ 64 - 2 ^ 62) % 2 ^ 42 / 2 ^ 24 = 0 by omega,
      show ((x.toNat + k.toNat) % 2 ^ 64 - 2 ^ 62) / 2 ^ 42 = r / 2 ^ 42 by omega,
      beq_self_eq_true, ite_true, Ptr.mk.injEq, true_and]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  · have e : Ptr.ofAddr x = ⟨.local (r / 2 ^ 42) (r % 2 ^ 42 / 2 ^ 24), BitVec.ofNat 64 (r % 2 ^ 24)⟩ := by
      simp only [Ptr.ofAddr, h1, h2, ite_false, hr', beq_iff_eq, h3]
    rw [e] at h ⊢
    simp only [Ptr.add, Ptr.inWindow, Blk.window?, decide_eq_true_eq, BitVec.toNat_add,
      BitVec.toNat_ofNat] at h
    simp only [Ptr.ofAddr, hs, Ptr.add, show ¬ (x.toNat + k.toNat) % 2 ^ 64 < 2 ^ 40 by omega,
      show ¬ (x.toNat + k.toNat) % 2 ^ 64 < 2 ^ 62 by omega, ite_false,
      show ((x.toNat + k.toNat) % 2 ^ 64 - 2 ^ 62) % 2 ^ 42 / 2 ^ 24 = r % 2 ^ 42 / 2 ^ 24 by omega,
      show ((x.toNat + k.toNat) % 2 ^ 64 - 2 ^ 62) / 2 ^ 42 = r / 2 ^ 42 by omega,
      beq_iff_eq, h3, ite_false, Ptr.mk.injEq, true_and]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega

/-- The pointer at an address lies inside its block's window. -/
theorem Ptr.ofAddr_inWindow (x : BitVec 64) : (Ptr.ofAddr x).inWindow = true := by
  have hx := x.isLt
  unfold Ptr.ofAddr; dsimp only
  split
  · simp only [Ptr.inWindow, Blk.window?, decide_eq_true_eq]; assumption
  split
  · simp only [Ptr.inWindow, Blk.window?, decide_eq_true_eq, BitVec.toNat_ofNat]; omega
  split <;> (simp only [Ptr.inWindow, Blk.window?, decide_eq_true_eq, BitVec.toNat_ofNat]; omega)

/-- Adding nothing to an integer word keeps it. -/
theorem PtrOps.wordRes_zero (x : BitVec 64) : PtrOps.wordRes x 0 = .int .w64 x := by
  have e : (Ptr.ofAddr x).add 0 = Ptr.ofAddr x := by simp [Ptr.add]
  unfold PtrOps.wordRes
  rw [e, Ptr.ofAddr_inWindow, if_pos rfl]
  simp

/-- Two steps of pointer arithmetic on an integer word, the first inside its window, are one. -/
theorem PtrOps.wordRes_wordRes {x a b : BitVec 64} (h : ((Ptr.ofAddr x).add a).inWindow = true) :
    PtrOps.wordRes (x + a) b = PtrOps.wordRes x (a + b) := by
  have e : ((Ptr.ofAddr x).add a).add b = (Ptr.ofAddr x).add (a + b) := by
    simp only [Ptr.add, BitVec.add_assoc]
  unfold PtrOps.wordRes
  rw [Ptr.ofAddr_add_of_inWindow h, BitVec.add_assoc, e]

theorem Ptr.eq_iff (p q : Ptr) : p.eq q = true ↔ p = q := by
  obtain ⟨b, o⟩ := p; obtain ⟨b', o'⟩ := q
  simp [Ptr.eq]

/-- The pointer `Ptr.ofAddr` gives at an address has that address. -/
theorem Ptr.addr?_ofAddr (x : BitVec 64) : (Ptr.ofAddr x).addr? = some x := by
  have hx := x.isLt
  unfold Ptr.ofAddr
  dsimp only
  split
  · simp [Ptr.addr?, Blk.base?]
  · split
    · rename_i h1 h2
      simp only [Ptr.addr?, Blk.base?, Option.map_some, Option.some.injEq]
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
      have : (x.toNat / 2 ^ 40 - 1 + 1) * 2 ^ 40 + x.toNat % 2 ^ 40 = x.toNat := by omega
      omega
    · rename_i h1 h2
      split
      · rename_i hk
        simp only [beq_iff_eq] at hk
        simp only [Ptr.addr?, Blk.base?, Option.map_some, Option.some.injEq]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        omega
      · simp only [Ptr.addr?, Blk.base?, Option.map_some, Option.some.injEq]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
        omega

/-- Distinct addresses are distinct pointers (`Ptr.addr?_ofAddr`). -/
theorem Ptr.ofAddr_eq_ofAddr (x y : BitVec 64) :
    (Ptr.ofAddr x).eq (Ptr.ofAddr y) = (x == y) := by
  rw [Bool.eq_iff_iff, Ptr.eq_iff, beq_iff_eq]
  constructor
  · intro h
    have := congrArg Ptr.addr? h
    rwa [Ptr.addr?_ofAddr, Ptr.addr?_ofAddr, Option.some.injEq] at this
  · rintro rfl; rfl

/-! ## Pointer arithmetic on pointer words -/

/-- `p + k` where it stays inside its block's address window (the pointer arithmetic of
`PtrOps.ptrRes`, `PtrOps.wordRes`). -/
def Ptr.step? (p : Ptr) (k : BitVec 64) : Option Ptr :=
  if (p.add k).inWindow then some (p.add k) else none

theorem PtrOps.ptrRes_asPtrWord (p : Ptr) (k : BitVec 64) :
    (PtrOps.ptrRes (p.add k)).asPtrWord = p.step? k := by
  unfold PtrOps.ptrRes Ptr.step?; split <;> rfl

theorem PtrOps.wordRes_asPtrWord (x k : BitVec 64) :
    (PtrOps.wordRes x k).asPtrWord = (Ptr.ofAddr x).step? k := by
  unfold PtrOps.wordRes Ptr.step?; split
  · rename_i h; simp only [Val.asPtrWord, Ptr.ofAddr_add_of_inWindow h]
  · rfl

/-- Pointer arithmetic reads its operand as a pointer word (§3.3). -/
theorem PtrOps.offPtr_asPtrWord (ai : Int64) (x : Val) :
    (PtrOps.offPtr ai [x]).asPtrWord = x.asPtrWord.bind (·.step? (BitVec.ofInt 64 ai.toInt)) := by
  match x with
  | .ptr p => exact PtrOps.ptrRes_asPtrWord _ _
  | .int .w64 x => exact PtrOps.wordRes_asPtrWord _ _
  | .int .w8 _ | .int .w16 _ | .int .w32 _ | .bool _ | .mem _ | .tuple _ | .agg _ | .blob _
  | .empty | .poison => rfl

theorem PtrOps.addPtr_asPtrWord (x i : Val) :
    (PtrOps.addPtr [x, i]).asPtrWord =
      x.asPtrWord.bind fun p => (asOffset i).bind (p.step? ·) := by
  match x with
  | .ptr p =>
    cases h : asOffset i with
    | none => simp only [PtrOps.addPtr, h, Val.asPtrWord, Option.bind_some, Option.bind_none]
    | some k =>
      simp only [PtrOps.addPtr, h, Val.asPtrWord, Option.bind_some]
      exact PtrOps.ptrRes_asPtrWord _ _
  | .int .w64 x =>
    cases h : asOffset i with
    | none => simp only [PtrOps.addPtr, h, Val.asPtrWord, Option.bind_some, Option.bind_none]
    | some k =>
      simp only [PtrOps.addPtr, h, Val.asPtrWord, Option.bind_some]
      exact PtrOps.wordRes_asPtrWord _ _
  | .int .w8 _ | .int .w16 _ | .int .w32 _ | .bool _ | .mem _ | .tuple _ | .agg _ | .blob _
  | .empty | .poison => rfl

theorem PtrOps.ptrIndex_asPtrWord (el : Option Nat) (x i : Val) :
    (PtrOps.ptrIndex el [x, i]).asPtrWord =
      x.asPtrWord.bind fun p => el.bind fun e => (asOffset i).bind
        fun k => p.step? (k * BitVec.ofNat 64 e) := by
  match x with
  | .ptr p =>
    unfold PtrOps.ptrIndex; simp only [Val.asPtrWord, Option.bind_some]
    cases el <;> cases h : asOffset i <;> simp only [Option.bind_some, Option.bind_none] <;>
      first | rfl | exact PtrOps.ptrRes_asPtrWord _ _
  | .int .w64 x =>
    unfold PtrOps.ptrIndex; simp only [Val.asPtrWord, Option.bind_some]
    cases el <;> cases h : asOffset i <;> simp only [Option.bind_some, Option.bind_none] <;>
      first | rfl | exact PtrOps.wordRes_asPtrWord _ _
  | .int .w8 _ | .int .w16 _ | .int .w32 _ | .bool _ | .mem _ | .tuple _ | .agg _ | .blob _
  | .empty | .poison => rfl

/-- Retyping at a pointer shape keeps the pointer a word reads as. -/
theorem Val.asPtrWord_retype_ptr (e : Option Nat) (v : Val) :
    (v.retype (.ptr e)).asPtrWord = v.asPtrWord := by
  cases v with
  | int w x => cases w <;> rfl
  | _ => rfl

end GoFV.SSA.Sem
