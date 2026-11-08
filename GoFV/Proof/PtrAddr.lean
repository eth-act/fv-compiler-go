import GoFV.SSA.Sem.Ptr
import GoFV.SSA.Sem.Layout
import GoFV.Proof.Retype

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

/-- **`Ptr.word` reads back as the pointer** wherever a pointer is read (`Val.asPtrWord`): the
concrete address of a convertible pointer converts back to it (`Ptr.ofAddr_addr`), any other
pointer inside its window stays a pointer. -/
theorem Ptr.word_asPtrWord {p : Ptr} (hw : p.inWindow = true) : p.word.asPtrWord = some p := by
  unfold Ptr.word
  cases hc : p.convertible <;> cases ha : p.addr?
  · simp [hw, Val.asPtrWord]
  · simp [hw, Val.asPtrWord]
  · simp [hw, Val.asPtrWord]
  · simp only [Val.asPtrWord, Ptr.ofAddr_addr hc ha]

/-- A pointer's word reads, if at all, as the pointer. -/
theorem Ptr.word_asPtrWord_of {p q : Ptr} (h : p.word.asPtrWord = some q) : q = p := by
  rcases Ptr.word_cases p with ⟨hc, e⟩ | ⟨hc, a, ha, e⟩ | ⟨-, e⟩ <;> rw [e] at h
  · cases h; rfl
  · simp only [Val.asPtrWord, Option.some.injEq] at h
    rw [← h, Ptr.ofAddr_addr hc ha]
  · cases h

/-- **A slot of an outgoing-arguments area is an integer word** (`SelectNAddr`'s result,
`Tuple.selectNAddr`): the area of every activation numbered below `2^20` has a concrete address
(`Blk.base?`), and for every offset inside its window the word `Ptr.ofAddr` reads back is exactly
the slot `⟨outargs act, off⟩`. -/
theorem Ptr.word_outargs {act : Nat} {off : BitVec 64} (ha : act < 2 ^ 20)
    (ho : off.toNat < 2 ^ 24) :
    ∃ x, (⟨.outargs act, off⟩ : Ptr).word = .int .w64 x ∧
      Ptr.ofAddr x = ⟨.outargs act, off⟩ := by
  have hc : (⟨.outargs act, off⟩ : Ptr).convertible = true := by
    simp only [Ptr.convertible, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨by omega, ho⟩
  refine ⟨BitVec.ofNat 64 (2 ^ 62 + act * 2 ^ 42) + off, ?_, Ptr.ofAddr_addr hc rfl⟩
  unfold Ptr.word
  rw [hc]
  rfl

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

/-- **The pointer at an address converts** (back to that address, `Ptr.addr?_ofAddr`): its block
is inside the address encoding (a heap object below `2^22 - 1`, a frame of an activation below
`3·2^20`, which is every address from `2^62` up to `2^64`). -/
theorem Ptr.convertible_ofAddr (x : BitVec 64) : (Ptr.ofAddr x).convertible = true := by
  have hx := x.isLt
  unfold Ptr.ofAddr; dsimp only
  split
  · simp only [Ptr.convertible, decide_eq_true_eq]; assumption
  split
  · simp only [Ptr.convertible, Bool.and_eq_true, decide_eq_true_eq, BitVec.toNat_ofNat]; omega
  split
  · simp only [Ptr.convertible, Bool.and_eq_true, decide_eq_true_eq, BitVec.toNat_ofNat]; omega
  · rename_i hk
    simp only [beq_iff_eq] at hk
    simp only [Ptr.convertible, Bool.and_eq_true, decide_eq_true_eq, BitVec.toNat_ofNat]; omega

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

/-! ## Pointer arithmetic on a pointer's word -/

/-- Stepping a convertible pointer inside its window keeps it convertible. -/
theorem Ptr.convertible_add {p : Ptr} {k : BitVec 64} (hc : p.convertible = true)
    (hw : (p.add k).inWindow = true) : (p.add k).convertible = true := by
  obtain ⟨b, off⟩ := p
  cases b <;> simp_all [Ptr.convertible, Ptr.add, Ptr.inWindow, Blk.window?]

theorem Ptr.addr?_add (p : Ptr) (k : BitVec 64) : (p.add k).addr? = p.addr?.map (· + k) := by
  obtain ⟨b, off⟩ := p
  simp only [Ptr.addr?, Ptr.add, Option.map_map]
  cases b.base? <;> simp [BitVec.add_assoc]

/-- A convertible pointer stepped inside its window is the word of its address plus the step. -/
theorem Ptr.word_add {p : Ptr} {k a : BitVec 64} (hc : p.convertible = true)
    (ha : p.addr? = some a) (hw : (p.add k).inWindow = true) :
    (p.add k).word = .int .w64 (a + k) := by
  unfold Ptr.word
  rw [Ptr.convertible_add hc hw, Ptr.addr?_add, ha]
  rfl

/-- Arithmetic on the address of a convertible pointer is the pointer's arithmetic. -/
theorem PtrOps.wordRes_addr {p : Ptr} {a : BitVec 64} (hc : p.convertible = true)
    (ha : p.addr? = some a) (k : BitVec 64) : PtrOps.wordRes a k = PtrOps.ptrRes (p.add k) := by
  unfold PtrOps.wordRes PtrOps.ptrRes
  rw [Ptr.ofAddr_addr hc ha]
  split
  · rename_i hw; rw [Ptr.word_add hc ha hw]
  · rfl

/-- **Pointer arithmetic does not tell a pointer inside its window from its word** (`Ptr.word`,
#290). -/
theorem PtrOps.offPtr_word (ai : Int64) {p : Ptr} (hw : p.inWindow = true) :
    PtrOps.offPtr ai [p.word] = PtrOps.offPtr ai [.ptr p] := by
  rcases Ptr.word_cases p with ⟨-, h⟩ | ⟨hc, a, ha, h⟩ | ⟨h', -⟩
  · rw [h]
  · rw [h]; exact PtrOps.wordRes_addr hc ha _
  · rw [hw] at h'; cases h'

theorem PtrOps.addPtr_word {p : Ptr} (hw : p.inWindow = true) (i : Val) :
    PtrOps.addPtr [p.word, i] = PtrOps.addPtr [.ptr p, i] := by
  rcases Ptr.word_cases p with ⟨-, h⟩ | ⟨hc, a, ha, h⟩ | ⟨h', -⟩
  · rw [h]
  · rw [h]
    simp only [PtrOps.addPtr]
    split
    · exact PtrOps.wordRes_addr hc ha _
    · rfl
  · rw [hw] at h'; cases h'

theorem PtrOps.ptrIndex_word (el : Option Nat) {p : Ptr} (hw : p.inWindow = true) (i : Val) :
    PtrOps.ptrIndex el [p.word, i] = PtrOps.ptrIndex el [.ptr p, i] := by
  rcases Ptr.word_cases p with ⟨-, h⟩ | ⟨hc, a, ha, h⟩ | ⟨h', -⟩
  · rw [h]
  · rw [h]
    simp only [PtrOps.ptrIndex]
    split
    · exact PtrOps.wordRes_addr hc ha _
    · rfl
  · rw [hw] at h'; cases h'

/-- A `Load` reads its address through `Val.asPtrWord`: a pointer inside its window and its word
load alike. -/
theorem loadOp_word (t : Ty) {p : Ptr} (hw : p.inWindow = true) (m : Val) :
    loadOp t [p.word, m] = loadOp t [.ptr p, m] := by
  cases m <;> simp only [loadOp] <;> rw [Ptr.word_asPtrWord hw] <;> rfl

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

/-- **`Ptr.convertible` is exactly the round trip** (F2, #385): a pointer converts iff it has a
concrete address and is the pointer `Ptr.ofAddr` gives back at it. So a pointer has a lowered
register (`Arm64.ptrReg`) iff it converts. -/
theorem Ptr.convertible_iff (p : Ptr) :
    p.convertible = true ↔ ∃ x, p.addr? = some x ∧ Ptr.ofAddr x = p := by
  constructor
  · intro hc
    have hs := Ptr.addr?_isSome_of_convertible hc
    cases ha : p.addr? with
    | none => rw [ha] at hs; cases hs
    | some x => exact ⟨x, rfl, Ptr.ofAddr_addr hc ha⟩
  · rintro ⟨x, -, rfl⟩
    exact Ptr.convertible_ofAddr x

/-- Inside its window, whether a pointer converts depends only on its block (`Ptr.convertible` is
the block's encoding condition and the window). -/
theorem Ptr.convertible_eq_of_blk {p q : Ptr} (hb : q.blk = p.blk) (hp : p.inWindow = true)
    (hq : q.inWindow = true) : q.convertible = p.convertible := by
  obtain ⟨b, o⟩ := p
  obtain ⟨b', o'⟩ := q
  simp only at hb
  subst hb
  cases b' <;> simp_all [Ptr.convertible, Ptr.inWindow, Blk.window?]

/-- A pointer of a block whose pointers are held as pointers, inside its window, is held too
(F1+F2, #385: not converting is a property of the block). -/
theorem Ptr.held_of_blk {p q : Ptr} (hb : q.blk = p.blk) (hp : p.held = true)
    (hq : q.inWindow = true) : q.held = true := by
  obtain ⟨hc, hw⟩ := Ptr.held_iff.1 hp
  exact Ptr.held_iff.2 ⟨(Ptr.convertible_eq_of_blk hb hw hq).trans hc, hq⟩

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
  unfold PtrOps.ptrRes Ptr.step?; split
  · rename_i hw; exact Ptr.word_asPtrWord hw
  · rfl

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

/-- Retyping at a pointer shape keeps the pointer a word reads as, unless it is a pointer
outside its window (whose word is `poison`). -/
theorem Val.asPtrWord_retype_ptr (e : Option Nat) {v : Val}
    (hv : ∀ p, v = .ptr p → p.inWindow = true) :
    (v.retype (.ptr e)).asPtrWord = v.asPtrWord := by
  cases v with
  | int w x => cases w <;> rfl
  | ptr p => exact Ptr.word_asPtrWord (hv p rfl)
  | _ => rfl

/-- A value whose retype at a pointer shape reads as a pointer reads as that pointer. -/
theorem Val.asPtrWord_of_retype_ptr {e : Option Nat} {v : Val} {q : Ptr}
    (h : (v.retype (.ptr e)).asPtrWord = some q) : v.asPtrWord = some q := by
  cases v with
  | int w x => cases w <;> first | exact h | cases h
  | ptr p =>
    show some p = some q
    rw [Ptr.word_asPtrWord_of h]
  | _ => cases h

/-- `PtrOps.ptrRes` gives a value of every pointer shape (a word or `poison`). -/
theorem PtrOps.ptrRes_retype_ptr (e : Option Nat) (p : Ptr) :
    (PtrOps.ptrRes p).retype (.ptr e) = PtrOps.ptrRes p := by
  unfold PtrOps.ptrRes; split
  · exact Ptr.word_retype_ptr p e
  · rfl

theorem PtrOps.wordRes_retype_ptr (e : Option Nat) (x k : BitVec 64) :
    (PtrOps.wordRes x k).retype (.ptr e) = PtrOps.wordRes x k := by
  unfold PtrOps.wordRes; split <;> rfl

/-- The result of `OffPtr` has every pointer shape. -/
theorem PtrOps.offPtr_retype_ptr (e : Option Nat) (ai : Int64) (xs : List Val) :
    (PtrOps.offPtr ai xs).retype (.ptr e) = PtrOps.offPtr ai xs := by
  unfold PtrOps.offPtr
  split
  · exact PtrOps.ptrRes_retype_ptr e _
  · exact PtrOps.wordRes_retype_ptr e _ _
  · rfl

/-- The result of `AddPtr` has every pointer shape. -/
theorem PtrOps.addPtr_retype_ptr (e : Option Nat) (xs : List Val) :
    (PtrOps.addPtr xs).retype (.ptr e) = PtrOps.addPtr xs := by
  unfold PtrOps.addPtr
  split
  · split
    · exact PtrOps.ptrRes_retype_ptr e _
    · rfl
  · split
    · exact PtrOps.wordRes_retype_ptr e _ _
    · rfl
  · rfl

/-- The result of `PtrIndex` has every pointer shape. -/
theorem PtrOps.ptrIndex_retype_ptr (e el : Option Nat) (xs : List Val) :
    (PtrOps.ptrIndex el xs).retype (.ptr e) = PtrOps.ptrIndex el xs := by
  unfold PtrOps.ptrIndex
  split
  · split
    · exact PtrOps.ptrRes_retype_ptr e _
    · rfl
  · split
    · exact PtrOps.wordRes_retype_ptr e _ _
    · rfl
  · rfl

end GoFV.SSA.Sem
