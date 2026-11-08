import GoFV.Proof.Gen.G1

variable [GoFV.SSA.Sem.Addrs]

/-!
# The frame under `LocMatch` (`docs/plans/proofs3.md` §4)

Slice G2's functions have frames (`MatchEnv.framed`: the caller's `LR` and `FP` saved at `0(SP)`
and `-8(SP)`) and spill slots (`LocMatch.slots`: 8 bytes at `SP + E.slot k`). `StkAt E` are those
machine addresses; `FrameOK E` places them above the nil page without wrapping around, the slots
above the saved `LR`. A machine memory that agrees with `m`'s at `StkAt E` keeps the slots and
the frame of `LocMatch` (`stk_keeps`), also under a larger injection after a call
(`stk_slots_frame`). `memInj_congr`: `MemInj` only reads the windows of the live blocks.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64

variable {ι ι' : Blk → Option (BitVec 64)}

/-! ## Values under a larger injection -/

theorem ptrRel_mono (hext : ∀ b a, ι b = some a → ι' b = some a) {p : Ptr} {r : BitVec 64}
    (h : PtrRel ι p r) : PtrRel ι' p r := by
  obtain ⟨a, ha, rfl⟩ := h
  exact ⟨a, hext _ _ ha, rfl⟩

theorem valRel_mono (hext : ∀ b a, ι b = some a → ι' b = some a) {v : Val} {r : BitVec 64}
    (h : ValRel ι v r) : ValRel ι' v r := by
  cases v with
  | int w x =>
    cases w with
    | w64 =>
      rcases h with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, ptrRel_mono hext h2⟩
    | _ => exact h
  | ptr p => exact ptrRel_mono hext h
  | _ => exact h

/-! ## Machine memory -/

theorem readMem_congr {M M' : Memory} : ∀ (n : Nat) (a : BitVec 64),
    (∀ j, j < n → M (a + BitVec.ofNat 64 j) = M' (a + BitVec.ofNat 64 j)) →
    readMem M a n = readMem M' a n
  | 0, _, _ => rfl
  | n + 1, a, h => by
    have h0 := h 0 (by omega)
    simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at h0
    simp only [readMem]
    have ih := readMem_congr n (a + 1) (fun j hj => by
      simpa only [addr_succ] using h (j + 1) (by omega))
    rw [ih, h0]

theorem readMem_writeMem_self (mm : Memory) (A V : BitVec 64) :
    readMem (writeMem mm A 8 V) A 8 = V := by
  apply BitVec.eq_of_toNat_eq
  apply readMem_of_bytes _ 8 A V.toNat (by have := V.isLt; simpa using this)
  intro j hj
  rw [writeMem_at 8 mm A V j hj (Nat.le_refl 8)]
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [show 2 ^ (8 * j) = 256 ^ j by rw [Nat.pow_mul], show 2 ^ 8 = 256 from rfl]

theorem ofInt_nonneg {off : Int} (h0 : 0 ≤ off) : BitVec.ofInt 64 off = BitVec.ofNat 64 off.toNat := by
  have := BitVec.ofInt_natCast (w := 64) off.toNat
  rwa [Int.toNat_of_nonneg h0] at this

/-- A byte of an 8-byte window at a non-negative offset from `sp` that does not wrap around. -/
theorem win_toNat {sp : BitVec 64} {off : Int} (h0 : 0 ≤ off)
    (h : sp.toNat + off.toNat + 8 ≤ 2 ^ 64) {j : Nat} (hj : j < 8) :
    (sp + BitVec.ofInt 64 off + BitVec.ofNat 64 j).toNat = sp.toNat + off.toNat + j := by
  rw [ofInt_nonneg h0]
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h64] at h ⊢
  omega

theorem win0_toNat {sp : BitVec 64} {off : Int} (h0 : 0 ≤ off)
    (h : sp.toNat + off.toNat + 8 ≤ 2 ^ 64) :
    (sp + BitVec.ofInt 64 off).toNat = sp.toNat + off.toNat := by
  have := win_toNat h0 h (j := 0) (by omega)
  simpa using this

/-! ## The frame -/

/-- The machine addresses `LocMatch` keeps in the frame: the saved `LR`/`FP` words of a framed
activation (`[SP - 8, SP + 8)`) and the 8 bytes of every spill slot. -/
def StkAt (E : MatchEnv) (y : BitVec 64) : Prop :=
  (E.framed = true ∧ E.sp.toNat - 8 ≤ y.toNat ∧ y.toNat < E.sp.toNat + 8) ∨
  ∃ k off, E.slot k = some off ∧ E.sp.toNat + off.toNat ≤ y.toNat ∧
    y.toNat < E.sp.toNat + off.toNat + 8

/-- The frame layout of an activation: `SP` above the nil page with the saved `FP` below it, the
saved `LR` word not wrapping around, every spill slot above the saved `LR` and not wrapping
around. -/
structure FrameOK (E : MatchEnv) : Prop where
  lo : 4096 + 8 ≤ E.sp.toNat
  hi : E.sp.toNat + 8 ≤ 2 ^ 64
  slot : ∀ k off, E.slot k = some off → 8 ≤ off ∧ E.sp.toNat + off.toNat + 8 ≤ 2 ^ 64

theorem stk_slot {E : MatchEnv} (hF : FrameOK E) {k : SlotKey} {off : Int}
    (hk : E.slot k = some off) {j : Nat} (hj : j < 8) :
    StkAt E (E.sp + BitVec.ofInt 64 off + BitVec.ofNat 64 j) := by
  obtain ⟨h8, hhi⟩ := hF.slot k off hk
  right
  refine ⟨k, off, hk, ?_⟩
  rw [win_toNat (by omega) hhi hj]
  omega

theorem sp_toNat {E : MatchEnv} (hF : FrameOK E) {j : Nat} (hj : j < 8) :
    (E.sp + BitVec.ofNat 64 j).toNat = E.sp.toNat + j := by
  have := hF.hi
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h64] at this ⊢
  omega

theorem spm8_toNat {E : MatchEnv} (hF : FrameOK E) {j : Nat} (hj : j < 8) :
    (E.sp - 8 + BitVec.ofNat 64 j).toNat = E.sp.toNat - 8 + j := by
  have := hF.lo
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  have hsub : (E.sp - 8).toNat = E.sp.toNat - 8 := by
    rw [BitVec.toNat_sub]; simp only [h64]
    have := E.sp.isLt; simp only [h64] at this
    simp; omega
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hsub, h64]
  have := E.sp.isLt; simp only [h64] at this
  omega

/-- The slots and the frame of `LocMatch E s b i m` hold for `E'` (`E` with a larger injection)
and a machine state `m'` whose memory agrees with `m`'s at `StkAt E` and whose `SP`, `R28`, `R29`
(and `X30` in a leaf) are `m`'s. -/
theorem stk_slots_frame {E E' : MatchEnv} {s : LocState} {b : ID} {i : Nat} {m m' : MState}
    (hm : LocMatch E s b i m) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size = 8)
    (hE' : E' = { E with ι := E'.ι }) (hext : ∀ b a, E.ι b = some a → E'.ι b = some a)
    (hmem : ∀ y, StkAt E y → m'.mem y = m.mem y) (hsp : m'.sp = m.sp) (h28 : m'.x 28 = m.x 28)
    (h29 : m'.x 29 = m.x 29) (h30 : E.framed = false → m'.x 30 = m.x 30) :
    (∀ k v, s.slots.lookup k = some v → ∃ off, E'.slot k = some off ∧
      SlotRel E'.ι (E'.lc.slotTy k) v m'.mem (E'.sp + BitVec.ofInt 64 off)) ∧
    FrameRel E' m' := by
  rw [hE']
  refine ⟨fun k v hk => ?_, ?_⟩
  · obtain ⟨off, hoff, hrel⟩ := hm.slots k v hk
    refine ⟨off, hoff, ?_⟩
    unfold SlotRel at hrel ⊢
    have h8 := hsz k v hk
    simp only at h8 ⊢
    rw [h8] at hrel ⊢
    rw [readMem_congr 8 (E.sp + BitVec.ofInt 64 off) (fun j hj => hmem _ (stk_slot hF hoff hj))]
    exact valRel_mono hext hrel
  · obtain ⟨h1, h2, h3, h4⟩ := hm.frame
    refine ⟨by rw [hsp, h1], by rw [h28, h2], fun hf => ?_, fun hf => ?_⟩
    · obtain ⟨a1, a2, a3⟩ := h3 hf
      refine ⟨by rw [h29, a1], ?_, ?_⟩
      · unfold MState.word at a2 ⊢
        rw [readMem_congr 8 E.sp (fun j hj => hmem _ (Or.inl ⟨hf, by rw [sp_toNat hF hj]; omega,
          by rw [sp_toNat hF hj]; omega⟩))]
        exact a2
      · unfold MState.word at a3 ⊢
        rw [readMem_congr 8 (E.sp - 8) (fun j hj => hmem _ (Or.inl ⟨hf,
          by rw [spm8_toNat hF hj]; omega, by rw [spm8_toNat hF hj]; have := hF.lo; omega⟩))]
        exact a3
    · obtain ⟨a1, a2⟩ := h4 hf
      exact ⟨by rw [h29, a1], by rw [h30 hf, a2]⟩

/-- A memory agreeing at `StkAt E` keeps `LocMatch`'s slots and frame. -/
theorem stk_keeps {E : MatchEnv} {s : LocState} {b : ID} {i : Nat} {m : MState}
    (hm : LocMatch E s b i m) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size = 8) :
    Keeps E (StkAt E) s m := fun M hM =>
  stk_slots_frame (E' := E) (m' := { m with mem := M }) hm hF hsz rfl (fun _ _ h => h) hM rfl rfl
    rfl (fun _ => rfl)

/-! ## `MemInj` reads only the windows of the live blocks -/

theorem memInj_congr {m : Mem} {mm M : Memory} (h : MemInj ι m mm)
    (hag : ∀ b al a, (b, al) ∈ m.blocks → ι b = some a → ∀ i, i < al.data.size →
      M (a + BitVec.ofNat 64 i) = mm (a + BitVec.ofNat 64 i)) :
    MemInj ι m M := by
  obtain ⟨W, hW⟩ := h.bytes
  refine ⟨h.nil, h.mapped, h.inj, W, fun b al a hb ha => ?_⟩
  obtain ⟨hw1, hw2, hw3⟩ := hW b al a hb ha
  refine ⟨fun o ho => ?_, hw2, fun i hi hno => ?_⟩
  · obtain ⟨p, hp, hrel⟩ := hw1 o ho
    have ho8 : o + 8 ≤ al.data.size := by
      unfold ptrWordAt? at hp
      split at hp
      · assumption
      · cases hp
    refine ⟨p, hp, ?_⟩
    unfold memWord at hrel ⊢
    have hc : readMem M (a + BitVec.ofNat 64 o) 8 = readMem mm (a + BitVec.ofNat 64 o) 8 :=
      readMem_congr 8 (a + BitVec.ofNat 64 o) (fun j hj => by
        have := hag b al a hb ha (o + j) (by omega)
        rwa [← BitVec.ofNat_add_ofNat, ← BitVec.add_assoc] at this)
    rw [hc]
    exact hrel
  · rw [hag b al a hb ha i hi]
    exact hw3 i hi hno

/-- An address of `P` is no byte of a live block when the blocks are away from `P`. -/
theorem ne_of_sep {P : BitVec 64 → Prop} {m : Mem} {mm : Memory} (h : MemInj ι m mm)
    (hsep : SepFrom ι P m) {b : Blk} {al : Alloc} {a y : BitVec 64} (hb : (b, al) ∈ m.blocks)
    (ha : ι b = some a) (hy : P y) {i : Nat} (hi : i < al.data.size) :
    a + BitVec.ofNat 64 i ≠ y := by
  intro he
  obtain ⟨a0, ha0, -, hhi⟩ := h.mapped b al hb
  rw [ha] at ha0; cases ha0
  apply hsep b al a hb ha y hy
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  have : (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h64] at hhi ⊢
    omega
  rw [← he, this]
  omega

end GoFV.Proof.Gen
