import GoFV.Proof.TabsAgreeModMem
import GoFV.Proof.MemInv
import GoFV.Proof.Pass.CSEMemBytes
import GoFV.Proof.ValRefine

variable [GoFV.SSA.Sem.Addrs]

/-!
# writebarrier: memories (issue #36)

`MemOK m`: the write-barrier flag `runtime.writeBarrier` is a read-only allocation whose first
four bytes are concrete (`FlagOK`), so the flag `Load <uint32>` is an integer (`load_flag`), and
`m` has no write-barrier buffer (`Blk.wbuf`). Writes and `poisonBlock`s of other blocks keep it
(`MemOK.write`, `MemOK.poison`).

`W mS mT`: the target's memory is the source's with possibly a buffer (`mT.erase isW = mS`,
`mS` without one). The re-emitted stores keep it (`W.write`, `W.poison`), and `WBend` (`Mem.free
.wbuf`) ends it (`W.free`). `Buf M n m`: a memory of the buffer block of a write-barrier
sequence: `M` with a writable buffer of `8 n` bytes; a buffer store of 8 bytes at `8 j < 8 n`
succeeds and keeps it (`Buf.write`).
-/

namespace GoFV.Proof.WB

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof.TabsMod

/-- The block of the write-barrier flag. -/
def flagBlk : Blk := .global "runtime.writeBarrier"

/-- The write-barrier buffer, as a block predicate (`Mem.erase`). -/
def isW (b : Blk) : Bool := b == .wbuf

/-- The flag's allocation: read-only, its first four bytes concrete. -/
def FlagOK (a : Alloc) : Prop :=
  a.writable = false ∧ 4 ≤ a.data.size ∧ ∀ i < 4, ∃ x, a.data[i]? = some (.b x)

/-- A memory of a run of the source: a defined flag and no write-barrier buffer. -/
structure MemOK (m : Mem) : Prop where
  flag : ∃ a, m.find? flagBlk = some a ∧ FlagOK a
  nobuf : m.find? .wbuf = none

theorem MemOK.set {m : Mem} (h : MemOK m) {b : Blk} (hf : b ≠ flagBlk) (hw : b ≠ .wbuf)
    (a : Alloc) : MemOK (m.set b a) := by
  obtain ⟨a', ha', hok⟩ := h.flag
  refine ⟨⟨a', ?_, hok⟩, ?_⟩
  · rw [CSE.Mem.find?_set, if_neg hf]; exact ha'
  · rw [CSE.Mem.find?_set, if_neg hw]; exact h.nobuf

/-- **Writes keep `MemOK`**: the flag is read-only, the buffer absent. -/
theorem MemOK.write {m m' : Mem} (h : MemOK m) {p : Ptr} {bs : Array Byte}
    (hw : m.write p bs = some m') : MemOK m' := by
  unfold Mem.write at hw
  by_cases he : bs.isEmpty = true
  · simp only [he, ↓reduceIte] at hw; cases hw; exact h
  · simp only [he, Bool.false_eq_true, ↓reduceIte] at hw
    cases ha : m.find? p.blk with
    | none => rw [ha] at hw; cases hw
    | some a =>
      rw [ha] at hw
      dsimp only [bind, Option.bind] at hw
      split at hw
      · rename_i hc
        cases hw
        have hwr : a.writable = true := by
          simp only [Bool.and_eq_true] at hc; exact hc.1.1.1.1
        refine h.set ?_ ?_ _
        · intro hb
          obtain ⟨a', ha', hok⟩ := h.flag
          rw [hb, ha'] at ha
          cases ha
          rw [hok.1] at hwr; cases hwr
        · intro hb
          rw [hb, h.nobuf] at ha; cases ha
      · cases hw

theorem MemOK.poison {m : Mem} (h : MemOK m) {b : Blk} (hf : b ≠ flagBlk) (hw : b ≠ .wbuf) :
    MemOK (m.poisonBlock b) := by
  unfold Mem.poisonBlock
  split
  · exact h.set hf hw _
  · exact h

theorem bytesNat?_four (x0 x1 x2 x3 : BitVec 8) :
    ∃ n, bytesNat? #[.b x0, .b x1, .b x2, .b x3] = some n := by
  exact ⟨_, rfl⟩

/-- **The flag load is an integer.** -/
theorem load_flag {m : Mem} (h : MemOK m) :
    ∃ x, m.load (.int .w32) ⟨flagBlk, 0⟩ = .int .w32 x := by
  obtain ⟨a, ha, -, hsz, hb⟩ := h.flag
  obtain ⟨x0, h0⟩ := hb 0 (by omega)
  obtain ⟨x1, h1⟩ := hb 1 (by omega)
  obtain ⟨x2, h2⟩ := hb 2 (by omega)
  obtain ⟨x3, h3⟩ := hb 3 (by omega)
  have hg : ∀ i (hi : i < a.data.size) {y}, a.data[i]? = some y → a.data[i] = y :=
    fun i hi y hy => by rw [Array.getElem?_eq_getElem hi] at hy; exact Option.some.inj hy
  have hex : a.data.extract 0 4 = #[.b x0, .b x1, .b x2, .b x3] := by
    apply Array.ext_getElem?
    intro i
    rcases i with _ | _ | _ | _ | i
    · simp [Array.getElem?_extract, show 0 < min 4 a.data.size by omega, hg 0 (by omega) h0]
    · simp [Array.getElem?_extract, show 1 < min 4 a.data.size by omega, hg 1 (by omega) h1]
    · simp [Array.getElem?_extract, show 2 < min 4 a.data.size by omega, hg 2 (by omega) h2]
    · simp [Array.getElem?_extract, show 3 < min 4 a.data.size by omega, hg 3 (by omega) h3]
    · simp [Array.getElem?_extract]; omega
  have hr : m.read ⟨flagBlk, 0⟩ 4 = some (a.data.extract 0 4) := by
    unfold Mem.read
    simp only [ha]
    simp [Blk.endsInWindow, Blk.window?, flagBlk, hsz]
  obtain ⟨n, hn⟩ := bytesNat?_four x0 x1 x2 x3
  refine ⟨BitVec.ofNat 32 n, ?_⟩
  unfold Mem.load
  simp only [Ty.size, Width.bytes, Width.bits, Nat.reduceDiv, hr, hex, decodeLoad, decode,
    decodeInt]
  rw [Array.extract_eq_self_of_le (by simp), hn]

/-! ## The buffer -/

theorem free_eq_erase (m : Mem) : m.free .wbuf = m.erase isW := rfl

theorem erase_of_none {m : Mem} (h : m.find? .wbuf = none) : m.erase isW = m := by
  refine mem_ext ?_ rfl rfl
  rw [erase_toList, List.filter_eq_self]
  intro e he
  rw [DSE.find?_toList, Option.map_eq_none_iff, List.find?_eq_none] at h
  have := h e he
  simp only [isW, Bool.not_eq_eq_eq_not, Bool.not_true]
  simpa using this

theorem erase_find_wbuf (m : Mem) : (m.erase isW).find? .wbuf = none := by
  rw [DSE.find?_toList, erase_toList, Option.map_eq_none_iff, List.find?_eq_none]
  intro e he
  rw [List.mem_filter] at he
  simpa [isW] using he.2

/-- The target memory is the source's, possibly with a buffer. -/
def W (mS mT : Mem) : Prop := mT.erase isW = mS ∧ mS.find? .wbuf = none

theorem W.refl {m : Mem} (h : m.find? .wbuf = none) : W m m := ⟨erase_of_none h, h⟩

theorem W.free {mS mT : Mem} (h : W mS mT) : mT.free .wbuf = mS := h.1

/-- **The same write** (the source's succeeds). -/
theorem W.write {mS mT mS' : Mem} (h : W mS mT) {p : Ptr} {bs : Array Byte}
    (hw : mS.write p bs = some mS') : ∃ mT', mT.write p bs = some mT' ∧ W mS' mT' := by
  by_cases he : bs.isEmpty = true
  · have h1 : mS.write p bs = some mS := by unfold Mem.write; simp [he]
    have h2 : mT.write p bs = some mT := by unfold Mem.write; simp [he]
    rw [h1] at hw; cases hw
    exact ⟨mT, h2, h⟩
  have hb : isW p.blk = false := by
    unfold Mem.write at hw
    simp only [he, Bool.false_eq_true, ↓reduceIte] at hw
    cases ha : mS.find? p.blk with
    | none => rw [ha] at hw; cases hw
    | some a =>
      simp only [isW, beq_eq_false_iff_ne]
      rintro hpb
      rw [hpb, h.2] at ha; cases ha
  have e1 := erase_write (m := mT) bs hb
  rw [h.1, hw] at e1
  cases hT : mT.write p bs with
  | none => rw [hT] at e1; cases e1
  | some mT' =>
    rw [hT] at e1
    simp only [Option.map_some, Option.some.injEq] at e1
    have hnb : mS'.find? .wbuf = none := by rw [e1]; exact erase_find_wbuf mT'
    exact ⟨mT', rfl, e1.symm, hnb⟩

theorem W.poison {mS mT : Mem} (h : W mS mT) {b : Blk} (hb : b ≠ .wbuf) :
    W (mS.poisonBlock b) (mT.poisonBlock b) := by
  have hx : isW b = false := by simp only [isW, beq_eq_false_iff_ne]; exact hb
  refine ⟨?_, ?_⟩
  · have := EqX.poison (X := isW) (show EqX isW mT mS from by
      unfold EqX; rw [h.1, erase_of_none h.2]) b
    unfold EqX at this
    rw [this, erase_of_none]
    unfold Mem.poisonBlock
    split
    · rw [CSE.Mem.find?_set, if_neg hb]; exact h.2
    · exact h.2
  · unfold Mem.poisonBlock
    split
    · rw [CSE.Mem.find?_set, if_neg hb]; exact h.2
    · exact h.2

theorem W.find {mS mT : Mem} (h : W mS mT) {b : Blk} (hb : b ≠ .wbuf) : mT.find? b = mS.find? b := by
  rw [← h.1, TabsMod.erase_find (by simp [isW, hb])]

/-- **The same read** (the source's succeeds). -/
theorem W.read {mS mT : Mem} (h : W mS mT) {p : Ptr} {n : Nat} {bs : Array Byte}
    (hr : mS.read p n = some bs) : mT.read p n = some bs := by
  by_cases hb : p.blk = .wbuf
  · by_cases hn : n = 0
    · subst hn; unfold Mem.read at hr ⊢; simpa using hr
    · exfalso
      unfold Mem.read at hr
      rw [hb, h.2] at hr
      simp [hn] at hr
  · have he : mT.read p n = mS.read p n := by unfold Mem.read; rw [W.find h hb]
    rw [he]; exact hr

/-- A memory of the buffer block of a write-barrier sequence: `M` with a writable buffer of
`8 n` bytes, `n ≤ 8`. -/
def Buf (M : Mem) (n : Nat) (m : Mem) : Prop :=
  m.erase isW = M ∧ n ≤ 8 ∧ ∃ a, m.find? .wbuf = some a ∧ a.data.size = 8 * n ∧ a.writable = true

theorem buf_wbAlloc {M m : Mem} (h : W M m) {n : Nat} (hn : n ≤ 8) : Buf M n (m.wbAlloc n) := by
  refine ⟨?_, hn, { data := Array.replicate (8 * n) .poison }, ?_, by simp, rfl⟩
  · unfold Mem.wbAlloc; rw [erase_set_X (by rfl)]; exact h.1
  · unfold Mem.wbAlloc; rw [CSE.Mem.find?_set, if_pos rfl]

theorem buf_wbAlloc' {M m : Mem} {n' : Nat} (h : Buf M n' m) {n : Nat} (hn : n ≤ 8) :
    Buf M n (m.wbAlloc n) := by
  refine ⟨?_, hn, { data := Array.replicate (8 * n) .poison }, ?_, by simp, rfl⟩
  · unfold Mem.wbAlloc; rw [erase_set_X (by rfl)]; exact h.1
  · unfold Mem.wbAlloc; rw [CSE.Mem.find?_set, if_pos rfl]

theorem Buf.w {M m : Mem} {n : Nat} (h : Buf M n m) (hM : M.find? .wbuf = none) : W M m :=
  ⟨h.1, hM⟩

/-- **A buffer store succeeds**: 8 bytes at entry `j < n`. -/
theorem Buf.write {M m : Mem} {n : Nat} (h : Buf M n m) {j : Nat} (hj : j < n) {bs : Array Byte}
    (hbs : bs.size = 8) : ∃ m', m.write ⟨.wbuf, BitVec.ofNat 64 (8 * j)⟩ bs = some m' ∧
      Buf M n m' := by
  obtain ⟨he, hn, a, ha, hsz, hwr⟩ := h
  have hne : bs.isEmpty = false := by
    rw [Bool.eq_false_iff]; intro h; rw [Array.isEmpty_iff_size_eq_zero] at h; omega
  have hoff : (BitVec.ofNat 64 (8 * j)).toNat = 8 * j := by
    rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; omega
  unfold Mem.write
  simp only [hne, Bool.false_eq_true, ↓reduceIte, ha]
  dsimp only [bind, Option.bind]
  rw [if_pos (by simp [hwr, hoff, hbs, hsz, Blk.endsInWindow, Blk.window?, Blk.writableFrom]; omega)]
  refine ⟨_, rfl, ?_, hn, _, by rw [CSE.Mem.find?_set, if_pos rfl], ?_, ?_⟩
  · rw [erase_set_X (by rfl)]; exact he
  · show (List.foldl _ a.data _).size = _; rw [CSE.Mem.foldl_set_size]; exact hsz
  · exact hwr

theorem MemOK.free_wbuf {m : Mem} (h : MemOK m) : MemOK (m.free .wbuf) := by
  obtain ⟨a, ha, hok⟩ := h.flag
  refine ⟨⟨a, ?_, hok⟩, ?_⟩
  · rw [free_eq_erase, TabsMod.erase_find (by rfl)]; exact ha
  · rw [free_eq_erase]; exact erase_find_wbuf m

/-- `MemOK` is kept by every `set` of a block that is neither a global nor the buffer. -/
theorem memOK_set {m : Mem} {b : Blk} (a : Alloc) (h : MemOK m) (hg : ∀ n, b ≠ .global n)
    (hw : b ≠ .wbuf) : MemOK (m.set b a) := h.set (hg "runtime.writeBarrier") hw a

/-- **`MemOK` is a memory invariant** (`MemInv.MemPred`): the flag is a global, the buffer
absent; the runtime's blocks are other globals. -/
theorem memOK_pred : MemInv.MemPred MemOK where
  write h hw := h.write hw
  poison h hg hw := MemInv.poison_of_set memOK_set h hg hw
  poisonBelow n h hg hw := MemInv.poisonBelow_of_set memOK_set n h hg hw
  free_wbuf h := h.free_wbuf
  rt a hb _ _ h := by
    rcases hb with rfl | rfl <;> exact h.set (by decide) (by decide) a

end GoFV.Proof.WB
