import GoFV.Proof.Pass.ECChain
import GoFV.Proof.Pass.LoadFwdMem
import GoFV.Proof.Pass.MemCombineBytes
import GoFV.Proof.MemRefine

/-!
# `expand calls`: stack-assigned call arguments (issue #28)

A stack-assigned argument of a call becomes a chain of new `Store`s (one per leaf of its shape)
into the outgoing-arguments area of the activation, on the source call's memory; the call's
memory argument is the last store. The source call (`callOp`) is `stuck` unless those slots are
writable (`outargsOK`), so:

* the stores never get stuck once the source has reached the call (`NewObl`, `ecs_storeObl`);
* the post-`expand calls` call decodes the arguments from the stored bytes
  (`ecs_writes_read`, `decode_atom`, `build_decode`), and its callee sees the area poisoned, so
  the stores are invisible to it (`ecs_writeAll_poison`).
-/

namespace GoFV.Proof.EC

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.ECCheck GoFV.Proof.ABI GoFV.Proof.AtomSim GoFV.Proof.CSE.Mem

/-! ## Writable ranges and writes -/

/-- What `canWrite` reads of an allocation. -/
def ecsAttr (a : Alloc) : Bool × Nat := (a.writable, a.data.size)

theorem ecs_canWrite_congr {m m' : Mem}
    (h : ∀ b, (m'.find? b).map ecsAttr = (m.find? b).map ecsAttr) (p : Ptr) (n : Nat) :
    m'.canWrite p n = m.canWrite p n := by
  unfold Mem.canWrite
  have hb := h p.blk
  cases h1 : m.find? p.blk with
  | none =>
    rw [h1] at hb
    cases h2 : m'.find? p.blk with
    | none => rfl
    | some a' => rw [h2] at hb; cases hb
  | some a =>
    rw [h1] at hb
    cases h2 : m'.find? p.blk with
    | none => rw [h2] at hb; cases hb
    | some a' =>
      rw [h2] at hb
      simp only [Option.map_some, Option.some.injEq, ecsAttr, Prod.mk.injEq] at hb
      simp only [hb.1, hb.2]

/-- A write keeps every allocation's writability and size. -/
theorem ecs_find_write {m m' : Mem} {p : Ptr} {bs : Array Byte} (hw : m.write p bs = some m')
    (b : Blk) : (m'.find? b).map ecsAttr = (m.find? b).map ecsAttr := by
  unfold Mem.write at hw
  by_cases he : bs.isEmpty = true
  · simp only [he, ite_true] at hw; cases hw; rfl
  simp only [he, Bool.false_eq_true, ite_false] at hw
  cases ha : m.find? p.blk with
  | none => rw [ha] at hw; cases hw
  | some a =>
    rw [ha] at hw
    simp only [Option.bind_eq_bind, Option.bind_some] at hw
    split at hw
    · cases hw
      rw [find?_set]
      split
      · next hb =>
        subst hb; rw [ha]
        simp only [Option.map_some, ecsAttr, foldl_set_size]
      · rfl
    · cases hw

theorem ecs_canWrite_write {m m' : Mem} {p : Ptr} {bs : Array Byte} (hw : m.write p bs = some m')
    (q : Ptr) (n : Nat) : m'.canWrite q n = m.canWrite q n :=
  ecs_canWrite_congr (ecs_find_write hw) q n

theorem ecs_outargsOK_write {m m' : Mem} {p : Ptr} {bs : Array Byte} (hw : m.write p bs = some m')
    (tabs : Tables) (act : Nat) (ps : List ABIParam) :
    outargsOK tabs act m' ps = outargsOK tabs act m ps := by
  unfold outargsOK
  simp only [ecs_canWrite_write hw]

theorem ecs_canWrite_pos {m : Mem} {p : Ptr} {n : Nat} (hn : n ≠ 0) :
    m.canWrite p n = (match m.find? p.blk with
      | some a => a.writable && decide (p.off.toNat + n ≤ a.data.size) &&
          decide (p.off.toNat + n < 2 ^ 64) && p.blk.endsInWindow (p.off.toNat + n)
      | none => false) := by
  unfold Mem.canWrite
  simp only [show (n == 0) = false from by simp [hn], Bool.false_or]
  cases m.find? p.blk <;> rfl

/-- A writable range takes any write of its size. -/
theorem ecs_write_of_canWrite {m : Mem} {p : Ptr} {bs : Array Byte}
    (h : m.canWrite p bs.size = true) : ∃ m', m.write p bs = some m' := by
  unfold Mem.write
  by_cases he : bs.isEmpty = true
  · simp only [he, ite_true]; exact ⟨_, rfl⟩
  have hn : bs.size ≠ 0 := fun h0 => he (by simp [Array.isEmpty, h0])
  simp only [he, Bool.false_eq_true, ite_false]
  rw [ecs_canWrite_pos hn] at h
  cases ha : m.find? p.blk with
  | none => rw [ha] at h; cases h
  | some a =>
    rw [ha] at h
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [if_pos h]
    exact ⟨_, rfl⟩

/-- A writable range can be read. -/
theorem ecs_read_of_canWrite {m : Mem} {p : Ptr} {n : Nat} (h : m.canWrite p n = true) :
    ∃ bs, m.read p n = some bs := by
  unfold Mem.read
  by_cases hn : n = 0
  · simp [hn]
  rw [ecs_canWrite_pos hn] at h
  simp only [hn, beq_iff_eq, ite_false]
  cases ha : m.find? p.blk with
  | none => rw [ha] at h; cases h
  | some a =>
    rw [ha] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [if_pos ⟨h.1.1.2, h.1.2, h.2⟩]
    exact ⟨_, rfl⟩

/-- A writable range's sub-ranges are writable. -/
theorem ecs_canWrite_sub {m : Mem} {b : Blk} {o n k l : Nat} (hkl : k + l ≤ n)
    (h : m.canWrite ⟨b, BitVec.ofNat 64 o⟩ n = true) (ho : o < 2 ^ 64) :
    m.canWrite ⟨b, BitVec.ofNat 64 (o + k)⟩ l = true := by
  by_cases hl : l = 0
  · unfold Mem.canWrite; simp [hl]
  have hn : n ≠ 0 := by omega
  rw [ecs_canWrite_pos hn] at h
  rw [ecs_canWrite_pos hl]
  cases ha : m.find? b with
  | none => rw [ha] at h; cases h
  | some a =>
    rw [ha] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    obtain ⟨⟨⟨hw, h1⟩, h2⟩, h3⟩ := h
    have e1 : (BitVec.ofNat 64 o).toNat = o := by simp [Nat.mod_eq_of_lt ho]
    rw [e1] at h1 h2 h3
    have e2 : (BitVec.ofNat 64 (o + k)).toNat = o + k := by
      simp [Nat.mod_eq_of_lt (show o + k < 2 ^ 64 by omega)]
    rw [e2]
    refine ⟨⟨⟨hw, by omega⟩, by omega⟩, ?_⟩
    unfold Blk.endsInWindow at h3 ⊢
    split at h3
    · simp only [decide_eq_true_eq] at h3 ⊢
      omega
    · rfl

/-- A sub-range of a read. -/
theorem ecs_read_sub {m : Mem} {b : Blk} {o n k l : Nat} {bs : Array Byte} (hkl : k + l ≤ n)
    (hl : l ≠ 0) (h : m.read ⟨b, BitVec.ofNat 64 o⟩ n = some bs) (ho : o + n < 2 ^ 64) :
    m.read ⟨b, BitVec.ofNat 64 (o + k)⟩ l = some (bs.extract k (k + l)) := by
  unfold Mem.read at h ⊢
  have hn : n ≠ 0 := by omega
  simp only [hn, hl, beq_iff_eq, ite_false] at h ⊢
  cases ha : m.find? b with
  | none => rw [ha] at h; cases h
  | some a =>
    rw [ha] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h ⊢
    have e1 : (BitVec.ofNat 64 o).toNat = o := by simp [Nat.mod_eq_of_lt (by omega : o < 2 ^ 64)]
    have e2 : (BitVec.ofNat 64 (o + k)).toNat = o + k := by
      simp [Nat.mod_eq_of_lt (show o + k < 2 ^ 64 by omega)]
    rw [e1] at h
    rw [e2]
    split at h
    · rename_i hc
      cases h
      obtain ⟨h1, -, h3⟩ := hc
      have hwin : b.endsInWindow (o + k + l) = true := by
        unfold Blk.endsInWindow at h3 ⊢
        split at h3
        · simp only [decide_eq_true_eq] at h3 ⊢
          omega
        · rfl
      rw [if_pos ⟨by omega, by omega, hwin⟩]
      congr 1
      rw [Array.extract_extract]
      congr 1 <;> omega
    · cases h

/-- A write into block `b` vanishes when `b` is poisoned. -/
theorem ecs_poisonBlock_write {m m' : Mem} {p : Ptr} {bs : Array Byte}
    (hw : m.write p bs = some m') : m'.poisonBlock p.blk = m.poisonBlock p.blk := by
  unfold Mem.write at hw
  by_cases he : bs.isEmpty = true
  · simp only [he, ite_true] at hw; cases hw; rfl
  simp only [he, Bool.false_eq_true, ite_false] at hw
  cases ha : m.find? p.blk with
  | none => rw [ha] at hw; cases hw
  | some a =>
    rw [ha] at hw
    simp only [Option.bind_eq_bind, Option.bind_some] at hw
    split at hw
    · cases hw
      unfold Mem.poisonBlock
      rw [find?_set, if_pos rfl, ha]
      dsimp only
      rw [GoFV.Proof.MemCombine.set_set, foldl_set_size]
    · cases hw

/-! ## Sequences of writes -/

/-- The writes `ws` in order. -/
def writeAll : Mem → List (Ptr × Array Byte) → Option Mem
  | m, [] => some m
  | m, (p, bs) :: ws => (m.write p bs).bind (writeAll · ws)

theorem writeAll_append {m : Mem} {ws ws' : List (Ptr × Array Byte)} {m' : Mem}
    (h : writeAll m ws = some m') : writeAll m (ws ++ ws') = writeAll m' ws' := by
  induction ws generalizing m with
  | nil => cases h; rfl
  | cons e ws ih =>
    obtain ⟨p, bs⟩ := e
    simp only [writeAll, List.cons_append] at h ⊢
    cases hw : m.write p bs with
    | none => rw [hw] at h; cases h
    | some m1 => rw [hw] at h; simp only [Option.bind_some] at h ⊢; exact ih h

theorem writeAll_snoc {m m1 m' : Mem} {ws : List (Ptr × Array Byte)} {p : Ptr} {bs : Array Byte}
    (h : writeAll m ws = some m1) (hw : m1.write p bs = some m') :
    writeAll m (ws ++ [(p, bs)]) = some m' := by
  rw [writeAll_append h]; simp [writeAll, hw]

theorem writeAll_attr {m m' : Mem} :
    ∀ {ws : List (Ptr × Array Byte)}, writeAll m ws = some m' →
      ∀ b, (m'.find? b).map ecsAttr = (m.find? b).map ecsAttr
  | [], h, b => by cases h; rfl
  | (p, bs) :: ws, h, b => by
    simp only [writeAll] at h
    cases hw : m.write p bs with
    | none => rw [hw] at h; cases h
    | some m1 =>
      rw [hw] at h
      exact (writeAll_attr (m := m1) h b).trans (ecs_find_write hw b)

theorem writeAll_outargsOK {m m' : Mem} {ws : List (Ptr × Array Byte)} (h : writeAll m ws = some m')
    (tabs : Tables) (act : Nat) (ps : List ABIParam) :
    outargsOK tabs act m' ps = outargsOK tabs act m ps := by
  unfold outargsOK
  simp only [ecs_canWrite_congr (writeAll_attr h)]

/-- Writes into block `b` vanish when `b` is poisoned. -/
theorem writeAll_poison {m m' : Mem} {b : Blk} :
    ∀ {ws : List (Ptr × Array Byte)}, (∀ e ∈ ws, e.1.blk = b) → writeAll m ws = some m' →
      m'.poisonBlock b = m.poisonBlock b
  | [], _, h => by cases h; rfl
  | (p, bs) :: ws, hb, h => by
    simp only [writeAll] at h
    cases hw : m.write p bs with
    | none => rw [hw] at h; cases h
    | some m1 =>
      rw [hw] at h
      rw [writeAll_poison (fun e he => hb e (List.mem_cons_of_mem _ he)) h,
        ← hb (p, bs) List.mem_cons_self, ecs_poisonBlock_write hw]

/-- A write that no later write overlaps reads back. -/
theorem writeAll_read {p : Ptr} {bs : Array Byte} :
    ∀ {A B : List (Ptr × Array Byte)} {m m' : Mem}, writeAll m (A ++ (p, bs) :: B) = some m' →
      (∀ e ∈ B, Sep p bs.size e.1 e.2.size) → m'.read p bs.size = some bs
  | (q, cs) :: A, B, m, m', h, hs => by
    simp only [writeAll, List.cons_append] at h
    cases hw : m.write q cs with
    | none => rw [hw] at h; cases h
    | some m1 => rw [hw] at h; exact writeAll_read h hs
  | [], B, m, m', h, hs => by
    simp only [writeAll, List.nil_append] at h
    cases hw : m.write p bs with
    | none => rw [hw] at h; cases h
    | some m1 =>
      rw [hw] at h
      simp only [Option.bind_some] at h
      have h1 := GoFV.Proof.Pass.LoadFwd.read_write_self hw
      clear hw
      induction B generalizing m1 with
      | nil => cases h; exact h1
      | cons e B ih =>
        obtain ⟨q, cs⟩ := e
        simp only [writeAll] at h
        cases hw : m1.write q cs with
        | none => rw [hw] at h; cases h
        | some m2 =>
          rw [hw] at h
          exact ih (fun e he => hs e (List.mem_cons_of_mem _ he)) m2 h
            (by rw [read_write_sep hw (hs (q, cs) List.mem_cons_self)]; exact h1)

end GoFV.Proof.EC
