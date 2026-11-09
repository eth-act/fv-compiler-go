import GoFV.Proof.PtrAddr
import GoFV.Proof.Pass.ECChain
import GoFV.Proof.Pass.LoadFwdMem
import GoFV.Proof.Pass.MemCombineBytes
import GoFV.Proof.MemRefine
import GoFV.Proof.Pass.ECTree

variable [GoFV.SSA.Sem.Addrs]

/-!
# `expand calls`: stack-assigned call arguments (issue #28)

A stack-assigned argument of a call becomes a chain of new `Store`s (one per leaf of its shape)
into the outgoing-arguments area of the activation, on the source call's memory; the call's
memory argument is the last store. The source call (`callOp`) is `stuck` unless those slots are
writable (`outargsOK`), so:

* the stores never get stuck once the source has reached the call (`ECCall.ecc_storeObl`, with
  `ecs_chain_attr`: the stores below keep the writable ranges, `ecs_addr`: a store's address is
  its slot, `OffPtr [off]` of `SP` as a pointer or a `uintptr`);
* the chain writes the slots in order (`ecs_chain`), they read back (`ecs_reads`, disjoint by
  `ecs_leafSlots_pairwise`), and the post-`expand calls` call decodes from them refinements of
  the Go-typed arguments (`ecs_stack_params`: `decode_atom`-style leaf reads, `build_decode`);
  its callee sees the area poisoned, so the stores are invisible to it (`writeAll_poison`).
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

/-- A write below offset `n` into block `b` vanishes when `b`'s bytes below `n` are poisoned. -/
theorem ecs_poisonBelow_write {m m' : Mem} {p : Ptr} {bs : Array Byte} {n : Nat}
    (hw : m.write p bs = some m') (hn : p.off.toNat + bs.size ≤ n) :
    m'.poisonBelow p.blk n = m.poisonBelow p.blk n := by
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
      unfold Mem.poisonBelow
      rw [find?_set, if_pos rfl, ha]
      dsimp only
      rw [GoFV.Proof.MemCombine.set_set]
      have hd : ((List.range bs.size).foldl (fun d i => d.set! (p.off.toNat + i) bs[i]!) a.data).mapIdx
          (fun i x => if i < n then Byte.poison else x) =
          a.data.mapIdx (fun i x => if i < n then Byte.poison else x) := by
        apply Array.ext
        · rw [Array.size_mapIdx, Array.size_mapIdx, foldl_set_size]
        · intro i h1 h2
          simp only [Array.getElem_mapIdx]
          split
          · rfl
          · have := foldl_set_get p.off.toNat bs i (List.range bs.size) a.data
              (fun k hk => by simp only [List.mem_range] at hk; omega)
            simp only [Array.size_mapIdx] at h1 h2
            rw [Array.getElem?_eq_getElem h2] at this
            rw [Array.getElem?_eq_getElem (by rwa [foldl_set_size])] at this
            exact Option.some.inj this
      rw [hd]
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

/-- The frame end of a call bounds the `max` fold `callFrame` starts from. -/
private theorem callFrame_fold_ge (tabs : Tables) :
    ∀ (ins : List ABIParam) (n : Nat), n ≤ ins.foldl (fun n p =>
      if p.regs.isEmpty then max n ((BitVec.ofInt 64 p.offset).toNat + (tabs.ty p.type).size)
      else n) n
  | [], _ => Nat.le_refl _
  | p :: ps, n => by
    rw [List.foldl_cons]
    refine Nat.le_trans ?_ (callFrame_fold_ge tabs ps _)
    split
    · exact Nat.le_max_left _ _
    · exact Nat.le_refl _

/-- **A stack-assigned input parameter's slot lies below its call's frame end.** -/
theorem slot_le_callFrame {tabs : Tables} {aux : Option AuxRef} {ins : List ABIParam}
    {p : ABIParam} (hp : p ∈ ins) (hr : p.regs.isEmpty = true) (sp : Bool) :
    (BitVec.ofInt 64 p.offset).toNat + (tabs.ty p.type).size ≤ callFrame tabs aux ins sp := by
  unfold callFrame
  generalize (if sp then ((callABI? tabs aux).map fun a => (a.spillOff + a.spillSize).toNat).getD 0
    else 0) = n
  induction ins generalizing n with
  | nil => cases hp
  | cons q qs ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.1 hp with rfl | hq
    · refine Nat.le_trans ?_ (callFrame_fold_ge tabs qs _)
      rw [if_pos hr]
      exact Nat.le_max_right _ _
    · exact ih hq _

/-- Writes into block `b` below offset `n` vanish when `b`'s bytes below `n` are poisoned. -/
theorem writeAll_poisonBelow {m m' : Mem} {b : Blk} {n : Nat} :
    ∀ {ws : List (Ptr × Array Byte)}, (∀ e ∈ ws, e.1.blk = b ∧ e.1.off.toNat + e.2.size ≤ n) →
      writeAll m ws = some m' → m'.poisonBelow b n = m.poisonBelow b n
  | [], _, h => by cases h; rfl
  | (p, bs) :: ws, hb, h => by
    simp only [writeAll] at h
    cases hw : m.write p bs with
    | none => rw [hw] at h; cases h
    | some m1 =>
      rw [hw] at h
      have hp := hb (p, bs) List.mem_cons_self
      rw [writeAll_poisonBelow (fun e he => hb e (List.mem_cons_of_mem _ he)) h, ← hp.1,
        ecs_poisonBelow_write hw hp.2]

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

/-! ## Addresses and stores -/

/-- The pointer of offset `o` in the outgoing-arguments area of activation 0 (`Ctx.make`). -/
abbrev ecsSlot (o : Nat) : Ptr := ⟨.outargs 0, BitVec.ofNat 64 o⟩

theorem ecs_ofInt {o : Int} (h : 0 ≤ o) : BitVec.ofInt 64 o = BitVec.ofNat 64 o.toNat := by
  conv => lhs; rw [← Int.toNat_of_nonneg h]
  exact BitVec.ofInt_natCast 64 o.toNat

/-- `SP` evaluates to the start of the outgoing-arguments area, at its shape. -/
theorem ecs_sp_val {env : Env} {tabs : Tables} {g : Func} {T : Frame} {s : ID} {sw : Value}
    {ys : Val} (hsw : g.value? s = some sw) (hid : sw.id = s) (hop : sw.op = .SP)
    (hev : evalValue env (Ctx.make tabs g) T sw = .ok ys) :
    ys = (Val.ptr (ecsSlot 0)).retype (shapeOf (typeShapes tabs) g s) := by
  have hreg : ∀ a ∈ sw.args, Reg T a :=
    evalValue_args_def fun msg h => by rw [hev] at h; cases h
  rw [evalValue_of_regs hreg] at hev
  have hf : frameVal (Ctx.make tabs g) sw = some (.ptr (ecsSlot 0)) := by
    unfold frameVal; rw [hop]; rfl
  have he : evalOp env (Ctx.make tabs g) T sw (sw.args.toList.map (rv T))
      ((Ctx.make tabs g).tys[sw.id]?.getD .other) = .ok (.ptr (ecsSlot 0)) := by
    unfold evalOp; rw [hop]; dsimp only; rw [hf]; rfl
  rw [he] at hev
  cases hev
  rw [shapeOf_eq, hid]

private theorem ecs_ptr_inWindow {k : Nat} (hk : k < 2 ^ 24) : (ecsSlot k).inWindow = true := by
  simp only [Ptr.inWindow, Blk.window?, decide_eq_true_eq]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  exact hk

/-- `OffPtr [k]` of the area's start, as a pointer: slot `k`'s word. -/
theorem ecs_offPtr_ptr {ai : Int64} {k : Nat} (hai : ai.toInt = k) (hk : k < 2 ^ 24) :
    PtrOps.offPtr ai [.ptr (ecsSlot 0)] = (ecsSlot k).word := by
  simp only [PtrOps.offPtr, hai, BitVec.ofInt_natCast, Ptr.add, ecsSlot]
  rw [show BitVec.ofNat 64 0 + BitVec.ofNat 64 k = BitVec.ofNat 64 k by simp]
  simp only [PtrOps.ptrRes]
  rw [if_pos (ecs_ptr_inWindow hk)]

/-- `OffPtr [k]` of the area's start as a `uintptr`, read as a pointer: slot `k` (a word, §3.3,
whatever the address assignment). -/
theorem ecs_offPtr_int {ai : Int64} {k : Nat} (hai : ai.toInt = k) (hk : k < 2 ^ 24) (e : Option Nat) :
    ((PtrOps.offPtr ai [(Val.ptr (ecsSlot 0)).retype (.int .w64)]).retype (.ptr e)).asPtrWord =
      some (ecsSlot k) := by
  have h1 : (Val.ptr (ecsSlot 0)).retype (.int .w64) = (ecsSlot 0).word := rfl
  rw [h1, PtrOps.offPtr_word ai (ecs_ptr_inWindow (by decide)), ecs_offPtr_ptr hai hk,
    Ptr.word_retype_ptr, Ptr.word_asPtrWord (ecs_ptr_inWindow hk)]

/-- `Store`'s write (`memRoot`). -/
theorem ecs_store_inv {ctx : Ctx} {u : Value} {argv : List Val} {y : Val} (hu : u.op = .Store)
    (h : memRoot ctx u argv = .ok y) : ∃ a q x M M', argv = [a, x, .mem M] ∧
      a.asPtrWord = some q ∧ M.write q (encode (auxTy ctx.tabs u.aux) x) = some M' ∧
      y = .mem M' := by
  unfold memRoot at h
  rw [hu] at h
  split at h
  all_goals first
    | contradiction
    | (split at h
       · simp only [writeRes] at h; split at h
         · cases h; exact ⟨_, _, _, _, _, rfl, ‹_›, ‹_›, rfl⟩
         · cases h
       · cases h)
    | (simp only at h; split at h <;> cases h)

/-- A `Store` of shape `mem` whose write succeeds evaluates to it. -/
theorem ecs_store_eval {env : Env} {ctx : Ctx} {fr : Frame} {u : Value} (hu : u.op = .Store)
    (hreg : ∀ a ∈ u.args, Reg fr a) (hargs : u.args.toList = [u.args[0]!, u.args[1]!, u.args[2]!])
    (hty : ctx.tys[u.id]?.getD .other = .mem) {q : Ptr} {M M' : Mem}
    (hq : (rv fr u.args[0]!).asPtrWord = some q) (hm : rv fr u.args[2]! = .mem M)
    (hw : M.write q (encode (auxTy ctx.tabs u.aux) (rv fr u.args[1]!)) = some M') :
    evalValue env ctx fr u = .ok (.mem M') := by
  rw [evalValue_of_regs hreg, hty, hargs]
  have he : evalOp env ctx fr u [rv fr u.args[0]!, rv fr u.args[1]!, rv fr u.args[2]!] .mem =
      memRoot ctx u [rv fr u.args[0]!, rv fr u.args[1]!, rv fr u.args[2]!] := by
    unfold evalOp; rw [hu]
  simp only [List.map_cons, List.map_nil]
  rw [he, hm]
  unfold memRoot
  rw [hu]
  dsimp only
  rw [hq]
  dsimp only
  rw [hw]
  rfl

/-- A `Store`'s evaluation: the write of its value at its address into its memory. -/
theorem ecs_store_val {env : Env} {ctx : Ctx} {fr : Frame} {u : Value} {y : Val}
    (hu : u.op = .Store) (hargs : u.args.toList = [u.args[0]!, u.args[1]!, u.args[2]!])
    (hty : ctx.tys[u.id]?.getD .other = .mem) (h : evalValue env ctx fr u = .ok y) :
    ∃ q M M', (rv fr u.args[0]!).asPtrWord = some q ∧ rv fr u.args[2]! = .mem M ∧
      M.write q (encode (auxTy ctx.tabs u.aux) (rv fr u.args[1]!)) = some M' ∧ y = .mem M' := by
  have hreg := regs_of_ok h
  rw [evalValue_of_regs hreg, hty, hargs] at h
  have he : ∀ argv, evalOp env ctx fr u argv .mem = memRoot ctx u argv := fun _ => by
    unfold evalOp; rw [hu]
  simp only [List.map_cons, List.map_nil, he] at h
  cases hr : memRoot ctx u [rv fr u.args[0]!, rv fr u.args[1]!, rv fr u.args[2]!] with
  | ok r =>
    rw [hr] at h
    obtain ⟨a, q, x, M, M', hl, hq, hw, rfl⟩ := ecs_store_inv hu hr
    simp only [List.cons.injEq, and_true] at hl
    obtain ⟨h1, h2, h3⟩ := hl
    cases h
    exact ⟨q, M, M', by rw [h1]; exact hq, h3, by rw [h2]; exact hw, rfl⟩
  | panic e m => rw [hr] at h; cases h
  | stuck msg => rw [hr] at h; cases h

/-- Shapes `eqE` to a leaf shape encode alike. -/
theorem ecs_encode_eqE {s t : Ty} (ht : atom t = true) (h : eqE s t = true) (v : Val) :
    encode s v = encode t v := by
  have he : erase s = erase t := Ty.eq_of_beq h
  cases t with
  | ptr e =>
    cases s <;> simp only [erase, reduceCtorEq] at he
    cases v <;> try rfl
    rename_i w x; cases w <;> rfl
  | int w =>
    cases s <;> simp only [erase, reduceCtorEq] at he
    cases he; rfl
  | bool => cases s <;> simp only [erase, reduceCtorEq] at he; rfl
  | «opaque» n =>
    cases s <;> simp only [erase, reduceCtorEq] at he
    cases he; rfl
  | _ => simp [atom] at ht

theorem ecs_args_three {arr : Array ID} (h : arr.size = 3) :
    arr.toList = [arr[0]!, arr[1]!, arr[2]!] := by
  rcases arr with ⟨l⟩
  match l, h with
  | [x, y, z], _ => rfl

/-- The target register of `x` holds its evaluation: a new value of `E`, or a held one. -/
theorem ecs_holds_of_new {env : Env} {tabs : Tables} {f g : Func} {T : Frame} {E L : ID → Prop}
    (hNC : NewCons env (Ctx.make tabs g) (isNewB f) T E)
    (hL : ∀ z, L z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, isNewB f a = true → L a)
    {x : ID} (hE : E x) (hLx : L x) : EcTgtHolds env tabs g T x := by
  intro w hw
  obtain ⟨-, w', y, hw', -, hy, hev⟩ := hNC x hE
  change g.value? x = some w' at hw'
  rw [hw] at hw'; cases hw'
  exact ⟨(hL x hLx w hw).1, y, hy, hev⟩

/-- **The address of a stack-argument store** (`spOffOK`): the register of its `OffPtr [off]`
of `SP` holds the slot's pointer. -/
theorem ecs_addr {env : Env} {tabs : Tables} {f g : Func} {T : Frame} {E L : ID → Prop}
    (hNC : NewCons env (Ctx.make tabs g) (isNewB f) T E)
    (hL : ∀ z, L z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, isNewB f a = true → L a)
    {q : ID} {off : Int} (hok : spOffOK (typeShapes tabs) g (isNewB f) q off = true)
    (hEq : E q) (hLq : L q)
    (hsp : ∀ qw, g.value? q = some qw → isNewB f qw.args[0]! = false →
      EcTgtHolds env tabs g T qw.args[0]!) :
    ∃ a, T.regs[q]? = some (some a) ∧ a.asPtrWord = some (ecsSlot off.toNat) := by
  unfold spOffOK at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨-, h0⟩, h24⟩, hm⟩ := hok
  obtain ⟨-, qw, yq, hqw, hcl, hyq, hevq⟩ := hNC q hEq
  change g.value? q = some qw at hqw
  obtain ⟨hqid, hLcl⟩ := hL q hLq qw hqw
  rw [hqw] at hm
  dsimp only at hm
  simp only [Bool.and_eq_true, beq_iff_eq] at hm
  obtain ⟨⟨⟨⟨hop, hai⟩, hsz⟩, hqsh⟩, hspop, hssh⟩ := hm
  have hk : off.toNat < 2 ^ 24 := by omega
  have hai' : qw.auxInt.toInt = (off.toNat : Int) := by rw [hai]; omega
  -- the `SP`
  have hS : EcTgtHolds env tabs g T qw.args[0]! := by
    cases hn : isNewB f qw.args[0]! with
    | false => exact hsp qw hqw hn
    | true =>
      have hm0 : qw.args[0]! ∈ qw.args := by
        rw [← Array.mem_toList_iff, ec_args_one hsz]; exact List.mem_singleton_self _
      exact ecs_holds_of_new hNC hL (hcl _ hm0 hn) (hLcl _ hm0 hn)
  obtain ⟨sw, hsw, hspop'⟩ : ∃ sw, g.value? qw.args[0]! = some sw ∧ sw.op = .SP := by
    cases h : g.value? qw.args[0]! with
    | none => rw [h] at hspop; cases hspop
    | some sw => rw [h] at hspop; exact ⟨sw, rfl, beq_iff_eq.1 hspop⟩
  obtain ⟨hsid, ys, hys, hevs⟩ := hS sw hsw
  have hysv := ecs_sp_val hsw hsid hspop' hevs
  -- the `OffPtr`
  have hv := evalValue_term (by rw [hop]; decide) hevq
  rw [hop, GoFV.Proof.Rules.opVal_pure (by decide), ec_args_one hsz, hqid, ← shapeOf_eq] at hv
  simp only [List.map_cons, List.map_nil, rv_of hys, hysv] at hv
  change yq = (PtrOps.offPtr qw.auxInt [Val.retype (shapeOf (typeShapes tabs) g qw.args[0]!)
    (.ptr (ecsSlot 0))]).retype (shapeOf (typeShapes tabs) g q) at hv
  refine ⟨yq, hyq, ?_⟩
  rw [hv]
  split at hqsh
  · next e he =>
    rw [he]
    split at hssh
    · next e' he' =>
      rw [he']
      rw [show Val.retype (.ptr e') (.ptr (ecsSlot 0)) = (ecsSlot 0).word from rfl,
        PtrOps.offPtr_word _ (ecs_ptr_inWindow (k := 0) (by decide)), ecs_offPtr_ptr hai' hk,
        Ptr.word_retype_ptr, Ptr.word_asPtrWord (ecs_ptr_inWindow hk)]
    · next he' =>
      rw [he']
      exact ecs_offPtr_int hai' hk e
    · cases hssh
  · cases hqsh

/-! ## Chains of stores -/

/-- The write of a stack-argument store at slot `s` (offset, leaf shape) of the value `y`. -/
def ecsW (s : Int × Ty) (y : Val) : Ptr × Array Byte := (ecsSlot s.1.toNat, encode s.2 y)

theorem ecs_storesOK_length {tabs : Tables} {sh : Array Ty} {g : Func} {nw : ID → Bool} :
    ∀ {ss : List (Int × Ty)} {zs : List ID}, storesOK tabs sh g nw ss zs = true → ss.length = zs.length
  | [], [], _ => rfl
  | [], _ :: _, h | _ :: _, [], h => by simp [storesOK] at h
  | _ :: _, _ :: _, h => by
    unfold storesOK at h
    rw [Bool.and_eq_true] at h
    simp [ecs_storesOK_length h.2]

theorem ecs_storesOK_append {tabs : Tables} {sh : Array Ty} {g : Func} {nw : ID → Bool} :
    ∀ {ss : List (Int × Ty)} {A B : List ID}, storesOK tabs sh g nw ss (A ++ B) = true →
      ∃ s1 s2, ss = s1 ++ s2 ∧ storesOK tabs sh g nw s1 A = true ∧ storesOK tabs sh g nw s2 B = true
  | ss, [], B, h => ⟨[], ss, rfl, rfl, h⟩
  | [], _ :: _, B, h => by simp [storesOK] at h
  | s :: ss, z :: A, B, h => by
    rw [List.cons_append] at h
    unfold storesOK at h
    rw [Bool.and_eq_true] at h
    obtain ⟨s1, s2, rfl, h1, h2⟩ := ecs_storesOK_append h.2
    refine ⟨s :: s1, s2, rfl, ?_, h2⟩
    unfold storesOK
    rw [Bool.and_eq_true]
    exact ⟨h.1, h1⟩

/-- The facts of one stack-argument store `z` at slot `(off, lt)`. -/
theorem ecs_storesOK_one {tabs : Tables} {sh : Array Ty} {g : Func} {nw : ID → Bool}
    {s : Int × Ty} {z : ID} (h : storesOK tabs sh g nw [s] [z] = true) :
    ∃ w, g.value? z = some w ∧ eqE (auxTy tabs w.aux) s.2 = true ∧
      spOffOK sh g nw w.args[0]! s.1 = true ∧ shapeOf sh g z = .mem := by
  unfold storesOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, -⟩ := h
  cases hz : g.value? z with
  | none => rw [hz] at h1; cases h1
  | some w =>
    rw [hz] at h1
    dsimp only at h1
    simp only [Bool.and_eq_true] at h1
    obtain ⟨⟨he, hs⟩, hm⟩ := h1
    refine ⟨w, rfl, he, hs, ?_⟩
    split at hm
    · assumption
    · cases hm

theorem ecs_storeChain_new {g : Func} {nw : ID → Bool} :
    ∀ {n : Nat} {z b : ID} {zs : List ID}, storeChain g nw n z b = some zs → zs ≠ [] → nw z = true
  | 0, _, _, _, h, _ => by simp [storeChain] at h
  | n + 1, z, b, zs, h, hne => by
    unfold storeChain at h
    split at h
    · cases h; exact absurd rfl hne
    · split at h
      · split at h
        · next hc => simp only [Bool.and_eq_true] at hc; exact hc.1.1
        · cases h
      · cases h

/-- One step of a chain of stores. -/
theorem ecs_storeChain_step {g : Func} {nw : ID → Bool} {n : Nat} {z b : ID} {zs : List ID}
    (h : storeChain g nw (n + 1) z b = some zs) :
    (z = b ∧ zs = []) ∨ ∃ w zs', z ≠ b ∧ g.value? z = some w ∧ nw z = true ∧ w.op = .Store ∧
      w.args.size = 3 ∧ storeChain g nw n w.args[2]! b = some zs' ∧ zs = zs' ++ [z] := by
  unfold storeChain at h
  split at h
  · next hzb => cases h; exact .inl ⟨beq_iff_eq.1 hzb, rfl⟩
  · next hzb =>
    split at h
    · next w hw =>
      split at h
      · next hc =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        cases hs : storeChain g nw n w.args[2]! b with
        | none => rw [hs] at h; cases h
        | some zs' =>
          rw [hs] at h
          cases h
          exact .inr ⟨w, zs', fun he => hzb (beq_iff_eq.2 he), hw, hc.1.1, hc.1.2, hc.2, hs, rfl⟩
      · cases h
    · cases h

/-- **The chain of stores** writes its slots in order: from the memory `M` of its bottom, its top
holds `writeAll M` of the stores' writes. -/
theorem ecs_chain {env : Env} {tabs : Tables} {f g : Func} {T : Frame} {E L : ID → Prop}
    (hNC : NewCons env (Ctx.make tabs g) (isNewB f) T E)
    (hL : ∀ z, L z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, isNewB f a = true → L a) :
    ∀ (n : Nat) {z b : ID} {zs : List ID}, storeChain g (isNewB f) n z b = some zs →
      (zs ≠ [] → E z ∧ L z) → ∀ {ss : List (Int × Ty)},
      storesOK tabs (typeShapes tabs) g (isNewB f) ss zs = true → (∀ s ∈ ss, atom s.2 = true) →
      (∀ z' ∈ zs, ∀ w qw, g.value? z' = some w → g.value? w.args[0]! = some qw →
        isNewB f qw.args[0]! = false → EcTgtHolds env tabs g T qw.args[0]!) →
      ∀ M, rv T b = .mem M → ∃ M', rv T z = .mem M' ∧
        writeAll M (List.zipWith ecsW ss (zs.map fun z => rv T (storeVal g z))) = some M'
  | 0, _, _, _, h, _, _, _, _, _, _, _ => by simp [storeChain] at h
  | n + 1, z, b, zs, h, hEL, ss, hss, hat, hsp, M, hM => by
    rcases ecs_storeChain_step h with ⟨rfl, rfl⟩ | ⟨w, zs', hzb, hw, hnz, hop, hsz, hc, rfl⟩
    · have : ss = [] := by have := ecs_storesOK_length hss; simpa using this
      subst this
      exact ⟨M, hM, rfl⟩
    obtain ⟨hEz, hLz⟩ := hEL (by simp)
    obtain ⟨s1, s2, rfl, h1, h2⟩ := ecs_storesOK_append hss
    have hl2 := ecs_storesOK_length h2
    obtain ⟨s, rfl⟩ : ∃ s, s2 = [s] := by
      match s2, hl2 with
      | [s], _ => exact ⟨s, rfl⟩
    obtain ⟨w', hw', haux, hoff, hsh⟩ := ecs_storesOK_one h2
    rw [hw] at hw'; cases hw'
    obtain ⟨-, w', y, hw', hcl, hy, hev⟩ := hNC z hEz
    change g.value? z = some w' at hw'
    rw [hw] at hw'; cases hw'
    obtain ⟨hwid, hLcl⟩ := hL z hLz w hw
    have hargs := ecs_args_three hsz
    have hmem : ∀ i, i < 3 → w.args[i]! ∈ w.args := fun i hi => by
      rw [← Array.mem_toList_iff, hargs]
      match i, hi with
      | 0, _ | 1, _ | 2, _ => simp
    have hty : (Ctx.make tabs g).tys[w.id]?.getD .other = .mem := by
      rw [hwid, ← shapeOf_eq]; exact hsh
    obtain ⟨P, M0, M1, hP, hM0, hW, rfl⟩ := ecs_store_val hop hargs hty hev
    -- the stores below
    have hEL' : zs' ≠ [] → E w.args[2]! ∧ L w.args[2]! := fun hne => by
      have hn := ecs_storeChain_new hc hne
      exact ⟨hcl _ (hmem 2 (by decide)) hn, hLcl _ (hmem 2 (by decide)) hn⟩
    obtain ⟨M0', hM0', hW'⟩ := ecs_chain hNC hL n hc hEL' h1
      (fun s hs => hat s (List.mem_append_left _ hs))
      (fun z' hz' => hsp z' (List.mem_append_left _ hz')) M hM
    rw [hM0] at hM0'; cases hM0'
    -- the address
    have hEq : E w.args[0]! ∧ L w.args[0]! := by
      have hn : isNewB f w.args[0]! = true := by
        unfold spOffOK at hoff; simp only [Bool.and_eq_true] at hoff; exact hoff.1.1.1
      exact ⟨hcl _ (hmem 0 (by decide)) hn, hLcl _ (hmem 0 (by decide)) hn⟩
    have ha := ecs_addr hNC hL hoff hEq.1 hEq.2 fun qw hqw => hsp z (by simp) w qw hw hqw
    obtain ⟨a0, ha0, hasl⟩ := ha
    rw [rv_of ha0, hasl] at hP; cases hP
    rw [show (Ctx.make tabs g).tabs = tabs from rfl, ecs_encode_eqE (hat s (by simp)) haux] at hW
    refine ⟨M1, rv_of hy, ?_⟩
    have hlen : s1.length = (zs'.map fun z => rv T (storeVal g z)).length := by
      rw [List.length_map]; exact ecs_storesOK_length h1
    rw [List.map_append, List.zipWith_append hlen]
    refine writeAll_snoc hW' ?_
    have hsv : storeVal g z = w.args[1]! := by unfold storeVal; rw [hw]; rfl
    simp only [List.map_cons, List.map_nil, List.zipWith_cons_cons, List.zipWith_nil_right, ecsW, hsv]
    exact hW

/-- The stores of a chain whose top is a new value of `E` are new values of `E`. -/
theorem ecs_chain_E {env : Env} {tabs : Tables} {f g : Func} {T : Frame} {E L : ID → Prop}
    (hNC : NewCons env (Ctx.make tabs g) (isNewB f) T E)
    (hL : ∀ z, L z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, isNewB f a = true → L a) :
    ∀ (n : Nat) {z b : ID} {zs : List ID}, storeChain g (isNewB f) n z b = some zs →
      (zs ≠ [] → E z ∧ L z) → ∀ z' ∈ zs, E z' ∧ L z'
  | 0, _, _, _, h, _, _, _ => by simp [storeChain] at h
  | n + 1, z, b, zs, h, hEL, z', hz' => by
    rcases ecs_storeChain_step h with ⟨-, rfl⟩ | ⟨w, zs', -, hw, -, -, hsz, hc, rfl⟩
    · exact absurd hz' List.not_mem_nil
    have hz := hEL (by simp)
    rcases List.mem_append.1 hz' with hz' | hz'
    · refine ecs_chain_E hNC hL n hc (fun hne => ?_) z' hz'
      obtain ⟨-, w', -, hw', hcl, -⟩ := hNC z hz.1
      change g.value? z = some w' at hw'
      rw [hw] at hw'; cases hw'
      have hm2 : w.args[2]! ∈ w.args := by rw [← Array.mem_toList_iff, ecs_args_three hsz]; simp
      have hn := ecs_storeChain_new hc hne
      exact ⟨hcl _ hm2 hn, (hL z hz.2 w hw).2 _ hm2 hn⟩
    · rw [List.mem_singleton.1 hz']; exact hz

theorem ecs_storeChain_nil {g : Func} {nw : ID → Bool} :
    ∀ {n : Nat} {z b : ID}, storeChain g nw n z b = some [] → z = b
  | 0, _, _, h => by simp [storeChain] at h
  | n + 1, z, b, h => by
    rcases ecs_storeChain_step h with ⟨h1, -⟩ | ⟨w, zs', -, -, -, -, -, -, h2⟩
    · exact h1
    · simp at h2

/-- The bottom of a chain of stores is a new value of `E` when its top is and it is new. -/
theorem ecs_chain_base_E {env : Env} {tabs : Tables} {f g : Func} {T : Frame} {E L : ID → Prop}
    (hNC : NewCons env (Ctx.make tabs g) (isNewB f) T E)
    (hL : ∀ z, L z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, isNewB f a = true → L a) :
    ∀ (n : Nat) {z b : ID} {zs : List ID}, storeChain g (isNewB f) n z b = some zs →
      E z ∧ L z → isNewB f b = true → E b ∧ L b
  | 0, _, _, _, h, _, _ => by simp [storeChain] at h
  | n + 1, z, b, zs, h, hEL, hb => by
    rcases ecs_storeChain_step h with ⟨rfl, rfl⟩ | ⟨w, zs', -, hw, -, -, hsz, hc, rfl⟩
    · exact hEL
    obtain ⟨-, w', -, hw', hcl, -⟩ := hNC z hEL.1
    change g.value? z = some w' at hw'
    rw [hw] at hw'; cases hw'
    have hm2 : w.args[2]! ∈ w.args := by rw [← Array.mem_toList_iff, ecs_args_three hsz]; simp
    have hn : isNewB f w.args[2]! = true := by
      by_cases hne : zs' = []
      · subst hne; rw [ecs_storeChain_nil hc]; exact hb
      · exact ecs_storeChain_new hc hne
    exact ecs_chain_base_E hNC hL n hc ⟨hcl _ hm2 hn, (hL z hEL.2 w hw).2 _ hm2 hn⟩ hb

/-- A store of a chain heads the chain below it, a prefix of the chain. -/
theorem ecs_chain_mem {g : Func} {nw : ID → Bool} :
    ∀ {n : Nat} {top b : ID} {zs : List ID}, storeChain g nw n top b = some zs → ∀ {z : ID}, z ∈ zs →
      ∃ wz n' zs', g.value? z = some wz ∧ nw z = true ∧ wz.op = .Store ∧ wz.args.size = 3 ∧
        storeChain g nw n' wz.args[2]! b = some zs' ∧ ∃ rest, zs = zs' ++ [z] ++ rest
  | 0, _, _, _, h, _, _ => by simp [storeChain] at h
  | n + 1, top, b, zs, h, z, hz => by
    rcases ecs_storeChain_step h with ⟨-, rfl⟩ | ⟨w, zs', -, hw, hnw, hop, hsz, hc, rfl⟩
    · exact absurd hz List.not_mem_nil
    rcases List.mem_append.1 hz with hz | hz
    · obtain ⟨wz, n', zs'', h1, h2, h3, h4, h5, rest, hr⟩ := ecs_chain_mem hc hz
      exact ⟨wz, n', zs'', h1, h2, h3, h4, h5, rest ++ [top], by rw [hr]; simp⟩
    · rw [List.mem_singleton.1 hz]
      exact ⟨w, n, zs', hw, hnw, hop, hsz, hc, [], by simp⟩

/-- The top of a chain of stores is a memory with the bottom's writable ranges. -/
theorem ecs_chain_attr {env : Env} {tabs : Tables} {f g : Func} {T : Frame} {E L : ID → Prop}
    (hNC : NewCons env (Ctx.make tabs g) (isNewB f) T E)
    (hL : ∀ z, L z → ∀ w, g.value? z = some w → w.id = z ∧ ∀ a ∈ w.args, isNewB f a = true → L a) :
    ∀ (n : Nat) {z b : ID} {zs : List ID}, storeChain g (isNewB f) n z b = some zs →
      (zs ≠ [] → E z ∧ L z) → ∀ {ss : List (Int × Ty)},
      storesOK tabs (typeShapes tabs) g (isNewB f) ss zs = true →
      ∀ M, rv T b = .mem M → ∃ M', rv T z = .mem M' ∧
        ∀ blk, (M'.find? blk).map ecsAttr = (M.find? blk).map ecsAttr
  | 0, _, _, _, h, _, _, _, _, _ => by simp [storeChain] at h
  | n + 1, z, b, zs, h, hEL, ss, hss, M, hM => by
    rcases ecs_storeChain_step h with ⟨rfl, rfl⟩ | ⟨w, zs', hzb, hw, hnz, hop, hsz, hc, rfl⟩
    · exact ⟨M, hM, fun _ => rfl⟩
    obtain ⟨hEz, hLz⟩ := hEL (by simp)
    obtain ⟨s1, s2, rfl, h1, h2⟩ := ecs_storesOK_append hss
    have hl2 := ecs_storesOK_length h2
    obtain ⟨s, rfl⟩ : ∃ s, s2 = [s] := by
      match s2, hl2 with
      | [s], _ => exact ⟨s, rfl⟩
    obtain ⟨w', hw', -, -, hsh⟩ := ecs_storesOK_one h2
    rw [hw] at hw'; cases hw'
    obtain ⟨-, w', y, hw', hcl, hy, hev⟩ := hNC z hEz
    change g.value? z = some w' at hw'
    rw [hw] at hw'; cases hw'
    obtain ⟨hwid, hLcl⟩ := hL z hLz w hw
    have hargs := ecs_args_three hsz
    have hm2 : w.args[2]! ∈ w.args := by rw [← Array.mem_toList_iff, hargs]; simp
    have hty : (Ctx.make tabs g).tys[w.id]?.getD .other = .mem := by
      rw [hwid, ← shapeOf_eq]; exact hsh
    obtain ⟨P, M0, M1, -, hM0, hW, rfl⟩ := ecs_store_val hop hargs hty hev
    have hEL' : zs' ≠ [] → E w.args[2]! ∧ L w.args[2]! := fun hne => by
      have hn := ecs_storeChain_new hc hne
      exact ⟨hcl _ hm2 hn, hLcl _ hm2 hn⟩
    obtain ⟨M0', hM0', hA⟩ := ecs_chain_attr hNC hL n hc hEL' h1 M hM
    rw [hM0] at hM0'; cases hM0'
    exact ⟨M1, rv_of hy, fun blk => (ecs_find_write hW blk).trans (hA blk)⟩

/-! ## Reading the stack arguments back -/

theorem ecs_rl_length : ∀ {as bs : List Val}, Sem.RefinesList as bs → as.length = bs.length
  | _, _, .nil => rfl
  | _, _, .cons _ t => by simp [ecs_rl_length t]

theorem ecs_rl_split : ∀ {A B ys : List Val}, Sem.RefinesList (A ++ B) ys →
    ∃ y1 y2, ys = y1 ++ y2 ∧ Sem.RefinesList A y1 ∧ Sem.RefinesList B y2
  | [], _, ys, h => ⟨[], ys, rfl, .nil, h⟩
  | a :: A, B, _, .cons h t => by
    obtain ⟨y1, y2, rfl, h1, h2⟩ := ecs_rl_split t
    exact ⟨_ :: y1, y2, rfl, .cons h h1, h2⟩

theorem ecs_forall₂_of_zip {α β : Type} {P : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, l.length = l'.length → (∀ a b, (a, b) ∈ l.zip l' → P a b) →
      List.Forall₂ P l l'
  | [], [], _, _ => .nil
  | [], _ :: _, h, _ | _ :: _, [], h, _ => by simp at h
  | a :: l, b :: l', h, hP =>
    .cons (hP a b (by simp)) (ecs_forall₂_of_zip (by simpa using h)
      fun x y hm => hP x y (List.mem_cons_of_mem _ hm))

theorem ecs_mem_zipWith {α β γ : Type} {f : α → β → γ} :
    ∀ {l : List α} {l' : List β} {e : γ}, e ∈ List.zipWith f l l' → ∃ a ∈ l, ∃ b, e = f a b
  | [], _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | a :: l, b :: l', e, h => by
    rw [List.zipWith_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨a, List.mem_cons_self, b, rfl⟩
    · obtain ⟨a', ha', b', rfl⟩ := ecs_mem_zipWith h
      exact ⟨a', List.mem_cons_of_mem _ ha', b', rfl⟩

/-- An atom read from bytes agreeing with the encoding of a refinement of it. -/
theorem ecs_leaf_dec {lt : Ty} {a y : Val} {bs : Array Byte} {o : Nat} (ht : atom lt = true)
    (ha : a.hasTy lt = true) (hr : Sem.Refines a y) (h : Agree bs o (encode lt y) 0 lt.size) :
    Sem.Refines a (decode bs o lt) := by
  rw [decode_agree lt (wf_atom ht) h]
  cases hr with
  | poison => exact .poison _
  | int w x => rw [decode_encode_atom lt _ ht ha]; exact .int w x
  | bool b => rw [decode_encode_atom lt _ ht ha]; exact .bool b
  | ptr p => rw [decode_encode_atom lt _ ht ha]; exact .ptr p
  | mem _ | tuple _ | agg _ | blob _ | empty => cases lt <;> simp_all [atom, Val.hasTy]

theorem ecs_leaves_dec {bs : Array Byte} :
    ∀ {ls : List (Nat × Ty)} {as ys : List Val}, List.Forall₂ (fun a (l : Nat × Ty) => a.hasTy l.2 = true) as ls →
      Sem.RefinesList as ys →
      List.Forall₂ (fun (l : Nat × Ty) y => Agree bs l.1 (encode l.2 y) 0 l.2.size) ls ys →
      (∀ l ∈ ls, atom l.2 = true) →
      Sem.RefinesList as (ls.map fun (o, lt) => decode bs (0 + o) lt)
  | _, _, _, .nil, .nil, .nil, _ => .nil
  | l :: ls, _, _, .cons h1 t1, .cons h2 t2, .cons h3 t3, hat => by
    refine .cons ?_ (ecs_leaves_dec t1 t2 t3 fun x hx => hat x (List.mem_cons_of_mem _ hx))
    show Sem.Refines _ (decode bs (0 + l.1) l.2)
    rw [Nat.zero_add]
    exact ecs_leaf_dec (hat l List.mem_cons_self) h1 h2 h3

/-- **A stack argument read back**: bytes whose leaf ranges hold the encodings of refinements
of the leaf values of `v` decode to a refinement of `v`. -/
theorem ecs_param_dec {t : Ty} {v : Val} {ys : List Val} {bs : Array Byte} (hw : wf t = true)
    (hv : v.hasTy t = true) (hr : Sem.RefinesList (leafVals t v) ys)
    (hag : List.Forall₂ (fun (l : Nat × Ty) y => Agree bs l.1 (encode l.2 y) 0 l.2.size) (leaves t) ys) :
    Sem.Refines v (decode bs 0 t) := by
  rw [← build_decode (b := 0) hw]
  exact (build_leafVals hw hv).trans (build_mono (ecs_leaves_dec (leafVals_hasTy hw) hr hag
    fun l hl => (mem_leaves hw hl).2))

theorem ecs_canWrite_bound {m : Mem} {p : Ptr} {n : Nat} (h : m.canWrite p n = true) (hn : n ≠ 0) :
    p.off.toNat + n < 2 ^ 64 := by
  rw [ecs_canWrite_pos hn] at h
  split at h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.2
  · cases h

/-- The leaf ranges of a parameter's bytes hold what the stores wrote. -/
theorem ecs_param_bytes {M : Mem} {p0 : Nat} {t : Ty} {bs : Array Byte} (hw : wf t = true)
    (hrd : M.read (ecsSlot p0) t.size = some bs) (hb : leaves t ≠ [] → p0 + t.size < 2 ^ 64)
    {ys : List Val} (hlen : (leaves t).length = ys.length)
    (hleaf : ∀ l y, (l, y) ∈ (leaves t).zip ys →
      M.read (ecsSlot (p0 + l.1)) l.2.size = some (encode l.2 y)) :
    List.Forall₂ (fun (l : Nat × Ty) y => Agree bs l.1 (encode l.2 y) 0 l.2.size) (leaves t) ys := by
  refine ecs_forall₂_of_zip hlen fun l y hm => ?_
  have hl := (mem_leaves hw (List.of_mem_zip hm).1).1
  by_cases h0 : l.2.size = 0
  · intro k hk; omega
  have hrd' := ecs_read_sub hl h0 hrd (hb (List.ne_nil_of_mem (List.of_mem_zip hm).1))
  rw [hleaf l y hm] at hrd'
  rw [Option.some.inj hrd']
  intro k hk
  rw [Nat.zero_add, getElem?_extract_add, if_pos hk]

/-- The leaf slots of one parameter and of the rest. -/
theorem ecs_leafSlots_cons (tabs : Tables) (p : ABIParam) (ps : List ABIParam) :
    leafSlots tabs (p :: ps) =
      (leaves (tabs.ty p.type)).map (fun (o, lt) => (p.offset + o, lt)) ++ leafSlots tabs ps := by
  simp [leafSlots]

/-- **The stack parameters read back**: every stack parameter's slot decodes to a refinement of its
argument, when each leaf slot holds the encoding of a refinement of its leaf value. -/
theorem ecs_stack_params {tabs : Tables} {M : Mem} :
    ∀ (sp : List (ABIParam × Val)) (ys : List Val),
      Sem.RefinesList (sp.flatMap fun x => leafVals (tabs.ty x.1.type) x.2) ys →
      (∀ s y, (s, y) ∈ (leafSlots tabs (sp.map Prod.fst)).zip ys →
        M.read (ecsSlot s.1.toNat) s.2.size = some (encode s.2 y)) →
      (∀ s ∈ leafSlots tabs (sp.map Prod.fst), s.1 < 2 ^ 24) →
      (∀ x ∈ sp, wf (tabs.ty x.1.type) = true ∧ x.2.hasTy (tabs.ty x.1.type) = true ∧
        0 ≤ x.1.offset ∧ M.canWrite (ecsSlot x.1.offset.toNat) (tabs.ty x.1.type).size = true) →
      ∀ x ∈ sp, ∃ bs, M.read (ecsSlot x.1.offset.toNat) (tabs.ty x.1.type).size = some bs ∧
        Sem.Refines x.2 (decode bs 0 (tabs.ty x.1.type))
  | [], _, _, _, _, _, x, hx => absurd hx List.not_mem_nil
  | (p, v) :: sp, ys, hr, hrd, hlt, hok, x, hx => by
    rw [List.flatMap_cons] at hr
    obtain ⟨y1, y2, rfl, h1, h2⟩ := ecs_rl_split hr
    obtain ⟨hw, hv, h0, hcw⟩ := hok (p, v) List.mem_cons_self
    dsimp only at hw hv h0 hcw
    have hl1 : (leaves (tabs.ty p.type)).length = y1.length := by
      rw [← ecs_rl_length h1, leafVals_length hw]
    have hz : (leafSlots tabs (((p, v) :: sp).map Prod.fst)).zip (y1 ++ y2) =
        ((leaves (tabs.ty p.type)).map (fun (o, lt) => (p.offset + o, lt))).zip y1 ++
          (leafSlots tabs (sp.map Prod.fst)).zip y2 := by
      rw [List.map_cons, ecs_leafSlots_cons, List.zip_append (by rw [List.length_map]; exact hl1)]
    rw [hz] at hrd
    rcases List.mem_cons.1 hx with rfl | hx
    · obtain ⟨bs, hbs⟩ := ecs_read_of_canWrite hcw
      refine ⟨bs, hbs, ecs_param_dec hw hv h1 (ecs_param_bytes hw hbs (fun hne => ?_) hl1 ?_)⟩
      · obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil _ hne
        have h24 := hlt (p.offset + l.1, l.2) (by
          rw [List.map_cons, ecs_leafSlots_cons]
          exact List.mem_append_left _ (List.mem_map.2 ⟨l, hl, rfl⟩))
        dsimp only at h24
        by_cases hn : (tabs.ty p.type).size = 0
        · omega
        have := ecs_canWrite_bound hcw hn
        simp only [ecsSlot, BitVec.toNat_ofNat] at this
        rw [Nat.mod_eq_of_lt (by omega)] at this
        exact this
      · intro l y hm
        have := hrd (p.offset + l.1, l.2) y (List.mem_append_left _ (by
          rw [List.zip_map_left]
          exact List.mem_map.2 ⟨(l, y), hm, rfl⟩))
        rw [show (p.offset + (l.1 : Int)).toNat = p.offset.toNat + l.1 by omega] at this
        exact this
    · exact ecs_stack_params sp y2 h2 (fun s y hm => hrd s y (List.mem_append_right _ hm))
        (fun s hs => hlt s (by rw [List.map_cons, ecs_leafSlots_cons]; exact List.mem_append_right _ hs))
        (fun x hx => hok x (List.mem_cons_of_mem _ hx)) x hx

/-! ## Disjoint slots -/

theorem ecs_wfFields_pairwise : ∀ {l : List (Nat × Ty)} {n s : Nat}, wfFields l n s = true →
    l.Pairwise fun a b => a.1 + a.2.size ≤ b.1
  | [], _, _, _ => .nil
  | (o, t) :: fs, n, s, h => by
    simp only [wfFields, Bool.and_eq_true, decide_eq_true_eq] at h
    exact .cons (fun b hb => (wfFields_mem h.2 b hb).1) (ecs_wfFields_pairwise h.2)

theorem ecs_slotsSorted_pairwise {tabs : Tables} : ∀ {ps : List ABIParam}, slotsSorted tabs ps = true →
    ps.Pairwise fun p q => p.offset + ((tabs.ty p.type).size : Int) ≤ q.offset
  | [], _ => .nil
  | [_], _ => .cons (fun _ h => absurd h List.not_mem_nil) .nil
  | p :: q :: ps, h => by
    unfold slotsSorted at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := ecs_slotsSorted_pairwise h.2
    refine .cons (fun r hr => ?_) ih
    rcases List.mem_cons.1 hr with rfl | hr
    · exact h.1
    · have := List.rel_of_pairwise_cons ih hr
      omega

theorem ecs_mem_leafSlots {tabs : Tables} {ps : List ABIParam} {s : Int × Ty}
    (h : s ∈ leafSlots tabs ps) :
    ∃ p ∈ ps, ∃ l ∈ leaves (tabs.ty p.type), s = (p.offset + l.1, l.2) := by
  unfold leafSlots at h
  obtain ⟨p, hp, hs⟩ := List.mem_flatMap.1 h
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hs
  exact ⟨p, hp, l, hl, rfl⟩

/-- The leaf slots of disjoint well-formed parameters are in order and disjoint. -/
theorem ecs_leafSlots_pairwise {tabs : Tables} : ∀ {ps : List ABIParam},
    (∀ p ∈ ps, wf (tabs.ty p.type) = true) →
    (ps.Pairwise fun p q => p.offset + ((tabs.ty p.type).size : Int) ≤ q.offset) →
    (leafSlots tabs ps).Pairwise fun a b => a.1 + (a.2.size : Int) ≤ b.1
  | [], _, _ => by simp [leafSlots]
  | p :: ps, hw, hs => by
    rw [ecs_leafSlots_cons, List.pairwise_append]
    have hwp := hw p List.mem_cons_self
    refine ⟨?_, ecs_leafSlots_pairwise (fun q hq => hw q (List.mem_cons_of_mem _ hq))
      (List.Pairwise.of_cons hs), fun a ha b hb => ?_⟩
    · rw [List.pairwise_map]
      refine (ecs_wfFields_pairwise (leaves_wfFields hwp)).imp fun h => ?_
      dsimp only; omega
    · obtain ⟨l, hl, rfl⟩ := List.mem_map.1 ha
      obtain ⟨q, hq, l', -, rfl⟩ := ecs_mem_leafSlots hb
      have h1 := (mem_leaves hwp hl).1
      have h2 := List.rel_of_pairwise_cons hs hq
      dsimp only
      omega

/-- **The stores' writes read back**: in order, disjoint, inside the area's window. -/
theorem ecs_reads : ∀ {ss : List (Int × Ty)} {ys : List Val} {M M' : Mem},
    ss.Pairwise (fun a b => a.1 + (a.2.size : Int) ≤ b.1) → (∀ s ∈ ss, 0 ≤ s.1 ∧ s.1 < 2 ^ 24) →
    writeAll M (List.zipWith ecsW ss ys) = some M' →
    ∀ s y, (s, y) ∈ ss.zip ys → M'.read (ecsSlot s.1.toNat) s.2.size = some (encode s.2 y)
  | [], _, _, _, _, _, _, _, _, hm => by simp at hm
  | _ :: _, [], _, _, _, _, _, _, _, hm => by simp at hm
  | s :: ss, y :: ys, M, M', hp, hb, hw, s', y', hm => by
    rw [List.zipWith_cons_cons] at hw
    rcases List.mem_cons.1 hm with he | hm
    · cases he
      have h := writeAll_read (A := []) (B := List.zipWith ecsW ss ys) hw ?_
      · rw [GoFV.SSA.Sem.encode_size] at h; exact h
      intro e he
      obtain ⟨a, ha, b, rfl⟩ := ecs_mem_zipWith he
      have h1 := List.rel_of_pairwise_cons hp ha
      have hs := hb s List.mem_cons_self
      have ha' := hb a (List.mem_cons_of_mem _ ha)
      refine .inr (.inr (.inr (.inl ?_)))
      simp only [ecsW, ecsSlot, BitVec.toNat_ofNat, GoFV.SSA.Sem.encode_size]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · simp only [writeAll] at hw
      cases hw1 : M.write (ecsW s y).1 (ecsW s y).2 with
      | none => rw [hw1] at hw; cases hw
      | some M1 =>
        rw [hw1] at hw
        exact ecs_reads (List.Pairwise.of_cons hp) (fun a ha => hb a (List.mem_cons_of_mem _ ha))
          hw s' y' hm

theorem ecs_storesOK_bounds {tabs : Tables} {sh : Array Ty} {g : Func} {nw : ID → Bool} :
    ∀ {ss : List (Int × Ty)} {zs : List ID}, storesOK tabs sh g nw ss zs = true →
      ∀ s ∈ ss, 0 ≤ s.1 ∧ s.1 < 2 ^ 24
  | [], _, _, _, hs => absurd hs List.not_mem_nil
  | _ :: _, [], h, _, _ => by simp [storesOK] at h
  | s :: ss, z :: zs, h, s', hs => by
    have h' := h
    unfold storesOK at h'
    rw [Bool.and_eq_true] at h'
    rcases List.mem_cons.1 hs with rfl | hs
    · obtain ⟨w, -, -, hoff, -⟩ := ecs_storesOK_one (s := s') (z := z)
        (by unfold storesOK; rw [Bool.and_eq_true]; exact ⟨h'.1, rfl⟩)
      unfold spOffOK at hoff
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hoff
      exact ⟨hoff.1.1.2, hoff.1.2⟩
    · exact ecs_storesOK_bounds h'.2 s' hs

/-! ## Moves of wide arguments -/

/-- `Move`'s copy (`memRoot`). -/
theorem ecs_move_inv {ctx : Ctx} {u : Value} {argv : List Val} {y : Val} (hu : u.op = .Move)
    (h : memRoot ctx u argv = .ok y) : ∃ a b d s M bs M', argv = [a, b, .mem M] ∧
      a.asPtrWord = some d ∧ b.asPtrWord = some s ∧
      M.read s u.auxInt.toInt.toNat = some bs ∧ M.write d bs = some M' ∧ y = .mem M' := by
  unfold memRoot at h
  rw [hu] at h
  split at h
  all_goals first
    | contradiction
    | (split at h
       · split at h
         · simp only [writeRes] at h
           split at h
           · cases h; exact ⟨_, _, _, _, _, _, _, rfl, ‹_›, ‹_›, ‹_›, ‹_›, rfl⟩
           · cases h
         · cases h
       · cases h)
    | (simp only at h; split at h <;> cases h)

/-- A `Move`'s evaluation: the copy of the bytes at its source to its destination. -/
theorem ecs_move_val {env : Env} {ctx : Ctx} {fr : Frame} {u : Value} {y : Val}
    (hu : u.op = .Move) (hargs : u.args.toList = [u.args[0]!, u.args[1]!, u.args[2]!])
    (hty : ctx.tys[u.id]?.getD .other = .mem) (h : evalValue env ctx fr u = .ok y) :
    ∃ d s M bs M', (rv fr u.args[0]!).asPtrWord = some d ∧ (rv fr u.args[1]!).asPtrWord = some s ∧
      rv fr u.args[2]! = .mem M ∧ M.read s u.auxInt.toInt.toNat = some bs ∧
      M.write d bs = some M' ∧ y = .mem M' := by
  have hreg := regs_of_ok h
  rw [evalValue_of_regs hreg, hty, hargs] at h
  have he : ∀ argv, evalOp env ctx fr u argv .mem = memRoot ctx u argv := fun _ => by
    unfold evalOp; rw [hu]
  simp only [List.map_cons, List.map_nil, he] at h
  cases hr : memRoot ctx u [rv fr u.args[0]!, rv fr u.args[1]!, rv fr u.args[2]!] with
  | ok r =>
    rw [hr] at h
    obtain ⟨a, b, d, s, M, bs, M', hl, hd, hs, hrd, hw, rfl⟩ := ecs_move_inv hu hr
    simp only [List.cons.injEq, and_true] at hl
    obtain ⟨h1, h2, h3⟩ := hl
    cases h
    exact ⟨d, s, M, bs, M', by rw [h1]; exact hd, by rw [h2]; exact hs, h3, hrd, hw, rfl⟩
  | panic e m => rw [hr] at h; cases h
  | stuck msg => rw [hr] at h; cases h

/-- A `Move` of shape `mem` whose read and write succeed evaluates to the copy. -/
theorem ecs_move_eval {env : Env} {ctx : Ctx} {fr : Frame} {u : Value} (hu : u.op = .Move)
    (hreg : ∀ a ∈ u.args, Reg fr a) (hargs : u.args.toList = [u.args[0]!, u.args[1]!, u.args[2]!])
    (hty : ctx.tys[u.id]?.getD .other = .mem) {d s : Ptr} {M M' : Mem} {bs : Array Byte}
    (hd : (rv fr u.args[0]!).asPtrWord = some d) (hs : (rv fr u.args[1]!).asPtrWord = some s)
    (hm : rv fr u.args[2]! = .mem M) (hrd : M.read s u.auxInt.toInt.toNat = some bs)
    (hw : M.write d bs = some M') :
    evalValue env ctx fr u = .ok (.mem M') := by
  rw [evalValue_of_regs hreg, hty, hargs]
  have he : evalOp env ctx fr u [rv fr u.args[0]!, rv fr u.args[1]!, rv fr u.args[2]!] .mem =
      memRoot ctx u [rv fr u.args[0]!, rv fr u.args[1]!, rv fr u.args[2]!] := by
    unfold evalOp; rw [hu]
  simp only [List.map_cons, List.map_nil]
  rw [he, hm]
  unfold memRoot
  rw [hu]
  dsimp only
  rw [hd, hs]
  dsimp only
  rw [hrd]
  dsimp only
  rw [hw]
  rfl

mutual
/-- What a `Load` reads refines what `decode` reads (an all-`poison` aggregate is `poison`). -/
theorem ecs_decodeLoad_le (bs : Array Byte) (off : Nat) :
    (t : Ty) → Sem.Refines (decodeLoad bs off t) (decode bs off t)
  | .agg fs n => by
    simp only [decodeLoad, decode]
    split
    · exact .poison _
    · exact .agg (ecs_decodeLoadFields_le bs off fs)
  | .int w => by simp only [decodeLoad]; exact Sem.Refines.refl _
  | .bool => by simp only [decodeLoad]; exact Sem.Refines.refl _
  | .ptr _ => by simp only [decodeLoad]; exact Sem.Refines.refl _
  | .blob _ => by simp only [decodeLoad]; exact Sem.Refines.refl _
  | .opaque _ => by simp only [decodeLoad]; exact Sem.Refines.refl _
  | .empty => by simp only [decodeLoad, decode]; exact .empty
  | .other => by simp only [decodeLoad]; exact .poison _
  | .mem => by simp only [decodeLoad]; exact .poison _
  | .tuple _ => by simp only [decodeLoad]; exact .poison _
  | .str => by
    simp only [decodeLoad]
    split
    · exact .poison _
    · exact Sem.Refines.refl _
  | .slice _ => by
    simp only [decodeLoad]
    split
    · exact .poison _
    · exact Sem.Refines.refl _
theorem ecs_decodeLoadFields_le (bs : Array Byte) (off : Nat) :
    (fs : List (Nat × Ty)) → Sem.RefinesList (decodeLoadFields bs off fs) (decodeFields bs off fs)
  | [] => by simp only [decodeLoadFields, decodeFields]; exact .nil
  | (o, t) :: fs => by
    simp only [decodeLoadFields, decodeFields]
    exact .cons (ecs_decodeLoad_le bs (off + o) t) (ecs_decodeLoadFields_le bs off fs)
end

theorem ecs_read_size {M : Mem} {p : Ptr} {n : Nat} {bs : Array Byte} (h : M.read p n = some bs) :
    bs.size = n := by
  unfold Mem.read at h
  by_cases hn : n = 0
  · simp only [hn, beq_self_eq_true, ite_true] at h; cases h; simp [hn]
  · simp only [beq_iff_eq, hn, ite_false, Option.bind_eq_bind] at h
    cases ha : M.find? p.blk with
    | none => rw [ha] at h; cases h
    | some a =>
      rw [ha] at h
      simp only [Option.bind_some] at h
      split at h
      · cases h; simp; omega
      · cases h

theorem ecs_movFields_le : {fs : List (Nat × Ty)} → {n s : Nat} → movFields fs n s = true → s ≤ n
  | [], _, _, h => by simpa [movFields] using h
  | (o, t) :: fs, n, s, h => by
    simp only [movFields, Bool.and_eq_true, decide_eq_true_eq] at h
    have := ecs_movFields_le h.2
    omega

mutual
/-- Decoding enough bytes at a `movTy` shape gives a value of that shape. -/
theorem ecs_decode_hasTy_mov : (t : Ty) → (bs : Array Byte) → (o : Nat) → movTy t = true →
    o + t.size ≤ bs.size → (decode bs o t).hasTy t = true
  | .int w, _, _, _, _ => decodeInt_hasTy w _
  | .bool, bs, o, _, _ => by
    simp only [decode]
    split
    · split <;> rfl
    · rfl
  | .ptr e, _, _, _, _ => decodePtr_hasTy e _
  | .agg fs n, bs, o, h, hs => ecs_decodeFields_hasTy_mov fs n 0 bs o h hs
  | .str, _, _, _, _ => Val.ofStr_hasTy_of (decodePtr_isPtrWord _) _
  | .slice e, _, _, _, _ => Val.ofSlice_hasTy_of (decodePtr_isPtrWord _) e _ _
  | .empty, _, _, _, _ | .opaque _, _, _, _, _ => rfl
  | .blob n, bs, o, _, hs => by
    simp only [Ty.size] at hs
    simp only [decode, Val.hasTy, Array.length_toList, Array.size_extract, beq_iff_eq]
    omega
  | .mem, _, _, h, _ | .tuple _, _, _, h, _ | .other, _, _, h, _ => nomatch h
theorem ecs_decodeFields_hasTy_mov : (fs : List (Nat × Ty)) → (n s : Nat) → (bs : Array Byte) →
    (o : Nat) → movFields fs n s = true → o + n ≤ bs.size →
    Val.hasTyList (decodeFields bs o fs) (fs.map (·.2)) = true
  | [], _, _, _, _, _, _ => rfl
  | (fo, ft) :: fs, n, s, bs, o, h, hs => by
    simp only [movFields, Bool.and_eq_true, decide_eq_true_eq] at h
    have hle := ecs_movFields_le h.2
    simp only [decodeFields, List.map_cons, Val.hasTyList, Bool.and_eq_true]
    exact ⟨ecs_decode_hasTy_mov ft bs (o + fo) h.1.2 (by omega),
      ecs_decodeFields_hasTy_mov fs n _ bs o h.2 hs⟩
end

/-- **A wide argument copied by a `Move`**: the source's `Dereference` of `P` (refined by the
target's pointer word `Q`, reading as `s`) at its memory `m` (refined by `M`) is refined by the
bytes the target reads at `s` decoded at the parameter's shape `t`. -/
theorem ecs_move_arg {m M : Mem} (hMR : Mem.Refines m M) {t ta : Ty} (hw : movTy t = true)
    (he : eqE ta t = true) (hmt : moveTy t = true) {P Q : Val} {s : Ptr} (hP : Sem.Refines P Q)
    (hQ : Q.asPtrWord = some s) {bs : Array Byte} (hrd : M.read s t.size = some bs) :
    Sem.Refines ((loadOp ta [P, .mem m]).retype ta) (decode bs 0 t) := by
  have hdt : (decode bs 0 t).retype ta = decode bs 0 t := by
    apply Val.retype_of_hasTy
    rw [eqE_hasTy he]; exact ecs_decode_hasTy_mov t bs 0 hw (by rw [ecs_read_size hrd]; omega)
  have hPw : P = .poison ∨ P.asPtrWord = some s := by
    cases hP with
    | poison => exact .inl rfl
    | _ => first | exact .inr hQ | simp [Val.asPtrWord] at hQ
  rcases hPw with rfl | hPw
  · simp only [loadOp, Val.asPtrWord]
    rw [show Val.retype ta .poison = .poison by cases ta <;> rfl]
    exact .poison _
  · simp only [loadOp, hPw]
    rw [← hdt]
    refine retype_mono ta ((load_mono hMR ta s).trans ?_)
    have hsz := ecT_eqE_size he
    unfold Mem.load
    split
    · have := Ty.eq_of_beq he
      cases t <;> simp_all [erase, moveTy]
    · exact .poison _
    · exact .poison _
    · exact .poison _
    · rw [hsz, hrd]
      dsimp only
      rw [← ecT_eqE_decode he]
      exact ecs_decodeLoad_le bs 0 ta

/-- A `Dereference` without `poison` read its bytes. -/
theorem ecs_deref_read {ta : Ty} (hmt : moveTy ta = true) {P : Val} {m : Mem}
    (h : ((loadOp ta [P, .mem m]).retype ta).hasPoison = false) :
    ∃ p bs, P.asPtrWord = some p ∧ m.read p ta.size = some bs := by
  have hpo : ∀ t : Ty, Val.retype t .poison = .poison := fun t => by cases t <;> rfl
  cases hP : P.asPtrWord with
  | some p =>
    refine ⟨p, ?_⟩
    simp only [loadOp, hP] at h
    cases hr : m.read p ta.size with
    | some bs => exact ⟨bs, rfl, rfl⟩
    | none =>
      exfalso
      unfold Mem.load at h
      split at h
      · simp [moveTy] at hmt
      all_goals first
        | (rw [hpo] at h; cases h)
        | (rw [hr] at h; dsimp only at h; rw [hpo] at h; cases h)
  | none => simp only [loadOp, hP, hpo, Val.hasPoison] at h; cases h

end GoFV.Proof.EC
