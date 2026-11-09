import GoFV.Proof.Low.DenL
import GoFV.Proof.PtrAddr

variable [GoFV.SSA.Sem.Addrs]

/-!
# Folding an `ADDconst` offset or a symbol's address into an address (issue #385)

`(MOV…load [off1] {sym} (ADDconst [off2] ptr) mem)` and `(MOV…store [off1] {sym} (ADDconst [off2]
ptr) val mem)` become the access at `[off1+int32(off2)]` of `ptr` (`ARM64.rules:658-676`,
`758-776`). The validator admits an instance only without a symbol and with small non-negative
offsets (`offOK`): a symbol's address ignores the base (`Sem.symAddr`), and a register pointer
outside its block's window moved back into it by `off2` is a word whose concrete address `off1`
could carry into another allocation (`Ptr.ofAddr`), where the folded offset stays in the first.
Under the premise the two addresses are the same (`addr_fold`): an integer register adds as an
integer on both sides; a pointer without an integer form (`Val.hasTy`) moved by `off2` is in its
window (else the `ADDconst` is `poison`), and if it then has an integer form, the pointer was
outside its window and `off2` wrapped its offset to below `2^23`, so moving it by `off1` stays in
the window (`Ptr.ofAddr_add_of_inWindow`). For a store the address relation `AddrRef` carries over
(`addrRef_fold`).

`(MOV…store [off1] {sym1} (MOVDaddr [off2] {sym2} ptr) val mem) && canMergeSym(sym1,sym2) && … =>
(MOV…store [off1+off2] {mergeSym(sym1,sym2)} ptr val mem)` (`881-905`): the store then writes at
the symbol's address (`Sem.symAddr`, `addrAt`), ignoring the base: a global symbol's `MOVDaddr` is
that address (`addrRef_foldSym`); a frame variable's is the register of the `LocalAddr` it lowers,
`poison` or the variable's address word (`FrameVals`), which moved by a small offset stays in the
frame block's window (`addr_framePtr`, `addrRef_foldFrame`).
-/

namespace GoFV.Proof.Low

open GoFV.SSA GoFV.SSA.Sem
open GoFV.Opt.LowerTerm (auxIsName)

/-- A pointer a register holds as a pointer has no integer form. -/
theorem ptr_hasTy_conv {p : Ptr} {T : Ty} (h : (Val.ptr p).hasTy T = true) :
    p.convertible = false := by
  cases T with
  | int w =>
    cases w <;> simp only [Val.hasTy, reduceCtorEq] at h
    exact Ptr.not_convertible_of_held h
  | ptr e => exact Ptr.not_convertible_of_held (by simpa [Val.hasTy] using h)
  | _ => simp [Val.hasTy] at h

/-- Two pointers of one block, the first without an integer form, the second with one: the first
is outside the block's window, the second inside. -/
theorem conv_window {p q : Ptr} (hb : q.blk = p.blk) (hp : p.convertible = false)
    (hq : q.convertible = true) :
    ∃ w, p.blk.window? = some w ∧ 2 ^ 24 ≤ w ∧ w ≤ p.off.toNat ∧ q.off.toNat < w := by
  have hqw := Ptr.inWindow_of_convertible hq
  have hpw : p.inWindow = false := by
    cases h : p.inWindow
    · rfl
    · rw [Ptr.convertible_eq_of_blk (p := q) (q := p) hb.symm hqw h, hq] at hp; cases hp
  obtain ⟨bq, oq⟩ := q
  obtain ⟨bp, op⟩ := p
  simp only at hb
  subst hb
  cases bq <;> simp_all [Ptr.inWindow, Blk.window?] <;> omega

/-- An offset at or above a window `w ≥ 2^24` moved by `k2` below `w` (it wrapped) stays below
`w` when moved further by `k1`, for `k1 + k2 < 2^24`. -/
theorem off_fold {o k1 k2 : BitVec 64} {w : Nat} (hw : 2 ^ 24 ≤ w) (hp : w ≤ o.toNat)
    (hq : (o + k2).toNat < w) (h12 : k1.toNat + k2.toNat < 2 ^ 24) :
    (o + k2 + k1).toNat < w := by
  have ho := o.isLt
  simp only [BitVec.toNat_add] at hq ⊢
  omega

/-- `retypeL` at a word shape keeps a pointer's word. -/
theorem word_retypeL {T : Ty} (hT : T = .int .w64 ∨ ∃ e, T = .ptr e) (q : Ptr) :
    q.word.retypeL T = q.word := by
  unfold Val.retypeL
  rcases hT with rfl | ⟨e, rfl⟩
  · rw [Mono.widen_of_hasTy _ _ (Ptr.word_hasTy_i64 q), Ptr.word_retype_i64]
  · rw [Mono.widen_of_hasTy _ _ (Ptr.word_hasTy_ptr q e), Ptr.word_retype_ptr]

/-- **The folded address.** The address of `ADDconst [k2] x` (at a shape of at least 64 bits)
moved by `k1` is undefined or `x` moved by `k1 + k2`, for `k1 + k2 < 2^24` and `x` a register
value. -/
theorem addr_fold_sum {T0 T1 : Ty} {x : Val} (hx : x.hasTy T0 = true) (hT1 : 64 ≤ argWidth T1)
    {k1 k2 : BitVec 64} (h12 : k1.toNat + k2.toNat < 2 ^ 24) :
    Arm64.addr ((Arm64.addP T1 x k2).retypeL T1) k1 = none ∨
      Arm64.addr ((Arm64.addP T1 x k2).retypeL T1) k1 = Arm64.addr x (k1 + k2) := by
  obtain ⟨fs, n, rfl⟩ | hw : (∃ fs n, T1 = .agg fs n) ∨ (T1 = .int .w64 ∨ ∃ e, T1 = .ptr e) := by
    cases T1 with
    | int w => cases w <;> simp_all [argWidth, Width.bits]
    | ptr e => exact .inr (.inr ⟨e, rfl⟩)
    | agg fs n => exact .inl ⟨fs, n, rfl⟩
    | _ => simp [argWidth] at hT1
  · -- an aggregate shape: the `ADDconst` is `poison`
    left
    cases x with
    | ptr p =>
      simp only [Arm64.addP, PtrOps.ptrRes]
      split
      · rcases Ptr.word_cases (p.add k2) with ⟨-, h⟩ | ⟨-, a, -, h⟩ | ⟨-, h⟩ <;> rw [h] <;> rfl
      · rfl
    | _ =>
      simp only [Arm64.addP]
      split <;> rfl
  cases x with
  | ptr p =>
    have hpc := ptr_hasTy_conv hx
    simp only [Arm64.addP, PtrOps.ptrRes]
    split
    · rename_i hwin
      rw [word_retypeL hw]
      right
      rcases Ptr.word_cases (p.add k2) with ⟨-, h⟩ | ⟨hc, a, ha, h⟩ | ⟨h', -⟩
      rotate_right
      · rw [hwin] at h'; cases h'
      · rw [h]
        simp only [Arm64.addr, Option.some.injEq, Ptr.add, Ptr.mk.injEq, true_and]
        rw [BitVec.add_assoc, BitVec.add_comm k2 k1]
      · rw [h]
        simp only [Arm64.addr, Arm64.reg, BitVec.setWidth_eq, Option.map_some, Option.some.injEq]
        obtain ⟨w, hwp, hw24, hpw, hqw⟩ := conv_window (p := p) (q := p.add k2) rfl hpc hc
        have hq : Ptr.ofAddr a = p.add k2 := Ptr.ofAddr_addr hc ha
        have hin : ((Ptr.ofAddr a).add k1).inWindow = true := by
          rw [hq]
          simp only [Ptr.add] at hqw
          simp only [Ptr.inWindow, Ptr.add, hwp]
          exact decide_eq_true (off_fold hw24 hpw hqw h12)
        rw [Ptr.ofAddr_add_of_inWindow hin, hq]
        simp only [Ptr.add, Ptr.mk.injEq, true_and]
        rw [BitVec.add_assoc, BitVec.add_comm k2 k1]
    · left
      rw [retypeL_poison]
      rfl
  | _ =>
    right
    simp only [Arm64.addP]
    rcases hw with rfl | ⟨e, rfl⟩ <;>
    · split
      · rename_i y hy
        simp only [Arm64.res, Arm64.addr, hy, Option.map_some]
        rw [show (Val.int .w64 (y + k2)).retypeL _ = .int .w64 (y + k2) from by
          unfold Val.retypeL; rw [Mono.widen_of_hasTy _ _ (by simp [Val.hasTy])]; rfl]
        simp only [Arm64.reg, BitVec.setWidth_eq, Option.map_some, Option.some.injEq]
        rw [BitVec.add_assoc, BitVec.add_comm k2 k1]
      · rename_i hy
        simp only [Arm64.addr, hy, Option.map_none, Val.retypeL]
        rfl

/-- `addr_fold` for `k1`, `k2` below `2^23`. -/
theorem addr_fold {T0 T1 : Ty} {x : Val} (hx : x.hasTy T0 = true) (hT1 : 64 ≤ argWidth T1)
    {k1 k2 : BitVec 64} (h1 : k1.toNat < 2 ^ 23) (h2 : k2.toNat < 2 ^ 23) :
    Arm64.addr ((Arm64.addP T1 x k2).retypeL T1) k1 = none ∨
      Arm64.addr ((Arm64.addP T1 x k2).retypeL T1) k1 = Arm64.addr x (k1 + k2) :=
  addr_fold_sum hx hT1 (by omega)

/-- **The folded address of a `MOVDaddr` base without aux.** The address of `MOVDaddr [k2] x` (at
a shape of at least 64 bits) moved by `k1` is undefined, `x` moved by `k1 + k2`, or outside its
block's window, for `k1 + k2 < 2^24` and `x` a register value: a pointer base is `ADDconst`'s
case (`addr_fold_sum`); an integer base `r` addresses `Ptr.ofAddr (r + k2)`, whose word is the
integer `r + k2` if it converts back, else the pointer, which moved by `k1` inside its window is
`Ptr.ofAddr (r + k2 + k1)` (`Ptr.ofAddr_add_of_inWindow`). -/
theorem addr_movFold {T0 T1 : Ty} {x : Val} (hx : x.hasTy T0 = true) (hT1 : 64 ≤ argWidth T1)
    {k1 k2 : BitVec 64} (h12 : k1.toNat + k2.toNat < 2 ^ 24) :
    Arm64.addr (((Arm64.addr x k2).elim .poison PtrOps.ptrRes).retypeL T1) k1 = none ∨
      Arm64.addr (((Arm64.addr x k2).elim .poison PtrOps.ptrRes).retypeL T1) k1 =
        Arm64.addr x (k1 + k2) ∨
      ∃ q, Arm64.addr (((Arm64.addr x k2).elim .poison PtrOps.ptrRes).retypeL T1) k1 = some q ∧
        q.inWindow = false := by
  by_cases hp : ∃ p, x = .ptr p
  · obtain ⟨p, rfl⟩ := hp
    have h := addr_fold_sum (x := .ptr p) hx hT1 h12
    simp only [Arm64.addP] at h
    simp only [Arm64.addr, Option.elim]
    rcases h with h | h
    · exact .inl h
    · exact .inr (.inl h)
  have ha : ∀ k, Arm64.addr x k = (Arm64.reg x).map fun r => Ptr.ofAddr (r + k) := by
    intro k
    cases x <;> first | rfl | exact absurd ⟨_, rfl⟩ hp
  rw [ha k2, ha (k1 + k2)]
  obtain ⟨fs, n, rfl⟩ | hw : (∃ fs n, T1 = .agg fs n) ∨ (T1 = .int .w64 ∨ ∃ e, T1 = .ptr e) := by
    cases T1 with
    | int w => cases w <;> simp_all [argWidth, Width.bits]
    | ptr e => exact .inr (.inr ⟨e, rfl⟩)
    | agg fs n => exact .inl ⟨fs, n, rfl⟩
    | _ => simp [argWidth] at hT1
  · left
    cases Arm64.reg x with
    | none => rfl
    | some r =>
      simp only [Option.map_some, Option.elim, PtrOps.ptrRes, Ptr.ofAddr_inWindow, ite_true]
      rcases Ptr.word_cases (Ptr.ofAddr (r + k2)) with ⟨-, h⟩ | ⟨-, a, -, h⟩ | ⟨-, h⟩ <;> rw [h] <;> rfl
  cases Arm64.reg x with
  | none => left; simp only [Option.map_none, Option.elim, retypeL_poison]; rfl
  | some r =>
    simp only [Option.map_some, Option.elim, PtrOps.ptrRes, Ptr.ofAddr_inWindow, ite_true,
      word_retypeL hw]
    rcases Ptr.word_cases (Ptr.ofAddr (r + k2)) with ⟨-, h⟩ | ⟨-, a, ha', h⟩ | ⟨h', -⟩
    rotate_right
    · rw [Ptr.ofAddr_inWindow] at h'; cases h'
    all_goals rw [h]
    · simp only [Arm64.addr]
      by_cases hin : ((Ptr.ofAddr (r + k2)).add k1).inWindow = true
      · right; left
        rw [← Ptr.ofAddr_add_of_inWindow hin, BitVec.add_assoc, BitVec.add_comm k2 k1]
      · right; right
        exact ⟨_, rfl, by simpa using hin⟩
    · rw [Ptr.addr?_ofAddr] at ha'
      obtain rfl := Option.some.inj ha'
      right; left
      simp only [Arm64.addr, Arm64.reg, BitVec.setWidth_eq, Option.map_some]
      rw [BitVec.add_assoc, BitVec.add_comm k2 k1]

/-- A small non-negative offset as a register immediate. -/
theorem offOK_toNat {k : Int64} (h : offOK k = true) :
    (BitVec.ofInt 64 k.toInt).toNat < 2 ^ 23 ∧ 0 ≤ k.toInt ∧ k.toInt < 2 ^ 23 := by
  simp only [offOK, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨?_, h⟩
  rw [BitVec.toNat_ofInt]
  omega

/-- Two small non-negative offsets as register immediates sum below `2^24`. -/
theorem offOK_sum {k1 k2 : Int64} (h1 : offOK k1 = true) (h2 : offOK k2 = true) :
    (BitVec.ofInt 64 k1.toInt).toNat + (BitVec.ofInt 64 k2.toInt).toNat < 2 ^ 24 := by
  have := (offOK_toNat h1).1
  have := (offOK_toNat h2).1
  omega

/-- `opValL` of `ADDconst [k]` on one argument: `Arm64.addP` by the immediate. -/
theorem opValL_addConst (tabs : Tables) (T : Ty) (k : Int64) (ax : Option AuxRef) (z : Val) :
    opValL tabs .ARM64ADDconst T k ax [z] = Arm64.addP T z (BitVec.ofInt 64 k.toInt) := by
  simp only [opValL, show Op.ARM64ADDconst.generic = false by decide,
    show (Op.ARM64ADDconst == .ARM64MOVDaddr) = false by decide,
    show ldOp? .ARM64ADDconst = none by decide, Bool.false_eq_true, ite_false]
  rfl

/-- `opValL` of `MOVDaddr`: `movAddr`. -/
theorem opValL_movDaddr (tabs : Tables) (T : Ty) (k : Int64) (ax : Option AuxRef)
    (args : List Val) : opValL tabs .ARM64MOVDaddr T k ax args = movAddr tabs k ax args := by
  simp only [opValL, show Op.ARM64MOVDaddr.generic = false by decide,
    show (Op.ARM64MOVDaddr == .ARM64MOVDaddr) = true by decide, Bool.false_eq_true, ite_false,
    ite_true]

/-- **A store's address with an `ADDconst` offset folded** (`ARM64.rules:758-776`): if `ADDconst
[k2] z` (at a shape of at least 64 bits, `z` a register value) moved by `k1` is the pointer word of
`x`, then `z` moved by `k = k1 + k2` is, for small non-negative `k1`, `k2`. -/
theorem addrRef_fold {tabs : Tables} {act : Nat} {T0 T1 : Ty} {z x : Val}
    (hz : z.hasTy T0 = true) (hT1 : 64 ≤ argWidth T1)
    {k1 k2 k : Int64} (h1 : offOK k1 = true) (h2 : offOK k2 = true)
    (hk : k.toInt = k1.toInt + k2.toInt)
    (h : AddrRef tabs act none k1 x ((Arm64.addP T1 z (BitVec.ofInt 64 k2.toInt)).retypeL T1)) :
    AddrRef tabs act none k x z := by
  intro p hp
  have hy := h p hp
  unfold addrAt at hy ⊢
  obtain ⟨b1, -⟩ := offOK_toNat h1
  obtain ⟨b2, -⟩ := offOK_toNat h2
  rcases addr_fold hz hT1 b1 b2 with h' | h' <;> rw [h'] at hy
  · cases hy
  · rw [hk, BitVec.ofInt_add]; exact hy

/-- The store address at a frame variable's aux: the variable's block at the offset. -/
theorem addrAt_name {tabs : Tables} {act : Nat} {n : AuxRef} (hn : auxIsName tabs (some n) = true)
    (k : Int64) (y : Val) :
    addrAt tabs act (some n) k y = some ⟨frameBlk tabs act n, BitVec.ofInt 64 k.toInt⟩ := by
  unfold auxIsName at hn
  simp only [Option.bind_some] at hn
  split at hn
  · rename_i hd
    simp only [addrAt, hd]
  · cases hn

/-- A pointer's word moved by an offset that keeps it inside its block's window addresses the
moved pointer (`Ptr.ofAddr_add_of_inWindow`), for a pointer inside its window. -/
theorem addr_word {p : Ptr} {k : BitVec 64} (hp : p.inWindow = true)
    (hw : (p.add k).inWindow = true) : Arm64.addr p.word k = some (p.add k) := by
  rcases Ptr.word_cases p with ⟨-, h⟩ | ⟨hc, a, ha, h⟩ | ⟨h', -⟩
  · rw [h]; rfl
  · rw [h]
    simp only [Arm64.addr, Arm64.reg, BitVec.setWidth_eq, Option.map_some, Option.some.injEq]
    have he : Ptr.ofAddr a = p := Ptr.ofAddr_addr hc ha
    rw [Ptr.ofAddr_add_of_inWindow (by rw [he]; exact hw), he]
  · rw [hp] at h'; cases h'

/-- A frame block's offsets below `2^24` are inside its window. -/
theorem frame_inWindow (tabs : Tables) (act : Nat) (n : AuxRef) {k : BitVec 64}
    (hk : k.toNat < 2 ^ 24) : (⟨frameBlk tabs act n, k⟩ : Ptr).inWindow = true := by
  unfold frameBlk
  split <;> simp [Ptr.inWindow, Blk.window?, hk]

/-- A frame variable's address as a word, moved by an offset inside the frame block's window, is
the variable's address at that offset. -/
theorem addr_framePtr (tabs : Tables) (act : Nat) (n : AuxRef) {k : BitVec 64}
    (hk : k.toNat < 2 ^ 24) :
    Arm64.addr (framePtr tabs act n).word k = some ⟨frameBlk tabs act n, k⟩ := by
  have hq : (framePtr tabs act n).add k = ⟨frameBlk tabs act n, k⟩ := by
    simp [framePtr, Ptr.add]
  rw [addr_word (by simpa [framePtr] using Ptr.inWindow_zero (frameBlk tabs act n))
    (by rw [hq]; exact frame_inWindow tabs act n hk), hq]

/-- **A frame variable's address folded into a store** (`ARM64.rules:881-905`): if the frame
address `y` (`poison` or the variable's address word, `FrameVals`) moved by `k1` is the pointer
word of `x`, then the store at the variable `n` and offset `k = k1` writes at it, on any base. -/
theorem addrRef_foldFrame {tabs : Tables} {act : Nat} {n : AuxRef}
    (hn : auxIsName tabs (some n) = true) {k1 k : Int64} (h1 : offOK k1 = true)
    (hk : k.toInt = k1.toInt) {x y : Val} (hy : y = .poison ∨ y = (framePtr tabs act n).word)
    (h : AddrRef tabs act none k1 x y) (z : Val) : AddrRef tabs act (some n) k x z := by
  intro p hp
  have hy' := h p hp
  rw [addrAt_name hn, hk]
  unfold addrAt at hy'
  rcases hy with rfl | rfl
  · simp [Arm64.addr, Arm64.reg] at hy'
  · obtain ⟨b1, -⟩ := offOK_toNat h1
    rw [addr_framePtr tabs act n (by omega)] at hy'
    exact hy'

/-- A word shape is the 64-bit integer shape or a pointer shape. -/
theorem wordShape_cases {T : Ty} (hT : wordShape T = true) : T = .int .w64 ∨ ∃ e, T = .ptr e := by
  cases T with
  | int w => cases w <;> simp_all [wordShape]
  | ptr e => exact .inr ⟨e, rfl⟩
  | _ => simp [wordShape] at hT

/-- A read outside its block's window reads nothing. -/
theorem read_outWindow {q : Ptr} (hq : q.inWindow = false) (m : Mem) {k : Nat} (hk : 0 < k) :
    m.read q k = none := by
  unfold Mem.read
  have hk0 : (k == 0) = false := by simp; omega
  simp only [hk0, Bool.false_eq_true, ite_false]
  cases hf : m.find? q.blk with
  | none => rfl
  | some a =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    split
    · rename_i hc
      obtain ⟨-, -, he⟩ := hc
      simp only [Ptr.inWindow] at hq
      simp only [Blk.endsInWindow] at he
      split at hq <;> simp_all <;> omega
    · rfl

/-- A load outside its block's window reads `poison`. -/
theorem loadN_outWindow {q : Ptr} (hq : q.inWindow = false) (ty : Ty) (n : Nat) (s : Bool)
    (m : Mem) : Arm64.loadN ty n s m q = .poison := by
  have hs : ∀ w : Width, 0 < (Ty.int w).size := by intro w; cases w <;> decide
  unfold Arm64.loadN
  split
  · simp only [Mem.load, read_outWindow hq m (hs .w64)]
  · split
    · simp only [Mem.load, read_outWindow hq m (hs _)]
    · rfl

/-- A 128-bit load outside its block's window reads `poison`. -/
theorem load16_outWindow {q : Ptr} (hq : q.inWindow = false) (m : Mem) :
    Arm64.load16 m q = .poison := by
  simp only [Arm64.load16, read_outWindow hq m (by decide : 0 < 16)]

/-- **A global symbol's or frame variable's address term folded into a store**
(`ARM64.rules:881-905`): if `MOVDaddr [k2] {n} b` (at a word shape; a frame variable's in
activation 0, `movAddr`) moved by `k1` is the pointer word of `x`, then the store at the aux `n`
and offset `k = k1 + k2` writes at it, on any base, for small non-negative `k1` and `k`. -/
theorem addrRef_foldSym {tabs : Tables} {n : AuxRef} {T : Ty}
    (hT : wordShape T = true) {k1 k2 k : Int64} (h1 : offOK k1 = true) (hk0 : offOK k = true)
    (hk : k.toInt = k1.toInt + k2.toInt)
    {x b : Val} (h : AddrRef tabs 0 none k1 x ((movAddr tabs k2 (some n) [b]).retypeL T))
    (z : Val) : AddrRef tabs 0 (some n) k x z := by
  have hw := wordShape_cases hT
  intro p hp
  have hy := h p hp
  simp only [addrAt, movAddr, symPtr] at hy ⊢
  split at hy
  · rename_i hd
    simp only [hd]
    simp only [Option.elim_some, PtrOps.ptrRes, Ptr.inWindow, Blk.window?, ite_true,
      word_retypeL hw] at hy
    simp only [Ptr.word, Ptr.convertible, Ptr.addr?, Blk.base?_global, Option.map_none,
      Ptr.inWindow, Blk.window?, ite_true, Arm64.addr, Ptr.add, Option.some.injEq] at hy
    rw [← hy, hk, BitVec.ofInt_add, BitVec.add_comm]
  · rename_i hd
    simp only [hd]
    simp only [Option.elim_some, PtrOps.ptrRes] at hy
    obtain ⟨-, a1, b1⟩ := offOK_toNat h1
    obtain ⟨-, a0, b0⟩ := offOK_toNat hk0
    split at hy
    · rename_i hwin
      rw [word_retypeL hw] at hy
      have hk2 : 0 ≤ k2.toInt := by
        refine Classical.byContradiction fun hneg => ?_
        have : (BitVec.ofInt 64 k2.toInt).toNat ≥ 2 ^ 63 := by
          rw [BitVec.toNat_ofInt]; omega
        unfold frameBlk at hwin
        split at hwin <;> simp only [Ptr.inWindow, Blk.window?, decide_eq_true_eq] at hwin <;> omega
      have hsum : (BitVec.ofInt 64 k2.toInt + BitVec.ofInt 64 k1.toInt).toNat < 2 ^ 24 := by
        rw [← BitVec.ofInt_add, BitVec.toNat_ofInt]; omega
      rw [addr_word hwin (by simp only [Ptr.add]; exact frame_inWindow tabs 0 _ hsum)] at hy
      simp only [Ptr.add, Option.some.injEq] at hy
      rw [← hy, hk, BitVec.ofInt_add, BitVec.add_comm]
    · simp only [retypeL_poison, Arm64.addr, Arm64.reg] at hy
      cases hy
  · simp only [Option.elim_none, retypeL_poison, Arm64.addr, Arm64.reg] at hy
    cases hy

/-- A `MOVDaddr` is a term unless it is a frame variable's address at offset 0. -/
theorem termVL_movDaddr {tabs : Tables} {m : Value} (h : m.op = .ARM64MOVDaddr) :
    termVL tabs m = !(auxIsName tabs m.aux && m.auxInt == 0) := by
  unfold termVL; rw [h]; rfl

/-- A `MOVDaddr` atom is a frame variable's address at offset 0. -/
theorem movDaddr_atom {tabs : Tables} {m : Value} (h : m.op = .ARM64MOVDaddr)
    (ht : termVL tabs m = false) : auxIsName tabs m.aux = true ∧ m.auxInt = 0 := by
  rw [termVL_movDaddr h] at ht
  simpa using ht

end GoFV.Proof.Low
