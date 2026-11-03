import GoFV.Proof.Low.Rules.LoadStore
import GoFV.Proof.PtrAddr

/-!
# Lowering rule lemmas: offsets folded into loads (`ARM64.rules:658-676`)

`(MOV{B,BU,H,HU,W,WU,D}load [off1] {sym} (ADDconst [off2] ptr) mem) && is32Bit(int64(off1)+off2)
&& … => (MOV…load [off1+int32(off2)] {sym} ptr mem)`. The validator admits an instance only
without a symbol and with small non-negative offsets (`Pat.addrOKL`, `offOK`): a symbol's address
ignores the base (`Sem.symAddr`), and a register pointer outside its block's window moved back into
it by `off2` is a word whose concrete address `off1` could carry into another allocation
(`Ptr.ofAddr`), where the folded offset stays in the first. Under the premise the two addresses
are the same (`addr_fold`): an integer register adds as an integer on both sides; a pointer
without an integer form (`Val.hasTy`) moved by `off2` is in its window (else the `ADDconst` is
`poison`), and if it then has an integer form, the pointer was outside its window and `off2`
wrapped its offset to below `2^23`, so moving it by `off1` stays in the window
(`Ptr.ofAddr_add_of_inWindow`).
-/

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules GoFV.Proof.Low
open GoFV.Rules.Generated.ARM64

/-- A pointer a register holds as a pointer has no integer form. -/
theorem ptr_hasTy_conv {p : Ptr} {T : Ty} (h : (Val.ptr p).hasTy T = true) :
    p.convertible = false := by
  cases T with
  | int w => cases w <;> simp_all [Val.hasTy]
  | ptr e => simpa [Val.hasTy] using h
  | _ => simp [Val.hasTy] at h

/-- Two pointers of one block, the first without an integer form, the second with one: the first
is outside the block's window, the second inside. -/
theorem conv_window {p q : Ptr} (hb : q.blk = p.blk) (hp : p.convertible = false)
    (hq : q.convertible = true) :
    ∃ w, p.blk.window? = some w ∧ 2 ^ 24 ≤ w ∧ w ≤ p.off.toNat ∧ q.off.toNat < w := by
  obtain ⟨bq, oq⟩ := q
  obtain ⟨bp, op⟩ := p
  simp only at hb
  subst hb
  cases bq <;> simp_all [Ptr.convertible, Blk.window?] <;> omega

/-- An offset at or above a window `w ≥ 2^24` moved by `k2 < 2^23` below `w` (it wrapped) stays
below `w` when moved further by `k1 < 2^23`. -/
theorem off_fold {o k1 k2 : BitVec 64} {w : Nat} (hw : 2 ^ 24 ≤ w) (hp : w ≤ o.toNat)
    (hq : (o + k2).toNat < w) (h1 : k1.toNat < 2 ^ 23) (h2 : k2.toNat < 2 ^ 23) :
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
moved by `k1` is undefined or `x` moved by `k1 + k2`, for `k1`, `k2` below `2^23` and `x` a
register value. -/
theorem addr_fold {T0 T1 : Ty} {x : Val} (hx : x.hasTy T0 = true) (hT1 : 64 ≤ argWidth T1)
    {k1 k2 : BitVec 64} (h1 : k1.toNat < 2 ^ 23) (h2 : k2.toNat < 2 ^ 23) :
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
      · rcases Ptr.word_cases (p.add k2) with ⟨-, h⟩ | ⟨-, a, -, h⟩ <;> rw [h] <;> rfl
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
      rcases Ptr.word_cases (p.add k2) with ⟨-, h⟩ | ⟨hc, a, ha, h⟩
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
          exact decide_eq_true (off_fold hw24 hpw hqw h1 h2)
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

/-- A small non-negative offset as a register immediate. -/
theorem offOK_toNat {k : Int64} (h : offOK k = true) :
    (BitVec.ofInt 64 k.toInt).toNat < 2 ^ 23 ∧ 0 ≤ k.toInt ∧ k.toInt < 2 ^ 23 := by
  simp only [offOK, Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨?_, h⟩
  rw [BitVec.toNat_ofInt]
  omega

/-- The folded auxint `off1+int32(off2)` of two small non-negative offsets, as an immediate: the
sum of theirs. -/
theorem imm_fold {k1 k2 : Int64} (h1 : offOK k1 = true) (h2 : offOK k2 = true) :
    BitVec.ofInt 64
        (Int64.ofInt (wrapInt 32 true (wrapInt 32 true k1.toInt + wrapInt 32 true k2.toInt))).toInt =
      BitVec.ofInt 64 k1.toInt + BitVec.ofInt 64 k2.toInt := by
  obtain ⟨-, a1, b1⟩ := offOK_toNat h1
  obtain ⟨-, a2, b2⟩ := offOK_toNat h2
  have w1 : wrapInt 32 true k1.toInt = k1.toInt := by rw [wrapInt32_omega]; omega
  have w2 : wrapInt 32 true k2.toInt = k2.toInt := by rw [wrapInt32_omega]; omega
  have w3 : wrapInt 32 true (k1.toInt + k2.toInt) = k1.toInt + k2.toInt := by
    rw [wrapInt32_omega]; omega
  rw [w1, w2, w3, ofInt_int64_ofInt (by decide), BitVec.ofInt_add]

/-- **An offset folded into an integer load** (module doc), without a symbol, at small
non-negative offsets, the `ADDconst` at a shape of at least 64 bits and its argument a register
value. -/
theorem refines_ld_fold {o : Op} {n : Nat} {s : Bool} (hl : ldOp? o = some (n, s))
    (hg : o.generic = false) (hm : (o == .ARM64MOVDaddr) = false) (tabs : Tables) {T T0 T1 : Ty}
    {k1 k2 : Int64} (hk1 : offOK k1 = true) (hk2 : offOK k2 = true) (hT1 : 64 ≤ argWidth T1)
    {x : Val} (hx : x.hasTy T0 = true) (m : Val) :
    Sem.Refines
      ((opValL tabs o T k1 none
        [(Arm64.addP T1 x (BitVec.ofInt 64 k2.toInt)).retypeL T1, m]).retypeL T)
      ((opValL tabs o T
        (Int64.ofInt (wrapInt 32 true (wrapInt 32 true k1.toInt + wrapInt 32 true k2.toInt))) none
        [x, m]).retypeL T) := by
  rw [opValL_ld hg hm hl, opValL_ld hg hm hl]
  cases m with
  | mem mm =>
    simp only [ldVal, movPtr, imm_fold hk1 hk2]
    obtain ⟨b1, -⟩ := offOK_toNat hk1
    obtain ⟨b2, -⟩ := offOK_toNat hk2
    rcases addr_fold hx hT1 b1 b2 with h | h <;> rw [h]
    · rw [Option.elim, retypeL_poison]; exact .poison _
    · exact Sem.Refines.refl _
  | _ => simp only [ldVal, retypeL_poison]; exact .poison _

set_option hygiene false in
/-- The obligation of a load-folding rule, unfolded and normalized (`arm_unfold`, `arm_norm`). -/
macro "arm_ldfold" : tactic => `(tactic| (
  left
  arm_unfold
  simp only [Pat.addrOKL, Pat.addrOKLs, Bool.and_eq_true, Bool.or_eq_true] at hadr
  arm_norm
  obtain ⟨hA | ⟨⟨hax, hk1⟩, hk2⟩, -⟩ := hadr
  · exact absurd hA (by decide)
  rw [show _ = none from beq_iff_eq.1 hax]
  exact refines_ld_fold rfl rfl rfl _ hk1 hk2 (by simpa [armReadW] using harg.1.1) hty.1 _))

/-- `ARM64.rules:658`: `(MOVBload [off1] {sym} (ADDconst [off2] ptr) mem) && is32Bit(int64(off1)+off2) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (MOVBload [off1+int32(off2)] {sym} ptr mem)` -/
theorem r_ARM64_658_sound : ArmRule.Checked r_ARM64_658 := by
  arm_ldfold

/-- `ARM64.rules:661`: `(MOVBUload [off1] {sym} (ADDconst [off2] ptr) mem) && is32Bit(int64(off1)+off2) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (MOVBUload [off1+int32(off2)] {sym} ptr mem)` -/
theorem r_ARM64_661_sound : ArmRule.Checked r_ARM64_661 := by
  arm_ldfold

/-- `ARM64.rules:664`: `(MOVHload [off1] {sym} (ADDconst [off2] ptr) mem) && is32Bit(int64(off1)+off2) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (MOVHload [off1+int32(off2)] {sym} ptr mem)` -/
theorem r_ARM64_664_sound : ArmRule.Checked r_ARM64_664 := by
  arm_ldfold

/-- `ARM64.rules:667`: `(MOVHUload [off1] {sym} (ADDconst [off2] ptr) mem) && is32Bit(int64(off1)+off2) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (MOVHUload [off1+int32(off2)] {sym} ptr mem)` -/
theorem r_ARM64_667_sound : ArmRule.Checked r_ARM64_667 := by
  arm_ldfold

/-- `ARM64.rules:670`: `(MOVWload [off1] {sym} (ADDconst [off2] ptr) mem) && is32Bit(int64(off1)+off2) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (MOVWload [off1+int32(off2)] {sym} ptr mem)` -/
theorem r_ARM64_670_sound : ArmRule.Checked r_ARM64_670 := by
  arm_ldfold

/-- `ARM64.rules:673`: `(MOVWUload [off1] {sym} (ADDconst [off2] ptr) mem) && is32Bit(int64(off1)+off2) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (MOVWUload [off1+int32(off2)] {sym} ptr mem)` -/
theorem r_ARM64_673_sound : ArmRule.Checked r_ARM64_673 := by
  arm_ldfold

/-- `ARM64.rules:676`: `(MOVDload [off1] {sym} (ADDconst [off2] ptr) mem) && is32Bit(int64(off1)+off2) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (MOVDload [off1+int32(off2)] {sym} ptr mem)` -/
theorem r_ARM64_676_sound : ArmRule.Checked r_ARM64_676 := by
  arm_ldfold

end GoFV.Proof.Low.Rules
