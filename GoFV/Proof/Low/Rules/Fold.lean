import GoFV.Proof.Low.Rules.LoadStore
import GoFV.Proof.Low.AddrFold

/-!
# Lowering rule lemmas: offsets folded into loads (`ARM64.rules:658-676`) and stores (`758-776`),
symbols and frame variables folded into stores (`881-905`), indexed stores (`786-791`, `806-808`)

`(MOV{B,BU,H,HU,W,WU,D}load [off1] {sym} (ADDconst [off2] ptr) mem) && is32Bit(int64(off1)+off2)
&& … => (MOV…load [off1+int32(off2)] {sym} ptr mem)`. The validator admits an instance only
without a symbol and with small non-negative offsets (`Pat.addrOKL`, `offOK`), where the two
addresses are the same (`GoFV.Proof.Low.addr_fold`).

`(MOV{B,H,W,D}store [off1] {sym} (ADDconst [off2] ptr) val mem) && … => (MOV…store
[off1+int32(off2)] {sym} ptr val mem)` and `FMOV{S,D}store`: stores are atoms, the validator
replays the fold as the store's new definition (`LowerCheck.stFold`, the store lowering a `Store`,
its address related by `AddrRef`, `GoFV.Proof.Low.addrRef_fold`), so these rules are
`ArmRule.Mem` (`checked_armStore`). Likewise `(MOV…store [off1] {sym1} (MOVDaddr [off2] {sym2}
ptr) val mem) && canMergeSym(sym1,sym2) && … => (MOV…store [off1+off2] {mergeSym(sym1,sym2)} ptr
val mem)`: the validator replays a global symbol's or a frame variable's address folded into the
store (`LowerCheck.stFoldAddr`; `GoFV.Proof.Low.addrRef_foldSym`, `addrRef_foldFrame`). And
`(MOV…store [off] {sym} (ADD ptr idx) val mem) && off == 0 && sym == nil => (MOV…storeidx ptr idx
val mem)` (and `ADDshiftLL [k]` to the scaled `MOV…storeidx{2,4,8}`): the validator replays the
indexed store as the store's new definition (`LowerCheck.stIdxFold`), whose indexed address is the
`ADD`'s (`GoFV.Proof.Low.Val.ReplayInvL.idxFold`).
-/

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules GoFV.Proof.Low
open GoFV.Rules.Generated.ARM64

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
    simp only [ldVal, symPtr, imm_fold hk1 hk2]
    obtain ⟨b1, -⟩ := offOK_toNat hk1
    obtain ⟨b2, -⟩ := offOK_toNat hk2
    rcases addr_fold hx hT1 b1 b2 with h | h <;> rw [h]
    · rw [Option.elim, retypeL_poison]; exact .poison _
    · exact Sem.Refines.refl _
  | _ => simp only [ldVal, retypeL_poison]; exact .poison _

/-- A global symbol's `MOVDaddr` (the pointer: no window, no address) at a shape: the pointer
at a word shape, `poison` at the others. -/
theorem retypeL_global (g : String) (o : BitVec 64) (T : Ty) :
    (PtrOps.ptrRes ⟨.global g, o⟩).retypeL T = .ptr ⟨.global g, o⟩ ∨
      (PtrOps.ptrRes ⟨.global g, o⟩).retypeL T = .poison := by
  simp only [PtrOps.ptrRes, Ptr.inWindow, Blk.window?, ite_true]
  cases T with
  | int w => cases w <;> simp [Val.retypeL, Val.widen, Val.retype, Ptr.word, Ptr.convertible]
  | _ => simp [Val.retypeL, Val.widen, Val.retype, Ptr.word, Ptr.convertible]

/-- A pointer's word at a shape of at least 64 bits: kept (a word shape) or `poison` (an
aggregate). -/
theorem retypeL_word_wide (p : Ptr) {T : Ty} (hT : 64 ≤ argWidth T) :
    p.word.retypeL T = p.word ∨ p.word.retypeL T = .poison := by
  cases T with
  | int w => cases w <;> simp_all [argWidth, Width.bits, word_retypeL]
  | ptr e => exact .inl (word_retypeL (.inr ⟨e, rfl⟩) p)
  | agg fs n =>
    right
    rcases Ptr.word_cases p with ⟨-, h⟩ | ⟨-, a, -, h⟩ | ⟨-, h⟩ <;> rw [h] <;> rfl
  | _ => simp [argWidth] at hT

/-- `MOVDaddr [k2] {ax} x` (at a shape of at least 64 bits) moved by `k1` as a load address:
undefined, the folded address `[k1+k2] {ax} x` a load reads (`symPtr`), or outside its block's
window, for small non-negative offsets and `x` a register value. A global symbol's `MOVDaddr` is
the symbol at `k2` (no window, no address); a frame variable's the variable's address word,
which moved by `k1` stays in the frame block's window (`addr_word`); without aux,
`addr_movFold`; with any other aux the `MOVDaddr` term is `poison`. -/
theorem symPtr_movFold (tabs : Tables) {T0 T1 : Ty} {k1 k2 : Int64} (hk1 : offOK k1 = true)
    (hk2 : offOK k2 = true) (hT1 : 64 ≤ argWidth T1) {x : Val} (hx : x.hasTy T0 = true)
    (ax : Option AuxRef) :
    symPtr tabs k1 none ((movAddr tabs k2 ax [x]).retypeL T1) = none ∨
      symPtr tabs k1 none ((movAddr tabs k2 ax [x]).retypeL T1) =
        symPtr tabs
          (Int64.ofInt (wrapInt 32 true (wrapInt 32 true k1.toInt + wrapInt 32 true k2.toInt)))
          ax x ∨
      ∃ q, symPtr tabs k1 none ((movAddr tabs k2 ax [x]).retypeL T1) = some q ∧
        q.inWindow = false := by
  obtain ⟨b1, -⟩ := offOK_toNat hk1
  obtain ⟨b2, -⟩ := offOK_toNat hk2
  cases ax with
  | none =>
    simp only [movAddr, symPtr, imm_fold hk1 hk2]
    exact addr_movFold hx hT1 b1 b2
  | some a =>
    simp only [movAddr, symPtr]
    split
    · rename_i hd
      simp only [Option.elim, hd]
      rcases retypeL_global _ _ T1 with hw | hw <;> rw [hw]
      · right; left
        simp only [Arm64.addr, Ptr.add, imm_fold hk1 hk2, BitVec.add_comm]
      · left; rfl
    · rename_i hd
      simp only [Option.elim, hd, imm_fold hk1 hk2]
      simp only [PtrOps.ptrRes,
        frame_inWindow tabs 0 a (k := BitVec.ofInt 64 k2.toInt) (by omega), ite_true]
      rcases retypeL_word_wide ⟨frameBlk tabs 0 a, BitVec.ofInt 64 k2.toInt⟩ hT1 with hw | hw <;>
        rw [hw]
      · right; left
        rw [addr_word (frame_inWindow tabs 0 a (by omega)) (by
          simp only [Ptr.add]
          exact frame_inWindow tabs 0 a (by rw [BitVec.toNat_add]; omega))]
        simp only [Ptr.add, BitVec.add_comm]
      · left; rfl
    · left
      simp only [Option.elim, retypeL_poison]
      rfl

/-- **A symbol's address folded into an integer load** (`ARM64.rules:832-856`): the load at
`k1` (no aux) of `MOVDaddr [k2] {ax} x` is the load at `k1 + k2` with `MOVDaddr`'s aux of `x`,
for small non-negative offsets, the `MOVDaddr` at a shape of at least 64 bits and `x` a register
value (`symPtr_movFold`; a load outside its window is `poison`, `loadN_outWindow`). -/
theorem refines_ld_foldAddr {o : Op} {n : Nat} {s : Bool} (hl : ldOp? o = some (n, s))
    (hg : o.generic = false) (hm : (o == .ARM64MOVDaddr) = false) (tabs : Tables) {T T0 T1 : Ty}
    {k1 k2 : Int64} (hk1 : offOK k1 = true) (hk2 : offOK k2 = true) (hT1 : 64 ≤ argWidth T1)
    {x : Val} (hx : x.hasTy T0 = true) (ax : Option AuxRef) (m : Val) :
    Sem.Refines
      ((opValL tabs o T k1 none [(movAddr tabs k2 ax [x]).retypeL T1, m]).retypeL T)
      ((opValL tabs o T
        (Int64.ofInt (wrapInt 32 true (wrapInt 32 true k1.toInt + wrapInt 32 true k2.toInt))) ax
        [x, m]).retypeL T) := by
  rw [opValL_ld hg hm hl, opValL_ld hg hm hl]
  cases m with
  | mem mm =>
    simp only [ldVal]
    rcases symPtr_movFold tabs hk1 hk2 hT1 hx ax with h | h | ⟨q, h, hq⟩ <;> rw [h]
    · rw [Option.elim, retypeL_poison]; exact .poison _
    · exact Sem.Refines.refl _
    · rw [Option.elim, loadN_outWindow hq, retypeL_poison]; exact .poison _
  | _ => simp only [ldVal, retypeL_poison]; exact .poison _

/-- **An offset folded into a symbol's address** (`ARM64.rules:650`): `ADDconst [k1]` of
`MOVDaddr [k2] {ax} x` is `MOVDaddr [k1+k2] {ax} x`, for an aux, small non-negative offsets and
word shapes. A global symbol's `MOVDaddr` is the symbol at `k2`, which `ADDconst` moves
(`Arm64.addP`, no window); a frame variable's is its address word in activation 0, which
`ADDconst` moves as a pointer or as its concrete address, within the frame block's window
(`Ptr.word_add`); any other aux makes the `MOVDaddr` `poison`. -/
theorem refines_addConst_movAddr (tabs : Tables) {T T1 : Ty} (hT : wordShape T = true)
    (hT1 : wordShape T1 = true) {k1 k2 : Int64}
    (hk1 : offOK k1 = true) (hk2 : offOK k2 = true) {ax : Option AuxRef} (hs : ax.isSome = true)
    (x : Val) :
    Sem.Refines
      ((Arm64.addP T ((movAddr tabs k2 ax [x]).retypeL T1) (BitVec.ofInt 64 k1.toInt)).retypeL T)
      ((movAddr tabs
        (Int64.ofInt (wrapInt 32 true (wrapInt 32 true k1.toInt + wrapInt 32 true k2.toInt))) ax
        [x]).retypeL T) := by
  obtain ⟨a, rfl⟩ := Option.isSome_iff_exists.1 hs
  obtain ⟨b1, -⟩ := offOK_toNat hk1
  obtain ⟨b2, -⟩ := offOK_toNat hk2
  simp only [movAddr, symPtr]
  split
  · simp only [Option.elim]
    rcases retypeL_global _ _ T1 with hw | hw <;> rw [hw]
    · simp only [Arm64.addP, Ptr.add, imm_fold hk1 hk2, BitVec.add_comm]
      exact Sem.Refines.refl _
    · simp only [Arm64.addP, Arm64.reg, retypeL_poison]; exact .poison _
  · simp only [Option.elim, imm_fold hk1 hk2]
    have hw2 := frame_inWindow tabs 0 a (k := BitVec.ofInt 64 k2.toInt) (by omega)
    have hq : (⟨frameBlk tabs 0 a, BitVec.ofInt 64 k1.toInt + BitVec.ofInt 64 k2.toInt⟩ : Ptr) =
        (⟨frameBlk tabs 0 a, BitVec.ofInt 64 k2.toInt⟩ : Ptr).add (BitVec.ofInt 64 k1.toInt) := by
      simp [Ptr.add, BitVec.add_comm]
    have hw12 : ((⟨frameBlk tabs 0 a, BitVec.ofInt 64 k2.toInt⟩ : Ptr).add
        (BitVec.ofInt 64 k1.toInt)).inWindow = true := by
      rw [← hq]; exact frame_inWindow tabs 0 a (by rw [BitVec.toNat_add]; omega)
    rw [hq]
    simp only [PtrOps.ptrRes, hw2, hw12, ite_true, word_retypeL (wordShape_cases hT1)]
    rcases Ptr.word_cases ⟨frameBlk tabs 0 a, BitVec.ofInt 64 k2.toInt⟩ with
      ⟨-, h⟩ | ⟨hc, w, hwa, h⟩ | ⟨h', -⟩
    rotate_right
    · rw [hw2] at h'; cases h'
    · rw [h]
      simp only [Arm64.addP, PtrOps.ptrRes, hw12, ite_true]
      exact Sem.Refines.refl _
    · rw [h, Ptr.word_add hc hwa hw12]
      have hres : Arm64.res T (w + BitVec.ofInt 64 k1.toInt) =
          .int .w64 (w + BitVec.ofInt 64 k1.toInt) := by
        rcases wordShape_cases hT with rfl | ⟨e, rfl⟩ <;> rfl
      simp only [Arm64.addP, Arm64.reg, BitVec.setWidth_eq, hres]
      exact Sem.Refines.refl _
  · simp only [Option.elim, retypeL_poison, Arm64.addP, Arm64.reg]; exact .poison _

set_option hygiene false in
/-- The obligation of a load-folding rule, unfolded and normalized (`arm_unfold`, `arm_norm`). -/
macro "arm_ldfold" : tactic => `(tactic| (
  left
  arm_unfold
  simp only [Pat.addrOKL, Pat.addrOKLs, Bool.and_eq_true, Bool.or_eq_true] at hadr
  arm_norm
  obtain ⟨⟨hA | ⟨⟨hax, hk1⟩, hk2⟩, -⟩, -⟩ := hadr
  · exact absurd hA (by decide)
  rw [show _ = none from beq_iff_eq.1 hax]
  exact refines_ld_fold rfl rfl rfl _ hk1 hk2 (by simpa [armReadW] using harg.1.1) hty.1 _))

set_option hygiene false in
/-- The obligation of a rule folding a symbol's address into a load (`arm_unfold`, `arm_norm`). -/
macro "arm_ldfoldAddr" : tactic => `(tactic| (
  left
  arm_unfold
  simp only [Pat.addrOKL, Pat.addrOKLs, Bool.and_eq_true, Bool.or_eq_true] at hadr
  arm_norm
  obtain ⟨⟨hA | ⟨⟨hax, hk1⟩, hk2⟩, -⟩, -⟩ := hadr
  · exact absurd hA (by decide)
  rw [show e.aux [] = none from beq_iff_eq.1 hax]
  exact refines_ld_foldAddr rfl rfl rfl _ hk1 hk2 (by simpa [armReadW] using harg.1.1) hty.1 _ _))

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

/-- `ARM64.rules:758`: `(MOVBstore [off1] {sym} (ADDconst [off2] ptr) val mem) && is32Bit(int64(off1)+off2) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (MOVBstore [off1+int32(off2)] {sym} ptr val mem)` -/
theorem r_ARM64_758_sound : ArmRule.Checked r_ARM64_758 := checked_armStore rfl rfl

/-- `ARM64.rules:761`: `(MOVHstore [off1] {sym} (ADDconst [off2] ptr) val mem) && is32Bit(int64(off1)+off2) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (MOVHstore [off1+int32(off2)] {sym} ptr val mem)` -/
theorem r_ARM64_761_sound : ArmRule.Checked r_ARM64_761 := checked_armStore rfl rfl

/-- `ARM64.rules:764`: `(MOVWstore [off1] {sym} (ADDconst [off2] ptr) val mem) && is32Bit(int64(off1)+off2) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (MOVWstore [off1+int32(off2)] {sym} ptr val mem)` -/
theorem r_ARM64_764_sound : ArmRule.Checked r_ARM64_764 := checked_armStore rfl rfl

/-- `ARM64.rules:767`: `(MOVDstore [off1] {sym} (ADDconst [off2] ptr) val mem) && is32Bit(int64(off1)+off2) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (MOVDstore [off1+int32(off2)] {sym} ptr val mem)` -/
theorem r_ARM64_767_sound : ArmRule.Checked r_ARM64_767 := checked_armStore rfl rfl

/-- `ARM64.rules:773`: `(FMOVSstore [off1] {sym} (ADDconst [off2] ptr) val mem) && is32Bit(int64(off1)+off2) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (FMOVSstore [off1+int32(off2)] {sym} ptr val mem)` -/
theorem r_ARM64_773_sound : ArmRule.Checked r_ARM64_773 := checked_armStore rfl rfl

/-- `ARM64.rules:776`: `(FMOVDstore [off1] {sym} (ADDconst [off2] ptr) val mem) && is32Bit(int64(off1)+off2) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (FMOVDstore [off1+int32(off2)] {sym} ptr val mem)` -/
theorem r_ARM64_776_sound : ArmRule.Checked r_ARM64_776 := checked_armStore rfl rfl

/-- `ARM64.rules:881`: `(MOVBstore [off1] {sym1} (MOVDaddr [off2] {sym2} ptr) val mem) && canMergeSym(sym1,sym2) && is32Bit(int64(off1)+int64(off2)) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (MOVBstore [off1+off2] {mergeSym(sym1,sym2)} ptr val mem)` -/
theorem r_ARM64_881_sound : ArmRule.Checked r_ARM64_881 := checked_armStore rfl rfl

/-- `ARM64.rules:885`: `(MOVHstore [off1] {sym1} (MOVDaddr [off2] {sym2} ptr) val mem) && canMergeSym(sym1,sym2) && is32Bit(int64(off1)+int64(off2)) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (MOVHstore [off1+off2] {mergeSym(sym1,sym2)} ptr val mem)` -/
theorem r_ARM64_885_sound : ArmRule.Checked r_ARM64_885 := checked_armStore rfl rfl

/-- `ARM64.rules:889`: `(MOVWstore [off1] {sym1} (MOVDaddr [off2] {sym2} ptr) val mem) && canMergeSym(sym1,sym2) && is32Bit(int64(off1)+int64(off2)) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (MOVWstore [off1+off2] {mergeSym(sym1,sym2)} ptr val mem)` -/
theorem r_ARM64_889_sound : ArmRule.Checked r_ARM64_889 := checked_armStore rfl rfl

/-- `ARM64.rules:893`: `(MOVDstore [off1] {sym1} (MOVDaddr [off2] {sym2} ptr) val mem) && canMergeSym(sym1,sym2) && is32Bit(int64(off1)+int64(off2)) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (MOVDstore [off1+off2] {mergeSym(sym1,sym2)} ptr val mem)` -/
theorem r_ARM64_893_sound : ArmRule.Checked r_ARM64_893 := checked_armStore rfl rfl

/-- `ARM64.rules:901`: `(FMOVSstore [off1] {sym1} (MOVDaddr [off2] {sym2} ptr) val mem) && canMergeSym(sym1,sym2) && is32Bit(int64(off1)+int64(off2)) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (FMOVSstore [off1+off2] {mergeSym(sym1,sym2)} ptr val mem)` -/
theorem r_ARM64_901_sound : ArmRule.Checked r_ARM64_901 := checked_armStore rfl rfl

/-- `ARM64.rules:905`: `(FMOVDstore [off1] {sym1} (MOVDaddr [off2] {sym2} ptr) val mem) && canMergeSym(sym1,sym2) && is32Bit(int64(off1)+int64(off2)) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (FMOVDstore [off1+off2] {mergeSym(sym1,sym2)} ptr val mem)` -/
theorem r_ARM64_905_sound : ArmRule.Checked r_ARM64_905 := checked_armStore rfl rfl

/-- `ARM64.rules:786`: `(MOVDstore [off] {sym} (ADD ptr idx) val mem) && off == 0 && sym == nil => (MOVDstoreidx ptr idx val mem)` -/
theorem r_ARM64_786_sound : ArmRule.Checked r_ARM64_786 := checked_armStore rfl rfl

/-- `ARM64.rules:787`: `(MOVWstore [off] {sym} (ADD ptr idx) val mem) && off == 0 && sym == nil => (MOVWstoreidx ptr idx val mem)` -/
theorem r_ARM64_787_sound : ArmRule.Checked r_ARM64_787 := checked_armStore rfl rfl

/-- `ARM64.rules:788`: `(MOVHstore [off] {sym} (ADD ptr idx) val mem) && off == 0 && sym == nil => (MOVHstoreidx ptr idx val mem)` -/
theorem r_ARM64_788_sound : ArmRule.Checked r_ARM64_788 := checked_armStore rfl rfl

/-- `ARM64.rules:789`: `(MOVBstore [off] {sym} (ADD ptr idx) val mem) && off == 0 && sym == nil => (MOVBstoreidx ptr idx val mem)` -/
theorem r_ARM64_789_sound : ArmRule.Checked r_ARM64_789 := checked_armStore rfl rfl

/-- `ARM64.rules:790`: `(FMOVDstore [off] {sym} (ADD ptr idx) val mem) && off == 0 && sym == nil => (FMOVDstoreidx ptr idx val mem)` -/
theorem r_ARM64_790_sound : ArmRule.Checked r_ARM64_790 := checked_armStore rfl rfl

/-- `ARM64.rules:791`: `(FMOVSstore [off] {sym} (ADD ptr idx) val mem) && off == 0 && sym == nil => (FMOVSstoreidx ptr idx val mem)` -/
theorem r_ARM64_791_sound : ArmRule.Checked r_ARM64_791 := checked_armStore rfl rfl

/-- `ARM64.rules:806`: `(MOVDstore [off] {sym} (ADDshiftLL [3] ptr idx) val mem) && off == 0 && sym == nil => (MOVDstoreidx8 ptr idx val mem)` -/
theorem r_ARM64_806_sound : ArmRule.Checked r_ARM64_806 := checked_armStore rfl rfl

/-- `ARM64.rules:807`: `(MOVWstore [off] {sym} (ADDshiftLL [2] ptr idx) val mem) && off == 0 && sym == nil => (MOVWstoreidx4 ptr idx val mem)` -/
theorem r_ARM64_807_sound : ArmRule.Checked r_ARM64_807 := checked_armStore rfl rfl

/-- `ARM64.rules:808`: `(MOVHstore [off] {sym} (ADDshiftLL [1] ptr idx) val mem) && off == 0 && sym == nil => (MOVHstoreidx2 ptr idx val mem)` -/
theorem r_ARM64_808_sound : ArmRule.Checked r_ARM64_808 := checked_armStore rfl rfl

/-- `ARM64.rules:650`: `(ADDconst [off1] (MOVDaddr [off2] {sym} ptr)) && is32Bit(off1+int64(off2)) => (MOVDaddr [int32(off1)+off2] {sym} ptr)` -/
theorem r_ARM64_650_sound : ArmRule.Checked r_ARM64_650 := by
  left
  arm_unfold
  simp only [Pat.addrOKL, Pat.addrOKLs, Bool.and_eq_true, Bool.or_eq_true] at hadr
  arm_norm
  obtain ⟨⟨-, (hB | hB) | ⟨⟨⟨⟨hs, hk1⟩, hk2⟩, hT⟩, hT1⟩⟩, -⟩ := hadr
  · exact absurd hB (by decide)
  · exact absurd hB (by decide)
  exact refines_addConst_movAddr _ hT hT1 hk1 hk2 hs _

/-- `ARM64.rules:832`: `(MOVBload [off1] {sym1} (MOVDaddr [off2] {sym2} ptr) mem) && canMergeSym(sym1,sym2) && is32Bit(int64(off1)+int64(off2)) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (MOVBload [off1+off2] {mergeSym(sym1,sym2)} ptr mem)` -/
theorem r_ARM64_832_sound : ArmRule.Checked r_ARM64_832 := by
  arm_ldfoldAddr

/-- `ARM64.rules:836`: `(MOVBUload [off1] {sym1} (MOVDaddr [off2] {sym2} ptr) mem) && canMergeSym(sym1,sym2) && is32Bit(int64(off1)+int64(off2)) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (MOVBUload [off1+off2] {mergeSym(sym1,sym2)} ptr mem)` -/
theorem r_ARM64_836_sound : ArmRule.Checked r_ARM64_836 := by
  arm_ldfoldAddr

/-- `ARM64.rules:840`: `(MOVHload [off1] {sym1} (MOVDaddr [off2] {sym2} ptr) mem) && canMergeSym(sym1,sym2) && is32Bit(int64(off1)+int64(off2)) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (MOVHload [off1+off2] {mergeSym(sym1,sym2)} ptr mem)` -/
theorem r_ARM64_840_sound : ArmRule.Checked r_ARM64_840 := by
  arm_ldfoldAddr

/-- `ARM64.rules:844`: `(MOVHUload [off1] {sym1} (MOVDaddr [off2] {sym2} ptr) mem) && canMergeSym(sym1,sym2) && is32Bit(int64(off1)+int64(off2)) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (MOVHUload [off1+off2] {mergeSym(sym1,sym2)} ptr mem)` -/
theorem r_ARM64_844_sound : ArmRule.Checked r_ARM64_844 := by
  arm_ldfoldAddr

/-- `ARM64.rules:848`: `(MOVWload [off1] {sym1} (MOVDaddr [off2] {sym2} ptr) mem) && canMergeSym(sym1,sym2) && is32Bit(int64(off1)+int64(off2)) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (MOVWload [off1+off2] {mergeSym(sym1,sym2)} ptr mem)` -/
theorem r_ARM64_848_sound : ArmRule.Checked r_ARM64_848 := by
  arm_ldfoldAddr

/-- `ARM64.rules:852`: `(MOVWUload [off1] {sym1} (MOVDaddr [off2] {sym2} ptr) mem) && canMergeSym(sym1,sym2) && is32Bit(int64(off1)+int64(off2)) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (MOVWUload [off1+off2] {mergeSym(sym1,sym2)} ptr mem)` -/
theorem r_ARM64_852_sound : ArmRule.Checked r_ARM64_852 := by
  arm_ldfoldAddr

/-- `ARM64.rules:856`: `(MOVDload [off1] {sym1} (MOVDaddr [off2] {sym2} ptr) mem) && canMergeSym(sym1,sym2) && is32Bit(int64(off1)+int64(off2)) && (ptr.Op != OpSB || !config.ctxt.Flag_dynlink) => (MOVDload [off1+off2] {mergeSym(sym1,sym2)} ptr mem)` -/
theorem r_ARM64_856_sound : ArmRule.Checked r_ARM64_856 := by
  arm_ldfoldAddr

end GoFV.Proof.Low.Rules
