import GoFV.Proof.Low.Rules.LoadStore
import GoFV.Proof.Low.AddrFold

/-!
# Lowering rule lemmas: offsets folded into loads (`ARM64.rules:658-676`) and stores (`758-776`),
symbols and frame variables folded into stores (`881-905`)

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
store (`LowerCheck.stFoldAddr`; `GoFV.Proof.Low.addrRef_foldSym`, `addrRef_foldFrame`).
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

end GoFV.Proof.Low.Rules
