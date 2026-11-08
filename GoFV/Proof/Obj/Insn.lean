import GoFV.Proof.Obj.Ex

/-!
# `symInsn` is the symbolic `exec` (`GoFV/Asm/CheckObjSym.lean`)

One lemma per encoding class `symInsn` models: from a state `t` that the symbolic effect `σ`
describes (`Holds`) at offset `o` of code placed at `base`, `exec` succeeds (no access in the
nil page, given `NoNil` of the resulting effect) and its state is described by the resulting
effect, with the PC where the control goes (`CtlPc`). `symInsn_sound` collects them.
-/

namespace GoFV.Proof.Obj

open GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj

theorem symInsn_sound {i : Insn} {o : Nat} {σ σ' : Sym} {mc : MCtl} {c : Ctx} {t : MState}
    {base : BitVec 64} (h : symInsn i o σ = .ok (σ', mc)) (hH : Holds c σ t)
    (hpc : t.pc = base + BitVec.ofNat 64 o) (hnil : NoNil c σ') :
    ∃ t', exec i t = .ok t' ∧ Holds c σ' t' ∧ CtlPc c base o mc t' := by
  sorry

end GoFV.Proof.Obj
