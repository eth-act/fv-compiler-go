import GoFV.Proof.Obj.Ex
import GoFV.Proof.Obj.Bitfield

/-!
# `progSym` is the symbolic `progEffect` (`GoFV/Asm/CheckObj.lean`)

For every Prog `progSym` describes (one lemma per opcode family), a successful `progStep`
under a layout with the same frame performs no access in the nil page (`NoNil`), ends in the
state the symbolic effect describes (`HoldsCore`), and its PC (and a call's `X30`) is where the
symbolic control goes (`PcP`).
-/

namespace GoFV.Proof.Obj

open GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj

theorem progSym_sound {az ez : Int} {p : Prog} {σ : Sym} {pc : PCtl} {L : Link} {s s' : MState}
    (h : progSym az ez p = .ok (σ, pc)) (haz : L.autosize = az) (hez : L.extrasize = ez)
    (hskip : p.isSkip = false) (hs : progStep L p s = .ok s') :
    NoNil ⟨s, L.sym⟩ σ ∧ HoldsCore ⟨s, L.sym⟩ σ s' ∧ PcP L p σ s pc s' := by
  sorry

end GoFV.Proof.Obj
