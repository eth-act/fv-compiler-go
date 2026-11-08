import GoFV.Proof.Obj.Basic

/-!
# The bitfield moves the assembler encodes shifts, field extracts and extensions as

`progSym` (`GoFV/Asm/CheckObj.lean`) describes a P0 constant shift, `UBFX`/`SBFX`/`UBFIZ` and the
`MOV{B,BU,H,HU,W}` register extensions by the bitfield move (`UBFM`/`SBFM`) the assembler encodes
them as; here each equals what `progEffect` computes (`dp2Op` of a constant amount, `ubfx`,
`sbfx`, `ubfiz`, `sext`, `maskN`), for every operand.
-/

namespace GoFV.Proof.Obj

open GoFV.Arm64 GoFV.Asm GoFV.Arm64.ProgOp
open GoFV.SSA.Sem.Arm64 (sext ubfx sbfx ubfiz)

/-- The datasize in bits. -/
abbrev wOf (sf : Bool) : Nat := if sf then 64 else 32

theorem lsl_bfm (sf : Bool) (k : Nat) (hk : 0 < k ∧ k < wOf sf) (x : BitVec 64) :
    dp2Op sf 8 (trunc sf x) (trunc sf (BitVec.ofNat 64 k)) =
      bitfieldMove sf 2 (BitVec.ofNat 6 ((wOf sf - k) % wOf sf)) (BitVec.ofNat 6 (wOf sf - 1 - k)) 0 x := by
  sorry

theorem lsr_bfm (sf : Bool) (k : Nat) (hk : 0 < k ∧ k < wOf sf) (x : BitVec 64) :
    dp2Op sf 9 (trunc sf x) (trunc sf (BitVec.ofNat 64 k)) =
      bitfieldMove sf 2 (BitVec.ofNat 6 k) (BitVec.ofNat 6 (wOf sf - 1)) 0 x := by
  sorry

theorem asr_bfm (sf : Bool) (k : Nat) (hk : 0 < k ∧ k < wOf sf) (x : BitVec 64) :
    dp2Op sf 10 (trunc sf x) (trunc sf (BitVec.ofNat 64 k)) =
      bitfieldMove sf 0 (BitVec.ofNat 6 k) (BitVec.ofNat 6 (wOf sf - 1)) 0 x := by
  sorry

theorem ubfx_bfm (sf : Bool) (lsb width : Nat) (hw : 0 < width) (hb : lsb + width ≤ wOf sf)
    (x : BitVec 64) :
    trunc sf (ubfx (Int64.ofNat (lsb * 256 + width)) (trunc sf x)) =
      bitfieldMove sf 2 (BitVec.ofNat 6 lsb) (BitVec.ofNat 6 (lsb + width - 1)) 0 x := by
  sorry

theorem sbfx_bfm (sf : Bool) (lsb width : Nat) (hw : 0 < width) (hb : lsb + width ≤ wOf sf)
    (x : BitVec 64) :
    trunc sf (sbfx (Int64.ofNat (lsb * 256 + width)) (trunc sf x)) =
      bitfieldMove sf 0 (BitVec.ofNat 6 lsb) (BitVec.ofNat 6 (lsb + width - 1)) 0 x := by
  sorry

theorem ubfiz_bfm (sf : Bool) (lsb width : Nat) (hw : 0 < width) (hb : lsb + width ≤ wOf sf)
    (x : BitVec 64) :
    trunc sf (ubfiz (Int64.ofNat (lsb * 256 + width)) x) =
      bitfieldMove sf 2 (BitVec.ofNat 6 ((wOf sf - lsb) % wOf sf)) (BitVec.ofNat 6 (width - 1)) 0 x := by
  sorry

/-- `MOVB`/`MOVH`/`MOVW` between registers: `SBFM Xd, Xn, #0, #(8n − 1)`. -/
theorem sext_bfm (n : Nat) (hn : n = 1 ∨ n = 2 ∨ n = 4) (x : BitVec 64) :
    sextTo64 n x = bitfieldMove true 0 0 (BitVec.ofNat 6 (8 * n - 1)) 0 x := by
  sorry

/-- `MOVBU`/`MOVHU` between registers: `UBFM Xd, Xn, #0, #(8n − 1)`. -/
theorem zext_bfm (n : Nat) (hn : n = 1 ∨ n = 2) (x : BitVec 64) :
    maskN n x = bitfieldMove true 2 0 (BitVec.ofNat 6 (8 * n - 1)) 0 x := by
  sorry

/-- `MOVWU` between registers: `ORR Wd, WZR, Wn`. -/
theorem zext32 (x : BitVec 64) : maskN 4 x = trunc false x := by
  sorry

end GoFV.Proof.Obj
