import GoFV.Proof.Gen.Progs3
import GoFV.Gen.Check4

/-!
# The Progs of slice G4 under `runProg` (`docs/plans/proofs3.md` §4)

`progStep` of the Prog shapes slice G4 adds to G3's (`Progs3.lean`, `GoFV.Gen.Check4`), with
symbolic registers `REG_R0 + k` as in `Progs.lean`: the pair load `LDP off(Rn), (Ra, Rb)`
(`progStep_ldp`: `Ra` from the 8 bytes at the address, then `Rb` from the 8 bytes above, both read
before either register is written) and the pair store `STP (Rx, Ry), off(Rn)` (`progStep_stp`: `Rx`
to the address, then `Ry` 8 bytes above), each address outside the nil page; the same at a frame
operand (`progStep_slotLdp`, `progStep_slotStp`, slice G6).
-/

namespace GoFV.Proof.Gen

open GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64 GoFV.Gen.Check

/-- `LDP` at the address `A` of its operand: two 8-byte loads at `A` and 8 bytes above. -/
private theorem eff_ldp {c : ProgCtx} {ka kb : Nat} {A : BitVec 64} (hka : ka < 31)
    (hkb : kb < 31) (has : c.p.as = .LDP) (hma : c.mem c.p.from_ = .ok (A, none))
    (ht : c.p.to = pairA (REG_R0 + ka) (REG_R0 + kb)) :
    progEffect c = .ok
      { x := [(kb, c.load (A + BitVec.ofNat 64 8) 8), (ka, c.load A 8)],
        loads := [(A + BitVec.ofNat 64 8, 8), (A, 8)] } := by
  have hname : As.name .LDP = "LDP" := rfl
  unfold progEffect
  simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
    ProgOp.movMem, ProgOp.pairOp, ht, pairA, hma, Eff.ld, eff_wX_r0 hka, eff_wX_r0 hkb]
  rfl

/-- `STP (Rx, Ry)` at the address `A` of its operand: the 8 bytes of `X kx` at `A`, then those of
`X ky` 8 bytes above. -/
private theorem eff_stp {c : ProgCtx} {kx ky : Nat} {A : BitVec 64} (hkx : kx < 32)
    (hky : ky < 32) (has : c.p.as = .STP) (hf : c.p.from_ = pairA (REG_R0 + kx) (REG_R0 + ky))
    (hma : c.mem c.p.to = .ok (A, none)) :
    progEffect c = .ok
      { stores := [(A, 8, (c.s.rX (BitVec.ofNat 5 kx)).toNat % 2 ^ (8 * 8)),
        (A + BitVec.ofNat 64 8, 8, (c.s.rX (BitVec.ofNat 5 ky)).toNat % 2 ^ (8 * 8))] } := by
  have hname : As.name .STP = "STP" := rfl
  unfold progEffect
  simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
    ProgOp.movMem, ProgOp.pairOp, hf, pairA, hma, ctx_x_r0 hkx, ctx_x_r0 hky]
  rfl

variable {L : Link} {p : Prog} {s : MState} {next : BitVec 64}

/-- `LDP` at the address `A` of its operand (`Ra`, `Rb` not `ZR`), both addresses outside the nil
page. -/
private theorem step_ldp {ka kb : Nat} {A : BitVec 64} (hka : ka < 31) (hkb : kb < 31)
    (hn : L.nextAddr p.id = some next) (has : p.as = .LDP)
    (hma : (ProgCtx.mk L s p).mem p.from_ = .ok (A, none))
    (ht : p.to = pairA (REG_R0 + ka) (REG_R0 + kb))
    (hnil : nilPage A = false) (hnil8 : nilPage (A + 8) = false) :
    progStep L p s = .ok { (s.wX (BitVec.ofNat 5 ka) ((readMem s.mem A 8).setWidth 64)).wX
        (BitVec.ofNat 5 kb) ((readMem s.mem (A + 8) 8).setWidth 64) with pc := next } := by
  have he := eff_ldp (c := ⟨L, s, p⟩) hka hkb has hma ht
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
    (by
      have h8 : nilPage (A + 8#64) = false := hnil8
      simp [Eff.nilAccess?, List.find?, hnil, h8])]
  rfl

/-- `STP (Rx, Ry)` at the address `A` of its operand, both addresses outside the nil page. -/
private theorem step_stp {kx ky : Nat} {A : BitVec 64} (hkx : kx < 32) (hky : ky < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .STP)
    (hf : p.from_ = pairA (REG_R0 + kx) (REG_R0 + ky))
    (hma : (ProgCtx.mk L s p).mem p.to = .ok (A, none))
    (hnil : nilPage A = false) (hnil8 : nilPage (A + 8) = false) :
    progStep L p s = .ok { s with
      mem := writeMem (writeMem s.mem A 8
          (BitVec.ofNat (8 * 8) ((s.rX (BitVec.ofNat 5 kx)).toNat % 2 ^ (8 * 8))))
        (A + 8) 8 (BitVec.ofNat (8 * 8) ((s.rX (BitVec.ofNat 5 ky)).toNat % 2 ^ (8 * 8))),
      pc := next } := by
  have he := eff_stp (c := ⟨L, s, p⟩) hkx hky has hf hma
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
    (by
      have h8 : nilPage (A + 8#64) = false := hnil8
      simp [Eff.nilAccess?, List.find?, hnil, h8])]
  rfl

/-- `LDP off(Rn), (Ra, Rb)` (`Ra`, `Rb` not `ZR`), both addresses outside the nil page: `Ra` from
the 8 bytes at `X kn + off`, then `Rb` from the 8 bytes above. -/
theorem progStep_ldp {kn ka kb : Nat} {off : Int} (hkn : kn < 32) (hka : ka < 31) (hkb : kb < 31)
    (hn : L.nextAddr p.id = some next) (has : p.as = .LDP)
    (hf : p.from_ = memA (REG_R0 + kn) off) (hsc : p.scond = 0)
    (ht : p.to = pairA (REG_R0 + ka) (REG_R0 + kb))
    (hnil : nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off) = false)
    (hnil8 : nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off + 8) = false) :
    progStep L p s = .ok { (s.wX (BitVec.ofNat 5 ka)
        ((readMem s.mem (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off) 8).setWidth 64)).wX
        (BitVec.ofNat 5 kb)
        ((readMem s.mem (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off + 8) 8).setWidth 64) with
      pc := next } := by
  have hma := ctx_mem_reg (c := ⟨L, s, p⟩) hkn hsc (off := off)
  rw [← hf] at hma
  exact step_ldp hka hkb hn has hma ht hnil hnil8

/-- `STP (Rx, Ry), off(Rn)`, both addresses outside the nil page: the 8 bytes of `X kx` at
`X kn + off`, then those of `X ky` 8 bytes above. -/
theorem progStep_stp {kn kx ky : Nat} {off : Int} (hkn : kn < 32) (hkx : kx < 32) (hky : ky < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .STP)
    (hf : p.from_ = pairA (REG_R0 + kx) (REG_R0 + ky)) (hsc : p.scond = 0)
    (ht : p.to = memA (REG_R0 + kn) off)
    (hnil : nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off) = false)
    (hnil8 : nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off + 8) = false) :
    progStep L p s = .ok { s with
      mem := writeMem (writeMem s.mem (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off) 8
          (BitVec.ofNat (8 * 8) ((s.rX (BitVec.ofNat 5 kx)).toNat % 2 ^ (8 * 8))))
        (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off + 8) 8
          (BitVec.ofNat (8 * 8) ((s.rX (BitVec.ofNat 5 ky)).toNat % 2 ^ (8 * 8))),
      pc := next } := by
  have hma := ctx_mem_reg (c := ⟨L, s, p⟩) hkn hsc (off := off)
  rw [← ht] at hma
  exact step_stp hkx hky hn has hf hma hnil hnil8

/-- `LDP off(RSP), (Ra, Rb)` at a frame operand (`slotA`), both addresses outside the nil page. -/
theorem progStep_slotLdp {ka kb : Nat} {nc : AddrName} {off : Int} (hka : ka < 31) (hkb : kb < 31)
    (hn : L.nextAddr p.id = some next) (has : p.as = .LDP) (hf : slotA p.from_ nc off = true)
    (hnc : nc = .AUTO ∨ nc = .PARAM) (ht : p.to = pairA (REG_R0 + ka) (REG_R0 + kb))
    (hnil : nilPage (s.sp + BitVec.ofInt 64 (frameOff L nc off)) = false)
    (hnil8 : nilPage (s.sp + BitVec.ofInt 64 (frameOff L nc off) + 8) = false) :
    progStep L p s = .ok { (s.wX (BitVec.ofNat 5 ka)
        ((readMem s.mem (s.sp + BitVec.ofInt 64 (frameOff L nc off)) 8).setWidth 64)).wX
        (BitVec.ofNat 5 kb)
        ((readMem s.mem (s.sp + BitVec.ofInt 64 (frameOff L nc off) + 8) 8).setWidth 64) with
      pc := next } :=
  step_ldp hka hkb hn has (ctx_mem_slot hf hnc) ht hnil hnil8

/-- `STP (Rx, Ry), off(RSP)` at a frame operand (`slotA`), both addresses outside the nil page. -/
theorem progStep_slotStp {kx ky : Nat} {nc : AddrName} {off : Int} (hkx : kx < 32) (hky : ky < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .STP)
    (hf : p.from_ = pairA (REG_R0 + kx) (REG_R0 + ky)) (ht : slotA p.to nc off = true)
    (hnc : nc = .AUTO ∨ nc = .PARAM)
    (hnil : nilPage (s.sp + BitVec.ofInt 64 (frameOff L nc off)) = false)
    (hnil8 : nilPage (s.sp + BitVec.ofInt 64 (frameOff L nc off) + 8) = false) :
    progStep L p s = .ok { s with
      mem := writeMem (writeMem s.mem (s.sp + BitVec.ofInt 64 (frameOff L nc off)) 8
          (BitVec.ofNat (8 * 8) ((s.rX (BitVec.ofNat 5 kx)).toNat % 2 ^ (8 * 8))))
        (s.sp + BitVec.ofInt 64 (frameOff L nc off) + 8) 8
          (BitVec.ofNat (8 * 8) ((s.rX (BitVec.ofNat 5 ky)).toNat % 2 ^ (8 * 8))),
      pc := next } :=
  step_stp hkx hky hn has hf (ctx_mem_slot ht hnc) hnil hnil8

end GoFV.Proof.Gen
