import GoFV.Proof.Gen.Progs3
import GoFV.Gen.Check4

/-!
# The Progs of slice G4 under `runProg` (`docs/plans/proofs3.md` §4)

`progStep` of the Prog shapes slice G4 adds to G3's (`Progs3.lean`, `GoFV.Gen.Check4`), with
symbolic registers `REG_R0 + k` as in `Progs.lean`: the pair load `LDP off(Rn), (Ra, Rb)`
(`progStep_ldp`: `Ra` from the 8 bytes at the address, then `Rb` from the 8 bytes above, both read
before either register is written) and the pair store `STP (Rx, Ry), off(Rn)` (`progStep_stp`: `Rx`
to the address, then `Ry` 8 bytes above), each address outside the nil page.
-/

namespace GoFV.Proof.Gen

open GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64 GoFV.Gen.Check

/-- `LDP off(Rn), (Ra, Rb)`: two 8-byte loads at the address and 8 bytes above. -/
private theorem eff_ldp {c : ProgCtx} {kn ka kb : Nat} {off : Int} (hkn : kn < 32) (hka : ka < 31)
    (hkb : kb < 31) (has : c.p.as = .LDP) (hf : c.p.from_ = memA (REG_R0 + kn) off)
    (hsc : c.p.scond = 0) (ht : c.p.to = pairA (REG_R0 + ka) (REG_R0 + kb)) :
    progEffect c = .ok
      { x := [(kb, c.load (c.s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off + BitVec.ofNat 64 8) 8),
          (ka, c.load (c.s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off) 8)],
        loads := [(c.s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off + BitVec.ofNat 64 8, 8),
          (c.s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off, 8)] } := by
  have hname : As.name .LDP = "LDP" := rfl
  have hma := ctx_mem_reg (c := c) hkn hsc (off := off)
  rw [← hf] at hma
  unfold progEffect
  simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
    ProgOp.movMem, ProgOp.pairOp, ht, pairA, hma, Eff.ld, eff_wX_r0 hka, eff_wX_r0 hkb]
  rfl

/-- `STP (Rx, Ry), off(Rn)`: the 8 bytes of `X kx` at the address, then those of `X ky` 8 bytes
above. -/
private theorem eff_stp {c : ProgCtx} {kn kx ky : Nat} {off : Int} (hkn : kn < 32) (hkx : kx < 32)
    (hky : ky < 32) (has : c.p.as = .STP) (hf : c.p.from_ = pairA (REG_R0 + kx) (REG_R0 + ky))
    (hsc : c.p.scond = 0) (ht : c.p.to = memA (REG_R0 + kn) off) :
    progEffect c = .ok
      { stores := [(c.s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off, 8,
          (c.s.rX (BitVec.ofNat 5 kx)).toNat % 2 ^ (8 * 8)),
        (c.s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off + BitVec.ofNat 64 8, 8,
          (c.s.rX (BitVec.ofNat 5 ky)).toNat % 2 ^ (8 * 8))] } := by
  have hname : As.name .STP = "STP" := rfl
  have hma := ctx_mem_reg (c := c) hkn hsc (off := off)
  rw [← ht] at hma
  unfold progEffect
  simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
    ProgOp.movMem, ProgOp.pairOp, hf, pairA, hma, ctx_x_r0 hkx, ctx_x_r0 hky]
  rfl

variable {L : Link} {p : Prog} {s : MState} {next : BitVec 64}

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
  have he := eff_ldp (c := ⟨L, s, p⟩) hkn hka hkb has hf hsc ht
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
    (by
      have h8 : nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off + 8#64) = false := hnil8
      simp [Eff.nilAccess?, List.find?, hnil, h8])]
  rfl

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
  have he := eff_stp (c := ⟨L, s, p⟩) hkn hkx hky has hf hsc ht
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
    (by
      have h8 : nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off + 8#64) = false := hnil8
      simp [Eff.nilAccess?, List.find?, hnil, h8])]
  rfl

end GoFV.Proof.Gen
