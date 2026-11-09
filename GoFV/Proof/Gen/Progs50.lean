import GoFV.Proof.Gen.Progs4
import GoFV.Proof.Gen.FMove

variable [GoFV.SSA.Sem.Addrs]

/-!
# The Progs of slice G50 under `runProg` (`docs/plans/proofs3.md` §4)

`progStep` of the pair loads slice G50 adds (`GoFV/Gen/Check50.lean`), as `Progs4.lean` does for
`LDP`, with symbolic registers `REG_R0 + k` (`X k`) and `REG_F0 + k` (`V k`):

* `LDPW off(Rn), (Ra, Rb)` and `LDPSW` (`progStep_ldpw`): `Ra` from the 4 bytes at `X kn + off`,
  `Rb` from the 4 bytes above, zero-extended (`LDPW`) or sign-extended (`LDPSW`, `sextTo64 4`);
* `FLDPD off(Rn), (Fa, Fb)` and `FLDPS` (`progStep_fldp`): `V ka` from the `n` bytes at the
  address, `V kb` from the `n` bytes above (`n = 8`, `4`), zero-extended to 128 bits.

Both registers are read before either is written, and both addresses are outside the nil page.
-/

namespace GoFV.Proof.Gen

open GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64 GoFV.Gen.Check

/-- `LDPW`/`LDPSW` at the address `A` of its operand: two 4-byte loads at `A` and 4 bytes above,
sign-extended if `sg`. -/
private theorem eff_ldpw {c : ProgCtx} {ka kb : Nat} {A : BitVec 64} {sg : Bool} (hka : ka < 31)
    (hkb : kb < 31) (has : c.p.as = .LDPW ∧ sg = false ∨ c.p.as = .LDPSW ∧ sg = true)
    (hma : c.mem c.p.from_ = .ok (A, none))
    (ht : c.p.to = pairA (REG_R0 + ka) (REG_R0 + kb)) :
    progEffect c = .ok
      { x := [(kb, if sg then ProgOp.sextTo64 4 (c.load (A + BitVec.ofNat 64 4) 4)
                else c.load (A + BitVec.ofNat 64 4) 4),
              (ka, if sg then ProgOp.sextTo64 4 (c.load A 4) else c.load A 4)],
        loads := [(A + BitVec.ofNat 64 4, 4), (A, 4)] } := by
  rcases has with ⟨has, rfl⟩ | ⟨has, rfl⟩
  · have hname : As.name .LDPW = "LDPW" := rfl
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
      ProgOp.movMem, ProgOp.pairOp, ht, pairA, hma, Eff.ld, eff_wX_r0 hka, eff_wX_r0 hkb]
    rfl
  · have hname : As.name .LDPSW = "LDPSW" := rfl
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
      ProgOp.movMem, ProgOp.pairOp, ht, pairA, hma, Eff.ld, eff_wX_r0 hka, eff_wX_r0 hkb]
    rfl

/-- `FLDPD`/`FLDPS` at the address `A` of its operand: two `n`-byte loads at `A` and `n` bytes
above, into V registers. -/
private theorem eff_fldp {c : ProgCtx} {ka kb n : Nat} {A : BitVec 64} (hka : ka < 32)
    (hkb : kb < 32) (has : c.p.as = .FLDPD ∧ n = 8 ∨ c.p.as = .FLDPS ∧ n = 4)
    (hma : c.mem c.p.from_ = .ok (A, none))
    (ht : c.p.to = pairA (REG_F0 + ka) (REG_F0 + kb)) :
    progEffect c = .ok
      { v := [(kb, (readMem c.s.mem (A + BitVec.ofNat 64 n) n).setWidth 128),
              (ka, (readMem c.s.mem A n).setWidth 128)],
        loads := [(A + BitVec.ofNat 64 n, n), (A, n)] } := by
  rcases has with ⟨has, rfl⟩ | ⟨has, rfl⟩
  · have hname : As.name .FLDPD = "FLDPD" := rfl
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
      ProgOp.movMem, ProgOp.pairOp, ht, pairA, hma, Eff.ld, eff_wV_f0 hka, eff_wV_f0 hkb]
    rfl
  · have hname : As.name .FLDPS = "FLDPS" := rfl
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
      ProgOp.movMem, ProgOp.pairOp, ht, pairA, hma, Eff.ld, eff_wV_f0 hka, eff_wV_f0 hkb]
    rfl

variable {L : Link} {p : Prog} {s : MState} {next : BitVec 64}

/-- `LDPW off(Rn), (Ra, Rb)` or `LDPSW` (`Ra`, `Rb` not `ZR`), both addresses outside the nil page:
`Ra` from the 4 bytes at `X kn + off`, then `Rb` from the 4 bytes above, zero-extended or, if
`sg`, sign-extended. -/
theorem progStep_ldpw {kn ka kb : Nat} {off : Int} {sg : Bool} (hkn : kn < 32) (hka : ka < 31)
    (hkb : kb < 31) (hn : L.nextAddr p.id = some next)
    (has : p.as = .LDPW ∧ sg = false ∨ p.as = .LDPSW ∧ sg = true)
    (hf : p.from_ = memA (REG_R0 + kn) off) (hsc : p.scond = 0)
    (ht : p.to = pairA (REG_R0 + ka) (REG_R0 + kb))
    (hnil : nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off) = false)
    (hnil4 : nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off + BitVec.ofNat 64 4) = false) :
    progStep L p s = .ok { (s.wX (BitVec.ofNat 5 ka)
        (if sg then ProgOp.sextTo64 4
            ((readMem s.mem (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off) 4).setWidth 64)
          else (readMem s.mem (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off) 4).setWidth 64)).wX
        (BitVec.ofNat 5 kb)
        (if sg then ProgOp.sextTo64 4 ((readMem s.mem (s.rX (BitVec.ofNat 5 kn) +
            BitVec.ofInt 64 off + BitVec.ofNat 64 4) 4).setWidth 64)
          else (readMem s.mem (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off +
            BitVec.ofNat 64 4) 4).setWidth 64) with
      pc := next } := by
  have hma := ctx_mem_reg (c := ⟨L, s, p⟩) hkn hsc (off := off)
  rw [← hf] at hma
  have he := eff_ldpw (c := ⟨L, s, p⟩) hka hkb has hma ht
  have hsk : p.isSkip = false := by
    rcases has with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [Prog.isSkip, h]
  rw [progStep_eq hn hsk he (by simp [Eff.nilAccess?, List.find?, hnil, hnil4])]
  rfl

/-- `FLDPD off(Rn), (Fa, Fb)` or `FLDPS` (`n = 8`, `4`), both addresses outside the nil page: `V ka`
from the `n` bytes at `X kn + off`, then `V kb` from the `n` bytes above. -/
theorem progStep_fldp {kn ka kb n : Nat} {off : Int} (hkn : kn < 32) (hka : ka < 32)
    (hkb : kb < 32) (hn : L.nextAddr p.id = some next)
    (has : p.as = .FLDPD ∧ n = 8 ∨ p.as = .FLDPS ∧ n = 4)
    (hf : p.from_ = memA (REG_R0 + kn) off) (hsc : p.scond = 0)
    (ht : p.to = pairA (REG_F0 + ka) (REG_F0 + kb))
    (hnil : nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off) = false)
    (hniln : nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off + BitVec.ofNat 64 n) = false) :
    progStep L p s = .ok { (s.wV (BitVec.ofNat 5 ka)
        ((readMem s.mem (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off) n).setWidth 128)).wV
        (BitVec.ofNat 5 kb)
        ((readMem s.mem (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off + BitVec.ofNat 64 n)
          n).setWidth 128) with
      pc := next } := by
  have hma := ctx_mem_reg (c := ⟨L, s, p⟩) hkn hsc (off := off)
  rw [← hf] at hma
  have he := eff_fldp (c := ⟨L, s, p⟩) hka hkb has hma ht
  have hsk : p.isSkip = false := by
    rcases has with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [Prog.isSkip, h]
  rw [progStep_eq hn hsk he (by simp [Eff.nilAccess?, List.find?, hnil, hniln])]
  simp only [Eff.apply, List.foldr]
  rfl

end GoFV.Proof.Gen
