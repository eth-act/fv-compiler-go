import GoFV.Proof.Gen.Progs3

variable [GoFV.SSA.Sem.Addrs]

/-!
# The nil check under `runProg`, and Prog runs that panic (`docs/plans/proofs3.md` §4, G7)

`MOVB (Rn), R27` (`LoweredNilCheck`'s Prog, `REGTMP` the destination): outside the nil page it
loads the byte into `X27` (`progStep_nilCheck`, `progStep_loadN` at `kd = 27`); in the nil page
it faults (`progStep_nilCheck_nil`, `progStep` is `.error (.nilPage a)`), which `runProg` turns
into `panicked .nilDeref` (`PPanics`, `PPanics.runProg`: `runProg`'s panic, as `MPanics` is
`runMach`'s).
-/

namespace GoFV.Proof.Gen

open GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64 GoFV.Gen.Check

/-! ## Panicking runs -/

/-- `runProg H L ps ret` panics with `e` from `s`, as `MPanics` for `runMach`: a Prog whose access
is in the nil page (`nilDeref`; `runProg` stops at the state before the Prog), or a hook that
panics. -/
def PPanics (H : Hooks) (L : Link) (ps : List Prog) (ret : BitVec 64) (s : MState)
    (e : GoFV.SSA.Sem.Panic) : Prop :=
  s.pc ≠ ret ∧
    ((∃ p a, progAt? L ps s.pc = some p ∧ progStep L p s = .error (.nilPage a) ∧
        e = .nilDeref) ∨
     (progAt? L ps s.pc = none ∧ ∃ s', H.call s = some (.panicked e s')))

/-- `PPanics` is a panicking `runProg`. -/
theorem PPanics.runProg {H : Hooks} {L : Link} {ps : List Prog} {ret : BitVec 64} {s : MState}
    {e : GoFV.SSA.Sem.Panic} (h : PPanics H L ps ret s e) (k : Nat) :
    ∃ s', GoFV.Arm64.runProg H L ps ret (k + 1) s = .panicked e s' := by
  obtain ⟨hpc, ⟨p, a, hp, hs, rfl⟩ | ⟨hp, s', hh⟩⟩ := h
  · exact ⟨s, by simp [GoFV.Arm64.runProg, hpc, hp, hs]⟩
  · exact ⟨s', by simp [GoFV.Arm64.runProg, hpc, hp, hh]⟩

/-! ## `MOVB (Rn), R27` -/

/-- `REGTMP` is `R27`. -/
theorem regTmp_eq : REGTMP = REG_R0 + 27 := rfl

/-- The effect of `MOVB (Rn), R27`: a one-byte load at `Rn`, sign-extended into `X27`. -/
theorem progEffect_nilCheck {c : ProgCtx} {kn : Nat} (hkn : kn < 32) (has : c.p.as = .MOVB)
    (hf : c.p.from_ = memA (REG_R0 + kn) 0) (hsc : c.p.scond = 0) (ht : c.p.to = regA REGTMP) :
    progEffect c = .ok (effWd { loads := [(c.s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 0, 1)] } 27
      (ProgOp.sextTo64 1
        ((readMem c.s.mem (c.s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 0) 1).setWidth 64))) := by
  have hn : c.p.as.name = "MOVB" := by rw [has]; rfl
  have hma := ctx_mem_reg (c := c) (off := 0) hkn hsc
  unfold progEffect
  simp (config := { decide := true }) only [hn, hf, ht, hma, regA, regTmp_eq, Eff.ld,
    ProgCtx.load, ProgOp.baseOf, ProgOp.movMem, ProgOp.pairOp, ProgOp.endsS, ProgOp.chopS,
    ↓reduceIte]
  exact eff_wX_dest (kd := 27) (by decide)

variable {L : Link} {p : Prog} {s : MState} {next : BitVec 64}

/-- `MOVB (Rn), R27` outside the nil page: `X27` is the byte, sign-extended, and the PC the
fall-through. -/
theorem progStep_nilCheck {kn : Nat} (hkn : kn < 32) (hn : L.nextAddr p.id = some next)
    (has : p.as = .MOVB) (hf : p.from_ = memA (REG_R0 + kn) 0) (hsc : p.scond = 0)
    (ht : p.to = regA REGTMP)
    (hnil : nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 0) = false) :
    ∃ val, progStep L p s = .ok { s.wX (BitVec.ofNat 5 27) val with pc := next } :=
  ⟨_, progStep_loadN (kd := 27) hkn (by decide) hn (by rw [has]; rfl) hf hsc ht hnil⟩

/-- `MOVB (Rn), R27` in the nil page: the access faults. -/
theorem progStep_nilCheck_nil {kn : Nat} (hkn : kn < 32) (hn : L.nextAddr p.id = some next)
    (has : p.as = .MOVB) (hf : p.from_ = memA (REG_R0 + kn) 0) (hsc : p.scond = 0)
    (ht : p.to = regA REGTMP)
    (hnil : nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 0) = true) :
    progStep L p s = .error (.nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 0)) := by
  have he := progEffect_nilCheck (c := ⟨L, s, p⟩) hkn has hf hsc ht
  have hsk : p.isSkip = false := by unfold Prog.isSkip; rw [has]
  have hnil' : nilPage (s.rX (BitVec.ofNat 5 kn)) = true := by simpa using hnil
  simp [progStep, hn, hsk, he, effWd, Eff.nilAccess?, hnil']

end GoFV.Proof.Gen
