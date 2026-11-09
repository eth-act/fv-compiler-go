import GoFV.Proof.Obj.Sim

open scoped GoFV.SSA.Sem.Fixed

/-!
# Non-vacuity witnesses: the opcodes `checkObj` added (#553)

* `objOps_csel_witness`: `symInsn_sound` on a `CSINC` word (`CSET` as the assembler encodes it)
  from the initial symbolic state: the conditional-select case of `symInsn`.
* `objOps_blr_witness`: `symInsn_sound` on `BLR X2`: the machine control `callReg`, `X30` the next
  word.
* `objOps_fault_witness`: `symInsn_fault` on `LDAR X1, [X0]` from a state with `X0 = 0`: the
  acquire load's symbolic access is in the nil page and the word faults there.
* `objOps_ctl_witness`: `progSym_ctl` on `CALL (R2)`: an indirect call's control is `callReg`,
  from a `CALL`.
* `objOps_udiv_witness`, `objOps_bic_witness`: `symInsn_sound` on `UDIV X1, X2, X3` (`Ex.dp2`)
  and on `BIC X1, X2, X3` (logical shifted register with the inversion, `Ex.inv`).
* `objOps_rem_witness`: `REM R3, R1, R2` (`progSym`, `dp2P`) and its words `SDIV X27, X1, X3;
  MSUB X2, X27, X3, X1` (`symInsn`) have the same effect (`sameEffect`).
* `objOps_fadd_witness`: `symInsn_sound` on `FADD D3, D2, D1` (the SIMD&FP data processing,
  `VEx.fp2` into `V3`), and `FADDD F1, F2, F3` (`progSym`, `fpP`) has the same effect.
* `objOps_stpq_witness`: `symInsn_sound` on `STP Q1, Q2, [SP, #32]` (two `Q` stores, `Ex.vq`)
  from a state whose `V1`, `V2` have both halves nonzero: the memory after holds all 128 bits
  of each; and `FSTPQ (F1, F2), 32(RSP)` (`progSym`, `fpairP`) has the same effect.
* `objOps_strq_witness`: the same for `STR Q3, [SP, #16]` and `FMOVQ F3, 16(RSP)` (`fmovP`).
* `objOps_eval128_witness`: `Ex.eval128` of `Ex.vq` is the whole register, and
  `Ex.eval128_setWidth` its low half as `Ex.eval`; `Ex.eval128_congr` across two contexts.
-/

namespace GoFV.Proof.Witness.ObjOps

open GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj GoFV.Proof.Obj
open GoFV.Asm.ARM64 (REG_R0 REG_F0 REG_RSP)

/-- A machine state with every register `0`, at `0x1000`. -/
def t0 : MState :=
  { x := fun _ => 0, sp := 0x8000, v := fun _ => 0, nzcv := ⟨false, false, false, false⟩,
    pc := 0x1000, mem := fun _ => 0 }

/-- `CSINC X1, XZR, XZR, NE` (`CSET X1, EQ`). -/
def cset : Insn := .condSel true false true 31 1 31 1

theorem objOps_csel_witness :
    ∃ σ' mc t', symInsn cset 0 {} = .ok (σ', mc) ∧ exec cset t0 = .ok t' ∧
      WordsPost ⟨t0, fun _ => 0⟩ 0x1000 0 σ' mc t' := by
  have h : symInsn cset 0 {} = .ok (({} : Sym).wX 1 (.csel true false true 1 (.k 0) (.k 0)), .fall) :=
    rfl
  obtain ⟨t', he, hp⟩ := symInsn_sound (c := ⟨t0, fun _ => 0⟩) (base := 0x1000) h (holds_init _)
    (by simp [t0]) ⟨fun _ _ h => by simp [Sym.wX] at h, fun _ _ _ h => by simp [Sym.wX] at h⟩
  exact ⟨_, _, t', h, he, hp⟩

/-- `BLR X2`. -/
def blr : Insn := .br .blr 2

theorem objOps_blr_witness :
    ∃ t', exec blr t0 = .ok t' ∧ t'.pc = t0.x 2 ∧ t'.x 30 = 0x1004 := by
  have h : symInsn blr 0 {} = .ok ({}, .callReg (.x 2)) := rfl
  obtain ⟨t', he, -, -, hpc, h30⟩ := symInsn_sound (c := ⟨t0, fun _ => 0⟩) (base := 0x1000) h
    (holds_init _) (by simp [t0]) ⟨fun _ _ h => by simp at h, fun _ _ _ h => by simp at h⟩
  refine ⟨t', he, by rw [hpc]; rfl, by rw [h30]; rfl⟩

/-- `LDAR X1, [X0]`. -/
def ldar : Insn := .ldstExcl 3 true true false 31 0 1

theorem objOps_fault_witness : ∃ x, exec ldar t0 = .error (.nilPage x) := by
  have h : symInsn ldar 0 {} =
      .ok (({ loads := [(.x 0, 8)] } : Sym).wX 1 (.ld 8 (.x 0)), .fall) := rfl
  refine symInsn_fault (c := ⟨t0, fun _ => 0⟩) h (holds_init _)
    ⟨fun _ _ h => by simp at h, fun _ _ _ h => by simp at h⟩ fun hn => ?_
  have := hn.1 (.x 0) 8 (by simp [Sym.wX])
  revert this
  decide

/-- `CALL (R2)`. -/
def callR2 : Prog := mkProg 3 .CALL {} { type := .REG, reg := REG_R0 + 2 }

theorem objOps_ctl_witness :
    progSym 0 0 callR2 = .ok ({}, .callReg (.x 2)) ∧ callR2.as = .CALL :=
  have h : progSym 0 0 callR2 = .ok ({}, .callReg (.x 2)) := by rfl
  ⟨h, (progSym_ctl h).2.1 _ rfl⟩

/-- `UDIV X1, X2, X3`. -/
def udiv : Insn := .dp2 true 2 3 2 1

theorem objOps_udiv_witness :
    ∃ σ' mc t', symInsn udiv 0 {} = .ok (σ', mc) ∧ exec udiv t0 = .ok t' ∧
      WordsPost ⟨t0, fun _ => 0⟩ 0x1000 0 σ' mc t' := by
  have h : symInsn udiv 0 {} = .ok (({} : Sym).wX 1 (.dp2 true 2 (.x 2) (.x 3)), .fall) := rfl
  obtain ⟨t', he, hp⟩ := symInsn_sound (c := ⟨t0, fun _ => 0⟩) (base := 0x1000) h (holds_init _)
    (by simp [t0]) ⟨fun _ _ h => by simp [Sym.wX] at h, fun _ _ _ h => by simp [Sym.wX] at h⟩
  exact ⟨_, _, t', h, he, hp⟩

/-- `BIC X1, X2, X3` (`AND` shifted register with the inversion `n`). -/
def bic : Insn := .logShift true 0 0 true 3 0 2 1

theorem objOps_bic_witness :
    ∃ σ' mc t', symInsn bic 0 {} = .ok (σ', mc) ∧ exec bic t0 = .ok t' ∧
      WordsPost ⟨t0, fun _ => 0⟩ 0x1000 0 σ' mc t' := by
  have h : symInsn bic 0 {} =
      .ok (({} : Sym).wX 1 (.logical true 0 (.x 2) (.inv true (.x 3))), .fall) := rfl
  obtain ⟨t', he, hp⟩ := symInsn_sound (c := ⟨t0, fun _ => 0⟩) (base := 0x1000) h (holds_init _)
    (by simp [t0]) ⟨fun _ _ h => by simp [Sym.wX] at h, fun _ _ _ h => by simp [Sym.wX] at h⟩
  exact ⟨_, _, t', h, he, hp⟩

/-- `REM R3, R1, R2` and the words the assembler encodes it as (`asmout` case 16):
`SDIV X27, X1, X3; MSUB X2, X27, X3, X1`. -/
def remP : Prog :=
  mkProg 3 .REM { type := .REG, reg := REG_R0 + 3 } { type := .REG, reg := REG_R0 + 2 } (REG_R0 + 1)

/-- `SDIV X27, X1, X3`. -/
def sdiv27 : Insn := .dp2 true 3 3 1 27

/-- `MSUB X2, X27, X3, X1`. -/
def msub27 : Insn := .dp3 true 0 true 3 1 27 2

theorem objOps_rem_witness :
    ∃ σ1 σ2 pσ, symInsn sdiv27 0 {} = .ok (σ1, .fall) ∧ symInsn msub27 4 σ1 = .ok (σ2, .fall) ∧
      progSym 0 0 remP = .ok (pσ, .fall) ∧ sameEffect σ2 pσ = .ok () :=
  ⟨_, _, _, rfl, rfl, rfl, rfl⟩

/-- `FADD D3, D2, D1`. -/
def fadd : Insn := .fp2 1 2 1 2 3

/-- `FADDD F1, F2, F3`. -/
def faddP : Prog :=
  mkProg 3 .FADDD { type := .REG, reg := REG_F0 + 1 } { type := .REG, reg := REG_F0 + 3 }
    (REG_F0 + 2)

theorem objOps_fadd_witness :
    ∃ σ' mc t' pσ, symInsn fadd 0 {} = .ok (σ', mc) ∧ exec fadd t0 = .ok t' ∧
      WordsPost ⟨t0, fun _ => 0⟩ 0x1000 0 σ' mc t' ∧
      progSym 0 0 faddP = .ok (pσ, .fall) ∧ sameEffect σ' pσ = .ok () := by
  have h : symInsn fadd 0 {} = .ok (({} : Sym).wV 3 (.fp2 1 2 (.v 2) (.v 1)), .fall) := rfl
  obtain ⟨t', he, hp⟩ := symInsn_sound (c := ⟨t0, fun _ => 0⟩) (base := 0x1000) h (holds_init _)
    (by simp [t0]) ⟨fun _ _ h => by simp [Sym.wV] at h, fun _ _ _ h => by simp [Sym.wV] at h⟩
  exact ⟨_, _, t', _, h, he, hp, rfl, rfl⟩

/-- `t0` with `V1`, `V2`, `V3` set to values whose high halves are nonzero. -/
def t1 : MState :=
  { t0 with v := fun r =>
      if r = 1 then 0x0123456789abcdeffedcba9876543210#128
      else if r = 2 then 0x00112233445566778899aabbccddeeff#128
      else if r = 3 then 0xfedcba98765432100123456789abcdef#128 else 0 }

/-- `STP Q1, Q2, [SP, #32]`. -/
def stpq : Insn := .ldstPair 2 true 2 false 2 2 31 1

/-- `FSTPQ (F1, F2), 32(RSP)`. -/
def fstpqP : Prog :=
  mkProg 3 .FSTPQ { type := .REGREG, reg := REG_F0 + 1, offset := REG_F0 + 2 }
    { type := .MEM, reg := REG_RSP, offset := 32 }

theorem objOps_stpq_witness :
    ∃ σ' mc t' pσ, symInsn stpq 0 {} = .ok (σ', mc) ∧ exec stpq t1 = .ok t' ∧
      WordsPost ⟨t1, fun _ => 0⟩ 0x1000 0 σ' mc t' ∧
      readMem t'.mem 0x8020 16 = t1.v 1 ∧ readMem t'.mem 0x8030 16 = t1.v 2 ∧
      progSym 0 0 fstpqP = .ok (pσ, .fall) ∧ sameEffect σ' pσ = .ok () := by
  have h : symInsn stpq 0 {} =
      .ok ({ stores := [(.add .sp (.k 32), 16, .vq 1), (.add .sp (.k 48), 16, .vq 2)] }, .fall) :=
    rfl
  obtain ⟨t', he, hp⟩ := symInsn_sound (c := ⟨t1, fun _ => 0⟩) (base := 0x1000) h (holds_init _)
    (by simp [t1, t0]) ⟨fun _ _ h => by simp at h, fun a n v h => by
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
      rcases h with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ <;> decide⟩
  have hm := hp.1.mem
  refine ⟨_, _, t', _, h, he, hp, ?_, ?_, rfl, rfl⟩ <;> (rw [hm]; decide +kernel)

/-- `STR Q3, [SP, #16]`. -/
def strq : Insn := .ldst 0 true 2 (.uimm 1) 31 3

/-- `FMOVQ F3, 16(RSP)`. -/
def fmovqP : Prog :=
  mkProg 3 .FMOVQ { type := .REG, reg := REG_F0 + 3 } { type := .MEM, reg := REG_RSP, offset := 16 }

theorem objOps_strq_witness :
    ∃ σ' mc t' pσ, symInsn strq 0 {} = .ok (σ', mc) ∧ exec strq t1 = .ok t' ∧
      WordsPost ⟨t1, fun _ => 0⟩ 0x1000 0 σ' mc t' ∧ readMem t'.mem 0x8010 16 = t1.v 3 ∧
      progSym 0 0 fmovqP = .ok (pσ, .fall) ∧ sameEffect σ' pσ = .ok () := by
  have h : symInsn strq 0 {} = .ok ({ stores := [(.add .sp (.k 16), 16, .vq 3)] }, .fall) := rfl
  obtain ⟨t', he, hp⟩ := symInsn_sound (c := ⟨t1, fun _ => 0⟩) (base := 0x1000) h (holds_init _)
    (by simp [t1, t0]) ⟨fun _ _ h => by simp at h, fun a n v h => by
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h
      obtain ⟨rfl, -, -⟩ := h
      decide⟩
  have hm := hp.1.mem
  refine ⟨_, _, t', _, h, he, hp, ?_, rfl, rfl⟩
  rw [hm]
  decide +kernel

theorem objOps_eval128_witness :
    (Ex.vq 1).eval128 ⟨t1, fun _ => 0⟩ = t1.v 1 ∧
      ((Ex.vq 1).eval128 ⟨t1, fun _ => 0⟩).setWidth (8 * 8) =
        ((Ex.vq 1).eval ⟨t1, fun _ => 0⟩).setWidth (8 * 8) ∧
      (Ex.vq 1).eval128 ⟨t1, fun _ => 0⟩ = (Ex.vq 1).eval128 ⟨{ t1 with x := fun _ => 1 }, fun _ => 0⟩ :=
  ⟨rfl, Ex.eval128_setWidth (Nat.le_refl 8) _ _,
    Ex.eval128_congr rfl rfl rfl rfl rfl _ fun _ h => by simp [Ex.reads] at h⟩

end GoFV.Proof.Witness.ObjOps
