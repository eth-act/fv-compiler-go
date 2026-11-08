import GoFV.Proof.Obj.Sim

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
-/

namespace GoFV.Proof.Witness.ObjOps

open GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj GoFV.Proof.Obj
open GoFV.Asm.ARM64 (REG_R0)

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

end GoFV.Proof.Witness.ObjOps
