import GoFV.Proof.Gen.Basic
import GoFV.Gen.Check

variable [GoFV.SSA.Sem.Addrs]

/-!
# The Progs of slice G1 under `runProg` (`docs/plans/proofs3.md` §3)

`progStep` of each Prog shape the genssa validator accepts (`GoFV.Gen.Check`), with symbolic
registers and offsets: an obj register `REG_R0 + k` (`k < 32`; `k = 31` is `ZR`) reads `rX k`.
-/

namespace GoFV.Proof.Gen

open GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64 GoFV.Gen.Check

/-! ## Operands -/

theorem gpIdx?_r0 {k : Nat} (hk : k < 32) : ProgOp.gpIdx? (REG_R0 + k) = some k := by
  have h : (REG_R0 ≤ REG_R0 + k && REG_R0 + k ≤ REG_R31) = true := by
    show (decide ((8192 : Int) ≤ 8192 + k) && decide ((8192 : Int) + k ≤ 8223)) = true
    simp; omega
  simp only [ProgOp.gpIdx?, h, if_true, Option.some.injEq]
  omega

theorem fpIdx?_r0 {k : Nat} (hk : k < 32) : ProgOp.fpIdx? (REG_R0 + k) = none := by
  have h1 : (REG_F0 ≤ REG_R0 + k && REG_R0 + k < REG_V0 + 32) = false := by
    show (decide ((8224 : Int) ≤ 8192 + k) && decide ((8192 : Int) + k < 8256 + 32)) = false
    simp; omega
  have h2 : (REG_ARNG ≤ REG_R0 + k && REG_R0 + k < REG_ARNG + 1024) = false := by
    show (decide ((9216 : Int) ≤ 8192 + k) && decide ((8192 : Int) + k < 9216 + 1024)) = false
    simp; omega
  simp only [ProgOp.fpIdx?, h1, h2]
  rfl

theorem extReg?_r0 {k : Nat} (hk : k < 32) : ProgOp.extReg? (REG_R0 + k) = none := by
  have h : (REG_R0 + k ≥ REG_EXT && REG_R0 + k < REG_EXT + 4096) = false := by
    show (decide ((8192 : Int) + k ≥ 12288) && decide ((8192 : Int) + k < 12288 + 4096)) = false
    simp; omega
  simp only [ProgOp.extReg?, h]
  rfl

theorem ctx_x_r0 {c : ProgCtx} {k : Nat} (hk : k < 32) :
    c.x (REG_R0 + k) = .ok (c.s.rX (BitVec.ofNat 5 k)) := by
  have h1 : (REG_R0 + (k : Int) == REG_RSP) = false := by
    show ((8192 : Int) + k == 8383) = false
    simp; omega
  simp only [ProgCtx.x, h1, gpIdx?_r0 hk]
  rfl

theorem ctx_src_reg {c : ProgCtx} {k : Nat} (hk : k < 32) :
    c.src true { type := .REG, reg := REG_R0 + k } = .ok (c.s.rX (BitVec.ofNat 5 k)) := by
  simp only [ProgCtx.src, extReg?_r0 hk, ctx_x_r0 hk]
  rfl

theorem ctx_src_const {c : ProgCtx} {o : Int} :
    c.src true (constA o) = .ok (BitVec.ofInt 64 o) := rfl

theorem eff_wX_r0 {e : Eff} {k : Nat} {val : BitVec 64} (hk : k < 31) :
    e.wX (REG_R0 + k) val = .ok { e with x := (k, val) :: e.x } := by
  have h1 : (REG_R0 + (k : Int) == REG_R31) = false := by
    show ((8192 : Int) + k == 8223) = false
    simp; omega
  have h2 : (REG_R0 + (k : Int) == REG_RSP) = false := by
    show ((8192 : Int) + k == 8383) = false
    simp; omega
  simp only [Eff.wX, h1, h2, gpIdx?_r0 (by omega : k < 32)]
  rfl

theorem eff_wX_zr {e : Eff} {val : BitVec 64} : e.wX REGZERO val = .ok e := rfl

/-- `e` with `X kd` written (`kd = 31`: `ZR`, no write). -/
def effWd (e : Eff) (kd : Nat) (val : BitVec 64) : Eff :=
  if kd = 31 then e else { e with x := (kd, val) :: e.x }

theorem eff_wX_dest {e : Eff} {kd : Nat} {val : BitVec 64} (hk : kd < 32) :
    e.wX (REG_R0 + kd) val = .ok (effWd e kd val) := by
  by_cases h : kd = 31
  · subst h; exact eff_wX_zr
  · simp only [effWd, h, ↓reduceIte]; exact eff_wX_r0 (by omega)

theorem wd_apply {kd : Nat} (hk : kd < 32) {val : BitVec 64} {s : MState} {next : BitVec 64} :
    (effWd {} kd val).apply s next = { s.wX (BitVec.ofNat 5 kd) val with pc := next } := by
  by_cases h : kd = 31
  · subst h; rfl
  · simp only [effWd, h, ↓reduceIte, Eff.apply, List.foldr]
    rfl

/-! ## Steps -/

theorem progStep_eq {L : Link} {p : Prog} {s : MState} {next : BitVec 64} {e : Eff}
    (hn : L.nextAddr p.id = some next) (hs : p.isSkip = false)
    (he : progEffect ⟨L, s, p⟩ = .ok e) (hnil : e.nilAccess? = none) :
    progStep L p s = .ok (e.apply s next) := by
  simp [progStep, hn, hs, he, hnil]

theorem progStep_skip {L : Link} {p : Prog} {s : MState} {next : BitVec 64}
    (hn : L.nextAddr p.id = some next) (hs : p.isSkip = true) :
    progStep L p s = .ok { s with pc := next } := by
  simp [progStep, hn, hs]

/-- A no-op (`noop`: a pseudo-op or `HINT $0`) moves the PC to the fall-through. -/
theorem progStep_noop {L : Link} {p : Prog} {s : MState} {next : BitVec 64}
    (hn : L.nextAddr p.id = some next) (h : noop p = true) :
    progStep L p s = .ok { s with pc := next } := by
  cases hs : p.isSkip
  · simp only [noop, hs, Bool.false_or, Shape.ok, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨has, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
    have hname : As.name .HINT = "HINT" := rfl
    have he : progEffect ⟨L, s, p⟩ = .ok {} := by
      unfold progEffect
      simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
        ProgOp.movMem, ProgOp.pairOp, ProgOp.rmw, ProgOp.bcond, ProgOp.startsS]
      rfl
    rw [progStep_eq hn hs he rfl]
    rfl
  · exact progStep_skip hn hs

variable {L : Link} {p : Prog} {s : MState} {next : BitVec 64}

/-- `MOVD Rs, Rd`. -/
theorem progStep_movReg {ka kd : Nat} (hka : ka < 32) (hkd : kd < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .MOVD) (hf : p.from_ = regA (REG_R0 + ka))
    (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd) (s.rX (BitVec.ofNat 5 ka)) with pc := next } := by
  have hname : As.name .MOVD = "MOVD" := rfl
  have he : progEffect ⟨L, s, p⟩ = .ok (effWd {} kd (s.rX (BitVec.ofNat 5 ka))) := by
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, hf, ht, regA, ProgOp.baseOf, ↓reduceIte,
      ProgOp.movMem, fpIdx?_r0 hka, fpIdx?_r0 hkd, ctx_x_r0 hka, ProgOp.maskN]
    exact eff_wX_dest hkd
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]),
    wd_apply hkd]

/-! ## Arithmetic -/

theorem addSub_add (x y : BitVec 64) : (addSub true false x y).1 = x + y := by
  apply BitVec.eq_of_toNat_eq
  simp [addSub, sizedF, GoFV.SSA.Sem.addWithCarry, BitVec.toNat_add]

theorem addSub_sub (x y : BitVec 64) : (addSub true true x y).1 = x - y := by
  apply BitVec.eq_of_toNat_eq
  simp only [addSub, sizedF, GoFV.SSA.Sem.addWithCarry, ↓reduceIte, BitVec.setWidth_eq,
    BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_not]
  omega

theorem addSub_flags (x y : BitVec 64) :
    (addSub true true x y).2 = (GoFV.SSA.Sem.Arm64.subFlags x y).2 := by
  simp [addSub, sizedF, GoFV.SSA.Sem.Arm64.subFlags]

/-- `MOVD $k, Rd`. -/
theorem progStep_movConst {kd : Nat} {k : Int} (hkd : kd < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .MOVD) (hf : p.from_ = constA k)
    (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd) (BitVec.ofInt 64 k) with pc := next } := by
  have hname : As.name .MOVD = "MOVD" := rfl
  have he : progEffect ⟨L, s, p⟩ = .ok (effWd {} kd (BitVec.ofInt 64 k)) := by
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, hf, ht, regA, constA, ProgOp.baseOf,
      ↓reduceIte, ProgOp.movMem, ProgOp.maskN]
    exact eff_wX_dest hkd
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
    (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]), wd_apply hkd]

theorem rn_reg {c : ProgCtx} {kn : Nat} (h : c.p.reg = REG_R0 + kn) : c.rn = REG_R0 + kn := by
  have hrn : (REG_R0 + (kn : Int) != 0) = true := by
    show ((8192 : Int) + kn != 0) = true
    simp; omega
  simp [ProgCtx.rn, h, hrn]

/-- `ADD Rm, Rn, Rd` and `SUB Rm, Rn, Rd`. -/
theorem progStep_aluReg {kn km kd : Nat} (hkn : kn < 32) (hkm : km < 32) (hkd : kd < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .ADD ∨ p.as = .SUB)
    (hf : p.from_ = regA (REG_R0 + km)) (hr : p.reg = REG_R0 + kn)
    (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      (if p.as = .ADD then s.rX (BitVec.ofNat 5 kn) + s.rX (BitVec.ofNat 5 km)
       else s.rX (BitVec.ofNat 5 kn) - s.rX (BitVec.ofNat 5 km)) with pc := next } := by
  have hrn := rn_reg (c := ⟨L, s, p⟩) hr
  rcases has with has | has
  · have hname : As.name .ADD = "ADD" := rfl
    have he : progEffect ⟨L, s, p⟩ =
        .ok (effWd {} kd (s.rX (BitVec.ofNat 5 kn) + s.rX (BitVec.ofNat 5 km))) := by
      unfold progEffect
      simp (config := { decide := true }) only [has, hname, hf, ht, hrn, regA, ProgOp.baseOf,
        ↓reduceIte, ProgOp.binNames, ctx_src_reg hkn, ctx_src_reg hkm, ProgOp.binOp, addSub_add]
      simp only [eff_wX_dest hkd]
      by_cases h : kd = 31 <;> simp [effWd, h] <;> rfl
    rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
      (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]), wd_apply hkd]
    simp [has]
  · have hname : As.name .SUB = "SUB" := rfl
    have he : progEffect ⟨L, s, p⟩ =
        .ok (effWd {} kd (s.rX (BitVec.ofNat 5 kn) - s.rX (BitVec.ofNat 5 km))) := by
      unfold progEffect
      simp (config := { decide := true }) only [has, hname, hf, ht, hrn, regA, ProgOp.baseOf,
        ↓reduceIte, ProgOp.binNames, ctx_src_reg hkn, ctx_src_reg hkm, ProgOp.binOp, addSub_sub]
      simp only [eff_wX_dest hkd]
      by_cases h : kd = 31 <;> simp [effWd, h] <;> rfl
    rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
      (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]), wd_apply hkd]
    simp [has]
/-- `ADD $k, Rn, Rd` and `SUB $k, Rn, Rd`. -/
theorem progStep_aluConst {kn kd : Nat} {k : Int} (hkn : kn < 32) (hkd : kd < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .ADD ∨ p.as = .SUB)
    (hf : p.from_ = constA k) (hr : p.reg = REG_R0 + kn) (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      (if p.as = .ADD then s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 k
       else s.rX (BitVec.ofNat 5 kn) - BitVec.ofInt 64 k) with pc := next } := by
  have hrn := rn_reg (c := ⟨L, s, p⟩) hr
  rcases has with has | has
  · have hname : As.name .ADD = "ADD" := rfl
    have he : progEffect ⟨L, s, p⟩ =
        .ok (effWd {} kd (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 k)) := by
      unfold progEffect
      simp (config := { decide := true }) only [has, hname, hf, ht, hrn, regA, constA,
        ProgOp.baseOf, ↓reduceIte, ProgOp.binNames, ctx_src_reg hkn, ctx_src_const, ProgOp.binOp,
        addSub_add]
      simp only [eff_wX_dest hkd]
      by_cases h : kd = 31 <;> simp [effWd, h] <;> rfl
    rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
      (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]), wd_apply hkd]
    simp [has]
  · have hname : As.name .SUB = "SUB" := rfl
    have he : progEffect ⟨L, s, p⟩ =
        .ok (effWd {} kd (s.rX (BitVec.ofNat 5 kn) - BitVec.ofInt 64 k)) := by
      unfold progEffect
      simp (config := { decide := true }) only [has, hname, hf, ht, hrn, regA, constA,
        ProgOp.baseOf, ↓reduceIte, ProgOp.binNames, ctx_src_reg hkn, ctx_src_const, ProgOp.binOp,
        addSub_sub]
      simp only [eff_wX_dest hkd]
      by_cases h : kd = 31 <;> simp [effWd, h] <;> rfl
    rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
      (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]), wd_apply hkd]
    simp [has]

/-- `CMP from, Rn` with `from` a register or a constant whose value is `y`. -/
theorem progStep_cmp {kn : Nat} {y : BitVec 64} (hkn : kn < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .CMP)
    (hy : ProgCtx.src ⟨L, s, p⟩ true p.from_ = .ok y) (hr : p.reg = REG_R0 + kn) :
    progStep L p s = .ok { s with
      nzcv := (GoFV.SSA.Sem.Arm64.subFlags (s.rX (BitVec.ofNat 5 kn)) y).2, pc := next } := by
  have hname : As.name .CMP = "CMP" := rfl
  have he : progEffect ⟨L, s, p⟩ =
      .ok { flags := some (GoFV.SSA.Sem.Arm64.subFlags (s.rX (BitVec.ofNat 5 kn)) y).2 } := by
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, hr, ProgOp.baseOf, ↓reduceIte,
      ProgOp.binNames, ctx_src_reg hkn, hy, ProgOp.binOp, addSub_flags]
    rfl
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he rfl]
  rfl

/-- `MOVD off(Rn), Rd`, the address outside the nil page. -/
theorem progStep_load {kn kd : Nat} {off : Int} (hkn : kn < 32) (hkd : kd < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .MOVD) (hf : p.from_ = memA (REG_R0 + kn) off)
    (hsc : p.scond = 0) (ht : p.to = regA (REG_R0 + kd))
    (hnil : nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off) = false) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      ((readMem s.mem (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off) 8).setWidth 64) with
        pc := next } := by
  have hname : As.name .MOVD = "MOVD" := rfl
  let a := s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off
  have he : progEffect ⟨L, s, p⟩ =
      .ok (effWd { loads := [(a, 8)] } kd ((readMem s.mem a 8).setWidth 64)) := by
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, hf, ht, hsc, memA, regA, ProgOp.baseOf,
      ↓reduceIte, ProgOp.movMem, ProgCtx.mem, ctx_x_r0 hkn, Eff.ld, ProgCtx.load]
    simp only [eff_wX_dest hkd]
    rfl
  have hnil' : (effWd { loads := [(a, 8)] } kd ((readMem s.mem a 8).setWidth 64)).nilAccess? =
      none := by
    by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?, List.find?, hnil, a]
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he hnil']
  by_cases h : kd = 31
  · subst h; rfl
  · simp only [effWd, h, ↓reduceIte, Eff.apply, List.foldr]
    rfl

/-- `MOVD Rs, off(Rn)`, the address outside the nil page. -/
theorem progStep_store {kn ks : Nat} {off : Int} (hkn : kn < 32) (hks : ks < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .MOVD) (hf : p.from_ = regA (REG_R0 + ks))
    (hsc : p.scond = 0) (ht : p.to = memA (REG_R0 + kn) off)
    (hnil : nilPage (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off) = false) :
    progStep L p s = .ok { s with
      mem := writeMem s.mem (s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off) 8
        (BitVec.ofNat (8 * 8) ((s.rX (BitVec.ofNat 5 ks)).toNat % 2 ^ (8 * 8))),
      pc := next } := by
  have hname : As.name .MOVD = "MOVD" := rfl
  let a := s.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 off
  have he : progEffect ⟨L, s, p⟩ =
      .ok { stores := [(a, 8, (s.rX (BitVec.ofNat 5 ks)).toNat % 2 ^ (8 * 8))] } := by
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, hf, ht, hsc, memA, regA, ProgOp.baseOf,
      ↓reduceIte, ProgOp.movMem, ProgCtx.mem, ctx_x_r0 hkn, ctx_x_r0 hks]
    rfl
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he (by simp [Eff.nilAccess?, List.find?, hnil, a])]
  rfl

/-- The condition of a conditional branch opcode. -/
def condAs : As → Option GoFV.SSA.Sem.Cond
  | .BEQ => some .eq | .BNE => some .ne | .BLT => some .lt | .BGE => some .ge
  | .BLE => some .le | .BGT => some .gt | .BLO => some .lo | .BHS => some .hs
  | .BLS => some .ls | .BHI => some .hi
  | _ => none

theorem ctx_target {c : ProgCtx} {t : Nat} {pt : BitVec 64} (h : c.L.addr t = some pt) :
    c.target (brA t) = .ok pt := by
  simp [ProgCtx.target, brA, h]
  rfl

end GoFV.Proof.Gen
