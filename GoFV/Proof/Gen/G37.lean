import GoFV.Proof.Gen.G36
import GoFV.Proof.Gen.Spec37

variable [GoFV.SSA.Sem.Addrs]

/-!
# Soundness of the genssa validator's slice G37: multiplies, divides, byte and bit reversals, `SBFX`
(`docs/plans/proofs3.md` §4)

`g37_value`, `g37_term`, `g37_nilPanic`, `g37_boundsPanic`: `g36_value`'s, `g36_term`'s,
`g36_nilPanic`'s and `g36_boundsPanic`'s statements over `checkG37`, carrying the upper-bit
invariant `UOKL` of G35's table `uL35` alike.

`runLoc` runs the G37 ops as `Arm64.evalPure` of the arguments read from their homes
(`stepLoc_alu37`). On 64-bit arguments a register is the machine word, so `UMULH`, `SMULH`, `UDIV`,
`SDIV` (`binF37`) and `RBIT` agree with the machine (`progStep_bin37`, `progStep_un37`); on
arguments of at least 32 bits the low words are the machine's, which the `W` ops (`MULW`, `UDIVW`,
`SDIVW`, `REVW`, `REV16W`, `MADDW`, `MSUBW`) and `UMULL` read, zero-extending their 32-bit results as
the machine does (`res32`). `MADD`/`MSUB` are Phase 1's `madd`, `addP` of `a` and the product (or
its negation), whose low bits read only the factors' low bits (`lo_madd37`, with `ADD`'s pointer
case); the machine computes `Ra ± Rn · Rm` (`dp3Op`, `progStep_madd37`). `SBFX $lsb, Rn, $width,
Rd` sign-extends bits `lsb … lsb + width - 1` of the argument, all below its class (`lo_sbfx37`,
`progStep_sbfx37`). The G37 ops empty the upper-bit table (`uStep35_alu37`). On a function with no
arm64 op, `checkG37` is `checkG33` (`checkG33_of_37`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The ops -/

/-- The machine word function of a register op of G37 (`op Rm, Rn, Rd`, `Rn` first). -/
def binF37 : As → BitVec 64 → BitVec 64 → BitVec 64
  | .UMULH => GoFV.SSA.Sem.Arm64.umulh
  | .SMULH => GoFV.SSA.Sem.Arm64.smulh
  | .UDIV => fun x y => x / y
  | .SDIV => fun x y => x.sdiv y
  | .MULW => fun x y => (x.setWidth 32 * y.setWidth 32).setWidth 64
  | .UDIVW => fun x y => (x.setWidth 32 / y.setWidth 32).setWidth 64
  | .SDIVW => fun x y => ((x.setWidth 32).sdiv (y.setWidth 32)).setWidth 64
  | _ => GoFV.SSA.Sem.Arm64.umull

/-- The machine word function of a unary op of G37. -/
def unF37 : As → BitVec 64 → BitVec 64
  | .RBIT => GoFV.SSA.Sem.Arm64.rbit
  | .REVW => fun x => (GoFV.SSA.Sem.Arm64.rev (x.setWidth 32)).setWidth 64
  | _ => fun x => (GoFV.SSA.Sem.Arm64.rev16 (x.setWidth 32)).setWidth 64

/-- The machine word function of a multiply-add of G37 (`op Rm, Ra, Rn, Rd`): `Ra ± Rn · Rm`. -/
def maddF37 : As → BitVec 64 → BitVec 64 → BitVec 64 → BitVec 64
  | .MADD => fun a n m => a + n * m
  | .MSUB => fun a n m => a - n * m
  | .MADDW => fun a n m => (a.setWidth 32 + n.setWidth 32 * m.setWidth 32).setWidth 64
  | _ => fun a n m => (a.setWidth 32 - n.setWidth 32 * m.setWidth 32).setWidth 64

theorem full37?_some {op : Op} {as : As} (h : full37? op = some as) :
    op = .ARM64UMULH ∧ as = .UMULH ∨ op = .ARM64MULH ∧ as = .SMULH ∨
      op = .ARM64UDIV ∧ as = .UDIV ∨ op = .ARM64DIV ∧ as = .SDIV := by
  unfold full37? at h
  split at h <;> (try cases h) <;> simp

theorem w37?_some {op : Op} {as : As} (h : w37? op = some as) :
    op = .ARM64MULW ∧ as = .MULW ∨ op = .ARM64UDIVW ∧ as = .UDIVW ∨
      op = .ARM64DIVW ∧ as = .SDIVW ∨ op = .ARM64UMULL ∧ as = .UMULL := by
  unfold w37? at h
  split at h <;> (try cases h) <;> simp

theorem un37?_some {op : Op} {as : As} {ca : Nat} (h : un37? op = some (as, ca)) :
    op = .ARM64RBIT ∧ as = .RBIT ∧ ca = 64 ∨ op = .ARM64REVW ∧ as = .REVW ∧ ca = 32 ∨
      op = .ARM64REV16W ∧ as = .REV16W ∧ ca = 32 := by
  unfold un37? at h
  split at h <;> (try cases h) <;> simp

theorem madd37?_some {op : Op} {as : As} {w : Bool} (h : madd37? op = some (as, w)) :
    op = .ARM64MADD ∧ as = .MADD ∧ w = false ∨ op = .ARM64MSUB ∧ as = .MSUB ∧ w = false ∨
      op = .ARM64MADDW ∧ as = .MADDW ∧ w = true ∨ op = .ARM64MSUBW ∧ as = .MSUBW ∧ w = true := by
  unfold madd37? at h
  split at h <;> (try cases h) <;> simp

/-- The ops of G37. -/
def AluOp37 (op : Op) : Prop :=
  op = .ARM64UMULH ∨ op = .ARM64MULH ∨ op = .ARM64UDIV ∨ op = .ARM64DIV ∨ op = .ARM64MULW ∨
    op = .ARM64UDIVW ∨ op = .ARM64DIVW ∨ op = .ARM64UMULL ∨ op = .ARM64RBIT ∨
    op = .ARM64REVW ∨ op = .ARM64REV16W ∨ op = .ARM64MADD ∨ op = .ARM64MSUB ∨
    op = .ARM64MADDW ∨ op = .ARM64MSUBW ∨ op = .ARM64SBFX

theorem aluOp37_bin {op : Op} {as : As} {cw : Nat}
    (h : full37? op = some as ∧ cw = 64 ∨ w37? op = some as ∧ cw = 32) : AluOp37 op := by
  unfold AluOp37
  rcases h with ⟨h, -⟩ | ⟨h, -⟩
  · rcases full37?_some h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
  · rcases w37?_some h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp

theorem aluOp37_un {op : Op} {as : As} {ca : Nat} (h : un37? op = some (as, ca)) : AluOp37 op := by
  unfold AluOp37
  rcases un37?_some h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp

theorem aluOp37_madd {op : Op} {as : As} {w : Bool} (h : madd37? op = some (as, w)) :
    AluOp37 op := by
  unfold AluOp37
  rcases madd37?_some h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp

theorem aluOp37_ne {op : Op} (h : AluOp37 op) :
    op ≠ .Phi ∧ op ≠ .ARM64MOVDnop ∧ op ≠ .ARM64MOVDreg ∧ op ≠ .ARM64LoweredNilCheck ∧
      pbOp op = false := by
  unfold AluOp37 at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    exact ⟨nofun, nofun, nofun, nofun, rfl⟩

/-- A G37 op empties G35's table. -/
theorem uStep35_alu37 {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value}
    (hop : AluOp37 v.op) : uStep35 lc L v = [] := by
  obtain ⟨-, hn1, hn2, -, -⟩ := aluOp37_ne hop
  have hl : loadOp? v.op = none := by
    unfold AluOp37 at hop
    rcases hop with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;>
      rfl
  have hp : pairOp35 lc v = false := by
    unfold AluOp37 at hop
    simp only [pairOp35, Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
    rcases hop with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      (rw [h]; exact ⟨nofun, .inl (by decide)⟩)
  have hk : keep34 v = false := by
    unfold AluOp37 at hop
    unfold keep34 keep31
    rcases hop with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      simp [h, keepOp31, keepOp34]
  have hk31 : keep31 v = false := by
    simp only [keep34, Bool.or_eq_false_iff] at hk
    exact hk.1
  have hue : uEntry lc v = none := by
    have : narrowLd? lc v = none := by
      unfold narrowLd?
      have hi : loadIdxOp? v.op = none := by
        unfold AluOp37 at hop
        rcases hop with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
          rw [h] <;> rfl
      rw [hl, hi]
    simp only [uEntry, this]
  rw [uStep35_other (ldEntry35_none hl) hp, uStep34_other hk, uStep31_other hk31,
    uStepL_other hue hn1 hn2]

/-! ## `runLoc` -/

section Steps

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

/-- The ops of G37: `Arm64.evalPure` on the arguments read from their homes. -/
theorem stepLoc_alu37 (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : AluOp37 v.op) (h : stepLoc env lc s v = .ok s') :
    ∃ argv, v.args.toList.mapM (s.read lc) = .ok argv ∧
      s' = s.write lc v.id ((Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux argv).retypeL
        (lc.ty v.id)) := by
  unfold AluOp37 at hop
  rcases hop with hop | hop | hop | hop | hop | hop | hop | hop | hop | hop | hop | hop | hop |
    hop | hop | hop <;>
  · obtain ⟨argv, r, hm, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
      (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
      (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
    have he : evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) =
        .ok (Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux argv) := by
      unfold evalOpL; rw [hop]; rfl
    rw [he] at hr; cases hr
    exact ⟨argv, hm, rfl⟩

end Steps

/-! ## The machine -/

section Progs

variable {L : Link} {p : Prog} {s : MState} {next : BitVec 64}

private theorem nUMULH : As.UMULH.name = "UMULH" := rfl
private theorem nSMULH : As.SMULH.name = "SMULH" := rfl
private theorem nUDIV : As.UDIV.name = "UDIV" := rfl
private theorem nSDIV : As.SDIV.name = "SDIV" := rfl
private theorem nMULW : As.MULW.name = "MULW" := rfl
private theorem nUDIVW : As.UDIVW.name = "UDIVW" := rfl
private theorem nSDIVW : As.SDIVW.name = "SDIVW" := rfl
private theorem nUMULL : As.UMULL.name = "UMULL" := rfl
private theorem nRBIT : As.RBIT.name = "RBIT" := rfl
private theorem nREVW : As.REVW.name = "REVW" := rfl
private theorem nREV16W : As.REV16W.name = "REV16W" := rfl
private theorem nMADD : As.MADD.name = "MADD" := rfl
private theorem nMSUB : As.MSUB.name = "MSUB" := rfl
private theorem nMADDW : As.MADDW.name = "MADDW" := rfl
private theorem nMSUBW : As.MSUBW.name = "MSUBW" := rfl
private theorem cMULW : ProgOp.chopS "MULW" 1 = "MUL" := by decide
private theorem cUDIVW : ProgOp.chopS "UDIVW" 1 = "UDIV" := by decide
private theorem cSDIVW : ProgOp.chopS "SDIVW" 1 = "SDIV" := by decide
private theorem cREVW : ProgOp.chopS "REVW" 1 = "REV" := by decide
private theorem cREV16W : ProgOp.chopS "REV16W" 1 = "REV16" := by decide
private theorem cMADDW : ProgOp.chopS "MADDW" 1 = "MADD" := by decide
private theorem cMSUBW : ProgOp.chopS "MSUBW" 1 = "MSUB" := by decide

/-- `op Rm, Rn, Rd` for a register op of G37. -/
theorem progStep_bin37 {as : As} {kn km kd : Nat}
    (has : as = .UMULH ∨ as = .SMULH ∨ as = .UDIV ∨ as = .SDIV ∨ as = .MULW ∨ as = .UDIVW ∨
      as = .SDIVW ∨ as = .UMULL)
    (hkn : kn < 32) (hkm : km < 32) (hkd : kd < 32)
    (hn : L.nextAddr p.id = some next) (hpa : p.as = as) (hf : p.from_ = regA (REG_R0 + km))
    (hr : p.reg = REG_R0 + kn) (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      (binF37 as (s.rX (BitVec.ofNat 5 kn)) (s.rX (BitVec.ofNat 5 km))) with pc := next } := by
  have hrn := rn_reg (c := ⟨L, s, p⟩) hr
  have he : progEffect ⟨L, s, p⟩ = .ok (effWd {} kd
      (binF37 as (s.rX (BitVec.ofNat 5 kn)) (s.rX (BitVec.ofNat 5 km)))) := by
    rcases has with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    · unfold progEffect
      simp (config := { decide := true }) only [hpa, nUMULH, nSMULH, nUDIV, nSDIV, nMULW, nUDIVW,
        nSDIVW, nUMULL, hf, ht, hrn, regA, ProgOp.baseOf, ↓reduceIte, ProgOp.binNames, ProgOp.endsS,
        cMULW, cUDIVW, cSDIVW, ctx_src_reg hkn, ctx_src_reg hkm, ctx_src_reg32 hkn,
        ctx_src_reg32 hkm]
      simp only [bind, Except.bind, eff_wX_dest hkd]
      by_cases h : kd = 31 <;> simp (config := { decide := true }) [effWd, h, ProgOp.binOp,
        binF37, dp2Op, sized, trunc_false_setWidth] <;> rfl
  have hsk : p.isSkip = false := by
    rcases has with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Prog.isSkip, hpa]
  rw [progStep_eq hn hsk he (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]),
    wd_apply hkd]

/-- `op Rm, Rd` for a unary op of G37. -/
theorem progStep_un37 {as : As} {km kd : Nat} (has : as = .RBIT ∨ as = .REVW ∨ as = .REV16W)
    (hkm : km < 32) (hkd : kd < 32)
    (hn : L.nextAddr p.id = some next) (hpa : p.as = as) (hf : p.from_ = regA (REG_R0 + km))
    (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd) (unF37 as (s.rX (BitVec.ofNat 5 km))) with
      pc := next } := by
  have he : progEffect ⟨L, s, p⟩ = .ok (effWd {} kd (unF37 as (s.rX (BitVec.ofNat 5 km)))) := by
    rcases has with rfl | rfl | rfl <;>
    · unfold progEffect
      simp (config := { decide := true }) only [hpa, nRBIT, nREVW, nREV16W, hf, ht, regA,
        ProgOp.baseOf, ↓reduceIte, ProgOp.binNames, ProgOp.endsS, cREVW, cREV16W, ctx_x_r0 hkm]
      simp only [bind, Except.bind, eff_wX_dest hkd]
      simp [dp1Op, sized, unF37]
  have hsk : p.isSkip = false := by
    rcases has with rfl | rfl | rfl <;> simp [Prog.isSkip, hpa]
  rw [progStep_eq hn hsk he (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]),
    wd_apply hkd]

/-- `op Rm, Ra, Rn, Rd` for a multiply-add of G37: `Ra ± Rn · Rm`. -/
theorem progStep_madd37 {as : As} {ka km kn kd x : Nat}
    (has : as = .MADD ∨ as = .MSUB ∨ as = .MADDW ∨ as = .MSUBW)
    (hka : ka < 32) (hkm : km < 32) (hkn : kn < 32) (hkd : kd < 32)
    (hn : L.nextAddr p.id = some next) (hpa : p.as = as) (hf : p.from_ = regA (REG_R0 + km))
    (hr : p.reg = REG_R0 + ka) (hrest : p.rest = #[(x, regA (REG_R0 + kn))])
    (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd) (maddF37 as (s.rX (BitVec.ofNat 5 ka))
      (s.rX (BitVec.ofNat 5 kn)) (s.rX (BitVec.ofNat 5 km))) with pc := next } := by
  have hrest0 : (ProgCtx.mk L s p).rest 0 = .ok (regA (REG_R0 + kn)) := by
    simp [ProgCtx.rest, hrest]
    rfl
  have he : progEffect ⟨L, s, p⟩ = .ok (effWd {} kd (maddF37 as (s.rX (BitVec.ofNat 5 ka))
      (s.rX (BitVec.ofNat 5 kn)) (s.rX (BitVec.ofNat 5 km)))) := by
    rcases has with rfl | rfl | rfl | rfl <;>
    · unfold progEffect
      simp (config := { decide := true }) only [hpa, nMADD, nMSUB, nMADDW, nMSUBW, hf, hr, ht,
        hrest0, regA, ProgOp.baseOf, ↓reduceIte, ProgOp.binNames, ProgOp.endsS, cMADDW, cMSUBW,
        ctx_x_r0 hkm, ctx_x_r0 hka, ctx_x_r0 hkn]
      simp only [bind, Except.bind, ctx_x_r0 hkn, eff_wX_dest hkd]
      simp [dp3Op, sized, maddF37]
  have hsk : p.isSkip = false := by
    rcases has with rfl | rfl | rfl | rfl <;> simp [Prog.isSkip, hpa]
  rw [progStep_eq hn hsk he (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]),
    wd_apply hkd]

/-- `SBFX` of a bitfield auxint `lsb · 256 + width` (`width < 256`, the auxint below `2 ^ 63`). -/
theorem sbfx_ofNat {lsb width : Nat} (hw : width < 256) (hk : lsb * 256 + width < 2 ^ 63)
    (x : BitVec 64) :
    GoFV.SSA.Sem.Arm64.sbfx (Int64.ofNat (lsb * 256 + width)) x =
      GoFV.SSA.Sem.Arm64.sext width (x >>> lsb) := by
  have h : (Int64.ofNat (lsb * 256 + width)).toInt = ((lsb * 256 + width : Nat) : Int) := by
    rw [Int64.toInt_ofNat_of_lt hk]
  simp only [GoFV.SSA.Sem.Arm64.sbfx, GoFV.SSA.Sem.Arm64.bf, h, Int.toNat_natCast]
  congr 2 <;> omega

/-- `SBFX $lsb, Rn, $width, Rd` (the operands `sbfxOK` fixes; `0 ≤ width < 256`, the auxint
`lsb · 256 + width` below `2 ^ 63`): bits `lsb …` of `X kn`, `width` of them, sign-extended. -/
theorem progStep_sbfx37 {kn kd x : Nat} {lsb width : Int} (hkn : kn < 32) (hkd : kd < 32)
    (hw0 : 0 ≤ width) (hw : width < 256) (hlw : lsb.toNat * 256 + width.toNat < 2 ^ 63)
    (hn : L.nextAddr p.id = some next) (has : p.as = .SBFX) (hf : p.from_ = constA lsb)
    (hr : p.reg = REG_R0 + kn) (ht : p.to = regA (REG_R0 + kd))
    (hrest : p.rest = #[(x, constA width)]) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      (GoFV.SSA.Sem.Arm64.sext width.toNat (s.rX (BitVec.ofNat 5 kn) >>> lsb.toNat)) with
        pc := next } := by
  have hname : As.name .SBFX = "SBFX" := rfl
  have hrest0 : (ProgCtx.mk L s p).rest 0 = .ok (constA width) := by
    simp [ProgCtx.rest, hrest]
    rfl
  have hval : ProgOp.trunc true (GoFV.SSA.Sem.Arm64.sbfx
      (Int64.ofNat (lsb.toNat * 256 + width.toNat)) (ProgOp.trunc true (s.rX (BitVec.ofNat 5 kn)))) =
      GoFV.SSA.Sem.Arm64.sext width.toNat (s.rX (BitVec.ofNat 5 kn) >>> lsb.toNat) := by
    simp only [ProgOp.trunc, ↓reduceIte]
    exact sbfx_ofNat (by omega) hlw _
  have he : progEffect ⟨L, s, p⟩ = .ok (effWd {} kd
      (GoFV.SSA.Sem.Arm64.sext width.toNat (s.rX (BitVec.ofNat 5 kn) >>> lsb.toNat))) := by
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
      ProgOp.binNames, hrest0, hf, hr, ht, constA, regA, ctx_x_r0 hkn, ctx_x_r0 hkd]
    rw [← hval]
    exact eff_wX_dest hkd
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
    (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]), wd_apply hkd]

end Progs

/-! ## Values -/

section Vals

variable {ι : Blk → Option (BitVec 64)}

private theorem res_int37 {t : Ty} (ht : t ≠ .bool) (r : BitVec 64) :
    Arm64.res t r = .int .w64 r := by
  cases t <;> first | rfl | exact absurd rfl ht

private theorem low_le37 {c ca : Nat} {a b : BitVec 64} (h : a.setWidth ca = b.setWidth ca)
    (hc : c ≤ ca) : a.setWidth c = b.setWidth c := by
  have := congrArg (BitVec.setWidth c) h
  simpa only [BitVec.setWidth_setWidth_of_le _ hc] using this

private theorem fits_le37 {c : Nat} {x : Val} {r : BitVec 64} (hf : Fits c x)
    (hr : Arm64.reg x = some r) : c ≤ 64 := by
  cases x with
  | int w v => have : w.bits = c := hf; subst this; cases w <;> decide
  | bool b => have : c = 1 := hf; omega
  | ptr p => have : c = 64 := hf; omega
  | _ => cases hr

/-- The register of an argument of 64 bits is the machine word. -/
private theorem reg64 (hA : AddrAgree ι) {x : Val} {X a : BitVec 64} {cx : Nat} (hx : ValRel ι x X)
    (hfx : Fits cx x) (hcx : 64 ≤ cx) (hr : Arm64.reg x = some a) : a = X := by
  have h64 := fits_le37 hfx hr
  have : cx = 64 := by omega
  subst this
  simpa only [BitVec.setWidth_eq] using reg_low hA hx hfx hr

/-- The low word of an argument of at least 32 bits is the machine word's. -/
private theorem reg32_37 (hA : AddrAgree ι) {x : Val} {X : BitVec 64} {a : BitVec 32} {cx : Nat}
    (hx : ValRel ι x X) (hfx : Fits cx x) (hcx : 32 ≤ cx) (hr : Arm64.reg32 x = some a) :
    a = X.setWidth 32 := by
  unfold Arm64.reg32 at hr
  cases hr' : Arm64.reg x with
  | none => rw [hr'] at hr; cases hr
  | some b =>
    rw [hr'] at hr
    cases hr
    exact low_le37 (reg_low hA hx hfx hr') hcx

private theorem sw_mul37 {c : Nat} (hc : c ≤ 64) {a b A B : BitVec 64}
    (ha : a.setWidth c = A.setWidth c) (hb : b.setWidth c = B.setWidth c) :
    (a * b).setWidth c = (A * B).setWidth c := by
  rw [BitVec.setWidth_mul _ _ hc, BitVec.setWidth_mul _ _ hc, ha, hb]

private theorem sw_neg37 {c : Nat} (hc : c ≤ 64) {y Y : BitVec 64}
    (hy : y.setWidth c = Y.setWidth c) : (-y).setWidth c = (-Y).setWidth c := by
  rw [BitVec.neg_eq_neg_one_mul y, BitVec.neg_eq_neg_one_mul Y, BitVec.setWidth_mul _ _ hc,
    BitVec.setWidth_mul _ _ hc, hy]

/-- A register op of G37 on two arguments of at least `cw` bits (64 for `full37?`, 32 for
`w37?`): the machine's word (`binF37`). -/
theorem lo_bin37 (hA : AddrAgree ι) {op : Op} {t : Ty} {k : Int64} {aux : Option AuxRef}
    {as : As} {cw cx cy : Nat} {x y : Val} {X Y : BitVec 64}
    (hop : full37? op = some as ∧ cw = 64 ∨ w37? op = some as ∧ cw = 32) (hx : ValRel ι x X)
    (hy : ValRel ι y Y) (hfx : Fits cx x) (hfy : Fits cy y) (hcx : cw ≤ cx) (hcy : cw ≤ cy)
    (ht : t ≠ .bool) :
    Lo ι 64 (Arm64.evalPure op t k aux [x, y]) (binF37 as X Y) := by
  rcases hop with ⟨hop, rfl⟩ | ⟨hop, rfl⟩
  · rcases full37?_some hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · show Lo ι 64 (Arm64.op2 t _ [x, y]) _
      simp only [Arm64.op2]
      cases hrx : Arm64.reg x with
      | none => trivial
      | some a =>
        cases hry : Arm64.reg y with
        | none => trivial
        | some b =>
          rw [reg64 hA hx hfx hcx hrx, reg64 hA hy hfy hcy hry]
          show Lo ι 64 (Arm64.res t _) _
          rw [res_int37 ht]
          rfl
  · rcases w37?_some hop with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals first
      | (show Lo ι 64 (Arm64.op2w t _ [x, y]) _
         simp only [Arm64.op2w]
         cases hrx : Arm64.reg32 x with
         | none => trivial
         | some a =>
           cases hry : Arm64.reg32 y with
           | none => trivial
           | some b =>
             rw [reg32_37 hA hx hfx hcx hrx, reg32_37 hA hy hfy hcy hry]
             show Lo ι 64 (Arm64.res t _) _
             rw [res_int37 ht]
             rfl)
      | (show Lo ι 64 (Arm64.op2 t GoFV.SSA.Sem.Arm64.umull [x, y]) _
         simp only [Arm64.op2]
         cases hrx : Arm64.reg x with
         | none => trivial
         | some a =>
           cases hry : Arm64.reg y with
           | none => trivial
           | some b =>
             have ha : a.setWidth 32 = X.setWidth 32 := low_le37 (reg_low hA hx hfx hrx) hcx
             have hb : b.setWidth 32 = Y.setWidth 32 := low_le37 (reg_low hA hy hfy hry) hcy
             show Lo ι 64 (Arm64.res t _) _
             rw [res_int37 ht]
             show (GoFV.SSA.Sem.Arm64.umull a b).setWidth 64 = (binF37 .UMULL X Y).setWidth 64
             simp only [binF37, GoFV.SSA.Sem.Arm64.umull, ha, hb])

/-- A unary op of G37 on an argument of at least `ca` bits: the machine's word (`unF37`). -/
theorem lo_un37 (hA : AddrAgree ι) {op : Op} {t : Ty} {k : Int64} {aux : Option AuxRef}
    {as : As} {ca cx : Nat} {x : Val} {X : BitVec 64} (hop : un37? op = some (as, ca))
    (hx : ValRel ι x X) (hfx : Fits cx x) (hcx : ca ≤ cx) (ht : t ≠ .bool) :
    Lo ι 64 (Arm64.evalPure op t k aux [x]) (unF37 as X) := by
  rcases un37?_some hop with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · show Lo ι 64 (Arm64.op1 t _ [x]) _
    simp only [Arm64.op1]
    cases hrx : Arm64.reg x with
    | none => trivial
    | some a =>
      rw [reg64 hA hx hfx hcx hrx]
      show Lo ι 64 (Arm64.res t _) _
      rw [res_int37 ht]
      rfl
  all_goals
    show Lo ι 64 (Arm64.op1w t _ [x]) _
    simp only [Arm64.op1w]
    cases hrx : Arm64.reg32 x with
    | none => trivial
    | some a =>
      rw [reg32_37 hA hx hfx hcx hrx]
      show Lo ι 64 (Arm64.res t _) _
      rw [res_int37 ht]
      rfl

/-- `MADD`/`MSUB a x y` of arguments of classes at least the result's `c`: `Ra ± Rn · Rm` on the
low `c` bits, with `ADD`'s pointer case; `MADDW`/`MSUBW` of arguments of at least 32 bits: the
machine's word. -/
theorem lo_madd37 (hA : AddrAgree ι) {op : Op} {t : Ty} {k : Int64} {aux : Option AuxRef}
    {as : As} {w : Bool} {c ca cx cy : Nat} {a x y : Val} {A X Y : BitVec 64}
    (hop : madd37? op = some (as, w)) (ha : ValRel ι a A) (hx : ValRel ι x X) (hy : ValRel ι y Y)
    (hfa : Fits ca a) (hfx : Fits cx x) (hfy : Fits cy y) (hc : c ≤ 64)
    (hw1 : w = true → 32 ≤ ca ∧ 32 ≤ cx ∧ 32 ≤ cy) (hw0 : w = false → c ≤ ca ∧ c ≤ cx ∧ c ≤ cy)
    (ht : t ≠ .bool) :
    Lo ι c (Arm64.evalPure op t k aux [a, x, y]) (maddF37 as A Y X) := by
  rcases madd37?_some hop with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩
  · obtain ⟨hca, hcx, hcy⟩ := hw0 rfl
    show Lo ι c (Arm64.madd t false [a, x, y]) _
    simp only [Arm64.madd, Bool.false_eq_true, ↓reduceIte]
    cases hrx : Arm64.reg x with
    | none => trivial
    | some u =>
      cases hry : Arm64.reg y with
      | none => trivial
      | some v =>
        have hu := low_le37 (reg_low hA hx hfx hrx) hcx
        have hv := low_le37 (reg_low hA hy hfy hry) hcy
        refine lo_addP hA ha hfa hc hca ht (by rw [sw_mul37 hc hu hv, BitVec.mul_comm]) ?_
        rcases Nat.lt_or_ge c 64 with h | h
        · exact .inl h
        · right
          rw [reg64 hA hx hfx (by omega) hrx, reg64 hA hy hfy (by omega) hry, BitVec.mul_comm]
  · obtain ⟨hca, hcx, hcy⟩ := hw0 rfl
    show Lo ι c (Arm64.madd t true [a, x, y]) _
    simp only [Arm64.madd, ↓reduceIte]
    cases hrx : Arm64.reg x with
    | none => trivial
    | some u =>
      cases hry : Arm64.reg y with
      | none => trivial
      | some v =>
        have hu := low_le37 (reg_low hA hx hfx hrx) hcx
        have hv := low_le37 (reg_low hA hy hfy hry) hcy
        show Lo ι c (Arm64.addP t a (-(u * v))) (A - Y * X)
        rw [BitVec.sub_eq_add_neg]
        refine lo_addP hA ha hfa hc hca ht
          (sw_neg37 hc (by rw [sw_mul37 hc hu hv, BitVec.mul_comm])) ?_
        rcases Nat.lt_or_ge c 64 with h | h
        · exact .inl h
        · right
          rw [reg64 hA hx hfx (by omega) hrx, reg64 hA hy hfy (by omega) hry, BitVec.mul_comm]
  all_goals
    obtain ⟨hca, hcx, hcy⟩ := hw1 rfl
    refine Lo.mono ?_ hc
    show Lo ι 64 (Arm64.op3w t _ [a, x, y]) _
    simp only [Arm64.op3w]
    cases hra : Arm64.reg32 a with
    | none => trivial
    | some a' =>
      cases hrx : Arm64.reg32 x with
      | none => trivial
      | some x' =>
        cases hry : Arm64.reg32 y with
        | none => trivial
        | some y' =>
          rw [reg32_37 hA ha hfa hca hra, reg32_37 hA hx hfx hcx hrx, reg32_37 hA hy hfy hcy hry]
          show Lo ι 64 (Arm64.res t _) _
          rw [res_int37 ht]
          show _ = (maddF37 _ A Y X).setWidth 64
          simp only [maddF37, BitVec.mul_comm (Y.setWidth 32)]

/-- `SBFX [k]` (`k = lsb · 256 + width ≥ 0`, `0 < width`, `lsb + width ≤` the argument's class):
the machine's `SBFX $lsb, Rn, $width, Rd` (`progStep_sbfx37`) on the whole word. -/
theorem lo_sbfx37 (hA : AddrAgree ι) {t : Ty} {k : Int64} {aux : Option AuxRef} {x : Val}
    {X : BitVec 64} {ca : Nat} (hx : ValRel ι x X) (hfx : Fits ca x) (hk : 0 ≤ k.toInt)
    (hw0 : 0 < k.toInt % 256) (hlw : k.toInt / 256 + k.toInt % 256 ≤ ca) (ht : t ≠ .bool) :
    Lo ι 64 (Arm64.evalPure .ARM64SBFX t k aux [x])
      (GoFV.SSA.Sem.Arm64.sext (k.toInt % 256).toNat (X >>> (k.toInt / 256).toNat)) := by
  show Lo ι 64 (Arm64.op1 t (GoFV.SSA.Sem.Arm64.sbfx k) [x]) _
  simp only [Arm64.op1]
  cases hrx : Arm64.reg x with
  | none => trivial
  | some a =>
    show Lo ι 64 (Arm64.res t _) _
    rw [res_int37 ht]
    show (GoFV.SSA.Sem.Arm64.sbfx k a).setWidth 64 = _
    rw [BitVec.setWidth_eq, BitVec.setWidth_eq]
    have hlow := reg_low hA hx hfx hrx
    have hca64 := fits_le37 hfx hrx
    have h1 : k.toInt.toNat / 256 = (k.toInt / 256).toNat := by omega
    have h2 : k.toInt.toNat % 256 = (k.toInt % 256).toNat := by omega
    simp only [GoFV.SSA.Sem.Arm64.sbfx, GoFV.SSA.Sem.Arm64.bf, h1, h2]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    have hw : 0 < (k.toInt % 256).toNat ∧ (k.toInt % 256).toNat ≤ 64 := by omega
    rw [sext_bit _ hw _ i hi, sext_bit _ hw _ i hi]
    have hbit : ∀ j, j < (k.toInt % 256).toNat →
        (a >>> (k.toInt / 256).toNat).getLsbD j = (X >>> (k.toInt / 256).toNat).getLsbD j := by
      intro j hj
      simp only [BitVec.getLsbD_ushiftRight]
      have := congrArg (fun v => v.getLsbD ((k.toInt / 256).toNat + j)) hlow
      simpa only [BitVec.getLsbD_setWidth, show (k.toInt / 256).toNat + j < ca by omega,
        decide_true, Bool.true_and] using this
    split
    · exact hbit i (by omega)
    · exact hbit _ (by omega)

end Vals

/-! ## The cases -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- `op Rm, Rn, Rd` for a register op of G37. -/
theorem g37_bin (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {cw cx cy c : Nat} {rn rm rd : Int}
    (hop : full37? v.op = some as ∧ cw = 64 ∨ w37? v.op = some as ∧ cw = 32)
    (hsz : v.args.size = 2) (hao : argObj lc v 0 = .ok (cx, rn)) (hbo : argObj lc v 1 = .ok (cy, rm))
    (hro : resObj lc v = .ok (c, rd)) (h8 : 8 ≤ c) (hcx : cw ≤ cx) (hcy : cw ≤ cy)
    (hvs : OneAt2 psA j (.ofShape { as, from_ := regA rm, reg := rn, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have halu := aluOp37_bin hop
  have hnp : v.op ≠ .Phi := (aluOp37_ne halu).1
  have has : as = .UMULH ∨ as = .SMULH ∨ as = .UDIV ∨ as = .SDIV ∨ as = .MULW ∨ as = .UDIVW ∨
      as = .SDIVW ∨ as = .UMULL := by
    rcases hop with ⟨h, -⟩ | ⟨h, -⟩
    · rcases full37?_some h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
    · rcases w37?_some h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hbo
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨km, hkm, rfl, hkkm⟩ := objOf?_some hor1
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨y, hy, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkkm
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu37 hl htemp halu hs
  rw [arr2 hsz ha0 ha1] at hargv
  obtain rfl := mapM_res_two hargv hx hy
  rw [write_reg hvh hcv]
  have ht := cls_ne_bool hcv h8
  refine (op_reg2 (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_retypeL_lo hA hcv ht ((lo_bin37 hA hop hxv hyv hxf hyf hcx hcy ht).mono (cls_le hcv)))
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0' hok => ?_)).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨hpa, hf, hr, ht', -⟩ := Shape.ok_eq hok
  rw [progStep_bin37 has hkn hkm hkd (nextAddr_pcAt F.nodup hk0') hpa hf hr ht', wX_pc]
  rfl

/-- `op Rm, Rd` for a unary op of G37. -/
theorem g37_un (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {ca cx c : Nat} {rm rd : Int} (hop : un37? v.op = some (as, ca))
    (hsz : v.args.size = 1) (hao : argObj lc v 0 = .ok (cx, rm)) (hro : resObj lc v = .ok (c, rd))
    (h8 : 8 ≤ c) (hcx : ca ≤ cx)
    (hvs : OneAt2 psA j (.ofShape { as, from_ := regA rm, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have halu := aluOp37_un hop
  have hnp : v.op ≠ .Phi := (aluOp37_ne halu).1
  have has : as = .RBIT ∨ as = .REVW ∨ as = .REV16W := by
    rcases un37?_some hop with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> simp
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨km, hkm, rfl, hkkm⟩ := objOf?_some hor0
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkm
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu37 hl htemp halu hs
  rw [arr1 hsz ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  rw [write_reg hvh hcv]
  have ht := cls_ne_bool hcv h8
  refine (op_reg2 (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_retypeL_lo hA hcv ht ((lo_un37 hA hop hxv hxf hcx ht).mono (cls_le hcv)))
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0' hok => ?_)).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨hpa, hf, -, ht', -⟩ := Shape.ok_eq hok
  rw [progStep_un37 has hkm hkd (nextAddr_pcAt F.nodup hk0') hpa hf ht', wX_pc]
  rfl

/-- `op Rm, Ra, Rn, Rd` for a multiply-add of G37. -/
theorem g37_madd (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {w : Bool} {ca cx cy c : Nat} {ra rm rn rd : Int}
    (hop : madd37? v.op = some (as, w)) (hsz : v.args.size = 3)
    (hao : argObj lc v 0 = .ok (ca, ra)) (hxo : argObj lc v 1 = .ok (cx, rm))
    (hyo : argObj lc v 2 = .ok (cy, rn)) (hro : resObj lc v = .ok (c, rd)) (h8 : 8 ≤ c)
    (hw1 : w = true → 32 ≤ ca ∧ 32 ≤ cx ∧ 32 ≤ cy) (hw0 : w = false → c ≤ ca ∧ c ≤ cx ∧ c ≤ cy)
    (hvs : OneAt2 psA j ⟨maddOK as ra rm rn rd, as.name⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have halu := aluOp37_madd hop
  have hnp : v.op ≠ .Phi := (aluOp37_ne halu).1
  have has : as = .MADD ∨ as = .MSUB ∨ as = .MADDW ∨ as = .MSUBW := by
    rcases madd37?_some hop with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> simp
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hxo
  obtain ⟨a2, r2, ha2, hah2, hor2, hca2⟩ := argObj_spec hyo
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨ka, hka, rfl, hkka⟩ := objOf?_some hor0
  obtain ⟨km, hkm, rfl, hkkm⟩ := objOf?_some hor1
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor2
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨a, ha, hav, haf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkka
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkkm
  obtain ⟨y, hy, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah2 hca2 (kread_arg hR hnp ha2 hah2 hca2) hkkn
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu37 hl htemp halu hs
  rw [arr3 hsz ha0 ha1 ha2] at hargv
  obtain rfl := mapM_res_three hargv ha hx hy
  rw [write_reg hvh hcv]
  have ht := cls_ne_bool hcv h8
  refine (op_reg2 (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_retypeL_lo hA hcv ht (lo_madd37 hA hop hav hxv hyv haf hxf hyf (cls_le hcv) hw1 hw0 ht))
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0' hok => ?_)).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨hpa, hf, hr, ht', -, -, xr, hrest⟩ := maddOK_spec hok
  rw [progStep_madd37 has hka hkm hkn hkd (nextAddr_pcAt F.nodup hk0') hpa hf hr hrest ht', wX_pc]
  rfl

/-- `SBFX $lsb, Rn, $width, Rd`. -/
theorem g37_sbfx (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {ca c : Nat} {rn rd : Int}
    (hop : v.op = .ARM64SBFX) (hsz1 : v.args.size = 1) (hk0 : 0 ≤ v.auxInt.toInt)
    (hk16 : v.auxInt.toInt < 2 ^ 16) (hao : argObj lc v 0 = .ok (ca, rn))
    (hro : resObj lc v = .ok (c, rd)) (h8 : 8 ≤ c) (hw0 : 0 < v.auxInt.toInt % 256)
    (hlw : v.auxInt.toInt / 256 + v.auxInt.toInt % 256 ≤ ca)
    (hvs : OneAt2 psA j
      ⟨sbfxOK (v.auxInt.toInt / 256) (v.auxInt.toInt % 256) rn rd, "SBFX"⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have halu : AluOp37 v.op := by unfold AluOp37; simp [hop]
  have hnp : v.op ≠ .Phi := (aluOp37_ne halu).1
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu37 hl htemp halu hs
  rw [arr1 hsz1 ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  rw [write_reg hvh hcv, hop]
  have ht := cls_ne_bool hcv h8
  refine (op_reg2 (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_retypeL_lo hA hcv ht ((lo_sbfx37 hA hxv hxf hk0 hw0 hlw ht).mono (cls_le hcv)))
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0' hok => ?_)).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨has, hf, hr, ht', -, -, xr, hrest⟩ := sbfxOK_spec hok
  rw [progStep_sbfx37 hkn hkd (by omega) (by omega) (by omega) (nextAddr_pcAt F.nodup hk0') has hf
    hr ht' hrest, wX_pc]
  rfl

end Cases

/-! ## The theorems -/

/-- One value of G37's kinds: `vk36_step`'s statement. -/
theorem vk37_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)}
    (hE : G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK37 lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s) (hL : UOKL m L)
    (hmem : ∀ x, (v.op = .ARM64MOVDnop ∨ v.op = .ARM64MOVDreg) → v.args[0]? = some x →
      ∃ r c, regHome? lc x = some r ∧ cls (lc.ty x) = some c ∧
        (r, c, lc.signOf lc.ctx.f.valueTab.size x) ∈ L)
    (hpre : G14Pre lc s v)
    (hcall : CallOK H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hcallz : CallOKZ H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hicall : ICallOK H E (Link.byId sym text az ez ps.toList) ret lc s s' v m)
    (hwb : WbOK H E g (Link.byId sym text az ez ps.toList) lc s v m) (hclo : CloOK E s v m)
    (hgetg : GetGOK E v) (hmeq : MemEqOK H E g (Link.byId sym text az ez ps.toList) lc s v m)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' ∧
      UOKL m' (uStep35 lc L v) := by
  have fin : AluOp37 v.op → ∀ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' →
      LocMatch E s' bid (i + 1) m' → CoreInv E.ι (StkAt E) (kStep lc K v).get s' →
      SlotInv lc s' →
      ∃ E' m', E.Extends E' ∧ G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
        PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
        LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' ∧
        UOKL m' (uStep35 lc L v) := fun halu m' h1 h2 h3 h4 => by
    refine ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩, ?_⟩
    rw [uStep35_alu37 halu]
    intro e he
    cases he
  cases hVK with
  | g36 _ _ _ _ _ hVK36 =>
    exact vk36_step hE F hhome hcf hv hVK36 hvs htemp hj hj' hreads hm hinv hL hmem hpre hcall
      hcallz hicall hwb hclo hgetg hmeq hs
  | bin hop hsz hao hbo hro h8 hcx hcy =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4⟩ := g37_bin (H := H) F hm hinv.core hinv.slots
      (kread_of_reads hreads) (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hbo
      hro h8 hcx hcy hvs htemp hs
    exact fin (aluOp37_bin hop) m' h1 h2 h3 h4
  | un hop hsz hao hro h8 hcx =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4⟩ := g37_un (H := H) F hm hinv.core hinv.slots
      (kread_of_reads hreads) (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hro
      h8 hcx hvs htemp hs
    exact fin (aluOp37_un hop) m' h1 h2 h3 h4
  | madd hop hsz hao hxo hyo hro h8 hw1 hw0 =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4⟩ := g37_madd (H := H) F hm hinv.core hinv.slots
      (kread_of_reads hreads) (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hxo
      hyo hro h8 hw1 hw0 hvs htemp hs
    exact fin (aluOp37_madd hop) m' h1 h2 h3 h4
  | sbfx hop hsz hk0 hk16 hao hro h8 hw0 hlw =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4⟩ := g37_sbfx (H := H) F hm hinv.core hinv.slots
      (kread_of_reads hreads) (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hk0 hk16
      hao hro h8 hw0 hlw hvs htemp hs
    exact fin (by unfold AluOp37; simp [hop]) m' h1 h2 h3 h4

/-- **G37, values.** `g36_value`'s statement over `checkG37`, carrying the upper-bit invariant
`UOKL` of G35's table `uL35` (started from `uIn35 lc bid`) from value `i` to value `i + 1`. -/
theorem g37_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG37 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hu : UOKL m (uL35 lc (uIn35 lc bid) blk i))
    (hpre : G14Pre lc s v)
    (hcall : CallOK H E g L lc s s' v m) (hcallz : CallOKZ H E g L lc s s' v m)
    (hicall : ICallOK H E L ret lc s s' v m)
    (hwb : WbOK H E g L lc s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hmeq : MemEqOK H E g L lc s v m) (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' ∧
      UOKL m' (uL35 lc (uIn35 lc bid) blk (i + 1)) := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    obtain ⟨E', m', hx, hE', h1, h2, h3, -⟩ := g33_value (checkG33_of_37 hl hc) hE hbid hb hi hv
      hen hm hinv (by rw [uL31_nl hl]; intro e he; cases he) hpre hcall hcallz hicall hwb hclo
      hgetg hmeq hs
    refine ⟨E', m', hx, hE', h1, h2, h3, ?_⟩
    rw [uL35_nl hl]
    intro e he
    cases he
  | true =>
  rw [uL35_succ hl hi hv]
  have hE0 := hE
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, hcf, hk, hlt, hnd, hblocks, -, hmovd, -⟩ :=
    checkG37_spec hl hc
  obtain ⟨b, j, js, e, next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk] at hkd
  obtain ⟨htemp, hVK⟩ := vkind37_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  rw [kAt_succ hi hv]
  exact vk37_step hE0 F hhome hcf hv hVK hvs htemp hj hj' hreads hm hinv hu
    (fun x hop hx => movdOK35_spec hmovd hbid hb hi hv hop hx)
    hpre hcall hcallz hicall hwb hclo hgetg hmeq hs

/-- A nil check of G37's kinds is G7's. -/
theorem vk37_nil {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK37 lc g v kd)
    (hop : v.op = .ARM64LoweredNilCheck) : VK7 lc g v kd := by
  cases h with
  | g36 _ _ _ _ _ h => exact vk36_nil h hop
  | bin h => exact absurd hop (aluOp37_ne (aluOp37_bin h)).2.2.2.1
  | un h => exact absurd hop (aluOp37_ne (aluOp37_un h)).2.2.2.1
  | madd h => exact absurd hop (aluOp37_ne (aluOp37_madd h)).2.2.2.1
  | sbfx h => rw [hop] at h; cases h

/-- **G37, nil panics.** `g36_nilPanic`'s statement over `checkG37`. -/
theorem g37_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG37 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  cases hl : lc.ctx.f.lowered with
  | false => exact g33_nilPanic (checkG33_of_37 hl hc) hE hbid hb hi hv hop hm hinv hs
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, -⟩ :=
    checkG37_spec hl hc
  obtain ⟨b, j, js, e', next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk] at hkd
  obtain ⟨-, hVK⟩ := vkind37_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases vk37_nil hVK hop with
  | g6 hne _ => exact absurd hop hne
  | nil _ hsz2 _ _ hao hma =>
    exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao hma hvs hs

/-- **G37, bounds panics.** `g36_boundsPanic`'s statement over `checkG37`, under `BoundsOK`. -/
theorem g37_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG37 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hbok : BoundsOK H g L ps.toList)
    (hs : stepLoc env lc s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    exact g33_boundsPanic (checkG33_of_37 hl hc) hE hbid hb hi hv hop hm hinv hbok hs
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, hsyms, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, hpb, -, -⟩ :=
    checkG37_spec hl hc
  obtain ⟨b, j, js, e', next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk] at hkd
  have hen : entryOp24 v.op = false := by
    rcases pbOp_cases hop with h | h | h | h <;> rw [h] <;> rfl
  obtain ⟨-, hVK⟩ := vkind37_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases hVK with
  | bin h => rw [(aluOp37_ne (aluOp37_bin h)).2.2.2.2] at hop; cases hop
  | un h => rw [(aluOp37_ne (aluOp37_un h)).2.2.2.2] at hop; cases hop
  | madd h => rw [(aluOp37_ne (aluOp37_madd h)).2.2.2.2] at hop; cases hop
  | sbfx h => rw [h] at hop; cases hop
  | g36 _ _ _ _ _ hVK36 =>
  cases hVK36 with
  | g33 _ _ _ hVK33 =>
    cases hVK33 with
    | g32 _ _ _ _ hVK32 =>
      cases hVK32 with
      | g28 _ _ _ _ _ hVK28 =>
        exact vk28_boundsPanic F hsyms hpb hrow hb hi hv hVK28 hvs hj hreads hop hm hinv hbok hs
      | bin h =>
        rw [(aluOp32_ne (aluOp32_bin h)).2.2.2.2] at hop; cases hop
      | binK h =>
        rw [(aluOp32_ne (aluOp32_binK h)).2.2.2.2] at hop; cases hop
      | un h =>
        rw [(aluOp32_ne (aluOp32_un h)).2.2.2.2] at hop; cases hop
      | csinc h => rw [h] at hop; cases hop
      | stlr h => rw [(stlr_ne (lc := c.cx.lc) h).2.2.2.2.1] at hop; cases hop
    | un h => rw [(aluOp33_ne (aluOp33_un h)).2.2.2.2] at hop; cases hop
    | ubfiz h => rw [h] at hop; cases hop
    | sra h => rw [h] at hop; cases hop
    | cmnw h => rw [h] at hop; cases hop
  | sh h => rw [(aluOp36_ne (aluOp36_sh h)).2.2.2.2] at hop; cases hop
  | shOp h => rw [(aluOp36_ne (aluOp36_shOp h)).2.2.2.2] at hop; cases hop
  | tst h => rw [h] at hop; cases hop

/-- **G37, terminators.** `g36_term`'s statement over `checkG37`, taking the upper-bit invariant of
G35's table at the block's end and giving it for the successor's start `uIn35 lc e.b`. -/
theorem g37_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG37 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s) (hpre : G1TermPre lc s blk)
    (hu : UOKL m (uL35 lc (uIn35 lc bid) blk blk.values.size))
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' ∧
      e.b ∈ lc.ctx.f.blocks.toList ∧ UOKL m' (uIn35 lc e.b) := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g33_term (checkG33_of_37 hl hc) hE hbid hb hm hinv hpre
      (by rw [uL31_nl hl]; intro e he; cases he) ht
    refine ⟨m', h1, h2, h3, h4, ?_⟩
    rw [uIn35_nl hl]
    intro e he
    cases he
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, hedges⟩ :=
    checkG37_spec hl hc
  obtain ⟨m', h1, h2, h3, h4, he, hx⟩ := termK_stepX hpcOf
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb hm hinv hpre ht
  refine ⟨m', h1, h2, h3, h4, fun x hxin => ?_⟩
  exact uok_of_x hx (hu x (uEdgesOK35_edge hedges hbid hb he x hxin))

end GoFV.Proof.Gen
