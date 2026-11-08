import GoFV.Proof.Gen.Progs
import GoFV.Gen.Check2

/-!
# The Progs of slice G2 under `runProg` (`docs/plans/proofs3.md` §4)

`progStep` of the Prog shapes slice G2 adds to G1's (`Progs.lean`): a spill and a reload at a
frame operand (`MOVD Rs, off(RSP)` / `MOVD off(RSP), Rd` with `NAME_AUTO` or `NAME_PARAM`, at
`SP + frameOff`), the address of a global (`MOVD $sym+off(SB), Rd`) and P0's static call
(`CALL sym(SB)`: `X30` the fall-through, the PC the symbol).
-/

namespace GoFV.Proof.Gen

open GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64 GoFV.Gen.Check

/-- The `SP` offset of a frame operand (`ProgCtx.mem`, semantics3 §5): `NAME_AUTO` at
`autosize + off - extrasize`, `NAME_PARAM` at `autosize + off + 8`. -/
def frameOff (L : Link) : AddrName → Int → Int
  | .AUTO, off => L.autosize + off - L.extrasize
  | .PARAM, off => L.autosize + off + 8
  | _, _ => 0

theorem slotA_eq {a : Addr} {nc : AddrName} {off : Int} (h : slotA a nc off = true) :
    a.type = .MEM ∧ a.reg = regSP ∧ a.index = 0 ∧ a.name = nc ∧ a.offset = off := by
  simp only [slotA, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-- A frame operand's address. -/
theorem ctx_mem_slot {c : ProgCtx} {a : Addr} {nc : AddrName} {off : Int}
    (h : slotA a nc off = true) (hnc : nc = .AUTO ∨ nc = .PARAM) :
    c.mem a = .ok (c.s.sp + BitVec.ofInt 64 (frameOff c.L nc off), none) := by
  obtain ⟨h1, -, -, h4, h5⟩ := slotA_eq h
  rcases hnc with rfl | rfl <;>
    simp [ProgCtx.mem, h1, h4, h5, frameOff] <;> rfl

variable {L : Link} {p : Prog} {s : MState} {next : BitVec 64}

/-- A spill: `MOVD Rs, off(RSP)` at a frame operand outside the nil page. -/
theorem progStep_slotStore {ks : Nat} {nc : AddrName} {off : Int} (hks : ks < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .MOVD) (hf : p.from_ = regA (REG_R0 + ks))
    (ht : slotA p.to nc off = true) (hnc : nc = .AUTO ∨ nc = .PARAM)
    (hnil : nilPage (s.sp + BitVec.ofInt 64 (frameOff L nc off)) = false) :
    progStep L p s = .ok { s with
      mem := writeMem s.mem (s.sp + BitVec.ofInt 64 (frameOff L nc off)) 8
        (BitVec.ofNat (8 * 8) ((s.rX (BitVec.ofNat 5 ks)).toNat % 2 ^ (8 * 8))),
      pc := next } := by
  have hname : As.name .MOVD = "MOVD" := rfl
  obtain ⟨ht1, -, -, -, -⟩ := slotA_eq ht
  let a := s.sp + BitVec.ofInt 64 (frameOff L nc off)
  have hm : (ProgCtx.mk L s p).mem p.to = .ok (a, none) := ctx_mem_slot ht hnc
  have he : progEffect ⟨L, s, p⟩ =
      .ok { stores := [(a, 8, (s.rX (BitVec.ofNat 5 ks)).toNat % 2 ^ (8 * 8))] } := by
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, hf, ht1, regA, ProgOp.baseOf,
      ↓reduceIte, ProgOp.movMem, hm, ctx_x_r0 hks]
    rfl
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he (by simp [Eff.nilAccess?, List.find?, hnil, a])]
  rfl

/-- A reload: `MOVD off(RSP), Rd` from a frame operand outside the nil page. -/
theorem progStep_slotLoad {kd : Nat} {nc : AddrName} {off : Int} (hkd : kd < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .MOVD) (hf : slotA p.from_ nc off = true)
    (hnc : nc = .AUTO ∨ nc = .PARAM) (ht : p.to = regA (REG_R0 + kd))
    (hnil : nilPage (s.sp + BitVec.ofInt 64 (frameOff L nc off)) = false) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      ((readMem s.mem (s.sp + BitVec.ofInt 64 (frameOff L nc off)) 8).setWidth 64) with
        pc := next } := by
  have hname : As.name .MOVD = "MOVD" := rfl
  obtain ⟨hf1, -, -, -, -⟩ := slotA_eq hf
  let a := s.sp + BitVec.ofInt 64 (frameOff L nc off)
  have hm : (ProgCtx.mk L s p).mem p.from_ = .ok (a, none) := ctx_mem_slot hf hnc
  have he : progEffect ⟨L, s, p⟩ =
      .ok (effWd { loads := [(a, 8)] } kd ((readMem s.mem a 8).setWidth 64)) := by
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, hf1, ht, regA, ProgOp.baseOf,
      ↓reduceIte, ProgOp.movMem, hm, Eff.ld, ProgCtx.load]
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

/-- The address of a global: `MOVD $sym+off(SB), Rd`. -/
theorem progStep_movAddr {kd : Nat} {y : Nat} {off : Int} (hkd : kd < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .MOVD) (hf1 : p.from_.type = .ADDR)
    (hf2 : p.from_.name = .EXTERN) (hf3 : p.from_.offset = off) (hf4 : p.from_.sym = some y)
    (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd) (L.sym y + BitVec.ofInt 64 off) with
      pc := next } := by
  have hname : As.name .MOVD = "MOVD" := rfl
  have hm : (ProgCtx.mk L s p).mem { p.from_ with type := .MEM } =
      .ok (L.sym y + BitVec.ofInt 64 off, none) := by
    simp [ProgCtx.mem, hf2, hf3, hf4]; rfl
  have he : progEffect ⟨L, s, p⟩ = .ok (effWd {} kd (L.sym y + BitVec.ofInt 64 off)) := by
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, hf1, ht, regA, ProgOp.baseOf,
      ↓reduceIte, ProgOp.movMem, hm]
    exact eff_wX_dest hkd
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
    (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]), wd_apply hkd]

/-- P0's static call `CALL sym(SB)`: `X30` the fall-through, the PC the symbol. -/
theorem progStep_callSym {y : Nat} (hn : L.nextAddr p.id = some next) (has : p.as = .CALL)
    (ht1 : p.to.type = .MEM) (ht2 : p.to.name = .EXTERN) (ht3 : p.to.offset = 0)
    (ht4 : p.to.sym = some y) :
    progStep L p s = .ok { s.wX 30 next with pc := L.sym y } := by
  have hname : As.name .CALL = "CALL" := rfl
  have hfall : (ProgCtx.mk L s p).fall = .ok next := by simp [ProgCtx.fall, hn]; rfl
  have hw : ({} : Eff).wX (REG_R0 + 30) next = .ok { x := [(30, next)] } :=
    eff_wX_r0 (k := 30) (by omega)
  have he : progEffect ⟨L, s, p⟩ = .ok { x := [(30, next)], pc := some (L.sym y) } := by
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, ht1, ht2, ht3, ht4, ProgOp.baseOf,
      ↓reduceIte, ProgOp.movMem, ProgOp.pairOp, ProgOp.rmw, ProgOp.bcond, ProgOp.startsS, hfall]
    simp only [pure, Except.pure, bind, Except.bind, hw]
    simp
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he rfl]
  rfl

end GoFV.Proof.Gen
