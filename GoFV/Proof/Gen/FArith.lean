import GoFV.Proof.Gen.G44
import GoFV.Gen.Check46

variable [GoFV.SSA.Sem.Addrs]

/-!
# Float arithmetic, conversions and compares (`docs/plans/proofs3.md` §4, float stage (b))

The lemmas a slice accepting arm64's scalar float ops needs, on top of G44's float moves
(`FMove.lean`, `G44.lean`): a float is `.int .w32`/`.int .w64` (its bits), related to its V
register by `FValRel` (`q.setWidth w.bits = x`).

**Machine steps** (symbolic registers `REG_F0 + k` = `V k`, `REG_R0 + k` = `X k`), in the form
`op_regV`/`op_reg2W` consume, for the operand layout genssa emits (`Gen/Arm64Value.lean`): binary
`from = arg1 (Rm), reg = arg0 (Rn), to`, unary `from = arg0, to`, compare `from = arg1, reg = arg0`
(zero form: `from` an `FCONST`), fused multiply-add `reg = arg0 (Ra), from = arg1 (Rm),
RestArgs = [arg2 (Rn)]`. Each table (`fp2Of`, `fp1Of`, `cvtfOf`, `fcvtzOf`, `fcmpOf`, `fp3Of`) maps
the SSA op to the operands of `Exec.lean`'s `fp2Op`/`fp1Op`/`fp3Op`/`fcmpOp`, and the opcode is
`opAsm op`: `progStep_fp2`, `progStep_fp1`, `progStep_cvtf` (`cvtfBits`), `progStep_fcvtz`
(`fcvtzBits`, `Rd = ZR` allowed), `progStep_fcmp`, `progStep_fcmp0`, `progStep_fp3`.

**Values** (`stepLoc` writes `(Arm64.evalPure op t k aux args).retypeL t`): `fvalRel_fp2`
(`FADD`/`FSUB`/`FMUL`/`FDIV`; `fvalRel_fsubdiv` without premise), `fvalRel_fp1`
(`FNEG`/`FABS`/`FSQRT`/`FCVTSD`/`FCVTDS`), `fvalRel_cvtf` (an X argument of class `≥ 8 ns`, as
`fvalRel_gpfp`), `lo_fcvtz` (an X result, `Lo ι 64` as `lo_fmovVX`), `flagsRel_fcmp`/
`flagsRel_fcmp0` (at `Ty.flags`), `fvalRel_fma` (`FMADD`/`FNMSUB` only).

**Where Phase 1 and the machine disagree.**

* `FADD`/`FMUL`: Phase 1 takes the operands in encoding order (`FOps.ordered`), the machine in
  `Rn, Rm` = `arg0, arg1` order, and `FPProcessNaNs` returns the first NaN of the highest kind.
  `FPAdd`/`FPMul` are commutative unless both operands are NaNs of the same kind (`add_comm_of`,
  `mul_comm_of`), so the results differ exactly when `FNaNSwap arg0 arg1`: both NaNs of one kind
  (both signalling or both quiet) and `arg1`'s encoding below `arg0`'s (distinct encodings of one
  kind stay distinct after quietening). `fvalRel_fp2` assumes `¬ FNaNSwap arg0 arg1` for them.
  Checked by `#eval`: `FADDS 0x7FC00001, 0x7FC00000` is `0x7FC00000` in Phase 1 and `0x7FC00001`
  on the machine; `FMULD 0xFFF8000000000000, 0x7FF8000000000000` (`−qNaN`, `+qNaN`) is
  `0x7FF8000000000000` and `0xFFF8000000000000`; `FADDD 0x7FF0000000000002, 0x7FF0000000000001`
  (two signalling NaNs) is `0x7FF8000000000001` and `0x7FF8000000000002`.
* Fused multiply-adds: Phase 1's `fmadd w negA negN [a, n, m]` is `FPMulAdd(±a, ±arg1, arg2)`
  (`negN` negates `arg1`), the machine's `fp3Op` on genssa's operands is
  `FPMulAdd(±arg0, ±arg2, arg1)` (`Rn = arg2` is the negated multiplicand). For `FMADD`/`FNMSUB`
  (no multiplicand negated) they differ exactly when the multiplicands are NaNs of the same kind
  with distinct encodings and the addend is not the NaN `FPProcessNaNs3` picks first (an addend
  sNaN, or a qNaN addend with qNaN multiplicands): `fvalRel_fma` assumes `¬ FSameNaN arg1 arg2`
  (`mulAdd_comm_of`). `#eval`: `FMADDD 1.0, 0x7FF8000000000001, 0x7FF8000000000002` is
  `0x7FF8000000000001` in Phase 1 and `0x7FF8000000000002` on the machine. For `FMSUB`/`FNMADD`
  they also differ in the NaN's sign whenever the picked NaN is a multiplicand (unless both
  multiplicands are the same NaN): Phase 1 returns `−arg1` or `arg2`, the machine `arg1` or
  `−arg2`. `#eval`: `FMSUBD 1.0, 0x7FF8000000000000, 2.0` is `0xFFF8000000000000` in Phase 1 and
  `0x7FF8000000000000` on the machine; `FNMADDS 1.0, 2.0, 0x7FC00000` is `0x7FC00000` and
  `0xFFC00000`. On non-NaN multiplicands they agree (the product's sign is `s1 != s2` either
  way), not proved here.
* Everything else here (`FSUB`, `FDIV`, `FNEG`, `FABS`, `FSQRT`, `FCVT`, `SCVTF`/`UCVTF`,
  `FCVTZS`/`FCVTZU`, `FCMP`) agrees on all inputs.
-/

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64
open GoFV.IEEE (Fmt RMode FPType)

namespace GoFV.Proof.Gen

/-! ## Opcode tables

The tables (`fp2Of`, `fp1Of`, `cvtfOf`, `fcvtzOf`, `fcmpOf`, `fp3Of`) are the validator's
(`GoFV/Gen/Check46.lean`); their inversions. -/

set_option hygiene false in
/-- Inverting an opcode table: one `split` per `if`, the `some` leaves give the row. -/
local macro "table_some" : tactic => `(tactic| (
  repeat' split at h
  all_goals (cases h <;> simp_all)))

theorem fp2Of_some {op : Op} {n : Nat} {ft : BitVec 2} {opc : BitVec 4}
    (h : fp2Of op = some (n, ft, opc)) :
    op = .ARM64FADDD ∧ n = 8 ∧ ft = 1 ∧ opc = 2 ∨ op = .ARM64FADDS ∧ n = 4 ∧ ft = 0 ∧ opc = 2 ∨
    op = .ARM64FSUBD ∧ n = 8 ∧ ft = 1 ∧ opc = 3 ∨ op = .ARM64FSUBS ∧ n = 4 ∧ ft = 0 ∧ opc = 3 ∨
    op = .ARM64FMULD ∧ n = 8 ∧ ft = 1 ∧ opc = 0 ∨ op = .ARM64FMULS ∧ n = 4 ∧ ft = 0 ∧ opc = 0 ∨
    op = .ARM64FDIVD ∧ n = 8 ∧ ft = 1 ∧ opc = 1 ∨ op = .ARM64FDIVS ∧ n = 4 ∧ ft = 0 ∧ opc = 1 := by
  unfold fp2Of at h
  table_some

theorem fp1Of_some {op : Op} {ns nd : Nat} {ft : BitVec 2} {opc : BitVec 6}
    (h : fp1Of op = some (ns, nd, ft, opc)) :
    op = .ARM64FNEGD ∧ ns = 8 ∧ nd = 8 ∧ ft = 1 ∧ opc = 2 ∨
    op = .ARM64FNEGS ∧ ns = 4 ∧ nd = 4 ∧ ft = 0 ∧ opc = 2 ∨
    op = .ARM64FABSD ∧ ns = 8 ∧ nd = 8 ∧ ft = 1 ∧ opc = 1 ∨
    op = .ARM64FABSS ∧ ns = 4 ∧ nd = 4 ∧ ft = 0 ∧ opc = 1 ∨
    op = .ARM64FSQRTD ∧ ns = 8 ∧ nd = 8 ∧ ft = 1 ∧ opc = 3 ∨
    op = .ARM64FSQRTS ∧ ns = 4 ∧ nd = 4 ∧ ft = 0 ∧ opc = 3 ∨
    op = .ARM64FCVTSD ∧ ns = 4 ∧ nd = 8 ∧ ft = 0 ∧ opc = 5 ∨
    op = .ARM64FCVTDS ∧ ns = 8 ∧ nd = 4 ∧ ft = 1 ∧ opc = 4 := by
  unfold fp1Of at h
  table_some

theorem cvtfOf_some {op : Op} {u : Bool} {ns nd : Nat} (h : cvtfOf op = some (u, ns, nd)) :
    op = .ARM64SCVTFWS ∧ u = false ∧ ns = 4 ∧ nd = 4 ∨
    op = .ARM64SCVTFWD ∧ u = false ∧ ns = 4 ∧ nd = 8 ∨
    op = .ARM64UCVTFWS ∧ u = true ∧ ns = 4 ∧ nd = 4 ∨
    op = .ARM64UCVTFWD ∧ u = true ∧ ns = 4 ∧ nd = 8 ∨
    op = .ARM64SCVTFS ∧ u = false ∧ ns = 8 ∧ nd = 4 ∨
    op = .ARM64SCVTFD ∧ u = false ∧ ns = 8 ∧ nd = 8 ∨
    op = .ARM64UCVTFS ∧ u = true ∧ ns = 8 ∧ nd = 4 ∨
    op = .ARM64UCVTFD ∧ u = true ∧ ns = 8 ∧ nd = 8 := by
  unfold cvtfOf at h
  table_some

theorem fcvtzOf_some {op : Op} {u : Bool} {ns nd : Nat} (h : fcvtzOf op = some (u, ns, nd)) :
    op = .ARM64FCVTZSSW ∧ u = false ∧ ns = 4 ∧ nd = 4 ∨
    op = .ARM64FCVTZSDW ∧ u = false ∧ ns = 8 ∧ nd = 4 ∨
    op = .ARM64FCVTZUSW ∧ u = true ∧ ns = 4 ∧ nd = 4 ∨
    op = .ARM64FCVTZUDW ∧ u = true ∧ ns = 8 ∧ nd = 4 ∨
    op = .ARM64FCVTZSS ∧ u = false ∧ ns = 4 ∧ nd = 8 ∨
    op = .ARM64FCVTZSD ∧ u = false ∧ ns = 8 ∧ nd = 8 ∨
    op = .ARM64FCVTZUS ∧ u = true ∧ ns = 4 ∧ nd = 8 ∨
    op = .ARM64FCVTZUD ∧ u = true ∧ ns = 8 ∧ nd = 8 := by
  unfold fcvtzOf at h
  table_some

theorem fcmpOf_some {op : Op} {n : Nat} {ft : BitVec 2} {z : Bool}
    (h : fcmpOf op = some (n, ft, z)) :
    op = .ARM64FCMPS ∧ n = 4 ∧ ft = 0 ∧ z = false ∨ op = .ARM64FCMPD ∧ n = 8 ∧ ft = 1 ∧ z = false ∨
    op = .ARM64FCMPS0 ∧ n = 4 ∧ ft = 0 ∧ z = true ∨
    op = .ARM64FCMPD0 ∧ n = 8 ∧ ft = 1 ∧ z = true := by
  unfold fcmpOf at h
  table_some

theorem fp3Of_some {op : Op} {n : Nat} {ft : BitVec 2} {o1 o0 : Bool}
    (h : fp3Of op = some (n, ft, o1, o0)) :
    op = .ARM64FMADDD ∧ n = 8 ∧ ft = 1 ∧ o1 = false ∧ o0 = false ∨
    op = .ARM64FMADDS ∧ n = 4 ∧ ft = 0 ∧ o1 = false ∧ o0 = false ∨
    op = .ARM64FMSUBD ∧ n = 8 ∧ ft = 1 ∧ o1 = false ∧ o0 = true ∨
    op = .ARM64FMSUBS ∧ n = 4 ∧ ft = 0 ∧ o1 = false ∧ o0 = true ∨
    op = .ARM64FNMADDD ∧ n = 8 ∧ ft = 1 ∧ o1 = true ∧ o0 = false ∨
    op = .ARM64FNMADDS ∧ n = 4 ∧ ft = 0 ∧ o1 = true ∧ o0 = false ∨
    op = .ARM64FNMSUBD ∧ n = 8 ∧ ft = 1 ∧ o1 = true ∧ o0 = true ∨
    op = .ARM64FNMSUBS ∧ n = 4 ∧ ft = 0 ∧ o1 = true ∧ o0 = true := by
  unfold fp3Of at h
  table_some

/-! ## Machine bits of the conversions -/

/-- `SCVTF`/`UCVTF` of the low `8 ns` bits of `X` to a float of `nd` bytes, zero-extended to the
V register. -/
def cvtfBits (u : Bool) (ns nd : Nat) (X : BitVec 64) : BitVec 128 :=
  if nd = 4 then (GoFV.IEEE.fromFixed Fmt.b32 (8 * ns) (X.setWidth (8 * ns)) u .rne).setWidth 128
  else (GoFV.IEEE.fromFixed Fmt.b64 (8 * ns) (X.setWidth (8 * ns)) u .rne).setWidth 128

/-- `FCVTZS`/`FCVTZU` of the float of `ns` bytes in `q` to an integer of `nd` bytes, rounding toward
zero and saturating, zero-extended to the X register. -/
def fcvtzBits (u : Bool) (ns nd : Nat) (q : BitVec 128) : BitVec 64 :=
  if ns = 4 then (GoFV.IEEE.toFixed Fmt.b32 (q.setWidth 32) u (8 * nd) .rz).setWidth 64
  else (GoFV.IEEE.toFixed Fmt.b64 (q.setWidth 64) u (8 * nd) .rz).setWidth 64

/-! ## Machine steps -/

theorem rn_f0 {c : ProgCtx} {kn : Nat} (hr : c.p.reg = REG_F0 + kn) : c.rn = REG_F0 + kn := by
  have h : (REG_F0 + (kn : Int) != 0) = true := by
    show ((8224 : Int) + kn != 0) = true
    simp; omega
  simp only [ProgCtx.rn, hr, h, ↓reduceIte]

variable {L : Link} {p : Prog} {s : MState} {next : BitVec 64}

set_option hygiene false in
/-- `progEffect` of a Prog with opcode `p.as = opAsm op` named `nm`, unfolded and evaluated
definitionally (`dsimp`) down to its register reads and writes. Rewriting the opcode name first
keeps `simp` off `progEffect`'s string `match`es; `dsimp` also evaluates the conversions' width
`if w then 32 else 64`, a type index. -/
local macro "name_eff " nm:str : tactic => `(tactic| (
  have hname : p.as.name = $nm := by rw [has]; rfl
  unfold progEffect
  dsimp only
  rw [hname]
  dsimp (config := { decide := true }) only [ProgOp.baseOf, ↓reduceIte, ProgOp.movMem,
    ProgOp.pairOp, ProgOp.rmw]))

/-- `FADD`/`FSUB`/`FMUL`/`FDIV` `Fm, Fn, Fd` (`fp2Of`): `fp2Op` of `V kn` and `V km`. -/
theorem progStep_fp2 {op : Op} {n : Nat} {ft : BitVec 2} {opc : BitVec 4} {kn km kd : Nat}
    (hkn : kn < 32) (hkm : km < 32) (hkd : kd < 32) (hop : fp2Of op = some (n, ft, opc))
    (hn : L.nextAddr p.id = some next) (has : p.as = opAsm op)
    (hf : p.from_ = regA (REG_F0 + km)) (hr : p.reg = REG_F0 + kn)
    (ht : p.to = regA (REG_F0 + kd)) :
    progStep L p s = .ok { s.wV (BitVec.ofNat 5 kd)
      (fp2Op ft opc (s.v (BitVec.ofNat 5 kn)) (s.v (BitVec.ofNat 5 km))) with pc := next } := by
  have hrn := rn_f0 (c := ⟨L, s, p⟩) hr
  have hsk : p.isSkip = false := by
    rcases fp2Of_some hop with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
      ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> (unfold Prog.isSkip; rw [has]; rfl)
  have he : progEffect ⟨L, s, p⟩ = .ok { v := [(kd,
      fp2Op ft opc (s.v (BitVec.ofNat 5 kn)) (s.v (BitVec.ofNat 5 km)))] } := by
    rcases fp2Of_some hop with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ <;>
    · first
        | name_eff "FADDD" | name_eff "FADDS" | name_eff "FSUBD" | name_eff "FSUBS"
        | name_eff "FMULD" | name_eff "FMULS" | name_eff "FDIVD" | name_eff "FDIVS"
      simp only [hrn, hf, ht, regA, ctx_v_f0 hkn, ctx_v_f0 hkm, eff_wV_f0 hkd]
      rfl
  rw [progStep_eq hn hsk he rfl, effV_apply]

/-- `FNEG`/`FABS`/`FSQRT`/`FCVTSD`/`FCVTDS` `Fn, Fd` (`fp1Of`): `fp1Op` of `V ka`. -/
theorem progStep_fp1 {op : Op} {ns nd : Nat} {ft : BitVec 2} {opc : BitVec 6} {ka kd : Nat}
    (hka : ka < 32) (hkd : kd < 32) (hop : fp1Of op = some (ns, nd, ft, opc))
    (hn : L.nextAddr p.id = some next) (has : p.as = opAsm op)
    (hf : p.from_ = regA (REG_F0 + ka)) (ht : p.to = regA (REG_F0 + kd)) :
    progStep L p s = .ok { s.wV (BitVec.ofNat 5 kd) (fp1Op ft opc (s.v (BitVec.ofNat 5 ka))) with
      pc := next } := by
  have hsk : p.isSkip = false := by
    rcases fp1Of_some hop with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
      ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> (unfold Prog.isSkip; rw [has]; rfl)
  have he : progEffect ⟨L, s, p⟩ = .ok { v := [(kd, fp1Op ft opc (s.v (BitVec.ofNat 5 ka)))] } := by
    rcases fp1Of_some hop with ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ <;>
    · first
        | name_eff "FNEGD" | name_eff "FNEGS" | name_eff "FABSD" | name_eff "FABSS"
        | name_eff "FSQRTD" | name_eff "FSQRTS" | name_eff "FCVTSD" | name_eff "FCVTDS"
      simp only [hf, ht, regA, ctx_v_f0 hka, eff_wV_f0 hkd]
      rfl
  rw [progStep_eq hn hsk he rfl, effV_apply]

/-- `SCVTF`/`UCVTF` `Rn, Fd` (`cvtfOf`): `cvtfBits` of `X ka`. -/
theorem progStep_cvtf {op : Op} {u : Bool} {ns nd ka kd : Nat} (hka : ka < 32) (hkd : kd < 32)
    (hop : cvtfOf op = some (u, ns, nd)) (hn : L.nextAddr p.id = some next)
    (has : p.as = opAsm op) (hf : p.from_ = regA (REG_R0 + ka))
    (ht : p.to = regA (REG_F0 + kd)) :
    progStep L p s = .ok { s.wV (BitVec.ofNat 5 kd)
      (cvtfBits u ns nd (s.rX (BitVec.ofNat 5 ka))) with pc := next } := by
  have hsk : p.isSkip = false := by
    rcases cvtfOf_some hop with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
      ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> (unfold Prog.isSkip; rw [has]; rfl)
  have he : progEffect ⟨L, s, p⟩ =
      .ok { v := [(kd, cvtfBits u ns nd (s.rX (BitVec.ofNat 5 ka)))] } := by
    rcases cvtfOf_some hop with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ <;>
    · first
        | name_eff "SCVTFWS" | name_eff "SCVTFWD" | name_eff "UCVTFWS" | name_eff "UCVTFWD"
        | name_eff "SCVTFS" | name_eff "SCVTFD" | name_eff "UCVTFS" | name_eff "UCVTFD"
      simp only [hf, ht, regA, ctx_x_r0 hka, eff_wV_f0 hkd]
      rfl
  rw [progStep_eq hn hsk he rfl, effV_apply]

/-- `FCVTZS`/`FCVTZU` `Fn, Rd` (`fcvtzOf`): `fcvtzBits` of `V ka` (`kd = 31`: `ZR`, as
`progStep_fmovVX`). -/
theorem progStep_fcvtz {op : Op} {u : Bool} {ns nd ka kd : Nat} (hka : ka < 32) (hkd : kd < 32)
    (hop : fcvtzOf op = some (u, ns, nd)) (hn : L.nextAddr p.id = some next)
    (has : p.as = opAsm op) (hf : p.from_ = regA (REG_F0 + ka))
    (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      (fcvtzBits u ns nd (s.v (BitVec.ofNat 5 ka))) with pc := next } := by
  have hsk : p.isSkip = false := by
    rcases fcvtzOf_some hop with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
      ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> (unfold Prog.isSkip; rw [has]; rfl)
  have he : progEffect ⟨L, s, p⟩ =
      .ok (effWd {} kd (fcvtzBits u ns nd (s.v (BitVec.ofNat 5 ka)))) := by
    rcases fcvtzOf_some hop with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
    · first
        | name_eff "FCVTZSSW" | name_eff "FCVTZSDW" | name_eff "FCVTZUSW" | name_eff "FCVTZUDW"
        | name_eff "FCVTZSS" | name_eff "FCVTZSD" | name_eff "FCVTZUS" | name_eff "FCVTZUD"
      simp only [hf, ht, regA, ctx_v_f0 hka, eff_wX_dest hkd]
      rfl
  rw [progStep_eq hn hsk he (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]),
    wd_apply hkd]

/-- `FCMPS`/`FCMPD` `Fm, Fn` (`fcmpOf`, register form): the flags of comparing `V kn` with
`V km`. -/
theorem progStep_fcmp {op : Op} {n : Nat} {ft : BitVec 2} {kn km : Nat} (hkn : kn < 32)
    (hkm : km < 32) (hop : fcmpOf op = some (n, ft, false)) (hn : L.nextAddr p.id = some next)
    (has : p.as = opAsm op) (hf : p.from_ = regA (REG_F0 + km)) (hr : p.reg = REG_F0 + kn) :
    progStep L p s = .ok { s with
      nzcv := fcmpOp ft (s.v (BitVec.ofNat 5 kn)) (s.v (BitVec.ofNat 5 km)), pc := next } := by
  have hsk : p.isSkip = false := by
    rcases fcmpOf_some hop with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩
    · unfold Prog.isSkip; rw [has]; rfl
    · unfold Prog.isSkip; rw [has]; rfl
    · cases h
    · cases h
  have he : progEffect ⟨L, s, p⟩ =
      .ok { flags := some (fcmpOp ft (s.v (BitVec.ofNat 5 kn)) (s.v (BitVec.ofNat 5 km))) } := by
    rcases fcmpOf_some hop with ⟨rfl, rfl, rfl, -⟩ | ⟨rfl, rfl, rfl, -⟩ | ⟨-, -, -, h⟩ |
      ⟨-, -, -, h⟩
    rotate_left 2
    · cases h
    · cases h
    all_goals
      first | name_eff "FCMPS" | name_eff "FCMPD"
      simp only [hf, hr, regA, ctx_v_f0 hkn, ctx_v_f0 hkm]
      rfl
  rw [progStep_eq hn hsk he rfl]
  rfl

/-- `FCMPS`/`FCMPD` `$0.0, Fn` (`fcmpOf`, zero form; `from` an `FCONST`): the flags of comparing
`V kn` with `0`. -/
theorem progStep_fcmp0 {op : Op} {n : Nat} {ft : BitVec 2} {kn : Nat} (hkn : kn < 32)
    (hop : fcmpOf op = some (n, ft, true)) (hn : L.nextAddr p.id = some next)
    (has : p.as = opAsm op) (hf : p.from_.type = .FCONST) (hr : p.reg = REG_F0 + kn) :
    progStep L p s = .ok { s with nzcv := fcmpOp ft (s.v (BitVec.ofNat 5 kn)) 0, pc := next } := by
  have hsk : p.isSkip = false := by
    rcases fcmpOf_some hop with ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
    · cases h
    · cases h
    · unfold Prog.isSkip; rw [has]; rfl
    · unfold Prog.isSkip; rw [has]; rfl
  have he : progEffect ⟨L, s, p⟩ =
      .ok { flags := some (fcmpOp ft (s.v (BitVec.ofNat 5 kn)) 0) } := by
    rcases fcmpOf_some hop with ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ | ⟨rfl, rfl, rfl, -⟩ |
      ⟨rfl, rfl, rfl, -⟩
    · cases h
    · cases h
    all_goals
      first | name_eff "FCMPS" | name_eff "FCMPD"
      simp only [hf, hr, ctx_v_f0 hkn]
      rfl
  rw [progStep_eq hn hsk he rfl]
  rfl

/-- `FMADD`/`FMSUB`/`FNMADD`/`FNMSUB` `Fm, Fa, Fn, Fd` (`fp3Of`; genssa's operands: `reg` = `Ra`,
`from` = `Rm`, the `RestArgs` source = `Rn`): `fp3Op` of `V ka`, `V kn`, `V km`. -/
theorem progStep_fp3 {op : Op} {n : Nat} {ft : BitVec 2} {o1 o0 : Bool} {ka kn km kd x : Nat}
    (hka : ka < 32) (hkn : kn < 32) (hkm : km < 32) (hkd : kd < 32)
    (hop : fp3Of op = some (n, ft, o1, o0)) (hn : L.nextAddr p.id = some next)
    (has : p.as = opAsm op) (hr : p.reg = REG_F0 + ka) (hf : p.from_ = regA (REG_F0 + km))
    (hrest : p.rest = #[(x, regA (REG_F0 + kn))]) (ht : p.to = regA (REG_F0 + kd)) :
    progStep L p s = .ok { s.wV (BitVec.ofNat 5 kd) (fp3Op ft o1 o0 (s.v (BitVec.ofNat 5 ka))
      (s.v (BitVec.ofNat 5 kn)) (s.v (BitVec.ofNat 5 km))) with pc := next } := by
  have hsk : p.isSkip = false := by
    rcases fp3Of_some hop with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
      ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> (unfold Prog.isSkip; rw [has]; rfl)
  have hrest0 : (ProgCtx.mk L s p).rest 0 = .ok (regA (REG_F0 + kn)) := by
    simp only [ProgCtx.rest, hrest]
    rfl
  have he : progEffect ⟨L, s, p⟩ = .ok { v := [(kd, fp3Op ft o1 o0 (s.v (BitVec.ofNat 5 ka))
      (s.v (BitVec.ofNat 5 kn)) (s.v (BitVec.ofNat 5 km)))] } := by
    rcases fp3Of_some hop with ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ <;>
    · first
        | name_eff "FMADDD" | name_eff "FMADDS" | name_eff "FMSUBD" | name_eff "FMSUBS"
        | name_eff "FNMADDD" | name_eff "FNMADDS" | name_eff "FNMSUBD" | name_eff "FNMSUBS"
      simp only [hr, hf, hrest0, ht, regA, ctx_v_f0 hka, ctx_v_f0 hkm, eff_wV_f0 hkd]
      simp only [bind, Except.bind, pure, Except.pure, ctx_v_f0 hkn]
      rfl
  rw [progStep_eq hn hsk he rfl, effV_apply]

/-! ## The operand order of `FADD`/`FMUL` -/

/-- `a` and `b` are NaNs of the same kind (both signalling or both quiet). -/
def SameNaN (f : Fmt) (a b : GoFV.IEEE.Bits f) : Prop :=
  GoFV.IEEE.typeOf f a = .snan ∧ GoFV.IEEE.typeOf f b = .snan ∨
    GoFV.IEEE.typeOf f a = .qnan ∧ GoFV.IEEE.typeOf f b = .qnan

/-- `FPProcessNaNs` does not depend on the operand order unless both are NaNs of one kind. -/
private theorem processNaNs_comm {f : Fmt} {a b : GoFV.IEEE.Bits f} {t1 t2 : FPType}
    (h1 : GoFV.IEEE.typeOf f a = t1) (h2 : GoFV.IEEE.typeOf f b = t2) (h : ¬ SameNaN f a b) :
    GoFV.IEEE.processNaNs f t1 t2 a b = GoFV.IEEE.processNaNs f t2 t1 b a := by
  unfold SameNaN at h
  rw [h1, h2] at h
  cases t1 <;> cases t2 <;> simp_all [GoFV.IEEE.processNaNs]

private theorem addExact_comm (s1 : Bool) (m1 : Nat) (e1 : Int) (s2 : Bool) (m2 : Nat) (e2 : Int) :
    GoFV.IEEE.addExact s1 m1 e1 s2 m2 e2 = GoFV.IEEE.addExact s2 m2 e2 s1 m1 e1 := by
  unfold GoFV.IEEE.addExact
  dsimp only
  rw [Int.min_comm e2 e1, Int.add_comm]

/-- `FPAdd` is commutative unless both operands are NaNs of the same kind. -/
theorem add_comm_of {f : Fmt} {rm : RMode} {a b : GoFV.IEEE.Bits f} (h : ¬ SameNaN f a b) :
    GoFV.IEEE.add f rm a b = GoFV.IEEE.add f rm b a := by
  have hp := processNaNs_comm (f := f) (a := a) (b := b) rfl rfl h
  unfold GoFV.IEEE.typeOf at hp
  unfold GoFV.IEEE.add
  rcases hu1 : GoFV.IEEE.unpack f a with ⟨t1, s1, m1, e1⟩
  rcases hu2 : GoFV.IEEE.unpack f b with ⟨t2, s2, m2, e2⟩
  rw [hu1, hu2] at hp
  dsimp only at hp ⊢
  rw [hp]
  cases hpn : GoFV.IEEE.processNaNs f t2 t1 b a with
  | some r => rfl
  | none =>
    dsimp only
    cases t1 <;> cases t2 <;> simp [GoFV.IEEE.processNaNs] at hpn <;> cases s1 <;> cases s2 <;>
      simp [addExact_comm]

/-- `FPMul` is commutative unless both operands are NaNs of the same kind. -/
theorem mul_comm_of {f : Fmt} {rm : RMode} {a b : GoFV.IEEE.Bits f} (h : ¬ SameNaN f a b) :
    GoFV.IEEE.mul f rm a b = GoFV.IEEE.mul f rm b a := by
  have hp := processNaNs_comm (f := f) (a := a) (b := b) rfl rfl h
  unfold GoFV.IEEE.typeOf at hp
  unfold GoFV.IEEE.mul
  rcases hu1 : GoFV.IEEE.unpack f a with ⟨t1, s1, m1, e1⟩
  rcases hu2 : GoFV.IEEE.unpack f b with ⟨t2, s2, m2, e2⟩
  rw [hu1, hu2] at hp
  dsimp only at hp ⊢
  rw [hp]
  have hc : ((t1 = .infinity ∧ t2 = .zero) ∨ (t1 = .zero ∧ t2 = .infinity)) =
      ((t2 = .infinity ∧ t1 = .zero) ∨ (t2 = .zero ∧ t1 = .infinity)) :=
    propext ⟨fun h => by rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all,
      fun h => by rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all⟩
  have hi : (t1 = .infinity ∨ t2 = .infinity) = (t2 = .infinity ∨ t1 = .infinity) :=
    propext or_comm
  have hz : (t1 = .zero ∨ t2 = .zero) = (t2 = .zero ∨ t1 = .zero) := propext or_comm
  have hs : (s1 != s2) = (s2 != s1) := by cases s1 <;> cases s2 <;> rfl
  simp only [hc, hi, hz, hs, Nat.mul_comm m1 m2, Int.add_comm e1 e2]

/-- The operands `a` (first, `Rn`) and `b` (second, `Rm`) of an `FADD`/`FMUL` on which Phase 1's
`FOps.ordered` swaps them and the result may differ: `b`'s encoding is below `a`'s and both are
NaNs of the same kind. -/
def NaNSwap (f : Fmt) (a b : GoFV.IEEE.Bits f) : Prop := b.toNat < a.toNat ∧ SameNaN f a b

/-- `NaNSwap` of two float values of one width (`False` otherwise). -/
def FNaNSwap : Val → Val → Prop
  | .int .w32 a, .int .w32 b => NaNSwap Fmt.b32 a b
  | .int .w64 a, .int .w64 b => NaNSwap Fmt.b64 a b
  | _, _ => False

/-- Phase 1's operand order is the machine's unless `NaNSwap`, for an op commutative outside
same-kind NaN pairs. -/
theorem ordered_of {f : Fmt} {g : GoFV.IEEE.Bits f → GoFV.IEEE.Bits f → GoFV.IEEE.Bits f}
    {a b : GoFV.IEEE.Bits f} (hg : ¬ SameNaN f a b → g a b = g b a) (h : ¬ NaNSwap f a b) :
    FOps.ordered g a b = g a b := by
  unfold FOps.ordered
  split
  · rename_i hlt
    exact (hg fun hs => h ⟨hlt, hs⟩).symm
  · rfl

/-! ## Values -/

theorem retypeL_int_self (w : Width) (z : BitVec w.bits) :
    (Val.int w z).retypeL (.int w) = .int w z := by
  cases w <;> exact (congrArg (Val.int _) (BitVec.setWidth_eq z) :)

/-- A float result zero-extended to the V register. -/
theorem fvalRel_setWidth {w : Width} (r : BitVec w.bits) : FValRel (.int w r) (r.setWidth 128) := by
  show (r.setWidth 128).setWidth w.bits = r
  rw [BitVec.setWidth_setWidth_of_le _ (by cases w <;> decide), BitVec.setWidth_eq]

/-- A value related to a V register and of class `w.bits` is `poison` or the register's low
`w.bits` bits at width `w`. -/
theorem fval_rel {w : Width} {x : Val} {q : BitVec 128} (hx : FValRel x q) (hf : Fits w.bits x) :
    x = .poison ∨ x = .int w (q.setWidth w.bits) := by
  rcases fval_cases hx hf with rfl | ⟨w', y, rfl, hw'⟩
  · exact .inl rfl
  · right
    have : w' = w := by cases w <;> cases w' <;> first | rfl | simp [Width.bits] at hw'
    subst this
    have hy : q.setWidth w'.bits = y := hx
    rw [hy]

private theorem int1_fval {ws wd : Width} (g : BitVec ws.bits → BitVec wd.bits)
    (z : BitVec ws.bits) :
    int1 ws (fun a => .int wd (g a)) [Arm64.fval ws (.int ws z)] = .int wd (g z) := by
  simp [int1, Arm64.fval, Val.asInt]

private theorem int2_fval {w : Width} (g : BitVec w.bits → BitVec w.bits → Val)
    (a b : BitVec w.bits) :
    int2 w g [Arm64.fval w (.int w a), Arm64.fval w (.int w b)] = g a b := by
  simp [int2, Arm64.fval, Val.asInt]

/-- A unary float op of `Arm64.fop` shape on an operand related to `q`. -/
private theorem fvalRel_int1 {ws wd : Width} {g : BitVec ws.bits → BitVec wd.bits} {x : Val}
    {q q' : BitVec 128} (hx : FValRel x q) (hf : Fits ws.bits x)
    (hg : FValRel (.int wd (g (q.setWidth ws.bits))) q') :
    FValRel ((int1 ws (fun a => .int wd (g a)) [Arm64.fval ws x]).retypeL (.int wd)) q' := by
  rcases fval_rel hx hf with rfl | rfl
  · show FValRel (Val.poison.retypeL _) _
    rw [retypeL_poison]; trivial
  · rw [int1_fval, retypeL_int_self]; exact hg

/-- A binary float op of `Arm64.fop` shape on operands related to `qx`, `qy`. -/
private theorem fvalRel_int2 {w : Width} {g : BitVec w.bits → BitVec w.bits → BitVec w.bits}
    {x y : Val} {qx qy q : BitVec 128} (hx : FValRel x qx) (hy : FValRel y qy)
    (hfx : Fits w.bits x) (hfy : Fits w.bits y)
    (hg : x = .int w (qx.setWidth w.bits) → y = .int w (qy.setWidth w.bits) →
      FValRel (.int w (g (qx.setWidth w.bits) (qy.setWidth w.bits))) q) :
    FValRel ((int2 w (fun a b => .int w (g a b)) [Arm64.fval w x, Arm64.fval w y]).retypeL (.int w))
      q := by
  rcases fval_rel hx hfx with rfl | rfl
  · show FValRel (Val.poison.retypeL _) _
    rw [retypeL_poison]; trivial
  · rcases fval_rel hy hfy with rfl | rfl
    · have : int2 w (fun a b => .int w (g a b))
          [Arm64.fval w (.int w (qx.setWidth w.bits)), Arm64.fval w .poison] = .poison := by
        simp [int2, Arm64.fval, Val.asInt]
      rw [this, retypeL_poison]; trivial
    · rw [int2_fval, retypeL_int_self]; exact hg rfl rfl

/-- `FADD`/`FSUB`/`FMUL`/`FDIV` (`fp2Of`) of arguments related to the V registers `qx` (`Rn`,
argument 0) and `qy` (`Rm`, argument 1): the machine's `fp2Op`, unless (`FADD`/`FMUL` only) the
arguments are a `FNaNSwap` pair. -/
theorem fvalRel_fp2 {op : Op} {n : Nat} {ft : BitVec 2} {opc : BitVec 4}
    (hop : fp2Of op = some (n, ft, opc)) {t : Ty} {k : Int64} {aux : Option AuxRef} {x y : Val}
    {qx qy : BitVec 128} (hx : FValRel x qx) (hy : FValRel y qy) (hfx : Fits (8 * n) x)
    (hfy : Fits (8 * n) y) (hft : fTy t = true) (hct : cls t = some (8 * n))
    (hnan : opc = 0 ∨ opc = 2 → ¬ FNaNSwap x y) :
    FValRel ((Arm64.evalPure op t k aux [x, y]).retypeL t) (fp2Op ft opc qx qy) := by
  obtain ⟨rfl, -⟩ := fTy_eq hft hct
  rcases fp2Of_some hop with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩
  · refine fvalRel_int2 (w := .w64) (g := FOps.ordered (GoFV.IEEE.add Fmt.b64 .rne)) hx hy hfx hfy
      fun h1 h2 => ?_
    have hs := hnan (.inr rfl)
    rw [h1, h2] at hs
    rw [ordered_of (f := Fmt.b64) (a := qx.setWidth 64) (b := qy.setWidth 64) add_comm_of hs]
    exact fvalRel_setWidth _
  · refine fvalRel_int2 (w := .w32) (g := FOps.ordered (GoFV.IEEE.add Fmt.b32 .rne)) hx hy hfx hfy
      fun h1 h2 => ?_
    have hs := hnan (.inr rfl)
    rw [h1, h2] at hs
    rw [ordered_of (f := Fmt.b32) (a := qx.setWidth 32) (b := qy.setWidth 32) add_comm_of hs]
    exact fvalRel_setWidth _
  · exact fvalRel_int2 (w := .w64) (g := GoFV.IEEE.sub Fmt.b64 .rne) hx hy hfx hfy
      fun _ _ => fvalRel_setWidth _
  · exact fvalRel_int2 (w := .w32) (g := GoFV.IEEE.sub Fmt.b32 .rne) hx hy hfx hfy
      fun _ _ => fvalRel_setWidth _
  · refine fvalRel_int2 (w := .w64) (g := FOps.ordered (GoFV.IEEE.mul Fmt.b64 .rne)) hx hy hfx hfy
      fun h1 h2 => ?_
    have hs := hnan (.inl rfl)
    rw [h1, h2] at hs
    rw [ordered_of (f := Fmt.b64) (a := qx.setWidth 64) (b := qy.setWidth 64) mul_comm_of hs]
    exact fvalRel_setWidth _
  · refine fvalRel_int2 (w := .w32) (g := FOps.ordered (GoFV.IEEE.mul Fmt.b32 .rne)) hx hy hfx hfy
      fun h1 h2 => ?_
    have hs := hnan (.inl rfl)
    rw [h1, h2] at hs
    rw [ordered_of (f := Fmt.b32) (a := qx.setWidth 32) (b := qy.setWidth 32) mul_comm_of hs]
    exact fvalRel_setWidth _
  · exact fvalRel_int2 (w := .w64) (g := GoFV.IEEE.div Fmt.b64 .rne) hx hy hfx hfy
      fun _ _ => fvalRel_setWidth _
  · exact fvalRel_int2 (w := .w32) (g := GoFV.IEEE.div Fmt.b32 .rne) hx hy hfx hfy
      fun _ _ => fvalRel_setWidth _

/-- `FSUB`/`FDIV`: `fvalRel_fp2` without a premise. -/
theorem fvalRel_fsubdiv {op : Op} {n : Nat} {ft : BitVec 2} {opc : BitVec 4}
    (hop : fp2Of op = some (n, ft, opc)) (hsd : opc = 1 ∨ opc = 3) {t : Ty} {k : Int64}
    {aux : Option AuxRef} {x y : Val} {qx qy : BitVec 128} (hx : FValRel x qx) (hy : FValRel y qy)
    (hfx : Fits (8 * n) x) (hfy : Fits (8 * n) y) (hft : fTy t = true)
    (hct : cls t = some (8 * n)) :
    FValRel ((Arm64.evalPure op t k aux [x, y]).retypeL t) (fp2Op ft opc qx qy) :=
  fvalRel_fp2 hop hx hy hfx hfy hft hct fun h => by
    rcases hsd with rfl | rfl <;> rcases h with h | h <;> exact absurd h (by decide)

/-- `FNEG`/`FABS`/`FSQRT`/`FCVTSD`/`FCVTDS` (`fp1Of`) of an argument related to the V register
`q`: the machine's `fp1Op`. -/
theorem fvalRel_fp1 {op : Op} {ns nd : Nat} {ft : BitVec 2} {opc : BitVec 6}
    (hop : fp1Of op = some (ns, nd, ft, opc)) {t : Ty} {k : Int64} {aux : Option AuxRef} {x : Val}
    {q : BitVec 128} (hx : FValRel x q) (hf : Fits (8 * ns) x) (hft : fTy t = true)
    (hct : cls t = some (8 * nd)) :
    FValRel ((Arm64.evalPure op t k aux [x]).retypeL t) (fp1Op ft opc q) := by
  obtain ⟨rfl, -⟩ := fTy_eq hft hct
  rcases fp1Of_some hop with ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl⟩
  · exact fvalRel_int1 (ws := .w64) (wd := .w64) (g := GoFV.IEEE.neg Fmt.b64) hx hf
      (fvalRel_setWidth _)
  · exact fvalRel_int1 (ws := .w32) (wd := .w32) (g := GoFV.IEEE.neg Fmt.b32) hx hf
      (fvalRel_setWidth _)
  · exact fvalRel_int1 (ws := .w64) (wd := .w64) (g := GoFV.IEEE.abs Fmt.b64) hx hf
      (fvalRel_setWidth _)
  · exact fvalRel_int1 (ws := .w32) (wd := .w32) (g := GoFV.IEEE.abs Fmt.b32) hx hf
      (fvalRel_setWidth _)
  · exact fvalRel_int1 (ws := .w64) (wd := .w64) (g := GoFV.IEEE.sqrt Fmt.b64 .rne) hx hf
      (fvalRel_setWidth _)
  · exact fvalRel_int1 (ws := .w32) (wd := .w32) (g := GoFV.IEEE.sqrt Fmt.b32 .rne) hx hf
      (fvalRel_setWidth _)
  · exact fvalRel_int1 (ws := .w32) (wd := .w64) (g := GoFV.IEEE.convert Fmt.b32 Fmt.b64 .rne) hx hf
      (fvalRel_setWidth _)
  · exact fvalRel_int1 (ws := .w64) (wd := .w32) (g := GoFV.IEEE.convert Fmt.b64 Fmt.b32 .rne) hx hf
      (fvalRel_setWidth _)

section X

variable {ι : Blk → Option (BitVec 64)}

private theorem low_of_le' {c ca : Nat} {a b : BitVec 64} (h : a.setWidth ca = b.setWidth ca)
    (hc : c ≤ ca) : a.setWidth c = b.setWidth c := by
  have := congrArg (BitVec.setWidth c) h
  simpa only [BitVec.setWidth_setWidth_of_le _ hc] using this

private theorem cvtf_eq32 {u : Bool} {ws : Width} {x : Val} {X' : BitVec 64}
    (hr : Arm64.reg x = some X') :
    Arm64.cvtf u ws .w32 [x] =
      .int .w32 (GoFV.IEEE.fromFixed Fmt.b32 ws.bits (X'.setWidth ws.bits) u .rne) := by
  simp [Arm64.cvtf, hr, FOps.ofInt, int1, Val.asInt]

private theorem cvtf_eq64 {u : Bool} {ws : Width} {x : Val} {X' : BitVec 64}
    (hr : Arm64.reg x = some X') :
    Arm64.cvtf u ws .w64 [x] =
      .int .w64 (GoFV.IEEE.fromFixed Fmt.b64 ws.bits (X'.setWidth ws.bits) u .rne) := by
  simp [Arm64.cvtf, hr, FOps.ofInt, int1, Val.asInt]

private theorem cvtf_none {u : Bool} {ws wd : Width} {x : Val} (hr : Arm64.reg x = none) :
    Arm64.cvtf u ws wd [x] = .poison := by
  simp [Arm64.cvtf, hr]

private theorem fvalRel_cvtf32 (hA : AddrAgree ι) {u : Bool} {ws : Width} {x : Val} {X : BitVec 64}
    {ca : Nat} (hx : ValRel ι x X) (hf : Fits ca x) (hca : ws.bits ≤ ca) :
    FValRel ((Arm64.cvtf u ws .w32 [x]).retypeL (.int .w32))
      ((GoFV.IEEE.fromFixed Fmt.b32 ws.bits (X.setWidth ws.bits) u .rne).setWidth 128) := by
  cases hr : Arm64.reg x with
  | none => rw [cvtf_none hr, retypeL_poison]; trivial
  | some X' =>
    rw [cvtf_eq32 hr, retypeL_int_self, low_of_le' (reg_low hA hx hf hr) hca]
    exact fvalRel_setWidth _

private theorem fvalRel_cvtf64 (hA : AddrAgree ι) {u : Bool} {ws : Width} {x : Val} {X : BitVec 64}
    {ca : Nat} (hx : ValRel ι x X) (hf : Fits ca x) (hca : ws.bits ≤ ca) :
    FValRel ((Arm64.cvtf u ws .w64 [x]).retypeL (.int .w64))
      ((GoFV.IEEE.fromFixed Fmt.b64 ws.bits (X.setWidth ws.bits) u .rne).setWidth 128) := by
  cases hr : Arm64.reg x with
  | none => rw [cvtf_none hr, retypeL_poison]; trivial
  | some X' =>
    rw [cvtf_eq64 hr, retypeL_int_self, low_of_le' (reg_low hA hx hf hr) hca]
    exact fvalRel_setWidth _

/-- `SCVTF`/`UCVTF` (`cvtfOf`) of an X register argument of class `ca ≥ 8 ns` related to `X`: the
machine's `cvtfBits` (as `fvalRel_gpfp`, only the low `8 ns` bits of the register are read). -/
theorem fvalRel_cvtf (hA : AddrAgree ι) {op : Op} {u : Bool} {ns nd : Nat}
    (hop : cvtfOf op = some (u, ns, nd)) {t : Ty} {k : Int64} {aux : Option AuxRef} {x : Val}
    {X : BitVec 64} {ca : Nat} (hx : ValRel ι x X) (hf : Fits ca x) (hca : 8 * ns ≤ ca)
    (hft : fTy t = true) (hct : cls t = some (8 * nd)) :
    FValRel ((Arm64.evalPure op t k aux [x]).retypeL t) (cvtfBits u ns nd X) := by
  obtain ⟨rfl, -⟩ := fTy_eq hft hct
  rcases cvtfOf_some hop with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩
  · exact fvalRel_cvtf32 (ws := .w32) hA hx hf hca
  · exact fvalRel_cvtf64 (ws := .w32) hA hx hf hca
  · exact fvalRel_cvtf32 (ws := .w32) hA hx hf hca
  · exact fvalRel_cvtf64 (ws := .w32) hA hx hf hca
  · exact fvalRel_cvtf32 (ws := .w64) hA hx hf hca
  · exact fvalRel_cvtf64 (ws := .w64) hA hx hf hca
  · exact fvalRel_cvtf32 (ws := .w64) hA hx hf hca
  · exact fvalRel_cvtf64 (ws := .w64) hA hx hf hca

private theorem res_ne_bool {t : Ty} (ht : t ≠ .bool) (r : BitVec 64) :
    Arm64.res t r = .int .w64 r := by
  cases t <;> first | rfl | exact absurd rfl ht

private theorem lo_fcvtz32 {u : Bool} {wd : Width} {x : Val} {q : BitVec 128}
    (hx : FValRel x q) (hf : Fits 32 x) {t : Ty} (ht : t ≠ .bool) :
    Lo ι 64 (Arm64.fcvtz t u .w32 wd [x])
      ((GoFV.IEEE.toFixed Fmt.b32 (q.setWidth 32) u wd.bits .rz).setWidth 64) := by
  rcases fval_rel (w := .w32) hx hf with rfl | rfl
  · simp [Arm64.fcvtz, FOps.toInt, int1, Arm64.fval, Val.asInt]; trivial
  · simp only [Arm64.fcvtz, FOps.toInt, List.map, Arm64.fval, int1, Val.asInt, dite_true,
      res_ne_bool ht]
    show _ = _
    simp

private theorem lo_fcvtz64 {u : Bool} {wd : Width} {x : Val} {q : BitVec 128}
    (hx : FValRel x q) (hf : Fits 64 x) {t : Ty} (ht : t ≠ .bool) :
    Lo ι 64 (Arm64.fcvtz t u .w64 wd [x])
      ((GoFV.IEEE.toFixed Fmt.b64 (q.setWidth 64) u wd.bits .rz).setWidth 64) := by
  rcases fval_rel (w := .w64) hx hf with rfl | rfl
  · simp [Arm64.fcvtz, FOps.toInt, int1, Arm64.fval, Val.asInt]; trivial
  · simp only [Arm64.fcvtz, FOps.toInt, List.map, Arm64.fval, int1, Val.asInt, dite_true,
      res_ne_bool ht]
    show _ = _
    simp

/-- `FCVTZS`/`FCVTZU` (`fcvtzOf`) of an argument related to the V register `q`: the 64-bit
register result agrees with the machine's `fcvtzBits` (as `lo_fmovVX`; `valRel_retypeL_lo` reads
it at the result's shape). -/
theorem lo_fcvtz {op : Op} {u : Bool} {ns nd : Nat} (hop : fcvtzOf op = some (u, ns, nd))
    {t : Ty} {k : Int64} {aux : Option AuxRef} {x : Val} {q : BitVec 128} (hx : FValRel x q)
    (hf : Fits (8 * ns) x) (ht : t ≠ .bool) :
    Lo ι 64 (Arm64.evalPure op t k aux [x]) (fcvtzBits u ns nd q) := by
  rcases fcvtzOf_some hop with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl, rfl⟩
  · exact lo_fcvtz32 (wd := .w32) hx hf ht
  · exact lo_fcvtz64 (wd := .w32) hx hf ht
  · exact lo_fcvtz32 (wd := .w32) hx hf ht
  · exact lo_fcvtz64 (wd := .w32) hx hf ht
  · exact lo_fcvtz32 (wd := .w64) hx hf ht
  · exact lo_fcvtz64 (wd := .w64) hx hf ht
  · exact lo_fcvtz32 (wd := .w64) hx hf ht
  · exact lo_fcvtz64 (wd := .w64) hx hf ht

end X

private theorem flagsRel_toVal (f : Flags) : FlagsRel f.toVal f := ⟨rfl, rfl, rfl, rfl⟩

private theorem fval_self (w : Width) (z : BitVec w.bits) : Arm64.fval w (.int w z) = .int w z := by
  simp only [Arm64.fval, BitVec.setWidth_eq]

private theorem fcmp_w32 {x y : Val} {qx qy : BitVec 128} (hx : FValRel x qx) (hy : FValRel y qy)
    (hfx : Fits 32 x) (hfy : Fits 32 y) :
    FlagsRel (Arm64.fcmp .w32 false [x, y]) (fcmpOp 0 qx qy) := by
  rcases fval_rel (w := .w32) hx hfx with rfl | rfl
  · simp [Arm64.fcmp, int2, Arm64.fval, Val.asInt]; trivial
  · rcases fval_rel (w := .w32) hy hfy with rfl | rfl
    · simp [Arm64.fcmp, int2, Arm64.fval, Val.asInt]; trivial
    · simp only [Arm64.fcmp, Bool.false_eq_true, ↓reduceIte, List.map, fval_self, int2,
        Val.asInt, dite_true, fcmpOp]
      exact flagsRel_toVal _

private theorem fcmp_w64 {x y : Val} {qx qy : BitVec 128} (hx : FValRel x qx) (hy : FValRel y qy)
    (hfx : Fits 64 x) (hfy : Fits 64 y) :
    FlagsRel (Arm64.fcmp .w64 false [x, y]) (fcmpOp 1 qx qy) := by
  rcases fval_rel (w := .w64) hx hfx with rfl | rfl
  · simp [Arm64.fcmp, int2, Arm64.fval, Val.asInt]; trivial
  · rcases fval_rel (w := .w64) hy hfy with rfl | rfl
    · simp [Arm64.fcmp, int2, Arm64.fval, Val.asInt]; trivial
    · simp only [Arm64.fcmp, Bool.false_eq_true, ↓reduceIte, List.map, fval_self, int2,
        Val.asInt, dite_true, fcmpOp]
      exact flagsRel_toVal _

private theorem fcmp0_w32 {x : Val} {qx : BitVec 128} (hx : FValRel x qx) (hfx : Fits 32 x) :
    FlagsRel (Arm64.fcmp .w32 true [x]) (fcmpOp 0 qx 0) := by
  rcases fval_rel (w := .w32) hx hfx with rfl | rfl
  · simp [Arm64.fcmp, int2, Arm64.fval, Val.asInt]; trivial
  · simp only [Arm64.fcmp, ↓reduceIte, List.cons_append, List.nil_append, List.map, fval_self,
      int2, Val.asInt, dite_true, fcmpOp]
    exact flagsRel_toVal _

private theorem fcmp0_w64 {x : Val} {qx : BitVec 128} (hx : FValRel x qx) (hfx : Fits 64 x) :
    FlagsRel (Arm64.fcmp .w64 true [x]) (fcmpOp 1 qx 0) := by
  rcases fval_rel (w := .w64) hx hfx with rfl | rfl
  · simp [Arm64.fcmp, int2, Arm64.fval, Val.asInt]; trivial
  · simp only [Arm64.fcmp, ↓reduceIte, List.cons_append, List.nil_append, List.map, fval_self,
      int2, Val.asInt, dite_true, fcmpOp]
    exact flagsRel_toVal _

/-- `FCMPS`/`FCMPD` (`fcmpOf`, register form) of arguments related to the V registers `qx` (`Rn`,
argument 0) and `qy` (`Rm`, argument 1): the machine's `fcmpOp`, read at the flags shape. -/
theorem flagsRel_fcmp {op : Op} {n : Nat} {ft : BitVec 2} (hop : fcmpOf op = some (n, ft, false))
    {t : Ty} {k : Int64} {aux : Option AuxRef} {x y : Val} {qx qy : BitVec 128}
    (hx : FValRel x qx) (hy : FValRel y qy) (hfx : Fits (8 * n) x) (hfy : Fits (8 * n) y) :
    FlagsRel ((Arm64.evalPure op t k aux [x, y]).retypeL Ty.flags) (fcmpOp ft qx qy) := by
  refine (flags_retypeL ?_).1
  rcases fcmpOf_some hop with ⟨rfl, rfl, rfl, -⟩ | ⟨rfl, rfl, rfl, -⟩ | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩
  · exact fcmp_w32 hx hy hfx hfy
  · exact fcmp_w64 hx hy hfx hfy
  · cases h
  · cases h

/-- `FCMPS0`/`FCMPD0` (`fcmpOf`, zero form) of an argument related to the V register `qx`: the
machine's `fcmpOp` against `0` (`progStep_fcmp0`), read at the flags shape. -/
theorem flagsRel_fcmp0 {op : Op} {n : Nat} {ft : BitVec 2} (hop : fcmpOf op = some (n, ft, true))
    {t : Ty} {k : Int64} {aux : Option AuxRef} {x : Val} {qx : BitVec 128}
    (hx : FValRel x qx) (hfx : Fits (8 * n) x) :
    FlagsRel ((Arm64.evalPure op t k aux [x]).retypeL Ty.flags) (fcmpOp ft qx 0) := by
  refine (flags_retypeL ?_).1
  rcases fcmpOf_some hop with ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ | ⟨rfl, rfl, rfl, -⟩ | ⟨rfl, rfl, rfl, -⟩
  · cases h
  · cases h
  · exact fcmp0_w32 hx hfx
  · exact fcmp0_w64 hx hfx

/-! ## Fused multiply-adds -/

/-- `FPProcessNaNs3` does not depend on the order of the multiplicands unless both are NaNs of
one kind. -/
private theorem processNaNs3_comm {f : Fmt} {a n m : GoFV.IEEE.Bits f} {tA t1 t2 : FPType}
    (h1 : GoFV.IEEE.typeOf f n = t1) (h2 : GoFV.IEEE.typeOf f m = t2) (h : ¬ SameNaN f n m) :
    GoFV.IEEE.processNaNs3 f tA t1 t2 a n m = GoFV.IEEE.processNaNs3 f tA t2 t1 a m n := by
  unfold SameNaN at h
  rw [h1, h2] at h
  cases tA <;> cases t1 <;> cases t2 <;> simp_all [GoFV.IEEE.processNaNs3]

/-- `FPMulAdd` is commutative in its multiplicands unless both are NaNs of the same kind. -/
theorem mulAdd_comm_of {f : Fmt} {rm : RMode} {a n m : GoFV.IEEE.Bits f} (h : ¬ SameNaN f n m) :
    GoFV.IEEE.mulAdd f rm a n m = GoFV.IEEE.mulAdd f rm a m n := by
  have hp := processNaNs3_comm (f := f) (a := a) (n := n) (m := m)
    (tA := (GoFV.IEEE.unpack f a).1) rfl rfl h
  unfold GoFV.IEEE.typeOf at hp
  unfold GoFV.IEEE.mulAdd
  rcases huA : GoFV.IEEE.unpack f a with ⟨tA, sA, mA, eA⟩
  rcases hu1 : GoFV.IEEE.unpack f n with ⟨t1, s1, m1, e1⟩
  rcases hu2 : GoFV.IEEE.unpack f m with ⟨t2, s2, m2, e2⟩
  rw [huA, hu1, hu2] at hp
  dsimp only at hp ⊢
  rw [hp]
  -- the rest is symmetric up to the order of the multiplicands' classes, signs and magnitudes
  have hc : ∀ C : Prop, ((t1 = .infinity ∧ t2 = .zero) ∨ (t1 = .zero ∧ t2 = .infinity) ∨ C) =
      ((t2 = .infinity ∧ t1 = .zero) ∨ (t2 = .zero ∧ t1 = .infinity) ∨ C) := fun C =>
    propext ⟨fun h => by rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h <;> simp_all,
      fun h => by rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h <;> simp_all⟩
  have hc' : ((t1 = .infinity ∧ t2 = .zero) ∨ (t1 = .zero ∧ t2 = .infinity)) =
      ((t2 = .infinity ∧ t1 = .zero) ∨ (t2 = .zero ∧ t1 = .infinity)) :=
    propext ⟨fun h => by rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all,
      fun h => by rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> simp_all⟩
  have hi : (t1 = .infinity ∨ t2 = .infinity) = (t2 = .infinity ∨ t1 = .infinity) :=
    propext or_comm
  have hz : (t1 = .zero ∨ t2 = .zero) = (t2 = .zero ∨ t1 = .zero) := propext or_comm
  have hs : (s1 != s2) = (s2 != s1) := by cases s1 <;> cases s2 <;> rfl
  simp only [hc, hc', hi, hz, hs, Nat.mul_comm m1 m2, Int.add_comm e1 e2]

/-- `SameNaN` of two float values of one width (`False` otherwise). -/
def FSameNaN : Val → Val → Prop
  | .int .w32 a, .int .w32 b => SameNaN Fmt.b32 a b
  | .int .w64 a, .int .w64 b => SameNaN Fmt.b64 a b
  | _, _ => False

private theorem fma_w32 {negA : Bool} {a y z : Val} {qa qm qn : BitVec 128}
    (ha : FValRel a qa) (hy : FValRel y qm) (hz : FValRel z qn) (hfa : Fits 32 a)
    (hfy : Fits 32 y) (hfz : Fits 32 z) (hnan : ¬ FSameNaN y z) :
    FValRel ((Arm64.fmadd .w32 negA false [a, y, z]).retypeL (.int .w32))
      (fp3Op 0 negA negA qa qn qm) := by
  rcases fval_rel (w := .w32) ha hfa with rfl | rfl <;>
    rcases fval_rel (w := .w32) hy hfy with rfl | rfl <;>
    rcases fval_rel (w := .w32) hz hfz with rfl | rfl
  all_goals first
    | (cases negA <;> simp [Arm64.fmadd, FOps.neg, FOps.un, FOps.fma, int1, int3, Arm64.fval,
        Val.asInt, retypeL_poison] <;> trivial)
    | skip
  have hc := mulAdd_comm_of (rm := .rne) (a := (if negA then GoFV.IEEE.neg Fmt.b32 (qa.setWidth 32)
    else qa.setWidth 32)) hnan
  cases negA <;>
  · simp only [Arm64.fmadd, fval_self, Bool.false_eq_true, ↓reduceIte, FOps.neg, FOps.un, int1,
      FOps.fma, int3, Val.asInt, dite_true] at hc ⊢
    rw [retypeL_int_self, hc]
    simp only [fp3Op, ↓reduceIte, bne_self_eq_false, Bool.false_eq_true]
    exact fvalRel_setWidth _

private theorem fma_w64 {negA : Bool} {a y z : Val} {qa qm qn : BitVec 128}
    (ha : FValRel a qa) (hy : FValRel y qm) (hz : FValRel z qn) (hfa : Fits 64 a)
    (hfy : Fits 64 y) (hfz : Fits 64 z) (hnan : ¬ FSameNaN y z) :
    FValRel ((Arm64.fmadd .w64 negA false [a, y, z]).retypeL (.int .w64))
      (fp3Op 1 negA negA qa qn qm) := by
  rcases fval_rel (w := .w64) ha hfa with rfl | rfl <;>
    rcases fval_rel (w := .w64) hy hfy with rfl | rfl <;>
    rcases fval_rel (w := .w64) hz hfz with rfl | rfl
  all_goals first
    | (cases negA <;> simp [Arm64.fmadd, FOps.neg, FOps.un, FOps.fma, int1, int3, Arm64.fval,
        Val.asInt, retypeL_poison] <;> trivial)
    | skip
  have hc := mulAdd_comm_of (rm := .rne) (a := (if negA then GoFV.IEEE.neg Fmt.b64 (qa.setWidth 64)
    else qa.setWidth 64)) hnan
  cases negA <;>
  · simp only [Arm64.fmadd, fval_self, Bool.false_eq_true, ↓reduceIte, FOps.neg, FOps.un, int1,
      FOps.fma, int3, Val.asInt, dite_true] at hc ⊢
    rw [retypeL_int_self, hc]
    simp only [fp3Op, ↓reduceIte, bne_self_eq_false, Bool.false_eq_true]
    exact fvalRel_setWidth _

/-- `FMADD`/`FNMSUB` (`fp3Of` with `o1 = o0`: no multiplicand negated) of arguments related to the
V registers `qa` (`Ra`, argument 0, the addend), `qm` (`Rm`, argument 1) and `qn` (`Rn`, argument
2): the machine's `fp3Op`, unless the multiplicands are NaNs of one kind (`FSameNaN`: genssa
swaps the multiplicands relative to Phase 1's `FPMulAdd(a, arg1, arg2)`). -/
theorem fvalRel_fma {op : Op} {n : Nat} {ft : BitVec 2} {o : Bool}
    (hop : fp3Of op = some (n, ft, o, o)) {t : Ty} {k : Int64} {aux : Option AuxRef}
    {a y z : Val} {qa qm qn : BitVec 128} (ha : FValRel a qa) (hy : FValRel y qm)
    (hz : FValRel z qn) (hfa : Fits (8 * n) a) (hfy : Fits (8 * n) y) (hfz : Fits (8 * n) z)
    (hft : fTy t = true) (hct : cls t = some (8 * n)) (hnan : ¬ FSameNaN y z) :
    FValRel ((Arm64.evalPure op t k aux [a, y, z]).retypeL t) (fp3Op ft o o qa qn qm) := by
  obtain ⟨rfl, -⟩ := fTy_eq hft hct
  rcases fp3Of_some hop with ⟨rfl, rfl, rfl, rfl, -⟩ | ⟨rfl, rfl, rfl, rfl, -⟩ |
    ⟨-, -, -, rfl, h⟩ | ⟨-, -, -, rfl, h⟩ | ⟨-, -, -, rfl, h⟩ | ⟨-, -, -, rfl, h⟩ |
    ⟨rfl, rfl, rfl, rfl, -⟩ | ⟨rfl, rfl, rfl, rfl, -⟩
  · exact fma_w64 (negA := false) ha hy hz hfa hfy hfz hnan
  · exact fma_w32 (negA := false) ha hy hz hfa hfy hfz hnan
  · cases h
  · cases h
  · cases h
  · cases h
  · exact fma_w64 (negA := true) ha hy hz hfa hfy hfz hnan
  · exact fma_w32 (negA := true) ha hy hz hfa hfy hfz hnan

end GoFV.Proof.Gen
