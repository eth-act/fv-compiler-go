import GoFV.Proof.Gen.G50
import GoFV.Proof.Gen.Spec51b

variable [GoFV.SSA.Sem.Addrs]

/-!
# Soundness of the genssa validator's slice G51, group b: shifted `MVN`, `SBFIZ`, rotates
(`docs/plans/proofs3.md` §4)

`vk51b_step`: one value of `VK51b` (`GoFV/Proof/Gen/Spec51b.lean`) steps the machine as `runLoc`
steps it, `vk50_step`'s conclusion with no run premise and the empty upper-bit table.

`runLoc` runs the G51b ops as `Arm64.evalPure` of the arguments read from their homes
(`stepLoc_alu51b`).

* `MVNshiftXX [k] x` is `op1` of `~(x SHIFT k)` (`evalPure_mvnSh51b`), which the machine's
  `MVN Rm SHIFT k, Rd` computes through G27's shifted operand (`ORN` of `ZR`, `progStep_mvnSh51b`);
  a left shift's low bits read only the low bits of `x` (G27's `shl_low`), a right shift reads a
  64-bit `x` whole (`lo_mvnSh51b`).
* `SBFIZ [k] x` is `op1` of `sbfiz k`, the low `width` bits of `x` sign-extended and moved up by
  `lsb` (`progStep_sbfiz51b`, `sbfiz_ofNat51b`); bit `i` of the result reads bit `i - lsb` of `x`
  below `width`, else bit `width - 1` (G20's `sext_bit`), all below the argument's class
  (`lo_sbfiz51b`).
* The rotates `RORconst`, `RORWconst [k] x` and `ROR`, `RORW x y` are a rotate right of `x`'s
  register (its low word for the `W` forms, zero-extended) by `k` or `y` modulo the width
  (`rotF51b`), which the machine's `ROR`/`RORW` compute (`dp2Op`, `progStep_rorK51b`,
  `progStep_ror51b`); the amount reads only the low 6 bits of `y`'s register (G36's `mod64_low`;
  `lo_rorK51b`, `lo_ror51b`).

The G51b ops empty the upper-bit table (`uStep35_alu51b`). None needs a run premise: Phase 1 reads
a pointer argument by its register (`Arm64.reg`), which `ValRel` relates to the machine word.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The ops -/

theorem mvnSh51b?_some {op : Op} {typ : Nat} (h : mvnSh51b? op = some typ) :
    op = .ARM64MVNshiftLL ∧ typ = 0 ∨ op = .ARM64MVNshiftRL ∧ typ = 1 ∨
      op = .ARM64MVNshiftRA ∧ typ = 2 := by
  unfold mvnSh51b? at h
  split at h
  next h1 => cases h; exact .inl ⟨h1, rfl⟩
  next =>
    split at h
    next h1 => cases h; exact .inr (.inl ⟨h1, rfl⟩)
    next =>
      split at h
      next h1 => cases h; exact .inr (.inr ⟨h1, rfl⟩)
      next => cases h

theorem rorK51b?_some {op : Op} {as : As} {w : Nat} (h : rorK51b? op = some (as, w)) :
    op = .ARM64RORconst ∧ as = .ROR ∧ w = 64 ∨ op = .ARM64RORWconst ∧ as = .RORW ∧ w = 32 := by
  unfold rorK51b? at h
  split at h
  next h1 => cases h; exact .inl ⟨h1, rfl, rfl⟩
  next =>
    split at h
    next h1 => cases h; exact .inr ⟨h1, rfl, rfl⟩
    next => cases h

theorem ror51b?_some {op : Op} {as : As} {w : Nat} (h : ror51b? op = some (as, w)) :
    op = .ARM64ROR ∧ as = .ROR ∧ w = 64 ∨ op = .ARM64RORW ∧ as = .RORW ∧ w = 32 := by
  unfold ror51b? at h
  split at h
  next h1 => cases h; exact .inl ⟨h1, rfl, rfl⟩
  next =>
    split at h
    next h1 => cases h; exact .inr ⟨h1, rfl, rfl⟩
    next => cases h

/-- The ops of G51b. -/
def AluOp51b (op : Op) : Prop :=
  op = .ARM64MVNshiftLL ∨ op = .ARM64MVNshiftRL ∨ op = .ARM64MVNshiftRA ∨ op = .ARM64SBFIZ ∨
    op = .ARM64RORconst ∨ op = .ARM64RORWconst ∨ op = .ARM64ROR ∨ op = .ARM64RORW

theorem aluOp51b_mvnSh {op : Op} {typ : Nat} (h : mvnSh51b? op = some typ) : AluOp51b op := by
  unfold AluOp51b
  rcases mvnSh51b?_some h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp

theorem aluOp51b_rorK {op : Op} {as : As} {w : Nat} (h : rorK51b? op = some (as, w)) :
    AluOp51b op := by
  unfold AluOp51b
  rcases rorK51b?_some h with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp

theorem aluOp51b_ror {op : Op} {as : As} {w : Nat} (h : ror51b? op = some (as, w)) :
    AluOp51b op := by
  unfold AluOp51b
  rcases ror51b?_some h with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp

theorem aluOp51b_ne {op : Op} (h : AluOp51b op) : op ≠ .Phi := by
  unfold AluOp51b at h
  rcases h with h | h | h | h | h | h | h | h <;> subst h <;> nofun

/-- A G51b op empties G35's table. -/
theorem uStep35_alu51b {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value}
    (hop : AluOp51b v.op) : uStep35 lc L v = [] := by
  unfold AluOp51b at hop
  rcases hop with h | h | h | h | h | h | h | h <;>
    simp [uStep35, ldEntry35, loadOp?, narrowLoad?, pairOp35, uStep34, keep34, keep31, keepOp31,
      keepOp34, uStepL, uEntry, narrowLd?, loadIdxOp?, h]

/-- `Arm64.evalPure` of a shifted `MVN`: `op1` of the complement of the shifted register. -/
theorem evalPure_mvnSh51b {op : Op} {typ : Nat} (h : mvnSh51b? op = some typ) (t : Ty) (k : Int64)
    (aux : Option AuxRef) (argv : List Val) :
    Arm64.evalPure op t k aux argv =
      Arm64.op1 t (fun x => ~~~(Sem.Arm64.Shift.apply (shK typ) x (Arm64.amt k))) argv := by
  rcases mvnSh51b?_some h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-! ## `runLoc` -/

section Steps

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

/-- The ops of G51b: `Arm64.evalPure` on the arguments read from their homes. -/
theorem stepLoc_alu51b (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : AluOp51b v.op) (h : stepLoc env lc s v = .ok s') :
    ∃ argv, v.args.toList.mapM (s.read lc) = .ok argv ∧
      s' = s.write lc v.id ((Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux argv).retypeL
        (lc.ty v.id)) := by
  unfold AluOp51b at hop
  rcases hop with hop | hop | hop | hop | hop | hop | hop | hop <;>
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

/-- The machine word of a rotate right of `w` bits (64: `ROR`; else `RORW`, on the low word,
zero-extended) of `x` by `s` modulo the width. -/
def rotF51b (w : Nat) (x : BitVec 64) (s : Nat) : BitVec 64 :=
  if w = 64 then x.rotateRight (s % 64) else ((x.setWidth 32).rotateRight (s % 32)).setWidth 64

section Progs

variable {L : Link} {p : Prog} {s : MState} {next : BitVec 64}

private theorem nMVN51b : As.MVN.name = "MVN" := rfl
private theorem nSBFIZ51b : As.SBFIZ.name = "SBFIZ" := rfl
private theorem nROR51b : As.ROR.name = "ROR" := rfl
private theorem nRORW51b : As.RORW.name = "RORW" := rfl
private theorem cRORW51b : ProgOp.chopS "RORW" 1 = "ROR" := by decide

/-- `MVN Rm SHIFT k, Rd`: the complement of `X km` shifted by `k`. -/
theorem progStep_mvnSh51b {typ km kd k : Nat} (ht3 : typ < 3) (hkm : km < 32) (hkd : kd < 32)
    (hk : k < 64) (hn : L.nextAddr p.id = some next) (hpa : p.as = .MVN)
    (hf : p.from_ = shiftA typ (REG_R0 + km) k) (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      (~~~(Sem.Arm64.Shift.apply (shK typ) (s.rX (BitVec.ofNat 5 km)) k)) with pc := next } := by
  have he : progEffect ⟨L, s, p⟩ = .ok (effWd {} kd
      (~~~(Sem.Arm64.Shift.apply (shK typ) (s.rX (BitVec.ofNat 5 km)) k))) := by
    unfold progEffect
    simp (config := { decide := true }) only [hpa, nMVN51b, hf, ht, regA, ProgOp.baseOf,
      ↓reduceIte, ProgOp.binNames]
    rw [ctx_src_shift ht3 hkm hk]
    simp only [eff_wX_dest hkd]
    by_cases h : kd = 31 <;> simp (config := { decide := true }) [effWd, h, ProgOp.binOp,
      logical, sizedF, ProgOp.trunc] <;> rfl
  rw [progStep_eq hn (by simp [Prog.isSkip, hpa]) he
    (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]), wd_apply hkd]

/-- `SBFIZ` of a bitfield auxint `lsb · 256 + width` (`width < 256`, the auxint below `2 ^ 63`). -/
theorem sbfiz_ofNat51b {lsb width : Nat} (hw : width < 256) (hk : lsb * 256 + width < 2 ^ 63)
    (x : BitVec 64) :
    GoFV.SSA.Sem.Arm64.sbfiz (Int64.ofNat (lsb * 256 + width)) x =
      GoFV.SSA.Sem.Arm64.sext width x <<< lsb := by
  have h : (Int64.ofNat (lsb * 256 + width)).toInt = ((lsb * 256 + width : Nat) : Int) := by
    rw [Int64.toInt_ofNat_of_lt hk]
  simp only [GoFV.SSA.Sem.Arm64.sbfiz, GoFV.SSA.Sem.Arm64.bf, h, Int.toNat_natCast]
  rw [show (lsb * 256 + width) % 256 = width by omega,
    show (lsb * 256 + width) / 256 = lsb by omega]

/-- `SBFIZ $lsb, Rn, $width, Rd` (the operands `sbfizOK` fixes; `0 ≤ width < 256`, the auxint
`lsb · 256 + width` below `2 ^ 63`): the low `width` bits of `X kn` sign-extended, at bit `lsb`. -/
theorem progStep_sbfiz51b {kn kd x : Nat} {lsb width : Int} (hkn : kn < 32) (hkd : kd < 32)
    (hw0 : 0 ≤ width) (hw : width < 256) (hlw : lsb.toNat * 256 + width.toNat < 2 ^ 63)
    (hn : L.nextAddr p.id = some next) (has : p.as = .SBFIZ) (hf : p.from_ = constA lsb)
    (hr : p.reg = REG_R0 + kn) (ht : p.to = regA (REG_R0 + kd))
    (hrest : p.rest = #[(x, constA width)]) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      (GoFV.SSA.Sem.Arm64.sext width.toNat (s.rX (BitVec.ofNat 5 kn)) <<< lsb.toNat) with
        pc := next } := by
  have hrest0 : (ProgCtx.mk L s p).rest 0 = .ok (constA width) := by
    simp [ProgCtx.rest, hrest]
    rfl
  have hval : ProgOp.trunc true (GoFV.SSA.Sem.Arm64.sbfiz
      (Int64.ofNat (lsb.toNat * 256 + width.toNat)) (s.rX (BitVec.ofNat 5 kn))) =
      GoFV.SSA.Sem.Arm64.sext width.toNat (s.rX (BitVec.ofNat 5 kn)) <<< lsb.toNat := by
    simp only [ProgOp.trunc, ↓reduceIte]
    exact sbfiz_ofNat51b (by omega) hlw _
  have he : progEffect ⟨L, s, p⟩ = .ok (effWd {} kd
      (GoFV.SSA.Sem.Arm64.sext width.toNat (s.rX (BitVec.ofNat 5 kn)) <<< lsb.toNat)) := by
    unfold progEffect
    simp (config := { decide := true }) only [has, nSBFIZ51b, ProgOp.baseOf, ↓reduceIte,
      ProgOp.binNames, hrest0, hf, hr, ht, constA, regA, ctx_x_r0 hkn, ctx_x_r0 hkd]
    rw [← hval]
    exact eff_wX_dest hkd
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
    (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]), wd_apply hkd]

/-- The amount of a 32-bit rotate by a non-negative constant `k`. -/
theorem ofInt32_toNat_mod51b {k : Int} (hk : 0 ≤ k) :
    (BitVec.ofInt 32 k).toNat % 32 = k.toNat % 32 := by
  rw [BitVec.toNat_ofInt]
  have : ((2 ^ 32 : Nat) : Int) = 4294967296 := rfl
  rw [this]
  omega

/-- A 32-bit amount modulo 32 reads only the low 5 bits. -/
theorem setWidth32_toNat_mod51b (y : BitVec 64) : (y.setWidth 32).toNat % 32 = y.toNat % 32 := by
  rw [BitVec.toNat_setWidth]
  exact Nat.mod_mod_of_dvd _ (by decide)

/-- `RORW`'s `dp2Op` on 32-bit sources: the low word rotated right by the amount modulo 32,
zero-extended. -/
theorem dp2Op_rorw51b (x y : BitVec 64) :
    dp2Op false 11#6 (ProgOp.trunc false x) (ProgOp.trunc false y) =
      ((x.setWidth 32).rotateRight (y.toNat % 32)).setWidth 64 := by
  show (Sem.Arm64.Shift.apply .ro ((ProgOp.trunc false x).setWidth 32)
    ((ProgOp.trunc false y).setWidth 32).toNat).setWidth 64 = _
  rw [trunc_false_setWidth, trunc_false_setWidth]
  simp only [Sem.Arm64.Shift.apply, setWidth32_toNat_mod51b]

/-- `ROR`/`RORW $k, Rn, Rd` (`0 ≤ k`): `X kn` rotated right by `k` (`rotF51b`). -/
theorem progStep_rorK51b {as : As} {w kn kd : Nat} {k : Int} {op : Op}
    (hop : rorK51b? op = some (as, w)) (hkn : kn < 32) (hkd : kd < 32) (hk : 0 ≤ k)
    (hn : L.nextAddr p.id = some next) (has : p.as = as) (hf : p.from_ = constA k)
    (hr : p.reg = REG_R0 + kn) (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      (rotF51b w (s.rX (BitVec.ofNat 5 kn)) k.toNat) with pc := next } := by
  have hrn := rn_reg (c := ⟨L, s, p⟩) hr
  have hnm : ["LSL", "LSR", "ASR", "ROR"].contains "ROR" = true := by decide
  rcases rorK51b?_some hop with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
  · have hb : ProgOp.baseOf p.as.name ProgOp.binNames = some ("ROR", true) := by
      rw [has]; simp (config := { decide := true })
    have he : progEffect ⟨L, s, p⟩ = .ok (effWd {} kd
        (ProgOp.binOp "ROR" true (s.rX (BitVec.ofNat 5 kn)) (BitVec.ofInt 64 k) false).1) := by
      unfold progEffect
      simp only [hb, hf, constA, hnm, beq_self_eq_true, Bool.true_and, ↓reduceIte, hrn,
        ctx_src_reg hkn, ProgOp.trunc, ht, regA]
      exact eff_wX_dest hkd
    rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
      (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]), wd_apply hkd]
    simp (config := { decide := true }) only [ProgOp.binOp, dp2Op, sized, rotF51b, ↓reduceIte,
      BitVec.setWidth_eq, Sem.Arm64.Shift.apply, ofInt_toNat_mod hk]
  · have hb : ProgOp.baseOf p.as.name ProgOp.binNames = some ("ROR", false) := by
      rw [has]; simp (config := { decide := true }) [ProgOp.baseOf, nRORW51b, cRORW51b]
    have he : progEffect ⟨L, s, p⟩ = .ok (effWd {} kd
        (ProgOp.binOp "ROR" false (ProgOp.trunc false (s.rX (BitVec.ofNat 5 kn)))
          (ProgOp.trunc false (BitVec.ofInt 64 k)) false).1) := by
      unfold progEffect
      simp only [hb, hf, constA, hnm, beq_self_eq_true, Bool.true_and, ↓reduceIte, hrn,
        ctx_src_reg32 hkn, ht, regA]
      exact eff_wX_dest hkd
    rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
      (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]), wd_apply hkd]
    simp (config := { decide := true }) only [ProgOp.binOp, dp2Op, sized, rotF51b, ↓reduceIte,
      Sem.Arm64.Shift.apply, trunc_false_setWidth, ofInt_setWidth32, ofInt32_toNat_mod51b hk]

/-- `ROR`/`RORW Rm, Rn, Rd`: `X kn` rotated right by `X km` (`rotF51b`). -/
theorem progStep_ror51b {as : As} {w kn km kd : Nat} {op : Op}
    (hop : ror51b? op = some (as, w)) (hkn : kn < 32) (hkm : km < 32) (hkd : kd < 32)
    (hn : L.nextAddr p.id = some next) (hpa : p.as = as) (hf : p.from_ = regA (REG_R0 + km))
    (hr : p.reg = REG_R0 + kn) (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      (rotF51b w (s.rX (BitVec.ofNat 5 kn)) (s.rX (BitVec.ofNat 5 km)).toNat) with
        pc := next } := by
  have hrn := rn_reg (c := ⟨L, s, p⟩) hr
  have he : progEffect ⟨L, s, p⟩ = .ok (effWd {} kd
      (rotF51b w (s.rX (BitVec.ofNat 5 kn)) (s.rX (BitVec.ofNat 5 km)).toNat)) := by
    rcases ror51b?_some hop with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
    · unfold progEffect
      simp (config := { decide := true }) only [hpa, nROR51b, hf, ht, hrn, regA,
        ProgOp.baseOf, ↓reduceIte, ProgOp.binNames, ctx_src_reg hkn, ctx_src_reg hkm]
      simp only [eff_wX_dest hkd]
      by_cases h : kd = 31 <;> simp (config := { decide := true }) [effWd, h, ProgOp.binOp,
        dp2Op, sized, rotF51b, Sem.Arm64.Shift.apply] <;> rfl
    · unfold progEffect
      simp (config := { decide := true }) only [hpa, nRORW51b, hf, ht, hrn, regA,
        ProgOp.baseOf, ↓reduceIte, ProgOp.binNames, ProgOp.endsS, cRORW51b, ctx_src_reg32 hkn,
        ctx_src_reg32 hkm]
      simp only [bind, Except.bind, eff_wX_dest hkd]
      by_cases h : kd = 31 <;> simp (config := { decide := true }) [effWd, h, ProgOp.binOp,
        dp2Op_rorw51b, rotF51b] <;> rfl
  have hsk : p.isSkip = false := by
    rcases ror51b?_some hop with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> simp [Prog.isSkip, hpa]
  rw [progStep_eq hn hsk he (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]),
    wd_apply hkd]

end Progs

/-! ## Values -/

section Vals

variable {ι : Blk → Option (BitVec 64)}

private theorem res_int51b {t : Ty} (ht : t ≠ .bool) (r : BitVec 64) :
    Arm64.res t r = .int .w64 r := by
  cases t <;> first | rfl | exact absurd rfl ht

private theorem fits_le51b {c : Nat} {x : Val} {r : BitVec 64} (hf : Fits c x)
    (hr : Arm64.reg x = some r) : c ≤ 64 := by
  cases x with
  | int w v => have : w.bits = c := hf; subst this; cases w <;> decide
  | bool b => have : c = 1 := hf; omega
  | ptr p => have : c = 64 := hf; omega
  | _ => cases hr

private theorem low_le51b {c ca : Nat} {a b : BitVec 64} (h : a.setWidth ca = b.setWidth ca)
    (hc : c ≤ ca) : a.setWidth c = b.setWidth c := by
  have := congrArg (BitVec.setWidth c) h
  simpa only [BitVec.setWidth_setWidth_of_le _ hc] using this

private theorem bit_of_low51b {c i : Nat} {a b : BitVec 64} (h : a.setWidth c = b.setWidth c)
    (hi : i < c) : a.getLsbD i = b.getLsbD i := by
  have := congrArg (fun v => v.getLsbD i) h
  simpa only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and] using this

private theorem low_of_bits51b {c : Nat} {a b : BitVec 64}
    (h : ∀ i, i < c → i < 64 → a.getLsbD i = b.getLsbD i) : a.setWidth c = b.setWidth c := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth]
  by_cases h64 : i < 64
  · rw [h i hi h64]
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 64 ≤ i)]

/-- The register of an argument of 64 bits is the machine word. -/
private theorem reg64_51b (hA : AddrAgree ι) {x : Val} {X a : BitVec 64} {cx : Nat}
    (hx : ValRel ι x X) (hfx : Fits cx x) (hcx : 64 ≤ cx) (hr : Arm64.reg x = some a) : a = X := by
  have h64 := fits_le51b hfx hr
  have : cx = 64 := by omega
  subst this
  simpa only [BitVec.setWidth_eq] using reg_low hA hx hfx hr

/-- A unary op on the register of `x`, each register giving `Z` on the low `c` bits. -/
private theorem lo_op1_51b {t : Ty} {f : BitVec 64 → BitVec 64} {x : Val} {Z : BitVec 64}
    {c : Nat} (ht : t ≠ .bool) (hf : ∀ a, Arm64.reg x = some a → (f a).setWidth c = Z.setWidth c) :
    Lo ι c (Arm64.op1 t f [x]) Z := by
  simp only [Arm64.op1]
  cases hr : Arm64.reg x with
  | none => trivial
  | some a =>
    show Lo ι c (Arm64.res t (f a)) Z
    rw [res_int51b ht]
    exact hf a hr

/-- `MVNshiftXX [k] x` of an argument of class `ca`, at least the result's class `c` for a left
shift, of 64 bits otherwise: `MVN Rm SHIFT k, Rd` (`progStep_mvnSh51b`) on the low `c` bits. -/
theorem lo_mvnSh51b (hA : AddrAgree ι) {op : Op} {t : Ty} {typ : Nat} {k : Int64}
    {aux : Option AuxRef} {x : Val} {X : BitVec 64} {c ca : Nat}
    (hop : mvnSh51b? op = some typ) (hx : ValRel ι x X) (hfx : Fits ca x) (hc : c ≤ 64)
    (hll : typ = 0 → c ≤ ca) (hrr : typ ≠ 0 → ca = 64) (ht : t ≠ .bool) :
    Lo ι c (Arm64.evalPure op t k aux [x])
      (~~~(Sem.Arm64.Shift.apply (shK typ) X (Arm64.amt k))) := by
  rw [evalPure_mvnSh51b hop]
  refine lo_op1_51b ht fun a hr => ?_
  have hxa := reg_low hA hx hfx hr
  have hsh : (Sem.Arm64.Shift.apply (shK typ) a (Arm64.amt k)).setWidth c =
      (Sem.Arm64.Shift.apply (shK typ) X (Arm64.amt k)).setWidth c := by
    by_cases h0 : typ = 0
    · subst h0
      exact shl_low (low_le51b hxa (hll rfl))
    · have hca := hrr h0
      subst hca
      have : a = X := by simpa only [BitVec.setWidth_eq] using hxa
      rw [this]
  exact unF_low .MVN hc hsh

/-- `SBFIZ [k]` (`k = lsb · 256 + width ≥ 0`, `0 < width ≤ 64`) of an argument of class `ca`
holding every bit it reads (`width ≤ ca` or `c ≤ ca`): `SBFIZ $lsb, Rn, $width, Rd`
(`progStep_sbfiz51b`) on the low `c` bits. -/
theorem lo_sbfiz51b (hA : AddrAgree ι) {t : Ty} {k : Int64} {aux : Option AuxRef} {x : Val}
    {X : BitVec 64} {ca c : Nat} (hx : ValRel ι x X) (hfx : Fits ca x) (hk : 0 ≤ k.toInt)
    (hw0 : 0 < k.toInt % 256) (hw64 : k.toInt % 256 ≤ 64) (hw : k.toInt % 256 ≤ ca ∨ c ≤ ca)
    (ht : t ≠ .bool) :
    Lo ι c (Arm64.evalPure .ARM64SBFIZ t k aux [x])
      (GoFV.SSA.Sem.Arm64.sext (k.toInt % 256).toNat X <<< (k.toInt / 256).toNat) := by
  show Lo ι c (Arm64.op1 t (GoFV.SSA.Sem.Arm64.sbfiz k) [x]) _
  refine lo_op1_51b ht fun a hr => low_of_bits51b fun i hi h64 => ?_
  have hlow := reg_low hA hx hfx hr
  have h1 : k.toInt.toNat / 256 = (k.toInt / 256).toNat := by omega
  have h2 : k.toInt.toNat % 256 = (k.toInt % 256).toNat := by omega
  show (GoFV.SSA.Sem.Arm64.sext (k.toInt.toNat % 256) a <<< (k.toInt.toNat / 256)).getLsbD i = _
  rw [h1, h2]
  simp only [BitVec.getLsbD_shiftLeft]
  by_cases hs : i < (k.toInt / 256).toNat
  · simp [hs]
  · have hw' : 0 < (k.toInt % 256).toNat ∧ (k.toInt % 256).toNat ≤ 64 := by omega
    rw [sext_bit _ hw' _ _ (by omega), sext_bit _ hw' _ _ (by omega)]
    split
    · rw [bit_of_low51b hlow (by rcases hw with hw | hw <;> omega)]
    · rw [bit_of_low51b hlow (by rcases hw with hw | hw <;> omega)]

/-- `RORconst`, `RORWconst [k]` of an argument of at least the rotated width `w`: the machine's
rotate (`rotF51b`, `progStep_rorK51b`) on the whole word. -/
theorem lo_rorK51b (hA : AddrAgree ι) {op : Op} {t : Ty} {k : Int64} {aux : Option AuxRef}
    {as : As} {w ca : Nat} {x : Val} {X : BitVec 64} (hop : rorK51b? op = some (as, w))
    (hx : ValRel ι x X) (hfx : Fits ca x) (hw : w ≤ ca) (ht : t ≠ .bool) :
    Lo ι 64 (Arm64.evalPure op t k aux [x]) (rotF51b w X (Arm64.amt k)) := by
  rcases rorK51b?_some hop with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · show Lo ι 64 (Arm64.op1 t _ [x]) _
    refine lo_op1_51b ht fun a hr => ?_
    rw [reg64_51b hA hx hfx hw hr]
    rfl
  · show Lo ι 64 (Arm64.op1w t _ [x]) _
    simp only [Arm64.op1w]
    cases hrx : Arm64.reg32 x with
    | none => trivial
    | some a =>
      have ha : a = X.setWidth 32 := by
        unfold Arm64.reg32 at hrx
        cases hr : Arm64.reg x with
        | none => rw [hr] at hrx; cases hrx
        | some b =>
          rw [hr] at hrx
          cases hrx
          exact low_le51b (reg_low hA hx hfx hr) hw
      subst ha
      show Lo ι 64 (Arm64.res t _) _
      rw [res_int51b ht]
      rfl

/-- `ROR`, `RORW x y` of an `x` of at least the rotated width `w` and a `y` of at least 8 bits: the
machine's rotate (`rotF51b`, `progStep_ror51b`) on the whole word. -/
theorem lo_ror51b (hA : AddrAgree ι) {op : Op} {t : Ty} {k : Int64} {aux : Option AuxRef}
    {as : As} {w ca cb : Nat} {x y : Val} {X Y : BitVec 64} (hop : ror51b? op = some (as, w))
    (hx : ValRel ι x X) (hy : ValRel ι y Y) (hfx : Fits ca x) (hfy : Fits cb y) (hw : w ≤ ca)
    (hcb : 8 ≤ cb) (ht : t ≠ .bool) :
    Lo ι 64 (Arm64.evalPure op t k aux [x, y]) (rotF51b w X Y.toNat) := by
  rcases ror51b?_some hop with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · show Lo ι 64 (Arm64.op2 t _ [x, y]) _
    simp only [Arm64.op2]
    cases hrx : Arm64.reg x with
    | none => trivial
    | some a =>
      cases hry : Arm64.reg y with
      | none => trivial
      | some b =>
        have hm := mod64_low (by omega) (fits_le51b hfy hry) (reg_low hA hy hfy hry)
        rw [reg64_51b hA hx hfx hw hrx]
        show Lo ι 64 (Arm64.res t _) _
        rw [res_int51b ht]
        show (X.rotateRight (b.toNat % 64)).setWidth 64 = (rotF51b 64 X Y.toNat).setWidth 64
        simp only [rotF51b, ↓reduceIte, hm]
  · show Lo ι 64 (Arm64.op2w t _ [x, y]) _
    simp only [Arm64.op2w]
    cases hrx : Arm64.reg32 x with
    | none => trivial
    | some a =>
      cases hry : Arm64.reg32 y with
      | none => trivial
      | some b' =>
        have ha : a = X.setWidth 32 := by
          unfold Arm64.reg32 at hrx
          cases hr : Arm64.reg x with
          | none => rw [hr] at hrx; cases hrx
          | some u =>
            rw [hr] at hrx
            cases hrx
            exact low_le51b (reg_low hA hx hfx hr) hw
        have hb : b'.toNat % 32 = Y.toNat % 32 := by
          unfold Arm64.reg32 at hry
          cases hr : Arm64.reg y with
          | none => rw [hr] at hry; cases hry
          | some b =>
            rw [hr] at hry
            cases hry
            have hm := mod64_low (by omega) (fits_le51b hfy hr) (reg_low hA hy hfy hr)
            rw [setWidth32_toNat_mod51b, ← Nat.mod_mod_of_dvd b.toNat (by decide : 32 ∣ 64), hm,
              Nat.mod_mod_of_dvd Y.toNat (by decide : 32 ∣ 64)]
        subst ha
        show Lo ι 64 (Arm64.res t _) _
        rw [res_int51b ht]
        show (((X.setWidth 32).rotateRight (b'.toNat % 32)).setWidth 64).setWidth 64 =
          (rotF51b 32 X Y.toNat).setWidth 64
        simp only [rotF51b, hb]
        rfl

end Vals

/-! ## The cases -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- `MVN Rm SHIFT k, Rd`. -/
theorem g51b_mvnSh (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {typ ca c : Nat} {rm rd : Int} (hop : mvnSh51b? v.op = some typ)
    (hsz : v.args.size = 1) (hk0 : 0 ≤ v.auxInt.toInt) (hk64 : v.auxInt.toInt < 64)
    (hao : argObj lc v 0 = .ok (ca, rm)) (hro : resObj lc v = .ok (c, rd)) (h8 : 8 ≤ c)
    (hll : typ = 0 → c ≤ ca) (hrr : typ ≠ 0 → ca = 64)
    (hvs : OneAt2 psA j (.ofShape
      { as := .MVN, from_ := shiftA typ rm v.auxInt.toInt.toNat, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have halu := aluOp51b_mvnSh hop
  have hnp : v.op ≠ .Phi := aluOp51b_ne halu
  have ht3 : typ < 3 := by
    rcases mvnSh51b?_some hop with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨km, hkm, rfl, hkkm⟩ := objOf?_some hor0
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkm
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu51b hl htemp halu hs
  rw [arr1 hsz ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  rw [write_reg hvh hcv]
  have ht := cls_ne_bool hcv h8
  have hamt : Arm64.amt v.auxInt = v.auxInt.toInt.toNat := rfl
  have hk : v.auxInt.toInt.toNat < 64 := by omega
  have hlo := lo_mvnSh51b (k := v.auxInt) (aux := v.aux) (t := lc.ty v.id) hA hop hxv hxf
    (cls_le hcv) hll hrr ht
  rw [hamt] at hlo
  refine (op_reg2 (H := H) F hm hinv hj hj' hvs hd hkd hor (valRel_retypeL_lo hA hcv ht hlo)
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0' hok => ?_)).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨hpa, hf, -, ht', -⟩ := Shape.ok_eq hok
  rw [progStep_mvnSh51b ht3 hkm hkd hk (nextAddr_pcAt F.nodup hk0') hpa hf ht', wX_pc]
  rfl

/-- `SBFIZ $lsb, Rn, $width, Rd`. -/
theorem g51b_sbfiz (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {ca c : Nat} {rn rd : Int}
    (hop : v.op = .ARM64SBFIZ) (hsz1 : v.args.size = 1) (hk0 : 0 ≤ v.auxInt.toInt)
    (hk16 : v.auxInt.toInt < 2 ^ 16) (hao : argObj lc v 0 = .ok (ca, rn))
    (hro : resObj lc v = .ok (c, rd)) (h8 : 8 ≤ c) (hw0 : 0 < v.auxInt.toInt % 256)
    (hw64 : v.auxInt.toInt % 256 ≤ 64) (hw : v.auxInt.toInt % 256 ≤ ca ∨ c ≤ ca)
    (hvs : OneAt2 psA j
      ⟨sbfizOK (v.auxInt.toInt / 256) (v.auxInt.toInt % 256) rn rd, "SBFIZ"⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have halu : AluOp51b v.op := by unfold AluOp51b; simp [hop]
  have hnp : v.op ≠ .Phi := aluOp51b_ne halu
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu51b hl htemp halu hs
  rw [arr1 hsz1 ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  rw [write_reg hvh hcv, hop]
  have ht := cls_ne_bool hcv h8
  refine (op_reg2 (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_retypeL_lo hA hcv ht (lo_sbfiz51b hA hxv hxf hk0 hw0 hw64 hw ht))
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0' hok => ?_)).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨has, hf, hr, ht', -, -, xr, hrest⟩ := sbfizOK_spec hok
  rw [progStep_sbfiz51b hkn hkd (by omega) (by omega) (by omega) (nextAddr_pcAt F.nodup hk0') has
    hf hr ht' hrest, wX_pc]
  rfl

/-- `ROR`/`RORW $k, Rn, Rd`. -/
theorem g51b_rorK (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {w ca c : Nat} {rn rd : Int} (hop : rorK51b? v.op = some (as, w))
    (hsz : v.args.size = 1) (hao : argObj lc v 0 = .ok (ca, rn)) (hro : resObj lc v = .ok (c, rd))
    (h8 : 8 ≤ c) (hw : w ≤ ca) (hk0 : 0 ≤ v.auxInt.toInt)
    (hvs : OneAt2 psA j
      (.ofShape { as, from_ := constA v.auxInt.toInt, reg := rn, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have halu := aluOp51b_rorK hop
  have hnp : v.op ≠ .Phi := aluOp51b_ne halu
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu51b hl htemp halu hs
  rw [arr1 hsz ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  rw [write_reg hvh hcv]
  have ht := cls_ne_bool hcv h8
  refine (op_reg2 (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_retypeL_lo hA hcv ht ((lo_rorK51b hA hop hxv hxf hw ht).mono (cls_le hcv)))
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0' hok => ?_)).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨hpa, hf, hr, ht', -⟩ := Shape.ok_eq hok
  rw [progStep_rorK51b hop hkn hkd hk0 (nextAddr_pcAt F.nodup hk0') hpa hf hr ht', wX_pc]
  rfl

/-- `ROR`/`RORW Rm, Rn, Rd`. -/
theorem g51b_ror (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {w ca cb c : Nat} {rn rm rd : Int} (hop : ror51b? v.op = some (as, w))
    (hsz : v.args.size = 2) (hao : argObj lc v 0 = .ok (ca, rn)) (hbo : argObj lc v 1 = .ok (cb, rm))
    (hro : resObj lc v = .ok (c, rd)) (h8 : 8 ≤ c) (hw : w ≤ ca) (hcb : 8 ≤ cb)
    (hvs : OneAt2 psA j (.ofShape { as, from_ := regA rm, reg := rn, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have halu := aluOp51b_ror hop
  have hnp : v.op ≠ .Phi := aluOp51b_ne halu
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
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu51b hl htemp halu hs
  rw [arr2 hsz ha0 ha1] at hargv
  obtain rfl := mapM_res_two hargv hx hy
  rw [write_reg hvh hcv]
  have ht := cls_ne_bool hcv h8
  refine (op_reg2 (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_retypeL_lo hA hcv ht ((lo_ror51b hA hop hxv hyv hxf hyf hw hcb ht).mono (cls_le hcv)))
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0' hok => ?_)).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨hpa, hf, hr, ht', -⟩ := Shape.ok_eq hok
  rw [progStep_ror51b hop hkn hkm hkd (nextAddr_pcAt F.nodup hk0') hpa hf hr ht', wX_pc]
  rfl

end Cases

/-! ## One value -/

/-- One value of G51b's kinds: `vk50_step`'s conclusion for `VK51b` (no run premise), with the
empty upper-bit table after it. -/
theorem vk51b_step {env : Env} {H : Hooks} {lc : LocCtx} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)}
    (F : Facts lc sym text az ez ps.toList ret E) (hVK : VK51b lc v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E s' bid (i + 1) m' ∧ G3Inv E lc (kStep lc K v) s' ∧ UOKL m' (uStep35 lc L v) := by
  have hR := kread_of_reads hreads
  have fin : AluOp51b v.op → ∀ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' →
      LocMatch E s' bid (i + 1) m' → CoreInv E.ι (StkAt E) (kStep lc K v).get s' →
      SlotInv lc s' →
      ∃ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
        LocMatch E s' bid (i + 1) m' ∧ G3Inv E lc (kStep lc K v) s' ∧
        UOKL m' (uStep35 lc L v) := fun halu m' h1 h2 h3 h4 => by
    refine ⟨m', h1, h2, ⟨h3, h4⟩, ?_⟩
    rw [uStep35_alu51b halu]
    intro e he
    cases he
  cases hVK with
  | mvnSh hop hsz hk0 hk hao hro h8 hll hrr =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4⟩ := g51b_mvnSh (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hk0 hk hao hro h8 hll hrr hvs
      htemp hs
    exact fin (aluOp51b_mvnSh hop) m' h1 h2 h3 h4
  | sbfiz hop hsz hk0 hk16 hao hro h8 hw0 hw64 hw =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4⟩ := g51b_sbfiz (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hk0 hk16 hao hro h8 hw0 hw64 hw
      hvs htemp hs
    exact fin (by unfold AluOp51b; simp [hop]) m' h1 h2 h3 h4
  | rorK hop hsz hao hro h8 hw hk0 hk =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4⟩ := g51b_rorK (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hro h8 hw hk0 hvs htemp hs
    exact fin (aluOp51b_rorK hop) m' h1 h2 h3 h4
  | ror hop hsz hao hbo hro h8 hw hcb =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4⟩ := g51b_ror (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hbo hro h8 hw hcb hvs htemp hs
    exact fin (aluOp51b_ror hop) m' h1 h2 h3 h4

end GoFV.Proof.Gen
