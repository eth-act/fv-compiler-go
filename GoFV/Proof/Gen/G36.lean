import GoFV.Proof.Gen.G35
import GoFV.Proof.Gen.Spec36

/-!
# Soundness of the genssa validator's slice G36: register shifts, shifted adds and subtracts, `TST`
(`docs/plans/proofs3.md` §4)

`g36_value`, `g36_term`, `g36_nilPanic`, `g36_boundsPanic`: `g35_value`'s, `g35_term`'s,
`g35_nilPanic`'s and `g35_boundsPanic`'s statements over `checkG36`, carrying the upper-bit
invariant `UOKL` of G35's table `uL35` alike.

`runLoc` runs the G36 ops as `Arm64.evalPure` of the arguments read from their homes
(`stepLoc_alu36`). `SLL`, `SRL`, `SRA x y` are `Arm64.op2` of a shift by `y` modulo 64
(`evalPure_sh36`, `shF36`), which the machine's `LSL`/`LSR`/`ASR Rm, Rn, Rd` compute on the
registers (`dp2Op`, `progStep_sh36`); the amount reads only the low 6 bits of `y`'s register,
which a class of at least 8 bits relates (`mod64_low`), and a left shift's low bits only the low
bits of `x` (G27's `shl_low`; `lo_sh36`). The shifted adds and subtracts are Phase 1's `addSh`/
`subSh` (`evalPure_shOp36`): `addP` of `x` and the shifted (negated) register of `y`, which the
machine's `ADD`/`SUB Rm SHIFT k, Rn, Rd` computes through G27's shifted operand (`progStep_shOp36`,
`lo_shOp36`, with `ADD`'s pointer case, `lo_addP`). `TST Rm, Rn` sets `ANDS`' flags of the two
registers (`progStep_tst36`), which `TST`'s are on 64-bit arguments (`flagsRel_tst36`). The G36 ops
empty the upper-bit table (`uStep35_alu36`). On a function with no arm64 op, `checkG36` is
`checkG33` (`checkG33_of_36`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The ops -/

/-- The word function of a register shift of G36. -/
def shF36 : As → BitVec 64 → BitVec 64 → BitVec 64
  | .LSL => fun x y => x <<< (y.toNat % 64)
  | .LSR => fun x y => x >>> (y.toNat % 64)
  | _ => fun x y => x.sshiftRight (y.toNat % 64)

/-- The word function of a shifted add or subtract of G36, on the shifted register. -/
def shOpF36 : As → BitVec 64 → BitVec 64 → BitVec 64
  | .ADD => (· + ·)
  | _ => (· - ·)

/-- Phase 1's shifted add or subtract. -/
def shOpV36 (as : As) (typ : Nat) (t : Ty) (k : Int64) (argv : List Val) : Val :=
  if as = .ADD then Arm64.addSh t (shK typ) k argv else Arm64.subSh t (shK typ) k argv

theorem sh36?_some {op : Op} {as : As} (h : sh36? op = some as) :
    op = .ARM64SLL ∧ as = .LSL ∨ op = .ARM64SRL ∧ as = .LSR ∨ op = .ARM64SRA ∧ as = .ASR := by
  unfold sh36? at h
  split at h <;> (try cases h) <;> simp

theorem shOp36?_some {op : Op} {as : As} {typ : Nat} (h : shOp36? op = some (as, typ)) :
    op = .ARM64ADDshiftRL ∧ as = .ADD ∧ typ = 1 ∨ op = .ARM64ADDshiftRA ∧ as = .ADD ∧ typ = 2 ∨
      op = .ARM64SUBshiftLL ∧ as = .SUB ∧ typ = 0 ∨ op = .ARM64SUBshiftRL ∧ as = .SUB ∧ typ = 1 ∨
      op = .ARM64SUBshiftRA ∧ as = .SUB ∧ typ = 2 := by
  unfold shOp36? at h
  split at h <;> (try cases h) <;> simp

/-- `Arm64.evalPure` of a register shift: `op2` of its word function. -/
theorem evalPure_sh36 {op : Op} {as : As} (h : sh36? op = some as) (t : Ty) (k : Int64)
    (aux : Option AuxRef) (argv : List Val) :
    Arm64.evalPure op t k aux argv = Arm64.op2 t (shF36 as) argv := by
  rcases sh36?_some h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-- `Arm64.evalPure` of a shifted add or subtract: `addSh`/`subSh` of its shift. -/
theorem evalPure_shOp36 {op : Op} {as : As} {typ : Nat} (h : shOp36? op = some (as, typ)) (t : Ty)
    (k : Int64) (aux : Option AuxRef) (argv : List Val) :
    Arm64.evalPure op t k aux argv = shOpV36 as typ t k argv := by
  rcases shOp36?_some h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> rfl

/-- The ops of G36. -/
def AluOp36 (op : Op) : Prop :=
  op = .ARM64SLL ∨ op = .ARM64SRL ∨ op = .ARM64SRA ∨ op = .ARM64ADDshiftRL ∨
    op = .ARM64ADDshiftRA ∨ op = .ARM64SUBshiftLL ∨ op = .ARM64SUBshiftRL ∨
    op = .ARM64SUBshiftRA ∨ op = .ARM64TST

theorem aluOp36_sh {op : Op} {as : As} (h : sh36? op = some as) : AluOp36 op := by
  unfold AluOp36
  rcases sh36?_some h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp

theorem aluOp36_shOp {op : Op} {as : As} {typ : Nat} (h : shOp36? op = some (as, typ)) :
    AluOp36 op := by
  unfold AluOp36
  rcases shOp36?_some h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp

theorem aluOp36_ne {op : Op} (h : AluOp36 op) :
    op ≠ .Phi ∧ op ≠ .ARM64MOVDnop ∧ op ≠ .ARM64MOVDreg ∧ op ≠ .ARM64LoweredNilCheck ∧
      pbOp op = false := by
  unfold AluOp36 at h
  rcases h with h | h | h | h | h | h | h | h | h <;> subst h <;>
    exact ⟨nofun, nofun, nofun, nofun, rfl⟩

/-- A G36 op empties G35's table. -/
theorem uStep35_alu36 {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value}
    (hop : AluOp36 v.op) : uStep35 lc L v = [] := by
  obtain ⟨-, hn1, hn2, -, -⟩ := aluOp36_ne hop
  have hl : loadOp? v.op = none := by
    unfold AluOp36 at hop
    rcases hop with h | h | h | h | h | h | h | h | h <;> rw [h] <;> rfl
  have hp : pairOp35 lc v = false := by
    unfold AluOp36 at hop
    simp only [pairOp35, Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne]
    rcases hop with h | h | h | h | h | h | h | h | h <;>
      (rw [h]; exact ⟨nofun, .inl (by decide)⟩)
  have hk : keep34 v = false := by
    unfold AluOp36 at hop
    unfold keep34 keep31
    rcases hop with h | h | h | h | h | h | h | h | h <;> simp [h, keepOp31, keepOp34]
  have hk31 : keep31 v = false := by
    simp only [keep34, Bool.or_eq_false_iff] at hk
    exact hk.1
  have hue : uEntry lc v = none := by
    have : narrowLd? lc v = none := by
      unfold narrowLd?
      have hi : loadIdxOp? v.op = none := by
        unfold AluOp36 at hop
        rcases hop with h | h | h | h | h | h | h | h | h <;> rw [h] <;> rfl
      rw [hl, hi]
    simp only [uEntry, this]
  rw [uStep35_other (ldEntry35_none hl) hp, uStep34_other hk, uStep31_other hk31,
    uStepL_other hue hn1 hn2]

/-! ## `runLoc` -/

section Steps

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

/-- The ops of G36: `Arm64.evalPure` on the arguments read from their homes. -/
theorem stepLoc_alu36 (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : AluOp36 v.op) (h : stepLoc env lc s v = .ok s') :
    ∃ argv, v.args.toList.mapM (s.read lc) = .ok argv ∧
      s' = s.write lc v.id ((Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux argv).retypeL
        (lc.ty v.id)) := by
  unfold AluOp36 at hop
  rcases hop with hop | hop | hop | hop | hop | hop | hop | hop | hop <;>
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

private theorem nLSL : As.LSL.name = "LSL" := rfl
private theorem nLSR : As.LSR.name = "LSR" := rfl
private theorem nASR : As.ASR.name = "ASR" := rfl
private theorem nADD : As.ADD.name = "ADD" := rfl
private theorem nSUB : As.SUB.name = "SUB" := rfl

/-- `LSL`/`LSR`/`ASR Rm, Rn, Rd`: `X kn` shifted by `X km` modulo 64. -/
theorem progStep_sh36 {op : Op} {as : As} {kn km kd : Nat} (has : sh36? op = some as)
    (hkn : kn < 32) (hkm : km < 32) (hkd : kd < 32)
    (hn : L.nextAddr p.id = some next) (hpa : p.as = as) (hf : p.from_ = regA (REG_R0 + km))
    (hr : p.reg = REG_R0 + kn) (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      (shF36 as (s.rX (BitVec.ofNat 5 kn)) (s.rX (BitVec.ofNat 5 km))) with pc := next } := by
  have hrn := rn_reg (c := ⟨L, s, p⟩) hr
  have he : progEffect ⟨L, s, p⟩ = .ok (effWd {} kd
      (shF36 as (s.rX (BitVec.ofNat 5 kn)) (s.rX (BitVec.ofNat 5 km)))) := by
    rcases sh36?_some has with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
    · unfold progEffect
      simp (config := { decide := true }) only [hpa, nLSL, nLSR, nASR, hf, ht, hrn, regA,
        ProgOp.baseOf, ↓reduceIte, ProgOp.binNames, ctx_src_reg hkn, ctx_src_reg hkm]
      simp only [ProgOp.binOp, dp2Op_lsl, dp2Op_lsr, dp2Op_asr, shF36]
      simp only [eff_wX_dest hkd]
      by_cases h : kd = 31 <;> simp [effWd, h] <;> rfl
  have hsk : p.isSkip = false := by
    rcases sh36?_some has with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [Prog.isSkip, hpa]
  rw [progStep_eq hn hsk he (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]),
    wd_apply hkd]

/-- `ADD`/`SUB Rm SHIFT k, Rn, Rd`: `X kn` plus or minus `X km` shifted by `k`. -/
theorem progStep_shOp36 {as : As} {typ kn km kd k : Nat} (has : as = .ADD ∨ as = .SUB)
    (ht3 : typ < 3) (hkn : kn < 32) (hkm : km < 32) (hkd : kd < 32) (hk : k < 64)
    (hn : L.nextAddr p.id = some next) (hpa : p.as = as)
    (hf : p.from_ = shiftA typ (REG_R0 + km) k) (hr : p.reg = REG_R0 + kn)
    (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      (shOpF36 as (s.rX (BitVec.ofNat 5 kn))
        (Sem.Arm64.Shift.apply (shK typ) (s.rX (BitVec.ofNat 5 km)) k)) with pc := next } := by
  have hrn := rn_reg (c := ⟨L, s, p⟩) hr
  have he : progEffect ⟨L, s, p⟩ = .ok (effWd {} kd (shOpF36 as (s.rX (BitVec.ofNat 5 kn))
      (Sem.Arm64.Shift.apply (shK typ) (s.rX (BitVec.ofNat 5 km)) k))) := by
    rcases has with rfl | rfl <;>
    · unfold progEffect
      simp (config := { decide := true }) only [hpa, nADD, nSUB, hf, ht, hrn, regA, shiftA,
        ProgOp.baseOf, ↓reduceIte, ProgOp.binNames, ctx_src_reg hkn]
      rw [← shiftA, ctx_src_shift ht3 hkm hk]
      simp only [ProgOp.binOp, addSub_add, addSub_sub, shOpF36]
      simp only [eff_wX_dest hkd]
      by_cases h : kd = 31 <;> simp [effWd, h] <;> rfl
  have hsk : p.isSkip = false := by
    rcases has with rfl | rfl <;> simp [Prog.isSkip, hpa]
  rw [progStep_eq hn hsk he
    (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]), wd_apply hkd]

/-- `TST Rm, Rn`: `ANDS`' flags of `X kn` and `X km`. -/
theorem progStep_tst36 {kn km : Nat} (hkn : kn < 32) (hkm : km < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .TST) (hf : p.from_ = regA (REG_R0 + km))
    (hr : p.reg = REG_R0 + kn) :
    progStep L p s = .ok { s with
      nzcv := logicFlags (s.rX (BitVec.ofNat 5 kn) &&& s.rX (BitVec.ofNat 5 km)), pc := next } := by
  have hname : As.name .TST = "TST" := rfl
  have he : progEffect ⟨L, s, p⟩ =
      .ok { flags := some (logicFlags (s.rX (BitVec.ofNat 5 kn) &&& s.rX (BitVec.ofNat 5 km))) } := by
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, hr, hf, regA, ProgOp.baseOf,
      ↓reduceIte, ProgOp.binNames, ctx_src_reg hkn, ctx_src_reg hkm, ProgOp.binOp, logical_flags]
    rfl
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he rfl]
  rfl

end Progs

/-! ## Values -/

section Vals

variable {ι : Blk → Option (BitVec 64)}

private theorem res_int36 {t : Ty} (ht : t ≠ .bool) (r : BitVec 64) :
    Arm64.res t r = .int .w64 r := by
  cases t <;> first | rfl | exact absurd rfl ht

private theorem fits_le36 {c : Nat} {x : Val} {r : BitVec 64} (hf : Fits c x)
    (hr : Arm64.reg x = some r) : c ≤ 64 := by
  cases x with
  | int w v => have : w.bits = c := hf; subst this; cases w <;> decide
  | bool b => have : c = 1 := hf; omega
  | ptr p => have : c = 64 := hf; omega
  | _ => cases hr

private theorem low_le36 {c ca : Nat} {a b : BitVec 64} (h : a.setWidth ca = b.setWidth ca)
    (hc : c ≤ ca) : a.setWidth c = b.setWidth c := by
  have := congrArg (BitVec.setWidth c) h
  simpa only [BitVec.setWidth_setWidth_of_le _ hc] using this

private theorem sw_neg36 {c : Nat} (hc : c ≤ 64) {y Y : BitVec 64}
    (hy : y.setWidth c = Y.setWidth c) : (-y).setWidth c = (-Y).setWidth c := by
  rw [BitVec.neg_eq_neg_one_mul y, BitVec.neg_eq_neg_one_mul Y, BitVec.setWidth_mul _ _ hc,
    BitVec.setWidth_mul _ _ hc, hy]

/-- A shift amount modulo 64 reads only the low 6 bits: a register agreeing with `Y` on its low
`cb ≥ 6` bits gives the same amount. -/
theorem mod64_low {cb : Nat} {b Y : BitVec 64} (h6 : 6 ≤ cb) (hcb : cb ≤ 64)
    (h : b.setWidth cb = Y.setWidth cb) : b.toNat % 64 = Y.toNat % 64 := by
  have h1 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_setWidth] at h1
  have hd : 64 ∣ 2 ^ cb := by
    have : 2 ^ cb = 2 ^ 6 * 2 ^ (cb - 6) := by rw [← Nat.pow_add]; congr 1; omega
    rw [this]
    exact Nat.dvd_mul_right _ _
  rw [← Nat.mod_mod_of_dvd b.toNat hd, ← Nat.mod_mod_of_dvd Y.toNat hd, h1]

/-- A register shift `x op y`: `y` of class `cb ≥ 8`; `x` of class `ca` at least the result's class
`c` for `LSL`, of 64 bits otherwise. -/
theorem lo_sh36 (hA : AddrAgree ι) {t : Ty} {as : As} {x y : Val} {X Y : BitVec 64}
    {c ca cb : Nat} (hx : ValRel ι x X) (hy : ValRel ι y Y) (hfx : Fits ca x) (hfy : Fits cb y)
    (hcb : 8 ≤ cb) (hll : as = .LSL → c ≤ ca) (hr : as ≠ .LSL → ca = 64) (ht : t ≠ .bool) :
    Lo ι c (Arm64.op2 t (shF36 as) [x, y]) (shF36 as X Y) := by
  simp only [Arm64.op2]
  cases hrx : Arm64.reg x with
  | none => trivial
  | some a =>
    cases hry : Arm64.reg y with
    | none => trivial
    | some b =>
      show Lo ι c (Arm64.res t (shF36 as a b)) _
      rw [res_int36 ht]
      show (shF36 as a b).setWidth c = (shF36 as X Y).setWidth c
      have hm := mod64_low (by omega) (fits_le36 hfy hry) (reg_low hA hy hfy hry)
      have hxa := reg_low hA hx hfx hrx
      by_cases hl : as = .LSL
      · subst hl
        simp only [shF36]
        rw [hm]
        exact shl_low (low_le36 hxa (hll rfl))
      · have hca := hr hl
        subst hca
        have ha : a = X := by simpa only [BitVec.setWidth_eq] using hxa
        subst ha
        unfold shF36
        split <;> simp only [hm]

/-- A shifted add or subtract `x ± (y SHIFT k)`: `x` of class `ca ≥ c`; `y` of class `cb ≥ c` for
a left shift, of 64 bits otherwise. -/
theorem lo_shOp36 (hA : AddrAgree ι) {t : Ty} {as : As} {typ : Nat} {k : Int64} {x y : Val}
    {X Y : BitVec 64} {c ca cb : Nat} (hx : ValRel ι x X) (hy : ValRel ι y Y) (hfx : Fits ca x)
    (hfy : Fits cb y) (has : as = .ADD ∨ as = .SUB) (hca64 : c ≤ 64) (hca : c ≤ ca)
    (hll : typ = 0 → c ≤ cb) (hrr : typ ≠ 0 → cb = 64) (ht : t ≠ .bool) (hk : Arm64.amt k < 64) :
    Lo ι c (shOpV36 as typ t k [x, y])
      (shOpF36 as X (Sem.Arm64.Shift.apply (shK typ) Y (Arm64.amt k))) := by
  -- the shifted register of `y`, agreeing with `Y`'s on the low `c` bits (all of them at `c = 64`)
  have hsh : ∀ b, Arm64.reg y = some b →
      (Arm64.shifted (shK typ) k b).setWidth c =
        (Sem.Arm64.Shift.apply (shK typ) Y (Arm64.amt k)).setWidth c ∧
      (c < 64 ∨ Arm64.shifted (shK typ) k b = Sem.Arm64.Shift.apply (shK typ) Y (Arm64.amt k)) := by
    intro b hry
    have hb := reg_low hA hy hfy hry
    have hcb64 := fits_le36 hfy hry
    unfold Arm64.shifted
    by_cases h0 : typ = 0
    · subst h0
      have hcb := hll rfl
      have hs : ∀ z : BitVec 64, Sem.Arm64.Shift.apply (shK 0) z (Arm64.amt k) = z <<< Arm64.amt k := by
        intro z
        simp only [shK, Sem.Arm64.Shift.apply, Nat.mod_eq_of_lt hk]
      rw [hs, hs]
      refine ⟨shl_low (low_le36 hb hcb), ?_⟩
      rcases Nat.lt_or_ge c 64 with h | h
      · exact .inl h
      · right
        have : cb = 64 := by omega
        subst this
        have : b = Y := by simpa only [BitVec.setWidth_eq] using hb
        rw [this]
    · have hcb := hrr h0
      subst hcb
      have : b = Y := by simpa only [BitVec.setWidth_eq] using hb
      subst this
      exact ⟨rfl, .inr rfl⟩
  rcases has with rfl | rfl
  · show Lo ι c (Arm64.addSh t (shK typ) k [x, y]) _
    simp only [Arm64.addSh]
    cases hry : Arm64.reg y with
    | none => trivial
    | some b =>
      obtain ⟨h1, h2⟩ := hsh b hry
      exact lo_addP hA hx hfx hca64 hca ht h1 h2
  · show Lo ι c (Arm64.subSh t (shK typ) k [x, y]) _
    simp only [Arm64.subSh]
    cases hry : Arm64.reg y with
    | none => trivial
    | some b =>
      obtain ⟨h1, h2⟩ := hsh b hry
      show Lo ι c (Arm64.addP t x (-Arm64.shifted (shK typ) k b)) (X - _)
      rw [BitVec.sub_eq_add_neg]
      refine lo_addP hA hx hfx hca64 hca ht (sw_neg36 hca64 h1) ?_
      rcases h2 with h | h
      · exact .inl h
      · exact .inr (by rw [h])

/-- `TST x y` of two 64-bit arguments: the flags of the machine's `TST Rm, Rn`
(`progStep_tst36`), at the flags shape. -/
theorem flagsRel_tst36 (hA : AddrAgree ι) {t : Ty} {k : Int64} {aux : Option AuxRef} {x y : Val}
    {X Y : BitVec 64} (hx : ValRel ι x X) (hy : ValRel ι y Y) (hfx : Fits 64 x) (hfy : Fits 64 y) :
    FlagsRel ((Arm64.evalPure .ARM64TST t k aux [x, y]).retypeL Ty.flags)
      (logicFlags (X &&& Y)) := by
  refine (flags_retypeL ?_).1
  show FlagsRel (Arm64.flags2 (fun a b => logicFlags (a &&& b)) [x, y]) _
  simp only [Arm64.flags2]
  cases hrx : Arm64.reg x with
  | none => trivial
  | some a =>
    cases hry : Arm64.reg y with
    | none => trivial
    | some b =>
      have ha : a = X := by simpa only [BitVec.setWidth_eq] using reg_low hA hx hfx hrx
      have hb : b = Y := by simpa only [BitVec.setWidth_eq] using reg_low hA hy hfy hry
      subst ha; subst hb
      exact ⟨rfl, rfl, rfl, rfl⟩

end Vals

/-! ## The cases -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- `LSL`/`LSR`/`ASR Rm, Rn, Rd`. -/
theorem g36_sh (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {ca cb c : Nat} {rn rm rd : Int} (hop : sh36? v.op = some as)
    (hsz : v.args.size = 2) (hao : argObj lc v 0 = .ok (ca, rn)) (hbo : argObj lc v 1 = .ok (cb, rm))
    (hro : resObj lc v = .ok (c, rd)) (h8 : 8 ≤ c) (hcb : 8 ≤ cb) (hll : as = .LSL → c ≤ ca)
    (hrr : as ≠ .LSL → ca = 64)
    (hvs : OneAt2 psA j (.ofShape { as, from_ := regA rm, reg := rn, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have halu := aluOp36_sh hop
  have hnp : v.op ≠ .Phi := (aluOp36_ne halu).1
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
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu36 hl htemp halu hs
  rw [arr2 hsz ha0 ha1] at hargv
  obtain rfl := mapM_res_two hargv hx hy
  rw [write_reg hvh hcv, evalPure_sh36 hop]
  have ht := cls_ne_bool hcv h8
  refine (op_reg2 (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_retypeL_lo hA hcv ht (lo_sh36 hA hxv hyv hxf hyf hcb hll hrr ht))
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0' hok => ?_)).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨hpa, hf, hr, ht', -⟩ := Shape.ok_eq hok
  rw [progStep_sh36 hop hkn hkm hkd (nextAddr_pcAt F.nodup hk0') hpa hf hr ht', wX_pc]
  rfl

/-- `ADD`/`SUB Rm SHIFT k, Rn, Rd`. -/
theorem g36_shOp (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {typ ca cb c : Nat} {rn rm rd : Int} (hop : shOp36? v.op = some (as, typ))
    (hsz : v.args.size = 2) (hk0 : 0 ≤ v.auxInt.toInt) (hk64 : v.auxInt.toInt < 64)
    (hao : argObj lc v 0 = .ok (ca, rn)) (hbo : argObj lc v 1 = .ok (cb, rm))
    (hro : resObj lc v = .ok (c, rd)) (h8 : 8 ≤ c) (hca : c ≤ ca) (hll : typ = 0 → c ≤ cb)
    (hrr : typ ≠ 0 → cb = 64)
    (hvs : OneAt2 psA j (.ofShape
      { as, from_ := shiftA typ rm v.auxInt.toInt.toNat, reg := rn, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have halu := aluOp36_shOp hop
  have hnp : v.op ≠ .Phi := (aluOp36_ne halu).1
  have has : as = .ADD ∨ as = .SUB := by
    rcases shOp36?_some hop with ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩ <;>
      simp [h]
  have ht3 : typ < 3 := by
    rcases shOp36?_some hop with ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ | ⟨-, -, h⟩ <;>
      omega
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
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu36 hl htemp halu hs
  rw [arr2 hsz ha0 ha1] at hargv
  obtain rfl := mapM_res_two hargv hx hy
  rw [write_reg hvh hcv, evalPure_shOp36 hop]
  have ht := cls_ne_bool hcv h8
  have hamt : Arm64.amt v.auxInt = v.auxInt.toInt.toNat := rfl
  have hk : v.auxInt.toInt.toNat < 64 := by omega
  have hlo := lo_shOp36 (k := v.auxInt) hA hxv hyv hxf hyf has (cls_le hcv) hca hll hrr ht
    (by rw [hamt]; exact hk)
  rw [hamt] at hlo
  refine (op_reg2 (H := H) F hm hinv hj hj' hvs hd hkd hor (valRel_retypeL_lo hA hcv ht hlo)
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0' hok => ?_)).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨hpa, hf, hr, ht', -⟩ := Shape.ok_eq hok
  rw [progStep_shOp36 has ht3 hkn hkm hkd hk (nextAddr_pcAt F.nodup hk0') hpa hf hr ht', wX_pc]
  rfl

/-- `TST Rm, Rn` of two 64-bit arguments. -/
theorem g36_tst (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {rn rm : Int} (hop : v.op = .ARM64TST) (hsz : v.args.size = 2)
    (hfl : (lc.ty v.id).isFlags = true) (hhn : lc.home v.id = none)
    (hao : argObj lc v 0 = .ok (64, rn)) (hbo : argObj lc v 1 = .ok (64, rm))
    (hvs : OneAt2 psA j (.ofShape { as := .TST, from_ := regA rm, reg := rn }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have halu : AluOp36 v.op := by unfold AluOp36; simp [hop]
  have hnp : v.op ≠ .Phi := (aluOp36_ne halu).1
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hbo
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨km, hkm, rfl, hkkm⟩ := objOf?_some hor1
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨y, hy, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkkm
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu36 hl htemp halu hs
  rw [arr2 hsz ha0 ha1] at hargv
  obtain rfl := mapM_res_two hargv hx hy
  rw [write_flags hhn hfl, hop, isFlags_eq hfl]
  exact (op_flags F hm hinv hj hj' hvs (flagsRel_tst36 hA hxv hyv hxf hyf)
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun)) (fun k hk hok => by
      obtain ⟨has, hf, hr, -, -⟩ := Shape.ok_eq hok
      rw [progStep_tst36 hkn hkm (nextAddr_pcAt F.nodup hk) has hf hr] <;> rfl)).imp
    fun m' ⟨h1, h2, h3, _, _⟩ => ⟨h1, h2, h3, hsi⟩

end Cases

/-! ## The theorems -/

/-- One value of G36's kinds: `vk35_step`'s statement. -/
theorem vk36_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)}
    (hE : G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK36 lc g v kd)
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
  have fin : AluOp36 v.op → ∀ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' →
      LocMatch E s' bid (i + 1) m' → CoreInv E.ι (StkAt E) (kStep lc K v).get s' →
      SlotInv lc s' →
      ∃ E' m', E.Extends E' ∧ G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
        PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
        LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' ∧
        UOKL m' (uStep35 lc L v) := fun halu m' h1 h2 h3 h4 => by
    refine ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩, ?_⟩
    rw [uStep35_alu36 halu]
    intro e he
    cases he
  cases hVK with
  | g33 _ _ _ hVK33 =>
    exact vk35_step hE F hhome hcf hv hVK33 hvs htemp hj hj' hreads hm hinv hL hmem hpre hcall
      hcallz hicall hwb hclo hgetg hmeq hs
  | sh hop hsz hao hbo hro h8 hcb hll hrr =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4⟩ := g36_sh (H := H) F hm hinv.core hinv.slots
      (kread_of_reads hreads) (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hbo
      hro h8 hcb hll hrr hvs htemp hs
    exact fin (aluOp36_sh hop) m' h1 h2 h3 h4
  | shOp hop hsz hk0 hk hao hbo hro h8 hca hll hrr =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4⟩ := g36_shOp (H := H) F hm hinv.core hinv.slots
      (kread_of_reads hreads) (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hk0 hk
      hao hbo hro h8 hca hll hrr hvs htemp hs
    exact fin (aluOp36_shOp hop) m' h1 h2 h3 h4
  | tst hop hsz hfl hhn hao hbo =>
    obtain ⟨m', h1, h2, h3, h4⟩ := g36_tst (H := H) F hm hinv.core hinv.slots
      (kread_of_reads hreads) (knext_kStep fun _ => (hs_none hhn).noRegs) hj hj' hop hsz hfl hhn
      hao hbo hvs htemp hs
    exact fin (by unfold AluOp36; simp [hop]) m' h1 h2 h3 h4


/-- **G36, values.** `g35_value`'s statement over `checkG36`, carrying the upper-bit invariant
`UOKL` of G35's table `uL35` (started from `uIn35 lc bid`) from value `i` to value `i + 1`. -/
theorem g36_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG36 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
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
    obtain ⟨E', m', hx, hE', h1, h2, h3, -⟩ := g33_value (checkG33_of_36 hl hc) hE hbid hb hi hv
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
    checkG36_spec hl hc
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
  obtain ⟨htemp, hVK⟩ := vkind36_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  rw [kAt_succ hi hv]
  exact vk36_step hE0 F hhome hcf hv hVK hvs htemp hj hj' hreads hm hinv hu
    (fun x hop hx => movdOK35_spec hmovd hbid hb hi hv hop hx)
    hpre hcall hcallz hicall hwb hclo hgetg hmeq hs

/-- A nil check of G36's kinds is G7's. -/
theorem vk36_nil {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK36 lc g v kd)
    (hop : v.op = .ARM64LoweredNilCheck) : VK7 lc g v kd := by
  cases h with
  | g33 _ _ _ h => exact vk33_nil h hop
  | sh h => exact absurd hop (aluOp36_ne (aluOp36_sh h)).2.2.2.1
  | shOp h => exact absurd hop (aluOp36_ne (aluOp36_shOp h)).2.2.2.1
  | tst h => rw [hop] at h; cases h

/-- **G36, nil panics.** `g35_nilPanic`'s statement over `checkG36`. -/
theorem g36_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG36 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  cases hl : lc.ctx.f.lowered with
  | false => exact g33_nilPanic (checkG33_of_36 hl hc) hE hbid hb hi hv hop hm hinv hs
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, -⟩ :=
    checkG36_spec hl hc
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
  obtain ⟨-, hVK⟩ := vkind36_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases vk36_nil hVK hop with
  | g6 hne _ => exact absurd hop hne
  | nil _ hsz2 _ _ hao hma =>
    exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao hma hvs hs

/-- **G36, bounds panics.** `g35_boundsPanic`'s statement over `checkG36`, under `BoundsOK`. -/
theorem g36_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG36 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hbok : BoundsOK H g L ps.toList)
    (hs : stepLoc env lc s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    exact g33_boundsPanic (checkG33_of_36 hl hc) hE hbid hb hi hv hop hm hinv hbok hs
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, hsyms, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, hpb, -, -⟩ :=
    checkG36_spec hl hc
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
  obtain ⟨-, hVK⟩ := vkind36_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases hVK with
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

/-- **G36, terminators.** `g35_term`'s statement over `checkG36`, taking the upper-bit invariant of
G35's table at the block's end and giving it for the successor's start `uIn35 lc e.b`. -/
theorem g36_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG36 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s) (hpre : G1TermPre lc s blk)
    (hu : UOKL m (uL35 lc (uIn35 lc bid) blk blk.values.size))
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' ∧
      e.b ∈ lc.ctx.f.blocks.toList ∧ UOKL m' (uIn35 lc e.b) := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g33_term (checkG33_of_36 hl hc) hE hbid hb hm hinv hpre
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
    checkG36_spec hl hc
  obtain ⟨m', h1, h2, h3, h4, he, hx⟩ := termK_stepX hpcOf
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb hm hinv hpre ht
  refine ⟨m', h1, h2, h3, h4, fun x hxin => ?_⟩
  exact uok_of_x hx (hu x (uEdgesOK35_edge hedges hbid hb he x hxin))

end GoFV.Proof.Gen
