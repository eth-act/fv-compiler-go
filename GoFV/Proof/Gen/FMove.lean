import GoFV.Proof.Gen.G43
import GoFV.Gen.Check44

variable [GoFV.SSA.Sem.Addrs]

/-!
# Float moves: the V registers under `runProg` and `LocMatch` (`docs/plans/proofs3.md` §4, G44)

The machine side of slice G44 (`GoFV/Gen/Check44.lean`):

* `progStep` of the `FMOVD`/`FMOVS` forms genssa emits for G44's values, with symbolic registers
  `REG_F0 + k` (`V k`) and `REG_R0 + k` (`X k`): `Fs, Fd` (`progStep_fmovVV`), `Rn, Fd`
  (`progStep_fmovXV`), `Fn, Rd` (`progStep_fmovVX`), `$c, Fd` (`progStep_fconst`, the bits
  `fconstBits`), a load at an address (`progStep_floadAt`) and a store (`progStep_fstoreAt`);
  `fmovPre_of` is `Progs3`'s `movPre` for the `movMem` opcodes of the V registers;
* `LocMatch` across a V register write (`locMatch_setRegV`), and a value whose one Prog writes
  its V register (`op_regV`, `op_reg2W` for `wV`: the X registers are unchanged);
* the value relations: a register value of class `c` read at a float shape is unchanged
  (`fvalRel_retypeL`), so a float argument in a V register is related to it (`arg_relV`);
  `FValRel` depends only on the low `c` bits (`fvalRel_low`), gives `ValRel` of the low 64 bits
  (`valRel_of_fvalRel`), and follows from `ValRel` for an integer under `AddrAgree`
  (`fvalRel_of_valRel`).
-/

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

namespace GoFV.Proof.Gen

/-! ## Bits -/

/-- `maskN n` keeps the low `8n` bits. -/
theorem maskN_low {n : Nat} (hn : n = 4 ∨ n = 8) (X : BitVec 64) :
    (ProgOp.maskN n X).setWidth (8 * n) = X.setWidth (8 * n) := by
  rcases hn with rfl | rfl
  · show ((X &&& BitVec.ofNat 64 (2 ^ 32 - 1)).setWidth 32) = X.setWidth 32
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_and, BitVec.getLsbD_ofNat,
      Nat.testBit_two_pow_sub_one]
    simp [hi, show i < 64 by omega]
  · rfl

theorem setWidth128_64 (X : BitVec 64) : (X.setWidth 128).setWidth 64 = X := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

theorem fpIdx?_f0 {k : Nat} (hk : k < 32) : ProgOp.fpIdx? (REG_F0 + k) = some k := by
  have h : (REG_F0 ≤ REG_F0 + k && REG_F0 + k < REG_V0 + 32) = true := by
    show (decide ((8224 : Int) ≤ 8224 + k) && decide ((8224 : Int) + k < 8256 + 32)) = true
    simp; omega
  simp only [ProgOp.fpIdx?, h, ite_true, Option.some.injEq]
  omega

theorem ctx_v_f0 {c : ProgCtx} {k : Nat} (hk : k < 32) :
    c.v (REG_F0 + k) = .ok (c.s.v (BitVec.ofNat 5 k)) := by
  simp only [ProgCtx.v, fpIdx?_f0 hk]
  rfl

theorem eff_wV_f0 {e : Eff} {k : Nat} {val : BitVec 128} (hk : k < 32) :
    e.wV (REG_F0 + k) val = .ok { e with v := (k, val) :: e.v } := by
  simp only [Eff.wV, fpIdx?_f0 hk]
  rfl

private def fmovPre (name : String) : Prop :=
  name ∉ ["TEXT", "FUNCDATA", "PCDATA", "NOP"] ∧
  ProgOp.baseOf name ProgOp.binNames = none ∧ ProgOp.baseOf name ["CMP", "CMN", "TST"] = none ∧
  ProgOp.baseOf name ["NEG", "NEGS", "MVN", "NGC", "NGCS"] = none ∧
  ProgOp.baseOf name ["CLZ", "RBIT", "REV", "REV16", "REV32"] = none ∧
  ProgOp.baseOf name ["MADD", "MSUB"] = none ∧
  ProgOp.baseOf name ["UBFX", "SBFX", "UBFIZ", "SBFIZ", "BFI", "BFXIL"] = none ∧
  ProgOp.baseOf name ["EXTR"] = none ∧
  ProgOp.baseOf name ["CSEL", "CSINC", "CSINV", "CSNEG"] = none ∧
  ProgOp.baseOf name ["CSET", "CSETM"] = none

private theorem fmovPre_of {name : String} {n : Nat} {sg : Bool}
    (hm : ProgOp.movMem name = some (n, sg, true)) : fmovPre name := by
  unfold ProgOp.movMem at hm
  split at hm <;> (try cases hm) <;> simp (config := { decide := true }) [fmovPre]

/-- A register move of floats, `FMOVD`/`FMOVS Fs, Fd`. -/
private theorem eff_fmovVV {c : ProgCtx} {n ka kd : Nat} (hka : ka < 32) (hkd : kd < 32)
    (hm : ProgOp.movMem c.p.as.name = some (n, false, true)) (hf : c.p.from_ = regA (REG_F0 + ka))
    (ht : c.p.to = regA (REG_F0 + kd)) :
    progEffect c = .ok { v := [(kd, (ProgOp.maskN n ((c.s.v (BitVec.ofNat 5 ka)).setWidth 64)).setWidth 128)] } := by
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := fmovPre_of hm
  unfold progEffect
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, hm, hf, ht, regA, fpIdx?_f0 hka, fpIdx?_f0 hkd,
    ctx_v_f0 hka, eff_wV_f0 hkd]
  rfl

/-- An integer register to a float register, `FMOVD`/`FMOVS Rn, Fd`. -/
private theorem eff_fmovXV {c : ProgCtx} {n ka kd : Nat} (hka : ka < 32) (hkd : kd < 32)
    (hm : ProgOp.movMem c.p.as.name = some (n, false, true)) (hf : c.p.from_ = regA (REG_R0 + ka))
    (ht : c.p.to = regA (REG_F0 + kd)) :
    progEffect c = .ok { v := [(kd, (ProgOp.maskN n (c.s.rX (BitVec.ofNat 5 ka))).setWidth 128)] } := by
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := fmovPre_of hm
  unfold progEffect
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, hm, hf, ht, regA, fpIdx?_r0 hka, fpIdx?_f0 hkd,
    ctx_x_r0 hka, eff_wV_f0 hkd]
  rfl

/-- A float register to an integer register, `FMOVD`/`FMOVS Fn, Rd`. -/
private theorem eff_fmovVX {c : ProgCtx} {n ka kd : Nat} (hka : ka < 32) (hkd : kd < 32)
    (hm : ProgOp.movMem c.p.as.name = some (n, false, true)) (hf : c.p.from_ = regA (REG_F0 + ka))
    (ht : c.p.to = regA (REG_R0 + kd)) :
    progEffect c = .ok (effWd {} kd (ProgOp.maskN n ((c.s.v (BitVec.ofNat 5 ka)).setWidth 64))) := by
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := fmovPre_of hm
  unfold progEffect
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, hm, hf, ht, regA, fpIdx?_f0 hka, fpIdx?_r0 hkd,
    ctx_v_f0 hka]
  exact eff_wX_dest hkd

/-- The bits `FMOVD`/`FMOVS $c, Fd` writes for an `FCONST` operand of `float64` bits `bits`
(`ProgOp.fconst`): the bits, or their rounding to single precision for the 4-byte `FMOVS`. -/
def fconstBits (n : Nat) (bits : UInt64) : BitVec 128 :=
  if n = 4 then
    (GoFV.IEEE.convert GoFV.IEEE.Fmt.b64 GoFV.IEEE.Fmt.b32 .rne (BitVec.ofNat 64 bits.toNat)).setWidth 128
  else (BitVec.ofNat 64 bits.toNat).setWidth 128

/-- A float constant, `FMOVD`/`FMOVS $c, Fd`. -/
private theorem eff_fconst {c : ProgCtx} {n kd : Nat} {bits : UInt64} (hkd : kd < 32)
    (hm : ProgOp.movMem c.p.as.name = some (n, false, true))
    (hf : c.p.from_ = { type := .FCONST, val := .float bits }) (ht : c.p.to = regA (REG_F0 + kd)) :
    progEffect c = .ok { v := [(kd, fconstBits n bits)] } := by
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := fmovPre_of hm
  unfold progEffect
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, hm, hf, ht, regA, eff_wV_f0 hkd]
  by_cases h4 : n = 4
  · subst h4; rfl
  · have : (n == 4) = false := by simpa using h4
    simp only [this, fconstBits, h4, ProgOp.fconst]
    rfl

/-- A float load from `a`. -/
private theorem eff_fload {c : ProgCtx} {n kd : Nat} {a : BitVec 64} (hkd : kd < 32)
    (hm : ProgOp.movMem c.p.as.name = some (n, false, true)) (hf : c.p.from_.type = .MEM)
    (hma : c.mem c.p.from_ = .ok (a, none)) (ht : c.p.to = regA (REG_F0 + kd)) :
    progEffect c = .ok { loads := [(a, n)], v := [(kd, (readMem c.s.mem a n).setWidth 128)] } := by
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := fmovPre_of hm
  unfold progEffect
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, hm, hf, hma, ht, regA, Eff.ld, ↓reduceIte,
    eff_wV_f0 hkd]
  rfl

/-- A float store of `V ks` to `a`. -/
private theorem eff_fstore {c : ProgCtx} {n ks : Nat} {a : BitVec 64} (hks : ks < 32)
    (hm : ProgOp.movMem c.p.as.name = some (n, false, true)) (hf : c.p.from_ = regA (REG_F0 + ks))
    (ht : c.p.to.type = .MEM) (hma : c.mem c.p.to = .ok (a, none)) :
    progEffect c = .ok { stores := [(a, n, (c.s.v (BitVec.ofNat 5 ks)).toNat % 2 ^ (8 * n))] } := by
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := fmovPre_of hm
  unfold progEffect
  simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, hm, hf, ht, hma, regA, ctx_v_f0 hks, ↓reduceIte]
  rfl

private theorem isSkip_ofF {p : Prog} {n : Nat} {sg : Bool}
    (hm : ProgOp.movMem p.as.name = some (n, sg, true)) : p.isSkip = false := by
  have h := (fmovPre_of hm).1
  unfold Prog.isSkip
  split <;> rename_i has <;> (try rfl) <;> rw [has] at h <;> exact absurd (by decide) h

theorem effV_apply {kd : Nat} {q : BitVec 128} {s : MState} {next : BitVec 64} :
    ({ v := [(kd, q)] } : Eff).apply s next = { s.wV (BitVec.ofNat 5 kd) q with pc := next } := by
  simp only [Eff.apply, List.foldr]
  rfl

variable {L : Link} {p : Prog} {s : MState} {next : BitVec 64}

/-- `FMOVD`/`FMOVS Fs, Fd`: the low `n` bytes of `V ka`. -/
theorem progStep_fmovVV {n ka kd : Nat} (hka : ka < 32) (hkd : kd < 32)
    (hn : L.nextAddr p.id = some next) (hm : ProgOp.movMem p.as.name = some (n, false, true))
    (hf : p.from_ = regA (REG_F0 + ka)) (ht : p.to = regA (REG_F0 + kd)) :
    progStep L p s = .ok { s.wV (BitVec.ofNat 5 kd)
      ((ProgOp.maskN n ((s.v (BitVec.ofNat 5 ka)).setWidth 64)).setWidth 128) with pc := next } := by
  rw [progStep_eq hn (isSkip_ofF hm) (eff_fmovVV (c := ⟨L, s, p⟩) hka hkd hm hf ht) rfl, effV_apply]

/-- `FMOVD`/`FMOVS Rn, Fd`: the low `n` bytes of `X ka`. -/
theorem progStep_fmovXV {n ka kd : Nat} (hka : ka < 32) (hkd : kd < 32)
    (hn : L.nextAddr p.id = some next) (hm : ProgOp.movMem p.as.name = some (n, false, true))
    (hf : p.from_ = regA (REG_R0 + ka)) (ht : p.to = regA (REG_F0 + kd)) :
    progStep L p s = .ok { s.wV (BitVec.ofNat 5 kd)
      ((ProgOp.maskN n (s.rX (BitVec.ofNat 5 ka))).setWidth 128) with pc := next } := by
  rw [progStep_eq hn (isSkip_ofF hm) (eff_fmovXV (c := ⟨L, s, p⟩) hka hkd hm hf ht) rfl, effV_apply]

/-- `FMOVD`/`FMOVS Fn, Rd`: the low `n` bytes of `V ka`. -/
theorem progStep_fmovVX {n ka kd : Nat} (hka : ka < 32) (hkd : kd < 32)
    (hn : L.nextAddr p.id = some next) (hm : ProgOp.movMem p.as.name = some (n, false, true))
    (hf : p.from_ = regA (REG_F0 + ka)) (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      (ProgOp.maskN n ((s.v (BitVec.ofNat 5 ka)).setWidth 64)) with pc := next } := by
  rw [progStep_eq hn (isSkip_ofF hm) (eff_fmovVX (c := ⟨L, s, p⟩) hka hkd hm hf ht)
    (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]), wd_apply hkd]

/-- `FMOVD`/`FMOVS $c, Fd` (`fconstBits`). -/
theorem progStep_fconst {n kd : Nat} {bits : UInt64} (hkd : kd < 32)
    (hn : L.nextAddr p.id = some next) (hm : ProgOp.movMem p.as.name = some (n, false, true))
    (hf : p.from_ = { type := .FCONST, val := .float bits }) (ht : p.to = regA (REG_F0 + kd)) :
    progStep L p s = .ok { s.wV (BitVec.ofNat 5 kd) (fconstBits n bits) with pc := next } := by
  rw [progStep_eq hn (isSkip_ofF hm) (eff_fconst (c := ⟨L, s, p⟩) hkd hm hf ht) rfl, effV_apply]

/-- A float load of `n` bytes at `a` outside the nil page into `V kd`, whatever the memory operand
that denotes `a`. -/
theorem progStep_floadAt {n kd : Nat} {a : BitVec 64} (hkd : kd < 32)
    (hn : L.nextAddr p.id = some next) (hm : ProgOp.movMem p.as.name = some (n, false, true))
    (hf : p.from_.type = .MEM) (hma : (ProgCtx.mk L s p).mem p.from_ = .ok (a, none))
    (ht : p.to = regA (REG_F0 + kd)) (hnil : nilPage a = false) :
    progStep L p s = .ok { s.wV (BitVec.ofNat 5 kd) ((readMem s.mem a n).setWidth 128) with
      pc := next } := by
  rw [progStep_eq hn (isSkip_ofF hm) (eff_fload (c := ⟨L, s, p⟩) hkd hm hf hma ht)
    (by simp [Eff.nilAccess?, List.find?, hnil])]
  simp only [Eff.apply, List.foldr]
  rfl

/-- A float store of the low `n` bytes of `V ks` at `a` outside the nil page. -/
theorem progStep_fstoreAt {n ks : Nat} {a : BitVec 64} (hks : ks < 32)
    (hn : L.nextAddr p.id = some next) (hm : ProgOp.movMem p.as.name = some (n, false, true))
    (hf : p.from_ = regA (REG_F0 + ks)) (ht : p.to.type = .MEM)
    (hma : (ProgCtx.mk L s p).mem p.to = .ok (a, none)) (hnil : nilPage a = false) :
    progStep L p s = .ok { s with
      mem := writeMem s.mem a n (BitVec.ofNat (8 * n) ((s.v (BitVec.ofNat 5 ks)).toNat % 2 ^ (8 * n))),
      pc := next } := by
  rw [progStep_eq hn (isSkip_ofF hm) (eff_fstore (c := ⟨L, s, p⟩) hks hm hf ht hma)
    (by simp [Eff.nilAccess?, List.find?, hnil])]
  rfl

/-! ## V registers in `LocMatch` -/

theorem objV?_some {r : Nat} {k : GoFV.Arm64.Reg} (h : objV? r = some k) :
    31 ≤ r ∧ r < 63 ∧ k = BitVec.ofNat 5 (r - 31) := by
  unfold objV? at h
  split at h
  · cases h; exact ⟨by omega, by omega, rfl⟩
  · cases h

theorem objV?_inj {r r' : Nat} {k : GoFV.Arm64.Reg} (h : objV? r = some k) (h' : objV? r' = some k) :
    r = r' := by
  obtain ⟨h1, h2, rfl⟩ := objV?_some h
  obtain ⟨h1', h2', he⟩ := objV?_some h'
  have := congrArg BitVec.toNat he
  simp at this
  omega

theorem objX?_none_of_V {r : Nat} {k : GoFV.Arm64.Reg} (h : objV? r = some k) : objX? r = none := by
  obtain ⟨h1, -, -⟩ := objV?_some h
  unfold objX?
  simp only [show ¬ r < 18 by omega, show ¬ r < 26 by omega, show ¬ r < 29 by omega, ↓reduceIte]

/-- Writing a V register (`setReg` on `runLoc`'s side, `wV` on the machine's) with values related
by `VRel` keeps `LocMatch`, at any PC. -/
theorem locMatch_setRegVR {E : MatchEnv} {s : LocState} {b : ID} {i : Nat}
    {m : GoFV.Arm64.MState} (h : LocMatch E s b i m) {r : Nat} {k : GoFV.Arm64.Reg} {x : Val}
    {q : BitVec 128} (hrk : objV? r = some k) (hx : VRel E.ι x q) {b' : ID} {i' : Nat} :
    LocMatch E (s.setReg r x) b' i' { m.wV k q with pc := E.pcOf b' i' } := by
  have hr31 := (objV?_some hrk).1
  have hrz : r ≠ zeroReg := by unfold zeroReg; omega
  refine ⟨?_, h.flags, h.slots, h.mem, h.frame, rfl⟩
  intro r' v hv
  by_cases hrr : r' = r
  · subst hrr
    simp only [LocState.setReg] at hv
    split at hv
    · rename_i hlt
      simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hlt
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt hlt.1] at hv
      simp only [Option.some.injEq] at hv
      subst hv
      refine ⟨fun k' hk' => (by rw [objX?_none_of_V hrk] at hk'; cases hk'), fun k' hk' => ?_⟩
      rw [hrk] at hk'
      cases hk'
      simpa [GoFV.Arm64.MState.wV] using hx
    · rename_i hlt
      simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, not_and,
        Decidable.not_not] at hlt
      have := (Array.getElem?_eq_some_iff.1 hv).1
      exact absurd (hlt this) hrz
  · have hv' : s.regs[r']? = some v := by
      simp only [LocState.setReg] at hv
      split at hv
      · rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (Ne.symm hrr)] at hv
        exact hv
      · exact hv
    obtain ⟨h1, h2⟩ := h.regs r' v hv'
    refine ⟨fun k' hk' => h1 k' hk', fun k' hk' => ?_⟩
    have : k' ≠ k := by
      intro he; subst he; exact hrr (objV?_inj hk' hrk)
    simp only [GoFV.Arm64.MState.wV, this, ↓reduceIte]
    exact h2 k' hk'

/-- `locMatch_setRegVR` for a float (`FValRel`). -/
theorem locMatch_setRegV {E : MatchEnv} {s : LocState} {b : ID} {i : Nat} {m : GoFV.Arm64.MState}
    (h : LocMatch E s b i m) {r : Nat} {k : GoFV.Arm64.Reg} {x : Val} {q : BitVec 128}
    (hrk : objV? r = some k) (hx : FValRel x q) {b' : ID} {i' : Nat} :
    LocMatch E (s.setReg r x) b' i' { m.wV k q with pc := E.pcOf b' i' } :=
  locMatch_setRegVR h hrk (VRel.of_fval hx)

/-- A V register's content of a class (`FitsW`, no blob) is related by `FValRel`. -/
theorem vrel_fvalW {ι : Blk → Option (BitVec 64)} {x : Val} {q : BitVec 128} {c : Nat}
    (h : VRel ι x q) (hf : FitsW c x) : FValRel x q :=
  VRel.fval h fun bs he => by subst he; exact hf

/-- A register value of class `c` read at a float shape of class `c` is unchanged. -/
theorem fvalRel_retypeL {x : Val} {q : BitVec 128} {c : Nat} {t : Ty} (hx : FValRel x q)
    (hf : Fits c x) (ht : fTy t = true) (hc : cls t = some c) : FValRel (x.retypeL t) q := by
  have hw : ∃ w : Width, t = .int w ∧ (w = .w32 ∨ w = .w64) := by
    cases t with
    | int w => cases w <;> simp_all [fTy]
    | _ => simp [fTy] at ht
  obtain ⟨w, rfl, hw⟩ := hw
  simp only [GoFV.Gen.Check.cls, Option.some.injEq] at hc
  subst hc
  cases x with
  | poison => rw [retypeL_poison]; trivial
  | int w' y =>
    have hf' : w'.bits = w.bits := hf
    have hww : w' = w := by
      rcases hw with rfl | rfl <;> cases w' <;> simp_all [Width.bits]
    subst hww
    have hr : (Val.int w' y).retypeL (.int w') = .int w' y := by
      rcases hw with rfl | rfl <;>
        simp only [Val.retypeL, Val.widen, Val.retype, Width.bits, Nat.lt_irrefl, Nat.le_refl,
          ↓reduceIte, BitVec.setWidth_eq]
    rw [hr]
    exact hx
  | _ => exact absurd hx id

/-- A V register content read at a float shape of a class it allows (`FitsW`): its low bits. -/
theorem fvalRel_retypeLW {x : Val} {q : BitVec 128} {c : Nat} {t : Ty} (hx : FValRel x q)
    (hf : FitsW c x) (ht : fTy t = true) (hc : cls t = some c) : FValRel (x.retypeL t) q := by
  have hw : ∃ w : Width, t = .int w ∧ (w = .w32 ∨ w = .w64) := by
    cases t with
    | int w => cases w <;> simp_all [fTy]
    | _ => simp [fTy] at ht
  obtain ⟨w, rfl, -⟩ := hw
  simp only [GoFV.Gen.Check.cls, Option.some.injEq] at hc
  subst hc
  cases x with
  | poison => rw [retypeL_poison]; trivial
  | int w' y =>
    have hle : w.bits ≤ w'.bits := by
      have hf : kNarrow w.bits w'.bits = true := hf
      revert hf; cases w <;> cases w' <;> decide
    rw [retypeL_int_low y hle]
    have hx : q.setWidth w'.bits = y := hx
    show q.setWidth w.bits = y.setWidth w.bits
    rw [← hx, BitVec.setWidth_setWidth_of_le _ hle]
  | _ => exact absurd hx id

/-- A value related to a V register is `poison` or an integer of its class. -/
theorem fval_cases {x : Val} {q : BitVec 128} {c : Nat} (hx : FValRel x q) (hf : Fits c x) :
    x = .poison ∨ ∃ w y, x = .int w y ∧ w.bits = c := by
  cases x with
  | poison => exact .inl rfl
  | int w y => exact .inr ⟨w, y, rfl, hf⟩
  | _ => exact absurd hx id

/-- A value of class `c ≤ 64` related to `q` is related to every `q'` with the same low `c`
bits. -/
theorem fvalRel_low {x : Val} {q q' : BitVec 128} {c : Nat} (hx : FValRel x q) (hf : Fits c x)
    (hq : q'.setWidth c = q.setWidth c) : FValRel x q' := by
  rcases fval_cases hx hf with rfl | ⟨w, y, rfl, hw⟩
  · trivial
  · have hq' : q'.setWidth w.bits = q.setWidth w.bits := by subst hw; exact hq
    show q'.setWidth w.bits = y
    rw [hq']
    exact hx

/-- A value related to a V register is related, as a register, to its low 64 bits. -/
theorem valRel_of_fvalRel {ι : Blk → Option (BitVec 64)} {x : Val} {q : BitVec 128}
    (hx : FValRel x q) : ValRel ι x (q.setWidth 64) := by
  cases x with
  | poison => trivial
  | int w y =>
    have hx' : q.setWidth w.bits = y := hx
    cases w
    case w64 => exact .inl hx'
    all_goals
      show (q.setWidth 64).setWidth _ = y
      rw [BitVec.setWidth_setWidth_of_le _ (by decide)]
      exact hx'
  | _ => exact absurd hx id

/-- An integer or `poison` related, as a register, to `Y`, is related to a V register whose low
64 bits are `Y` (the injection agrees with the Phase 1 addresses, `valRel_i64`). -/
theorem fvalRel_of_valRel {ι : Blk → Option (BitVec 64)} (hA : AddrAgree ι) {x : Val}
    {Y : BitVec 64} {q : BitVec 128} (hx : ValRel ι x Y) (hnp : ∀ p, x ≠ .ptr p)
    (hnb : ∀ b, x ≠ .bool b) (hq : q.setWidth 64 = Y) : FValRel x q := by
  cases x with
  | poison => trivial
  | int w y =>
    show q.setWidth w.bits = y
    cases w
    case w64 =>
      rw [valRel_i64 hA hx] at hq
      exact hq
    all_goals
      have hx' : Y.setWidth _ = y := hx
      rw [← BitVec.setWidth_setWidth_of_le q (by decide : _ ≤ 64), hq]
      exact hx'
  | bool b => exact absurd rfl (hnb b)
  | ptr p => exact absurd rfl (hnp p)
  | _ => exact absurd hx id

section Machine

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s : LocState} {b : ID} {i : Nat} {m : MState}

/-- A value whose one Prog writes its V register `V kd` with `q` (`op_reg2W` for a V register):
the X registers are unchanged. -/
theorem op_regV {P : BitVec 64 → Prop} {K K' : Nat → Option Nat}
    (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι P K s osp) {j j' : Nat}
    (hj : E.pcOf b i = pcAt text psA.toList j)
    (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j') {pat : Pat} (hone : OneAt2 psA j pat j')
    {r c kd : Nat} {x : Val} {q : BitVec 128} (hrk : objV? r = some (BitVec.ofNat 5 kd))
    (hx : FValRel x q) (hfx : Fits c x) (hKL : KLe K' (kSet K r (some c)))
    (hstep : ∀ k (hk : k < psA.toList.length), pat.ok psA.toList[k] = true →
      progStep (Link.byId sym text az ez psA.toList) psA.toList[k]
          { m with pc := pcAt text psA.toList k } =
        .ok { m.wV (BitVec.ofNat 5 kd) q with pc := pcAt text psA.toList (k + 1) }) :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E (s.setReg r x) b (i + 1) m' ∧ CoreInv E.ι P K' (s.setReg r x) osp ∧
      m'.x = m.x := by
  obtain ⟨k, rfl, hk, hok, hstar⟩ := pstar_oneAt2 (H := H) F.nodup F.lt F.ret hone m
  rw [pc_eta hm hj] at hstar
  have hlm := locMatch_setRegV hm hrk hx (b' := b) (i' := i + 1)
  rw [hj'] at hlm
  exact ⟨_, hstar.tail (pstep_at F.nodup F.lt F.ret hk rfl (hstep k hk hok)), hlm,
    (core_setReg hinv hfx).mono hKL, rfl⟩

/-- A register argument in a V register, read at its float shape: related to the V register and
of its class. -/
theorem arg_relV (hl : lc.ctx.f.lowered = true) (hm : LocMatch E s b i m)
    {P : BitVec 64 → Prop} {K : Nat → Option Nat} (hinv : CoreInv E.ι P K s osp) {a r c : Nat}
    {k : GoFV.Arm64.Reg} (hh : lc.home a = some (.reg r)) (hft : fTy (lc.ty a) = true)
    (hc : cls (lc.ty a) = some c) (hK : K r = some c) (hobj : objV? r = some k) :
    ∃ x, s.read lc a = .ok x ∧ FValRel x (m.v k) ∧ Fits c x := by
  refine ⟨_, read_reg hl hh hc, ?_, fits_retypeL hc _⟩
  have hrz : r ≠ zeroReg := by have := (objV?_some hobj).1; unfold zeroReg; omega
  simp only [LocState.reg, beq_iff_eq, hrz, ↓reduceIte]
  cases hv : s.regs[r]? with
  | none => simp only [Option.getD_none, retypeL_poison]; trivial
  | some v =>
    simp only [Option.getD_some]
    have hfit := hinv.regs r v c hrz hv hK
    exact fvalRel_retypeLW (vrel_fvalW ((hm.regs r v hv).2 k hobj) hfit) hfit hft hc

end Machine

end GoFV.Proof.Gen
