import GoFV.Proof.Gen.G31
import GoFV.Proof.Gen.Spec33

variable [GoFV.SSA.Sem.Addrs]

/-!
# Soundness of the genssa validator's slice G33: more single-instruction ops
(`docs/plans/proofs3.md` §4)

`g33_value`, `g33_term`, `g33_nilPanic`, `g33_boundsPanic`: `g31_value`'s, `g31_term`'s,
`g31_nilPanic`'s and `g31_boundsPanic`'s statements over `checkG33`, carrying the upper-bit
invariant `UOKL` of G31's table `uL31` alike.

`runLoc` runs `CLZ`, `REV`, `SRAconst`, `UBFIZ` and `CMNWconst` as `Arm64.evalPure` of the
arguments read from their homes (`stepLoc_alu33`). `CLZ`/`REV x` are `Arm64.op1` of `clz`/`rev`,
which the machine's `CLZ`/`REV Rm, Rd` compute on the whole register (`progStep_un33`), and `ASR
$k, Rn, Rd` shifts the register as `SRAconst [k]` does (`progStep_asrK`): on a 64-bit argument the
register is the machine word, so the results agree (`lo_op1_64`). `UBFIZ $lsb, Rn, $width, Rd`
moves the low `width` bits up by `lsb`, as `Arm64.ubfiz` of the auxint `lsb · 256 + width`
(`progStep_ubfiz`); bit `i` of the result is bit `i - lsb < width` of the argument, which lies
below the argument's class when `width` or the result's class does (`lo_ubfiz`). `CMNW $k, Rn` sets
the flags of the 32-bit `ADDS` of the low words (`progStep_cmnwConst`), which `CMNWconst [k]`'s
flags are on an argument of class at least 32 (`flagsRel_cmnwK`). The G33 ops are outside
`keep31`, so the table after them is empty (`uStep31_other`, `uStepL_other`). On a function with no
arm64 op, `checkG33` is `checkG31` (`checkG31_of_33`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The ops -/

/-- The word function of a unary op of G33. -/
def unF33 : As → BitVec 64 → BitVec 64
  | .CLZ => GoFV.SSA.Sem.Arm64.clz
  | _ => GoFV.SSA.Sem.Arm64.rev

theorem un33?_some {op : Op} {as : As} (h : un33? op = some as) :
    op = .ARM64CLZ ∧ as = .CLZ ∨ op = .ARM64REV ∧ as = .REV := by
  unfold un33? at h
  split at h <;> (try cases h) <;> simp

/-- `Arm64.evalPure` of a unary op of G33: `op1` of its word function. -/
theorem evalPure_un33 {op : Op} {as : As} (h : un33? op = some as) (t : Ty) (k : Int64)
    (aux : Option AuxRef) (argv : List Val) :
    Arm64.evalPure op t k aux argv = Arm64.op1 t (unF33 as) argv := by
  rcases un33?_some h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-- The ops of G33. -/
def AluOp33 (op : Op) : Prop :=
  op = .ARM64UBFIZ ∨ op = .ARM64CLZ ∨ op = .ARM64REV ∨ op = .ARM64SRAconst ∨
    op = .ARM64CMNWconst

theorem aluOp33_un {op : Op} {as : As} (h : un33? op = some as) : AluOp33 op := by
  unfold AluOp33
  rcases un33?_some h with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp

theorem aluOp33_ne {op : Op} (h : AluOp33 op) :
    op ≠ .Phi ∧ op ≠ .ARM64MOVDnop ∧ op ≠ .ARM64MOVDreg ∧ op ≠ .ARM64LoweredNilCheck ∧
      pbOp op = false := by
  unfold AluOp33 at h
  rcases h with h | h | h | h | h <;> subst h <;> exact ⟨nofun, nofun, nofun, nofun, rfl⟩

/-- A G33 op is none of the narrow loads (`narrowLd?`). -/
theorem narrowLd?_alu33 {lc : LocCtx} {v : Value} (hop : AluOp33 v.op) : narrowLd? lc v = none := by
  unfold AluOp33 at hop
  rcases hop with hop | hop | hop | hop | hop <;>
  · unfold narrowLd?; rw [hop]; rfl

/-- A G33 op is outside `keep31`. -/
theorem keep31_alu33 {v : Value} (hop : AluOp33 v.op) : keep31 v = false := by
  unfold AluOp33 at hop
  unfold keep31
  rcases hop with hop | hop | hop | hop | hop <;> simp [hop, keepOp31]

/-! ## `runLoc` -/

section Steps

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

/-- The ops of G33: `Arm64.evalPure` on the arguments read from their homes. -/
theorem stepLoc_alu33 (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : AluOp33 v.op) (h : stepLoc env lc s v = .ok s') :
    ∃ argv, v.args.toList.mapM (s.read lc) = .ok argv ∧
      s' = s.write lc v.id ((Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux argv).retypeL
        (lc.ty v.id)) := by
  unfold AluOp33 at hop
  rcases hop with hop | hop | hop | hop | hop <;>
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

private theorem nCLZ : As.CLZ.name = "CLZ" := rfl
private theorem nREV : As.REV.name = "REV" := rfl

/-- `CLZ`/`REV Rm, Rd`. -/
theorem progStep_un33 {op : Op} {as : As} {km kd : Nat} (has : un33? op = some as)
    (hkm : km < 32) (hkd : kd < 32)
    (hn : L.nextAddr p.id = some next) (hpa : p.as = as) (hf : p.from_ = regA (REG_R0 + km))
    (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd) (unF33 as (s.rX (BitVec.ofNat 5 km))) with
      pc := next } := by
  have he : progEffect ⟨L, s, p⟩ = .ok (effWd {} kd (unF33 as (s.rX (BitVec.ofNat 5 km)))) := by
    rcases un33?_some has with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · unfold progEffect
      simp (config := { decide := true }) only [hpa, nCLZ, hf, ht, regA, ProgOp.baseOf,
        ↓reduceIte, ProgOp.binNames, ctx_x_r0 hkm]
      simp only [bind, Except.bind, eff_wX_dest hkd]
      simp [dp1Op, sized, unF33]
    · unfold progEffect
      simp (config := { decide := true }) only [hpa, nREV, hf, ht, regA, ProgOp.baseOf,
        ↓reduceIte, ProgOp.binNames, ctx_x_r0 hkm]
      simp only [bind, Except.bind, eff_wX_dest hkd]
      simp [dp1Op, unF33]
  have hsk : p.isSkip = false := by
    rcases un33?_some has with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [Prog.isSkip, hpa]
  rw [progStep_eq hn hsk he (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]),
    wd_apply hkd]

/-- A shift by a constant (`ASR $k, Rn, Rd`, `op` named `nm`, at 64 bits). -/
private theorem eff_shiftK33 {c : ProgCtx} {kn kd : Nat} {k : Int} {nm : String} (hkn : kn < 32)
    (hkd : kd < 32) (hb : ProgOp.baseOf c.p.as.name ProgOp.binNames = some (nm, true))
    (hnm : ["LSL", "LSR", "ASR", "ROR"].contains nm = true) (hf : c.p.from_ = constA k)
    (hr : c.p.reg = REG_R0 + kn) (ht : c.p.to = regA (REG_R0 + kd)) :
    progEffect c = .ok (effWd {} kd
      (ProgOp.binOp nm true (c.s.rX (BitVec.ofNat 5 kn)) (BitVec.ofInt 64 k) false).1) := by
  have hrn := rn_reg (c := c) hr
  unfold progEffect
  simp only [hb, hf, constA, hnm, beq_self_eq_true, Bool.true_and, ↓reduceIte, hrn,
    ctx_src_reg hkn, ProgOp.trunc, ht, regA]
  exact eff_wX_dest hkd

theorem dp2Op_asr (x y : BitVec 64) : dp2Op true 10 x y = x.sshiftRight (y.toNat % 64) := by
  simp [dp2Op, sized, GoFV.SSA.Sem.Arm64.Shift.apply]

/-- `ASR $k, Rn, Rd` (`0 ≤ k`). -/
theorem progStep_asrK {kn kd : Nat} {k : Int} (hkn : kn < 32) (hkd : kd < 32) (hk : 0 ≤ k)
    (hn : L.nextAddr p.id = some next) (has : p.as = .ASR) (hf : p.from_ = constA k)
    (hr : p.reg = REG_R0 + kn) (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      ((s.rX (BitVec.ofNat 5 kn)).sshiftRight (k.toNat % 64)) with pc := next } := by
  have hb : ProgOp.baseOf p.as.name ProgOp.binNames = some ("ASR", true) := by
    rw [has]; simp (config := { decide := true })
  have he := eff_shiftK33 (c := ⟨L, s, p⟩) hkn hkd hb (by decide) hf hr ht
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
    (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]), wd_apply hkd]
  simp (config := { decide := true }) only [ProgOp.binOp, dp2Op_asr, ofInt_toNat_mod hk]

/-- `UBFIZ` of a bitfield auxint `lsb · 256 + width` (`width < 256`, the auxint below `2 ^ 63`). -/
theorem ubfiz_ofNat {lsb width : Nat} (hw : width < 256) (hk : lsb * 256 + width < 2 ^ 63)
    (x : BitVec 64) :
    GoFV.SSA.Sem.Arm64.ubfiz (Int64.ofNat (lsb * 256 + width)) x =
      (x &&& GoFV.SSA.Sem.Arm64.mask width) <<< lsb := by
  have h : (Int64.ofNat (lsb * 256 + width)).toInt = ((lsb * 256 + width : Nat) : Int) := by
    rw [Int64.toInt_ofNat_of_lt hk]
  simp only [GoFV.SSA.Sem.Arm64.ubfiz, GoFV.SSA.Sem.Arm64.bf, h, Int.toNat_natCast]
  rw [show (lsb * 256 + width) % 256 = width by omega, show (lsb * 256 + width) / 256 = lsb by omega]

/-- `UBFIZ $lsb, Rn, $width, Rd` (the operands `ubfizOK` fixes; `0 ≤ width < 256`, the auxint
`lsb · 256 + width` below `2 ^ 63`): the low `width` bits of `X kn` at bit `lsb`. -/
theorem progStep_ubfiz {kn kd x : Nat} {lsb width : Int} (hkn : kn < 32) (hkd : kd < 32)
    (hw0 : 0 ≤ width) (hw : width < 256) (hlw : lsb.toNat * 256 + width.toNat < 2 ^ 63)
    (hn : L.nextAddr p.id = some next) (has : p.as = .UBFIZ) (hf : p.from_ = constA lsb)
    (hr : p.reg = REG_R0 + kn) (ht : p.to = regA (REG_R0 + kd))
    (hrest : p.rest = #[(x, constA width)]) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      ((s.rX (BitVec.ofNat 5 kn) &&& GoFV.SSA.Sem.Arm64.mask width.toNat) <<< lsb.toNat) with
        pc := next } := by
  have hname : As.name .UBFIZ = "UBFIZ" := rfl
  have hrest0 : (ProgCtx.mk L s p).rest 0 = .ok (constA width) := by
    simp [ProgCtx.rest, hrest]
    rfl
  have hval : ProgOp.trunc true (GoFV.SSA.Sem.Arm64.ubfiz
      (Int64.ofNat (lsb.toNat * 256 + width.toNat)) (s.rX (BitVec.ofNat 5 kn))) =
      (s.rX (BitVec.ofNat 5 kn) &&& GoFV.SSA.Sem.Arm64.mask width.toNat) <<< lsb.toNat := by
    simp only [ProgOp.trunc, ↓reduceIte]
    exact ubfiz_ofNat (by omega) hlw _
  have he : progEffect ⟨L, s, p⟩ = .ok (effWd {} kd
      ((s.rX (BitVec.ofNat 5 kn) &&& GoFV.SSA.Sem.Arm64.mask width.toNat) <<< lsb.toNat)) := by
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
      ProgOp.binNames, hrest0, hf, hr, ht, constA, regA, ctx_x_r0 hkn, ctx_x_r0 hkd]
    rw [← hval]
    exact eff_wX_dest hkd
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
    (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]), wd_apply hkd]

/-- The flags of the 32-bit `ADDS`. -/
theorem addSub_addFlags32 (x y : BitVec 64) :
    (addSub false false x y).2 =
      (GoFV.SSA.Sem.addWithCarry (x.setWidth 32) (y.setWidth 32) false).2 := by
  simp [addSub, sizedF]

/-- `CMNW $k, Rn`: the flags of the 32-bit `ADDS` of the low words. -/
theorem progStep_cmnwConst {kn : Nat} {k : Int} (hkn : kn < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .CMNW) (hf : p.from_ = constA k)
    (hr : p.reg = REG_R0 + kn) :
    progStep L p s = .ok { s with
      nzcv := (GoFV.SSA.Sem.addWithCarry ((s.rX (BitVec.ofNat 5 kn)).setWidth 32)
        ((BitVec.ofInt 64 k).setWidth 32) false).2, pc := next } := by
  have hname : As.name .CMNW = "CMNW" := rfl
  have he : progEffect ⟨L, s, p⟩ = .ok { flags := some (GoFV.SSA.Sem.addWithCarry
      ((s.rX (BitVec.ofNat 5 kn)).setWidth 32) ((BitVec.ofInt 64 k).setWidth 32) false).2 } := by
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, hr, hf, ProgOp.baseOf, ↓reduceIte,
      ProgOp.binNames, ProgOp.endsS, ProgOp.chopS, ctx_src_reg32 hkn, ctx_src_const32,
      ProgOp.binOp, addSub_addFlags32]
    simp only [bind, Except.bind, pure, Except.pure, trunc_false_setWidth]
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he rfl]
  rfl

end Progs

/-! ## Values -/

section Vals

variable {ι : Blk → Option (BitVec 64)}

private theorem res_int33 {t : Ty} (ht : t ≠ .bool) (r : BitVec 64) :
    Arm64.res t r = .int .w64 r := by
  cases t <;> first | rfl | exact absurd rfl ht

private theorem low_of_le33 {c ca : Nat} {a b : BitVec 64} (h : a.setWidth ca = b.setWidth ca)
    (hc : c ≤ ca) : a.setWidth c = b.setWidth c := by
  have := congrArg (BitVec.setWidth c) h
  simpa only [BitVec.setWidth_setWidth_of_le _ hc] using this

private theorem bit_of_low33 {c i : Nat} {a b : BitVec 64} (h : a.setWidth c = b.setWidth c)
    (hi : i < c) : a.getLsbD i = b.getLsbD i := by
  have := congrArg (fun v => v.getLsbD i) h
  simpa only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and] using this

private theorem low_of_bits33 {c : Nat} {a b : BitVec 64}
    (h : ∀ i, i < c → i < 64 → a.getLsbD i = b.getLsbD i) : a.setWidth c = b.setWidth c := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth]
  by_cases h64 : i < 64
  · rw [h i hi h64]
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 64 ≤ i)]

/-- A unary op on the register of `x`, each register giving `Z` on the low `c` bits. -/
private theorem lo_op1_33 {t : Ty} {f : BitVec 64 → BitVec 64} {x : Val} {Z : BitVec 64} {c : Nat}
    (ht : t ≠ .bool) (hf : ∀ a, Arm64.reg x = some a → (f a).setWidth c = Z.setWidth c) :
    Lo ι c (Arm64.op1 t f [x]) Z := by
  simp only [Arm64.op1]
  cases hr : Arm64.reg x with
  | none => trivial
  | some a =>
    show Lo ι c (Arm64.res t (f a)) Z
    rw [res_int33 ht]
    exact hf a hr

/-- A unary op of a 64-bit argument: its register is the machine word. -/
theorem lo_op1_64 (hA : AddrAgree ι) {t : Ty} {f : BitVec 64 → BitVec 64} {x : Val}
    {X : BitVec 64} (hx : ValRel ι x X) (hfx : Fits 64 x) (ht : t ≠ .bool) :
    Lo ι 64 (Arm64.op1 t f [x]) (f X) := by
  refine lo_op1_33 ht fun a hr => ?_
  have h := reg_low hA hx hfx hr
  simp only [BitVec.setWidth_eq] at h
  rw [h]

/-- `UBFIZ [k]` (`k = lsb · 256 + width ≥ 0`) of an argument of class `ca` holding every bit it
reads (`width ≤ ca` or `c ≤ ca`): `UBFIZ $lsb, Rn, $width, Rd` (`progStep_ubfiz`) on the low `c`
bits. -/
theorem lo_ubfiz (hA : AddrAgree ι) {t : Ty} {k : Int64} {aux : Option AuxRef} {x : Val}
    {X : BitVec 64} {ca c : Nat} (hx : ValRel ι x X) (hfx : Fits ca x) (hk : 0 ≤ k.toInt)
    (hw : k.toInt % 256 ≤ ca ∨ c ≤ ca) (ht : t ≠ .bool) :
    Lo ι c (Arm64.evalPure .ARM64UBFIZ t k aux [x])
      ((X &&& Arm64.mask (k.toInt % 256).toNat) <<< (k.toInt / 256).toNat) := by
  show Lo ι c (Arm64.op1 t (Arm64.ubfiz k) [x]) _
  refine lo_op1_33 ht fun a hr => low_of_bits33 fun i hi h64 => ?_
  have hlow := reg_low hA hx hfx hr
  have h1 : k.toInt.toNat / 256 = (k.toInt / 256).toNat := by omega
  have h2 : k.toInt.toNat % 256 = (k.toInt % 256).toNat := by omega
  show ((a &&& Arm64.mask (k.toInt.toNat % 256)) <<< (k.toInt.toNat / 256)).getLsbD i = _
  rw [h1, h2]
  simp only [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_and, Arm64.mask, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one]
  by_cases hs : i < (k.toInt / 256).toNat
  · simp [hs]
  · by_cases hiw : i - (k.toInt / 256).toNat < (k.toInt % 256).toNat
    · rw [bit_of_low33 hlow (by rcases hw with hw | hw <;> omega)]
    · simp [hiw]

/-- The `W` register of an argument of class at least 32: none, or the machine word's low word. -/
private theorem reg32_eq33 (hA : AddrAgree ι) {x : Val} {X : BitVec 64} {ca : Nat}
    (hx : ValRel ι x X) (hf : Fits ca x) (hca : 32 ≤ ca) :
    Arm64.reg32 x = none ∨ Arm64.reg32 x = some (X.setWidth 32) := by
  unfold Arm64.reg32
  cases hr : Arm64.reg x with
  | none => exact .inl rfl
  | some a => exact .inr (congrArg some (low_of_le33 (reg_low hA hx hf hr) hca))

/-- `CMNWconst [k]` of an argument of class at least 32: the flags of the machine's
`CMNW $k, Rn` (`progStep_cmnwConst`, `k` the auxint). -/
theorem flagsRel_cmnwK (hA : AddrAgree ι) {t : Ty} {k : Int64} {aux : Option AuxRef} {x : Val}
    {X : BitVec 64} {ca : Nat} (hx : ValRel ι x X) (hfx : Fits ca x) (hca : 32 ≤ ca) :
    FlagsRel (Arm64.evalPure .ARM64CMNWconst t k aux [x])
      (GoFV.SSA.Sem.addWithCarry (X.setWidth 32) ((BitVec.ofInt 64 k.toInt).setWidth 32)
        false).2 := by
  show FlagsRel (Arm64.cmp1w (fun a => GoFV.SSA.Sem.addWithCarry a (Arm64.imm32 k) false) [x]) _
  rw [ofInt_setWidth32]
  rcases reg32_eq33 hA hx hfx hca with h | h <;>
    simp only [Arm64.cmp1w, h] <;> first | trivial | exact ⟨rfl, rfl, rfl, rfl⟩

end Vals

/-! ## The cases -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- `CLZ`/`REV Rm, Rd` of a 64-bit argument. -/
theorem g33_un (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {ca c : Nat} {rm rd : Int} (hop : un33? v.op = some as)
    (hsz : v.args.size = 1) (hao : argObj lc v 0 = .ok (ca, rm)) (hro : resObj lc v = .ok (c, rd))
    (h8 : 8 ≤ c) (hca : ca = 64)
    (hvs : OneAt2 psA j (.ofShape { as, from_ := regA rm, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      XW lc v m m' := by
  have hl := F.lowered
  have hA := F.addr
  have halu := aluOp33_un hop
  have hnp : v.op ≠ .Phi := (aluOp33_ne halu).1
  subst hca
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨km, hkm, rfl, hkkm⟩ := objOf?_some hor0
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkm
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu33 hl htemp halu hs
  rw [arr1 hsz ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  rw [write_reg hvh hcv, evalPure_un33 hop]
  have ht := cls_ne_bool hcv h8
  refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_retypeL_lo hA hcv ht ((lo_op1_64 hA hxv hxf ht).mono (cls_le hcv)))
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0' hok => ?_)).imp
    fun m' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, hsi, .inr ⟨r, kd, _, hvh, hor, h4⟩⟩
  obtain ⟨hpa, hf, -, ht', -⟩ := Shape.ok_eq hok
  rw [progStep_un33 hop hkm hkd (nextAddr_pcAt F.nodup hk0') hpa hf ht', wX_pc]
  rfl

/-- `ASR $k, Rn, Rd` of a 64-bit argument. -/
theorem g33_sra (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {ca c : Nat} {rn rd : Int} (hop : v.op = .ARM64SRAconst)
    (hsz : v.args.size = 1) (hao : argObj lc v 0 = .ok (ca, rn)) (hro : resObj lc v = .ok (c, rd))
    (h8 : 8 ≤ c) (hca : ca = 64) (hk0 : 0 ≤ v.auxInt.toInt) (hk : v.auxInt.toInt < 64)
    (hvs : OneAt2 psA j
      (.ofShape { as := .ASR, from_ := constA v.auxInt.toInt, reg := rn, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      XW lc v m m' := by
  have hl := F.lowered
  have hA := F.addr
  have halu : AluOp33 v.op := by unfold AluOp33; simp [hop]
  have hnp : v.op ≠ .Phi := (aluOp33_ne halu).1
  subst hca
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu33 hl htemp halu hs
  rw [arr1 hsz ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  rw [write_reg hvh hcv, hop]
  have ht := cls_ne_bool hcv h8
  have he : Arm64.evalPure .ARM64SRAconst (lc.ty v.id) v.auxInt v.aux [x] =
      Arm64.op1 (lc.ty v.id) (fun a => Arm64.Shift.ra.apply a (Arm64.amt v.auxInt)) [x] := rfl
  rw [he]
  refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_retypeL_lo hA hcv ht ((lo_op1_64 hA hxv hxf ht).mono (cls_le hcv)))
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0' hok => ?_)).imp
    fun m' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, hsi, .inr ⟨r, kd, _, hvh, hor, h4⟩⟩
  obtain ⟨hpa, hf, hr, ht', -⟩ := Shape.ok_eq hok
  rw [progStep_asrK hkn hkd hk0 (nextAddr_pcAt F.nodup hk0') hpa hf hr ht', wX_pc]
  rfl

/-- `UBFIZ $lsb, Rn, $width, Rd`. -/
theorem g33_ubfiz (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {ca c : Nat} {rn rd : Int}
    (hop : v.op = .ARM64UBFIZ) (hsz1 : v.args.size = 1) (hk0 : 0 ≤ v.auxInt.toInt)
    (hk16 : v.auxInt.toInt < 2 ^ 16) (hao : argObj lc v 0 = .ok (ca, rn))
    (hro : resObj lc v = .ok (c, rd)) (h8 : 8 ≤ c) (hw : v.auxInt.toInt % 256 ≤ ca ∨ c ≤ ca)
    (hvs : OneAt2 psA j
      ⟨ubfizOK (v.auxInt.toInt / 256) (v.auxInt.toInt % 256) rn rd, "UBFIZ"⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      XW lc v m m' := by
  have hl := F.lowered
  have hA := F.addr
  have halu : AluOp33 v.op := by unfold AluOp33; simp [hop]
  have hnp : v.op ≠ .Phi := (aluOp33_ne halu).1
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu33 hl htemp halu hs
  rw [arr1 hsz1 ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  rw [write_reg hvh hcv, hop]
  have ht := cls_ne_bool hcv h8
  refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_retypeL_lo hA hcv ht (lo_ubfiz hA hxv hxf hk0 hw ht))
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0' hok => ?_)).imp
    fun m' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, hsi, .inr ⟨r, kd, _, hvh, hor, h4⟩⟩
  obtain ⟨has, hf, hr, ht', -, -, xr, hrest⟩ := ubfizOK_spec hok
  rw [progStep_ubfiz hkn hkd (by omega) (by omega) (by omega) (nextAddr_pcAt F.nodup hk0') has hf
    hr ht' hrest, wX_pc]
  rfl

/-- `CMNW $k, Rn`. -/
theorem g33_cmnw (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {ca : Nat} {rn : Int}
    (hop : v.op = .ARM64CMNWconst) (hsz1 : v.args.size = 1) (hfl : (lc.ty v.id).isFlags = true)
    (hhn : lc.home v.id = none) (hao : argObj lc v 0 = .ok (ca, rn)) (hca : 32 ≤ ca)
    (hvs : OneAt2 psA j (.ofShape { as := .CMNW, from_ := constA v.auxInt.toInt, reg := rn }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      m'.x = m.x := by
  have hl := F.lowered
  have hA := F.addr
  have halu : AluOp33 v.op := by unfold AluOp33; simp [hop]
  have hnp : v.op ≠ .Phi := (aluOp33_ne halu).1
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu33 hl htemp halu hs
  rw [arr1 hsz1 ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  rw [write_flags hhn hfl, hop, isFlags_eq hfl]
  exact (op_flags F hm hinv hj hj' hvs (flags_retypeL (flagsRel_cmnwK hA hxv hxf hca)).1
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun)) (fun k hk hok => by
      obtain ⟨has, hf, hr, -, -⟩ := Shape.ok_eq hok
      rw [progStep_cmnwConst hkn (nextAddr_pcAt F.nodup hk) has hf hr] <;> rfl)).imp
    fun m' ⟨h1, h2, h3, _, h5⟩ => ⟨h1, h2, h3, hsi, h5⟩

end Cases

/-! ## The theorems -/

/-- One value of G33's kinds: `vk31_step`'s statement. -/
theorem vk33_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)}
    (hE : G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK33 lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s osp) (hL : UOKL m L)
    (hmem : ∀ x, (v.op = .ARM64MOVDnop ∨ v.op = .ARM64MOVDreg) → v.args[0]? = some x →
      ∃ r c, regHome? lc x = some r ∧ cls (lc.ty x) = some c ∧
        (r, c, lc.signOf lc.ctx.f.valueTab.size x) ∈ L)
    (hpre : G14Pre lc s v)
    (hcall : CallOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hcallz : CallOKZAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hicall : ICallOKAt osp H E (Link.byId sym text az ez ps.toList) ret lc s s' v m)
    (hwb : WbOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s v m) (hclo : CloOK E s v m)
    (hgetg : GetGOK E v) (hmeq : MemEqOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s v m)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp ∧
      UOKL m' (uStep31 lc L v) := by
  have fin : AluOp33 v.op → ∀ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' →
      LocMatch E s' bid (i + 1) m' → CoreInv E.ι (StkAt E) (kStep lc K v).get s' osp →
      SlotInv lc s' →
      ∃ E' m', E.Extends E' ∧ G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
        PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
        LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp ∧
        UOKL m' (uStep31 lc L v) := fun halu m' h1 h2 h3 h4 => by
    refine ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩, ?_⟩
    obtain ⟨-, hn1, hn2, -, -⟩ := aluOp33_ne halu
    rw [uStep31_other (keep31_alu33 halu),
      uStepL_other (by simp only [uEntry, narrowLd?_alu33 halu]) hn1 hn2]
    intro e he
    cases he
  cases hVK with
  | g32 _ _ _ _ hVK32 =>
    exact vk31_step hE F hhome hcf hv hVK32 hvs htemp hj hj' hreads hm hinv hL hmem hpre hcall
      hcallz hicall hwb hclo hgetg hmeq hs
  | un hop hsz hao hro h8 hca =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g33_un (H := H) F hm hinv.core hinv.slots
      (kread_of_reads hreads) (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hro
      h8 hca hvs htemp hs
    exact fin (aluOp33_un hop) m' h1 h2 h3 h4
  | ubfiz hop hsz hk0 hk16 hao hro h8 hw =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g33_ubfiz (H := H) F hm hinv.core hinv.slots
      (kread_of_reads hreads) (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hk0 hk16
      hao hro h8 hw hvs htemp hs
    exact fin (by unfold AluOp33; simp [hop]) m' h1 h2 h3 h4
  | sra hop hsz hao hro h8 hca hk0 hk =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g33_sra (H := H) F hm hinv.core hinv.slots
      (kread_of_reads hreads) (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hro
      h8 hca hk0 hk hvs htemp hs
    exact fin (by unfold AluOp33; simp [hop]) m' h1 h2 h3 h4
  | cmnw hop hsz hfl hhn hao hca =>
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g33_cmnw (H := H) F hm hinv.core hinv.slots
      (kread_of_reads hreads) (knext_kStep fun _ => (hs_none hhn).noRegs) hj hj' hop hsz hfl hhn
      hao hca hvs htemp hs
    exact fin (by unfold AluOp33; simp [hop]) m' h1 h2 h3 h4

/-- **G33, values.** `g31_value`'s statement over `checkG33`, carrying the upper-bit invariant
`UOKL` of G31's table `uL31` (started from `uIn lc bid`) from value `i` to value `i + 1`. -/
theorem g33_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG33 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s osp) (hu : UOKL m (uL31 lc (uIn lc bid) blk i))
    (hpre : G14Pre lc s v)
    (hcall : CallOKAt osp H E g L lc s s' v m) (hcallz : CallOKZAt osp H E g L lc s s' v m)
    (hicall : ICallOKAt osp H E L ret lc s s' v m)
    (hwb : WbOKAt osp H E g L lc s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hmeq : MemEqOKAt osp H E g L lc s v m) (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' osp ∧
      UOKL m' (uL31 lc (uIn lc bid) blk (i + 1)) := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    exact g31_value (checkG31_of_33 hl hc) hE hbid hb hi hv hen hm hinv hu hpre hcall hcallz
      hicall hwb hclo hgetg hmeq hs
  | true =>
  rw [uL31_succ hl hi hv]
  have hE0 := hE
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, hcf, hk, hlt, hnd, hblocks, -, hmovd, -⟩ :=
    checkG33_spec hl hc
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
  obtain ⟨htemp, hVK⟩ := vkind33_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  rw [kAt_succ hi hv]
  exact vk33_step hE0 F hhome hcf hv hVK hvs htemp hj hj' hreads hm hinv hu
    (fun x hop hx => movdOK31_spec hmovd hbid hb hi hv hop hx)
    hpre hcall hcallz hicall hwb hclo hgetg hmeq hs

/-- A nil check of G33's kinds is G7's. -/
theorem vk33_nil {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK33 lc g v kd)
    (hop : v.op = .ARM64LoweredNilCheck) : VK7 lc g v kd := by
  cases h with
  | g32 _ _ _ _ h => exact vk32_nil h hop
  | un h => exact absurd hop (aluOp33_ne (aluOp33_un h)).2.2.2.1
  | ubfiz h => rw [hop] at h; cases h
  | sra h => rw [hop] at h; cases h
  | cmnw h => rw [hop] at h; cases h

/-- **G33, nil panics.** `g31_nilPanic`'s statement over `checkG33`. -/
theorem g33_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG33 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s osp) (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  cases hl : lc.ctx.f.lowered with
  | false => exact g31_nilPanic (checkG31_of_33 hl hc) hE hbid hb hi hv hop hm hinv hs
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, -⟩ :=
    checkG33_spec hl hc
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
  obtain ⟨-, hVK⟩ := vkind33_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases vk33_nil hVK hop with
  | g6 hne _ => exact absurd hop hne
  | nil _ hsz2 _ _ hao hma =>
    exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao hma hvs hs

/-- **G33, bounds panics.** `g31_boundsPanic`'s statement over `checkG33`, under `BoundsOK`. -/
theorem g33_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG33 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s osp) (hbok : BoundsOK H g L ps.toList)
    (hs : stepLoc env lc s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    exact g31_boundsPanic (checkG31_of_33 hl hc) hE hbid hb hi hv hop hm hinv hbok hs
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, hsyms, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, hpb, -, -⟩ :=
    checkG33_spec hl hc
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
  obtain ⟨-, hVK⟩ := vkind33_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases hVK with
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

/-- **G33, terminators.** `g31_term`'s statement over `checkG33`. -/
theorem g33_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG33 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s osp) (hpre : G1TermPre lc s blk)
    (hu : UOKL m (uL31 lc (uIn lc bid) blk blk.values.size))
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' osp ∧
      e.b ∈ lc.ctx.f.blocks.toList ∧ UOKL m' (uIn lc e.b) := by
  cases hl : lc.ctx.f.lowered with
  | false => exact g31_term (checkG31_of_33 hl hc) hE hbid hb hm hinv hpre hu ht
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, hedges⟩ :=
    checkG33_spec hl hc
  obtain ⟨m', h1, h2, h3, h4, he, hx⟩ := termK_stepX hpcOf
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb hm hinv hpre ht
  refine ⟨m', h1, h2, h3, h4, fun x hxin => ?_⟩
  exact uok_of_x hx (hu x (uEdgesOK_edge hedges hbid hb he x hxin))

end GoFV.Proof.Gen
