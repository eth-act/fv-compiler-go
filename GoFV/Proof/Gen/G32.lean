import GoFV.Proof.Gen.G30
import GoFV.Proof.Gen.Spec32

/-!
# Soundness of the genssa validator's slice G32: simple ops (`docs/plans/proofs3.md` §4)

`g32_value`, `g32_term`, `g32_nilPanic`, `g32_boundsPanic`: `g30_value`'s, `g30_term`'s,
`g30_nilPanic`'s and `g30_boundsPanic`'s statements over `checkG32`.

`runLoc` runs the register, constant and unary ops of G32 as `Arm64.op2`/`Arm64.op1` of a word
function (`binF`, `binKF`, `unF`) on the arguments read from their homes (`stepLoc_alu32`), and
genssa's `op Rm, Rn, Rd`, `op $k, Rn, Rd` and `op Rm, Rd` compute the same function of the machine
words (`progStep_bin32`, `progStep_binK32`, `progStep_un32`). Each function's low `c` bits depend
only on its operands' low `c` bits (`binF_low`, `binKF_low`, `unF_low`), so the result is related
on its class (`lo_bin32`, `lo_binK32`, `lo_un32`); on registers holding 0 or 1, `AND`, `OR`, `XOR`
and `XOR` with 1 give 0 or 1 (`valRel_binBool`, `valRel_xorBool`). `CSINC [cc] x y f` runs as
`Arm64.csinc`: `x`'s register, or `y + 1` (`Arm64.addP`), by the condition on the flags; the
machine's `CSINC cond, Rx, Ry, Rd` picks by `ConditionHolds` on `NZCV` (`progStep_csinc`,
`valRel_csinc`). The store-release ops are the generic `AtomicStore{8,32,64}` of the value at the
address (`stepLoc_stlr`), the same bytes as an `n`-byte store when the value has the access's
width (`encode_storeBytes`); the machine stores the low `n` bytes of the register (`progStep_stlr`),
so G3's store argument applies (`g32_stlr`). On a function with no arm64 op, `checkG32` is
`checkG30` (`checkG30_of_32`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The ops -/

/-- The word function of a register op of G32. -/
def binF : As → BitVec 64 → BitVec 64 → BitVec 64
  | .MUL => (· * ·)
  | .MNEG => fun x y => -(x * y)
  | .AND => (· &&& ·)
  | .ORR => (· ||| ·)
  | .EOR => (· ^^^ ·)
  | .BIC => fun x y => x &&& ~~~y
  | .EON => fun x y => x ^^^ ~~~y
  | _ => fun x y => x ||| ~~~y

/-- The word function of a constant op of G32. -/
def binKF : As → BitVec 64 → BitVec 64 → BitVec 64
  | .ORR => (· ||| ·)
  | _ => (· ^^^ ·)

/-- The word function of a unary op of G32. -/
def unF : As → BitVec 64 → BitVec 64
  | .NEG => (- ·)
  | _ => (~~~ ·)

theorem bin32?_some {op : Op} {as : As} (h : bin32? op = some as) :
    op = .ARM64MUL ∧ as = .MUL ∨ op = .ARM64MNEG ∧ as = .MNEG ∨ op = .ARM64AND ∧ as = .AND ∨
      op = .ARM64OR ∧ as = .ORR ∨ op = .ARM64XOR ∧ as = .EOR ∨ op = .ARM64BIC ∧ as = .BIC ∨
      op = .ARM64EON ∧ as = .EON ∨ op = .ARM64ORN ∧ as = .ORN := by
  unfold bin32? at h
  split at h <;> (try cases h) <;> simp

theorem binK32?_some {op : Op} {as : As} (h : binK32? op = some as) :
    op = .ARM64ORconst ∧ as = .ORR ∨ op = .ARM64XORconst ∧ as = .EOR := by
  unfold binK32? at h
  split at h <;> (try cases h) <;> simp

theorem un32?_some {op : Op} {as : As} (h : un32? op = some as) :
    op = .ARM64NEG ∧ as = .NEG ∨ op = .ARM64MVN ∧ as = .MVN := by
  unfold un32? at h
  split at h <;> (try cases h) <;> simp

theorem stlr?_some {op : Op} {as : As} {n : Nat} (h : stlr? op = some (as, n)) :
    op = .ARM64STLR ∧ as = .STLR ∧ n = 8 ∨ op = .ARM64STLRW ∧ as = .STLRW ∧ n = 4 ∨
      op = .ARM64STLRB ∧ as = .STLRB ∧ n = 1 := by
  unfold stlr? at h
  split at h <;> (try cases h) <;> simp

/-- `Arm64.evalPure` of a register op of G32: `op2` of its word function. -/
theorem evalPure_bin32 {op : Op} {as : As} (h : bin32? op = some as) (t : Ty) (k : Int64)
    (aux : Option AuxRef) (argv : List Val) :
    Arm64.evalPure op t k aux argv = Arm64.op2 t (binF as) argv := by
  rcases bin32?_some h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-- `Arm64.evalPure` of a constant op of G32: `op1` of its word function with the constant. -/
theorem evalPure_binK32 {op : Op} {as : As} (h : binK32? op = some as) (t : Ty) (k : Int64)
    (aux : Option AuxRef) (argv : List Val) :
    Arm64.evalPure op t k aux argv = Arm64.op1 t (fun x => binKF as x (Arm64.imm k)) argv := by
  rcases binK32?_some h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-- `Arm64.evalPure` of a unary op of G32: `op1` of its word function. -/
theorem evalPure_un32 {op : Op} {as : As} (h : un32? op = some as) (t : Ty) (k : Int64)
    (aux : Option AuxRef) (argv : List Val) :
    Arm64.evalPure op t k aux argv = Arm64.op1 t (unF as) argv := by
  rcases un32?_some h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-- The ALU ops of G32. -/
def AluOp32 (op : Op) : Prop :=
  op = .ARM64MUL ∨ op = .ARM64MNEG ∨ op = .ARM64AND ∨ op = .ARM64OR ∨ op = .ARM64XOR ∨
    op = .ARM64BIC ∨ op = .ARM64EON ∨ op = .ARM64ORN ∨ op = .ARM64ORconst ∨
    op = .ARM64XORconst ∨ op = .ARM64NEG ∨ op = .ARM64MVN ∨ op = .ARM64CSINC

theorem aluOp32_bin {op : Op} {as : As} (h : bin32? op = some as) : AluOp32 op := by
  unfold AluOp32
  rcases bin32?_some h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
    ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp

theorem aluOp32_binK {op : Op} {as : As} (h : binK32? op = some as) : AluOp32 op := by
  unfold AluOp32
  rcases binK32?_some h with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp

theorem aluOp32_un {op : Op} {as : As} (h : un32? op = some as) : AluOp32 op := by
  unfold AluOp32
  rcases un32?_some h with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp

theorem aluOp32_ne {op : Op} (h : AluOp32 op) :
    op ≠ .Phi ∧ op ≠ .ARM64MOVDnop ∧ op ≠ .ARM64MOVDreg ∧ op ≠ .ARM64LoweredNilCheck ∧
      pbOp op = false := by
  unfold AluOp32 at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    exact ⟨nofun, nofun, nofun, nofun, rfl⟩

/-! ## `runLoc` -/

section Steps

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

/-- The ALU ops of G32: `Arm64.evalPure` on the arguments read from their homes. -/
theorem stepLoc_alu32 (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : AluOp32 v.op) (h : stepLoc env lc s v = .ok s') :
    ∃ argv, v.args.toList.mapM (s.read lc) = .ok argv ∧
      s' = s.write lc v.id ((Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux argv).retypeL
        (lc.ty v.id)) := by
  unfold AluOp32 at hop
  rcases hop with hop | hop | hop | hop | hop | hop | hop | hop | hop | hop | hop | hop | hop <;>
  · obtain ⟨argv, r, hm, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
      (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
      (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
    have he : evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) =
        .ok (Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux argv) := by
      unfold evalOpL; rw [hop]; rfl
    rw [he] at hr; cases hr
    exact ⟨argv, hm, rfl⟩

end Steps

/-- A G32 ALU op is none of the narrow loads (`narrowLd?`). -/
theorem narrowLd?_alu32 {lc : LocCtx} {v : Value} (hop : AluOp32 v.op) : narrowLd? lc v = none := by
  unfold AluOp32 at hop
  rcases hop with hop | hop | hop | hop | hop | hop | hop | hop | hop | hop | hop | hop | hop <;>
  · unfold narrowLd?; rw [hop]; rfl

/-! ## The machine -/

section Progs

variable {L : Link} {p : Prog} {s : MState} {next : BitVec 64}

private theorem nMUL : As.MUL.name = "MUL" := rfl
private theorem nMNEG : As.MNEG.name = "MNEG" := rfl
private theorem nAND : As.AND.name = "AND" := rfl
private theorem nORR : As.ORR.name = "ORR" := rfl
private theorem nEOR : As.EOR.name = "EOR" := rfl
private theorem nBIC : As.BIC.name = "BIC" := rfl
private theorem nEON : As.EON.name = "EON" := rfl
private theorem nORN : As.ORN.name = "ORN" := rfl
private theorem nNEG : As.NEG.name = "NEG" := rfl
private theorem nMVN : As.MVN.name = "MVN" := rfl

/-- `op Rm, Rn, Rd` for a register op of G32. -/
theorem progStep_bin32 {op : Op} {as : As} {kn km kd : Nat} (has : bin32? op = some as)
    (hkn : kn < 32) (hkm : km < 32) (hkd : kd < 32)
    (hn : L.nextAddr p.id = some next) (hpa : p.as = as) (hf : p.from_ = regA (REG_R0 + km))
    (hr : p.reg = REG_R0 + kn) (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      (binF as (s.rX (BitVec.ofNat 5 kn)) (s.rX (BitVec.ofNat 5 km))) with pc := next } := by
  have hrn := rn_reg (c := ⟨L, s, p⟩) hr
  have he : progEffect ⟨L, s, p⟩ = .ok (effWd {} kd
      (binF as (s.rX (BitVec.ofNat 5 kn)) (s.rX (BitVec.ofNat 5 km)))) := by
    rcases bin32?_some has with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ |
      ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
    · unfold progEffect
      simp (config := { decide := true }) only [hpa, nMUL, nMNEG, nAND, nORR, nEOR, nBIC, nEON,
        nORN, hf, ht, hrn, regA, ProgOp.baseOf, ↓reduceIte, ProgOp.binNames, ctx_src_reg hkn,
        ctx_src_reg hkm]
      simp only [eff_wX_dest hkd]
      by_cases h : kd = 31 <;> simp (config := { decide := true }) [effWd, h, ProgOp.binOp,
        binF, logical, sizedF, sized, ProgOp.trunc] <;> rfl
  have hsk : p.isSkip = false := by
    rcases bin32?_some has with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ |
      ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [Prog.isSkip, hpa]
  rw [progStep_eq hn hsk he (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]),
    wd_apply hkd]

/-- `op $k, Rn, Rd` for a constant op of G32. -/
theorem progStep_binK32 {op : Op} {as : As} {kn kd : Nat} {k : Int} (has : binK32? op = some as)
    (hkn : kn < 32) (hkd : kd < 32)
    (hn : L.nextAddr p.id = some next) (hpa : p.as = as) (hf : p.from_ = constA k)
    (hr : p.reg = REG_R0 + kn) (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      (binKF as (s.rX (BitVec.ofNat 5 kn)) (BitVec.ofInt 64 k)) with pc := next } := by
  have hrn := rn_reg (c := ⟨L, s, p⟩) hr
  have he : progEffect ⟨L, s, p⟩ = .ok (effWd {} kd
      (binKF as (s.rX (BitVec.ofNat 5 kn)) (BitVec.ofInt 64 k))) := by
    rcases binK32?_some has with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
    · unfold progEffect
      simp (config := { decide := true }) only [hpa, nORR, nEOR, hf, ht, hrn, regA, constA,
        ProgOp.baseOf, ↓reduceIte, ProgOp.binNames, ctx_src_reg hkn, ctx_src_const]
      simp only [eff_wX_dest hkd]
      by_cases h : kd = 31 <;> simp (config := { decide := true }) [effWd, h, ProgOp.binOp,
        binKF, logical, sizedF] <;> rfl
  have hsk : p.isSkip = false := by
    rcases binK32?_some has with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [Prog.isSkip, hpa]
  rw [progStep_eq hn hsk he (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]),
    wd_apply hkd]

/-- `op Rm, Rd` for a unary op of G32. -/
theorem progStep_un32 {op : Op} {as : As} {km kd : Nat} (has : un32? op = some as)
    (hkm : km < 32) (hkd : kd < 32)
    (hn : L.nextAddr p.id = some next) (hpa : p.as = as) (hf : p.from_ = regA (REG_R0 + km))
    (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd) (unF as (s.rX (BitVec.ofNat 5 km))) with
      pc := next } := by
  have he : progEffect ⟨L, s, p⟩ = .ok (effWd {} kd (unF as (s.rX (BitVec.ofNat 5 km)))) := by
    rcases un32?_some has with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · unfold progEffect
      simp (config := { decide := true }) only [hpa, nNEG, hf, ht, regA, ProgOp.baseOf,
        ↓reduceIte, ProgOp.binNames, ctx_src_reg hkm]
      simp only [eff_wX_dest hkd]
      by_cases h : kd = 31 <;> simp (config := { decide := true }) [effWd, h, unF, ProgOp.binOp,
        addSub_sub] <;> rfl
    · unfold progEffect
      simp (config := { decide := true }) only [hpa, nMVN, hf, ht, regA, ProgOp.baseOf,
        ↓reduceIte, ProgOp.binNames, ctx_src_reg hkm]
      simp only [eff_wX_dest hkd]
      by_cases h : kd = 31 <;> simp (config := { decide := true }) [effWd, h, unF, ProgOp.binOp,
        logical, sizedF, ProgOp.trunc] <;> rfl
  have hsk : p.isSkip = false := by
    rcases un32?_some has with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> simp [Prog.isSkip, hpa]
  rw [progStep_eq hn hsk he (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]),
    wd_apply hkd]

/-- `CSINC cond, Rn, Rm, Rd` (`cond` a `SPECIAL` operand `SPOP_EQ + k`, `k < 16`): `X kn` in `Rd`
when the condition holds on `NZCV`, else `X km + 1`. -/
theorem progStep_csinc {kn km kd x : Nat} {cc : Int} (hkn : kn < 32) (hkm : km < 32)
    (hkd : kd < 32) (hn : L.nextAddr p.id = some next) (has : p.as = .CSINC)
    (hf : p.from_ = specA cc) (hcc : SPOP_EQ ≤ cc ∧ cc < SPOP_EQ + 16) (hr : p.reg = REG_R0 + kn)
    (hrest : p.rest = #[(x, regA (REG_R0 + km))]) (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      (if s.holds (BitVec.ofInt 4 (cc - SPOP_EQ)) then s.rX (BitVec.ofNat 5 kn)
        else s.rX (BitVec.ofNat 5 km) + 1) with pc := next } := by
  have hname : As.name .CSINC = "CSINC" := rfl
  have hsp : ProgOp.condOfSpecial (specA cc) = .ok (BitVec.ofInt 4 (cc - SPOP_EQ)) := by
    simp only [ProgOp.condOfSpecial, specA, hcc.1, hcc.2, decide_true, Bool.and_self,
      beq_self_eq_true, ↓reduceIte]
    rfl
  have hrest0 : (ProgCtx.mk L s p).rest 0 = .ok (regA (REG_R0 + km)) := by
    simp [ProgCtx.rest, hrest]
    rfl
  have he : progEffect ⟨L, s, p⟩ = .ok (effWd {} kd
      (if s.holds (BitVec.ofInt 4 (cc - SPOP_EQ)) then s.rX (BitVec.ofNat 5 kn)
        else s.rX (BitVec.ofNat 5 km) + 1)) := by
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
      ProgOp.binNames]
    simp only [hf, hsp, hr, hrest0, ht, regA, ctx_x_r0 hkn, ctx_x_r0 hkm]
    have htr : ∀ y : BitVec 64, ProgOp.trunc true y = y := fun y => by simp [ProgOp.trunc]
    simp only [bind, Except.bind, pure, Except.pure, htr]
    simp only [ctx_x_r0 hkm]
    exact eff_wX_dest hkd
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
    (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]), wd_apply hkd]

end Progs

/-! ## Values -/

section Vals

variable {ι : Blk → Option (BitVec 64)}

private theorem bits_sw32 {c : Nat} {a b : BitVec 64} (h : a.setWidth c = b.setWidth c) :
    ∀ i, i < c → a.getLsbD i = b.getLsbD i := by
  intro i hi
  have := congrArg (fun y : BitVec c => y.getLsbD i) h
  simpa [BitVec.getLsbD_setWidth, hi] using this

private theorem sw_of_bits32 {c : Nat} {a b : BitVec 64}
    (h : ∀ i, i < c → a.getLsbD i = b.getLsbD i) : a.setWidth c = b.setWidth c := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, hi, decide_true, Bool.true_and]
  exact h i hi

private theorem sw_mul32 {c : Nat} (hc : c ≤ 64) {a b a' b' : BitVec 64}
    (ha : a.setWidth c = a'.setWidth c) (hb : b.setWidth c = b'.setWidth c) :
    (a * b).setWidth c = (a' * b').setWidth c := by
  rw [BitVec.setWidth_mul _ _ hc, BitVec.setWidth_mul _ _ hc, ha, hb]

private theorem sw_neg32 {c : Nat} (hc : c ≤ 64) {a a' : BitVec 64}
    (ha : a.setWidth c = a'.setWidth c) : (-a).setWidth c = (-a').setWidth c := by
  rw [BitVec.neg_eq_neg_one_mul a, BitVec.neg_eq_neg_one_mul a']
  exact sw_mul32 hc rfl ha

/-- A register op's low bits depend only on its operands' low bits. -/
theorem binF_low (as : As) {c : Nat} (hc : c ≤ 64) {a b a' b' : BitVec 64}
    (ha : a.setWidth c = a'.setWidth c) (hb : b.setWidth c = b'.setWidth c) :
    (binF as a b).setWidth c = (binF as a' b').setWidth c := by
  have ha' := bits_sw32 ha
  have hb' := bits_sw32 hb
  unfold binF
  split
  · exact sw_mul32 hc ha hb
  · exact sw_neg32 hc (sw_mul32 hc ha hb)
  all_goals
    apply sw_of_bits32
    intro i hi
    simp [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_xor, BitVec.getLsbD_not,
      ha' i hi, hb' i hi]

/-- A constant op's low bits depend only on its operand's low bits. -/
theorem binKF_low (as : As) {c : Nat} {a a' k : BitVec 64} (ha : a.setWidth c = a'.setWidth c) :
    (binKF as a k).setWidth c = (binKF as a' k).setWidth c := by
  have ha' := bits_sw32 ha
  apply sw_of_bits32
  intro i hi
  unfold binKF
  split <;> simp [BitVec.getLsbD_or, BitVec.getLsbD_xor, ha' i hi]

/-- A unary op's low bits depend only on its operand's low bits. -/
theorem unF_low (as : As) {c : Nat} (hc : c ≤ 64) {a a' : BitVec 64}
    (ha : a.setWidth c = a'.setWidth c) : (unF as a).setWidth c = (unF as a').setWidth c := by
  unfold unF
  split
  · exact sw_neg32 hc ha
  · have ha' := bits_sw32 ha
    apply sw_of_bits32
    intro i hi
    simp [BitVec.getLsbD_not, ha' i hi]

private theorem res_int32 {t : Ty} (ht : t ≠ .bool) (r : BitVec 64) :
    Arm64.res t r = .int .w64 r := by
  cases t <;> first | exact absurd rfl ht | rfl

private theorem low_le32 {c ca : Nat} {a b : BitVec 64} (h : a.setWidth ca = b.setWidth ca)
    (hc : c ≤ ca) : a.setWidth c = b.setWidth c := by
  have := congrArg (BitVec.setWidth c) h
  simpa only [BitVec.setWidth_setWidth_of_le _ hc] using this

private theorem fits_le32 {c : Nat} {x : Val} {r : BitVec 64} (hf : Fits c x)
    (hr : Arm64.reg x = some r) : c ≤ 64 := by
  cases x with
  | int w v => have : w.bits = c := hf; subst this; cases w <;> decide
  | bool b => have : c = 1 := hf; omega
  | ptr p => have : c = 64 := hf; omega
  | _ => cases hr

/-- A register op of arguments of classes `ca`, `cb` at least the result's class `c`. -/
theorem lo_bin32 (hA : AddrAgree ι) {t : Ty} (as : As) {x y : Val} {X Y : BitVec 64}
    {c ca cb : Nat} (hx : ValRel ι x X) (hy : ValRel ι y Y) (hfx : Fits ca x) (hfy : Fits cb y)
    (hca : c ≤ ca) (hcb : c ≤ cb) (ht : t ≠ .bool) :
    Lo ι c (Arm64.op2 t (binF as) [x, y]) (binF as X Y) := by
  simp only [Arm64.op2]
  cases hrx : Arm64.reg x with
  | none => trivial
  | some a =>
    cases hry : Arm64.reg y with
    | none => trivial
    | some b =>
      show Lo ι c (Arm64.res t (binF as a b)) _
      rw [res_int32 ht]
      have hc : c ≤ 64 := Nat.le_trans hca (fits_le32 hfx hrx)
      exact binF_low as hc (low_le32 (reg_low hA hx hfx hrx) hca)
        (low_le32 (reg_low hA hy hfy hry) hcb)

/-- A constant op of an argument of class `ca` at least the result's class `c`. -/
theorem lo_binK32 (hA : AddrAgree ι) {t : Ty} (as : As) {x : Val} {X K : BitVec 64} {c ca : Nat}
    (hx : ValRel ι x X) (hfx : Fits ca x) (hca : c ≤ ca) (ht : t ≠ .bool) :
    Lo ι c (Arm64.op1 t (fun a => binKF as a K) [x]) (binKF as X K) := by
  simp only [Arm64.op1]
  cases hrx : Arm64.reg x with
  | none => trivial
  | some a =>
    show Lo ι c (Arm64.res t (binKF as a K)) _
    rw [res_int32 ht]
    exact binKF_low as (low_le32 (reg_low hA hx hfx hrx) hca)

/-- A unary op of an argument of class `ca` at least the result's class `c`. -/
theorem lo_un32 (hA : AddrAgree ι) {t : Ty} (as : As) {x : Val} {X : BitVec 64} {c ca : Nat}
    (hx : ValRel ι x X) (hfx : Fits ca x) (hca : c ≤ ca) (ht : t ≠ .bool) :
    Lo ι c (Arm64.op1 t (unF as) [x]) (unF as X) := by
  simp only [Arm64.op1]
  cases hrx : Arm64.reg x with
  | none => trivial
  | some a =>
    show Lo ι c (Arm64.res t (unF as a)) _
    rw [res_int32 ht]
    have hc : c ≤ 64 := Nat.le_trans hca (fits_le32 hfx hrx)
    exact unF_low as hc (low_le32 (reg_low hA hx hfx hrx) hca)

/-- A register of class 1 is a boolean or `poison`; a boolean's machine word is 0 or 1. -/
private theorem bool_cases {x : Val} {X : BitVec 64} (hx : ValRel ι x X) (hf : Fits 1 x) :
    x = .poison ∨ ∃ b, x = .bool b ∧ X = if b then 1 else 0 := by
  cases x with
  | poison => exact .inl rfl
  | bool b => exact .inr ⟨b, rfl, hx⟩
  | int w v =>
    have hf' : w.bits = 1 := hf
    cases w <;> exact absurd hf' (by decide)
  | ptr p =>
    have h1 : (1 : Nat) = 64 := hf
    omega
  | _ => exact False.elim hf

/-- A boolean result whose machine word is 0 or 1. -/
private theorem valRel_boolRes {X : BitVec 64} (h : X = 0 ∨ X = 1) :
    ValRel ι ((Arm64.res .bool X).retypeL .bool) X := by
  show X = if X.getLsbD 0 then 1 else 0
  rcases h with rfl | rfl <;> decide

/-- `AND`, `OR`, `XOR` of two booleans: the machine's 0 or 1. -/
theorem valRel_binBool {as : As} (hb : boolBin as = true) {x y : Val} {X Y : BitVec 64}
    (hx : ValRel ι x X) (hy : ValRel ι y Y) (hfx : Fits 1 x) (hfy : Fits 1 y) :
    ValRel ι ((Arm64.op2 .bool (binF as) [x, y]).retypeL .bool) (binF as X Y) := by
  have has : (as = .AND ∨ as = .ORR) ∨ as = .EOR := by
    unfold boolBin at hb
    simpa [Bool.or_eq_true, beq_iff_eq] using hb
  rcases bool_cases hx hfx with rfl | ⟨a, rfl, rfl⟩
  · trivial
  rcases bool_cases hy hfy with rfl | ⟨b, rfl, rfl⟩
  · cases a <;> trivial
  show ValRel ι ((Arm64.res .bool (binF as (if a then 1 else 0) (if b then 1 else 0))).retypeL
    .bool) _
  apply valRel_boolRes
  rcases has with (rfl | rfl) | rfl <;> cases a <;> cases b <;> decide

/-- `XORconst [1]` of a boolean: the machine's 0 or 1. -/
theorem valRel_xorBool {x : Val} {X : BitVec 64} {k : Int64} (hk : k.toInt = 1)
    (hx : ValRel ι x X) (hfx : Fits 1 x) :
    ValRel ι ((Arm64.op1 .bool (fun a => binKF .EOR a (Arm64.imm k)) [x]).retypeL .bool)
      (binKF .EOR X (BitVec.ofInt 64 k.toInt)) := by
  have him : Arm64.imm k = 1 := by simp [Arm64.imm, hk]
  rw [hk, him]
  rcases bool_cases hx hfx with rfl | ⟨a, rfl, rfl⟩
  · trivial
  · show ValRel ι ((Arm64.res .bool (binKF .EOR (if a then 1 else 0) 1)).retypeL .bool) _
    apply valRel_boolRes
    cases a <;> decide

/-- `addP`'s result is `poison`, a pointer or a 64-bit word. -/
private theorem addP_shape {t : Ty} (ht : t ≠ .bool) (y : Val) (k : BitVec 64) :
    Arm64.addP t y k = .poison ∨ (∃ p, Arm64.addP t y k = .ptr p) ∨
      ∃ r, Arm64.addP t y k = .int .w64 r := by
  unfold Arm64.addP
  split
  · unfold PtrOps.ptrRes Ptr.word
    split <;> (try split) <;> (try split) <;> simp
  · split
    · rw [res_int32 ht]; simp
    · simp

/-- A `regVal` of an `addP` result: unchanged. -/
private theorem regVal_addP {t : Ty} (ht : t ≠ .bool) (y : Val) (k : BitVec 64) :
    Arm64.regVal t (Arm64.addP t y k) = Arm64.addP t y k := by
  rcases addP_shape ht y k with h | ⟨p, h⟩ | ⟨r, h⟩ <;> rw [h]
  · rfl
  · rfl
  · show Arm64.res t (r.setWidth 64) = _
    rw [res_int32 ht, BitVec.setWidth_eq]

/-- `CSINC [cc] x y f` on flags related to `NZCV`, of arguments of classes `ca`, `cb` at least the
result's class `c ≥ 8`: the machine's `CSINC` word (`progStep_csinc`). -/
theorem valRel_csinc (hA : AddrAgree ι) {t : Ty} {k : Int64} {x y f : Val} {X Y : BitVec 64}
    {nz : Flags} {c ca cb : Nat} {cnd : Cond} (hcd : Cond.ofAux k = some cnd) (hf : FlagsRel f nz)
    (hx : ValRel ι x X) (hy : ValRel ι y Y) (hfx : Fits ca x) (hfy : Fits cb y)
    (hc : cls t = some c) (h8 : 8 ≤ c) (hca : c ≤ ca) (hcb : c ≤ cb) :
    ValRel ι ((Arm64.csinc t k [x, y, f]).retypeL t) (if cnd.holds nz then X else Y + 1) := by
  have ht := cls_ne_bool hc h8
  apply valRel_retypeL_lo hA hc ht
  unfold Arm64.csinc Arm64.condOn
  rw [hcd]
  simp only [Option.bind_some]
  cases ho : cnd.onVal f with
  | none => trivial
  | some b =>
    rw [onVal_holds hf ho]
    cases b
    · rw [regVal_addP ht]
      exact lo_addK hA hy hfy h8 hcb ht
    · exact lo_regVal hA hx hfx hca ht

end Vals

/-! ## The store-release ops -/

section Stlr

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

private theorem mapM_three32 {a b c : ID} :
    [a, b, c].mapM (s.read lc) =
      (s.read lc a).bind fun x => (s.read lc b).bind fun y => (s.read lc c).bind fun z =>
        .ok [x, y, z] := rfl

/-- A store-release whose `arm64Op` is the generic atomic store `g` of a `w`-wide location. -/
private theorem stlr_core {g : Op} {w : Width} (hl : lc.ctx.f.lowered = true)
    (ht : (lc.temps[v.id]?).join = none) (hne : v.op ≠ .Phi) (h1 : v.op ≠ .LoadReg)
    (h2 : v.op ≠ .StoreReg) (h3 : v.op ≠ .ARM64MOVDreg) (h4 : v.op ≠ .ARM64MOVDnop)
    (hc : v.op.regInfo.clobbers.isEmpty = true) (hc0 : v.op.regInfo.clobbersArg0 = false)
    (hc1 : v.op.regInfo.clobbersArg1 = false) (hf : v.op.clobberFlags = false)
    (hev : ∀ argv, evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) =
      arm64Op true env lc.ctx s.fr v argv (lc.ty v.id))
    (hst : ∀ x y mm, nilFaults true lc.ctx v [x, y, .mem mm] = none →
      arm64Op true env lc.ctx s.fr v [x, y, .mem mm] (lc.ty v.id) =
        Atomic.rmwRoot { v with op := g } x (fitPiece (.int w) y) (.mem mm))
    (hinfo : Atomic.info? g = some (.store, .int w))
    {a0 a1 a2 : ID} (ha : v.args = #[a0, a1, a2]) {mm : Mem} (hm : s.read lc a2 = .ok (.mem mm))
    (h : stepLoc env lc s v = .ok s') :
    ∃ x y p mm', s.read lc a0 = .ok x ∧ s.read lc a1 = .ok y ∧ x.asPtrWord = some p ∧
      mm.write p (encode (.int w) (fitPiece (.int w) y)) = some mm' ∧
      s' = s.write lc v.id ((Val.mem mm').retypeL (lc.ty v.id)) := by
  obtain ⟨argv, r, hmap, hr, rfl⟩ := stepLoc_noclobber hl ht hne h1 h2 h3 h4 hc hc0 hc1 hf h
  rw [ha] at hmap
  change [a0, a1, a2].mapM (s.read lc) = _ at hmap
  rw [mapM_three32] at hmap
  cases hx : s.read lc a0 with
  | panic e m => rw [hx] at hmap; cases hmap
  | stuck msg => rw [hx] at hmap; cases hmap
  | ok x =>
  cases hy : s.read lc a1 with
  | panic e m => rw [hx, hy] at hmap; cases hmap
  | stuck msg => rw [hx, hy] at hmap; cases hmap
  | ok y =>
    rw [hx, hy, hm] at hmap; cases hmap
    rw [hev] at hr
    cases hn : nilFaults true lc.ctx v [x, y, .mem mm] with
    | some m =>
      have he : arm64Op true env lc.ctx s.fr v [x, y, .mem mm] (lc.ty v.id) =
          .panic .nilDeref m := by
        unfold arm64Op; rw [hn]
      rw [he] at hr; cases hr
    | none =>
      rw [hst x y mm hn] at hr
      have hinfo' : Atomic.info? ({ v with op := g } : Value).op = some (.store, .int w) := hinfo
      cases hp : x.asPtrWord with
      | none => simp [Atomic.rmwRoot, hp, Atomic.unmodelled] at hr
      | some p =>
        simp only [Atomic.rmwRoot, hp, hinfo', Atomic.rmw, Atomic.step] at hr
        split at hr
        · cases hw : mm.write p (encode (.int w) (fitPiece (.int w) y)) with
          | none => rw [hw] at hr; cases hr
          | some mm' =>
            rw [hw] at hr; cases hr
            exact ⟨x, y, p, mm', rfl, rfl, hp, hw, rfl⟩
        · cases hr

/-- A store-release op (`STLR`, `STLRW`, `STLRB p x mem`): the generic atomic store of `x` at the
location `p` addresses, at the access's width `w`, which succeeded. -/
theorem stepLoc_stlr (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    {as : As} {n : Nat} (hop : stlr? v.op = some (as, n)) {a0 a1 a2 : ID}
    (ha : v.args = #[a0, a1, a2]) {mm : Mem} (hm : s.read lc a2 = .ok (.mem mm))
    (h : stepLoc env lc s v = .ok s') :
    ∃ (w : Width) (x y : Val) (p : Ptr) (mm' : Mem), w.bytes = n ∧ s.read lc a0 = .ok x ∧
      s.read lc a1 = .ok y ∧ x.asPtrWord = some p ∧
      mm.write p (encode (.int w) (fitPiece (.int w) y)) = some mm' ∧
      s' = s.write lc v.id ((Val.mem mm').retypeL (lc.ty v.id)) := by
  rcases stlr?_some hop with ⟨ho, -, rfl⟩ | ⟨ho, -, rfl⟩ | ⟨ho, -, rfl⟩
  · obtain ⟨x, y, p, mm', h1, h2, h3, h4, h5⟩ := stlr_core (g := .AtomicStore64) (w := .w64) hl ht
      (by rw [ho]; nofun) (by rw [ho]; nofun) (by rw [ho]; nofun) (by rw [ho]; nofun)
      (by rw [ho]; nofun) (by rw [ho]; rfl) (by rw [ho]; rfl) (by rw [ho]; rfl) (by rw [ho]; rfl)
      (fun _ => by unfold evalOpL; rw [ho]; rfl)
      (fun _ _ _ hn => by unfold arm64Op; rw [hn, ho]; rfl) rfl ha hm h
    exact ⟨.w64, x, y, p, mm', rfl, h1, h2, h3, h4, h5⟩
  · obtain ⟨x, y, p, mm', h1, h2, h3, h4, h5⟩ := stlr_core (g := .AtomicStore32) (w := .w32) hl ht
      (by rw [ho]; nofun) (by rw [ho]; nofun) (by rw [ho]; nofun) (by rw [ho]; nofun)
      (by rw [ho]; nofun) (by rw [ho]; rfl) (by rw [ho]; rfl) (by rw [ho]; rfl) (by rw [ho]; rfl)
      (fun _ => by unfold evalOpL; rw [ho]; rfl)
      (fun _ _ _ hn => by unfold arm64Op; rw [hn, ho]; rfl) rfl ha hm h
    exact ⟨.w32, x, y, p, mm', rfl, h1, h2, h3, h4, h5⟩
  · obtain ⟨x, y, p, mm', h1, h2, h3, h4, h5⟩ := stlr_core (g := .AtomicStore8) (w := .w8) hl ht
      (by rw [ho]; nofun) (by rw [ho]; nofun) (by rw [ho]; nofun) (by rw [ho]; nofun)
      (by rw [ho]; nofun) (by rw [ho]; rfl) (by rw [ho]; rfl) (by rw [ho]; rfl) (by rw [ho]; rfl)
      (fun _ => by unfold evalOpL; rw [ho]; rfl)
      (fun _ _ _ hn => by unfold arm64Op; rw [hn, ho]; rfl) rfl ha hm h
    exact ⟨.w8, x, y, p, mm', rfl, h1, h2, h3, h4, h5⟩

end Stlr

/-- The generic store's bytes of a value of the access's width are the `n`-byte store's. -/
theorem encode_storeBytes {w : Width} {y : Val} (hf : Fits w.bits y) :
    encode (.int w) (fitPiece (.int w) y) = Arm64.storeBytes w.bytes y := by
  cases y with
  | poison => cases w <;> rfl
  | int w' x =>
    have hw : w'.bits = w.bits := hf
    have hww : w' = w := by cases w <;> cases w' <;> first | rfl | exact absurd hw (by decide)
    subst hww
    have hlt : x.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le x.isLt
      (Nat.pow_le_pow_right (by omega) (by cases w' <;> decide))
    cases w' <;> simp (config := { decide := true }) [fitPiece, encode, Arm64.storeBytes,
      Arm64.reg, Width.bytes, Width.bits, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hlt]
  | ptr p =>
    have hw : w.bits = 64 := hf
    have hww : w = .w64 := by cases w <;> first | rfl | exact absurd hw (by decide)
    subst hww
    rfl
  | bool b =>
    have hw : w.bits = 1 := hf
    cases w <;> exact absurd hw (by decide)
  | _ => exact False.elim hf

/-- The address of a store-release: `Arm64.addr` of its base at offset 0 is the location the
generic store writes. -/
theorem addr_asPtrWord {x : Val} {p : Ptr} (h : x.asPtrWord = some p) : Arm64.addr x 0 = some p := by
  cases x with
  | ptr q =>
    simp only [Val.asPtrWord, Option.some.injEq] at h
    subst h
    show some (q.add 0) = some q
    simp [Ptr.add]
  | int w a =>
    cases w
    case w64 =>
      have h' : Ptr.ofAddr a = p := by simpa [Val.asPtrWord] using h
      subst h'
      show (Arm64.reg (.int .w64 a)).map (fun x => Ptr.ofAddr (x + 0)) = some (Ptr.ofAddr a)
      simp [Arm64.reg]
    all_goals simp [Val.asPtrWord] at h
  | _ => simp [Val.asPtrWord] at h

section StlrProg

variable {L : Link} {p : Prog} {s : MState} {next : BitVec 64}

/-- An opcode name none of `progEffect`'s branches before the store-release one takes. -/
private def stlrPre (name : String) (n : Nat) : Prop :=
  name ∉ ["TEXT", "FUNCDATA", "PCDATA", "NOP"] ∧
  ProgOp.baseOf name ProgOp.binNames = none ∧ ProgOp.baseOf name ["CMP", "CMN", "TST"] = none ∧
  ProgOp.baseOf name ["NEG", "NEGS", "MVN", "NGC", "NGCS"] = none ∧
  ProgOp.baseOf name ["CLZ", "RBIT", "REV", "REV16", "REV32"] = none ∧
  ProgOp.baseOf name ["MADD", "MSUB"] = none ∧
  ProgOp.baseOf name ["UBFX", "SBFX", "UBFIZ", "SBFIZ", "BFI", "BFXIL"] = none ∧
  ProgOp.baseOf name ["EXTR"] = none ∧
  ProgOp.baseOf name ["CSEL", "CSINC", "CSINV", "CSNEG"] = none ∧
  ProgOp.baseOf name ["CSET", "CSETM"] = none ∧ ProgOp.movMem name = none ∧
  ProgOp.pairOp name = none ∧ ProgOp.startsS name "LDAR" = false ∧
  ProgOp.startsS name "LDAXR" = false ∧ ProgOp.startsS name "STLR" = true ∧
  ProgOp.startsS name "STLXR" = false ∧ ProgOp.suffixBytes (ProgOp.dropS name 4) = n

private theorem stlrPre_of {op : Op} {as : As} {n : Nat} (h : stlr? op = some (as, n)) :
    stlrPre as.name n := by
  rcases stlr?_some h with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ <;>
    simp (config := { decide := true }) [stlrPre]

/-- `STLR{,W,B} Rs, (Rn)`: the low `n` bytes of `X ks` stored at `a`, outside the nil page. -/
theorem progStep_stlr {op : Op} {as : As} {n ks : Nat} {a : BitVec 64}
    (hop : stlr? op = some (as, n)) (hks : ks < 32) (hn : L.nextAddr p.id = some next)
    (hpa : p.as = as) (hf : p.from_ = regA (REG_R0 + ks))
    (hma : (ProgCtx.mk L s p).mem p.to = .ok (a, none)) (hnil : nilPage a = false) :
    progStep L p s = .ok { s with
      mem := writeMem s.mem a n (BitVec.ofNat (8 * n) ((s.rX (BitVec.ofNat 5 ks)).toNat % 2 ^ (8 * n))),
      pc := next } := by
  obtain ⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ :=
    stlrPre_of hop
  have he : progEffect ⟨L, s, p⟩ =
      .ok { stores := [(a, n, (s.rX (BitVec.ofNat 5 ks)).toNat % 2 ^ (8 * n))] } := by
    unfold progEffect
    simp only [hpa, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, hma, hf,
      regA, ctx_x_r0 hks, Bool.false_eq_true, Bool.or_false, Bool.false_or, ↓reduceIte]
    rfl
  have hsk : p.isSkip = false := by
    rcases stlr?_some hop with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ <;> simp [Prog.isSkip, hpa]
  rw [progStep_eq hn hsk he (by simp [Eff.nilAccess?, List.find?, hnil])]
  rfl

end StlrProg

/-- The fields of a Prog `csincOK` accepts. -/
theorem csincOK_spec {cc rn rm rd : Int} {p : Prog} (h : csincOK cc rn rm rd p = true) :
    p.as = .CSINC ∧ p.from_ = specA cc ∧ p.reg = rn ∧ p.to = regA rd ∧ p.scond = 0 ∧
      p.regTo2 = 0 ∧ ∃ x, p.rest = #[(x, regA rm)] := by
  unfold csincOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, ?_⟩
  cases h0 : p.rest[0]? with
  | none => rw [h0] at h8; cases h8
  | some q =>
    rw [h0] at h8
    obtain ⟨x, a⟩ := q
    simp only [Option.map_some, Option.some.injEq] at h8
    subst h8
    exact ⟨x, arr1 h7 h0⟩

/-- A store-release op is no `Phi`, `MOVDnop`, `MOVDreg`, nil check, bounds panic or narrow load. -/
theorem stlr_ne {lc : LocCtx} {v : Value} {as : As} {n : Nat} (h : stlr? v.op = some (as, n)) :
    v.op ≠ .Phi ∧ v.op ≠ .ARM64MOVDnop ∧ v.op ≠ .ARM64MOVDreg ∧ v.op ≠ .ARM64LoweredNilCheck ∧
      pbOp v.op = false ∧ narrowLd? lc v = none := by
  rcases stlr?_some h with ⟨ho, -⟩ | ⟨ho, -⟩ | ⟨ho, -⟩ <;>
  · refine ⟨by rw [ho]; nofun, by rw [ho]; nofun, by rw [ho]; nofun, by rw [ho]; nofun,
      by rw [ho]; rfl, ?_⟩
    unfold narrowLd?; rw [ho]; rfl

/-! ## The cases -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- `op Rm, Rn, Rd` for a register op of G32. -/
theorem g32_bin (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {ca cb c : Nat} {rn rm rd : Int} (hop : bin32? v.op = some as)
    (hsz : v.args.size = 2) (hao : argObj lc v 0 = .ok (ca, rn))
    (hbo : argObj lc v 1 = .ok (cb, rm)) (hro : resObj lc v = .ok (c, rd))
    (hw : 8 ≤ c ∧ c ≤ ca ∧ c ≤ cb ∨ c = 1 ∧ ca = 1 ∧ cb = 1 ∧ boolBin as = true)
    (hvs : OneAt2 psA j (.ofShape { as, from_ := regA rm, reg := rn, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have halu := aluOp32_bin hop
  have hnp : v.op ≠ .Phi := (aluOp32_ne halu).1
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
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu32 hl htemp halu hs
  rw [arr2 hsz ha0 ha1] at hargv
  obtain rfl := mapM_res_two hargv hx hy
  rw [write_reg hvh hcv, evalPure_bin32 hop]
  have hrel : ValRel E.ι ((Arm64.op2 (lc.ty v.id) (binF as) [x, y]).retypeL (lc.ty v.id))
      (binF as (m.rX (BitVec.ofNat 5 kn)) (m.rX (BitVec.ofNat 5 km))) := by
    rcases hw with ⟨h8, hca, hcb⟩ | ⟨rfl, rfl, rfl, hb⟩
    · have ht := cls_ne_bool hcv h8
      exact valRel_retypeL_lo hA hcv ht (lo_bin32 hA as hxv hyv hxf hyf hca hcb ht)
    · rw [cls_bool hcv]
      exact valRel_binBool hb hxv hyv hxf hyf
  refine (op_reg2 (H := H) F hm hinv hj hj' hvs hd hkd hor hrel (fits_retypeL hcv _)
    (knext_set hK hnp hvh hcv) (fun k0 hk0' hok => ?_)).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨hpa, hf, hr, ht', -⟩ := Shape.ok_eq hok
  rw [progStep_bin32 hop hkn hkm hkd (nextAddr_pcAt F.nodup hk0') hpa hf hr ht', wX_pc]
  rfl

/-- `op $k, Rn, Rd` for a constant op of G32. -/
theorem g32_binK (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {ca c : Nat} {rn rd : Int} (hop : binK32? v.op = some as)
    (hsz : v.args.size = 1) (hao : argObj lc v 0 = .ok (ca, rn)) (hro : resObj lc v = .ok (c, rd))
    (hw : 8 ≤ c ∧ c ≤ ca ∨ c = 1 ∧ ca = 1 ∧ as = .EOR ∧ v.auxInt.toInt = 1)
    (hvs : OneAt2 psA j
      (.ofShape { as, from_ := constA v.auxInt.toInt, reg := rn, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have halu := aluOp32_binK hop
  have hnp : v.op ≠ .Phi := (aluOp32_ne halu).1
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu32 hl htemp halu hs
  rw [arr1 hsz ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  rw [write_reg hvh hcv, evalPure_binK32 hop]
  have hrel : ValRel E.ι ((Arm64.op1 (lc.ty v.id) (fun a => binKF as a (Arm64.imm v.auxInt))
      [x]).retypeL (lc.ty v.id))
      (binKF as (m.rX (BitVec.ofNat 5 kn)) (BitVec.ofInt 64 v.auxInt.toInt)) := by
    rcases hw with ⟨h8, hca⟩ | ⟨rfl, rfl, rfl, hk1⟩
    · have ht := cls_ne_bool hcv h8
      exact valRel_retypeL_lo hA hcv ht (lo_binK32 hA as hxv hxf hca ht)
    · rw [cls_bool hcv]
      exact valRel_xorBool hk1 hxv hxf
  refine (op_reg2 (H := H) F hm hinv hj hj' hvs hd hkd hor hrel (fits_retypeL hcv _)
    (knext_set hK hnp hvh hcv) (fun k0 hk0' hok => ?_)).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨hpa, hf, hr, ht', -⟩ := Shape.ok_eq hok
  rw [progStep_binK32 hop hkn hkd (nextAddr_pcAt F.nodup hk0') hpa hf hr ht', wX_pc]
  rfl

/-- `op Rm, Rd` for a unary op of G32. -/
theorem g32_un (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {ca c : Nat} {rm rd : Int} (hop : un32? v.op = some as)
    (hsz : v.args.size = 1) (hao : argObj lc v 0 = .ok (ca, rm)) (hro : resObj lc v = .ok (c, rd))
    (h8 : 8 ≤ c) (hca : c ≤ ca)
    (hvs : OneAt2 psA j (.ofShape { as, from_ := regA rm, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have halu := aluOp32_un hop
  have hnp : v.op ≠ .Phi := (aluOp32_ne halu).1
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨km, hkm, rfl, hkkm⟩ := objOf?_some hor0
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkm
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu32 hl htemp halu hs
  rw [arr1 hsz ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  rw [write_reg hvh hcv, evalPure_un32 hop]
  have ht := cls_ne_bool hcv h8
  refine (op_reg2 (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_retypeL_lo hA hcv ht (lo_un32 hA as hxv hxf hca ht)) (fits_retypeL hcv _)
    (knext_set hK hnp hvh hcv) (fun k0 hk0' hok => ?_)).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨hpa, hf, -, ht', -⟩ := Shape.ok_eq hok
  rw [progStep_un32 hop hkm hkd (nextAddr_pcAt F.nodup hk0') hpa hf ht', wX_pc]
  rfl

/-- `CSINC [cc] x y f`: `CSINC cond, Rx, Ry, Rd` writes `x`'s word or `y`'s plus 1. -/
theorem g32_csinc (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {f : ID} {o : Op} {cc rn rm rd : Int} {ca cb c : Nat}
    (hop : v.op = .ARM64CSINC) (hsz : v.args.size = 3) (hfa : v.args[2]? = some f)
    (hfl : (lc.ty f).isFlags = true) (hhn : lc.home f = none) (ho : ccOp? v.auxInt = some o)
    (hco : (Cond.ofOp o).isSome = true) (hcc : ARM64.condBits o = some cc)
    (hao : argObj lc v 0 = .ok (ca, rn)) (hbo : argObj lc v 1 = .ok (cb, rm))
    (hro : resObj lc v = .ok (c, rd)) (h8 : 8 ≤ c) (hca : c ≤ ca) (hcb : c ≤ cb)
    (hvs : OneAt2 psA j ⟨csincOK cc rn rm rd, "CSINC"⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨cnd, hcs⟩ := Option.isSome_iff_exists.1 hco
  have hcd := ccOp?_ofAux ho hcs
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hbo
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨km, hkm, rfl, hkkm⟩ := objOf?_some hor1
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kd, hkd, rfl, -⟩ := objOf?_some hor
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨y, hy, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkkm
  have halu : AluOp32 v.op := by unfold AluOp32; simp [hop]
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu32 hl htemp halu hs
  rw [arr3 hsz ha0 ha1 hfa] at hargv
  obtain rfl := mapM_res_three hargv hx hy (read_flags hl hhn hfl)
  rw [write_reg hvh hcv, hop, isFlags_eq hfl]
  obtain ⟨hfr, -⟩ := flags_retypeL hm.flags
  obtain ⟨hrange, hcond⟩ := cset_cond hcs hcc
  refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_csinc hA hcd hfr hxv hyv hxf hyf hcv h8 hca hcb) (fits_retypeL hcv _)
    (knext_set hK hnp hvh hcv) (fun k hk hok => ?_)).imp
    fun m' ⟨h1, h2, h3, _⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨has, hf, hr, ht, -, -, xr, hrest⟩ := csincOK_spec hok
  rw [progStep_csinc hkn hkm hkd (nextAddr_pcAt F.nodup hk) has hf hrange hr hrest ht, wX_pc]
  simp only [MState.holds, hcond]
  rfl

/-- `STLR{,W,B} Rs, (Rn)`: G3's store argument with the generic atomic store's bytes. -/
theorem g32_stlr (F : Facts lc sym text az ez psA.toList ret E) (hF : FrameOK E)
    (hsz : ∀ k v, s.slots.lookup k = some v → (E.lc.slotTy k).size = 8)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {n ca cs : Nat} {rn rs : Int}
    (hop : stlr? v.op = some (as, n)) (hsz3 : v.args.size = 3) (hmt : memTy (lc.ty v.id) = true)
    (hhn : lc.home v.id = none) (haux : v.aux = none) (hk0 : v.auxInt.toInt = 0)
    (hao : argObj lc v 0 = .ok (ca, rn)) (hso : argObj lc v 1 = .ok (cs, rs))
    (hma : memArg lc v 2 = .ok ()) (hca : ca = 64) (hcs : cs = 8 * n)
    (hvs : OneAt2 psA j ⟨plain as (· == regA rs) (· == memA rn 0), as.name⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  obtain ⟨hnp, -, -, -, -, -⟩ := stlr_ne (lc := lc) hop
  have hn : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8 := by
    rcases stlr?_some hop with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> simp
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hso
  obtain ⟨ks, hks, rfl, hkks⟩ := objOf?_some hor1
  obtain ⟨a2, ha2, hamt, hah2⟩ := memArg_spec hma
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  obtain ⟨X, hX, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨y, hy, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkks
  obtain ⟨w, x, y', p, mm', hwn, hx, hy', hpw, hw, rfl⟩ := stepLoc_stlr hl htemp hop
    (arr3 hsz3 ha0 ha1 ha2) (read_mem hl hah2 hamt hmm) hs
  rw [hy] at hy'
  cases hy'
  have hxX : X = x := by rw [hx] at hX; cases hX; rfl
  subst hxX
  subst hca hcs
  have hfy : Fits w.bits y := by
    have hb : w.bits = 8 * w.bytes := by cases w <;> rfl
    rw [hb, hwn]; exact hyf
  rw [encode_storeBytes hfy, hwn] at hw
  obtain ⟨mm0, hmm0, hk0', hsep0⟩ := hinv.mem
  rw [hmm] at hmm0
  cases hmm0
  have hcs : 8 * n ≤ 8 * n ∨ 8 * n = 1 := .inl (Nat.le_refl _)
  have hbs := (storeBytes_relN hA hn hyv hyf hcs).1
  have hcan : mm.canWrite p n = true := by
    have := canWrite_of_write hw (by rw [hbs]; omega)
    rwa [hbs] at this
  rw [write_mem hhn hmt, memTy_eq hmt, retypeL_mem]
  have haddr : Arm64.addr X 0 = some p := addr_asPtrWord hpw
  obtain ⟨a, hpa, haeq, hnil⟩ := addr_rel hA hMI hxv hxf haddr (by omega : 0 < n) (Or.inl hcan)
  have hstep : ∀ k (hk : k < psA.toList.length),
      (Pat.mk (plain as (· == regA (REG_R0 + ks)) (· == memA (REG_R0 + kn) 0)) as.name).ok
        psA.toList[k] = true →
      progStep (Link.byId sym text az ez psA.toList) psA.toList[k]
          { m with pc := pcAt text psA.toList k } =
        .ok { m with
          mem := writeMem m.mem (a + p.off) n
            (BitVec.ofNat (8 * n) ((m.rX (BitVec.ofNat 5 ks)).toNat % 2 ^ (8 * n))),
          pc := pcAt text psA.toList (k + 1) } := by
    intro k0 hk0 hok
    obtain ⟨has, hf, -, ht', hsc, -, -⟩ := plain_spec hok
    simp only [beq_iff_eq] at hf ht'
    have hma' : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
        { m with pc := pcAt text psA.toList k0 } psA.toList[k0]).mem psA.toList[k0].to =
        .ok (a + p.off, none) := by
      rw [ht', ctx_mem_reg hkn hsc]
      have h0 : BitVec.ofInt 64 0 = (0 : BitVec 64) := by decide
      show Except.ok (m.rX (BitVec.ofNat 5 kn) + BitVec.ofInt 64 0, none) = _
      rw [h0, haeq]
    rw [progStep_stlr hop hks (nextAddr_pcAt F.nodup hk0) has hf hma' hnil]
    rfl
  obtain ⟨hM', hk', hback, al, hal, hoff, hout⟩ := memInj_storeN hA hMI hk0' hn hpa hyv hyf hcs hw
  have hsep' : SepFrom E.ι (StkAt E) mm' := by
    intro b2 al2 a2 hb hι y hy
    obtain ⟨al1, hb1, hs1⟩ := hback b2 al2 hb
    rw [← hs1]; exact hsep0 b2 al1 a2 hb1 hι y hy
  exact (op_mem2 (H := H) F hm hinv (stk_keeps hm hF hsz) hj hj' hvs hM' hk' hsep'
    (fun y hy => hout y fun j hj he => hsep0 _ _ _ hal hpa y hy ⟨by omega, by omega⟩)
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun)) hstep).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩

end Cases

/-! ## The theorems -/

/-- One value of G32's kinds: `vk28_step`'s statement. -/
theorem vk32_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2}
    (hE : G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK32 lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s)
    (hu : ∀ x, (v.op = .ARM64MOVDnop ∨ v.op = .ARM64MOVDreg) → v.args[0]? = some x →
      ∃ r c, regHome? lc x = some r ∧ cls (lc.ty x) = some c ∧
        UOK m (some (r, c, lc.signOf lc.ctx.f.valueTab.size x)))
    (hpre : G14Pre lc s v)
    (hcall : CallOK H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hcallz : CallOKZ H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hicall : ICallOK H E (Link.byId sym text az ez ps.toList) ret lc s s' v m)
    (hwb : WbOK H E g (Link.byId sym text az ez ps.toList) lc s v m) (hclo : CloOK E s v m)
    (hgetg : GetGOK E v) (hmeq : MemEqOK H E g (Link.byId sym text az ez ps.toList) lc s v m)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' ∧ UOK m' (uEntry lc v) := by
  have same : ∀ m', (uEntry lc v = none) →
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' →
      LocMatch E s' bid (i + 1) m' → CoreInv E.ι (StkAt E) (kStep lc K v).get s' →
      SlotInv lc s' →
      ∃ E' m', E.Extends E' ∧ G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
        PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
        LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' ∧
        UOK m' (uEntry lc v) := fun m' hue h1 h2 h3 h4 => by
    rw [hue]
    exact ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩, trivial⟩
  cases hVK with
  | g28 _ _ _ _ _ hVK28 =>
    exact vk28_step hE F hhome hcf hv hVK28 hvs htemp hj hj' hreads hm hinv hu hpre hcall hcallz
      hicall hwb hclo hgetg hmeq hs
  | bin hop hsz hao hbo hro hw =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4⟩ := g32_bin (H := H) F hm hinv.core hinv.slots
      (kread_of_reads hreads) (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hbo
      hro hw hvs htemp hs
    exact same m' (by simp only [uEntry, narrowLd?_alu32 (aluOp32_bin hop)]) h1 h2 h3 h4
  | binK hop hsz hao hro hw =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4⟩ := g32_binK (H := H) F hm hinv.core hinv.slots
      (kread_of_reads hreads) (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hro
      hw hvs htemp hs
    exact same m' (by simp only [uEntry, narrowLd?_alu32 (aluOp32_binK hop)]) h1 h2 h3 h4
  | un hop hsz hao hro h8 hca =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4⟩ := g32_un (H := H) F hm hinv.core hinv.slots
      (kread_of_reads hreads) (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hro
      h8 hca hvs htemp hs
    exact same m' (by simp only [uEntry, narrowLd?_alu32 (aluOp32_un hop)]) h1 h2 h3 h4
  | csinc hop hsz hfa hfl hhn ho hco hcc hao hbo hro h8 hca hcb =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4⟩ := g32_csinc (H := H) F hm hinv.core hinv.slots
      (kread_of_reads hreads) (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hfa hfl
      hhn ho hco hcc hao hbo hro h8 hca hcb hvs htemp hs
    have halu : AluOp32 v.op := by unfold AluOp32; simp [hop]
    exact same m' (by simp only [uEntry, narrowLd?_alu32 halu]) h1 h2 h3 h4
  | stlr hop hsz3 hmt hhn haux hk0 hao hso hma hca hcs =>
    obtain ⟨hlcE, -, -, -, -, -, -, -, -, -, hF⟩ := hE.env.env.env.env
    have hsz := slot_sizes hlcE hcf hinv.slots
    obtain ⟨-, -, -, -, -, hnl⟩ := stlr_ne (lc := lc) hop
    obtain ⟨m', h1, h2, h3, h4⟩ := g32_stlr (H := H) F hF hsz hm hinv.core hinv.slots
      (kread_of_reads hreads) (knext_kStep fun _ => (hs_none hhn).noRegs) hj hj' hop hsz3 hmt
      hhn haux hk0 hao hso hma hca hcs hvs htemp hs
    exact same m' (by simp only [uEntry, hnl]) h1 h2 h3 h4

/-- One value of G32's kinds: `vk29_step`'s statement, carrying the table's invariant `UOKL`
across the value (`uStepL`; G32's ops empty the table). -/
theorem vk32_stepU {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)}
    (hE : G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK32 lc g v kd)
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
      UOKL m' (uStepL lc L v) := by
  have fin : VK32 lc g v kd → v.op ≠ .ARM64MOVDnop → v.op ≠ .ARM64MOVDreg →
      narrowLd? lc v = none →
      ∃ E' m', E.Extends E' ∧ G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
        PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
        LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' ∧
        UOKL m' (uStepL lc L v) := fun hVK' h1 h2 hnl => by
    have hue : uEntry lc v = none := by simp only [uEntry, hnl]
    obtain ⟨E', m', hx, hE', hp, hlm, hinv', -⟩ := vk32_step hE F hhome hcf hv hVK' hvs htemp hj
      hj' hreads hm hinv (fun x hop _ => absurd hop (by rintro (h | h) <;> contradiction)) hpre
      hcall hcallz hicall hwb hclo hgetg hmeq hs
    refine ⟨E', m', hx, hE', hp, hlm, hinv', ?_⟩
    rw [uStepL_other hue h1 h2]
    intro e he
    cases he
  cases hVK with
  | g28 _ _ _ _ _ hVK28 =>
    exact vk29_step hE F hhome hcf hv hVK28 hvs htemp hj hj' hreads hm hinv hL hmem hpre hcall
      hcallz hicall hwb hclo hgetg hmeq hs
  | bin hop hsz hao hbo hro hw =>
    obtain ⟨-, h1, h2, -, -⟩ := aluOp32_ne (aluOp32_bin hop)
    exact fin (.bin hop hsz hao hbo hro hw) h1 h2 (narrowLd?_alu32 (aluOp32_bin hop))
  | binK hop hsz hao hro hw =>
    obtain ⟨-, h1, h2, -, -⟩ := aluOp32_ne (aluOp32_binK hop)
    exact fin (.binK hop hsz hao hro hw) h1 h2 (narrowLd?_alu32 (aluOp32_binK hop))
  | un hop hsz hao hro h8 hca =>
    obtain ⟨-, h1, h2, -, -⟩ := aluOp32_ne (aluOp32_un hop)
    exact fin (.un hop hsz hao hro h8 hca) h1 h2 (narrowLd?_alu32 (aluOp32_un hop))
  | csinc hop hsz hfa hfl hhn ho hco hcc hao hbo hro h8 hca hcb =>
    have halu : AluOp32 v.op := by unfold AluOp32; simp [hop]
    obtain ⟨-, h1, h2, -, -⟩ := aluOp32_ne halu
    exact fin (.csinc hop hsz hfa hfl hhn ho hco hcc hao hbo hro h8 hca hcb) h1 h2
      (narrowLd?_alu32 halu)
  | stlr hop hsz3 hmt hhn haux hk0 hao hso hma hca hcs =>
    obtain ⟨-, h1, h2, -, -, hnl⟩ := stlr_ne (lc := lc) hop
    exact fin (.stlr hop hsz3 hmt hhn haux hk0 hao hso hma hca hcs) h1 h2 hnl

/-- **G32, values.** `g30_value`'s statement over `checkG32`, with the same premises. -/
theorem g32_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG32 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hu : UOKL m (uL lc blk i))
    (hpre : G14Pre lc s v)
    (hcall : CallOK H E g L lc s s' v m) (hcallz : CallOKZ H E g L lc s s' v m)
    (hicall : ICallOK H E L ret lc s s' v m)
    (hwb : WbOK H E g L lc s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hmeq : MemEqOK H E g L lc s v m) (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' ∧
      UOKL m' (uL lc blk (i + 1)) := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    exact g30_value (checkG30_of_32 hl hc) hE hbid hb hi hv hen hm hinv hu hpre hcall hcallz
      hicall hwb hclo hgetg hmeq hs
  | true =>
  rw [uL_succ hi hv]
  have hE0 := hE
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, hcf, hk, hlt, hnd, hblocks, -, hmovd⟩ :=
    checkG32_spec hl hc
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
  obtain ⟨htemp, hVK⟩ := vkind32_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  rw [kAt_succ hi hv]
  exact vk32_stepU hE0 F hhome hcf hv hVK hvs htemp hj hj' hreads hm hinv hu
    (fun x hop hx => movdOK29_spec hmovd hbid hb hi hv hop hx)
    hpre hcall hcallz hicall hwb hclo hgetg hmeq hs

/-- A nil check of G32's kinds is G7's. -/
theorem vk32_nil {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK32 lc g v kd)
    (hop : v.op = .ARM64LoweredNilCheck) : VK7 lc g v kd := by
  cases h with
  | g28 _ _ _ _ _ h => exact vk28_nil h hop
  | bin h => exact absurd hop (aluOp32_ne (aluOp32_bin h)).2.2.2.1
  | binK h => exact absurd hop (aluOp32_ne (aluOp32_binK h)).2.2.2.1
  | un h => exact absurd hop (aluOp32_ne (aluOp32_un h)).2.2.2.1
  | csinc h => rw [hop] at h; cases h
  | stlr h => exact absurd hop (stlr_ne (lc := lc) h).2.2.2.1

/-- **G32, nil panics.** `g30_nilPanic`'s statement over `checkG32`. -/
theorem g32_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG32 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  cases hl : lc.ctx.f.lowered with
  | false => exact g30_nilPanic (checkG30_of_32 hl hc) hE hbid hb hi hv hop hm hinv hs
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, -, -⟩ :=
    checkG32_spec hl hc
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
  obtain ⟨-, hVK⟩ := vkind32_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases vk32_nil hVK hop with
  | g6 hne _ => exact absurd hop hne
  | nil _ hsz2 _ _ hao hma =>
    exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao hma hvs hs

/-- **G32, bounds panics.** `g30_boundsPanic`'s statement over `checkG32`, under `BoundsOK`. -/
theorem g32_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG32 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hbok : BoundsOK H g L ps.toList)
    (hs : stepLoc env lc s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    exact g30_boundsPanic (checkG30_of_32 hl hc) hE hbid hb hi hv hop hm hinv hbok hs
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, hsyms, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, hpb, -⟩ :=
    checkG32_spec hl hc
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
  obtain ⟨-, hVK⟩ := vkind32_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases hVK with
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

/-- **G32, terminators.** `g30_term`'s statement over `checkG32`. -/
theorem g32_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG32 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s) (hpre : G1TermPre lc s blk)
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' ∧
      e.b ∈ lc.ctx.f.blocks.toList := by
  cases hl : lc.ctx.f.lowered with
  | false => exact g30_term (checkG30_of_32 hl hc) hE hbid hb hm hinv hpre ht
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome, -, hk, hlt, hnd, hblocks, -, -⟩ :=
    checkG32_spec hl hc
  exact termK_step hpcOf ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb
    hm hinv hpre ht

end GoFV.Proof.Gen
