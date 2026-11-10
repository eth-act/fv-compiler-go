import GoFV.Proof.Gen.G38
import GoFV.Gen.Check61a

variable [GoFV.SSA.Sem.Addrs]

/-!
# The Progs of slice G61's group A under `runProg` (`docs/plans/proofs3.md` §4)

`progStep` of the load-exclusive `LDAXR*` (`progStep_ldaxr`: the zero extension of the `n` bytes,
as `LDAR*`), the store-exclusive `STLXR*` (`progStep_stlxr`: the low `n` bytes stored, the
status `R27` is 0: one core, `progEffect`'s exclusive store always succeeds), the
compare-and-swap `CASAL*` (`progStep_casal`: the old bytes to the compared register, the new
value stored when they equal it) and the other LSE instructions (`progStep_lse`: the old bytes to
the destination, `lseF` of them and the operand stored), and `ADD Rm, Rd` (`progStep_addTo`, the
two-operand form genssa emits after an atomic add).
-/

namespace GoFV.Proof.Gen

open GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64 GoFV.Gen.Check

/-- The combination `ProgOp.rmw` stores for an LSE family (`xchgV`: the operand, `addV`: the sum,
`andV`: the old value without the operand's bits, `orV`: with them). -/
def lseF (f : AtomF61) : BitVec 64 → BitVec 64 → BitVec 64 :=
  match f with
  | .xchgV => fun _ v => v
  | .addV => fun o v => o + v
  | .andV => fun o v => o &&& ~~~v
  | _ => fun o v => o ||| v

/-- An opcode name none of `progEffect`'s branches before the atomics takes. -/
private def atomPre (name : String) : Prop :=
  name ∉ ["TEXT", "FUNCDATA", "PCDATA", "NOP"] ∧
  ProgOp.baseOf name ProgOp.binNames = none ∧ ProgOp.baseOf name ["CMP", "CMN", "TST"] = none ∧
  ProgOp.baseOf name ["NEG", "NEGS", "MVN", "NGC", "NGCS"] = none ∧
  ProgOp.baseOf name ["CLZ", "RBIT", "REV", "REV16", "REV32"] = none ∧
  ProgOp.baseOf name ["MADD", "MSUB"] = none ∧
  ProgOp.baseOf name ["UBFX", "SBFX", "UBFIZ", "SBFIZ", "BFI", "BFXIL"] = none ∧
  ProgOp.baseOf name ["EXTR"] = none ∧
  ProgOp.baseOf name ["CSEL", "CSINC", "CSINV", "CSNEG"] = none ∧
  ProgOp.baseOf name ["CSET", "CSETM"] = none ∧ ProgOp.movMem name = none ∧
  ProgOp.pairOp name = none

/-- The load-exclusive of `n` bytes, by name. -/
private def ldaxPre (name : String) (n : Nat) : Prop :=
  atomPre name ∧ ProgOp.startsS name "LDAR" = false ∧ ProgOp.startsS name "LDAXR" = true ∧
  ProgOp.suffixBytes (ProgOp.dropS name 5) = n

/-- The store-exclusive of `n` bytes, by name. -/
private def stlxPre (name : String) (n : Nat) : Prop :=
  atomPre name ∧ ProgOp.startsS name "LDAR" = false ∧ ProgOp.startsS name "LDAXR" = false ∧
  ProgOp.startsS name "STLR" = false ∧ ProgOp.startsS name "STLXR" = true ∧
  ProgOp.suffixBytes (ProgOp.dropS name 5) = n

/-- `CASAL` of `n` bytes, by name. -/
private def casalPre (name : String) (n : Nat) : Prop :=
  atomPre name ∧ ProgOp.startsS name "LDAR" = false ∧ ProgOp.startsS name "LDAXR" = false ∧
  ProgOp.startsS name "STLR" = false ∧ ProgOp.startsS name "STLXR" = false ∧
  ProgOp.startsS name "CASAL" = true ∧ ProgOp.suffixBytes (ProgOp.dropS name 5) = n

/-- An LSE read-modify-write of `n` bytes combining with `F`, by name. -/
private def lsePre (name : String) (n : Nat) (F : BitVec 64 → BitVec 64 → BitVec 64) : Prop :=
  atomPre name ∧ ProgOp.startsS name "LDAR" = false ∧ ProgOp.startsS name "LDAXR" = false ∧
  ProgOp.startsS name "STLR" = false ∧ ProgOp.startsS name "STLXR" = false ∧
  ProgOp.startsS name "CASAL" = false ∧ ProgOp.rmw name = some (n, F)

private theorem ldaxPre_of {n : Nat} (hn : n = 8 ∨ n = 4 ∨ n = 1) :
    ldaxPre (llsc61 n).1.name n := by
  rcases hn with rfl | rfl | rfl <;> simp (config := { decide := true }) [ldaxPre, atomPre, llsc61]

private theorem stlxPre_of {n : Nat} (hn : n = 8 ∨ n = 4 ∨ n = 1) :
    stlxPre (llsc61 n).2.name n := by
  rcases hn with rfl | rfl | rfl <;> simp (config := { decide := true }) [stlxPre, atomPre, llsc61]

private theorem casalPre_of {n : Nat} (hn : n = 8 ∨ n = 4) :
    casalPre (lse61 .casV n).name n := by
  rcases hn with rfl | rfl <;> simp (config := { decide := true }) [casalPre, atomPre, lse61]

private theorem lsePre_of {f : AtomF61} {n : Nat}
    (hf : f = .xchgV ∧ (n = 8 ∨ n = 4 ∨ n = 1) ∨ f = .addV ∧ (n = 8 ∨ n = 4) ∨
      f = .andV ∧ (n = 8 ∨ n = 4 ∨ n = 1) ∨ f = .orV ∧ (n = 8 ∨ n = 4 ∨ n = 1)) :
    lsePre (lse61 f n).name n (lseF f) := by
  rcases hf with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ <;>
  · rcases hn with rfl | rfl | rfl <;>
      simp (config := { decide := true }) [lsePre, atomPre, lse61, lseF, ProgOp.rmw] <;> rfl

variable {L : Link} {p : Prog} {s : MState} {next : BitVec 64}

/-- `LDAXR{,W,B} (Rn), Rd` with the address `a` outside the nil page: the zero extension of the
`n` bytes at `a` in `X kd`. -/
theorem progStep_ldaxr {n kd : Nat} {a : BitVec 64} (hn' : n = 8 ∨ n = 4 ∨ n = 1) (hkd : kd < 32)
    (hn : L.nextAddr p.id = some next) (hpa : p.as = (llsc61 n).1)
    (hma : (ProgCtx.mk L s p).mem p.from_ = .ok (a, none))
    (ht : p.to = regA (REG_R0 + kd)) (hnil : nilPage a = false) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd) ((readMem s.mem a n).setWidth 64) with
      pc := next } := by
  have hp := ldaxPre_of hn'
  rw [← hpa] at hp
  obtain ⟨⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩, h12, h13, h14⟩ := hp
  have he : progEffect ⟨L, s, p⟩ =
      .ok (effWd { loads := [(a, n)] } kd ((readMem s.mem a n).setWidth 64)) := by
    unfold progEffect
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hma, ht, regA, Eff.ld,
      ProgCtx.load, Bool.false_or, Bool.false_eq_true, ↓reduceIte, h12, h13, h14, bind,
      Except.bind]
    rw [h12, if_neg Bool.false_ne_true, h14]
    exact eff_wX_dest hkd
  have hsk : p.isSkip = false := by
    rcases hn' with rfl | rfl | rfl <;> simp [Prog.isSkip, hpa, llsc61]
  have hnil' : (effWd { loads := [(a, n)] } kd ((readMem s.mem a n).setWidth 64)).nilAccess? =
      none := by
    by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?, List.find?, hnil]
  rw [progStep_eq hn hsk he hnil']
  by_cases h : kd = 31
  · subst h; rfl
  · simp only [effWd, h, ↓reduceIte, Eff.apply, List.foldr]
    rfl

/-- `STLXR{,W,B} Rs, (Rn), R27` with the address `a` outside the nil page: the low `n` bytes of
`X ks` stored at `a`, and the status `X27 = 0` (the store succeeds on one core). -/
theorem progStep_stlxr {n ks : Nat} {a : BitVec 64} (hn' : n = 8 ∨ n = 4 ∨ n = 1) (hks : ks < 32)
    (hn : L.nextAddr p.id = some next) (hpa : p.as = (llsc61 n).2)
    (hf : p.from_ = regA (REG_R0 + ks)) (hma : (ProgCtx.mk L s p).mem p.to = .ok (a, none))
    (ht2 : p.regTo2 = r27A) (hnil : nilPage a = false) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 27) 0 with
      mem := writeMem s.mem a n
        (BitVec.ofNat (8 * n) ((s.rX (BitVec.ofNat 5 ks)).toNat % 2 ^ (8 * n))),
      pc := next } := by
  have hp := stlxPre_of hn'
  rw [← hpa] at hp
  obtain ⟨⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩, h12, h13, h14, h15, h16⟩ := hp
  have he : progEffect ⟨L, s, p⟩ = .ok ({
      x := [(27, 0)]
      stores := [(a, n, (s.rX (BitVec.ofNat 5 ks)).toNat % 2 ^ (8 * n))] } : Eff) := by
    unfold progEffect
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hma, hf, ht2, regA,
      ctx_x_r0 hks, Bool.false_or, Bool.or_true, Bool.false_eq_true, ↓reduceIte, h12, h13, h14,
      h15, h16]
    rw [show r27A = REG_R0 + ((27 : Nat) : Int) from rfl, eff_wX_r0 (by omega)]
    rfl
  have hsk : p.isSkip = false := by
    rcases hn' with rfl | rfl | rfl <;> simp [Prog.isSkip, hpa, llsc61]
  rw [progStep_eq hn hsk he (by simp [Eff.nilAccess?, List.find?, hnil])]
  simp only [Eff.apply, List.foldr, List.foldl, Option.getD_none]
  simp only [MState.wX, show (BitVec.ofNat 5 27 : BitVec 5) ≠ 31 by decide, ↓reduceIte]

/-- `CASAL{D,W} Rs, (Rn), Rt` with the address `a` outside the nil page: the zero extension of
the `n` bytes at `a` in `X ks`, and, when they equal the low `n` bytes of `X ks`, the low `n`
bytes of `X kt` stored at `a`. -/
theorem progStep_casal {n ks kt : Nat} {a : BitVec 64} (hn' : n = 8 ∨ n = 4) (hks : ks < 31)
    (hkt : kt < 32) (hn : L.nextAddr p.id = some next) (hpa : p.as = lse61 .casV n)
    (hf : p.from_ = regA (REG_R0 + ks)) (hma : (ProgCtx.mk L s p).mem p.to = .ok (a, none))
    (ht2 : p.regTo2 = REG_R0 + kt) (hnil : nilPage a = false) :
    progStep L p s = .ok
      (if (readMem s.mem a n).setWidth 64 == ProgOp.maskN n (s.rX (BitVec.ofNat 5 ks)) then
        { s.wX (BitVec.ofNat 5 ks) ((readMem s.mem a n).setWidth 64) with
          mem := writeMem s.mem a n
            (BitVec.ofNat (8 * n) ((s.rX (BitVec.ofNat 5 kt)).toNat % 2 ^ (8 * n))),
          pc := next }
      else { s.wX (BitVec.ofNat 5 ks) ((readMem s.mem a n).setWidth 64) with pc := next }) := by
  have hp := casalPre_of hn'
  rw [← hpa] at hp
  obtain ⟨⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩, h12, h13, h14, h15, h16, h17⟩ := hp
  have hsk : p.isSkip = false := by
    rcases hn' with rfl | rfl <;> simp [Prog.isSkip, hpa, lse61]
  by_cases heq : (readMem s.mem a n).setWidth 64 == ProgOp.maskN n (s.rX (BitVec.ofNat 5 ks))
  · have he : progEffect ⟨L, s, p⟩ = .ok ({
        x := [(ks, (readMem s.mem a n).setWidth 64)]
        loads := [(a, n)]
        stores := [(a, n, (s.rX (BitVec.ofNat 5 kt)).toNat % 2 ^ (8 * n))] } : Eff) := by
      unfold progEffect
      simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hma, hf, ht2, regA, Eff.ld,
        ProgCtx.load, ctx_x_r0 (by omega : ks < 32), ctx_x_r0 hkt, Bool.false_or,
        Bool.false_eq_true, ↓reduceIte, h12, h13, h14, h15, h16, eff_wX_r0 hks, bind,
        Except.bind]
      rw [h17, if_pos heq]
      rfl
    rw [progStep_eq hn hsk he (by simp [Eff.nilAccess?, List.find?, hnil]), if_pos heq]
    simp only [Eff.apply, List.foldr, List.foldl, Option.getD_none]
    by_cases hc : (BitVec.ofNat 5 ks : BitVec 5) = 31 <;> simp only [MState.wX, hc, ↓reduceIte]
  · have he : progEffect ⟨L, s, p⟩ = .ok ({
        x := [(ks, (readMem s.mem a n).setWidth 64)]
        loads := [(a, n)] } : Eff) := by
      unfold progEffect
      simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hma, hf, ht2, regA, Eff.ld,
        ProgCtx.load, ctx_x_r0 (by omega : ks < 32), ctx_x_r0 hkt, Bool.false_or,
        Bool.false_eq_true, ↓reduceIte, h12, h13, h14, h15, h16, eff_wX_r0 hks, bind,
        Except.bind]
      rw [h17, if_neg heq]
      rfl
    rw [progStep_eq hn hsk he (by simp [Eff.nilAccess?, List.find?, hnil]), if_neg heq]
    simp only [Eff.apply, List.foldr, List.foldl, Option.getD_none]

/-- An LSE read-modify-write `op Rs, (Rn), Rt` of family `f` with the address `a` outside the nil
page: the zero extension of the `n` bytes at `a` in `X kt`, and the low `n` bytes of `lseF f` of
them and `X ks` stored at `a`. -/
theorem progStep_lse {f : AtomF61} {n ks kt : Nat} {a : BitVec 64}
    (hf' : f = .xchgV ∧ (n = 8 ∨ n = 4 ∨ n = 1) ∨ f = .addV ∧ (n = 8 ∨ n = 4) ∨
      f = .andV ∧ (n = 8 ∨ n = 4 ∨ n = 1) ∨ f = .orV ∧ (n = 8 ∨ n = 4 ∨ n = 1))
    (hks : ks < 32) (hkt : kt < 32) (hn : L.nextAddr p.id = some next) (hpa : p.as = lse61 f n)
    (hf : p.from_ = regA (REG_R0 + ks)) (hma : (ProgCtx.mk L s p).mem p.to = .ok (a, none))
    (ht2 : p.regTo2 = REG_R0 + kt) (hnil : nilPage a = false) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kt) ((readMem s.mem a n).setWidth 64) with
      mem := writeMem s.mem a n (BitVec.ofNat (8 * n) (ProgOp.maskN n
        (lseF f ((readMem s.mem a n).setWidth 64) (s.rX (BitVec.ofNat 5 ks)))).toNat),
      pc := next } := by
  have hp := lsePre_of hf'
  rw [← hpa] at hp
  obtain ⟨⟨-, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩, h12, h13, h14, h15, h16, h17⟩ := hp
  have hsk : p.isSkip = false := by
    rcases hf' with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | ⟨rfl, hn⟩ <;>
    · rcases hn with rfl | rfl | rfl <;> simp [Prog.isSkip, hpa, lse61]
  have he : progEffect ⟨L, s, p⟩ = .ok { (effWd { loads := [(a, n)] } kt
      ((readMem s.mem a n).setWidth 64)) with
        stores := [(a, n, (ProgOp.maskN n
          (lseF f ((readMem s.mem a n).setWidth 64) (s.rX (BitVec.ofNat 5 ks)))).toNat)] } := by
    unfold progEffect
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, hma, hf, ht2, regA, Eff.ld,
      ProgCtx.load, ctx_x_r0 hks, Bool.false_or, Bool.false_eq_true, ↓reduceIte, h12, h13, h14,
      h15, h16, h17, eff_wX_dest hkt, bind, Except.bind]
    rfl
  rw [progStep_eq hn hsk he (by by_cases h : kt = 31 <;>
    simp [effWd, h, Eff.nilAccess?, List.find?, hnil])]
  by_cases h : kt = 31
  · subst h
    simp only [effWd, ↓reduceIte, Eff.apply, List.foldr, List.foldl, Option.getD_none]
    simp only [MState.wX, show (BitVec.ofNat 5 31 : BitVec 5) = 31 by decide, ↓reduceIte]
  · simp only [effWd, h, ↓reduceIte, Eff.apply, List.foldr, List.foldl, Option.getD_none]
    by_cases hc : (BitVec.ofNat 5 kt : BitVec 5) = 31 <;> simp only [MState.wX, hc, ↓reduceIte]

theorem rn_to {c : ProgCtx} (h : c.p.reg = 0) : c.rn = c.p.to.reg := by
  simp [ProgCtx.rn, h]

/-- `ADD Rm, Rd` (`Rd` its own first operand): `X kd + X km` in `X kd`. -/
theorem progStep_addTo {km kd : Nat} (hkm : km < 32) (hkd : kd < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .ADD) (hf : p.from_ = regA (REG_R0 + km))
    (hr : p.reg = 0) (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      (s.rX (BitVec.ofNat 5 kd) + s.rX (BitVec.ofNat 5 km)) with pc := next } := by
  have hrn := rn_to (c := ⟨L, s, p⟩) hr
  rw [ht] at hrn
  have hname : As.name .ADD = "ADD" := rfl
  have he : progEffect ⟨L, s, p⟩ =
      .ok (effWd {} kd (s.rX (BitVec.ofNat 5 kd) + s.rX (BitVec.ofNat 5 km))) := by
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, hf, ht, hrn, regA, ProgOp.baseOf,
      ↓reduceIte, ProgOp.binNames, ctx_src_reg hkd, ctx_src_reg hkm, ProgOp.binOp, addSub_add]
    simp only [eff_wX_dest hkd]
    by_cases h : kd = 31 <;> simp [effWd, h] <;> rfl
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
    (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]), wd_apply hkd]

end GoFV.Proof.Gen
