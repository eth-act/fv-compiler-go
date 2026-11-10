import GoFV.Proof.Gen.G51b
import GoFV.Proof.Gen.Spec55b

variable [GoFV.SSA.Sem.Addrs]

/-!
# Soundness of the genssa validator's slice G55, group B: shifted `NEG`, `CLZW`, `MULL`, `EXTR`
(`docs/plans/proofs3.md` §4)

`vk55b_step`: one value of `VK55b` (`GoFV/Proof/Gen/Spec55b.lean`) steps the machine as `runLoc`
steps it, with no run premise and the empty upper-bit table after it.

`runLoc` runs the G55b ops as `Arm64.evalPure` of the arguments read from their homes
(`stepLoc_alu55b`).

* `NEGshiftXX [k] x` is `op1` of `-(x SHIFT k)` (`evalPure_negSh55b`), which the machine's
  `NEG Rm SHIFT k, Rd` computes through G27's shifted operand (`SUB` from `ZR`,
  `progStep_negSh55b`); the low bits of a negation read only the low bits of its operand (G32's
  `unF_low`), so as G51b's shifted `MVN` (`lo_negSh55b`).
* `CLZW x` is `op1w` of `clz` on the low word, zero-extended: `CLZW Rm, Rd` (`dp1Op`'s `CLZ` at
  32 bits, `progStep_clzw55b`) of an `x` of at least 32 bits (`lo_clzw55b`).
* `MULL x y` is `op2` of `smull`, which reads the low words: `SMULL Rm, Rn, Rd`
  (`progStep_smull55b`) of arguments of at least 32 bits (`lo_mull55b`).
* `EXTRconst`, `EXTRWconst [k] x y` are `op2`/`op2w` of `extr k` with `x` the high half:
  `EXTR`/`EXTRW $k, Rx, Ry, Rd` (`sized`, `progStep_extr55b`) of arguments of at least the width
  (`lo_extr55b`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The ops -/

theorem negSh55b?_some {op : Op} {typ : Nat} (h : negSh55b? op = some typ) :
    op = .ARM64NEGshiftLL ∧ typ = 0 ∨ op = .ARM64NEGshiftRL ∧ typ = 1 ∨
      op = .ARM64NEGshiftRA ∧ typ = 2 := by
  unfold negSh55b? at h
  split at h
  next h1 => cases h; exact .inl ⟨h1, rfl⟩
  next =>
    split at h
    next h1 => cases h; exact .inr (.inl ⟨h1, rfl⟩)
    next =>
      split at h
      next h1 => cases h; exact .inr (.inr ⟨h1, rfl⟩)
      next => cases h

theorem extr55b?_some {op : Op} {as : As} {w : Nat} (h : extr55b? op = some (as, w)) :
    op = .ARM64EXTRconst ∧ as = .EXTR ∧ w = 64 ∨ op = .ARM64EXTRWconst ∧ as = .EXTRW ∧ w = 32 := by
  unfold extr55b? at h
  split at h
  next h1 => cases h; exact .inl ⟨h1, rfl, rfl⟩
  next =>
    split at h
    next h1 => cases h; exact .inr ⟨h1, rfl, rfl⟩
    next => cases h

/-- The ops of G55b. -/
def AluOp55b (op : Op) : Prop :=
  op = .ARM64NEGshiftLL ∨ op = .ARM64NEGshiftRL ∨ op = .ARM64NEGshiftRA ∨ op = .ARM64CLZW ∨
    op = .ARM64MULL ∨ op = .ARM64EXTRconst ∨ op = .ARM64EXTRWconst

theorem aluOp55b_negSh {op : Op} {typ : Nat} (h : negSh55b? op = some typ) : AluOp55b op := by
  unfold AluOp55b
  rcases negSh55b?_some h with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp

theorem aluOp55b_extr {op : Op} {as : As} {w : Nat} (h : extr55b? op = some (as, w)) :
    AluOp55b op := by
  unfold AluOp55b
  rcases extr55b?_some h with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp

theorem aluOp55b_of {op : Op} (h : op55b op = true) : AluOp55b op := by
  simp only [op55b, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with ((h | h) | h) | h
  · cases hn : negSh55b? op with
    | none => rw [hn] at h; cases h
    | some typ => exact aluOp55b_negSh hn
  · unfold AluOp55b; simp [h]
  · unfold AluOp55b; simp [h]
  · cases he : extr55b? op with
    | none => rw [he] at h; cases h
    | some p => obtain ⟨as, w⟩ := p; exact aluOp55b_extr he

/-- G55b's ops are no `Phi`, no nil check and no bounds check. -/
theorem aluOp55b_facts {op : Op} (h : AluOp55b op) :
    op ≠ .Phi ∧ op ≠ .ARM64LoweredNilCheck ∧ pbOp op = false := by
  unfold AluOp55b at h
  rcases h with h | h | h | h | h | h | h <;> subst h <;> exact ⟨nofun, nofun, rfl⟩

/-- A G55b op empties G35's table. -/
theorem uStep35_alu55b {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value}
    (hop : AluOp55b v.op) : uStep35 lc L v = [] := by
  unfold AluOp55b at hop
  rcases hop with h | h | h | h | h | h | h <;>
    simp [uStep35, ldEntry35, loadOp?, narrowLoad?, pairOp35, uStep34, keep34, keep31, keepOp31,
      keepOp34, uStepL, uEntry, narrowLd?, loadIdxOp?, h]

/-- `Arm64.evalPure` of a shifted `NEG`: `op1` of the negation of the shifted register. -/
theorem evalPure_negSh55b {op : Op} {typ : Nat} (h : negSh55b? op = some typ) (t : Ty) (k : Int64)
    (aux : Option AuxRef) (argv : List Val) :
    Arm64.evalPure op t k aux argv =
      Arm64.op1 t (fun x => -(Sem.Arm64.Shift.apply (shK typ) x (Arm64.amt k))) argv := by
  rcases negSh55b?_some h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl

/-! ## `runLoc` -/

section Steps

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

/-- The ops of G55b: `Arm64.evalPure` on the arguments read from their homes. -/
theorem stepLoc_alu55b (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : AluOp55b v.op) (h : stepLoc env lc s v = .ok s') :
    ∃ argv, v.args.toList.mapM (s.read lc) = .ok argv ∧
      s' = s.write lc v.id ((Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux argv).retypeL
        (lc.ty v.id)) := by
  unfold AluOp55b at hop
  rcases hop with hop | hop | hop | hop | hop | hop | hop <;>
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

/-- The machine word of `CLZW`: the leading zeros of the low word, zero-extended. -/
def clzwF55b (x : BitVec 64) : BitVec 64 := (GoFV.SSA.Sem.Arm64.clz (x.setWidth 32)).setWidth 64

/-- The machine word of `EXTR` (`w = 64`) or `EXTRW` (else, on the low words, zero-extended) of
`n:m` from bit `k`. -/
def extrF55b (w k : Nat) (n m : BitVec 64) : BitVec 64 :=
  if w = 64 then GoFV.SSA.Sem.Arm64.extr k n m
  else (GoFV.SSA.Sem.Arm64.extr k (n.setWidth 32) (m.setWidth 32)).setWidth 64

section Progs

variable {L : Link} {p : Prog} {s : MState} {next : BitVec 64}

private theorem nNEG55b : As.NEG.name = "NEG" := rfl
private theorem nCLZW55b : As.CLZW.name = "CLZW" := rfl
private theorem nSMULL55b : As.SMULL.name = "SMULL" := rfl
private theorem nEXTR55b : As.EXTR.name = "EXTR" := rfl
private theorem nEXTRW55b : As.EXTRW.name = "EXTRW" := rfl
private theorem cCLZW55b : ProgOp.chopS "CLZW" 1 = "CLZ" := by decide
private theorem cEXTRW55b : ProgOp.chopS "EXTRW" 1 = "EXTR" := by decide

/-- `NEG Rm SHIFT k, Rd`: the negation of `X km` shifted by `k`. -/
theorem progStep_negSh55b {typ km kd k : Nat} (ht3 : typ < 3) (hkm : km < 32) (hkd : kd < 32)
    (hk : k < 64) (hn : L.nextAddr p.id = some next) (hpa : p.as = .NEG)
    (hf : p.from_ = shiftA typ (REG_R0 + km) k) (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      (unF .NEG (Sem.Arm64.Shift.apply (shK typ) (s.rX (BitVec.ofNat 5 km)) k)) with
      pc := next } := by
  have he : progEffect ⟨L, s, p⟩ = .ok (effWd {} kd
      (unF .NEG (Sem.Arm64.Shift.apply (shK typ) (s.rX (BitVec.ofNat 5 km)) k))) := by
    unfold progEffect
    simp (config := { decide := true }) only [hpa, nNEG55b, hf, ht, regA, ProgOp.baseOf,
      ↓reduceIte, ProgOp.binNames]
    rw [ctx_src_shift ht3 hkm hk]
    simp only [eff_wX_dest hkd]
    by_cases h : kd = 31 <;> simp (config := { decide := true }) [effWd, h, unF, ProgOp.binOp,
      addSub_sub] <;> rfl
  rw [progStep_eq hn (by simp [Prog.isSkip, hpa]) he
    (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]), wd_apply hkd]

/-- `CLZW Rm, Rd`: the leading zeros of the low word of `X km`. -/
theorem progStep_clzw55b {km kd : Nat} (hkm : km < 32) (hkd : kd < 32)
    (hn : L.nextAddr p.id = some next) (hpa : p.as = .CLZW) (hf : p.from_ = regA (REG_R0 + km))
    (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd) (clzwF55b (s.rX (BitVec.ofNat 5 km))) with
      pc := next } := by
  have he : progEffect ⟨L, s, p⟩ = .ok (effWd {} kd (clzwF55b (s.rX (BitVec.ofNat 5 km)))) := by
    unfold progEffect
    simp (config := { decide := true }) only [hpa, nCLZW55b, hf, ht, regA, ProgOp.baseOf,
      ↓reduceIte, ProgOp.binNames, ProgOp.endsS, cCLZW55b, ctx_x_r0 hkm]
    simp only [bind, Except.bind, eff_wX_dest hkd]
    simp [dp1Op, sized, clzwF55b]
  rw [progStep_eq hn (by simp [Prog.isSkip, hpa]) he
    (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]), wd_apply hkd]

/-- `SMULL Rm, Rn, Rd`: the signed product of the low words of `X kn` and `X km`. -/
theorem progStep_smull55b {kn km kd : Nat} (hkn : kn < 32) (hkm : km < 32) (hkd : kd < 32)
    (hn : L.nextAddr p.id = some next) (hpa : p.as = .SMULL) (hf : p.from_ = regA (REG_R0 + km))
    (hr : p.reg = REG_R0 + kn) (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      (GoFV.SSA.Sem.Arm64.smull (s.rX (BitVec.ofNat 5 kn)) (s.rX (BitVec.ofNat 5 km))) with
      pc := next } := by
  have hrn := rn_reg (c := ⟨L, s, p⟩) hr
  have he : progEffect ⟨L, s, p⟩ = .ok (effWd {} kd
      (GoFV.SSA.Sem.Arm64.smull (s.rX (BitVec.ofNat 5 kn)) (s.rX (BitVec.ofNat 5 km)))) := by
    unfold progEffect
    simp (config := { decide := true }) only [hpa, nSMULL55b, hf, ht, hrn, regA, ProgOp.baseOf,
      ↓reduceIte, ProgOp.binNames, ProgOp.endsS, ctx_src_reg hkn, ctx_src_reg hkm]
    simp only [bind, Except.bind, eff_wX_dest hkd]
    by_cases h : kd = 31 <;> simp (config := { decide := true }) [effWd, h, ProgOp.binOp] <;> rfl
  rw [progStep_eq hn (by simp [Prog.isSkip, hpa]) he
    (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]), wd_apply hkd]

/-- `EXTR`/`EXTRW $k, Rn, Rm, Rd` (`Rn` the `RestArgs` source): `extrF55b` of `X kn:X km`. -/
theorem progStep_extr55b {as : As} {w kn km kd x : Nat} {k : Int}
    (has : as = .EXTR ∧ w = 64 ∨ as = .EXTRW ∧ w = 32) (hkn : kn < 32) (hkm : km < 32)
    (hkd : kd < 32) (hn : L.nextAddr p.id = some next) (hpa : p.as = as)
    (hf : p.from_ = constA k) (hr : p.reg = REG_R0 + km)
    (hrest : p.rest = #[(x, regA (REG_R0 + kn))]) (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd) (extrF55b w k.toNat (s.rX (BitVec.ofNat 5 kn))
      (s.rX (BitVec.ofNat 5 km))) with pc := next } := by
  have hrest0 : (ProgCtx.mk L s p).rest 0 = .ok (regA (REG_R0 + kn)) := by
    simp [ProgCtx.rest, hrest]
    rfl
  have he : progEffect ⟨L, s, p⟩ = .ok (effWd {} kd (extrF55b w k.toNat
      (s.rX (BitVec.ofNat 5 kn)) (s.rX (BitVec.ofNat 5 km)))) := by
    rcases has with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    · unfold progEffect
      simp (config := { decide := true }) only [hpa, nEXTR55b, nEXTRW55b, hf, hr, ht, hrest0,
        regA, constA, ProgOp.baseOf, ↓reduceIte, ProgOp.binNames, ProgOp.endsS, cEXTRW55b,
        ctx_x_r0 hkm, ctx_x_r0 hkn]
      simp only [bind, Except.bind, ctx_x_r0 hkn, ctx_x_r0 hkm, eff_wX_dest hkd]
      simp [sized, extrF55b]
  have hsk : p.isSkip = false := by
    rcases has with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp [Prog.isSkip, hpa]
  rw [progStep_eq hn hsk he (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]),
    wd_apply hkd]

end Progs

/-! ## Values -/

section Vals

variable {ι : Blk → Option (BitVec 64)}

private theorem res_int55b {t : Ty} (ht : t ≠ .bool) (r : BitVec 64) :
    Arm64.res t r = .int .w64 r := by
  cases t <;> first | rfl | exact absurd rfl ht

private theorem fits_le55b {c : Nat} {x : Val} {r : BitVec 64} (hf : Fits c x)
    (hr : Arm64.reg x = some r) : c ≤ 64 := by
  cases x with
  | int w v => have : w.bits = c := hf; subst this; cases w <;> decide
  | bool b => have : c = 1 := hf; omega
  | ptr p => have : c = 64 := hf; omega
  | _ => cases hr

private theorem low_le55b {c ca : Nat} {a b : BitVec 64} (h : a.setWidth ca = b.setWidth ca)
    (hc : c ≤ ca) : a.setWidth c = b.setWidth c := by
  have := congrArg (BitVec.setWidth c) h
  simpa only [BitVec.setWidth_setWidth_of_le _ hc] using this

/-- The register of an argument of 64 bits is the machine word. -/
private theorem reg64_55b (hA : AddrAgree ι) {x : Val} {X a : BitVec 64} {cx : Nat}
    (hx : ValRel ι x X) (hfx : Fits cx x) (hcx : 64 ≤ cx) (hr : Arm64.reg x = some a) : a = X := by
  have h64 := fits_le55b hfx hr
  have : cx = 64 := by omega
  subst this
  simpa only [BitVec.setWidth_eq] using reg_low hA hx hfx hr

/-- The low word of an argument of at least 32 bits is the machine word's. -/
private theorem reg32_55b (hA : AddrAgree ι) {x : Val} {X : BitVec 64} {a : BitVec 32} {cx : Nat}
    (hx : ValRel ι x X) (hfx : Fits cx x) (hcx : 32 ≤ cx) (hr : Arm64.reg32 x = some a) :
    a = X.setWidth 32 := by
  unfold Arm64.reg32 at hr
  cases hr' : Arm64.reg x with
  | none => rw [hr'] at hr; cases hr
  | some b =>
    rw [hr'] at hr
    cases hr
    exact low_le55b (reg_low hA hx hfx hr') hcx

/-- `NEGshiftXX [k] x` of an argument of class `ca`, at least the result's class `c` for a left
shift, of 64 bits otherwise: `NEG Rm SHIFT k, Rd` (`progStep_negSh55b`) on the low `c` bits. -/
theorem lo_negSh55b (hA : AddrAgree ι) {op : Op} {t : Ty} {typ : Nat} {k : Int64}
    {aux : Option AuxRef} {x : Val} {X : BitVec 64} {c ca : Nat}
    (hop : negSh55b? op = some typ) (hx : ValRel ι x X) (hfx : Fits ca x) (hc : c ≤ 64)
    (hll : typ = 0 → c ≤ ca) (hrr : typ ≠ 0 → ca = 64) (ht : t ≠ .bool) :
    Lo ι c (Arm64.evalPure op t k aux [x])
      (unF .NEG (Sem.Arm64.Shift.apply (shK typ) X (Arm64.amt k))) := by
  rw [evalPure_negSh55b hop]
  simp only [Arm64.op1]
  cases hr : Arm64.reg x with
  | none => trivial
  | some a =>
    show Lo ι c (Arm64.res t _) _
    rw [res_int55b ht]
    have hxa := reg_low hA hx hfx hr
    have hsh : (Sem.Arm64.Shift.apply (shK typ) a (Arm64.amt k)).setWidth c =
        (Sem.Arm64.Shift.apply (shK typ) X (Arm64.amt k)).setWidth c := by
      by_cases h0 : typ = 0
      · subst h0
        exact shl_low (low_le55b hxa (hll rfl))
      · have hca := hrr h0
        subst hca
        have : a = X := by simpa only [BitVec.setWidth_eq] using hxa
        rw [this]
    exact unF_low .NEG hc hsh

/-- `CLZW x` of an argument of at least 32 bits: the machine's word (`clzwF55b`). -/
theorem lo_clzw55b (hA : AddrAgree ι) {t : Ty} {k : Int64} {aux : Option AuxRef} {cx : Nat}
    {x : Val} {X : BitVec 64} (hx : ValRel ι x X) (hfx : Fits cx x) (hcx : 32 ≤ cx)
    (ht : t ≠ .bool) :
    Lo ι 64 (Arm64.evalPure .ARM64CLZW t k aux [x]) (clzwF55b X) := by
  show Lo ι 64 (Arm64.op1w t _ [x]) _
  simp only [Arm64.op1w]
  cases hrx : Arm64.reg32 x with
  | none => trivial
  | some a =>
    rw [reg32_55b hA hx hfx hcx hrx]
    show Lo ι 64 (Arm64.res t _) _
    rw [res_int55b ht]
    rfl

/-- `MULL x y` of arguments of at least 32 bits: the machine's `smull`. -/
theorem lo_mull55b (hA : AddrAgree ι) {t : Ty} {k : Int64} {aux : Option AuxRef} {cx cy : Nat}
    {x y : Val} {X Y : BitVec 64} (hx : ValRel ι x X) (hy : ValRel ι y Y) (hfx : Fits cx x)
    (hfy : Fits cy y) (hcx : 32 ≤ cx) (hcy : 32 ≤ cy) (ht : t ≠ .bool) :
    Lo ι 64 (Arm64.evalPure .ARM64MULL t k aux [x, y]) (GoFV.SSA.Sem.Arm64.smull X Y) := by
  show Lo ι 64 (Arm64.op2 t GoFV.SSA.Sem.Arm64.smull [x, y]) _
  simp only [Arm64.op2]
  cases hrx : Arm64.reg x with
  | none => trivial
  | some a =>
    cases hry : Arm64.reg y with
    | none => trivial
    | some b =>
      have ha : a.setWidth 32 = X.setWidth 32 := low_le55b (reg_low hA hx hfx hrx) hcx
      have hb : b.setWidth 32 = Y.setWidth 32 := low_le55b (reg_low hA hy hfy hry) hcy
      show Lo ι 64 (Arm64.res t _) _
      rw [res_int55b ht]
      show (GoFV.SSA.Sem.Arm64.smull a b).setWidth 64 = (GoFV.SSA.Sem.Arm64.smull X Y).setWidth 64
      simp only [GoFV.SSA.Sem.Arm64.smull, ha, hb]

/-- `EXTRconst`, `EXTRWconst [k] x y` of arguments of at least the width `w`: the machine's word
(`extrF55b`). -/
theorem lo_extr55b (hA : AddrAgree ι) {op : Op} {t : Ty} {k : Int64} {aux : Option AuxRef}
    {as : As} {w ca cb : Nat} {x y : Val} {X Y : BitVec 64} (hop : extr55b? op = some (as, w))
    (hx : ValRel ι x X) (hy : ValRel ι y Y) (hfx : Fits ca x) (hfy : Fits cb y) (hca : w ≤ ca)
    (hcb : w ≤ cb) (ht : t ≠ .bool) :
    Lo ι 64 (Arm64.evalPure op t k aux [x, y]) (extrF55b w k.toInt.toNat X Y) := by
  rcases extr55b?_some hop with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · show Lo ι 64 (Arm64.op2 t _ [x, y]) _
    simp only [Arm64.op2]
    cases hrx : Arm64.reg x with
    | none => trivial
    | some a =>
      cases hry : Arm64.reg y with
      | none => trivial
      | some b =>
        rw [reg64_55b hA hx hfx hca hrx, reg64_55b hA hy hfy hcb hry]
        show Lo ι 64 (Arm64.res t _) _
        rw [res_int55b ht]
        rfl
  · show Lo ι 64 (Arm64.op2w t _ [x, y]) _
    simp only [Arm64.op2w]
    cases hrx : Arm64.reg32 x with
    | none => trivial
    | some a =>
      cases hry : Arm64.reg32 y with
      | none => trivial
      | some b =>
        rw [reg32_55b hA hx hfx hca hrx, reg32_55b hA hy hfy hcb hry]
        show Lo ι 64 (Arm64.res t _) _
        rw [res_int55b ht]
        rfl

end Vals

/-! ## The cases -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- `NEG Rm SHIFT k, Rd`. -/
theorem g55b_negSh (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {typ ca c : Nat} {rm rd : Int} (hop : negSh55b? v.op = some typ)
    (hsz : v.args.size = 1) (hk0 : 0 ≤ v.auxInt.toInt) (hk64 : v.auxInt.toInt < 64)
    (hao : argObj lc v 0 = .ok (ca, rm)) (hro : resObj lc v = .ok (c, rd)) (h8 : 8 ≤ c)
    (hll : typ = 0 → c ≤ ca) (hrr : typ ≠ 0 → ca = 64)
    (hvs : OneAt2 psA j (.ofShape
      { as := .NEG, from_ := shiftA typ rm v.auxInt.toInt.toNat, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have halu := aluOp55b_negSh hop
  have hnp : v.op ≠ .Phi := (aluOp55b_facts halu).1
  have ht3 : typ < 3 := by
    rcases negSh55b?_some hop with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨km, hkm, rfl, hkkm⟩ := objOf?_some hor0
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkm
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu55b hl htemp halu hs
  rw [arr1 hsz ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  rw [write_reg hvh hcv]
  have ht := cls_ne_bool hcv h8
  have hamt : Arm64.amt v.auxInt = v.auxInt.toInt.toNat := rfl
  have hk : v.auxInt.toInt.toNat < 64 := by omega
  have hlo := lo_negSh55b (k := v.auxInt) (aux := v.aux) (t := lc.ty v.id) hA hop hxv hxf
    (cls_le hcv) hll hrr ht
  rw [hamt] at hlo
  refine (op_reg2 (H := H) F hm hinv hj hj' hvs hd hkd hor (valRel_retypeL_lo hA hcv ht hlo)
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0' hok => ?_)).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨hpa, hf, -, ht', -⟩ := Shape.ok_eq hok
  rw [progStep_negSh55b ht3 hkm hkd hk (nextAddr_pcAt F.nodup hk0') hpa hf ht', wX_pc]
  rfl

/-- `CLZW Rm, Rd`. -/
theorem g55b_clzw (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {cx c : Nat} {rm rd : Int} (hop : v.op = .ARM64CLZW)
    (hsz : v.args.size = 1) (hao : argObj lc v 0 = .ok (cx, rm)) (hro : resObj lc v = .ok (c, rd))
    (h8 : 8 ≤ c) (hcx : 32 ≤ cx)
    (hvs : OneAt2 psA j (.ofShape { as := .CLZW, from_ := regA rm, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have halu : AluOp55b v.op := by unfold AluOp55b; simp [hop]
  have hnp : v.op ≠ .Phi := (aluOp55b_facts halu).1
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨km, hkm, rfl, hkkm⟩ := objOf?_some hor0
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkm
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu55b hl htemp halu hs
  rw [arr1 hsz ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  rw [write_reg hvh hcv]
  have ht := cls_ne_bool hcv h8
  rw [hop]
  refine (op_reg2 (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_retypeL_lo hA hcv ht ((lo_clzw55b hA hxv hxf hcx ht).mono (cls_le hcv)))
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0' hok => ?_)).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨hpa, hf, -, ht', -⟩ := Shape.ok_eq hok
  rw [progStep_clzw55b hkm hkd (nextAddr_pcAt F.nodup hk0') hpa hf ht', wX_pc]
  rfl

/-- `SMULL Rm, Rn, Rd`. -/
theorem g55b_mull (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {cx cy c : Nat} {rn rm rd : Int} (hop : v.op = .ARM64MULL)
    (hsz : v.args.size = 2) (hao : argObj lc v 0 = .ok (cx, rn)) (hbo : argObj lc v 1 = .ok (cy, rm))
    (hro : resObj lc v = .ok (c, rd)) (h8 : 8 ≤ c) (hcx : 32 ≤ cx) (hcy : 32 ≤ cy)
    (hvs : OneAt2 psA j (.ofShape { as := .SMULL, from_ := regA rm, reg := rn, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have halu : AluOp55b v.op := by unfold AluOp55b; simp [hop]
  have hnp : v.op ≠ .Phi := (aluOp55b_facts halu).1
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
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu55b hl htemp halu hs
  rw [arr2 hsz ha0 ha1] at hargv
  obtain rfl := mapM_res_two hargv hx hy
  rw [write_reg hvh hcv]
  have ht := cls_ne_bool hcv h8
  rw [hop]
  refine (op_reg2 (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_retypeL_lo hA hcv ht ((lo_mull55b hA hxv hyv hxf hyf hcx hcy ht).mono (cls_le hcv)))
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0' hok => ?_)).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨hpa, hf, hr, ht', -⟩ := Shape.ok_eq hok
  rw [progStep_smull55b hkn hkm hkd (nextAddr_pcAt F.nodup hk0') hpa hf hr ht', wX_pc]
  rfl

/-- `EXTR`/`EXTRW $k, Rn, Rm, Rd`. -/
theorem g55b_extr (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {w ca cb c : Nat} {rn rm rd : Int} (hop : extr55b? v.op = some (as, w))
    (hsz : v.args.size = 2) (hao : argObj lc v 0 = .ok (ca, rn)) (hbo : argObj lc v 1 = .ok (cb, rm))
    (hro : resObj lc v = .ok (c, rd)) (h8 : 8 ≤ c) (hca : w ≤ ca) (hcb : w ≤ cb)
    (hk0 : 0 ≤ v.auxInt.toInt)
    (hvs : OneAt2 psA j ⟨extrOK as v.auxInt.toInt rn rm rd, as.name⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have halu := aluOp55b_extr hop
  have hnp : v.op ≠ .Phi := (aluOp55b_facts halu).1
  have has : as = .EXTR ∧ w = 64 ∨ as = .EXTRW ∧ w = 32 := by
    rcases extr55b?_some hop with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ <;> simp
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
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu55b hl htemp halu hs
  rw [arr2 hsz ha0 ha1] at hargv
  obtain rfl := mapM_res_two hargv hx hy
  rw [write_reg hvh hcv]
  have ht := cls_ne_bool hcv h8
  refine (op_reg2 (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_retypeL_lo hA hcv ht ((lo_extr55b (k := v.auxInt) (aux := v.aux) hA hop hxv hyv hxf
      hyf hca hcb ht).mono (cls_le hcv)))
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0' hok => ?_)).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨hpa, hf, hr, ht', -, -, xr, hrest⟩ := extrOK_spec hok
  rw [progStep_extr55b has hkn hkm hkd (nextAddr_pcAt F.nodup hk0') hpa hf hr hrest ht', wX_pc]
  rfl

end Cases

/-! ## One value -/

/-- One value of G55b's kinds: it runs its one Prog, keeps the match and `G3Inv`, and empties the
upper-bit table. -/
theorem vk55b_step {env : Env} {H : Hooks} {lc : LocCtx} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)}
    (F : Facts lc sym text az ez ps.toList ret E) (hVK : VK55b lc v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s osp)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E s' bid (i + 1) m' ∧ G3Inv E lc (kStep lc K v) s' osp ∧
      UOKL m' (uStep35 lc L v) := by
  have hR := kread_of_reads hreads
  have fin : AluOp55b v.op → ∀ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' →
      LocMatch E s' bid (i + 1) m' → CoreInv E.ι (StkAt E) (kStep lc K v).get s' osp →
      SlotInv lc s' →
      ∃ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
        LocMatch E s' bid (i + 1) m' ∧ G3Inv E lc (kStep lc K v) s' osp ∧
        UOKL m' (uStep35 lc L v) := fun halu m' h1 h2 h3 h4 => by
    refine ⟨m', h1, h2, ⟨h3, h4⟩, ?_⟩
    rw [uStep35_alu55b halu]
    intro e he
    cases he
  cases hVK with
  | negSh hop hsz hk0 hk hao hro h8 hll hrr =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4⟩ := g55b_negSh (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hk0 hk hao hro h8 hll hrr hvs
      htemp hs
    exact fin (aluOp55b_negSh hop) m' h1 h2 h3 h4
  | clzw hop hsz hao hro h8 hcx =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4⟩ := g55b_clzw (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hro h8 hcx hvs htemp hs
    exact fin (by unfold AluOp55b; simp [hop]) m' h1 h2 h3 h4
  | mull hop hsz hao hbo hro h8 hcx hcy =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4⟩ := g55b_mull (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hbo hro h8 hcx hcy hvs htemp hs
    exact fin (by unfold AluOp55b; simp [hop]) m' h1 h2 h3 h4
  | extr hop hsz hao hbo hro h8 hca hcb hk0 hk =>
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4⟩ := g55b_extr (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hbo hro h8 hca hcb hk0 hvs
      htemp hs
    exact fin (aluOp55b_extr hop) m' h1 h2 h3 h4

end GoFV.Proof.Gen
