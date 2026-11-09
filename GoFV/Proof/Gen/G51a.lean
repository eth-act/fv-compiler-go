import GoFV.Proof.Gen.G50
import GoFV.Proof.Gen.Spec51a

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G51, group A: `CSNEG`, `TSTW`, `CMN`, `CMNW`, `CMPshiftRA` (`docs/plans/proofs3.md` §4)

`vkind51a` (`GoFV/Gen/Check51a.lean`) accepts these ops; `VK51a` (`Spec51a.lean`) says what it
accepted. `runLoc` runs each as `Arm64.evalPure` on its arguments (`stepLoc_alu51a`):

* `CSNEG [cc] x y f` is `Arm64.csel` with `−y`: on flags related to `NZCV`, `x`'s or `−y`'s word on
  the result's low `c` bits (`valRel_csneg`, G32's `NEG` for the negation), the machine's
  `CSNEG cond, Rx, Ry, Rd` (`progStep_csneg`);
* `TSTW`, `CMNW x y` are `flags2w`/`cmp2w` on the low words of arguments of classes at least 32
  (`flagsRel_tstwReg`, `flagsRel_cmnwReg`), the machine's 32-bit `ANDS`/`ADDS` (`progStep_tstwReg`,
  `progStep_cmnwReg`);
* `CMN x y` is `cmpP` of the 64-bit `ADDS` (`flagsRel_cmnReg`, `progStep_cmnReg`);
* `CMPshiftRA [k] x y` is `cmpSh` of the `SUBS` of `x` and `y >> k` (`flagsRel_cmpShRA`, G41's
  `progStep_cmpShift` at shift kind 2).

On a pointer without an integer form `cmpP` gives `Z` clear when the other argument is a register,
and `cmpSh` when the first argument is such a pointer (`Arm64.zClear`), which the machine does not
compute. The run premise `Pre51a` (the first argument of `CMN` and `CMPshiftRA` and the second of
`CMN` are no such pointer, G1's `NoBarePtr`, as G41's `CmpPre`) excludes that case: a property of
the run, checkable on the state, not a trusted hook. None of these ops is in an upper-bit keep or
entry table: after each the table is empty (`uStep35_51a`). `vk51a_step` is one value.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The premise -/

/-- The first argument of `CMN` and `CMPshiftRA`, and the second of `CMN`, is no pointer without
an integer form (`NoBarePtr`). -/
def Pre51a (lc : LocCtx) (s : LocState) (v : Value) : Prop :=
  ((v.op = .ARM64CMN ∨ v.op = .ARM64CMPshiftRA) →
    ∀ a x, v.args[0]? = some a → s.read lc a = .ok x → NoBarePtr x) ∧
  (v.op = .ARM64CMN → ∀ a x, v.args[1]? = some a → s.read lc a = .ok x → NoBarePtr x)

/-! ## Ops -/

private theorem op51a_cases {op : Op} (h : op51a op = true) :
    op = .ARM64CSNEG ∨ op = .ARM64TSTW ∨ op = .ARM64CMN ∨ op = .ARM64CMNW ∨
      op = .ARM64CMPshiftRA := by
  simpa only [op51a, Bool.or_eq_true, beq_iff_eq, or_assoc] using h

/-- After a value of G51's group A the upper-bit table is empty. -/
private theorem uStep35_51a {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value}
    (hop : op51a v.op = true) : uStep35 lc L v = [] := by
  rcases op51a_cases hop with h | h | h | h | h <;>
    simp [uStep35, ldEntry35, loadOp?, narrowLoad?, pairOp35, uStep34, keep34, keep31, keepOp31,
      keepOp34, uStepL, uEntry, narrowLd?, loadIdxOp?, h]

section Steps

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

/-- The ops of G51's group A: `Arm64.evalPure` on the arguments read from their homes. -/
private theorem stepLoc_alu51a (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : op51a v.op = true) (h : stepLoc env lc s v = .ok s') :
    ∃ argv, v.args.toList.mapM (s.read lc) = .ok argv ∧
      s' = s.write lc v.id ((Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux argv).retypeL
        (lc.ty v.id)) := by
  rcases op51a_cases hop with hop | hop | hop | hop | hop <;>
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

/-- `CSNEG cond, Rn, Rm, Rd` (`cond` a `SPECIAL` operand `SPOP_EQ + k`, `k < 16`): `X kn` in `Rd`
when the condition holds on `NZCV`, else `−X km`. -/
theorem progStep_csneg {kn km kd x : Nat} {cc : Int} (hkn : kn < 32) (hkm : km < 32)
    (hkd : kd < 32) (hn : L.nextAddr p.id = some next) (has : p.as = .CSNEG)
    (hf : p.from_ = specA cc) (hcc : SPOP_EQ ≤ cc ∧ cc < SPOP_EQ + 16) (hr : p.reg = REG_R0 + kn)
    (hrest : p.rest = #[(x, regA (REG_R0 + km))]) (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      (if s.holds (BitVec.ofInt 4 (cc - SPOP_EQ)) then s.rX (BitVec.ofNat 5 kn)
        else -s.rX (BitVec.ofNat 5 km)) with pc := next } := by
  have hname : As.name .CSNEG = "CSNEG" := rfl
  have hsp : ProgOp.condOfSpecial (specA cc) = .ok (BitVec.ofInt 4 (cc - SPOP_EQ)) := by
    simp only [ProgOp.condOfSpecial, specA, hcc.1, hcc.2, decide_true, Bool.and_self,
      beq_self_eq_true, ↓reduceIte]
    rfl
  have hrest0 : (ProgCtx.mk L s p).rest 0 = .ok (regA (REG_R0 + km)) := by
    simp [ProgCtx.rest, hrest]
    rfl
  have he : progEffect ⟨L, s, p⟩ = .ok (effWd {} kd
      (if s.holds (BitVec.ofInt 4 (cc - SPOP_EQ)) then s.rX (BitVec.ofNat 5 kn)
        else -s.rX (BitVec.ofNat 5 km))) := by
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

/-- `CMN Rm, Rn`: the flags of the 64-bit `ADDS` of `X kn` and `X km`. -/
theorem progStep_cmnReg {kn km : Nat} (hkn : kn < 32) (hkm : km < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .CMN) (hf : p.from_ = regA (REG_R0 + km))
    (hr : p.reg = REG_R0 + kn) :
    progStep L p s = .ok { s with
      nzcv := (GoFV.SSA.Sem.addWithCarry (s.rX (BitVec.ofNat 5 kn)) (s.rX (BitVec.ofNat 5 km))
        false).2, pc := next } := by
  have hname : As.name .CMN = "CMN" := rfl
  have he : progEffect ⟨L, s, p⟩ = .ok { flags := some (GoFV.SSA.Sem.addWithCarry
      (s.rX (BitVec.ofNat 5 kn)) (s.rX (BitVec.ofNat 5 km)) false).2 } := by
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, hr, hf, regA, ProgOp.baseOf,
      ↓reduceIte, ProgOp.binNames, ctx_src_reg hkn, ctx_src_reg hkm, ProgOp.binOp,
      addSub_addFlags]
    rfl
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he rfl]
  rfl

/-- `CMNW Rm, Rn`: the flags of the 32-bit `ADDS` of the low words of `X kn` and `X km`. -/
theorem progStep_cmnwReg {kn km : Nat} (hkn : kn < 32) (hkm : km < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .CMNW) (hf : p.from_ = regA (REG_R0 + km))
    (hr : p.reg = REG_R0 + kn) :
    progStep L p s = .ok { s with
      nzcv := (GoFV.SSA.Sem.addWithCarry ((s.rX (BitVec.ofNat 5 kn)).setWidth 32)
        ((s.rX (BitVec.ofNat 5 km)).setWidth 32) false).2, pc := next } := by
  have hname : As.name .CMNW = "CMNW" := rfl
  have he : progEffect ⟨L, s, p⟩ = .ok { flags := some (GoFV.SSA.Sem.addWithCarry
      ((s.rX (BitVec.ofNat 5 kn)).setWidth 32) ((s.rX (BitVec.ofNat 5 km)).setWidth 32)
        false).2 } := by
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, hr, hf, regA, ProgOp.baseOf,
      ↓reduceIte, ProgOp.binNames, ProgOp.endsS, ProgOp.chopS, ctx_src_reg32 hkn,
      ctx_src_reg32 hkm, ProgOp.binOp, addSub_addFlags32]
    simp only [bind, Except.bind, pure, Except.pure, trunc_false_setWidth]
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he rfl]
  rfl

/-- `TSTW Rm, Rn`: `ANDS`' flags of the low words of `X kn` and `X km`. -/
theorem progStep_tstwReg {kn km : Nat} (hkn : kn < 32) (hkm : km < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .TSTW) (hf : p.from_ = regA (REG_R0 + km))
    (hr : p.reg = REG_R0 + kn) :
    progStep L p s = .ok { s with
      nzcv := logicFlags ((s.rX (BitVec.ofNat 5 kn)).setWidth 32 &&&
        (s.rX (BitVec.ofNat 5 km)).setWidth 32), pc := next } := by
  have hname : As.name .TSTW = "TSTW" := rfl
  have he : progEffect ⟨L, s, p⟩ = .ok { flags := some (logicFlags
      ((s.rX (BitVec.ofNat 5 kn)).setWidth 32 &&& (s.rX (BitVec.ofNat 5 km)).setWidth 32)) } := by
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, hr, hf, regA, ProgOp.baseOf,
      ↓reduceIte, ProgOp.binNames, ProgOp.endsS, ProgOp.chopS, ctx_src_reg32 hkn,
      ctx_src_reg32 hkm, ProgOp.binOp, logical_flags32, trunc_false_setWidth]
    simp only [bind, Except.bind, pure, Except.pure, trunc_false_setWidth]
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he rfl]
  rfl

end Progs

/-! ## Values -/

section Vals

variable {ι : Blk → Option (BitVec 64)}

private theorem res_int51a {t : Ty} (ht : t ≠ .bool) (r : BitVec 64) :
    Arm64.res t r = .int .w64 r := by
  cases t <;> first | rfl | exact absurd rfl ht

/-- `CSNEG [cc] x y f` on flags related to `NZCV`, of arguments of classes `ca`, `cb` at least the
result's class `c ≥ 8`: the machine's `CSNEG` word (`progStep_csneg`). -/
private theorem valRel_csneg (hA : AddrAgree ι) {t : Ty} {k : Int64} {x y f : Val}
    {X Y : BitVec 64} {nz : Flags} {c ca cb : Nat} {cnd : Cond} (hcd : Cond.ofAux k = some cnd)
    (hf : FlagsRel f nz) (hx : ValRel ι x X) (hy : ValRel ι y Y) (hfx : Fits ca x)
    (hfy : Fits cb y) (hc : cls t = some c) (h8 : 8 ≤ c) (hca : c ≤ ca) (hcb : c ≤ cb) :
    ValRel ι ((Arm64.csel t k (some (- ·)) [x, y, f]).retypeL t)
      (if cnd.holds nz then X else -Y) := by
  have ht := cls_ne_bool hc h8
  apply valRel_retypeL_lo hA hc ht
  unfold Arm64.csel Arm64.condOn
  rw [hcd]
  simp only [Option.bind_some]
  cases ho : cnd.onVal f with
  | none => trivial
  | some b =>
    rw [onVal_holds hf ho]
    cases b
    · have hn := lo_un32 hA .NEG hy hfy hcb ht (t := t)
      simp only [Arm64.op1] at hn
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases hry : Arm64.reg y with
      | none => trivial
      | some r =>
        rw [hry] at hn
        exact hn
    · exact lo_regVal hA hx hfx hca ht

/-- The `W` register of an argument of class at least 32: none, or the machine word's low word. -/
private theorem reg32_eq51a (hA : AddrAgree ι) {x : Val} {X : BitVec 64} {ca : Nat}
    (hx : ValRel ι x X) (hf : Fits ca x) (hca : 32 ≤ ca) :
    Arm64.reg32 x = none ∨ Arm64.reg32 x = some (X.setWidth 32) := by
  unfold Arm64.reg32
  cases hr : Arm64.reg x with
  | none => exact .inl rfl
  | some a =>
    refine .inr (congrArg some ?_)
    have := congrArg (BitVec.setWidth 32) (reg_low hA hx hf hr)
    simpa only [BitVec.setWidth_setWidth_of_le _ hca] using this

/-- `TSTW` of arguments of classes at least 32: the flags of the machine's `TSTW Rm, Rn`
(`progStep_tstwReg`). -/
private theorem flagsRel_tstwReg (hA : AddrAgree ι) {t : Ty} {k : Int64} {aux : Option AuxRef}
    {x y : Val} {X Y : BitVec 64} {ca cb : Nat} (hx : ValRel ι x X) (hy : ValRel ι y Y)
    (hfx : Fits ca x) (hfy : Fits cb y) (hca : 32 ≤ ca) (hcb : 32 ≤ cb) :
    FlagsRel (Arm64.evalPure .ARM64TSTW t k aux [x, y])
      (logicFlags (X.setWidth 32 &&& Y.setWidth 32)) := by
  show FlagsRel (Arm64.flags2w (fun a b => logicFlags (a &&& b)) [x, y]) _
  rcases reg32_eq51a hA hx hfx hca with h | h <;>
    rcases reg32_eq51a hA hy hfy hcb with h' | h' <;>
    simp only [Arm64.flags2w, h, h'] <;> first | trivial | exact ⟨rfl, rfl, rfl, rfl⟩

/-- `CMNW` of arguments of classes at least 32: the flags of the machine's `CMNW Rm, Rn`
(`progStep_cmnwReg`). -/
private theorem flagsRel_cmnwReg (hA : AddrAgree ι) {t : Ty} {k : Int64} {aux : Option AuxRef}
    {x y : Val} {X Y : BitVec 64} {ca cb : Nat} (hx : ValRel ι x X) (hy : ValRel ι y Y)
    (hfx : Fits ca x) (hfy : Fits cb y) (hca : 32 ≤ ca) (hcb : 32 ≤ cb) :
    FlagsRel (Arm64.evalPure .ARM64CMNW t k aux [x, y])
      (GoFV.SSA.Sem.addWithCarry (X.setWidth 32) (Y.setWidth 32) false).2 := by
  show FlagsRel (Arm64.cmp2w (fun a b => GoFV.SSA.Sem.addWithCarry a b false) [x, y]) _
  rcases reg32_eq51a hA hx hfx hca with h | h <;>
    rcases reg32_eq51a hA hy hfy hcb with h' | h' <;>
    simp only [Arm64.cmp2w, h, h'] <;> first | trivial | exact ⟨rfl, rfl, rfl, rfl⟩

/-- A 64-bit register content that is no pointer without an integer form: `poison`, or its
register is the machine word. -/
private theorem reg_or_poison51a (hA : AddrAgree ι) {x : Val} {X : BitVec 64}
    (hx : ValRel ι x X) (hf : Fits 64 x) (hp : NoBarePtr x) :
    x = .poison ∨ Arm64.reg x = some X := by
  rcases reg_cases41 hA hx hf with h | h
  · exact .inr h
  · cases x with
    | poison => exact .inl rfl
    | int w v => cases h
    | bool b => cases h
    | ptr q =>
      have := hp q rfl
      simp only [Arm64.reg] at h
      rw [h] at this
      cases this
    | _ => exact False.elim hf

/-- `CMN` of two 64-bit arguments neither of which is a pointer without an integer form: the
flags of the machine's `CMN Rm, Rn` (`progStep_cmnReg`). -/
private theorem flagsRel_cmnReg (hA : AddrAgree ι) {t : Ty} {k : Int64} {aux : Option AuxRef}
    {x y : Val} {X Y : BitVec 64} (hx : ValRel ι x X) (hy : ValRel ι y Y) (hfx : Fits 64 x)
    (hfy : Fits 64 y) (hpx : NoBarePtr x) (hpy : NoBarePtr y) :
    FlagsRel (Arm64.evalPure .ARM64CMN t k aux [x, y])
      (GoFV.SSA.Sem.addWithCarry X Y false).2 := by
  show FlagsRel (Arm64.cmpP (fun a b => GoFV.SSA.Sem.addWithCarry a b false) [x, y]) _
  rcases reg_or_poison51a hA hx hfx hpx with rfl | hrx
  · cases y <;> trivial
  · rcases reg_or_poison51a hA hy hfy hpy with rfl | hry
    · cases x with
      | ptr q =>
        simp only [Arm64.cmpP, hrx] <;> trivial
      | _ => trivial
    · simp only [Arm64.cmpP, hrx, hry]
      exact ⟨rfl, rfl, rfl, rfl⟩

/-- `CMPshiftRA [k]` of a first argument that is no pointer without an integer form: the flags of
the machine's `CMP Rm->k, Rn` (`progStep_cmpShift` at shift kind 2). -/
private theorem flagsRel_cmpShRA (hA : AddrAgree ι) {t : Ty} {k : Int64} {aux : Option AuxRef}
    {x y : Val} {X Y : BitVec 64} (hx : ValRel ι x X) (hy : ValRel ι y Y) (hfx : Fits 64 x)
    (hfy : Fits 64 y) (hp : NoBarePtr x) :
    FlagsRel (Arm64.evalPure .ARM64CMPshiftRA t k aux [x, y])
      (GoFV.SSA.Sem.Arm64.subFlags X (Sem.Arm64.Shift.apply (shK 2) Y k.toInt.toNat)).2 := by
  show FlagsRel
    (Arm64.cmpSh (fun a b => Arm64.subFlags a (Arm64.shifted (shK 2) k b)) [x, y]) _
  rcases reg_cases41 hA hy hfy with hry | hry
  · rcases reg_cases41 hA hx hfx with hrx | hrx
    · simp only [Arm64.cmpSh, hrx, hry]
      exact ⟨rfl, rfl, rfl, rfl⟩
    · simp only [Arm64.cmpSh, hrx, hry]
      cases x with
      | ptr q =>
        have := hp q rfl
        simp only [Arm64.reg] at hrx
        rw [hrx] at this
        cases this
      | _ => trivial
  · simp only [Arm64.cmpSh, hry]
    trivial

end Vals

/-! ## The cases -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- The fields of a Prog `csnegOK` accepts. -/
private theorem csnegOK_spec {cc rn rm rd : Int} {p : Prog} (h : csnegOK cc rn rm rd p = true) :
    p.as = .CSNEG ∧ p.from_ = specA cc ∧ p.reg = rn ∧ p.to = regA rd ∧ p.scond = 0 ∧
      p.regTo2 = 0 ∧ ∃ x, p.rest = #[(x, regA rm)] := by
  unfold csnegOK at h
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

/-- `CSNEG [cc] x y f`: `CSNEG cond, Rx, Ry, Rd` writes `x`'s word or `y`'s negation. -/
private theorem g51a_csneg (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {f : ID} {o : Op} {cc rn rm rd : Int} {ca cb c : Nat}
    (hop : v.op = .ARM64CSNEG) (hsz : v.args.size = 3) (hfa : v.args[2]? = some f)
    (hfl : (lc.ty f).isFlags = true) (hhn : lc.home f = none) (ho : ccOp? v.auxInt = some o)
    (hco : (Cond.ofOp o).isSome = true) (hcc : ARM64.condBits o = some cc)
    (hao : argObj lc v 0 = .ok (ca, rn)) (hbo : argObj lc v 1 = .ok (cb, rm))
    (hro : resObj lc v = .ok (c, rd)) (h8 : 8 ≤ c) (hca : c ≤ ca) (hcb : c ≤ cb)
    (hvs : OneAt2 psA j ⟨csnegOK cc rn rm rd, "CSNEG"⟩ j')
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
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu51a hl htemp (by rw [hop]; rfl) hs
  rw [arr3 hsz ha0 ha1 hfa] at hargv
  obtain rfl := mapM_res_three hargv hx hy (read_flags hl hhn hfl)
  rw [write_reg hvh hcv, hop, isFlags_eq hfl]
  obtain ⟨hfr, -⟩ := flags_retypeL hm.flags
  obtain ⟨hrange, hcond⟩ := cset_cond hcs hcc
  refine (op_reg2 (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_csneg hA hcd hfr hxv hyv hxf hyf hcv h8 hca hcb) (fits_retypeL hcv _)
    (knext_set hK hnp hvh hcv) (fun k hk hok => ?_)).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨has, hf, hr, ht, -, -, xr, hrest⟩ := csnegOK_spec hok
  rw [progStep_csneg hkn hkm hkd (nextAddr_pcAt F.nodup hk) has hf hrange hr hrest ht, wX_pc]
  simp only [MState.holds, hcond]
  rfl

/-- `CMN Rm, Rn` of two 64-bit arguments that are no pointers without an integer form. -/
private theorem g51a_cmn (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K') (hpre : Pre51a lc s v)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {rn rm : Int} (hop : v.op = .ARM64CMN) (hsz : v.args.size = 2)
    (hfl : (lc.ty v.id).isFlags = true) (hhn : lc.home v.id = none)
    (hao : argObj lc v 0 = .ok (64, rn)) (hbo : argObj lc v 1 = .ok (64, rm))
    (hvs : OneAt2 psA j (.ofShape { as := .CMN, from_ := regA rm, reg := rn }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hbo
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨km, hkm, rfl, hkkm⟩ := objOf?_some hor1
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨y, hy, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkkm
  have hpx := hpre.1 (.inl hop) a0 x ha0 hx
  have hpy := hpre.2 hop a1 y ha1 hy
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu51a hl htemp (by rw [hop]; rfl) hs
  rw [arr2 hsz ha0 ha1] at hargv
  obtain rfl := mapM_res_two hargv hx hy
  rw [write_flags hhn hfl, hop, isFlags_eq hfl]
  exact (op_flags F hm hinv hj hj' hvs
    (flags_retypeL (flagsRel_cmnReg hA hxv hyv hxf hyf hpx hpy)).1
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun)) (fun k hk hok => by
      obtain ⟨has, hf, hr, -, -⟩ := Shape.ok_eq hok
      rw [progStep_cmnReg hkn hkm (nextAddr_pcAt F.nodup hk) has hf hr] <;> rfl)).imp
    fun m' ⟨h1, h2, h3, _, _⟩ => ⟨h1, h2, h3, hsi⟩

/-- `TSTW`/`CMNW Rm, Rn` of two arguments of classes at least 32. -/
private theorem g51a_cmpW (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {ca cb : Nat} {rn rm : Int}
    (hop : v.op = .ARM64TSTW ∧ as = .TSTW ∨ v.op = .ARM64CMNW ∧ as = .CMNW)
    (hsz : v.args.size = 2) (hfl : (lc.ty v.id).isFlags = true) (hhn : lc.home v.id = none)
    (hao : argObj lc v 0 = .ok (ca, rn)) (hbo : argObj lc v 1 = .ok (cb, rm)) (hca : 32 ≤ ca)
    (hcb : 32 ≤ cb) (hvs : OneAt2 psA j (.ofShape { as, from_ := regA rm, reg := rn }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have h51 : op51a v.op = true := by rcases hop with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl
  have hnp : v.op ≠ .Phi := by rcases hop with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> nofun
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hbo
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨km, hkm, rfl, hkkm⟩ := objOf?_some hor1
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨y, hy, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkkm
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu51a hl htemp h51 hs
  rw [arr2 hsz ha0 ha1] at hargv
  obtain rfl := mapM_res_two hargv hx hy
  rw [write_flags hhn hfl, isFlags_eq hfl]
  have hKL := knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun)
  rcases hop with ⟨hop, rfl⟩ | ⟨hop, rfl⟩
  · rw [hop]
    exact (op_flags F hm hinv hj hj' hvs
      (flags_retypeL (flagsRel_tstwReg hA hxv hyv hxf hyf hca hcb)).1 hKL (fun k hk hok => by
        obtain ⟨has, hf, hr, -, -⟩ := Shape.ok_eq hok
        rw [progStep_tstwReg hkn hkm (nextAddr_pcAt F.nodup hk) has hf hr] <;> rfl)).imp
      fun m' ⟨h1, h2, h3, _, _⟩ => ⟨h1, h2, h3, hsi⟩
  · rw [hop]
    exact (op_flags F hm hinv hj hj' hvs
      (flags_retypeL (flagsRel_cmnwReg hA hxv hyv hxf hyf hca hcb)).1 hKL (fun k hk hok => by
        obtain ⟨has, hf, hr, -, -⟩ := Shape.ok_eq hok
        rw [progStep_cmnwReg hkn hkm (nextAddr_pcAt F.nodup hk) has hf hr] <;> rfl)).imp
      fun m' ⟨h1, h2, h3, _, _⟩ => ⟨h1, h2, h3, hsi⟩

/-- `CMP Rm->k, Rn` of two 64-bit arguments, the first no pointer without an integer form. -/
private theorem g51a_cmpShRA (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K') (hpre : Pre51a lc s v)
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {rn rm : Int} (hop : v.op = .ARM64CMPshiftRA) (hsz : v.args.size = 2)
    (hfl : (lc.ty v.id).isFlags = true) (hhn : lc.home v.id = none) (hk0 : 0 ≤ v.auxInt.toInt)
    (hk64 : v.auxInt.toInt < 64) (hao : argObj lc v 0 = .ok (64, rn))
    (hbo : argObj lc v 1 = .ok (64, rm))
    (hvs : OneAt2 psA j (.ofShape
      { as := .CMP, from_ := shiftA 2 rm v.auxInt.toInt.toNat, reg := rn }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hbo
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨km, hkm, rfl, hkkm⟩ := objOf?_some hor1
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨y, hy, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkkm
  have hpx := hpre.1 (.inr hop) a0 x ha0 hx
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_alu51a hl htemp (by rw [hop]; rfl) hs
  rw [arr2 hsz ha0 ha1] at hargv
  obtain rfl := mapM_res_two hargv hx hy
  rw [write_flags hhn hfl, hop, isFlags_eq hfl]
  have hkk : v.auxInt.toInt.toNat < 64 := by omega
  exact (op_flags F hm hinv hj hj' hvs
    (flags_retypeL (flagsRel_cmpShRA hA hxv hyv hxf hyf hpx)).1
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun)) (fun k hk hok => by
      obtain ⟨has, hf, hr, -, -⟩ := Shape.ok_eq hok
      rw [progStep_cmpShift hkn hkm (by decide : 2 < 3) hkk (nextAddr_pcAt F.nodup hk) has hf
        hr] <;> rfl)).imp
    fun m' ⟨h1, h2, h3, _, _⟩ => ⟨h1, h2, h3, hsi⟩

end Cases

/-! ## One value -/

/-- One value of G51's group A, under `Pre51a`: the machine runs its Prog, the states match
after it, the invariant holds with the class table `kStep`, and the upper-bit table after it is
empty. -/
theorem vk51a_step {env : Env} {H : Hooks} {lc : LocCtx} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)}
    (F : Facts lc sym text az ez ps.toList ret E) (hVK : VK51a lc v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s) (hpre : Pre51a lc s v)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E s' bid (i + 1) m' ∧ G3Inv E lc (kStep lc K v) s' ∧ UOKL m' (uStep35 lc L v) := by
  have hR := kread_of_reads hreads
  have hU : ∀ m', UOKL m' (uStep35 lc L v) := fun _ => by
    rw [uStep35_51a (vk51a_op hVK)]
    exact fun e he => by cases he
  cases hVK with
  | csneg hop hsz hfa hfl hhn ho hco hcc hao hbo hro h8 hca hcb =>
    obtain ⟨r, hvh, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4⟩ := g51a_csneg (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hfa hfl hhn ho hco hcc hao hbo
      hro h8 hca hcb hvs htemp hs
    exact ⟨m', h1, h2, ⟨h3, h4⟩, hU m'⟩
  | cmpW hop hsz hfl hhn hao hbo hca hcb =>
    obtain ⟨m', h1, h2, h3, h4⟩ := g51a_cmpW (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_none hhn).noRegs) hj hj' hop hsz hfl hhn hao hbo hca hcb hvs
      htemp hs
    exact ⟨m', h1, h2, ⟨h3, h4⟩, hU m'⟩
  | cmn hop hsz hfl hhn hao hbo =>
    obtain ⟨m', h1, h2, h3, h4⟩ := g51a_cmn (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_none hhn).noRegs) hpre hj hj' hop hsz hfl hhn hao hbo hvs
      htemp hs
    exact ⟨m', h1, h2, ⟨h3, h4⟩, hU m'⟩
  | cmpShRA hop hsz hfl hhn hk0 hk64 hao hbo =>
    obtain ⟨m', h1, h2, h3, h4⟩ := g51a_cmpShRA (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_none hhn).noRegs) hpre hj hj' hop hsz hfl hhn hk0 hk64 hao hbo
      hvs htemp hs
    exact ⟨m', h1, h2, ⟨h3, h4⟩, hU m'⟩

end GoFV.Proof.Gen
