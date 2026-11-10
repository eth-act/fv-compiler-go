import GoFV.Proof.Gen.G24
import GoFV.Proof.Gen.Spec25

variable [GoFV.SSA.Sem.Addrs]

/-!
# Soundness of the genssa validator's slice G25: conditional selects and bit tests
(`docs/plans/proofs3.md` §4)

`g25_value`, `g25_term`, `g25_nilPanic`, `g25_boundsPanic`: `g24_value`'s, `g24_term`'s,
`g24_nilPanic`'s and `g24_boundsPanic`'s statements over `checkG25`.

* `CSEL [cc] x y f` runs in `runLoc` as `Arm64.csel`: `x`'s or `y`'s register (`regVal`) by the
  condition `Cond.ofAux cc` on the flags argument, `poison` when a flag bit it reads is unknown
  (`stepLoc_g25`). genssa's `CSEL cond, Rx, Ry, Rd` writes `X[x]` or `X[y]` by `ConditionHolds`
  on `NZCV` (`progStep_csel`), for the condition `condBits` names (`cset_cond`). `FlagsRel` makes
  the two choices agree (`onVal_holds`), and the selected argument's register agrees with its
  machine word on the result's low bits (`lo_regVal`, `valRel_csel`, `g25_csel`). `CSEL0` is
  `CSEL cond, Rx, ZR, Rd`, its other value 0 (`valRel_csel0`, `g25_csel0`).
* `TSTconst [k] x` runs as `Arm64.flags1` of `logicFlags (x &&& k)`; `TST $k, Rn` sets `NZCV` to
  `ANDS`' flags of the same word (`progStep_tst`, `flagsRel_tst`, `g25_tst`). `TSTWconst` and
  `TSTW` are the same on the low words (`progStep_tstw`, `flagsRel_tstw`, `g25_tstw`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## Small facts -/

theorem mapM_res_three {α β : Type} {f : α → Res β} {a b c : α} {x y z : β} {ys : List β}
    (h : [a, b, c].mapM f = .ok ys) (hx : f a = .ok x) (hy : f b = .ok y) (hz : f c = .ok z) :
    ys = [x, y, z] := by
  obtain ⟨hlen, hk⟩ := mapM_res h
  match ys, hlen with
  | [x', y', z'], _ =>
    have h0 := hk 0 (by simp) (by simp)
    have h1 := hk 1 (by simp) (by simp)
    have h2 := hk 2 (by simp) (by simp)
    simp only [List.getElem_cons_zero, List.getElem_cons_succ, hx, hy, hz, Res.ok.injEq] at h0 h1 h2
    rw [h0, h1, h2]

/-- The condition `ccOp?` names is `Cond.ofAux`'s. -/
theorem ccOp?_ofAux {k : Int64} {o : Op} {c : Cond} (ho : ccOp? k = some o)
    (hc : Cond.ofOp o = some c) : Cond.ofAux k = some c := by
  unfold ccOp? at ho
  unfold Cond.ofAux
  split at ho
  · cases ho
  · rename_i hk
    simp only [hk, ↓reduceIte, ho, Option.bind_some, hc]

/-- The fields of a Prog `cselOK` accepts. -/
theorem cselOK_spec {cc rn rm rd : Int} {p : Prog} (h : cselOK cc rn rm rd p = true) :
    p.as = .CSEL ∧ p.from_ = specA cc ∧ p.reg = rn ∧ p.to = regA rd ∧ p.scond = 0 ∧
      p.regTo2 = 0 ∧ ∃ x, p.rest = #[(x, regA rm)] := by
  unfold cselOK at h
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

/-! ## `runLoc` -/

section Steps

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

/-- The selects and bit tests of G25: `Arm64.evalPure` on the arguments read from their homes. -/
theorem stepLoc_g25 (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .ARM64CSEL ∨ v.op = .ARM64CSEL0 ∨ v.op = .ARM64TSTconst ∨
      v.op = .ARM64TSTWconst)
    (h : stepLoc env lc s v = .ok s') :
    ∃ argv, v.args.toList.mapM (s.read lc) = .ok argv ∧
      s' = s.write lc v.id ((Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux argv).retypeL
        (lc.ty v.id)) := by
  rcases hop with hop | hop | hop | hop <;>
  · obtain ⟨argv, r, hm, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
      (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
      (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
    have he : evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) =
        .ok (Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux argv) := by
      unfold evalOpL; rw [hop]; rfl
    rw [he] at hr; cases hr
    exact ⟨argv, hm, rfl⟩

end Steps

/-- A select or bit test is none of the narrow loads (`narrowLd?`). -/
theorem narrowLd?_g25 {lc : LocCtx} {v : Value}
    (hop : v.op = .ARM64CSEL ∨ v.op = .ARM64CSEL0 ∨ v.op = .ARM64TSTconst ∨
      v.op = .ARM64TSTWconst) :
    narrowLd? lc v = none := by
  rcases hop with hop | hop | hop | hop <;> · unfold narrowLd?; rw [hop]; rfl

/-! ## The machine -/

section Progs

variable {L : Link} {p : Prog} {s : MState} {next : BitVec 64}

/-- `ANDS`' flags at 64 bits. -/
theorem logical_flags (x y : BitVec 64) : (logical true 3 x y).2 = logicFlags (x &&& y) := by
  simp [logical, sizedF]

/-- `ANDS`' flags at 32 bits. -/
theorem logical_flags32 (x y : BitVec 64) :
    (logical false 3 x y).2 = logicFlags (x.setWidth 32 &&& y.setWidth 32) := by
  simp [logical, sizedF]

/-- `TST $k, Rn`: `ANDS`' flags of `X kn` and `k`. -/
theorem progStep_tst {kn : Nat} {k : Int} (hkn : kn < 32) (hn : L.nextAddr p.id = some next)
    (has : p.as = .TST) (hf : p.from_ = constA k) (hr : p.reg = REG_R0 + kn) :
    progStep L p s = .ok { s with
      nzcv := logicFlags (s.rX (BitVec.ofNat 5 kn) &&& BitVec.ofInt 64 k), pc := next } := by
  have hname : As.name .TST = "TST" := rfl
  have he : progEffect ⟨L, s, p⟩ =
      .ok { flags := some (logicFlags (s.rX (BitVec.ofNat 5 kn) &&& BitVec.ofInt 64 k)) } := by
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, hr, hf, ProgOp.baseOf, ↓reduceIte,
      ProgOp.binNames, ctx_src_reg hkn, ctx_src_const, ProgOp.binOp, logical_flags]
    rfl
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he rfl]
  rfl

/-- `TSTW $k, Rn`: `ANDS`' flags of the low words of `X kn` and `k`. -/
theorem progStep_tstw {kn : Nat} {k : Int} (hkn : kn < 32) (hn : L.nextAddr p.id = some next)
    (has : p.as = .TSTW) (hf : p.from_ = constA k) (hr : p.reg = REG_R0 + kn) :
    progStep L p s = .ok { s with
      nzcv := logicFlags ((s.rX (BitVec.ofNat 5 kn)).setWidth 32 &&& BitVec.ofInt 32 k),
      pc := next } := by
  have hname : As.name .TSTW = "TSTW" := rfl
  have he : progEffect ⟨L, s, p⟩ = .ok { flags := some (logicFlags
      ((s.rX (BitVec.ofNat 5 kn)).setWidth 32 &&& BitVec.ofInt 32 k)) } := by
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, hr, hf, ProgOp.baseOf, ↓reduceIte,
      ProgOp.binNames, ProgOp.endsS, ProgOp.chopS, ctx_src_reg32 hkn, ctx_src_const32,
      ProgOp.binOp, logical_flags32, trunc_false_setWidth, ofInt_setWidth32]
    simp only [bind, Except.bind, pure, Except.pure, trunc_false_setWidth, ofInt_setWidth32]
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he rfl]
  rfl

/-- `CSEL cond, Rn, Rm, Rd` (`cond` a `SPECIAL` operand `SPOP_EQ + k`, `k < 16`): `X kn` in `Rd`
when the condition holds on `NZCV`, else `X km`. -/
theorem progStep_csel {kn km kd x : Nat} {cc : Int} (hkn : kn < 32) (hkm : km < 32) (hkd : kd < 32)
    (hn : L.nextAddr p.id = some next) (has : p.as = .CSEL) (hf : p.from_ = specA cc)
    (hcc : SPOP_EQ ≤ cc ∧ cc < SPOP_EQ + 16) (hr : p.reg = REG_R0 + kn)
    (hrest : p.rest = #[(x, regA (REG_R0 + km))]) (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      (if s.holds (BitVec.ofInt 4 (cc - SPOP_EQ)) then s.rX (BitVec.ofNat 5 kn)
        else s.rX (BitVec.ofNat 5 km)) with pc := next } := by
  have hname : As.name .CSEL = "CSEL" := rfl
  have hsp : ProgOp.condOfSpecial (specA cc) = .ok (BitVec.ofInt 4 (cc - SPOP_EQ)) := by
    simp only [ProgOp.condOfSpecial, specA, hcc.1, hcc.2, decide_true, Bool.and_self,
      beq_self_eq_true, ↓reduceIte]
    rfl
  have hrest0 : (ProgCtx.mk L s p).rest 0 = .ok (regA (REG_R0 + km)) := by
    simp [ProgCtx.rest, hrest]
    rfl
  have he : progEffect ⟨L, s, p⟩ = .ok (effWd {} kd
      (if s.holds (BitVec.ofInt 4 (cc - SPOP_EQ)) then s.rX (BitVec.ofNat 5 kn)
        else s.rX (BitVec.ofNat 5 km))) := by
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

private theorem low_le {c ca : Nat} {a b : BitVec 64} (h : a.setWidth ca = b.setWidth ca)
    (hc : c ≤ ca) : a.setWidth c = b.setWidth c := by
  have := congrArg (BitVec.setWidth c) h
  simpa only [BitVec.setWidth_setWidth_of_le _ hc] using this

private theorem res_int' {t : Ty} (ht : t ≠ .bool) (r : BitVec 64) :
    Arm64.res t r = .int .w64 r := by
  cases t <;> first | rfl | exact absurd rfl ht

/-- A register value moved unchanged (`regVal`), of an argument of class `ca ≥ c`: the machine
word on the low `c` bits. -/
theorem lo_regVal (hA : AddrAgree ι) {t : Ty} {x : Val} {X : BitVec 64} {c ca : Nat}
    (hx : ValRel ι x X) (hfx : Fits ca x) (hca : c ≤ ca) (ht : t ≠ .bool) :
    Lo ι c (Arm64.regVal t x) X := by
  by_cases hp : ∃ p, x = .ptr p
  · obtain ⟨p, rfl⟩ := hp
    exact Or.inr hx
  · have he : Arm64.regVal t x = match Arm64.reg x with
        | some r => Arm64.res t r
        | none => .poison := by
      cases x <;> first | rfl | exact absurd ⟨_, rfl⟩ hp
    rw [he]
    cases hr : Arm64.reg x with
    | none => trivial
    | some r =>
      show Lo ι c (Arm64.res t r) X
      rw [res_int' ht]
      exact low_le (reg_low hA hx hfx hr) hca

/-- `CSEL [cc] x y f` on flags related to `NZCV`, of arguments of classes `ca`, `cb` at least the
result's class `c ≥ 8`: the machine's `CSEL` word (`progStep_csel`). -/
theorem valRel_csel (hA : AddrAgree ι) {t : Ty} {k : Int64} {x y f : Val} {X Y : BitVec 64}
    {nz : Flags} {c ca cb : Nat} {cnd : Cond} (hcd : Cond.ofAux k = some cnd) (hf : FlagsRel f nz)
    (hx : ValRel ι x X) (hy : ValRel ι y Y) (hfx : Fits ca x) (hfy : Fits cb y)
    (hc : cls t = some c) (h8 : 8 ≤ c) (hca : c ≤ ca) (hcb : c ≤ cb) :
    ValRel ι ((Arm64.csel t k none [x, y, f]).retypeL t) (if cnd.holds nz then X else Y) := by
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
    · exact lo_regVal hA hy hfy hcb ht
    · exact lo_regVal hA hx hfx hca ht

/-- `CSEL0 [cc] x f`: as `valRel_csel` with 0 for `y` (`ZR`). -/
theorem valRel_csel0 (hA : AddrAgree ι) {t : Ty} {k : Int64} {x f : Val} {X : BitVec 64}
    {nz : Flags} {c ca : Nat} {cnd : Cond} (hcd : Cond.ofAux k = some cnd) (hf : FlagsRel f nz)
    (hx : ValRel ι x X) (hfx : Fits ca x) (hc : cls t = some c) (h8 : 8 ≤ c) (hca : c ≤ ca) :
    ValRel ι ((Arm64.csel0 t k [x, f]).retypeL t) (if cnd.holds nz then X else 0) := by
  have ht := cls_ne_bool hc h8
  apply valRel_retypeL_lo hA hc ht
  unfold Arm64.csel0 Arm64.condOn
  rw [hcd]
  simp only [Option.bind_some]
  cases ho : cnd.onVal f with
  | none => trivial
  | some b =>
    rw [onVal_holds hf ho]
    cases b
    · show Lo ι c (Arm64.res t 0) 0
      rw [res_int' ht]
      rfl
    · exact lo_regVal hA hx hfx hca ht

/-- Words agreeing below `ca` agree under a mask with no bit at or above `ca`. -/
private theorem and_low {n ca : Nat} {r X K : BitVec n}
    (h : ∀ i, i < ca → r.getLsbD i = X.getLsbD i) (hK : ∀ i, ca ≤ i → K.getLsbD i = false) :
    r &&& K = X &&& K := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_and]
  by_cases hic : i < ca
  · rw [h i hic]
  · rw [hK i (by omega), Bool.and_false, Bool.and_false]

private theorem bits_of_setWidth {n ca : Nat} {r X : BitVec n} (h : r.setWidth ca = X.setWidth ca) :
    ∀ i, i < ca → r.getLsbD i = X.getLsbD i := by
  intro i hi
  have := congrArg (fun y : BitVec ca => y.getLsbD i) h
  simpa [BitVec.getLsbD_setWidth, hi] using this

/-- The constant of a test of datasize `w` that `tstOK` accepts for class `ca` has no bit at or
above `ca`. -/
private theorem tst_mask {w ca : Nat} {k : Int} (h : tstOK w ca k = true) :
    ∀ i, ca ≤ i → (BitVec.ofInt w k).getLsbD i = false := by
  intro i hi
  unfold tstOK at h
  simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h
  by_cases hiw : w ≤ i
  · exact BitVec.getLsbD_of_ge _ _ hiw
  · rcases h with h | ⟨h0, hk⟩
    · omega
    · rw [BitVec.getLsbD, BitVec.toNat_ofInt]
      apply Nat.testBit_lt_two_pow
      have hk' : k < ((2 ^ ca : Nat) : Int) := by exact_mod_cast hk
      have hpw : 2 ^ ca ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega)
      have hpi : 2 ^ ca ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hi
      have hmod : k % ((2 ^ w : Nat) : Int) = k := Int.emod_eq_of_lt h0 (by omega)
      rw [hmod]
      omega

/-- `TSTconst [k]` of an argument whose bits it reads are known (`tstOK`): the flags of the
machine's `TST $k, Rn` (`progStep_tst`), at the flags shape. -/
theorem flagsRel_tst (hA : AddrAgree ι) {t : Ty} {k : Int64} {aux : Option AuxRef} {x : Val}
    {X : BitVec 64} {ca : Nat} (hx : ValRel ι x X) (hfx : Fits ca x)
    (hok : tstOK 64 ca k.toInt = true) :
    FlagsRel ((Arm64.evalPure .ARM64TSTconst t k aux [x]).retypeL Ty.flags)
      (logicFlags (X &&& BitVec.ofInt 64 k.toInt)) := by
  refine (flags_retypeL ?_).1
  show FlagsRel (Arm64.flags1 (fun a => logicFlags (a &&& Arm64.imm k)) [x]) _
  simp only [Arm64.flags1]
  cases hr : Arm64.reg x with
  | none => trivial
  | some r =>
    have he : r &&& Arm64.imm k = X &&& BitVec.ofInt 64 k.toInt :=
      and_low (bits_of_setWidth (reg_low hA hx hfx hr)) (tst_mask hok)
    simp only [he]
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- `TSTWconst [k]` of an argument whose bits it reads are known (`tstOK`): the flags of the
machine's `TSTW $k, Rn` (`progStep_tstw`), at the flags shape. -/
theorem flagsRel_tstw (hA : AddrAgree ι) {t : Ty} {k : Int64} {aux : Option AuxRef} {x : Val}
    {X : BitVec 64} {ca : Nat} (hx : ValRel ι x X) (hfx : Fits ca x)
    (hok : tstOK 32 ca k.toInt = true) :
    FlagsRel ((Arm64.evalPure .ARM64TSTWconst t k aux [x]).retypeL Ty.flags)
      (logicFlags (X.setWidth 32 &&& BitVec.ofInt 32 k.toInt)) := by
  refine (flags_retypeL ?_).1
  show FlagsRel (Arm64.flags1w (fun a => logicFlags (a &&& Arm64.imm32 k)) [x]) _
  simp only [Arm64.flags1w, Arm64.reg32]
  cases hr : Arm64.reg x with
  | none => trivial
  | some r =>
    have hb := bits_of_setWidth (reg_low hA hx hfx hr)
    have he : r.setWidth 32 &&& Arm64.imm32 k = X.setWidth 32 &&& BitVec.ofInt 32 k.toInt := by
      refine and_low (fun i hi => ?_) (tst_mask hok)
      simp only [BitVec.getLsbD_setWidth]
      rw [hb i hi]
    simp only [Option.map_some, he]
    exact ⟨rfl, rfl, rfl, rfl⟩

end Vals

/-! ## The cases -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- `CSEL [cc] x y f`: `CSEL cond, Rx, Ry, Rd` writes the selected argument's word. -/
theorem g25_csel (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {f : ID} {o : Op} {cc rn rm rd : Int} {ca cb c : Nat}
    (hop : v.op = .ARM64CSEL) (hsz : v.args.size = 3) (hfa : v.args[2]? = some f)
    (hfl : (lc.ty f).isFlags = true) (hhn : lc.home f = none) (ho : ccOp? v.auxInt = some o)
    (hco : (Cond.ofOp o).isSome = true) (hcc : ARM64.condBits o = some cc)
    (hao : argObj lc v 0 = .ok (ca, rn)) (hbo : argObj lc v 1 = .ok (cb, rm))
    (hro : resObj lc v = .ok (c, rd)) (h8 : 8 ≤ c) (hca : c ≤ ca) (hcb : c ≤ cb)
    (hvs : OneAt2 psA j ⟨cselOK cc rn rm rd, "CSEL"⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      XW lc v m m' := by
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
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_g25 hl htemp (Or.inl hop) hs
  rw [arr3 hsz ha0 ha1 hfa] at hargv
  obtain rfl := mapM_res_three hargv hx hy (read_flags hl hhn hfl)
  rw [write_reg hvh hcv, hop, isFlags_eq hfl]
  obtain ⟨hfr, -⟩ := flags_retypeL hm.flags
  obtain ⟨hrange, hcond⟩ := cset_cond hcs hcc
  refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_csel hA hcd hfr hxv hyv hxf hyf hcv h8 hca hcb) (fits_retypeL hcv _)
    (knext_set hK hnp hvh hcv) (fun k hk hok => ?_)).imp
    fun m' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, hsi, .inr ⟨r, kd, _, hvh, hor, h4⟩⟩
  obtain ⟨has, hf, hr, ht, -, -, xr, hrest⟩ := cselOK_spec hok
  rw [progStep_csel hkn hkm hkd (nextAddr_pcAt F.nodup hk) has hf hrange hr hrest ht, wX_pc]
  simp only [MState.holds, hcond]
  rfl

/-- `CSEL0 [cc] x f`: `CSEL cond, Rx, ZR, Rd` writes `x`'s word or 0. -/
theorem g25_csel0 (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {f : ID} {o : Op} {cc rn rd : Int} {ca c : Nat}
    (hop : v.op = .ARM64CSEL0) (hsz : v.args.size = 2) (hfa : v.args[1]? = some f)
    (hfl : (lc.ty f).isFlags = true) (hhn : lc.home f = none) (ho : ccOp? v.auxInt = some o)
    (hco : (Cond.ofOp o).isSome = true) (hcc : ARM64.condBits o = some cc)
    (hao : argObj lc v 0 = .ok (ca, rn)) (hro : resObj lc v = .ok (c, rd)) (h8 : 8 ≤ c)
    (hca : c ≤ ca) (hvs : OneAt2 psA j ⟨cselOK cc rn (REG_R0 + 31) rd, "CSEL"⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      XW lc v m m' := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨cnd, hcs⟩ := Option.isSome_iff_exists.1 hco
  have hcd := ccOp?_ofAux ho hcs
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kd, hkd, rfl, -⟩ := objOf?_some hor
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_g25 hl htemp (Or.inr (Or.inl hop)) hs
  rw [arr2 hsz ha0 hfa] at hargv
  obtain rfl := mapM_res_two hargv hx (read_flags hl hhn hfl)
  rw [write_reg hvh hcv, hop, isFlags_eq hfl]
  obtain ⟨hfr, -⟩ := flags_retypeL hm.flags
  obtain ⟨hrange, hcond⟩ := cset_cond hcs hcc
  refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor
    (valRel_csel0 hA hcd hfr hxv hxf hcv h8 hca) (fits_retypeL hcv _)
    (knext_set hK hnp hvh hcv) (fun k hk hok => ?_)).imp
    fun m' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, hsi, .inr ⟨r, kd, _, hvh, hor, h4⟩⟩
  obtain ⟨has, hf, hr, ht, -, -, xr, hrest⟩ := cselOK_spec hok
  rw [progStep_csel (km := 31) hkn (by omega) hkd (nextAddr_pcAt F.nodup hk) has hf hrange hr
    (by rw [hrest]; rfl) ht, wX_pc, rX_31]
  simp only [MState.holds, hcond]
  rfl

/-- `TST $k, Rn`, the bits it reads of the argument known (`tstOK`). -/
theorem g25_tst (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {ca : Nat} {rn : Int}
    (hop : v.op = .ARM64TSTconst) (hsz1 : v.args.size = 1) (hfl : (lc.ty v.id).isFlags = true)
    (hhn : lc.home v.id = none) (hao : argObj lc v 0 = .ok (ca, rn))
    (hok : tstOK 64 ca v.auxInt.toInt = true)
    (hvs : OneAt2 psA j (.ofShape { as := .TST, from_ := constA v.auxInt.toInt, reg := rn }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      XW lc v m m' := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_g25 hl htemp (Or.inr (Or.inr (Or.inl hop))) hs
  rw [arr1 hsz1 ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  rw [write_flags hhn hfl, hop, isFlags_eq hfl]
  exact (op_flags F hm hinv hj hj' hvs (flagsRel_tst hA hxv hxf hok)
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun)) (fun k hk hok => by
      obtain ⟨has, hf, hr, -, -⟩ := Shape.ok_eq hok
      rw [progStep_tst hkn (nextAddr_pcAt F.nodup hk) has hf hr] <;> rfl)).imp
    fun m' ⟨h1, h2, h3, _, h5⟩ => ⟨h1, h2, h3, hsi, .inl h5⟩

/-- `TSTW $k, Rn`, the bits it reads of the argument known (`tstOK`). -/
theorem g25_tstw (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {ca : Nat} {rn : Int}
    (hop : v.op = .ARM64TSTWconst) (hsz1 : v.args.size = 1) (hfl : (lc.ty v.id).isFlags = true)
    (hhn : lc.home v.id = none) (hao : argObj lc v 0 = .ok (ca, rn))
    (hok : tstOK 32 ca v.auxInt.toInt = true)
    (hvs : OneAt2 psA j (.ofShape { as := .TSTW, from_ := constA v.auxInt.toInt, reg := rn }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      XW lc v m m' := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_g25 hl htemp (Or.inr (Or.inr (Or.inr hop))) hs
  rw [arr1 hsz1 ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  rw [write_flags hhn hfl, hop, isFlags_eq hfl]
  exact (op_flags F hm hinv hj hj' hvs (flagsRel_tstw hA hxv hxf hok)
    (knext_same hK (Or.inr fun _ _ => by rw [hhn]; nofun)) (fun k hk hok => by
      obtain ⟨has, hf, hr, -, -⟩ := Shape.ok_eq hok
      rw [progStep_tstw hkn (nextAddr_pcAt F.nodup hk) has hf hr] <;> rfl)).imp
    fun m' ⟨h1, h2, h3, _, h5⟩ => ⟨h1, h2, h3, hsi, .inl h5⟩

end Cases

/-! ## The theorems -/

/-- One value of G25's kinds: `vk24_step`'s statement. -/
theorem vk25_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2}
    (hE : G10Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK25 lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s osp)
    (hu : ∀ x, (v.op = .ARM64MOVDnop ∨ v.op = .ARM64MOVDreg) → v.args[0]? = some x →
      ∃ r c, regHome? lc x = some r ∧ cls (lc.ty x) = some c ∧
        UOK m (some (r, c, lc.signOf lc.ctx.f.valueTab.size x)))
    (hpre : G14Pre lc s v)
    (hcall : CallOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hcallz : CallOKZAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hicall : ICallOKAt osp H E (Link.byId sym text az ez ps.toList) ret lc s s' v m)
    (hwb : WbOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s v m) (hclo : CloOK E s v m)
    (hgetg : GetGOK E v) (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G10Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp ∧ UOK m' (uEntry lc v) := by
  have hR := kread_of_reads hreads
  cases hVK with
  | g24 _ _ hVK24 =>
    exact vk24_step hE F hhome hcf hv hVK24 hvs htemp hj hj' hreads hm hinv hu hpre hcall hcallz
      hicall hwb hclo hgetg hs
  | csel hop hsz hfa hfl hhn ho hco hcc hao hbo hro h8 hca hcb =>
    have hue : uEntry lc v = none := by simp only [uEntry, narrowLd?_g25 (Or.inl hop)]
    rw [hue]
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g25_csel (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hfa hfl hhn ho hco hcc hao hbo
      hro h8 hca hcb hvs htemp hs
    exact ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩, trivial⟩
  | csel0 hop hsz hfa hfl hhn ho hco hcc hao hro h8 hca =>
    have hue : uEntry lc v = none := by simp only [uEntry, narrowLd?_g25 (Or.inr (Or.inl hop))]
    rw [hue]
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g25_csel0 (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hfa hfl hhn ho hco hcc hao hro
      h8 hca hvs htemp hs
    exact ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩, trivial⟩
  | tst hop hsz1 hfl hhn hao hok =>
    have hue : uEntry lc v = none := by
      simp only [uEntry, narrowLd?_g25 (Or.inr (Or.inr (Or.inl hop)))]
    rw [hue]
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g25_tst (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_none hhn).noRegs) hj hj' hop hsz1 hfl hhn hao hok hvs htemp hs
    exact ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩, trivial⟩
  | tstw hop hsz1 hfl hhn hao hok =>
    have hue : uEntry lc v = none := by
      simp only [uEntry, narrowLd?_g25 (Or.inr (Or.inr (Or.inr hop)))]
    rw [hue]
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g25_tstw (H := H) F hm hinv.core hinv.slots hR
      (knext_kStep fun _ => (hs_none hhn).noRegs) hj hj' hop hsz1 hfl hhn hao hok hvs htemp hs
    exact ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩, trivial⟩

/-- **G25, values.** `g24_value`'s statement over `checkG25`. -/
theorem g25_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG25 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s osp) (hu : UOK m (uAt lc blk i))
    (hpre : G14Pre lc s v)
    (hcall : CallOKAt osp H E g L lc s s' v m) (hcallz : CallOKZAt osp H E g L lc s s' v m)
    (hicall : ICallOKAt osp H E L ret lc s s' v m)
    (hwb : WbOKAt osp H E g L lc s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G10Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' osp ∧
      UOK m' (uAt lc blk (i + 1)) := by
  have hE0 := hE
  obtain ⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, hcf, hk, hlt, hnd, hblocks, -, hmovd⟩ :=
    checkG25_spec hc
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
  obtain ⟨htemp, hVK⟩ := vkind25_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  have hu1 : uAt c.cx.lc blk (i + 1) = uEntry c.cx.lc v := by simp [uAt, hi, hv]
  rw [kAt_succ hi hv, hu1]
  exact vk25_step hE0 F hhome hcf hv hVK hvs htemp hj hj' hreads hm hinv
    (fun x hop hx => by
      obtain ⟨r, c', hr, hc', hu0⟩ := movdOK_spec hmovd hbid hb hi hv hop hx
      exact ⟨r, c', hr, hc', hu0 ▸ hu⟩)
    hpre hcall hcallz hicall hwb hclo hgetg hs

/-- A nil check of G25's kinds is G7's. -/
theorem vk25_nil {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK25 lc g v kd)
    (hop : v.op = .ARM64LoweredNilCheck) : VK7 lc g v kd := by
  cases h with
  | g24 _ _ h => exact vk24_nil h hop
  | csel h => rw [hop] at h; cases h
  | csel0 h => rw [hop] at h; cases h
  | tst h => rw [hop] at h; cases h
  | tstw h => rw [hop] at h; cases h

/-- **G25, nil panics.** `g24_nilPanic`'s statement over `checkG25`. -/
theorem g25_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG25 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  obtain ⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, -, -⟩ :=
    checkG25_spec hc
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
  obtain ⟨-, hVK⟩ := vkind25_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases vk25_nil hVK hop with
  | g6 hne _ => exact absurd hop hne
  | nil _ hsz2 _ _ hao hma =>
    exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao hma hvs hs

/-- **G25, bounds panics.** `g24_boundsPanic`'s statement over `checkG25`, under `BoundsOK`. -/
theorem g25_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG25 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hbok : BoundsOK H g L ps.toList)
    (hs : stepLoc env lc s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' := by
  obtain ⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, hsyms, -, -, -, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, hpb, -⟩ :=
    checkG25_spec hc
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
  obtain ⟨-, hVK⟩ := vkind25_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases hVK with
  | csel h => rcases pbOp_cases hop with h' | h' | h' | h' <;> rw [h'] at h <;> cases h
  | csel0 h => rcases pbOp_cases hop with h' | h' | h' | h' <;> rw [h'] at h <;> cases h
  | tst h => rcases pbOp_cases hop with h' | h' | h' | h' <;> rw [h'] at h <;> cases h
  | tstw h => rcases pbOp_cases hop with h' | h' | h' | h' <;> rw [h'] at h <;> cases h
  | g24 _ _ hVK24 =>
    cases hVK24 with
    | sp hsp => rcases pbOp_cases hop with h | h | h | h <;> rw [h] at hsp <;> cases hsp
    | g23 _ hVK23 =>
      cases hVK23 with
      | cset hc =>
        rcases pbOp_cases hop with h | h | h | h <;> rw [h] at hc <;> simp [Cond.ofOp] at hc
      | g22 _ hVK22 =>
        cases hVK22 with
        | ldp hop' => rw [hop'] at hop; cases hop
        | stp hop' => rw [hop'] at hop; cases hop
        | g21 _ hVK21 =>
          cases hVK21 with
          | regSame hop' => rw [hop'] at hop; cases hop
          | regMov hop' => rw [hop'] at hop; cases hop
          | g20 _ hVK20 =>
            cases hVK20 with
            | nop hop' => rw [hop'] at hop; cases hop
            | g19 _ hVK19 =>
              exact vk19_boundsPanic F hsyms hpb hrow hb hi hv hVK19 hvs hj hreads hop hm hinv
                hbok hs

/-- **G25, terminators.** `g24_term`'s statement over `checkG25`. -/
theorem g25_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG25 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s) (hpre : G1TermPre lc s blk)
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' ∧
      e.b ∈ lc.ctx.f.blocks.toList := by
  obtain ⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome, -, hk, hlt, hnd, hblocks, -, -⟩ :=
    checkG25_spec hc
  exact termK_step hpcOf ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb
    hm hinv hpre ht

end GoFV.Proof.Gen
