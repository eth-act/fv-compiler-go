import GoFV.Gen.Check66b
import GoFV.Proof.Gen.Keep35

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G66b: extensions of a narrow reload (`docs/plans/slot-size.md` §2.3, §2.4)

* **The table across a narrow reload** (`reload_uokl`): a `LoadReg` homed in an X register at
  class `c ∈ {8, 16, 32}` has G35's entry (`reloadEntry35`), and the machine's reload of `n = c / 8`
  bytes, sign-extended exactly for a signed type (`loadByType`), is that extension
  (`extOK_load`). A reload with no entry (a boolean) keeps the other registers' entries.
* **An elided extension** (`elide66b`, `extElide66b`): G3's extension (`valRel_ext`: the value of
  `MOV{B,H,W}{,U}reg x` is related to the extension of `x`'s register) of a register that already
  holds that extension (the table's entry, `UOK`, so the extension is the register itself,
  `ext_of_extOK`). With the same register there is no code (`g66b_elideSame`: the machine does not
  move), with another `MOVD Rx, Rv` (`g66b_elideMov`). No run premise.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The upper bits -/

/-- A register that holds the sign or zero extension of its low `w` bits (`ExtOK`) is its own
extension `MOV{B,H,W}{,U}` of `w` bits. -/
theorem ext_of_extOK {X : BitVec 64} {w : Nat} {sg : Bool} (hw : w = 8 ∨ w = 16 ∨ w = 32)
    (h : ExtOK X w sg) :
    (if sg then ProgOp.sextTo64 (w / 8) X else ProgOp.maskN (w / 8) X) = X := by
  unfold ExtOK at h
  have hw8 : 8 * (w / 8) = w := by omega
  have hn8 : (w / 8 == 8) = false := by rcases hw with rfl | rfl | rfl <;> rfl
  cases sg
  · simp only [Bool.false_eq_true, ↓reduceIte] at h ⊢
    refine Eq.trans ?_ h.symm
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [ProgOp.maskN, hn8, Bool.false_eq_true, ↓reduceIte, BitVec.getLsbD_and,
      BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one, BitVec.getLsbD_setWidth, hw8]
    by_cases h1 : i < w <;> simp [h1, hi]
  · simp only [↓reduceIte] at h ⊢
    refine Eq.trans ?_ h.symm
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [ProgOp.sextTo64, hw8]
    rw [sext_bit _ ⟨by omega, by omega⟩ _ _ hi, BitVec.getLsbD_signExtend]
    simp only [BitVec.getLsbD_setWidth, BitVec.msb_eq_getLsbD_last]
    by_cases h1 : i < w
    · simp [h1, hi]
    · simp [h1, hi, show w - 1 < w by omega]

/-- An extension's widths (`extOp?`). -/
theorem extOp?_w {op : Op} {as : As} {w : Nat} {sg : Bool} (h : extOp? op = some (as, w, sg)) :
    w = 8 ∨ w = 16 ∨ w = 32 := by
  unfold extOp? at h
  split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h <;> omega

/-- The machine register of an argument register `r` (an X register `k`, or `ZR`) whose entry
`(r, w, sg)` holds (`UOK`) is the extension of its low `w` bits. -/
theorem extOK_arg {m : MState} {r w kn : Nat} {sg : Bool}
    (hu : UOK m (some (r, w, sg))) (hor : objOf? r = some (GoFV.Asm.ARM64.REG_R0 + kn)) :
    ExtOK (m.rX (BitVec.ofNat 5 kn)) w sg := by
  obtain ⟨kn', hkn', hkk, hkn0⟩ := objOf?_some hor
  have hk : kn = kn' := by omega
  subst hk
  rcases hkn0 with ⟨-, h31⟩ | ⟨hk31, hobj⟩
  · subst h31
    rw [rX_31]
    exact extOK_zero w sg
  · rw [rX_lt hk31]
    exact hu kn hk31 hobj

/-! ## The table across a narrow reload -/

/-- A narrow integer reload's step (`n` bytes `Y` into `X[kd]`, sign-extended exactly when its
type is signed, `typeSigned`): G35's table holds after it, with its entry (`reloadEntry35`) when
it has one. -/
theorem reload_uokl {lc : LocCtx} {v : Value} {m m' : MState} {L : List (Nat × Nat × Bool)}
    {c n kd : Nat} {rd : Int} {Y : BitVec (8 * n)}
    (hop : v.op = .LoadReg) (hro : resObj lc v = .ok (c, rd))
    (hrd : rd = GoFV.Asm.ARM64.REG_R0 + kd) (hn : 1 ≤ n) (hnc : 8 * n = c ∨ c = 1)
    (hx : m'.x = (m.wX (BitVec.ofNat 5 kd)
      (if typeSigned lc.ctx.tabs v.type then ProgOp.sextTo64 n (Y.setWidth 64)
       else Y.setWidth 64)).x)
    (hL : UOKL m L) : UOKL m' (uStep35 lc L v) := by
  obtain ⟨r0, hvh0, -, hor0, hcv⟩ := resObj_spec hro
  rw [hrd] at hor0
  cases he : ldEntry35 lc v with
  | none =>
    have hxw : XW lc v m m' := .inr ⟨r0, kd, _, hvh0, hor0, hx⟩
    exact uokl_xw35 hL hxw he
      (by simp [uEntry, narrowLd?, loadOp?, narrowLoad?, loadIdxOp?, hop])
      (by simp [hop]) (by simp [hop]) (by simp [hop]) (by simp [hop])
  | some e =>
    obtain ⟨r, c', sg⟩ := e
    rcases ldEntry35_spec he with ⟨_, _, hl, _⟩ | ⟨_, hre⟩
    · rw [hop] at hl; cases hl
    obtain ⟨-, hr, -, hc', hcc, rfl⟩ := reloadEntry35_spec hre
    rw [regHome?_eq.2 hvh0] at hr
    cases hr
    rw [hcv] at hc'
    cases hc'
    have hn' : 8 * n = c := by omega
    rw [uStep35_ld he]
    exact uokl_ld hL (uok_ldW hor0 hn (by omega) (by omega) hx) hor0 hx

/-! ## Elided extensions -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- The value of an elided extension (`valRel_ext`) is related to its argument's machine register,
which holds that extension (`UOK`, `ext_of_extOK`). -/
theorem elide_rel (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hR : KRead lc v K)
    {as : As} {w : Nat} {sg : Bool} {ca c : Nat} {rn : Int}
    (he : extOp? v.op = some (as, w, sg)) (hsz1 : v.args.size = 1)
    (hao : argObj lc v 0 = .ok (ca, rn)) (hcv : cls (lc.ty v.id) = some c) (hw : w ≤ ca ∨ ca = 1)
    (h8 : 8 ≤ c)
    (hu : ∀ x r, v.args[0]? = some x → regHome? lc x = some r → UOK m (some (r, w, sg)))
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ (kn : Nat) (y : Val), rn = GoFV.Asm.ARM64.REG_R0 + kn ∧ kn < 32 ∧
      s' = s.write lc v.id y ∧ ValRel E.ι y (m.rX (BitVec.ofNat 5 kn)) ∧ Fits c y := by
  have hl := F.lowered
  have hA := F.addr
  have hnp := extOp?_ne_phi he
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_ext hl htemp he hs
  rw [arr1 hsz1 ha0] at hargv
  obtain rfl := mapM_res_one hargv hx
  have hrel := valRel_ext (k := v.auxInt) (aux := v.aux) hA hxv hxf hcv (cls_ne_bool hcv h8) he hw
  rw [ext_of_extOK (extOp?_w he) (extOK_arg (hu a0 r0 ha0 (regHome?_eq.2 hah0)) hor0)] at hrel
  exact ⟨kn, _, rfl, hkn, rfl, hrel, fits_retypeL hcv _⟩

/-- An elided extension of a value in its own register (`extElide66b`, no code): the machine does
not move. -/
theorem g66b_elideSame (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    (hvs : j' = j) {as : As} {w : Nat} {sg : Bool} {ca c : Nat} {r : Int}
    (he : extOp? v.op = some (as, w, sg)) (hsz1 : v.args.size = 1)
    (hao : argObj lc v 0 = .ok (ca, r)) (hro : resObj lc v = .ok (c, r)) (hw : w ≤ ca ∨ ca = 1)
    (h8 : 8 ≤ c)
    (hu : ∀ x r, v.args[0]? = some x → regHome? lc x = some r → UOK m (some (r, w, sg)))
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      m'.x = m.x := by
  have hnp := extOp?_ne_phi he
  obtain ⟨r2, hvh, hd, hor2, hcv⟩ := resObj_spec hro
  obtain ⟨kn, y, rfl, hkn, rfl, hrel, hfy⟩ :=
    elide_rel F hm hinv hR he hsz1 hao hcv hw h8 hu htemp hs
  rw [write_reg hvh hcv]
  obtain ⟨hlm, hinv'⟩ := finish_reg hm hinv hd hkn hor2 hrel hfy (b' := b) (i' := i + 1)
  rw [wX_rX_self, hj', hvs, ← hj, ← hm.pc] at hlm
  exact ⟨m, .refl, hlm, hinv'.mono (knext_set hK hnp hvh hcv), hsi, rfl⟩

/-- An elided extension of a value in another register (`extElide66b`): `MOVD Rx, Rv`. -/
theorem g66b_elideMov (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {as : As} {w : Nat} {sg : Bool} {ca c : Nat} {rn rd : Int}
    (he : extOp? v.op = some (as, w, sg)) (hsz1 : v.args.size = 1)
    (hao : argObj lc v 0 = .ok (ca, rn)) (hro : resObj lc v = .ok (c, rd)) (hw : w ≤ ca ∨ ca = 1)
    (h8 : 8 ≤ c)
    (hu : ∀ x r, v.args[0]? = some x → regHome? lc x = some r → UOK m (some (r, w, sg)))
    (hvs : OneAt2 psA j (.ofShape { as := .MOVD, from_ := regA rn, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      XW lc v m m' := by
  have hnp := extOp?_ne_phi he
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨kn, y, rfl, hkn, rfl, hrel, hfy⟩ :=
    elide_rel F hm hinv hR he hsz1 hao hcv hw h8 hu htemp hs
  rw [write_reg hvh hcv]
  refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor hrel hfy (knext_set hK hnp hvh hcv)
    (fun k0 hk0 hok => ?_)).imp
    fun m' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, hsi, .inr ⟨r, kd, _, hvh, hor, h4⟩⟩
  obtain ⟨has, hf, -, ht, -⟩ := Shape.ok_eq hok
  rw [progStep_movReg hkn hkd (nextAddr_pcAt F.nodup hk0) has hf ht, wX_pc] <;> rfl

end Cases

end GoFV.Proof.Gen
