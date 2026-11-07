import GoFV.Proof.Low.Rules.Peep
import GoFV.Proof.Low.Rules.Invert
import GoFV.Proof.Low.ArmMonoRetype

/-!
# Lowering rule lemmas: bit lengths, conditional selects, `TST` conditions, booleans, division (`ARM64.rules:15-35`, `104-106`, `135-137`, `187`, `271`, `564-570`, `1186-1195`)

* `(BitLen64 x) => (SUB (MOVDconst [64]) (CLZ <typ.Int> x))` (`104`), `(BitLen32 x) => (SUB
  (MOVDconst [32]) (CLZW <typ.Int> x))` (`105`), `(BitLen(16|8) x) => (BitLen64
  (ZeroExt(16|8)to64 x))` (`106`): the bit length `w − clz x` of a `w`-bit integer is its
  unsigned value's (`0`, or `log2 + 1`; `bitLen_eq`), which zero extension keeps
  (`bitLen_setWidth`); `64 − CLZ` is that count in the register (`sub_clz_setWidth`).
* `(CSEL [cc] x (MOVDconst [0]) flag) => (CSEL0 [cc] x flag)` (`1188`), `(CSEL [cc] (MOVDconst
  [-1]) (MOVDconst [0]) flag) => (CSETM [cc] flag)` (`1186`), `(CSEL [cc] x (MVN a) flag) =>
  (CSINV [cc] x a flag)` (`1192`) and `(CSEL [cc] x (NEG a) flag) => (CSNEG [cc] x a flag)`
  (`1194`): `CSEL` reads its arms whole (`armReadW`), so a constant arm is the constant or
  `poison` (`retypeL_res_wide`), and an `MVN`/`NEG` arm the register `CSINV`/`CSNEG` computes. The
  auxint `cc` is bound as the op it names (`ccDV`) and rebuilt from that op's Go number, which names
  the same condition (`ofAux_goNum`); an auxint naming no condition decides nothing and the source
  is `poison`.
* their mirrored forms on `arm64Negate(cc)` (`1187`, `1189`, `1193`, `1195`), split by the
  condition op (`GoFV.Rules.Derive.ccSplit` over `negCondOps`): the negated condition holds
  exactly when the condition does not, the float conditions included (`eval_condNeg`).
* `(CSEL [cc] x (ADDconst [1] a) flag) => (CSINC [cc] x a flag)` (`1190`) and its mirror on
  `arm64Negate(cc)` (`1191`, split as above): `CSINC` adds 1 to `a` as `ADDconst` does, a pointer
  `a` included (`Arm64.csinc`, `addP`); the `ADDconst` arm is read whole, so a pointer's word is
  kept at a word shape or `poison` (`retypeL_word_wide`), a register's sum likewise
  (`refines_regVal_addP`).
* `((Equal|NotEqual|LessThan|LessEqual|GreaterThan|GreaterEqual) (CMPconst [0] z:(AND x y)))
  => (… (TST x y))` (`564`) and the `CMPWconst`/`ANDconst`/`TSTW`/`TSTWconst`/`TSTconst` forms
  (`566`, `568`, `570`): the flags of `r − 0` and of `TST` (`r &&& r'`) differ only in `C`
  (`subFlags_zero`, `logicFlags`), which these conditions do not read (`noC`); the compare reads its
  `AND` whole (64 bits, `retypeL_res_wide`) or its low word (`retypeL_res_w32`).
* `(Not x) => (XOR (MOVDconst [1]) x)` (`137`), `(EqB x y) => (XOR (MOVDconst [1]) (XOR <typ.Bool> x
  y))` (`135`), `(NeqB ...) => (XOR ...)` (`136`): the booleans' registers are 0 or 1.
* `(Slicemask <t> x) => (SRAconst (NEG <t> x) [63])` (`187`): for `x ≥ 0` (else the source is
  `poison`) `−x` is negative exactly when `x ≠ 0` (`sra63_neg`); the argument is a 64-bit integer
  (`hat`), so a narrower result shape reads no integer and the source is `poison`.
* `(Less(8U|16U|32U|64U) zero:(MOVDconst [0]) x) => (Neq(8|16|32|64) zero x)` (`271`): `0 <u x`
  iff `x ≠ 0` (`zero_ult`), on the same `zero` value.
* `(Hmul64 ...) => (MULH ...)`, `(Hmul64u ...) => (UMULH ...)` (`15`, `16`); `(Div64 [false] x y)
  => (DIV x y)` (`22`), `(Div64u ...) => (UDIV ...)` (`28`), `(Mod64 x y) => (MOD x y)` (`33`),
  `(Mod64u ...) => (UMOD ...)` (`35`): Phase 1's quotients and remainders are `poison` on a zero
  divisor (and on a broken "not −1" promise), else the machine's (`MIN / −1 = MIN` both); `REM`/
  `UREM` as `x − (x / y)·y` are the truncated remainders (`srem_eq_sub`, `urem_eq`).

Found false (not proven; `docs/proofs/rules.md` "Findings"):

* `(AndB ...) => (AND ...)` (`133`) and `(OrB ...) => (OR ...)` (`134`): Phase 1's `AndB`/`OrB`
  are parallel (`Cmp.andB`: `false && poison` is `false`), `AND`/`OR` read both registers:
  `AndB false poison` is `false`, `AND` of it `poison` (`OrB true poison`: `true`, `poison`).
-/

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules GoFV.Proof.Low GoFV.Opt.LowerTerm
open GoFV.Rules.Generated.ARM64 GoFV.Rules.Derive

/-! ## Bit lengths -/

/-- The bit length `w − clz x` of a `w`-bit integer: 0 for 0, else `log2 + 1` of its value. -/
private theorem bitLen_eq {w : Nat} (hw : 0 < w) (x : BitVec w) :
    w - x.clz.toNat = if x.toNat = 0 then 0 else x.toNat.log2 + 1 := by
  have hle : x.clz.toNat ≤ w := by
    have h := BitVec.clz_le (x := x)
    rw [BitVec.le_def] at h
    have : (BitVec.ofNat w w).toNat = w := by
      simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Nat.lt_two_pow_self)
    simpa [this] using h
  by_cases h0 : x.toNat = 0
  · have hx : x = 0#w := BitVec.eq_of_toNat_eq (by simp [h0])
    have hc := BitVec.clz_eq_iff_eq_zero.mpr hx
    have : x.clz.toNat = w := by
      rw [hc]; simp only [BitVec.natCast_eq_ofNat, BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (Nat.lt_two_pow_self)
    simp [h0, this]
  · have hx : x ≠ 0#w := fun h => h0 (by simp [h])
    have h1 := BitVec.toNat_lt_two_pow_sub_clz (x := x)
    have h2 := BitVec.two_pow_sub_clz_le_toNat_of_ne_zero hw hx
    have hlt : x.clz.toNat < w := by
      rcases Nat.lt_or_ge x.clz.toNat w with h | h
      · exact h
      · exfalso
        have : w - x.clz.toNat = 0 := by omega
        rw [this] at h1; simp at h1; exact h0 (by omega)
    have hl : x.toNat.log2 = w - 1 - x.clz.toNat := by
      rw [Nat.log2_eq_iff h0]
      refine ⟨h2, ?_⟩
      rwa [show w - 1 - x.clz.toNat + 1 = w - x.clz.toNat by omega]
    simp only [h0, ite_false, hl]; omega

/-- Zero extension keeps the bit length. -/
private theorem bitLen_setWidth {n m : Nat} (hn : 0 < n) (h : n ≤ m) (x : BitVec n) :
    m - (x.setWidth m).clz.toNat = n - x.clz.toNat := by
  rw [bitLen_eq (by omega), bitLen_eq hn, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) h))]

private theorem asInt_eq_some {v : Val} {w : Width} {x : BitVec w.bits}
    (h : v.asInt w = some x) : v = .int w x := by
  cases v with
  | int w' y =>
    simp only [Val.asInt] at h
    split at h
    · rename_i hw; subst hw; cases h; rfl
    · cases h
  | _ => simp [Val.asInt] at h

private theorem clz_toNat_le {n : Nat} (x : BitVec n) : x.clz.toNat ≤ n := by
  have h := BitVec.clz_le (x := x)
  rw [BitVec.le_def] at h
  have : (BitVec.ofNat n n).toNat = n := by
    simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Nat.lt_two_pow_self)
  simpa [this] using h

/-- `n − c` in the register (`SUB (MOVDconst [n]) …`), read at `k ≤ 64` bits. -/
private theorem sub_clz_setWidth {k n : Nat} (hk : k ≤ 64) (hn : n ≤ 64) (c : Nat) (hc : c ≤ n) :
    (BitVec.ofInt 64 (n : Int) - BitVec.ofNat 64 c).setWidth k = BitVec.ofNat k (n - c) := by
  rw [BitVec.ofInt_natCast, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) hc,
    BitVec.setWidth_ofNat_of_le hk]

/-- A count `n − c` as `SUB (MOVDconst [n]) a` with `a` the register holding `c`. -/
private theorem refines_bitLen_sub (w : Width) (n : Nat) (hn : n ≤ 64) (c : Nat) (hc : c ≤ n)
    (a : Val) (ha : a = .int .w64 (BitVec.ofNat 64 c)) :
    Refines ((Val.int w (BitVec.ofNat w.bits (n - c))).retypeL (.int w))
      ((Arm64.sub (.int w) [(Arm64.res (.int .w64) (BitVec.ofInt 64 (n : Int))).retypeL (.int .w64),
        a]).retypeL (.int w)) := by
  subst ha
  have : Arm64.sub (.int w)
      [(Arm64.res (.int .w64) (BitVec.ofInt 64 (n : Int))).retypeL (.int .w64),
        .int .w64 (BitVec.ofNat 64 c)] =
      Arm64.res (.int w) (BitVec.ofInt 64 (n : Int) - BitVec.ofNat 64 c) := rfl
  rw [this, retypeL_res_int, sub_clz_setWidth (by cases w <;> decide) hn _ hc, retypeL_int_self]
  exact Refines.refl _

/-- `CLZW` of a 32-bit integer: its leading zeros in the register. -/
private theorem clzw_val (x : BitVec 32) :
    (Arm64.op1w (.int .w64) Arm64.clz [.int .w32 x]).retypeL (.int .w64) =
      .int .w64 (BitVec.ofNat 64 x.clz.toNat) := by
  have hl : x.clz.toNat < 2 ^ 32 := Nat.lt_of_le_of_lt (clz_toNat_le x) (by decide)
  simp only [Arm64.op1w, Arm64.reg32, Arm64.reg, Arm64.res32, Arm64.res, Arm64.clz,
    Option.map_some, Width.bits, BitVec.setWidth_setWidth_of_le _ (show 32 ≤ 64 by decide),
    BitVec.setWidth_eq]
  rw [BitVec.setWidth_ofNat_of_le_of_lt (by decide) hl]
  rfl

/-- `ARM64.rules:104`: `(BitLen64 x) => (SUB (MOVDconst [64]) (CLZ <typ.Int> x))` -/
theorem r_ARM64_104_sound : ArmRule.Checked r_ARM64_104 := by
  left; arm_unfold; arm_shape; all_goals arm_norm
  all_goals
    rcases h : (e.leaf [0]).asInt .w64 with _ | x
    · simp only [Option.elim, retypeL_poison]; exact .poison _
    · rw [asInt_eq_some h]
      exact refines_bitLen_sub _ 64 (by decide) _ (clz_toNat_le x) _ rfl

/-- `ARM64.rules:105`: `(BitLen32 x) => (SUB (MOVDconst [32]) (CLZW <typ.Int> x))` -/
theorem r_ARM64_105_sound : ArmRule.Checked r_ARM64_105 := by
  left; arm_unfold; arm_shape; all_goals arm_norm
  all_goals
    rcases h : (e.leaf [0]).asInt .w32 with _ | x
    · simp only [Option.elim, retypeL_poison]; exact .poison _
    · rw [asInt_eq_some h]
      exact refines_bitLen_sub _ 32 (by decide) _ (clz_toNat_le x) _ (clzw_val x)

/-- `ARM64.rules:106`: `(BitLen16 x) => (BitLen64 (ZeroExt16to64 x))` -/
theorem r_ARM64_106_sound : ArmRule.Checked r_ARM64_106 := by
  left; arm_unfold; arm_shape; all_goals arm_norm
  all_goals
    rcases h : (e.leaf [0]).asInt .w16 with _ | x
    · simp only [Option.elim, retypeL_poison]; exact .poison _
    · simp only [Option.elim, retypeL_int_self, Val.asInt_int]
      rw [bitLen_setWidth (by decide) (by decide)]; exact Refines.refl _

/-- `ARM64.rules:106`: `(BitLen8 x) => (BitLen64 (ZeroExt8to64 x))` -/
theorem r_ARM64_106_2_sound : ArmRule.Checked r_ARM64_106_2 := by
  left; arm_unfold; arm_shape; all_goals arm_norm
  all_goals
    rcases h : (e.leaf [0]).asInt .w8 with _ | x
    · simp only [Option.elim, retypeL_poison]; exact .poison _
    · simp only [Option.elim, retypeL_int_self, Val.asInt_int]
      rw [bitLen_setWidth (by decide) (by decide)]; exact Refines.refl _

/-! ## Condition auxints -/

set_option maxRecDepth 100000 in
/-- A condition op's Go number names it back (`Op.ofGoNum?`): the condition of its auxint. -/
private theorem ofAux_goNum (o : Op) (h : (Cond.ofOp o).isSome = true) :
    Cond.ofAux (Int64.ofNat o.goNum) = Cond.ofOp o := by
  cases o <;> first | exact absurd h Bool.false_ne_true | decide

/-- An auxint bound as the op `o` (`ccDV`) and rebuilt from it decides as itself. -/
private theorem condOn_goNum {k : Int64} {o : Op} (hk : Cond.ofAux k = Cond.ofOp o) (F : Val) :
    ∀ b, Arm64.condOn k F = some b → Arm64.condOn (Int64.ofNat o.goNum) F = some b := by
  intro b h
  simp only [Arm64.condOn] at h ⊢
  cases hc : Cond.ofOp o with
  | none => rw [hk, hc] at h; simp at h
  | some c =>
    rw [ofAux_goNum o (by simp [hc]), hc]
    rw [hk, hc] at h; exact h

/-- An auxint naming no condition decides nothing. -/
private theorem condOn_none {k : Int64} (hk : Cond.ofAux k = none) (F : Val) (k' : Int64)
    (f : Bool → Bool) : ∀ b, Arm64.condOn k F = some b → Arm64.condOn k' F = some (f b) := by
  intro b h; simp [Arm64.condOn, hk] at h

/-- The negated condition code. -/
private def condNeg : Cond → Cond
  | .eq => .ne | .ne => .eq | .hs => .lo | .lo => .hs | .mi => .pl | .pl => .mi
  | .vs => .vc | .vc => .vs | .hi => .ls | .ls => .hi | .ge => .lt | .lt => .ge
  | .gt => .le | .le => .gt | .al => .nv | .nv => .al

/-- A negated condition holds exactly when the condition does not (`al`/`nv` aside). -/
private theorem eval_condNeg (c : Cond) (hc : c ≠ .al ∧ c ≠ .nv) (n z cf v : Option Bool) :
    (condNeg c).eval n z cf v = (c.eval n z cf v).map (!·) := by
  cases c <;> simp only [ne_eq, not_true_eq_false, and_false, false_and, reduceCtorEq,
    not_false_eq_true] at hc <;>
    rcases n with _ | _ | _ <;> rcases z with _ | _ | _ <;> rcases cf with _ | _ | _ <;>
    rcases v with _ | _ | _ <;> rfl

private theorem condOn_neg {k k' : Int64} {c : Cond} (hk : Cond.ofAux k = some c)
    (hk' : Cond.ofAux k' = some (condNeg c)) (hc : c ≠ .al ∧ c ≠ .nv) (F : Val) :
    ∀ b, Arm64.condOn k F = some b → Arm64.condOn k' F = some (!b) := by
  intro b h
  simp only [Arm64.condOn, hk, hk', Option.bind_some] at h ⊢
  unfold Cond.onVal at h ⊢
  split
  · simp only at h
    rw [eval_condNeg c hc, h]; rfl
  · rename_i hne
    split at h
    · rename_i n z cf v g; exact absurd rfl (hne n z cf v g)
    · cases h

/-! ## `CSEL` arms -/

/-- `CSEL` reads its arms at the result's low bits (`armReadW`). -/
private theorem armReadW_csel (T : Ty) {i : Nat} (hi : i < 2) :
    armReadW .ARM64CSEL T i = lowW T := by
  cases T <;> simp [armReadW, lowW, hi]

private theorem armReadW_csel0 (T : Ty) : armReadW .ARM64CSEL T 0 = lowW T :=
  armReadW_csel T (by decide)

private theorem armReadW_csel1 (T : Ty) : armReadW .ARM64CSEL T 1 = lowW T :=
  armReadW_csel T (by decide)

/-- A constant register read at its node's shape is not a pointer. -/
private theorem retypeL_res_noPtr (T : Ty) (k : BitVec 64) (q : Ptr) :
    (Arm64.res T k).retypeL T ≠ .ptr q := by
  cases T with
  | int w => cases w <;> simp [Arm64.res, Val.retypeL, Val.widen, Val.retype, Width.bits]
  | _ => simp [Arm64.res, Val.retypeL, Val.widen, Val.retype]

/-- A 64-bit constant register read at a shape keeping the result's low bits (`lowW`), moved
(`regVal`): the constant at the result's shape, or `poison`. -/
private theorem refines_regVal_res {T T1 : Ty} (h : lowW T ≤ argWidth T1) (k : BitVec 64) :
    Refines ((Arm64.regVal T ((Arm64.res T1 k).retypeL T1)).retypeL T)
      ((Arm64.res T k).retypeL T) := by
  obtain ⟨h1, h2⟩ := lowW_pos T
  rcases retypeL_res_reg h1 h2 h k with h' | ⟨y, hy, hyk⟩
  · rw [h']
    have : Arm64.regVal T .poison = .poison := rfl
    rw [this, retypeL_poison]; exact .poison _
  · have hrv : Arm64.regVal T ((Arm64.res T1 k).retypeL T1) = Arm64.res T y := by
      generalize hV : (Arm64.res T1 k).retypeL T1 = V at hy
      cases V with
      | ptr q => exact absurd hV (retypeL_res_noPtr T1 k q)
      | _ => simp only [Arm64.regVal, hy]
    rw [hrv, retypeL_res_low T hyk]; exact Refines.refl _

/-- A unary op's register read at a shape keeping the result's low bits, moved (`regVal`): the
register the conditional op computes from the operand. -/
private theorem refines_regVal_op1 {T T1 : Ty} (h : lowW T ≤ argWidth T1)
    (g : BitVec 64 → BitVec 64) (a : Val) :
    Refines ((Arm64.regVal T ((Arm64.op1 T1 g [a]).retypeL T1)).retypeL T)
      ((match Arm64.reg a with
        | some r => Arm64.res T (g r)
        | none => .poison).retypeL T) := by
  cases hr : Arm64.reg a with
  | none =>
    have hp : Arm64.op1 T1 g [a] = .poison := by simp only [Arm64.op1, hr]
    have hq : Arm64.regVal T .poison = .poison := rfl
    simp only [hp, retypeL_poison, hq]; exact .poison _
  | some r => simp only [Arm64.op1, hr]; exact refines_regVal_res h (g r)

private theorem refines_csel_csel0 {T T1 : Ty} (h1 : lowW T ≤ argWidth T1) {k k' : Int64}
    {F : Val} (hk : ∀ b, Arm64.condOn k F = some b → Arm64.condOn k' F = some (id b)) (X : Val) :
    Refines ((Arm64.csel T k none [X, (Arm64.res T1 0).retypeL T1, F]).retypeL T)
      ((Arm64.csel0 T k' [X, F]).retypeL T) := by
  simp only [Arm64.csel, Arm64.csel0]
  cases hA : Arm64.condOn k F with
  | none => simp only [retypeL_poison]; exact .poison _
  | some b =>
    rw [hk b hA]
    cases b
    · exact refines_regVal_res h1 0
    · exact Refines.refl _

private theorem refines_csel_csel0_neg {T T0 : Ty} (h0 : lowW T ≤ argWidth T0) {k k' : Int64}
    {F : Val} (hk : ∀ b, Arm64.condOn k F = some b → Arm64.condOn k' F = some (!b)) (Y : Val) :
    Refines ((Arm64.csel T k none [(Arm64.res T0 0).retypeL T0, Y, F]).retypeL T)
      ((Arm64.csel0 T k' [Y, F]).retypeL T) := by
  simp only [Arm64.csel, Arm64.csel0]
  cases hA : Arm64.condOn k F with
  | none => simp only [retypeL_poison]; exact .poison _
  | some b =>
    rw [hk b hA]
    cases b
    · exact Refines.refl _
    · exact refines_regVal_res h0 0

private theorem refines_csel_csetm {T T0 T1 : Ty} (h0 : lowW T ≤ argWidth T0)
    (h1 : lowW T ≤ argWidth T1) {k k' : Int64} {F : Val}
    (hk : ∀ b, Arm64.condOn k F = some b → Arm64.condOn k' F = some (id b)) :
    Refines ((Arm64.csel T k none [(Arm64.res T0 (-1)).retypeL T0, (Arm64.res T1 0).retypeL T1,
        F]).retypeL T)
      ((Arm64.csetm T k' [F]).retypeL T) := by
  simp only [Arm64.csel, Arm64.csetm]
  cases hA : Arm64.condOn k F with
  | none => simp only [retypeL_poison]; exact .poison _
  | some b =>
    rw [hk b hA]
    cases b
    · exact refines_regVal_res h1 0
    · exact refines_regVal_res h0 (-1)

private theorem refines_csel_csetm_neg {T T0 T1 : Ty} (h0 : lowW T ≤ argWidth T0)
    (h1 : lowW T ≤ argWidth T1) {k k' : Int64} {F : Val}
    (hk : ∀ b, Arm64.condOn k F = some b → Arm64.condOn k' F = some (!b)) :
    Refines ((Arm64.csel T k none [(Arm64.res T0 0).retypeL T0, (Arm64.res T1 (-1)).retypeL T1,
        F]).retypeL T)
      ((Arm64.csetm T k' [F]).retypeL T) := by
  simp only [Arm64.csel, Arm64.csetm]
  cases hA : Arm64.condOn k F with
  | none => simp only [retypeL_poison]; exact .poison _
  | some b =>
    rw [hk b hA]
    cases b
    · exact refines_regVal_res h1 (-1)
    · exact refines_regVal_res h0 0

private theorem refines_csel_op1 {T T1 : Ty} (h1 : lowW T ≤ argWidth T1) {k k' : Int64}
    {F : Val} (hk : ∀ b, Arm64.condOn k F = some b → Arm64.condOn k' F = some (id b))
    (g : BitVec 64 → BitVec 64) (X a : Val) :
    Refines ((Arm64.csel T k none [X, (Arm64.op1 T1 g [a]).retypeL T1, F]).retypeL T)
      ((Arm64.csel T k' (some g) [X, a, F]).retypeL T) := by
  simp only [Arm64.csel]
  cases hA : Arm64.condOn k F with
  | none => simp only [retypeL_poison]; exact .poison _
  | some b =>
    rw [hk b hA]
    cases b
    · exact refines_regVal_op1 h1 g a
    · exact Refines.refl _

private theorem refines_csel_op1_neg {T T0 : Ty} (h0 : lowW T ≤ argWidth T0) {k k' : Int64}
    {F : Val} (hk : ∀ b, Arm64.condOn k F = some b → Arm64.condOn k' F = some (!b))
    (g : BitVec 64 → BitVec 64) (X a : Val) :
    Refines ((Arm64.csel T k none [(Arm64.op1 T0 g [a]).retypeL T0, X, F]).retypeL T)
      ((Arm64.csel T k' (some g) [X, a, F]).retypeL T) := by
  simp only [Arm64.csel]
  cases hA : Arm64.condOn k F with
  | none => simp only [retypeL_poison]; exact .poison _
  | some b =>
    rw [hk b hA]
    cases b
    · exact Refines.refl _
    · exact refines_regVal_op1 h0 g a

private theorem auxInt_zero {k : Int64} (h : DV.int k.toInt = DV.int 0) :
    BitVec.ofInt 64 k.toInt = 0 := by
  injection h with h; rw [h]; rfl

private theorem auxInt_m1 {k : Int64} (h : DV.int k.toInt = DV.int (-1)) :
    BitVec.ofInt 64 k.toInt = -1 := by
  injection h with h; rw [h]; rfl

/-- `ARM64.rules:1186`: `(CSEL [cc] (MOVDconst [-1]) (MOVDconst [0]) flag) => (CSETM [cc] flag)` -/
theorem r_ARM64_1186_sound : ArmRule.Checked r_ARM64_1186 := by
  left; arm_unfold; arm_norm
  simp only [armReadW_csel0, armReadW_csel1] at harg
  rw [auxInt_m1 hc.1, auxInt_zero hc.2]
  rcases ccDV_cases (e.auxInt []) with ⟨o, ho, hk⟩ | ⟨ho, hk⟩ <;> simp only [ho]
  · exact refines_csel_csetm harg.1 harg.2.1 (condOn_goNum hk _)
  · exact refines_csel_csetm harg.1 harg.2.1 (condOn_none hk _ _ _)

/-- `ARM64.rules:1188`: `(CSEL [cc] x (MOVDconst [0]) flag) => (CSEL0 [cc] x flag)` -/
theorem r_ARM64_1188_sound : ArmRule.Checked r_ARM64_1188 := by
  left; arm_unfold; arm_norm
  simp only [armReadW_csel0, armReadW_csel1] at harg
  rw [auxInt_zero hc]
  rcases ccDV_cases (e.auxInt []) with ⟨o, ho, hk⟩ | ⟨ho, hk⟩ <;> simp only [ho]
  · exact refines_csel_csel0 harg.2.1 (condOn_goNum hk _) _
  · exact refines_csel_csel0 harg.2.1 (condOn_none hk _ _ _) _

/-- `ARM64.rules:1192`: `(CSEL [cc] x (MVN a) flag) => (CSINV [cc] x a flag)` -/
theorem r_ARM64_1192_sound : ArmRule.Checked r_ARM64_1192 := by
  left; arm_unfold; arm_norm
  simp only [armReadW_csel0, armReadW_csel1] at harg
  rcases ccDV_cases (e.auxInt []) with ⟨o, ho, hk⟩ | ⟨ho, hk⟩ <;> simp only [ho]
  · exact refines_csel_op1 harg.2.1.1 (condOn_goNum hk _) _ _ _
  · exact refines_csel_op1 harg.2.1.1 (condOn_none hk _ _ _) _ _ _

/-- `ARM64.rules:1194`: `(CSEL [cc] x (NEG a) flag) => (CSNEG [cc] x a flag)` -/
theorem r_ARM64_1194_sound : ArmRule.Checked r_ARM64_1194 := by
  left; arm_unfold; arm_norm
  simp only [armReadW_csel0, armReadW_csel1] at harg
  rcases ccDV_cases (e.auxInt []) with ⟨o, ho, hk⟩ | ⟨ho, hk⟩ <;> simp only [ho]
  · exact refines_csel_op1 harg.2.1.1 (condOn_goNum hk _) _ _ _
  · exact refines_csel_op1 harg.2.1.1 (condOn_none hk _ _ _) _ _ _

/-! ## Negated conditions, split by the condition (`Derive.ccSplit`) -/

/-- `arm64Negate` on the condition ops (`Derive.negCondOps`); other ops unchanged. -/
private def negOp (o : Op) : Op :=
  match Arm64.arm64Negate o with
  | .ok o' => o'
  | .error _ => o

/-- `ccSplit r_ARM64_1187` on the condition op `cc`. -/
private def r1187 (cc : Op) : Rule where
  loc := ⟨"ARM64", 1187⟩
  op := .ARM64CSEL
  vars := [⟨"cc", .auxInt, (.named "Op")⟩, ⟨"flag", .value, (.named "*Value")⟩]
  pat := (.op .ARM64CSEL none .any (.bind 0) .any .fixed [(.op .ARM64MOVDconst none .any (.eq (.lit .int64 (.int 0))) .any .fixed [] false), (.op .ARM64MOVDconst none .any (.eq (.lit .int64 (.int (-1)))) .any .fixed [] false), (.bind 1)] false)
  cond := some (ccCond 0 cc)
  block := none
  result := .build
      [{ op := .ARM64CSETM, ty := none, auxInt := some (.op (negOp cc)), aux := none, args := [.var 1] }]
  pos := []

private theorem ccSplit_1187 : ccSplit r_ARM64_1187 = negCondOps.map r1187 := by rfl

set_option maxRecDepth 100000 in
/-- `ARM64.rules:1187`: `(CSEL [cc] (MOVDconst [0]) (MOVDconst [-1]) flag) => (CSETM [arm64Negate(cc)] flag)`, split by the condition (`ccSplit`) -/
theorem r_ARM64_1187_cc_sound : ForallL ArmRule.Checked (ccSplit r_ARM64_1187) := by
  rw [ccSplit_1187]
  simp only [negCondOps, intCondOps, List.cons_append, List.nil_append, List.map_cons,
    List.map_nil, ForallL]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  all_goals
    left; arm_unfold; arm_norm
    simp only [armReadW_csel0, armReadW_csel1] at harg
    simp only [ccCond, rule_unfold_ds, sigmaL, Pat.bindsL, Pat.bindssL, auxIntDVL] at hcond
    rw [auxInt_zero hc.1, auxInt_m1 hc.2]
    rcases ccDV_cases (e.auxInt []) with ⟨o, ho, hk⟩ | ⟨ho, hk⟩
    · rw [ho] at hcond
      simp [binE, binDV] at hcond
      subst hcond
      exact refines_csel_csetm_neg harg.1 harg.2.1
        (condOn_neg (hk.trans rfl) (by decide) (by decide) _)
    · exact refines_csel_csetm_neg harg.1 harg.2.1 (condOn_none hk _ _ _)

/-- `ccSplit r_ARM64_1189` on the condition op `cc`. -/
private def r1189 (cc : Op) : Rule where
  loc := ⟨"ARM64", 1189⟩
  op := .ARM64CSEL
  vars := [⟨"cc", .auxInt, (.named "Op")⟩, ⟨"y", .value, (.named "*Value")⟩, ⟨"flag", .value, (.named "*Value")⟩]
  pat := (.op .ARM64CSEL none .any (.bind 0) .any .fixed [(.op .ARM64MOVDconst none .any (.eq (.lit .int64 (.int 0))) .any .fixed [] false), (.bind 1), (.bind 2)] false)
  cond := some (ccCond 0 cc)
  block := none
  result := .build
      [{ op := .ARM64CSEL0, ty := none, auxInt := some (.op (negOp cc)), aux := none, args := [.var 1, .var 2] }]
  pos := []

private theorem ccSplit_1189 : ccSplit r_ARM64_1189 = negCondOps.map r1189 := by rfl

set_option maxRecDepth 100000 in
/-- `ARM64.rules:1189`: `(CSEL [cc] (MOVDconst [0]) y flag) => (CSEL0 [arm64Negate(cc)] y flag)`, split by the condition (`ccSplit`) -/
theorem r_ARM64_1189_cc_sound : ForallL ArmRule.Checked (ccSplit r_ARM64_1189) := by
  rw [ccSplit_1189]
  simp only [negCondOps, intCondOps, List.cons_append, List.nil_append, List.map_cons,
    List.map_nil, ForallL]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  all_goals
    left; arm_unfold; arm_norm
    simp only [armReadW_csel0, armReadW_csel1] at harg
    simp only [ccCond, rule_unfold_ds, sigmaL, Pat.bindsL, Pat.bindssL, auxIntDVL] at hcond
    rw [auxInt_zero hc]
    rcases ccDV_cases (e.auxInt []) with ⟨o, ho, hk⟩ | ⟨ho, hk⟩
    · rw [ho] at hcond
      simp [binE, binDV] at hcond
      subst hcond
      exact refines_csel_csel0_neg harg.1
        (condOn_neg (hk.trans rfl) (by decide) (by decide) _) _
    · exact refines_csel_csel0_neg harg.1 (condOn_none hk _ _ _) _

/-- `ccSplit r_ARM64_1193` on the condition op `cc`. -/
private def r1193 (cc : Op) : Rule where
  loc := ⟨"ARM64", 1193⟩
  op := .ARM64CSEL
  vars := [⟨"cc", .auxInt, (.named "Op")⟩, ⟨"a", .value, (.named "*Value")⟩, ⟨"x", .value, (.named "*Value")⟩, ⟨"flag", .value, (.named "*Value")⟩]
  pat := (.op .ARM64CSEL none .any (.bind 0) .any .fixed [(.op .ARM64MVN none .any .any .any .fixed [(.bind 1)] false), (.bind 2), (.bind 3)] false)
  cond := some (ccCond 0 cc)
  block := none
  result := .build
      [{ op := .ARM64CSINV, ty := none, auxInt := some (.op (negOp cc)), aux := none, args := [.var 2, .var 1, .var 3] }]
  pos := []

private theorem ccSplit_1193 : ccSplit r_ARM64_1193 = negCondOps.map r1193 := by rfl

set_option maxRecDepth 100000 in
/-- `ARM64.rules:1193`: `(CSEL [cc] (MVN a) x flag) => (CSINV [arm64Negate(cc)] x a flag)`, split by the condition (`ccSplit`) -/
theorem r_ARM64_1193_cc_sound : ForallL ArmRule.Checked (ccSplit r_ARM64_1193) := by
  rw [ccSplit_1193]
  simp only [negCondOps, intCondOps, List.cons_append, List.nil_append, List.map_cons,
    List.map_nil, ForallL]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  all_goals
    left; arm_unfold; arm_norm
    simp only [armReadW_csel0, armReadW_csel1] at harg
    simp only [ccCond, rule_unfold_ds, sigmaL, Pat.bindsL, Pat.bindssL, auxIntDVL] at hcond
    rcases ccDV_cases (e.auxInt []) with ⟨o, ho, hk⟩ | ⟨ho, hk⟩
    · rw [ho] at hcond
      simp [binE, binDV] at hcond
      subst hcond
      exact refines_csel_op1_neg harg.1.1
        (condOn_neg (hk.trans rfl) (by decide) (by decide) _) _ _ _
    · exact refines_csel_op1_neg harg.1.1 (condOn_none hk _ _ _) _ _ _

/-- `ccSplit r_ARM64_1195` on the condition op `cc`. -/
private def r1195 (cc : Op) : Rule where
  loc := ⟨"ARM64", 1195⟩
  op := .ARM64CSEL
  vars := [⟨"cc", .auxInt, (.named "Op")⟩, ⟨"a", .value, (.named "*Value")⟩, ⟨"x", .value, (.named "*Value")⟩, ⟨"flag", .value, (.named "*Value")⟩]
  pat := (.op .ARM64CSEL none .any (.bind 0) .any .fixed [(.op .ARM64NEG none .any .any .any .fixed [(.bind 1)] false), (.bind 2), (.bind 3)] false)
  cond := some (ccCond 0 cc)
  block := none
  result := .build
      [{ op := .ARM64CSNEG, ty := none, auxInt := some (.op (negOp cc)), aux := none, args := [.var 2, .var 1, .var 3] }]
  pos := []

private theorem ccSplit_1195 : ccSplit r_ARM64_1195 = negCondOps.map r1195 := by rfl

set_option maxRecDepth 100000 in
/-- `ARM64.rules:1195`: `(CSEL [cc] (NEG a) x flag) => (CSNEG [arm64Negate(cc)] x a flag)`, split by the condition (`ccSplit`) -/
theorem r_ARM64_1195_cc_sound : ForallL ArmRule.Checked (ccSplit r_ARM64_1195) := by
  rw [ccSplit_1195]
  simp only [negCondOps, intCondOps, List.cons_append, List.nil_append, List.map_cons,
    List.map_nil, ForallL]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  all_goals
    left; arm_unfold; arm_norm
    simp only [armReadW_csel0, armReadW_csel1] at harg
    simp only [ccCond, rule_unfold_ds, sigmaL, Pat.bindsL, Pat.bindssL, auxIntDVL] at hcond
    rcases ccDV_cases (e.auxInt []) with ⟨o, ho, hk⟩ | ⟨ho, hk⟩
    · rw [ho] at hcond
      simp [binE, binDV] at hcond
      subst hcond
      exact refines_csel_op1_neg harg.1.1
        (condOn_neg (hk.trans rfl) (by decide) (by decide) _) _ _ _
    · exact refines_csel_op1_neg harg.1.1 (condOn_none hk _ _ _) _ _ _

/-! ## `CSINC` of an incremented operand (`1190`, `1191`) -/

/-- A register result moved unchanged (`regVal`) is itself. -/
private theorem regVal_res (T : Ty) (r : BitVec 64) :
    Arm64.regVal T (Arm64.res T r) = Arm64.res T r := by
  cases T with
  | bool =>
    simp only [Arm64.res, Arm64.regVal, Arm64.reg]
    cases r.getLsbD 0 <;> rfl
  | _ => simp [Arm64.res, Arm64.regVal, Arm64.reg]

/-- A pointer's word at a shape with a whole register: kept (a word shape) or `poison` (an
aggregate). -/
private theorem retypeL_word_wide (p : Ptr) {T : Ty} (hT : 64 ≤ argWidth T) :
    p.word.retypeL T = p.word ∨ p.word.retypeL T = .poison := by
  cases T with
  | int w =>
    cases w <;> simp [argWidth, Width.bits] at hT
    left; unfold Val.retypeL
    rw [Mono.widen_of_hasTy _ _ (Ptr.word_hasTy_i64 p), Ptr.word_retype_i64]
  | ptr e =>
    left; unfold Val.retypeL
    rw [Mono.widen_of_hasTy _ _ (Ptr.word_hasTy_ptr p e), Ptr.word_retype_ptr]
  | agg fs n =>
    right
    rcases Ptr.word_cases p with ⟨-, h⟩ | ⟨-, a, -, h⟩ | ⟨-, h⟩ <;> rw [h] <;> rfl
  | _ => simp [argWidth] at hT

/-- A pointer at a shape without a whole register (`argWidth < 64`: a narrow integer or a
boolean, as `lowW T ≤ argWidth T1` leaves): `poison`. -/
private theorem retypeL_ptr_narrow {T T1 : Ty} (h : lowW T ≤ argWidth T1)
    (h64 : ¬ 64 ≤ argWidth T1) (q : Ptr) : (Val.ptr q).retypeL T1 = .poison := by
  have hl := (lowW_pos T).1
  cases T1 with
  | int w => cases w <;> simp_all [argWidth, Width.bits, Val.retypeL, Val.widen, Val.retype]
  | bool => simp [Val.retypeL, Val.widen, Val.retype]
  | _ => simp_all [argWidth] <;> omega

/-- `ADDconst [1] a` at a shape keeping the result's low bits, moved (`regVal`): `CSINC`'s
register (`Arm64.csinc`). With a whole register, a pointer `a` moves alike at every shape, its
word kept at a word shape (`retypeL_word_wide`); else a pointer is `poison` there
(`retypeL_ptr_narrow`). A register `a` gives the sum's low bits (`refines_regVal_res`). -/
private theorem refines_regVal_addP {T T1 : Ty} (h : lowW T ≤ argWidth T1) (a : Val) :
    Refines ((Arm64.regVal T ((Arm64.addP T1 a 1).retypeL T1)).retypeL T)
      ((Arm64.regVal T (Arm64.addP T a 1)).retypeL T) := by
  have hP : Arm64.regVal T .poison = .poison := rfl
  by_cases hap : ∃ p, a = .ptr p
  · obtain ⟨p, rfl⟩ := hap
    simp only [Arm64.addP, PtrOps.ptrRes]
    split
    · by_cases h64 : 64 ≤ argWidth T1
      · rcases retypeL_word_wide (p.add 1) h64 with h' | h' <;> rw [h']
        · exact Refines.refl _
        · rw [hP, retypeL_poison]; exact .poison _
      · rcases Ptr.word_cases (p.add 1) with ⟨-, h'⟩ | ⟨-, x, -, h'⟩ <;> rw [h']
        · rw [retypeL_ptr_narrow h h64, hP, retypeL_poison]; exact .poison _
        · have hw : Arm64.regVal T (.int .w64 x) = Arm64.res T x := by
            simp [Arm64.regVal, Arm64.reg]
          rw [hw]
          cases T1 with
          | bool =>
            have : (Val.int .w64 x).retypeL .bool = .poison := by
              simp [Val.retypeL, Val.widen, Val.retype]
            rw [this, hP, retypeL_poison]; exact .poison _
          | _ => exact refines_regVal_res h x
    · rw [retypeL_poison]; exact Refines.refl _
  · have hA : ∀ T', Arm64.addP T' a 1 = match Arm64.reg a with
        | some x => Arm64.res T' (x + 1)
        | none => .poison := fun T' => by
      cases a <;> first | rfl | exact absurd ⟨_, rfl⟩ hap
    rw [hA, hA]
    cases hr : Arm64.reg a with
    | none => simp only [retypeL_poison, hP]; exact .poison _
    | some x =>
      refine (refines_regVal_res h (x + 1)).trans ?_
      rw [regVal_res]; exact Refines.refl _

private theorem refines_csel_csinc {T T1 : Ty} (h1 : lowW T ≤ argWidth T1) {k k' : Int64}
    {F : Val} (hk : ∀ b, Arm64.condOn k F = some b → Arm64.condOn k' F = some (id b))
    (X a : Val) :
    Refines ((Arm64.csel T k none [X, (Arm64.addP T1 a 1).retypeL T1, F]).retypeL T)
      ((Arm64.csinc T k' [X, a, F]).retypeL T) := by
  simp only [Arm64.csel, Arm64.csinc]
  cases hA : Arm64.condOn k F with
  | none => simp only [retypeL_poison]; exact .poison _
  | some b =>
    rw [hk b hA]
    cases b
    · exact refines_regVal_addP h1 a
    · exact Refines.refl _

private theorem refines_csel_csinc_neg {T T0 : Ty} (h0 : lowW T ≤ argWidth T0) {k k' : Int64}
    {F : Val} (hk : ∀ b, Arm64.condOn k F = some b → Arm64.condOn k' F = some (!b)) (X a : Val) :
    Refines ((Arm64.csel T k none [(Arm64.addP T0 a 1).retypeL T0, X, F]).retypeL T)
      ((Arm64.csinc T k' [X, a, F]).retypeL T) := by
  simp only [Arm64.csel, Arm64.csinc]
  cases hA : Arm64.condOn k F with
  | none => simp only [retypeL_poison]; exact .poison _
  | some b =>
    rw [hk b hA]
    cases b
    · exact Refines.refl _
    · exact refines_regVal_addP h0 a

private theorem auxInt_one {k : Int64} (h : DV.int k.toInt = DV.int 1) :
    BitVec.ofInt 64 k.toInt = 1 := by
  injection h with h; rw [h]; rfl

/-- `ARM64.rules:1190`: `(CSEL [cc] x (ADDconst [1] a) flag) => (CSINC [cc] x a flag)` -/
theorem r_ARM64_1190_sound : ArmRule.Checked r_ARM64_1190 := by
  left; arm_unfold; arm_norm
  simp only [armReadW_csel0, armReadW_csel1] at harg
  rw [auxInt_one hc]
  rcases ccDV_cases (e.auxInt []) with ⟨o, ho, hk⟩ | ⟨ho, hk⟩ <;> simp only [ho]
  · exact refines_csel_csinc harg.2.1.1 (condOn_goNum hk _) _ _
  · exact refines_csel_csinc harg.2.1.1 (condOn_none hk _ _ _) _ _

/-- `ccSplit r_ARM64_1191` on the condition op `cc`. -/
private def r1191 (cc : Op) : Rule where
  loc := ⟨"ARM64", 1191⟩
  op := .ARM64CSEL
  vars := [⟨"cc", .auxInt, (.named "Op")⟩, ⟨"a", .value, (.named "*Value")⟩, ⟨"x", .value, (.named "*Value")⟩, ⟨"flag", .value, (.named "*Value")⟩]
  pat := (.op .ARM64CSEL none .any (.bind 0) .any .fixed [(.op .ARM64ADDconst none .any (.eq (.lit .int64 (.int 1))) .any .fixed [(.bind 1)] false), (.bind 2), (.bind 3)] false)
  cond := some (ccCond 0 cc)
  block := none
  result := .build
      [{ op := .ARM64CSINC, ty := none, auxInt := some (.op (negOp cc)), aux := none, args := [.var 2, .var 1, .var 3] }]
  pos := []

private theorem ccSplit_1191 : ccSplit r_ARM64_1191 = negCondOps.map r1191 := by rfl

set_option maxRecDepth 100000 in
/-- `ARM64.rules:1191`: `(CSEL [cc] (ADDconst [1] a) x flag) => (CSINC [arm64Negate(cc)] x a flag)`, split by the condition (`ccSplit`) -/
theorem r_ARM64_1191_cc_sound : ForallL ArmRule.Checked (ccSplit r_ARM64_1191) := by
  rw [ccSplit_1191]
  simp only [negCondOps, intCondOps, List.cons_append, List.nil_append, List.map_cons,
    List.map_nil, ForallL]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  all_goals
    left; arm_unfold; arm_norm
    simp only [armReadW_csel0, armReadW_csel1] at harg
    simp only [ccCond, rule_unfold_ds, sigmaL, Pat.bindsL, Pat.bindssL, auxIntDVL] at hcond
    rw [auxInt_one hc]
    rcases ccDV_cases (e.auxInt []) with ⟨o, ho, hk⟩ | ⟨ho, hk⟩
    · rw [ho] at hcond
      simp [binE, binDV] at hcond
      subst hcond
      exact refines_csel_csinc_neg harg.1.1
        (condOn_neg (hk.trans rfl) (by decide) (by decide) _) _ _
    · exact refines_csel_csinc_neg harg.1.1 (condOn_none hk _ _ _) _ _

/-! ## Conditions on `TST` (`564-570`) -/

/-- A condition that does not read `C` (`EQ`, `NE` and the signed ones). -/
private def noC (c : Cond) : Prop := ∀ n z cf cf' v, c.eval n z cf v = c.eval n z cf' v

/-- On a condition that does not read `C`, `CMP r, #0` is `TST r, r`. -/
private theorem onVal_sub0_logic {n : Nat} (hn : 0 < n) {c : Cond} (hc : noC c) (r : BitVec n) :
    c.onVal (Arm64.subFlags r 0).2.toVal = c.onVal (logicFlags r).toVal := by
  rw [subFlags_zero hn]
  simp only [Flags.toVal, Cond.onVal, logicFlags, Val.flagBit]
  exact hc _ _ _ _ _

private theorem refines_cset_of {op : Op} {A B : Val}
    (h : ∀ c, Cond.ofOp op = some c → ∀ b, c.onVal A = some b → c.onVal B = some b) (T : Ty) :
    Refines ((Arm64.cset T op [A]).retypeL T) ((Arm64.cset T op [B]).retypeL T) := by
  simp only [Arm64.cset]
  cases hc : Cond.ofOp op with
  | none => simp only [Option.bind_none, retypeL_poison]; exact .poison _
  | some c =>
    simp only [Option.bind_some]
    cases hA : c.onVal A with
    | none => simp only [retypeL_poison]; exact .poison _
    | some b => rw [h c hc b hA]; exact Refines.refl _

/-- `CMPconst [0]` of a 64-bit register result read at a whole-register shape. -/
private theorem onVal_cmp0_res {T0 T1 : Ty} (h1 : 64 ≤ argWidth T1) {c : Cond} (hc : noC c)
    (r : BitVec 64) {b : Bool}
    (h : c.onVal ((Arm64.cmp ((Arm64.res T1 r).retypeL T1) (.int .w64 0)).retypeL T0) = some b) :
    c.onVal (logicFlags r).toVal = some b := by
  have h' := Mono.onVal_of (retypeL_cmp_ref T0 _ _) h
  rcases retypeL_res_wide h1 r with he | he <;> rw [he] at h'
  · have : Arm64.cmp (.int .w64 r) (.int .w64 0) = Arm64.cmpRes (Arm64.subFlags r 0) := rfl
    rw [this, onVal_cmpRes, onVal_sub0_logic (by decide) hc] at h'
    exact h'
  · have : Arm64.cmp .poison (.int .w64 0) = .poison := rfl
    rw [this] at h'; simp [Cond.onVal] at h'

private theorem onVal_cmp0_poison {T0 : Ty} {c : Cond} {b : Bool}
    (h : c.onVal ((Arm64.cmp (Val.poison.retypeL T1) (.int .w64 0)).retypeL T0) = some b) : False := by
  have h' := Mono.onVal_of (retypeL_cmp_ref T0 _ _) h
  rw [retypeL_poison] at h'
  have : Arm64.cmp .poison (.int .w64 0) = .poison := rfl
  rw [this] at h'; simp [Cond.onVal] at h'

/-- `CMPWconst [0]` of a register result read at a shape with at least 32 bits. -/
private theorem onVal_cmpw0_res {T0 T1 : Ty} (h1 : 32 ≤ argWidth T1) {c : Cond} (hc : noC c)
    (r : BitVec 64) {b : Bool}
    (h : c.onVal ((Arm64.cmp1w (fun x => Arm64.subFlags x 0) [(Arm64.res T1 r).retypeL T1]).retypeL T0) = some b) :
    c.onVal (logicFlags (r.setWidth 32)).toVal = some b := by
  have h' := Mono.onVal_of (retypeL_cmp1w_ref T0 _ _) h
  rcases retypeL_res_w32 h1 r with he | he
  · simp only [Arm64.cmp1w, he, onVal_cmpRes] at h'
    rw [onVal_sub0_logic (by decide) hc] at h'
    exact h'
  · rw [he] at h'; simp [Arm64.cmp1w, Arm64.reg32, Arm64.reg, Cond.onVal] at h'

private theorem onVal_cmpw0_poison {T0 : Ty} {c : Cond} {b : Bool}
    (h : c.onVal ((Arm64.cmp1w (fun x => Arm64.subFlags x 0) [Val.poison.retypeL T1]).retypeL T0) = some b) : False := by
  have h' := Mono.onVal_of (retypeL_cmp1w_ref T0 _ _) h
  rw [retypeL_poison] at h'
  simp [Arm64.cmp1w, Arm64.reg32, Arm64.reg, Cond.onVal] at h'

private theorem flags_retypeL {f : Flags} : f.toVal.retypeL Ty.flags = f.toVal := rfl

/-- `(cc (CMPconst [0] (AND x y)))` as `(cc (TST x y))`. -/
private theorem refines_tst {op : Op} {c0 : Cond} (hop : Cond.ofOp op = some c0) (hc0 : noC c0)
    {T0 T1 : Ty} (h1 : 64 ≤ argWidth T1) (T : Ty) (x y : Val) {k : Int64}
    (hk : DV.int k.toInt = DV.int 0) :
    Refines ((Arm64.cset T op [(Arm64.cmp ((Arm64.op2 T1 (fun x1 x2 => x1 &&& x2) [x, y]).retypeL T1)
        (.int .w64 (BitVec.ofInt 64 k.toInt))).retypeL T0]).retypeL T)
      ((Arm64.cset T op [(Arm64.flags2 (fun x y => logicFlags (x &&& y)) [x, y]).retypeL Ty.flags]).retypeL T) := by
  injection hk with hk; rw [hk]
  refine refines_cset_of (fun c hc b h => ?_) T
  rw [hop] at hc; cases hc
  cases hx : Arm64.reg x <;> cases hy : Arm64.reg y <;> simp only [Arm64.op2, hx, hy] at h
  any_goals exact absurd h (fun h => onVal_cmp0_poison h)
  simp only [Arm64.flags2, hx, hy, flags_retypeL]
  exact onVal_cmp0_res h1 hc0 _ h


/-- `(cc (CMPconst [0] (ANDconst [c] y)))` as `(cc (TSTconst [c] y))`. -/
private theorem refines_tst_const {op : Op} {c0 : Cond} (hop : Cond.ofOp op = some c0) (hc0 : noC c0)
    {T0 T1 : Ty} (h1 : 64 ≤ argWidth T1) (T : Ty) (y : Val) (C : BitVec 64) {k : Int64}
    (hk : DV.int k.toInt = DV.int 0) :
    Refines ((Arm64.cset T op [(Arm64.cmp ((Arm64.op1 T1 (fun x => x &&& C) [y]).retypeL T1)
        (.int .w64 (BitVec.ofInt 64 k.toInt))).retypeL T0]).retypeL T)
      ((Arm64.cset T op [(Arm64.flags1 (fun x => logicFlags (x &&& C)) [y]).retypeL Ty.flags]).retypeL T) := by
  injection hk with hk; rw [hk]
  refine refines_cset_of (fun c hc b h => ?_) T
  rw [hop] at hc; cases hc
  cases hy : Arm64.reg y <;> simp only [Arm64.op1, hy] at h
  · exact absurd h (fun h => onVal_cmp0_poison h)
  simp only [Arm64.flags1, hy, flags_retypeL]
  exact onVal_cmp0_res h1 hc0 _ h

/-- `(cc (CMPWconst [0] (AND x y)))` as `(cc (TSTW x y))`. -/
private theorem refines_tstw {op : Op} {c0 : Cond} (hop : Cond.ofOp op = some c0) (hc0 : noC c0)
    {T0 T1 : Ty} (h1 : 32 ≤ argWidth T1) (T : Ty) (x y : Val) {k : Int64}
    (hk : DV.int (wrapInt 32 true k.toInt) = DV.int 0) :
    Refines ((Arm64.cset T op [(Arm64.cmp1w (fun x => Arm64.subFlags x (Arm64.imm32 k))
        [(Arm64.op2 T1 (fun x1 x2 => x1 &&& x2) [x, y]).retypeL T1]).retypeL T0]).retypeL T)
      ((Arm64.cset T op [(Arm64.flags2w (fun x y => logicFlags (x &&& y)) [x, y]).retypeL Ty.flags]).retypeL T) := by
  injection hk with hk; rw [imm32_of_zero hk]
  refine refines_cset_of (fun c hc b h => ?_) T
  rw [hop] at hc; cases hc
  cases hx : Arm64.reg x <;> cases hy : Arm64.reg y <;> simp only [Arm64.op2, hx, hy] at h
  any_goals exact absurd h (fun h => onVal_cmpw0_poison h)
  simp only [Arm64.flags2w, Arm64.reg32, hx, hy, Option.map_some, flags_retypeL]
  have h' := onVal_cmpw0_res h1 hc0 _ h
  rwa [BitVec.setWidth_and] at h'

/-- `(cc (CMPWconst [0] (ANDconst [c] y)))` as `(cc (TSTWconst [int32(c)] y))`. -/
private theorem refines_tstw_const {op : Op} {c0 : Cond} (hop : Cond.ofOp op = some c0) (hc0 : noC c0)
    {T0 T1 : Ty} (h1 : 32 ≤ argWidth T1) (T : Ty) (y : Val) (C : Int) {k : Int64}
    (hk : DV.int (wrapInt 32 true k.toInt) = DV.int 0) :
    Refines ((Arm64.cset T op [(Arm64.cmp1w (fun x => Arm64.subFlags x (Arm64.imm32 k))
        [(Arm64.op1 T1 (fun x => x &&& BitVec.ofInt 64 C) [y]).retypeL T1]).retypeL T0]).retypeL T)
      ((Arm64.cset T op [(Arm64.flags1w (fun x => logicFlags (x &&& Arm64.imm32
        (Int64.ofInt (wrapInt 32 true C)))) [y]).retypeL Ty.flags]).retypeL T) := by
  injection hk with hk; rw [imm32_of_zero hk, imm32_wrap]
  refine refines_cset_of (fun c hc b h => ?_) T
  rw [hop] at hc; cases hc
  cases hy : Arm64.reg y <;> simp only [Arm64.op1, hy] at h
  · exact absurd h (fun h => onVal_cmpw0_poison h)
  simp only [Arm64.flags1w, Arm64.reg32, hy, Option.map_some, flags_retypeL]
  have h' := onVal_cmpw0_res h1 hc0 _ h
  rwa [BitVec.setWidth_and, setWidth_ofInt_le (by decide)] at h'

/-- `ARM64.rules:564`: `(Equal (CMPconst [0] z:(AND x y))) && z.Uses == 1 => (Equal (TST x y))` -/
theorem r_ARM64_564_sound : ArmRule.Checked r_ARM64_564 := by
  left; arm_unfold; all_goals arm_norm
  all_goals exact refines_tst rfl (fun _ _ _ _ _ => rfl) harg.2.1 _ _ _ hc

/-- `ARM64.rules:564`: `(GreaterEqual (CMPconst [0] z:(AND x y))) && z.Uses == 1 => (GreaterEqual (TST x y))` -/
theorem r_ARM64_564_2_sound : ArmRule.Checked r_ARM64_564_2 := by
  left; arm_unfold; all_goals arm_norm
  all_goals exact refines_tst rfl (fun _ _ _ _ _ => rfl) harg.2.1 _ _ _ hc

/-- `ARM64.rules:564`: `(GreaterThan (CMPconst [0] z:(AND x y))) && z.Uses == 1 => (GreaterThan (TST x y))` -/
theorem r_ARM64_564_3_sound : ArmRule.Checked r_ARM64_564_3 := by
  left; arm_unfold; all_goals arm_norm
  all_goals exact refines_tst rfl (fun _ _ _ _ _ => rfl) harg.2.1 _ _ _ hc

/-- `ARM64.rules:564`: `(LessEqual (CMPconst [0] z:(AND x y))) && z.Uses == 1 => (LessEqual (TST x y))` -/
theorem r_ARM64_564_4_sound : ArmRule.Checked r_ARM64_564_4 := by
  left; arm_unfold; all_goals arm_norm
  all_goals exact refines_tst rfl (fun _ _ _ _ _ => rfl) harg.2.1 _ _ _ hc

/-- `ARM64.rules:564`: `(LessThan (CMPconst [0] z:(AND x y))) && z.Uses == 1 => (LessThan (TST x y))` -/
theorem r_ARM64_564_5_sound : ArmRule.Checked r_ARM64_564_5 := by
  left; arm_unfold; all_goals arm_norm
  all_goals exact refines_tst rfl (fun _ _ _ _ _ => rfl) harg.2.1 _ _ _ hc

/-- `ARM64.rules:564`: `(NotEqual (CMPconst [0] z:(AND x y))) && z.Uses == 1 => (NotEqual (TST x y))` -/
theorem r_ARM64_564_6_sound : ArmRule.Checked r_ARM64_564_6 := by
  left; arm_unfold; all_goals arm_norm
  all_goals exact refines_tst rfl (fun _ _ _ _ _ => rfl) harg.2.1 _ _ _ hc

/-- `ARM64.rules:566`: `(Equal (CMPWconst [0] x:(ANDconst [c] y))) && x.Uses == 1 => (Equal (TSTWconst [int32(c)] y))` -/
theorem r_ARM64_566_sound : ArmRule.Checked r_ARM64_566 := by
  left; arm_unfold; all_goals arm_norm
  all_goals exact refines_tstw_const rfl (fun _ _ _ _ _ => rfl) harg.2 _ _ _ hc

/-- `ARM64.rules:566`: `(GreaterEqual (CMPWconst [0] x:(ANDconst [c] y))) && x.Uses == 1 => (GreaterEqual (TSTWconst [int32(c)] y))` -/
theorem r_ARM64_566_2_sound : ArmRule.Checked r_ARM64_566_2 := by
  left; arm_unfold; all_goals arm_norm
  all_goals exact refines_tstw_const rfl (fun _ _ _ _ _ => rfl) harg.2 _ _ _ hc

/-- `ARM64.rules:566`: `(GreaterThan (CMPWconst [0] x:(ANDconst [c] y))) && x.Uses == 1 => (GreaterThan (TSTWconst [int32(c)] y))` -/
theorem r_ARM64_566_3_sound : ArmRule.Checked r_ARM64_566_3 := by
  left; arm_unfold; all_goals arm_norm
  all_goals exact refines_tstw_const rfl (fun _ _ _ _ _ => rfl) harg.2 _ _ _ hc

/-- `ARM64.rules:566`: `(LessEqual (CMPWconst [0] x:(ANDconst [c] y))) && x.Uses == 1 => (LessEqual (TSTWconst [int32(c)] y))` -/
theorem r_ARM64_566_4_sound : ArmRule.Checked r_ARM64_566_4 := by
  left; arm_unfold; all_goals arm_norm
  all_goals exact refines_tstw_const rfl (fun _ _ _ _ _ => rfl) harg.2 _ _ _ hc

/-- `ARM64.rules:566`: `(LessThan (CMPWconst [0] x:(ANDconst [c] y))) && x.Uses == 1 => (LessThan (TSTWconst [int32(c)] y))` -/
theorem r_ARM64_566_5_sound : ArmRule.Checked r_ARM64_566_5 := by
  left; arm_unfold; all_goals arm_norm
  all_goals exact refines_tstw_const rfl (fun _ _ _ _ _ => rfl) harg.2 _ _ _ hc

/-- `ARM64.rules:566`: `(NotEqual (CMPWconst [0] x:(ANDconst [c] y))) && x.Uses == 1 => (NotEqual (TSTWconst [int32(c)] y))` -/
theorem r_ARM64_566_6_sound : ArmRule.Checked r_ARM64_566_6 := by
  left; arm_unfold; all_goals arm_norm
  all_goals exact refines_tstw_const rfl (fun _ _ _ _ _ => rfl) harg.2 _ _ _ hc

/-- `ARM64.rules:568`: `(Equal (CMPWconst [0] z:(AND x y))) && z.Uses == 1 => (Equal (TSTW x y))` -/
theorem r_ARM64_568_sound : ArmRule.Checked r_ARM64_568 := by
  left; arm_unfold; all_goals arm_norm
  all_goals exact refines_tstw rfl (fun _ _ _ _ _ => rfl) harg.2.1 _ _ _ hc

/-- `ARM64.rules:568`: `(GreaterEqual (CMPWconst [0] z:(AND x y))) && z.Uses == 1 => (GreaterEqual (TSTW x y))` -/
theorem r_ARM64_568_2_sound : ArmRule.Checked r_ARM64_568_2 := by
  left; arm_unfold; all_goals arm_norm
  all_goals exact refines_tstw rfl (fun _ _ _ _ _ => rfl) harg.2.1 _ _ _ hc

/-- `ARM64.rules:568`: `(GreaterThan (CMPWconst [0] z:(AND x y))) && z.Uses == 1 => (GreaterThan (TSTW x y))` -/
theorem r_ARM64_568_3_sound : ArmRule.Checked r_ARM64_568_3 := by
  left; arm_unfold; all_goals arm_norm
  all_goals exact refines_tstw rfl (fun _ _ _ _ _ => rfl) harg.2.1 _ _ _ hc

/-- `ARM64.rules:568`: `(LessEqual (CMPWconst [0] z:(AND x y))) && z.Uses == 1 => (LessEqual (TSTW x y))` -/
theorem r_ARM64_568_4_sound : ArmRule.Checked r_ARM64_568_4 := by
  left; arm_unfold; all_goals arm_norm
  all_goals exact refines_tstw rfl (fun _ _ _ _ _ => rfl) harg.2.1 _ _ _ hc

/-- `ARM64.rules:568`: `(LessThan (CMPWconst [0] z:(AND x y))) && z.Uses == 1 => (LessThan (TSTW x y))` -/
theorem r_ARM64_568_5_sound : ArmRule.Checked r_ARM64_568_5 := by
  left; arm_unfold; all_goals arm_norm
  all_goals exact refines_tstw rfl (fun _ _ _ _ _ => rfl) harg.2.1 _ _ _ hc

/-- `ARM64.rules:568`: `(NotEqual (CMPWconst [0] z:(AND x y))) && z.Uses == 1 => (NotEqual (TSTW x y))` -/
theorem r_ARM64_568_6_sound : ArmRule.Checked r_ARM64_568_6 := by
  left; arm_unfold; all_goals arm_norm
  all_goals exact refines_tstw rfl (fun _ _ _ _ _ => rfl) harg.2.1 _ _ _ hc

/-- `ARM64.rules:570`: `(Equal (CMPconst [0] x:(ANDconst [c] y))) && x.Uses == 1 => (Equal (TSTconst [c] y))` -/
theorem r_ARM64_570_sound : ArmRule.Checked r_ARM64_570 := by
  left; arm_unfold; all_goals arm_norm
  all_goals exact refines_tst_const rfl (fun _ _ _ _ _ => rfl) harg.2.1 _ _ _ hc

/-- `ARM64.rules:570`: `(GreaterEqual (CMPconst [0] x:(ANDconst [c] y))) && x.Uses == 1 => (GreaterEqual (TSTconst [c] y))` -/
theorem r_ARM64_570_2_sound : ArmRule.Checked r_ARM64_570_2 := by
  left; arm_unfold; all_goals arm_norm
  all_goals exact refines_tst_const rfl (fun _ _ _ _ _ => rfl) harg.2.1 _ _ _ hc

/-- `ARM64.rules:570`: `(GreaterThan (CMPconst [0] x:(ANDconst [c] y))) && x.Uses == 1 => (GreaterThan (TSTconst [c] y))` -/
theorem r_ARM64_570_3_sound : ArmRule.Checked r_ARM64_570_3 := by
  left; arm_unfold; all_goals arm_norm
  all_goals exact refines_tst_const rfl (fun _ _ _ _ _ => rfl) harg.2.1 _ _ _ hc

/-- `ARM64.rules:570`: `(LessEqual (CMPconst [0] x:(ANDconst [c] y))) && x.Uses == 1 => (LessEqual (TSTconst [c] y))` -/
theorem r_ARM64_570_4_sound : ArmRule.Checked r_ARM64_570_4 := by
  left; arm_unfold; all_goals arm_norm
  all_goals exact refines_tst_const rfl (fun _ _ _ _ _ => rfl) harg.2.1 _ _ _ hc

/-- `ARM64.rules:570`: `(LessThan (CMPconst [0] x:(ANDconst [c] y))) && x.Uses == 1 => (LessThan (TSTconst [c] y))` -/
theorem r_ARM64_570_5_sound : ArmRule.Checked r_ARM64_570_5 := by
  left; arm_unfold; all_goals arm_norm
  all_goals exact refines_tst_const rfl (fun _ _ _ _ _ => rfl) harg.2.1 _ _ _ hc

/-- `ARM64.rules:570`: `(NotEqual (CMPconst [0] x:(ANDconst [c] y))) && x.Uses == 1 => (NotEqual (TSTconst [c] y))` -/
theorem r_ARM64_570_6_sound : ArmRule.Checked r_ARM64_570_6 := by
  left; arm_unfold; all_goals arm_norm
  all_goals exact refines_tst_const rfl (fun _ _ _ _ _ => rfl) harg.2.1 _ _ _ hc

/-! ## Booleans -/

private theorem asBool_eq_some {v : Val} {b : Bool} (h : v.asBool = some b) : v = .bool b := by
  cases v <;> simp_all [Val.asBool]

/-- `ARM64.rules:137`: `(Not x) => (XOR (MOVDconst [1]) x)` -/
theorem r_ARM64_137_sound : ArmRule.Checked r_ARM64_137 := by
  left; arm_unfold; arm_shape; all_goals arm_norm
  all_goals
    rcases h : (e.leaf [0]).asBool with _ | b
    · simp only [Option.elim, retypeL_poison]; exact .poison _
    · rw [asBool_eq_some h]; cases b <;> exact Refines.refl _

/-- `ARM64.rules:135`: `(EqB x y) => (XOR (MOVDconst [1]) (XOR <typ.Bool> x y))` -/
theorem r_ARM64_135_sound : ArmRule.Checked r_ARM64_135 := by
  left; arm_unfold; arm_shape; all_goals arm_norm
  all_goals
    rcases h : (e.leaf [0]).asBool with _ | a
    · simp only [Option.elim, retypeL_poison]; exact .poison _
    · rcases h' : (e.leaf [1]).asBool with _ | b
      · simp only [Option.elim, retypeL_poison]; exact .poison _
      · rw [asBool_eq_some h, asBool_eq_some h']; cases a <;> cases b <;> exact Refines.refl _

private theorem bool2_cases (f : Bool → Bool → Bool) (args : List Val) :
    bool2 f args = .poison ∨ ∃ a b, args = [.bool a, .bool b] ∧ bool2 f args = .bool (f a b) := by
  match args with
  | [x, y] =>
    rcases hx : x.asBool with _ | a
    · exact .inl (by simp [bool2, hx])
    rcases hy : y.asBool with _ | b
    · exact .inl (by simp [bool2, hx, hy])
    exact .inr ⟨a, b, by rw [asBool_eq_some hx, asBool_eq_some hy], by simp [bool2, hx, hy]⟩
  | [] => exact .inl rfl
  | [_] => exact .inl rfl
  | _ :: _ :: _ :: _ => exact .inl rfl

private theorem s_NeqB_ARM64XOR : SetOpSound .NeqB .ARM64XOR := by
  intro tabs ty ai ax args ht
  simp (disch := decide) only [opValL_arm, opValL_gen, reduceArmEvalPure, reduceEvalPure, Cmp.neqB]
  rcases bool2_cases (· != ·) args with h | ⟨a, b, rfl, h⟩
  · rw [h, retypeL_poison]; exact .poison _
  rw [h]
  cases ty with
  | bool => cases a <;> cases b <;> exact Refines.refl _
  | int w => cases w <;> cases a <;> cases b <;> exact Refines.refl _
  | _ => first | exact absurd ht Bool.false_ne_true | (cases a <;> cases b <;> exact Refines.refl _)

/-- `ARM64.rules:136`: `(NeqB ...) => (XOR ...)` -/
theorem r_ARM64_136_sound : ArmRule.Checked r_ARM64_136 :=
  checked_setOp .NeqB .ARM64XOR rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    s_NeqB_ARM64XOR

/-! ## `Slicemask`, unsigned compares with zero -/

/-- `ASR #63` of the negation of a nonnegative word: 0 for 0, else −1. -/
private theorem sra63_neg (x : BitVec 64) (h : x.msb = false) :
    (-x).sshiftRight 63 = if x = 0 then 0 else -1 := by
  split
  · rename_i hx; subst hx; rfl
  · rename_i hx
    have hm : (-x).msb = true := by
      rw [BitVec.msb_neg, h]
      have : x ≠ BitVec.intMin 64 := by
        intro he; rw [he] at h; exact absurd h (by decide)
      simp [show x ≠ 0#64 from hx, this]
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [BitVec.getLsbD_sshiftRight, hm]
    have : (-1 : BitVec 64).getLsbD i = true := by
      rw [show (-1 : BitVec 64) = BitVec.allOnes 64 by decide, BitVec.getLsbD_allOnes]; simp [hi]
    rw [this]
    by_cases h0 : i = 0
    · subst h0
      have h63 := hm
      rw [BitVec.msb_eq_getLsbD_last] at h63
      simpa using h63
    · simp [show ¬ 63 + i < 64 by omega, show ¬ 64 ≤ i by omega]

/-- `ARM64.rules:187`: `(Slicemask <t> x) => (SRAconst (NEG <t> x) [63])` -/
theorem r_ARM64_187_sound : ArmRule.Checked r_ARM64_187 := by
  left; arm_unfold; arm_shape; all_goals arm_norm
  all_goals
    rcases h : (e.leaf [0]).asInt _ with _ | x
    · simp only [Option.elim, retypeL_poison]; exact .poison _
    · rw [asInt_eq_some h] at hty ⊢
      rw [hat] at hty
      (try (simp [Val.hasTy] at hty; done)) <;> (
      simp only [Option.elim]
      split
      · simp only [retypeL_poison]; exact .poison _
      · rename_i hm
        have hm' : x.msb = false := by simpa using hm
        simp [Arm64.op1, Arm64.reg, Arm64.res, Arm64.Shift.apply, Arm64.amt, sra63_neg x hm']
        exact Refines.refl _)

/-- A zero constant register read as a `w`-bit integer is 0. -/
private theorem asInt_res_zero {T0 : Ty} {w : Width} {z : BitVec w.bits}
    (h : ((Arm64.res T0 0).retypeL T0).asInt w = some z) : z = 0 := by
  cases T0 with
  | int w' =>
    rw [retypeL_res_int] at h
    cases w' <;> cases w <;> simp [Val.asInt] at h <;> (subst h; rfl)
  | bool => simp_all [Arm64.res, Val.retypeL, Val.widen, Val.retype, Val.asInt]
  | ptr el => cases w <;> simp_all [Arm64.res, Val.retypeL, Val.widen, Val.retype, Val.asInt]
  | _ => simp_all [Arm64.res, Val.retypeL, Val.widen, Val.retype, Val.asInt]

private theorem zero_ult {n : Nat} (y : BitVec n) : (0 : BitVec n).ult y = ((0 : BitVec n) != y) := by
  apply Bool.eq_iff_iff.mpr
  simp only [BitVec.ult_iff_lt, BitVec.lt_def, BitVec.toNat_ofNat, Nat.zero_mod, bne_iff_ne, ne_eq,
    BitVec.ofNat_eq_ofNat]
  constructor
  · intro h h'; subst h'; simp at h
  · intro h
    have : y.toNat ≠ 0 := fun h0 => h (BitVec.eq_of_toNat_eq (by simp [h0])).symm
    omega

/-- `ARM64.rules:271`: `(Less16U zero:(MOVDconst [0]) x) => (Neq16 zero x)` -/
theorem r_ARM64_271_sound : ArmRule.Checked r_ARM64_271 := by
  left; arm_unfold; arm_norm
  injection hc with hc; rw [hc]
  rcases h : Val.asInt _ ((Arm64.res (e.ty [0]) (BitVec.ofInt 64 0)).retypeL (e.ty [0])) with _ | z
  · simp only [Option.elim, retypeL_poison]; exact .poison _
  · obtain rfl := asInt_res_zero h
    rcases h1 : (e.leaf [1]).asInt _ with _ | y <;> simp only [Option.elim]
    · rw [retypeL_poison]; exact .poison _
    · rw [zero_ult]; exact Refines.refl _

/-- `ARM64.rules:271`: `(Less32U zero:(MOVDconst [0]) x) => (Neq32 zero x)` -/
theorem r_ARM64_271_2_sound : ArmRule.Checked r_ARM64_271_2 := by
  left; arm_unfold; arm_norm
  injection hc with hc; rw [hc]
  rcases h : Val.asInt _ ((Arm64.res (e.ty [0]) (BitVec.ofInt 64 0)).retypeL (e.ty [0])) with _ | z
  · simp only [Option.elim, retypeL_poison]; exact .poison _
  · obtain rfl := asInt_res_zero h
    rcases h1 : (e.leaf [1]).asInt _ with _ | y <;> simp only [Option.elim]
    · rw [retypeL_poison]; exact .poison _
    · rw [zero_ult]; exact Refines.refl _

/-- `ARM64.rules:271`: `(Less64U zero:(MOVDconst [0]) x) => (Neq64 zero x)` -/
theorem r_ARM64_271_3_sound : ArmRule.Checked r_ARM64_271_3 := by
  left; arm_unfold; arm_norm
  injection hc with hc; rw [hc]
  rcases h : Val.asInt _ ((Arm64.res (e.ty [0]) (BitVec.ofInt 64 0)).retypeL (e.ty [0])) with _ | z
  · simp only [Option.elim, retypeL_poison]; exact .poison _
  · obtain rfl := asInt_res_zero h
    rcases h1 : (e.leaf [1]).asInt _ with _ | y <;> simp only [Option.elim]
    · rw [retypeL_poison]; exact .poison _
    · rw [zero_ult]; exact Refines.refl _

/-- `ARM64.rules:271`: `(Less8U zero:(MOVDconst [0]) x) => (Neq8 zero x)` -/
theorem r_ARM64_271_4_sound : ArmRule.Checked r_ARM64_271_4 := by
  left; arm_unfold; arm_norm
  injection hc with hc; rw [hc]
  rcases h : Val.asInt _ ((Arm64.res (e.ty [0]) (BitVec.ofInt 64 0)).retypeL (e.ty [0])) with _ | z
  · simp only [Option.elim, retypeL_poison]; exact .poison _
  · obtain rfl := asInt_res_zero h
    rcases h1 : (e.leaf [1]).asInt _ with _ | y <;> simp only [Option.elim]
    · rw [retypeL_poison]; exact .poison _
    · rw [zero_ult]; exact Refines.refl _

/-! ## High multiplication, division and remainder -/

/-- `ARM64.rules:15`: `(Hmul64 ...) => (MULH ...)` -/
theorem r_ARM64_15_sound : ArmRule.Checked r_ARM64_15 :=
  checked_setOp .Hmul64 .ARM64MULH rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    (setOpSound_int2 .w64 Arm64.smulh (fun _ _ _ _ _ => rfl) (by arm_reg))

/-- `ARM64.rules:16`: `(Hmul64u ...) => (UMULH ...)` -/
theorem r_ARM64_16_sound : ArmRule.Checked r_ARM64_16 :=
  checked_setOp .Hmul64u .ARM64UMULH rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    (setOpSound_int2 .w64 Arm64.umulh (fun _ _ _ _ _ => rfl) (by arm_reg))

/-- `ARM64.rules:22`: `(Div64 [false] x y) => (DIV x y)` -/
theorem r_ARM64_22_sound : ArmRule.Checked r_ARM64_22 := by
  left; arm_unfold; arm_norm
  rcases h0 : (e.leaf [0]).asInt .w64 with _ | x
  · simp only [Option.elim, retypeL_poison]; exact .poison _
  rcases h1 : (e.leaf [1]).asInt .w64 with _ | y
  · simp only [Option.elim, retypeL_poison]; exact .poison _
  rw [asInt_eq_some h0, asInt_eq_some h1]
  simp only [Option.elim]
  split
  · rw [retypeL_poison]; exact .poison _
  split
  · rw [retypeL_poison]; exact .poison _
  exact refines_res64 _ _

/-- `x − (x / y)·y` (`SDIV` + `MSUB`) is the truncated remainder. -/
private theorem srem_eq_sub (x y : BitVec 64) : x.srem y = x - x.sdiv y * y := by
  have hb : ∀ z : Int, BitVec.ofInt 64 (z.bmod (2 ^ 64)) = BitVec.ofInt 64 z := by
    intro z
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofInt]
    exact congrArg Int.toNat (Int.bmod_emod (x := z) (m := 2 ^ 64))
  have hq : x.sdiv y = BitVec.ofInt 64 (x.toInt.tdiv y.toInt) := by
    rw [← BitVec.ofInt_toInt (x := x.sdiv y), BitVec.toInt_sdiv, hb]
  rw [← BitVec.ofInt_toInt (x := x.srem y), BitVec.toInt_srem, Int.tmod_def, hq]
  conv => rhs; rw [← BitVec.ofInt_toInt (x := x), ← BitVec.ofInt_toInt (x := y)]
  rw [BitVec.ofInt_toInt, BitVec.ofInt_toInt, Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg,
    BitVec.ofInt_mul, BitVec.ofInt_toInt, BitVec.ofInt_toInt, BitVec.sub_eq_add_neg, BitVec.mul_comm]

/-- `ARM64.rules:33`: `(Mod64 x y) => (MOD x y)` -/
theorem r_ARM64_33_sound : ArmRule.Checked r_ARM64_33 := by
  left; arm_unfold; arm_norm
  rcases h0 : (e.leaf [0]).asInt .w64 with _ | x
  · simp only [Option.elim, retypeL_poison]; exact .poison _
  rcases h1 : (e.leaf [1]).asInt .w64 with _ | y
  · simp only [Option.elim, retypeL_poison]; exact .poison _
  rw [asInt_eq_some h0, asInt_eq_some h1]
  simp only [Option.elim]
  split
  · rw [retypeL_poison]; exact .poison _
  split
  · rw [retypeL_poison]; exact .poison _
  have : Arm64.op2 (e.ty []) Arm64.srem [.int .w64 x, .int .w64 y] = Arm64.res (e.ty []) (x.srem y) := by
    rw [srem_eq_sub]; rfl
  rw [this]; exact refines_res64 _ _

/-- `x − (x / y)·y` (`UDIV` + `MSUB`) is the unsigned remainder. -/
private theorem urem_eq (x y : BitVec 64) : Arm64.urem x y = x % y := by
  unfold Arm64.urem
  have hd := Nat.div_add_mod x.toNat y.toNat
  have hle : x.toNat / y.toNat * y.toNat ≤ x.toNat := Nat.div_mul_le_self _ _
  have h1 : (x / y * y).toNat = x.toNat / y.toNat * y.toNat := by
    rw [BitVec.toNat_mul, BitVec.toNat_udiv]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hle x.isLt)
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, h1]; exact hle), h1, BitVec.toNat_umod]
  rw [Nat.mul_comm] at hd
  omega

/-- `SetOpSound` of a partial binary `w`-bit op (`poison` or the value) whose arm64 op computes
the zero-extended value. -/
private theorem setOpSound_int2_part {o o' : Op} (w : Width) (g : BitVec w.bits → BitVec w.bits → Val)
    (f : BitVec w.bits → BitVec w.bits → BitVec w.bits)
    (h1 : ∀ tabs ty ai ax args, opValL tabs o ty ai ax args = GoFV.SSA.Sem.int2 w g args)
    (hg : ∀ x y, g x y = .poison ∨ g x y = .int w (f x y))
    (h2 : ∀ tabs ty ai ax x y,
      opValL tabs o' ty ai ax [.int w x, .int w y] = Arm64.res ty ((f x y).setWidth 64)) :
    SetOpSound o o' := by
  intro tabs ty ai ax args _
  rw [h1]
  rcases int2_cases w g args with h | ⟨x, y, rfl, h⟩
  · rw [h, retypeL_poison]; exact .poison _
  · rw [h, h2]
    rcases hg x y with h' | h' <;> rw [h']
    · rw [retypeL_poison]; exact .poison _
    · exact refines_res_zext ty w (f x y)

/-- `ARM64.rules:28`: `(Div64u ...) => (UDIV ...)` -/
theorem r_ARM64_28_sound : ArmRule.Checked r_ARM64_28 :=
  checked_setOp .Div64u .ARM64UDIV rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    (setOpSound_int2_part .w64 (fun x y => if y = 0 then .poison else .int .w64 (x / y)) Arm64.udiv
      (fun _ _ _ _ _ => rfl) (fun x y => by split <;> simp [Arm64.udiv]) (by arm_reg))

/-- `ARM64.rules:35`: `(Mod64u ...) => (UMOD ...)` -/
theorem r_ARM64_35_sound : ArmRule.Checked r_ARM64_35 :=
  checked_setOp .Mod64u .ARM64UMOD rfl rfl rfl rfl (termVL_generic _ rfl rfl) (termVL_arm _ rfl rfl rfl)
    (setOpSound_int2_part .w64 (fun x y => if y = 0 then .poison else .int .w64 (x % y))
      (fun x y => x % y) (fun _ _ _ _ _ => rfl) (fun x y => by split <;> simp)
      (by arm_reg; rw [urem_eq]))

end GoFV.Proof.Low.Rules
