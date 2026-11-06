import GoFV.Proof.Low.Rules.BlockFlags
import GoFV.Rules.Derive

/-!
# Lowering rule lemmas: `InvertFlags` (`ARM64.rules:991`, `993`, `1003`, `1352-1357`, `1374-1383`)

`InvertFlags f` is the flags of the compare with swapped operands (`Sem.invertFlags`, from the
fifth flags component `g`, the sign of the negated difference, which only `InvertFlags` reads):

* `(CMP x y) && canonLessThan(x,y) => (InvertFlags (CMP y x))` (`1003`, and `CMPW`), `(CMP
  (MOVDconst [c]) x) => (InvertFlags (CMPconst [c] x))` (`991`, and `CMPW`, `993`): `InvertFlags`
  of the swapped compare is the compare itself, value for value (`invertFlags_cmp`,
  `invertFlags_cmp2w`, both from `invertFlags_sub`).
* `(Equal (InvertFlags x)) => (Equal x)`, `(LessThan (InvertFlags x)) => (GreaterThan x)`, … on
  the integer conditions (`1374-1383`): the condition on `InvertFlags x` is the swapped one on `x`,
  whatever `x` (`invertFlags_cond`).
* `(CSEL [cc] x y (InvertFlags cmp)) => (CSEL [arm64Invert(cc)] x y cmp)` and the `CSEL0`,
  `CSETM`, `CSINC`, `CSINV`, `CSNEG` forms (`1352-1357`), split by the integer condition `cc`
  (`GoFV.Rules.Derive.ccSplit`; the lowered binding of a `CCop` auxint is its op, `ccDV`): the
  auxint's condition on `InvertFlags cmp` is the swapped one on `cmp` (`condOn_invert`); an
  auxint that names no op decides nothing, and the source is `poison` (`ccDV_cases`).
-/

namespace GoFV.Proof.Low.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Proof.Rules GoFV.Proof.Low
open GoFV.Rules.Generated.ARM64 GoFV.Rules.Derive

/-- A 64-bit compare's flags are at the flags shape. -/
theorem retypeL_flags_cmp (a b : Val) : (Arm64.cmp a b).retypeL Ty.flags = Arm64.cmp a b := by
  unfold Arm64.cmp
  split
  · rfl
  · split
    · split <;> rfl
    · split <;> rfl
    · split <;> rfl
    · rfl

/-- A 32-bit compare's flags are at the flags shape. -/
theorem retypeL_flags_cmp2w (f : BitVec 32 → BitVec 32 → BitVec 32 × Flags) (as : List Val) :
    (Arm64.cmp2w f as).retypeL Ty.flags = Arm64.cmp2w f as := by
  unfold Arm64.cmp2w
  split
  · split <;> rfl
  · rfl

/-- A 32-bit compare with an immediate: its flags are at the flags shape. -/
theorem retypeL_flags_cmp1w (f : BitVec 32 → BitVec 32 × Flags) (as : List Val) :
    (Arm64.cmp1w f as).retypeL Ty.flags = Arm64.cmp1w f as := by
  unfold Arm64.cmp1w
  split
  · split <;> rfl
  · rfl

theorem invertFlags_poison : invertFlags .poison = .poison := rfl

/-- **`InvertFlags (CMP b a)` is `CMP a b`**, on registers and on pointers alike. -/
theorem invertFlags_cmp (a b : Val) : invertFlags (Arm64.cmp b a) = Arm64.cmp a b := by
  have key : ∀ x y : BitVec 64, invertFlags (Arm64.cmpRes (Arm64.subFlags y x)) =
      Arm64.cmpRes (Arm64.subFlags x y) := fun x y =>
    invertFlags_sub x y (sub_lt64 x y) (sub_lt64 y x)
  have hp : invertFlags (.agg [.poison, .bool false, .poison, .poison, .poison]) =
      .agg [.poison, .bool false, .poison, .poison, .poison] := rfl
  have hP := invertFlags_poison
  unfold Arm64.cmp
  cases ha : Arm64.reg a <;> cases hb : Arm64.reg b
  case some.some x y => exact key x y
  all_goals
    cases a <;> cases b <;> simp only [Arm64.reg] at ha hb <;> simp_all
  all_goals (try split) <;> (try split) <;> simp_all

/-- **`InvertFlags (CMPW b a)` is `CMPW a b`.** -/
theorem invertFlags_cmp2w (a b : Val) :
    invertFlags (Arm64.cmp2w (fun x y => Arm64.subFlags x y) [b, a]) =
      Arm64.cmp2w (fun x y => Arm64.subFlags x y) [a, b] := by
  simp only [Arm64.cmp2w]
  cases ha : Arm64.reg32 a <;> cases hb : Arm64.reg32 b
  case some.some x y => exact invertFlags_sub x y (sub_lt32 x y) (sub_lt32 y x)
  all_goals rfl

/-- `InvertFlags (CMPWconst [k] a)` is `CMPW b a` for `b` a register holding `k`. -/
theorem invertFlags_cmp1w {k : BitVec 32} (a b : Val) (hb : Arm64.reg32 b = some k) :
    invertFlags (Arm64.cmp1w (fun x => Arm64.subFlags x k) [a]) =
      Arm64.cmp2w (fun x y => Arm64.subFlags x y) [b, a] := by
  simp only [Arm64.cmp1w, Arm64.cmp2w, hb]
  cases ha : Arm64.reg32 a
  · rfl
  · exact invertFlags_sub _ _ (sub_lt32 _ _) (sub_lt32 _ _)

theorem cmp_poison_left (b : Val) : Arm64.cmp .poison b = .poison := by
  cases b <;> simp [Arm64.cmp, Arm64.reg]

theorem cmp2w_poison_left (f : BitVec 32 → BitVec 32 → BitVec 32 × Flags) (b : Val) :
    Arm64.cmp2w f [.poison, b] = .poison := by
  simp [Arm64.cmp2w, Arm64.reg32, Arm64.reg]

/-- `CSET` of an integer condition on `InvertFlags f` is `CSET` of the swapped condition on `f`. -/
theorem refines_cset_invert {op op' : Op} {c c' : Cond} (hop : Cond.ofOp op = some c)
    (hop' : Cond.ofOp op' = some c') (hs : c.swapInt = some c') (T T0 : Ty) (f : Val) :
    Refines ((Arm64.cset T op [(invertFlags f).retypeL T0]).retypeL T)
      ((Arm64.cset T op' [f]).retypeL T) := by
  simp only [Arm64.cset, hop, hop', Option.bind_some]
  cases h : c.onVal ((invertFlags f).retypeL T0) with
  | none => rw [retypeL_poison]; exact .poison _
  | some b =>
    rw [invertFlags_cond hs (Mono.onVal_of (retypeL_invertFlags_ref _ _) h)]
    exact Refines.refl _

/-- `ARM64.rules:1003`: `(CMP x y) && canonLessThan(x,y) => (InvertFlags (CMP y x))` -/
theorem r_ARM64_1003_sound : ArmRule.Checked r_ARM64_1003 := by
  left; arm_unfold; arm_norm
  rw [retypeL_flags_cmp, invertFlags_cmp]; exact Refines.refl _

/-- `ARM64.rules:1003`: `(CMPW x y) && canonLessThan(x,y) => (InvertFlags (CMPW y x))` -/
theorem r_ARM64_1003_2_sound : ArmRule.Checked r_ARM64_1003_2 := by
  left; arm_unfold; arm_norm
  rw [retypeL_flags_cmp2w, invertFlags_cmp2w]; exact Refines.refl _

/-- `ARM64.rules:991`: `(CMP (MOVDconst [c]) x) => (InvertFlags (CMPconst [c] x))` -/
theorem r_ARM64_991_sound : ArmRule.Checked r_ARM64_991 := by
  left; arm_unfold; arm_norm
  rw [retypeL_flags_cmp, invertFlags_cmp]
  rcases retypeL_res_wide harg.1 (BitVec.ofInt 64 (e.auxInt [0]).toInt) with h | h <;> rw [h]
  · exact Refines.refl _
  · rw [cmp_poison_left, retypeL_poison]; exact .poison _

/-- `ARM64.rules:993`: `(CMPW (MOVDconst [c]) x) => (InvertFlags (CMPWconst [int32(c)] x))` -/
theorem r_ARM64_993_sound : ArmRule.Checked r_ARM64_993 := by
  left; arm_unfold; arm_norm
  rw [retypeL_flags_cmp1w]
  rcases retypeL_res_w32 harg.1 (BitVec.ofInt 64 (e.auxInt [0]).toInt) with h | h
  · rw [setWidth_ofInt_le (by decide)] at h
    rw [imm32_wrap, invertFlags_cmp1w _ _ h]
    exact Refines.refl _
  · rw [h, cmp2w_poison_left, retypeL_poison]; exact .poison _

/-- `ARM64.rules:1374`: `(Equal (InvertFlags x)) => (Equal x)` -/
theorem r_ARM64_1374_sound : ArmRule.Checked r_ARM64_1374 := by
  left; arm_unfold; arm_norm; exact refines_cset_invert rfl rfl rfl _ _ _

/-- `ARM64.rules:1375`: `(NotEqual (InvertFlags x)) => (NotEqual x)` -/
theorem r_ARM64_1375_sound : ArmRule.Checked r_ARM64_1375 := by
  left; arm_unfold; arm_norm; exact refines_cset_invert rfl rfl rfl _ _ _

/-- `ARM64.rules:1376`: `(LessThan (InvertFlags x)) => (GreaterThan x)` -/
theorem r_ARM64_1376_sound : ArmRule.Checked r_ARM64_1376 := by
  left; arm_unfold; arm_norm; exact refines_cset_invert rfl rfl rfl _ _ _

/-- `ARM64.rules:1377`: `(LessThanU (InvertFlags x)) => (GreaterThanU x)` -/
theorem r_ARM64_1377_sound : ArmRule.Checked r_ARM64_1377 := by
  left; arm_unfold; arm_norm; exact refines_cset_invert rfl rfl rfl _ _ _

/-- `ARM64.rules:1378`: `(GreaterThan (InvertFlags x)) => (LessThan x)` -/
theorem r_ARM64_1378_sound : ArmRule.Checked r_ARM64_1378 := by
  left; arm_unfold; arm_norm; exact refines_cset_invert rfl rfl rfl _ _ _

/-- `ARM64.rules:1379`: `(GreaterThanU (InvertFlags x)) => (LessThanU x)` -/
theorem r_ARM64_1379_sound : ArmRule.Checked r_ARM64_1379 := by
  left; arm_unfold; arm_norm; exact refines_cset_invert rfl rfl rfl _ _ _

/-- `ARM64.rules:1380`: `(LessEqual (InvertFlags x)) => (GreaterEqual x)` -/
theorem r_ARM64_1380_sound : ArmRule.Checked r_ARM64_1380 := by
  left; arm_unfold; arm_norm; exact refines_cset_invert rfl rfl rfl _ _ _

/-- `ARM64.rules:1381`: `(LessEqualU (InvertFlags x)) => (GreaterEqualU x)` -/
theorem r_ARM64_1381_sound : ArmRule.Checked r_ARM64_1381 := by
  left; arm_unfold; arm_norm; exact refines_cset_invert rfl rfl rfl _ _ _

/-- `ARM64.rules:1382`: `(GreaterEqual (InvertFlags x)) => (LessEqual x)` -/
theorem r_ARM64_1382_sound : ArmRule.Checked r_ARM64_1382 := by
  left; arm_unfold; arm_norm; exact refines_cset_invert rfl rfl rfl _ _ _

/-- `ARM64.rules:1383`: `(GreaterEqualU (InvertFlags x)) => (LessEqualU x)` -/
theorem r_ARM64_1383_sound : ArmRule.Checked r_ARM64_1383 := by
  left; arm_unfold; arm_norm; exact refines_cset_invert rfl rfl rfl _ _ _

/-! ## Conditional ops on `InvertFlags`, split by the condition (`Derive.ccSplit`) -/

/-- A `CCop` auxint binds an op (`ccDV`) whose condition it decides as, or is unknown and
decides nothing. -/
theorem ccDV_cases (k : Int64) :
    (∃ o, ccDV k = .op o ∧ Cond.ofAux k = Cond.ofOp o) ∨ (ccDV k = .other ∧ Cond.ofAux k = none) := by
  unfold ccDV Cond.ofAux
  split
  · rename_i o ho
    refine .inl ⟨o, rfl, ?_⟩
    split at ho
    · cases ho
    · rename_i hk; simp only [hk, if_false, ho, Option.bind_some]
  · rename_i ho
    refine .inr ⟨rfl, ?_⟩
    split at ho
    · rename_i hk; simp only [hk, if_true]
    · rename_i hk; simp only [hk, if_false, ho, Option.bind_none]

/-- An integer condition auxint on `InvertFlags f` decides as the swapped one on `f`. -/
theorem condOn_invert {k k' : Int64} {c c' : Cond} (hk : Cond.ofAux k = some c)
    (hk' : Cond.ofAux k' = some c') (hs : c.swapInt = some c') (T0 : Ty) (f : Val) :
    ∀ b, Arm64.condOn k ((invertFlags f).retypeL T0) = some b → Arm64.condOn k' f = some b := by
  intro b h
  simp only [Arm64.condOn, hk, hk', Option.bind_some] at h ⊢
  exact invertFlags_cond hs (Mono.onVal_of (retypeL_invertFlags_ref _ _) h)

theorem refines_csel_cond {ty : Ty} {k k' : Int64} {g : Option (BitVec 64 → BitVec 64)}
    {x y A B : Val} (h : ∀ b, Arm64.condOn k A = some b → Arm64.condOn k' B = some b) (T : Ty) :
    Refines ((Arm64.csel ty k g [x, y, A]).retypeL T) ((Arm64.csel ty k' g [x, y, B]).retypeL T) := by
  simp only [Arm64.csel]
  cases hA : Arm64.condOn k A with
  | none => simp only [retypeL_poison]; exact .poison _
  | some b => rw [h b hA]; exact Refines.refl _

theorem refines_csel0_cond {ty : Ty} {k k' : Int64} {x A B : Val}
    (h : ∀ b, Arm64.condOn k A = some b → Arm64.condOn k' B = some b) (T : Ty) :
    Refines ((Arm64.csel0 ty k [x, A]).retypeL T) ((Arm64.csel0 ty k' [x, B]).retypeL T) := by
  simp only [Arm64.csel0]
  cases hA : Arm64.condOn k A with
  | none => simp only [retypeL_poison]; exact .poison _
  | some b => rw [h b hA]; exact Refines.refl _

theorem refines_csetm_cond {ty : Ty} {k k' : Int64} {A B : Val}
    (h : ∀ b, Arm64.condOn k A = some b → Arm64.condOn k' B = some b) (T : Ty) :
    Refines ((Arm64.csetm ty k [A]).retypeL T) ((Arm64.csetm ty k' [B]).retypeL T) := by
  simp only [Arm64.csetm]
  cases hA : Arm64.condOn k A with
  | none => simp only [retypeL_poison]; exact .poison _
  | some b => rw [h b hA]; exact Refines.refl _

/-- `arm64Invert` on the integer conditions (`Derive.intCondOps`); other ops unchanged. -/
def intSwap : Op → Op
  | .ARM64LessThan => .ARM64GreaterThan
  | .ARM64LessThanU => .ARM64GreaterThanU
  | .ARM64GreaterThan => .ARM64LessThan
  | .ARM64GreaterThanU => .ARM64LessThanU
  | .ARM64LessEqual => .ARM64GreaterEqual
  | .ARM64LessEqualU => .ARM64GreaterEqualU
  | .ARM64GreaterEqual => .ARM64LessEqual
  | .ARM64GreaterEqualU => .ARM64LessEqualU
  | o => o

/-- `ccSplit r_ARM64_1352` on the integer condition op `cc`. -/
def r1352 (cc : Op) : Rule where
  loc := ⟨"ARM64", 1352⟩
  op := .ARM64CSEL
  vars := [⟨"cc", .auxInt, (.named "Op")⟩, ⟨"x", .value, (.named "*Value")⟩, ⟨"y", .value, (.named "*Value")⟩, ⟨"cmp", .value, (.named "*Value")⟩]
  pat := (.op .ARM64CSEL none .any (.bind 0) .any .fixed [(.bind 1), (.bind 2), (.op .ARM64InvertFlags none .any .any .any .fixed [(.bind 3)] false)] false)
  cond := some (ccCond 0 cc)
  block := none
  result := .build
      [{ op := .ARM64CSEL, ty := none, auxInt := some (.op (intSwap cc)), aux := none, args := [.var 1, .var 2, .var 3] }]
  pos := []

theorem ccSplit_1352 : ccSplit r_ARM64_1352 = intCondOps.map r1352 := by rfl

set_option maxRecDepth 100000 in
/-- `ARM64.rules:1352`: `(CSEL [cc] x y (InvertFlags cmp)) => (CSEL [arm64Invert(cc)] x y cmp)`, split by the integer condition (`ccSplit`) -/
theorem r_ARM64_1352_cc_sound : ForallL ArmRule.Checked (ccSplit r_ARM64_1352) := by
  rw [ccSplit_1352]
  simp only [intCondOps, List.map_cons, List.map_nil, ForallL]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  all_goals
    left; arm_unfold; arm_norm
    simp only [ccCond, rule_unfold_ds, sigmaL, Pat.bindsL, Pat.bindssL, auxIntDVL] at hcond
    rcases ccDV_cases (e.auxInt []) with ⟨o, ho, hk⟩ | ⟨ho, hk⟩
    · rw [ho] at hcond
      simp [binE, binDV] at hcond
      subst hcond
      exact refines_csel_cond (condOn_invert (hk.trans rfl) (by rfl) (by rfl) _ _) _
    · exact refines_csel_cond (fun b h => by simp [Arm64.condOn, hk] at h) _

/-- `ccSplit r_ARM64_1353` on the integer condition op `cc`. -/
def r1353 (cc : Op) : Rule where
  loc := ⟨"ARM64", 1353⟩
  op := .ARM64CSEL0
  vars := [⟨"cc", .auxInt, (.named "Op")⟩, ⟨"x", .value, (.named "*Value")⟩, ⟨"cmp", .value, (.named "*Value")⟩]
  pat := (.op .ARM64CSEL0 none .any (.bind 0) .any .fixed [(.bind 1), (.op .ARM64InvertFlags none .any .any .any .fixed [(.bind 2)] false)] false)
  cond := some (ccCond 0 cc)
  block := none
  result := .build
      [{ op := .ARM64CSEL0, ty := none, auxInt := some (.op (intSwap cc)), aux := none, args := [.var 1, .var 2] }]
  pos := []

theorem ccSplit_1353 : ccSplit r_ARM64_1353 = intCondOps.map r1353 := by rfl

set_option maxRecDepth 100000 in
/-- `ARM64.rules:1353`: `(CSEL0 [cc] x (InvertFlags cmp)) => (CSEL0 [arm64Invert(cc)] x cmp)`, split by the integer condition (`ccSplit`) -/
theorem r_ARM64_1353_cc_sound : ForallL ArmRule.Checked (ccSplit r_ARM64_1353) := by
  rw [ccSplit_1353]
  simp only [intCondOps, List.map_cons, List.map_nil, ForallL]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  all_goals
    left; arm_unfold; arm_norm
    simp only [ccCond, rule_unfold_ds, sigmaL, Pat.bindsL, Pat.bindssL, auxIntDVL] at hcond
    rcases ccDV_cases (e.auxInt []) with ⟨o, ho, hk⟩ | ⟨ho, hk⟩
    · rw [ho] at hcond
      simp [binE, binDV] at hcond
      subst hcond
      exact refines_csel0_cond (condOn_invert (hk.trans rfl) (by rfl) (by rfl) _ _) _
    · exact refines_csel0_cond (fun b h => by simp [Arm64.condOn, hk] at h) _

/-- `ccSplit r_ARM64_1354` on the integer condition op `cc`. -/
def r1354 (cc : Op) : Rule where
  loc := ⟨"ARM64", 1354⟩
  op := .ARM64CSETM
  vars := [⟨"cc", .auxInt, (.named "Op")⟩, ⟨"cmp", .value, (.named "*Value")⟩]
  pat := (.op .ARM64CSETM none .any (.bind 0) .any .fixed [(.op .ARM64InvertFlags none .any .any .any .fixed [(.bind 1)] false)] false)
  cond := some (ccCond 0 cc)
  block := none
  result := .build
      [{ op := .ARM64CSETM, ty := none, auxInt := some (.op (intSwap cc)), aux := none, args := [.var 1] }]
  pos := []

theorem ccSplit_1354 : ccSplit r_ARM64_1354 = intCondOps.map r1354 := by rfl

set_option maxRecDepth 100000 in
/-- `ARM64.rules:1354`: `(CSETM [cc] (InvertFlags cmp)) => (CSETM [arm64Invert(cc)] cmp)`, split by the integer condition (`ccSplit`) -/
theorem r_ARM64_1354_cc_sound : ForallL ArmRule.Checked (ccSplit r_ARM64_1354) := by
  rw [ccSplit_1354]
  simp only [intCondOps, List.map_cons, List.map_nil, ForallL]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  all_goals
    left; arm_unfold; arm_norm
    simp only [ccCond, rule_unfold_ds, sigmaL, Pat.bindsL, Pat.bindssL, auxIntDVL] at hcond
    rcases ccDV_cases (e.auxInt []) with ⟨o, ho, hk⟩ | ⟨ho, hk⟩
    · rw [ho] at hcond
      simp [binE, binDV] at hcond
      subst hcond
      exact refines_csetm_cond (condOn_invert (hk.trans rfl) (by rfl) (by rfl) _ _) _
    · exact refines_csetm_cond (fun b h => by simp [Arm64.condOn, hk] at h) _

/-- `ccSplit r_ARM64_1355` on the integer condition op `cc`. -/
def r1355 (cc : Op) : Rule where
  loc := ⟨"ARM64", 1355⟩
  op := .ARM64CSINC
  vars := [⟨"cc", .auxInt, (.named "Op")⟩, ⟨"x", .value, (.named "*Value")⟩, ⟨"y", .value, (.named "*Value")⟩, ⟨"cmp", .value, (.named "*Value")⟩]
  pat := (.op .ARM64CSINC none .any (.bind 0) .any .fixed [(.bind 1), (.bind 2), (.op .ARM64InvertFlags none .any .any .any .fixed [(.bind 3)] false)] false)
  cond := some (ccCond 0 cc)
  block := none
  result := .build
      [{ op := .ARM64CSINC, ty := none, auxInt := some (.op (intSwap cc)), aux := none, args := [.var 1, .var 2, .var 3] }]
  pos := []

theorem ccSplit_1355 : ccSplit r_ARM64_1355 = intCondOps.map r1355 := by rfl

set_option maxRecDepth 100000 in
/-- `ARM64.rules:1355`: `(CSINC [cc] x y (InvertFlags cmp)) => (CSINC [arm64Invert(cc)] x y cmp)`, split by the integer condition (`ccSplit`) -/
theorem r_ARM64_1355_cc_sound : ForallL ArmRule.Checked (ccSplit r_ARM64_1355) := by
  rw [ccSplit_1355]
  simp only [intCondOps, List.map_cons, List.map_nil, ForallL]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  all_goals
    left; arm_unfold; arm_norm
    simp only [ccCond, rule_unfold_ds, sigmaL, Pat.bindsL, Pat.bindssL, auxIntDVL] at hcond
    rcases ccDV_cases (e.auxInt []) with ⟨o, ho, hk⟩ | ⟨ho, hk⟩
    · rw [ho] at hcond
      simp [binE, binDV] at hcond
      subst hcond
      exact refines_csel_cond (condOn_invert (hk.trans rfl) (by rfl) (by rfl) _ _) _
    · exact refines_csel_cond (fun b h => by simp [Arm64.condOn, hk] at h) _

/-- `ccSplit r_ARM64_1356` on the integer condition op `cc`. -/
def r1356 (cc : Op) : Rule where
  loc := ⟨"ARM64", 1356⟩
  op := .ARM64CSINV
  vars := [⟨"cc", .auxInt, (.named "Op")⟩, ⟨"x", .value, (.named "*Value")⟩, ⟨"y", .value, (.named "*Value")⟩, ⟨"cmp", .value, (.named "*Value")⟩]
  pat := (.op .ARM64CSINV none .any (.bind 0) .any .fixed [(.bind 1), (.bind 2), (.op .ARM64InvertFlags none .any .any .any .fixed [(.bind 3)] false)] false)
  cond := some (ccCond 0 cc)
  block := none
  result := .build
      [{ op := .ARM64CSINV, ty := none, auxInt := some (.op (intSwap cc)), aux := none, args := [.var 1, .var 2, .var 3] }]
  pos := []

theorem ccSplit_1356 : ccSplit r_ARM64_1356 = intCondOps.map r1356 := by rfl

set_option maxRecDepth 100000 in
/-- `ARM64.rules:1356`: `(CSINV [cc] x y (InvertFlags cmp)) => (CSINV [arm64Invert(cc)] x y cmp)`, split by the integer condition (`ccSplit`) -/
theorem r_ARM64_1356_cc_sound : ForallL ArmRule.Checked (ccSplit r_ARM64_1356) := by
  rw [ccSplit_1356]
  simp only [intCondOps, List.map_cons, List.map_nil, ForallL]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  all_goals
    left; arm_unfold; arm_norm
    simp only [ccCond, rule_unfold_ds, sigmaL, Pat.bindsL, Pat.bindssL, auxIntDVL] at hcond
    rcases ccDV_cases (e.auxInt []) with ⟨o, ho, hk⟩ | ⟨ho, hk⟩
    · rw [ho] at hcond
      simp [binE, binDV] at hcond
      subst hcond
      exact refines_csel_cond (condOn_invert (hk.trans rfl) (by rfl) (by rfl) _ _) _
    · exact refines_csel_cond (fun b h => by simp [Arm64.condOn, hk] at h) _

/-- `ccSplit r_ARM64_1357` on the integer condition op `cc`. -/
def r1357 (cc : Op) : Rule where
  loc := ⟨"ARM64", 1357⟩
  op := .ARM64CSNEG
  vars := [⟨"cc", .auxInt, (.named "Op")⟩, ⟨"x", .value, (.named "*Value")⟩, ⟨"y", .value, (.named "*Value")⟩, ⟨"cmp", .value, (.named "*Value")⟩]
  pat := (.op .ARM64CSNEG none .any (.bind 0) .any .fixed [(.bind 1), (.bind 2), (.op .ARM64InvertFlags none .any .any .any .fixed [(.bind 3)] false)] false)
  cond := some (ccCond 0 cc)
  block := none
  result := .build
      [{ op := .ARM64CSNEG, ty := none, auxInt := some (.op (intSwap cc)), aux := none, args := [.var 1, .var 2, .var 3] }]
  pos := []

theorem ccSplit_1357 : ccSplit r_ARM64_1357 = intCondOps.map r1357 := by rfl

set_option maxRecDepth 100000 in
/-- `ARM64.rules:1357`: `(CSNEG [cc] x y (InvertFlags cmp)) => (CSNEG [arm64Invert(cc)] x y cmp)`, split by the integer condition (`ccSplit`) -/
theorem r_ARM64_1357_cc_sound : ForallL ArmRule.Checked (ccSplit r_ARM64_1357) := by
  rw [ccSplit_1357]
  simp only [intCondOps, List.map_cons, List.map_nil, ForallL]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
  all_goals
    left; arm_unfold; arm_norm
    simp only [ccCond, rule_unfold_ds, sigmaL, Pat.bindsL, Pat.bindssL, auxIntDVL] at hcond
    rcases ccDV_cases (e.auxInt []) with ⟨o, ho, hk⟩ | ⟨ho, hk⟩
    · rw [ho] at hcond
      simp [binE, binDV] at hcond
      subst hcond
      exact refines_csel_cond (condOn_invert (hk.trans rfl) (by rfl) (by rfl) _ _) _
    · exact refines_csel_cond (fun b h => by simp [Arm64.condOn, hk] at h) _

end GoFV.Proof.Low.Rules
