import GoFV.Proof.Obj.Basic

variable [GoFV.SSA.Sem.Addrs]

/-!
# The smart constructors of `Ex`/`Fl` preserve the meaning (`GoFV/Asm/CheckObjSym.lean`)

Each smart constructor (`Ex.mkAdd`, `Ex.mkAddSub`, …, `Fl.mkAddSub`, `Fl.mkAnds`) evaluates to
the data operation it stands for; `Ex.eval_congr` evaluates an `Ex` alike in two contexts that
agree on what it reads.
-/

namespace GoFV.Proof.Obj

open GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj
open GoFV.SSA.Sem.Arm64 (Shift sext)

private theorem exT_trunc_trunc (sf : Bool) (x : BitVec 64) :
    ProgOp.trunc sf (ProgOp.trunc sf x) = ProgOp.trunc sf x := by
  cases sf <;> simp [ProgOp.trunc, BitVec.setWidth_setWidth_of_le]

private theorem exT_addSub_trunc (sf sub : Bool) (x y : BitVec 64) :
    addSub sf sub (ProgOp.trunc sf x) (ProgOp.trunc sf y) = addSub sf sub x y := by
  cases sf <;> simp [addSub, sizedF, ProgOp.trunc, BitVec.setWidth_setWidth_of_le]

private theorem exT_logical_trunc (sf : Bool) (opc : BitVec 2) (x y : BitVec 64) :
    logical sf opc (ProgOp.trunc sf x) (ProgOp.trunc sf y) = logical sf opc x y := by
  cases sf <;> simp [logical, sizedF, ProgOp.trunc, BitVec.setWidth_setWidth_of_le]

private theorem exT_opnd_trunc (c : Ctx) (sf : Bool) (a : Ex) :
    ProgOp.trunc sf ((Ex.opnd sf a).eval c) = ProgOp.trunc sf (a.eval c) := by
  cases sf
  · simp only [Ex.opnd, Bool.false_eq_true, ↓reduceIte]
    split
    · simp only [Ex.eval, exT_trunc_trunc]
    · rfl
  · rfl

private theorem exT_addSub_opnd (c : Ctx) (sf sub : Bool) (a b : Ex) :
    addSub sf sub ((Ex.opnd sf a).eval c) ((Ex.opnd sf b).eval c) =
      addSub sf sub (a.eval c) (b.eval c) := by
  rw [← exT_addSub_trunc, exT_opnd_trunc, exT_opnd_trunc, exT_addSub_trunc]

private theorem exT_logical_opnd (c : Ctx) (sf : Bool) (opc : BitVec 2) (a b : Ex) :
    logical sf opc ((Ex.opnd sf a).eval c) ((Ex.opnd sf b).eval c) =
      logical sf opc (a.eval c) (b.eval c) := by
  rw [← exT_logical_trunc, exT_opnd_trunc, exT_opnd_trunc, exT_logical_trunc]

private theorem exT_addSub_add (x y : BitVec 64) : (addSub true false x y).1 = x + y := by
  apply BitVec.eq_of_toNat_eq
  simp [addSub, sizedF, GoFV.SSA.Sem.addWithCarry, BitVec.toNat_add]

private theorem exT_addSub_sub (x y : BitVec 64) : (addSub true true x y).1 = x - y := by
  apply BitVec.eq_of_toNat_eq
  simp only [addSub, sizedF, GoFV.SSA.Sem.addWithCarry, ↓reduceIte, BitVec.setWidth_eq,
    BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_not]
  omega

theorem Ex.eval_mkAdd (c : Ctx) (a b : Ex) : (Ex.mkAdd a b).eval c = a.eval c + b.eval c := by
  unfold Ex.mkAdd
  split
  · rfl
  · simp [Ex.eval]
  · split
    · rename_i h; simp [Ex.eval, BitVec.add_assoc, h]
    · simp only [Ex.eval]; rw [BitVec.add_assoc]
  · simp [Ex.eval]
  · rfl

theorem Ex.eval_mkTrunc (c : Ctx) (sf : Bool) (a : Ex) :
    (Ex.mkTrunc sf a).eval c = ProgOp.trunc sf (a.eval c) := by
  cases sf
  · simp only [Ex.mkTrunc, Bool.false_eq_true, ↓reduceIte]
    split
    · rfl
    · simp only [Ex.eval, exT_trunc_trunc]
    · rfl
  · rfl

theorem Ex.eval_mkAddSub (c : Ctx) (sf sub : Bool) (a b : Ex) :
    (Ex.mkAddSub sf sub a b).eval c = (addSub sf sub (a.eval c) (b.eval c)).1 := by
  rw [← exT_addSub_opnd]
  unfold Ex.mkAddSub
  generalize Ex.opnd sf a = a', Ex.opnd sf b = b'
  dsimp only
  split
  · rfl
  · cases sf
    · rfl
    · cases sub
      · simp only [Bool.not_false, ↓reduceIte, Ex.eval_mkAdd, exT_addSub_add]
      · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        split
        · simp [Ex.eval_mkAdd, exT_addSub_sub, Ex.eval, BitVec.sub_eq_add_neg]
        · rfl

theorem Ex.eval_mkLogical (c : Ctx) (sf : Bool) (opc : BitVec 2) (a b : Ex) :
    (Ex.mkLogical sf opc a b).eval c = (logical sf opc (a.eval c) (b.eval c)).1 := by
  rw [← exT_logical_opnd]
  unfold Ex.mkLogical
  generalize Ex.opnd sf a = a', Ex.opnd sf b = b'
  dsimp only
  split
  · rfl
  · split
    · subst opc
      rw [Ex.eval_mkTrunc]
      cases sf <;> simp [logical, sizedF, Ex.eval, ProgOp.trunc]
    · rfl
  · rfl

private theorem exT_shift_zero (k : Shift) {n : Nat} (y : BitVec n) : Shift.apply k y 0 = y := by
  cases k <;> simp [Shift.apply]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp [hi]

theorem Ex.eval_mkShift (c : Ctx) (sf : Bool) (kd : BitVec 2) (amt : Nat) (a : Ex) :
    (Ex.mkShift sf kd amt a).eval c =
      sized sf fun _ e => Shift.apply (shiftOf kd) (e (a.eval c)) amt := by
  unfold Ex.mkShift
  split
  · rfl
  · split
    · subst amt
      rw [Ex.eval_mkTrunc]
      simp only [exT_shift_zero]
      cases sf <;> simp [sized, ProgOp.trunc]
    · rfl

theorem Ex.eval_mkExt (c : Ctx) (opt : BitVec 3) (sh : Nat) (a : Ex) :
    (Ex.mkExt opt sh a).eval c = extendReg (a.eval c) opt sh := by
  unfold Ex.mkExt
  split
  · rfl
  · split
    · rename_i h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hm : GoFV.SSA.Sem.Arm64.mask 64 = BitVec.allOnes 64 := rfl
      have h3 : (3 : BitVec 3).getLsbD 2 = false := by decide
      have h4 : (3 : BitVec 3).toNat % 4 = 3 := by decide
      simp only [extendReg, h3, h4, Bool.false_eq_true, ↓reduceIte, Nat.reducePow, Nat.reduceMul,
        hm, BitVec.and_allOnes, BitVec.shiftLeft_zero]
    · rfl

private theorem exT_bfm_dst (sf : Bool) (opc : BitVec 2) (immr imms : BitVec 6) (d x : BitVec 64)
    (h : ¬opc = 1) : bitfieldMove sf opc immr imms d x = bitfieldMove sf opc immr imms 0 x := by
  have h1 : (opc != 1) = true := by simpa using h
  cases sf <;> simp only [bitfieldMove, sized, h1, ↓reduceIte]

theorem Ex.eval_mkBfm (c : Ctx) (sf : Bool) (opc : BitVec 2) (immr imms : BitVec 6) (d a : Ex) :
    (Ex.mkBfm sf opc immr imms d a).eval c = bitfieldMove sf opc immr imms (d.eval c) (a.eval c) := by
  have : bitfieldMove sf opc immr imms (d.eval c) (a.eval c) =
      bitfieldMove sf opc immr imms ((if opc = 1 then d else .k 0).eval c) (a.eval c) := by
    split
    · rfl
    · rename_i h; simp only [Ex.eval]; exact exT_bfm_dst sf opc immr imms _ _ h
  rw [this]
  unfold Ex.mkBfm
  generalize (if opc = 1 then d else .k 0) = d'
  dsimp only
  split <;> rfl

theorem Ex.eval_mkSext (c : Ctx) (n : Nat) (a : Ex) : (Ex.mkSext n a).eval c = sext n (a.eval c) := by
  unfold Ex.mkSext
  split <;> rfl

private theorem exT_opndK_trunc (c : Ctx) (sf : Bool) (a : Ex) :
    ProgOp.trunc sf ((Ex.opndK sf a).eval c) = ProgOp.trunc sf (a.eval c) := by
  rw [← exT_opnd_trunc c sf a]
  unfold Ex.opndK
  split
  · rename_i v hv; rw [hv]; simp only [Ex.eval, exT_trunc_trunc]
  · rfl

theorem dp3_trunc (sf o0 : Bool) (a x y : BitVec 64) :
    dp3Op sf 0 o0 (ProgOp.trunc sf a) (ProgOp.trunc sf x) (ProgOp.trunc sf y) = dp3Op sf 0 o0 a x y := by
  cases sf <;> simp [dp3Op, sized, ProgOp.trunc, BitVec.setWidth_setWidth_of_le]

theorem Ex.eval_mkDp3 (c : Ctx) (sf : Bool) (op31 : BitVec 3) (o0 : Bool) (a x y : Ex) :
    (Ex.mkDp3 sf op31 o0 a x y).eval c = dp3Op sf op31 o0 (a.eval c) (x.eval c) (y.eval c) := by
  unfold Ex.mkDp3
  split
  · rename_i h
    subst h
    simp only [Ex.eval]
    rw [← dp3_trunc, exT_opndK_trunc, exT_opndK_trunc, exT_opndK_trunc, dp3_trunc]
  · rfl

private theorem exT_awc_neg {w : Nat} (hw : 0 < w) (x y : BitVec w) (h0 : y ≠ 0)
    (hm : y ≠ BitVec.intMin w) :
    (GoFV.SSA.Sem.addWithCarry x (-y) false).2 = (GoFV.SSA.Sem.addWithCarry x (~~~y) true).2 := by
  have hy0 : y.toNat ≠ 0 := fun h => h0 (BitVec.eq_of_toNat_eq (by simp [h]))
  have hN : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← Nat.pow_succ']; congr 1; omega
  have hlt := y.isLt
  have hneg : (-y).toNat = 2 ^ w - y.toNat := by
    rw [BitVec.toNat_neg, Nat.mod_eq_of_lt (by omega)]
  have hnot := BitVec.toNat_not (x := y)
  have hu : x.toNat + (-y).toNat = x.toNat + (~~~y).toNat + 1 := by omega
  have hs' : x.toInt + (-y).toInt = x.toInt + (~~~y).toInt + 1 := by
    rw [BitVec.toInt_neg_of_ne_intMin hm, BitVec.toInt_eq_toNat_cond (~~~y),
      BitVec.toInt_eq_toNat_cond y, hnot]
    generalize 2 ^ (w - 1) = H at *
    rw [hN] at hlt ⊢
    split <;> split <;> omega
  have hs :
      x.toInt + (-y).toInt + ((0 : Nat) : Int) = x.toInt + (~~~y).toInt + ((1 : Nat) : Int) := by
    omega
  simp only [GoFV.SSA.Sem.addWithCarry, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, hu, hs]

private theorem exT_flags_sub (sf : Bool) (x y : BitVec 64) (h0 : ProgOp.trunc sf y ≠ 0)
    (hm : ProgOp.trunc sf y ≠ ProgOp.trunc sf (BitVec.ofNat 64 (if sf then 2 ^ 63 else 2 ^ 31))) :
    (addSub sf false x (ProgOp.trunc sf (-y))).2 = (addSub sf true x y).2 := by
  cases sf
  · simp only [addSub, sizedF, ProgOp.trunc, Bool.false_eq_true, ↓reduceIte] at h0 hm ⊢
    rw [BitVec.setWidth_setWidth_of_le _ (by decide), BitVec.setWidth_neg_of_le (by decide)]
    apply exT_awc_neg (by decide)
    · intro h; apply h0; rw [h]; rfl
    · intro h; apply hm; rw [h]; decide
  · simp only [addSub, sizedF, ProgOp.trunc, ↓reduceIte, BitVec.setWidth_eq] at h0 hm ⊢
    apply exT_awc_neg (by decide) _ _ h0
    intro h; apply hm; rw [h]; decide

theorem Fl.eval_mkAddSub (c : Ctx) (sf sub : Bool) (a b : Ex) :
    (Fl.mkAddSub sf sub a b).eval c = (addSub sf sub (a.eval c) (b.eval c)).2 := by
  rw [← exT_addSub_opnd]
  unfold Fl.mkAddSub
  generalize Ex.opnd sf a = a', Ex.opnd sf b = b'
  dsimp only
  split
  · rename_i y
    by_cases h : ProgOp.trunc sf y ≠ 0 ∧
        ProgOp.trunc sf y ≠ ProgOp.trunc sf (BitVec.ofNat 64 (if sf then 2 ^ 63 else 2 ^ 31))
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h)]
      exact exT_flags_sub sf _ _ h.1 h.2
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h)]; rfl
  · simp only [Fl.eval, Ex.eval]
    rw [← exT_addSub_trunc sf false _ (ProgOp.trunc sf _), exT_trunc_trunc,
      exT_addSub_trunc]
  · rfl

theorem Fl.eval_mkAnds (c : Ctx) (sf : Bool) (a b : Ex) :
    (Fl.mkAnds sf a b).eval c = (logical sf 3 (a.eval c) (b.eval c)).2 := by
  simp only [Fl.mkAnds, Fl.eval, exT_logical_opnd]

/-- An `Ex` evaluates alike in two contexts with the same symbols, `SP`, flags, memory and vector
registers that agree on the general registers it reads. -/
theorem Ex.eval_congr {c c' : Ctx} (hsym : c.sym = c'.sym) (hsp : c.s.sp = c'.s.sp)
    (hmem : c.s.mem = c'.s.mem) (hfl : c.s.nzcv = c'.s.nzcv) (hv : c.s.v = c'.s.v) :
    ∀ e : Ex, (∀ r, e.reads r = true → c.s.x (BitVec.ofNat 5 r) = c'.s.x (BitVec.ofNat 5 r)) →
      e.eval c = e.eval c' := by
  intro e
  induction e with
  | x r => intro he; exact he r (by simp [Ex.reads])
  | sp => intro _; exact hsp
  | k => intro _; rfl
  | sym n => intro _; simp only [Ex.eval, hsym]
  | ld n a ih => intro he; simp only [Ex.eval]; rw [ih he, hmem]
  | add a b iha ihb =>
    intro he; simp only [Ex.eval]
    rw [iha (fun r h => he r (by simp [Ex.reads, h])),
      ihb (fun r h => he r (by simp [Ex.reads, h]))]
  | addSub sf sub a b iha ihb =>
    intro he; simp only [Ex.eval]
    rw [iha (fun r h => he r (by simp [Ex.reads, h])),
      ihb (fun r h => he r (by simp [Ex.reads, h]))]
  | logical sf opc a b iha ihb =>
    intro he; simp only [Ex.eval]
    rw [iha (fun r h => he r (by simp [Ex.reads, h])),
      ihb (fun r h => he r (by simp [Ex.reads, h]))]
  | shift sf kd amt a ih => intro he; simp only [Ex.eval]; rw [ih he]
  | ext opt sh a ih => intro he; simp only [Ex.eval]; rw [ih he]
  | bfm sf opc immr imms a b iha ihb =>
    intro he; simp only [Ex.eval]
    rw [iha (fun r h => he r (by simp [Ex.reads, h])),
      ihb (fun r h => he r (by simp [Ex.reads, h]))]
  | lo32 a ih => intro he; simp only [Ex.eval]; rw [ih he]
  | sext n a ih => intro he; simp only [Ex.eval]; rw [ih he]
  | page a ih => intro he; simp only [Ex.eval]; rw [ih he]
  | dp1 sf opc a ih => intro he; simp only [Ex.eval]; rw [ih he]
  | dp3 sf op31 o0 a b d iha ihb ihd =>
    intro he; simp only [Ex.eval]
    rw [iha (fun r h => he r (by simp [Ex.reads, h])),
      ihb (fun r h => he r (by simp [Ex.reads, h])),
      ihd (fun r h => he r (by simp [Ex.reads, h]))]
  | csel sf op op2 cc a b iha ihb =>
    intro he; simp only [Ex.eval]
    rw [iha (fun r h => he r (by simp [Ex.reads, h])),
      ihb (fun r h => he r (by simp [Ex.reads, h])), hfl]
  | vlo ft r => intro _; simp only [Ex.eval, hv]
  | fcvtz ft u m r => intro _; simp only [Ex.eval, hv]

/-- `Ex.eval_congr` for a `VEx`. -/
theorem VEx.eval_congr {c c' : Ctx} (hsym : c.sym = c'.sym) (hsp : c.s.sp = c'.s.sp)
    (hmem : c.s.mem = c'.s.mem) (hfl : c.s.nzcv = c'.s.nzcv) (hv : c.s.v = c'.s.v) :
    ∀ e : VEx, (∀ r, e.reads r = true → c.s.x (BitVec.ofNat 5 r) = c'.s.x (BitVec.ofNat 5 r)) →
      e.eval c = e.eval c' := by
  intro e
  have ex := Ex.eval_congr hsym hsp hmem hfl hv
  induction e with
  | v r => intro _; simp only [VEx.eval, hv]
  | k => intro _; rfl
  | ofX w a => intro he; simp only [VEx.eval]; rw [ex a he]
  | ld n a => intro he; simp only [VEx.eval]; rw [ex a he, hmem]
  | fp1 ft opc a ih => intro he; simp only [VEx.eval]; rw [ih he]
  | fp2 ft opc a b iha ihb =>
    intro he; simp only [VEx.eval]
    rw [iha (fun r h => he r (by simp [VEx.reads, h])),
      ihb (fun r h => he r (by simp [VEx.reads, h]))]
  | fp3 ft o1 o0 a n m iha ihn ihm =>
    intro he; simp only [VEx.eval]
    rw [iha (fun r h => he r (by simp [VEx.reads, h])),
      ihn (fun r h => he r (by simp [VEx.reads, h])),
      ihm (fun r h => he r (by simp [VEx.reads, h]))]
  | fcsel ft cc a b iha ihb =>
    intro he; simp only [VEx.eval]
    rw [iha (fun r h => he r (by simp [VEx.reads, h])),
      ihb (fun r h => he r (by simp [VEx.reads, h])), hfl]
  | cvtf ft m u a => intro he; simp only [VEx.eval]; rw [ex a he]

/-- `Fl.eval_congr`, with the flags before the Prog equal. -/
theorem Fl.eval_congr {c c' : Ctx} (hsym : c.sym = c'.sym) (hsp : c.s.sp = c'.s.sp)
    (hmem : c.s.mem = c'.s.mem) (hfl : c.s.nzcv = c'.s.nzcv) (hv : c.s.v = c'.s.v) :
    ∀ f : Fl, (∀ r, f.reads r = true → c.s.x (BitVec.ofNat 5 r) = c'.s.x (BitVec.ofNat 5 r)) →
      f.eval c = f.eval c' := by
  intro f hf
  cases f with
  | init => exact hfl
  | addSub sf sub a b =>
    simp only [Fl.eval]
    rw [Ex.eval_congr hsym hsp hmem hfl hv a (fun r h => hf r (by simp [Fl.reads, h])),
      Ex.eval_congr hsym hsp hmem hfl hv b (fun r h => hf r (by simp [Fl.reads, h]))]
  | ands sf a b =>
    simp only [Fl.eval]
    rw [Ex.eval_congr hsym hsp hmem hfl hv a (fun r h => hf r (by simp [Fl.reads, h])),
      Ex.eval_congr hsym hsp hmem hfl hv b (fun r h => hf r (by simp [Fl.reads, h]))]
  | fcmp ft a b =>
    simp only [Fl.eval]
    rw [VEx.eval_congr hsym hsp hmem hfl hv a (fun r h => hf r (by simp [Fl.reads, h])),
      VEx.eval_congr hsym hsp hmem hfl hv b (fun r h => hf r (by simp [Fl.reads, h]))]

end GoFV.Proof.Obj
