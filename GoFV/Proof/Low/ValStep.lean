import GoFV.Proof.Low.ValRule

/-!
# One lowering rule event refines the denotations (issue #385)

The lowered counterpart of `GoFV/Proof/Pass/RewriteTermStep.lean`: in lowered mode (`denL true`),
`RuleFactsL.step` shows that on a set closed under arguments every value's denotation after a
validated rule event refines the one before (fuel multiplied by `stepK r`), from
`ArmRule.Sound1 r` at the matched instance (`RuleFactsL.top`). Also the copy lemmas of
`RewriteTermDen.lean` at the lowered shapes (`copyReachL_den`).
-/

namespace GoFV.Proof.Low.Val

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Opt.RewriteCheck GoFV.Opt.LowerCheck GoFV.Proof.Term
open GoFV.Proof.Low
open GoFV.Proof.Pass.Rewrite (putAll get?_putAll_not get?_putAll_mem get?_put defIds resLen stepK
  Good good_of_flat good_mono evalE_good evalE_erase InI DefClosed DefClosed.arg refinesList_idx
  wf_of cons_of cond_of toList_of_size_one isOpPat)
open GoFV.Proof.Rules (Path PEnv DV Oracle evalE)

/-! ## Lowered denotations -/

section Den

variable {D : ID → Option Value} {tabs : Tables} {ρ : ID → Val}

theorem shapeL_of {a : ID} {y : Value} (h : D a = some y) : shapeL true D tabs a = shpL tabs y.type := by
  simp only [shapeL, h, Option.map_some, Option.getD_some]; rfl

/-- Under `TypedL`, the lowered denotation of a defined value is fixed by `retypeL` at its shape. -/
theorem den_retypeL (hT : TypedL true D tabs ρ) :
    ∀ (k : Nat) (a : ID), (D a).isSome = true →
      (denL true D tabs ρ k a).retypeL (shapeL true D tabs a) = denL true D tabs ρ k a
  | 0, _, _ => retypeL_poison _
  | k + 1, a, hd => by
    by_cases ht : IsTermL tabs D a
    · obtain ⟨v, hv, hop⟩ := ht
      rw [denT_succ hv hop, shapeL_of hv]
      exact retypeL_idem _ _
    · rw [denL_succ_atom ht]; exact hT a ht hd

theorem den_hasTyL (hT : TypedL true D tabs ρ) (k : Nat) {a : ID} {y : Value} (hy : D a = some y) :
    (denL true D tabs ρ k a).hasTy (shpL tabs y.type) = true := by
  rw [← den_retypeL hT k a (by rw [hy]; rfl), shapeL_of hy]
  exact retypeL_hasTy _ _

theorem widen_ptr_elem (e e' : Option Nat) (v : Val) : v.widen (.ptr e) = v.widen (.ptr e') := by
  cases v <;> rfl

theorem retypeL_ptr_elem (e e' : Option Nat) (v : Val) :
    v.retypeL (.ptr e) = v.retypeL (.ptr e') := by
  simp only [Val.retypeL, widen_ptr_elem e e' v]
  exact GoFV.Proof.Pass.Rewrite.retype_ptr_elem e e' _

/-- A `Copy` of a compatible shape is the identity on a value fixed at its argument's shape. -/
theorem retypeL_copyCompat {s t : Ty} (h : copyCompatL s t = true) {z : Val} (hz : z.retypeL t = z) :
    z.retypeL s = z := by
  unfold copyCompatL copyCompat at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · rw [GoFV.Proof.Pass.Rewrite.tyEq_sound h, hz]
  · simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases s <;> simp at h1
    cases t <;> simp at h2
    rename_i e e'
    rw [retypeL_ptr_elem e e', hz]

theorem opValL_copy (tabs : Tables) (ty : Ty) (ai : Int64) (ax : Option AuxRef) (w : Val) :
    opValL tabs .Copy ty ai ax [w] = w := by
  have hg : Op.Copy.generic = true := by decide
  simp only [opValL, hg, ite_true]
  rw [GoFV.Proof.Rules.opVal_pure (by decide)]
  rfl

/-- The lowered denotation of a `Copy` of a compatible shape is its argument's, one fuel lower. -/
theorem den_copyL (hT : TypedL true D tabs ρ) {a : ID} {x y : Value} (hx : D a = some x)
    (hop : x.op = .Copy) (hsz : x.args.size = 1) (hy : D x.args[0]! = some y)
    (hc : copyCompatL (shpL tabs x.type) (shpL tabs y.type) = true) (k : Nat) :
    denL true D tabs ρ (k + 1) a = denL true D tabs ρ k x.args[0]! := by
  rw [denT_succ hx (termVL_of_copy hop), toList_of_size_one hsz, hop]
  simp only [List.map_cons, List.map_nil, opValL_copy]
  apply retypeL_copyCompat hc
  rw [← shapeL_of (tabs := tabs) hy]
  exact den_retypeL hT k _ (by rw [hy]; rfl)

end Den

/-- A value reached through compatible copies has a larger lowered denotation at the same fuel. -/
theorem copyReachL_den {M : Defs} {tabs : Tables} {ρ : ID → Val} (hT : TypedL true M.get? tabs ρ) :
    ∀ (N : Nat) (a w : ID), copyReachL tabs M N a w = true →
      ∀ k, Sem.Refines (denL true M.get? tabs ρ k a) (denL true M.get? tabs ρ k w)
  | 0, a, w, h, k => by
    simp only [copyReachL, beq_iff_eq] at h; subst h; exact Sem.Refines.refl _
  | N + 1, a, w, h, k => by
    simp only [copyReachL, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact Sem.Refines.refl _
    · cases hx : M.get? a with
      | none => rw [hx] at h; cases h
      | some x =>
        rw [hx] at h
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨⟨hop, hsz⟩, hy⟩, hr⟩ := h
        cases hy' : M.get? x.args[0]! with
        | none => rw [hy'] at hy; cases hy
        | some y =>
          rw [hy'] at hy
          cases k with
          | zero => exact .poison _
          | succ k =>
            rw [den_copyL hT hx hop hsz hy' hy k]
            exact Sem.Refines.trans (denL_fuel_mono _ _ _ _ k (k + 1) _ (by omega))
              (copyReachL_den hT N _ w hr (k + 1))

theorem copyReachL_closed {tabs : Tables} {M : Defs} {C : ID → Prop} (hC : DefClosed M C) :
    ∀ (N : Nat) (a w : ID), copyReachL tabs M N a w = true → C a → C w
  | 0, a, w, h, ha => by simp only [copyReachL, beq_iff_eq] at h; exact h ▸ ha
  | N + 1, a, w, h, ha => by
    simp only [copyReachL, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact ha
    · cases hx : M.get? a with
      | none => rw [hx] at h; cases h
      | some x =>
        rw [hx] at h
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨⟨-, hsz⟩, -⟩, hr⟩ := h
        obtain ⟨m, hm, hargs⟩ := hC a ha
        rw [hx] at hm; cases hm
        exact copyReachL_closed hC N _ w hr (hargs _ (Array.mem_toList_iff.1 (by
          rw [toList_of_size_one hsz]; exact List.mem_singleton_self _)))

/-- Zero-extending to `w ≥ n` bits, then to 64, is zero-extending to 64. -/
theorem setWidth_setWidth_wide {n : Nat} (w m : Nat) (hn : n ≤ w) (x : BitVec n) :
    (x.setWidth w).setWidth m = x.setWidth m := by
  ext i hi
  simp only [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_setWidth]
  by_cases h : i < w
  · simp [h]
  · have : x.getLsbD i = false := BitVec.getLsbD_of_ge x i (by omega)
    simp [h, this]

/-- A narrowing to 32 bits keeps the `W` register. -/
theorem reg32_retypeL_w32 {X : Val} {x : BitVec 32}
    (h : Arm64.reg32 (X.retypeL (.int .w32)) = some x) : Arm64.reg32 X = some x := by
  cases X with
  | int w v =>
    cases w <;> simp_all [Val.retypeL, Val.widen, Val.retype, Arm64.reg32, Arm64.reg, Width.bits,
      setWidth_setWidth_wide, BitVec.setWidth_setWidth_of_le]
  | bool b => cases b <;> simp_all [Val.retypeL, Val.widen, Val.retype, Arm64.reg32, Arm64.reg]
  | _ => simp [Val.retypeL, Val.widen, Val.retype, Arm64.reg32, Arm64.reg] at h

/-- A narrowing `Copy` in lowered mode: the copied value at the copy's shape. -/
theorem copy_den {tabs : Tables} {M : Defs} {ρ : ID → Val} {n : Nat} {a : ID} {c : Value}
    {w : Width} (hc : M.get? a = some c) (hcop : c.op = .Copy) (hcsz : c.args.size = 1)
    (hsh : shpL tabs c.type = .int w) :
    denL true M.get? tabs ρ (n + 1) a = (denL true M.get? tabs ρ n c.args[0]!).retypeL (.int w) := by
  rw [denT_succ hc (termVL_of_copy hcop), toList_of_size_one hcsz, hcop, hsh]
  simp only [List.map_cons, List.map_nil, opValL_copy]

/-- What `truncFromL` says. -/
theorem truncFromL_cases {tabs : Tables} {M : Defs} {n k : Nat} {a a' : ID}
    (h : truncFromL tabs M n k a a' = true) :
    ∃ c w, M.get? a = some c ∧ c.op = .Copy ∧ c.args.size = 1 ∧
      shpL tabs c.type = .int w ∧ k ≤ w.bits ∧ w ≠ .w64 ∧
      narrowReachL tabs M n w.bits c.args[0]! a' = true := by
  unfold truncFromL at h
  split at h
  · rename_i c hc
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hop, hsz⟩, hsh⟩ := h
    split at hsh
    · rename_i w hw
      simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hsh
      exact ⟨c, w, hc, hop, hsz, hw, hsh.1.1, hsh.1.2, hsh.2⟩
    · cases hsh
  · cases h

theorem narrowReachL_closed {tabs : Tables} {M : Defs} {C : ID → Prop} (hC : DefClosed M C) :
    ∀ (N k : Nat) (a w : ID), narrowReachL tabs M N k a w = true → C a → C w
  | 0, _, a, w, h, ha => by simp only [narrowReachL, beq_iff_eq] at h; exact h ▸ ha
  | N + 1, k, a, w, h, ha => by
    simp only [narrowReachL, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact ha
    · cases hx : M.get? a with
      | none => rw [hx] at h; cases h
      | some x =>
        rw [hx] at h
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨⟨-, hsz⟩, -⟩, hr⟩ := h
        obtain ⟨m, hm, hargs⟩ := hC a ha
        rw [hx] at hm; cases hm
        exact narrowReachL_closed hC N k _ w hr (hargs _ (Array.mem_toList_iff.1 (by
          rw [toList_of_size_one hsz]; exact List.mem_singleton_self _)))

/-- The source of a narrowing `Copy` of a value of `C` is in `C`. -/
theorem truncFrom_closed {tabs : Tables} {M : Defs} {C : ID → Prop} (hC : DefClosed M C)
    {N k : Nat} {a c' : ID} (h : truncFromL tabs M N k a c' = true) (ha : C a) : C c' := by
  obtain ⟨c, w, hc, -, hcsz, -, -, -, hcr⟩ := truncFromL_cases h
  obtain ⟨m, hm, hargs⟩ := hC a ha
  rw [hc] at hm; cases hm
  exact narrowReachL_closed hC N _ _ c' hcr (hargs _ (Array.mem_toList_iff.1 (by
    rw [toList_of_size_one hcsz]; exact List.mem_singleton_self _)))

/-! ## An extension's argument through a narrowing copy (`truncReachL`) -/

/-- The low `k ≤ w` bits of a `w`-bit truncation are the value's. -/
theorem and_mask_setWidth {n : Nat} (k w : Nat) (hk : k ≤ w) (x : BitVec n) :
    (x.setWidth w).setWidth 64 &&& Arm64.mask k = x.setWidth 64 &&& Arm64.mask k := by
  ext i hi
  simp only [BitVec.getElem_and, BitVec.getElem_setWidth, Arm64.mask, ← BitVec.getLsbD_eq_getElem]
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat,
    Nat.testBit_two_pow_sub_one]
  by_cases hik : i < k
  · have : i < w := by omega
    simp [this, hik]
  · simp [hik]

/-- An extension of the low `k ≤ w` bits reads the same bits of a `w`-bit truncation. -/
theorem ext_setWidth {n : Nat} (s : Bool) (k w : Nat) (hk : k ≤ w) (x : BitVec n) :
    Arm64.ext s k ((x.setWidth w).setWidth 64) = Arm64.ext s k (x.setWidth 64) := by
  unfold Arm64.ext Arm64.sext
  rw [and_mask_setWidth k w hk]

/-- **An extension of the low `k` bits of a register refines through a narrowing to `w ≥ k`
bits** (`Val.retypeL` at `int w`, `w < 64`: the value's low `w` bits, `poison` for a pointer). -/
theorem op1_ext_retypeL (s : Bool) (k : Nat) {w : Width} (hk : k ≤ w.bits) (hw : w ≠ .w64)
    (ty : Ty) (B : Val) :
    Sem.Refines (Arm64.op1 ty (Arm64.ext s k) [B.retypeL (.int w)])
      (Arm64.op1 ty (Arm64.ext s k) [B]) := by
  cases B with
  | int w' x =>
    by_cases hlt : w'.bits < w.bits
    · have : (Val.int w' x).retypeL (.int w) = .int w (x.setWidth w.bits) := by
        unfold Val.retypeL Val.widen
        rw [if_pos hlt]
        unfold Val.retype
        rw [if_pos (Nat.le_refl _), BitVec.setWidth_eq]
      rw [this]
      simp only [Arm64.op1, Arm64.reg]
      rw [setWidth_setWidth_wide _ _ (by omega)]
      exact Sem.Refines.refl _
    · have hle : w.bits ≤ w'.bits := by omega
      have : (Val.int w' x).retypeL (.int w) = .int w (x.setWidth w.bits) := by
        unfold Val.retypeL Val.widen
        rw [if_neg hlt]
        unfold Val.retype
        rw [if_pos hle]
      rw [this]
      simp only [Arm64.op1, Arm64.reg]
      rw [ext_setWidth s k w.bits hk]
      exact Sem.Refines.refl _
  | bool b =>
    have : (Val.bool b).retypeL (.int w) = .int w (if b then 1 else 0) := by
      simp [Val.retypeL, Val.widen, Val.retype]
    rw [this]
    cases w <;> cases b <;> first | exact absurd rfl hw | exact Sem.Refines.refl _
  | ptr p =>
    have : (Val.ptr p).retypeL (.int w) = .poison := by
      cases w <;> simp_all [Val.retypeL, Val.widen, Val.retype]
    rw [this]; exact .poison _
  | _ => simp [Val.retypeL, Val.widen, Val.retype, Arm64.op1, Arm64.reg]; exact .poison _

theorem extReadW_mem {o : Op} {k : Nat} (h : extReadW o = some k) :
    (o = .ARM64MOVBreg ∧ k = 8) ∨ (o = .ARM64MOVBUreg ∧ k = 8) ∨ (o = .ARM64MOVHreg ∧ k = 16) ∨
      (o = .ARM64MOVHUreg ∧ k = 16) ∨ (o = .ARM64MOVWreg ∧ k = 32) ∨ (o = .ARM64MOVWUreg ∧ k = 32) := by
  unfold extReadW at h
  split at h <;> simp_all

theorem extReadW_cases {o : Op} {k : Nat} (h : extReadW o = some k) :
    ∃ s, (∀ ty ai (ax : Option AuxRef) args,
        Arm64.evalPure o ty ai ax args = Arm64.op1 ty (Arm64.ext s k) args) ∧
      o.generic = false ∧ (o == .ARM64MOVDaddr) = false ∧ ldOp? o = none ∧
      (GoFV.Opt.LowerTerm.armTerm o && !GoFV.Opt.LowerTerm.actOp o && !isRoot o) = true := by
  rcases extReadW_mem h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩
  · exact ⟨true, fun _ _ _ _ => rfl, by decide, by decide, by decide, by decide⟩
  · exact ⟨false, fun _ _ _ _ => rfl, by decide, by decide, by decide, by decide⟩
  · exact ⟨true, fun _ _ _ _ => rfl, by decide, by decide, by decide, by decide⟩
  · exact ⟨false, fun _ _ _ _ => rfl, by decide, by decide, by decide, by decide⟩
  · exact ⟨true, fun _ _ _ _ => rfl, by decide, by decide, by decide, by decide⟩
  · exact ⟨false, fun _ _ _ _ => rfl, by decide, by decide, by decide, by decide⟩

/-- An extension is a term (`armTerm`), whose `opValL` is `Arm64.ext` of its register. -/
theorem opValL_ext {o : Op} {k : Nat} (h : extReadW o = some k) :
    ∃ s, ∀ tabs ty ai ax args, opValL tabs o ty ai ax args = Arm64.op1 ty (Arm64.ext s k) args := by
  obtain ⟨s, he, hg, hm, hl, -⟩ := extReadW_cases h
  exact ⟨s, fun tabs ty ai ax args => by
    simp only [opValL, hg, hm, hl, Bool.false_eq_true, ite_false]; exact he ty ai ax args⟩

theorem termVL_ext {tabs : Tables} {v : Value} {k : Nat} (h : extReadW v.op = some k) :
    termVL tabs v = true := by
  obtain ⟨-, -, hg, hm, hl, ht⟩ := extReadW_cases h
  have hact : GoFV.Opt.LowerTerm.actOp v.op = false := by
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at ht; exact ht.1.2
  simp only [termVL, hg, hm, hl, pureActOp_of_act hact, Option.isSome_none, Bool.false_eq_true,
    ite_false, ht]

theorem w32Op_mem {o : Op} (h : w32Op o = true) :
    o = .ARM64MULW ∨ o = .ARM64MNEGW ∨ o = .ARM64DIVW ∨ o = .ARM64UDIVW ∨ o = .ARM64MODW ∨
      o = .ARM64UMODW ∨ o = .ARM64RORW ∨ o = .ARM64RORWconst ∨ o = .ARM64EXTRWconst ∨
      o = .ARM64CLZW ∨ o = .ARM64RBITW ∨ o = .ARM64REVW ∨ o = .ARM64REV16W ∨ o = .ARM64CMPW ∨
      o = .ARM64CMPWconst ∨ o = .ARM64CMNW ∨ o = .ARM64CMNWconst ∨ o = .ARM64TSTW ∨
      o = .ARM64TSTWconst := by
  unfold w32Op at h
  split at h <;> simp_all

/-- A `W` op is no extension and a term (`armTerm`) whose `opValL` is `Arm64.evalPure`. -/
theorem w32Op_cases {o : Op} (h : w32Op o = true) :
    extReadW o = none ∧ o.generic = false ∧ (o == .ARM64MOVDaddr) = false ∧ ldOp? o = none ∧
      (GoFV.Opt.LowerTerm.armTerm o && !GoFV.Opt.LowerTerm.actOp o && !isRoot o) = true := by
  rcases w32Op_mem h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨rfl, by decide, by decide, by decide, by decide⟩

theorem opValL_w32 {o : Op} (h : w32Op o = true) (tabs : Tables) (ty : Ty) (ai : Int64)
    (ax : Option AuxRef) (args : List Val) :
    opValL tabs o ty ai ax args = Arm64.evalPure o ty ai ax args := by
  obtain ⟨-, hg, hm, hl, -⟩ := w32Op_cases h
  simp only [opValL, hg, hm, hl, Bool.false_eq_true, ite_false]

theorem narrowReadW_cases {o : Op} {ai : Int64} {i k : Nat} (h : narrowReadW o ai i = some k) :
    (o = .ARM64TSTWconst ∧ i = 0 ∧ k = tstReadW ai) ∨ (extReadW o = some k ∧ i = 0) ∨
      (w32Op o = true ∧ o ≠ .ARM64TSTWconst ∧ k = 32) := by
  unfold narrowReadW at h
  by_cases ht : o = .ARM64TSTWconst
  · subst ht
    by_cases hi : i = 0
    · subst hi
      simp only [beq_self_eq_true, ite_true, Option.some.injEq] at h
      exact .inl ⟨rfl, rfl, h.symm⟩
    · simp [hi] at h
  · have hb : (o == .ARM64TSTWconst) = false := by simpa using ht
    simp only [hb, Bool.false_eq_true, ite_false] at h
    right
    cases he : extReadW o with
    | some k' =>
      rw [he] at h
      by_cases hi : i = 0
      · subst hi; cases h; exact .inl ⟨rfl, rfl⟩
      · simp [hi] at h
    | none =>
      rw [he] at h
      cases hw : w32Op o
      · simp [hw] at h
      · simp only [hw, ite_true, Option.some.injEq] at h
        exact .inr ⟨rfl, ht, h.symm⟩

/-- An op reading narrow bits of an argument (`narrowReadW`) is a term. -/
theorem termVL_narrow {tabs : Tables} {v : Value} {ai : Int64} {i k : Nat}
    (h : narrowReadW v.op ai i = some k) : termVL tabs v = true := by
  have hw : extReadW v.op = some k ∨ w32Op v.op = true := by
    rcases narrowReadW_cases h with ⟨ht, -, -⟩ | ⟨hk, -⟩ | ⟨hw, -⟩
    · rw [ht]; exact .inr rfl
    · exact .inl hk
    · exact .inr hw
  rcases hw with hk | hw
  · exact termVL_ext hk
  · obtain ⟨-, hg, hm, hl, ht⟩ := w32Op_cases hw
    have hact : GoFV.Opt.LowerTerm.actOp v.op = false := by
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at ht; exact ht.1.2
    simp only [termVL, hg, hm, hl, pureActOp_of_act hact, Option.isSome_none, Bool.false_eq_true,
      ite_false, ht]

/-- What `truncReachL` says. -/
theorem truncReachL_cases {tabs : Tables} {M : Defs} {n : Nat} {o : Op} {ai : Int64} {i : Nat}
    {a a' : ID} (h : truncReachL tabs M n o ai i a a' = true) :
    ∃ k, narrowReadW o ai i = some k ∧ truncFromL tabs M n k a a' = true := by
  unfold truncReachL at h
  simp only [Option.any_eq_true] at h
  exact h

/-! ## A `W` op reads the low 32 bits of each argument -/

/-- `b`'s `W` register is `a`'s wherever `a` has one. -/
def R32 (a b : Val) : Prop := ∀ x, Arm64.reg32 a = some x → Arm64.reg32 b = some x

/-- `R32` pairwise. -/
inductive R32List : List Val → List Val → Prop
  | nil : R32List [] []
  | cons {a b : Val} {as bs : List Val} : R32 a b → R32List as bs → R32List (a :: as) (b :: bs)

theorem r32List_idx {α β : Type} {F : α → Val} {G : β → Val} :
    ∀ {l : List α} {m : List β}, l.length = m.length →
      (∀ j (h1 : j < l.length) (h2 : j < m.length), R32 (F l[j]) (G m[j])) →
      R32List (l.map F) (m.map G)
  | [], [], _, _ => .nil
  | _ :: _, _ :: _, hl, h => .cons (h 0 (by simp) (by simp))
      (r32List_idx (by simpa using hl) fun j h1 h2 => h (j + 1) (by simpa using h1) (by simpa using h2))
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => by simp at hl

section
variable {as bs : List Val}

theorem op1w_r32 (ty : Ty) (f : BitVec 32 → BitVec 32) :
    R32List as bs → Sem.Refines (Arm64.op1w ty f as) (Arm64.op1w ty f bs)
  | .nil => .poison _
  | .cons (a := a) h .nil => by
    simp only [Arm64.op1w]
    cases ha : Arm64.reg32 a with
    | none => exact .poison _
    | some x => rw [h x ha]; exact Sem.Refines.refl _
  | .cons _ (.cons _ _) => .poison _

theorem op2w_r32 (ty : Ty) (f : BitVec 32 → BitVec 32 → BitVec 32) :
    R32List as bs → Sem.Refines (Arm64.op2w ty f as) (Arm64.op2w ty f bs)
  | .nil => .poison _
  | .cons _ .nil => .poison _
  | .cons (a := a) h (.cons (a := c) h' .nil) => by
    simp only [Arm64.op2w]
    cases ha : Arm64.reg32 a with
    | none => exact .poison _
    | some x =>
      cases hc : Arm64.reg32 c with
      | none => exact .poison _
      | some y => rw [h x ha, h' y hc]; exact Sem.Refines.refl _
  | .cons _ (.cons _ (.cons _ _)) => .poison _

theorem cmp1w_r32 (f : BitVec 32 → BitVec 32 × Flags) :
    R32List as bs → Sem.Refines (Arm64.cmp1w f as) (Arm64.cmp1w f bs)
  | .nil => .poison _
  | .cons (a := a) h .nil => by
    simp only [Arm64.cmp1w]
    cases ha : Arm64.reg32 a with
    | none => exact .poison _
    | some x => rw [h x ha]; exact Sem.Refines.refl _
  | .cons _ (.cons _ _) => .poison _

theorem cmp2w_r32 (f : BitVec 32 → BitVec 32 → BitVec 32 × Flags) :
    R32List as bs → Sem.Refines (Arm64.cmp2w f as) (Arm64.cmp2w f bs)
  | .nil => .poison _
  | .cons _ .nil => .poison _
  | .cons (a := a) h (.cons (a := c) h' .nil) => by
    simp only [Arm64.cmp2w]
    cases ha : Arm64.reg32 a with
    | none => exact .poison _
    | some x =>
      cases hc : Arm64.reg32 c with
      | none => exact .poison _
      | some y => rw [h x ha, h' y hc]; exact Sem.Refines.refl _
  | .cons _ (.cons _ (.cons _ _)) => .poison _

theorem flags1w_r32 (f : BitVec 32 → Flags) :
    R32List as bs → Sem.Refines (Arm64.flags1w f as) (Arm64.flags1w f bs)
  | .nil => .poison _
  | .cons (a := a) h .nil => by
    simp only [Arm64.flags1w]
    cases ha : Arm64.reg32 a with
    | none => exact .poison _
    | some x => rw [h x ha]; exact Sem.Refines.refl _
  | .cons _ (.cons _ _) => .poison _

theorem flags2w_r32 (f : BitVec 32 → BitVec 32 → Flags) :
    R32List as bs → Sem.Refines (Arm64.flags2w f as) (Arm64.flags2w f bs)
  | .nil => .poison _
  | .cons _ .nil => .poison _
  | .cons (a := a) h (.cons (a := c) h' .nil) => by
    simp only [Arm64.flags2w]
    cases ha : Arm64.reg32 a with
    | none => exact .poison _
    | some x =>
      cases hc : Arm64.reg32 c with
      | none => exact .poison _
      | some y => rw [h x ha, h' y hc]; exact Sem.Refines.refl _
  | .cons _ (.cons _ (.cons _ _)) => .poison _

/-- **A `W` op is monotone in the low 32 bits of its arguments' registers.** -/
theorem w32_mono {o : Op} (ho : w32Op o = true) (ty : Ty) (k : Int64) (ax : Option AuxRef)
    (h : R32List as bs) : Sem.Refines (Arm64.evalPure o ty k ax as) (Arm64.evalPure o ty k ax bs) := by
  rcases w32Op_mem ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact op2w_r32 ty _ h
  · exact op2w_r32 ty _ h
  · exact op2w_r32 ty _ h
  · exact op2w_r32 ty _ h
  · exact op2w_r32 ty _ h
  · exact op2w_r32 ty _ h
  · exact op2w_r32 ty _ h
  · exact op1w_r32 ty _ h
  · exact op2w_r32 ty _ h
  · exact op1w_r32 ty _ h
  · exact op1w_r32 ty _ h
  · exact op1w_r32 ty _ h
  · exact op1w_r32 ty _ h
  · exact cmp2w_r32 _ h
  · exact cmp1w_r32 _ h
  · exact cmp2w_r32 _ h
  · exact cmp1w_r32 _ h
  · exact flags2w_r32 _ h
  · exact flags1w_r32 _ h

end

theorem width_bits_le (w : Width) : w.bits ≤ 64 := by cases w <;> decide

theorem refines_poison_retypeL (t : Ty) (v : Val) : Sem.Refines (Val.poison.retypeL t) v := by
  rw [retypeL_poison]; exact .poison _

/-- A value narrowed to a narrow width `w` is a narrow integer, or `poison`. -/
theorem retypeL_narrow_cases {w : Width} (hw : w ≠ .w64) (X : Val) :
    X.retypeL (.int w) = .poison ∨ (∃ v x, X = .int v x ∧ X.retypeL (.int w) = .int w (x.setWidth w.bits)) ∨
      ∃ b, X = .bool b ∧ X.retypeL (.int w) = .int w (if b then 1 else 0) := by
  cases X with
  | int v x => exact .inr (.inl ⟨v, x, rfl, int_retypeL_narrow v x⟩)
  | bool b => exact .inr (.inr ⟨b, rfl, bool_retypeL_narrow w b⟩)
  | ptr p => left; cases w <;> first | exact absurd rfl hw | simp [Val.retypeL, Val.widen, Val.retype]
  | _ => left; simp [Val.retypeL, Val.widen, Val.retype]

theorem setWidth_one_low {n m k : Nat} (hm : k ≤ m) (hn : 1 ≤ n) (hm1 : 1 ≤ m) :
    ((1 : BitVec n).setWidth m).setWidth k = (1 : BitVec m).setWidth k := by
  ext i hi
  have h1 : i < m := by omega
  have h2 : 0 < n := by omega
  have h3 : 0 < m := by omega
  simp [BitVec.getElem_setWidth, BitVec.getLsbD_one, h1, h2, h3]

theorem one_setWidth {n k : Nat} (hk : k ≤ n) (h1 : 1 ≤ k) : (1 : BitVec n).setWidth k = 1 := by
  ext i hi
  have h2 : 0 < n := by omega
  simp [BitVec.getElem_setWidth, BitVec.getLsbD_one, BitVec.getElem_one, h2]

/-- Read at a narrow width `w`, a value narrowed to a width `w'` at least `w` is the value read at
`w` (`MakeResult` reading its result through a narrowing `Copy`, `truncFitL`). -/
theorem retypeL_narrow_twice {w w' : Width} (hk : w.bits ≤ w'.bits) (hw : w' ≠ .w64) (X : Val) :
    Sem.Refines ((X.retypeL (.int w')).retypeL (.int w)) (X.retypeL (.int w)) := by
  rcases retypeL_narrow_cases hw X with he | ⟨v, x, rfl, he⟩ | ⟨b, rfl, he⟩ <;> rw [he]
  · exact refines_poison_retypeL _ _
  · rw [int_retypeL_narrow, int_retypeL_narrow, BitVec.setWidth_setWidth_of_le _ hk]
    exact Sem.Refines.refl _
  · rw [int_retypeL_narrow, bool_retypeL_narrow]
    have h1 : 1 ≤ w.bits := by cases w <;> decide
    cases b
    · simp; exact Sem.Refines.refl _
    · simp only [ite_true]
      rw [one_setWidth hk h1]
      exact Sem.Refines.refl _

/-! ## Chains of narrowing copies (`narrowReachL`, `truncFromL`) -/

/-- **A chain of compatible or narrowing copies of at least `w` bits** (`narrowReachL`) reads, at
the narrow width `w`, as its end does: a compatible copy is its argument (`den_copyL`), a narrowing
one of at least `w` bits its argument narrowed, which read at `w` is the argument read at `w`
(`retypeL_narrow_twice`). -/
theorem narrowReachL_den {M : Defs} {tabs : Tables} {ρ : ID → Val} (hT : TypedL true M.get? tabs ρ)
    {w : Width} (hw : w ≠ .w64) :
    ∀ (N : Nat) (b a' : ID), narrowReachL tabs M N w.bits b a' = true → ∀ n,
      Sem.Refines ((denL true M.get? tabs ρ n b).retypeL (.int w))
        ((denL true M.get? tabs ρ n a').retypeL (.int w))
  | 0, b, a', h, n => by
    simp only [narrowReachL, beq_iff_eq] at h; subst h; exact Sem.Refines.refl _
  | N + 1, b, a', h, n => by
    simp only [narrowReachL, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact Sem.Refines.refl _
    · cases hx : M.get? b with
      | none => rw [hx] at h; cases h
      | some x =>
        rw [hx] at h
        simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
        obtain ⟨⟨⟨hop, hsz⟩, hcase⟩, hr⟩ := h
        cases n with
        | zero => exact refines_poison_retypeL _ _
        | succ n =>
          have hih := narrowReachL_den hT hw N _ a' hr (n + 1)
          have hmono := retypeL_mono (.int w)
            (denL_fuel_mono true M.get? tabs ρ n (n + 1) x.args[0]! (by omega))
          rcases hcase with hcomp | hnar
          · cases hy : M.get? x.args[0]! with
            | none => rw [hy] at hcomp; cases hcomp
            | some y =>
              rw [hy] at hcomp
              rw [den_copyL hT hx hop hsz hy hcomp n]
              exact hmono.trans hih
          · split at hnar
            · rename_i w' hw'
              simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hnar
              rw [copy_den hx hop hsz hw']
              exact (retypeL_narrow_twice hnar.1 hnar.2 _).trans (hmono.trans hih)
            · cases hnar

/-- **A narrowing `Copy` read through** (`truncFromL`): the copy is the value its chain ends at,
read at the copy's narrow width `w`, which keeps the `k` bits asked for. -/
theorem truncFrom_den {M : Defs} {tabs : Tables} {ρ : ID → Val} (hT : TypedL true M.get? tabs ρ)
    {N k : Nat} {a a' : ID} (h : truncFromL tabs M N k a a' = true) :
    ∃ w : Width, k ≤ w.bits ∧ w ≠ .w64 ∧ ∀ n,
      Sem.Refines (denL true M.get? tabs ρ n a) ((denL true M.get? tabs ρ n a').retypeL (.int w)) := by
  obtain ⟨c, w, hc, hcop, hcsz, hsh, hkw, hw64, hr⟩ := truncFromL_cases h
  refine ⟨w, hkw, hw64, fun n => ?_⟩
  cases n with
  | zero => exact .poison _
  | succ n =>
    rw [copy_den hc hcop hcsz hsh]
    exact (narrowReachL_den hT hw64 N _ _ hr n).trans
      (retypeL_mono _ (denL_fuel_mono true M.get? tabs ρ n (n + 1) a' (by omega)))

/-- The source of a narrowing `Copy` of at least 32 bits holds the copy's `W` register. -/
theorem reg32_truncFrom {tabs : Tables} {M : Defs} {ρ : ID → Val} (hT : TypedL true M.get? tabs ρ)
    {N : Nat} {a c' : ID} (h : truncFromL tabs M N 32 a c' = true) :
    ∀ n (y : BitVec 32), Arm64.reg32 (denL true M.get? tabs ρ n a) = some y →
      Arm64.reg32 (denL true M.get? tabs ρ n c') = some y := by
  obtain ⟨w, hkw, hw64, hd⟩ := truncFrom_den hT h
  have hw32 : w = .w32 := by
    cases w <;> first | rfl | exact absurd rfl hw64 | simp [Width.bits] at hkw
  subst hw32
  intro n y hy
  exact reg32_retypeL_w32 (Mono.reg32_of (hd n) hy)

/-! ## `TSTWconst [c]` reads the bits of its argument up to `c`'s highest set bit -/

/-- The bits of `imm32 c` are below `tstReadW c`. -/
theorem imm32_lt_tstReadW (c : Int64) {w : Nat} (h : tstReadW c ≤ w) :
    (Arm64.imm32 c).toNat < 2 ^ w :=
  Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by decide) h)

/-- **`TSTWconst [c]` refines through a narrowing to `w ≥ tstReadW c` bits** (`Val.retypeL` at
`int w`, `w < 64`: the value's low `w` bits, which hold every bit `c` tests). -/
theorem tstw_retypeL {c : Int64} {w : Width} (hk : tstReadW c ≤ w.bits) (hw : w ≠ .w64) (B : Val) :
    Sem.Refines (Arm64.flags1w (fun x => logicFlags (x &&& Arm64.imm32 c)) [B.retypeL (.int w)])
      (Arm64.flags1w (fun x => logicFlags (x &&& Arm64.imm32 c)) [B]) := by
  have hc := imm32_lt_tstReadW c hk
  have hbit : ∀ i, w.bits ≤ i → (Arm64.imm32 c).getLsbD i = false := fun i hi =>
    Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hc (Nat.pow_le_pow_right (by decide) hi))
  have hw64 := width_bits_le w
  have key : ∀ {n : Nat} (x : BitVec n),
      ((x.setWidth w.bits).setWidth 64).setWidth 32 &&& Arm64.imm32 c =
        (x.setWidth 64).setWidth 32 &&& Arm64.imm32 c := by
    intro n x
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth]
    by_cases hiw : i < w.bits
    · simp [hiw]
    · simp [hiw, hbit i (by omega)]
  rcases retypeL_narrow_cases hw B with he | ⟨v, x, rfl, he⟩ | ⟨b, rfl, he⟩ <;> rw [he]
  · exact .poison _
  · simp only [Arm64.flags1w, Arm64.reg32, Arm64.reg, Option.map_some]
    rw [key x]; exact Sem.Refines.refl _
  · simp only [Arm64.flags1w, Arm64.reg32, Arm64.reg, Option.map_some]
    cases b
    · simp only [Bool.false_eq_true, ite_false]
      rw [show ((0 : BitVec w.bits).setWidth 64) = 0 by simp]
      exact Sem.Refines.refl _
    · simp only [ite_true]
      have h1 : 0 < w.bits := by cases w <;> decide
      have hone : (1 : BitVec w.bits).setWidth 64 = 1 := by
        ext i hi
        simp [BitVec.getElem_setWidth, BitVec.getLsbD_one, BitVec.getElem_one, h1]
      rw [hone]; exact Sem.Refines.refl _

/-! ## An op reading narrow bits of its arguments (`narrowReadW`) -/

/-- Argument `j` of the op `o` (auxint `ai`): `a` refines `b`, or `o` reads at most `k` bits of
it (`narrowReadW`) and `a` refines `b` narrowed to `w ≥ k` bits. -/
def NarrowArg (o : Op) (ai : Int64) (j : Nat) (a b : Val) : Prop :=
  Sem.Refines a b ∨ ∃ k w, narrowReadW o ai j = some k ∧ k ≤ w.bits ∧ w ≠ .w64 ∧
    Sem.Refines a (b.retypeL (.int w))

theorem r32List_of_idx : ∀ {as bs : List Val}, as.length = bs.length →
    (∀ j (h1 : j < as.length) (h2 : j < bs.length), R32 as[j] bs[j]) → R32List as bs
  | [], [], _, _ => .nil
  | _ :: _, _ :: _, hl, h => .cons (h 0 (by simp) (by simp))
      (r32List_of_idx (by simpa using hl) fun j h1 h2 =>
        h (j + 1) (by simpa using h1) (by simpa using h2))
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => by simp at hl

/-- A value list of one element, or none. -/
theorem list_one_or {α : Type} : ∀ (l : List α), (∃ a, l = [a]) ∨ l.length ≠ 1
  | [a] => .inl ⟨a, rfl⟩
  | [] => .inr (by simp)
  | _ :: _ :: _ => .inr (by simp)

/-- **An op reading narrow bits of its arguments is monotone in them up to those bits**
(`NarrowArg`): an extension (`op1_ext_retypeL`), `TSTWconst` (`tstw_retypeL`), a `W` op
(`w32_mono`). -/
theorem opValL_narrow_mono {tabs : Tables} {o : Op} {ai : Int64} {j0 k0 : Nat}
    (ho : narrowReadW o ai j0 = some k0) (ty : Ty) (ax : Option AuxRef) {as bs : List Val}
    (hlen : as.length = bs.length)
    (h : ∀ j (h1 : j < as.length) (h2 : j < bs.length), NarrowArg o ai j as[j] bs[j]) :
    Sem.Refines (opValL tabs o ty ai ax as) (opValL tabs o ty ai ax bs) := by
  rcases narrowReadW_cases ho with ⟨rfl, -, -⟩ | ⟨hext, -⟩ | ⟨hw, hnt, -⟩
  · rw [opValL_w32 (by decide), opValL_w32 (by decide)]
    show Sem.Refines (Arm64.flags1w _ as) (Arm64.flags1w _ bs)
    rcases list_one_or as with ⟨a, rfl⟩ | hl
    · obtain ⟨b, rfl⟩ : ∃ b, bs = [b] := by
        rcases list_one_or bs with ⟨b, rfl⟩ | hl'
        · exact ⟨b, rfl⟩
        · simp_all
      rcases h 0 (by simp) (by simp) with hr | ⟨k, w, hk, hkw, hw, hr⟩
      · exact Mono.flags1w_mono _ (.cons hr .nil)
      · rcases narrowReadW_cases hk with ⟨-, -, rfl⟩ | ⟨he, -⟩ | ⟨-, hne, -⟩
        · exact (Mono.flags1w_mono _ (.cons hr .nil)).trans (tstw_retypeL hkw hw b)
        · cases he
        · exact absurd rfl hne
    · have hp : ∀ (l : List Val), l.length ≠ 1 →
          Arm64.flags1w (fun x => logicFlags (x &&& Arm64.imm32 ai)) l = .poison := by
        intro l hl
        rcases l with _ | ⟨a, _ | ⟨a', l⟩⟩
        · rfl
        · simp at hl
        · rfl
      rw [hp as hl]; exact .poison _
  · obtain ⟨s, hs⟩ := opValL_ext hext
    rw [hs, hs]
    rcases list_one_or as with ⟨a, rfl⟩ | hl
    · obtain ⟨b, rfl⟩ : ∃ b, bs = [b] := by
        rcases list_one_or bs with ⟨b, rfl⟩ | hl'
        · exact ⟨b, rfl⟩
        · simp_all
      rcases h 0 (by simp) (by simp) with hr | ⟨k, w, hk, hkw, hw, hr⟩
      · exact Mono.op1_mono ty _ (.cons hr .nil)
      · rcases narrowReadW_cases hk with ⟨rfl, -, -⟩ | ⟨he, -⟩ | ⟨hw', -, -⟩
        · cases hext
        · rw [hext] at he; cases he
          exact (Mono.op1_mono ty _ (.cons hr .nil)).trans (op1_ext_retypeL s k0 hkw hw ty b)
        · rw [(w32Op_cases hw').1] at hext; cases hext
    · have hp : ∀ (l : List Val), l.length ≠ 1 → Arm64.op1 ty (Arm64.ext s k0) l = .poison := by
        intro l hl
        rcases l with _ | ⟨a, _ | ⟨a', l⟩⟩
        · rfl
        · simp at hl
        · rfl
      rw [hp as hl]; exact .poison _
  · rw [opValL_w32 hw, opValL_w32 hw]
    apply w32_mono hw
    refine r32List_of_idx hlen fun j h1 h2 => ?_
    rcases h j h1 h2 with hr | ⟨k, w, hk, hkw, hw64, hr⟩
    · exact fun x hx => Mono.reg32_of hr hx
    · rcases narrowReadW_cases hk with ⟨ho', -, -⟩ | ⟨he, -⟩ | ⟨-, -, rfl⟩
      · exact absurd ho' hnt
      · rw [(w32Op_cases hw).1] at he; cases he
      · have hw32 : w = .w32 := by
          cases w <;> first | rfl | exact absurd rfl hw64 | simp [Width.bits] at hkw
        subst hw32
        exact fun x hx => reg32_retypeL_w32 (Mono.reg32_of hr hx)

/-! ## The denotations of a rule event -/

/-- The semantic instance: the leaves are `L` of the matched values. -/
def semEnvL (tabs : Tables) (M : Defs) (I : Inst) (L : ID → Val) : PEnv :=
  { envL tabs M I with leaf := fun p => L (I.at p) }

section Step

variable {tabs : Tables} {M : Defs} {r : Rule} {v : ID} {defs : List Value}

theorem RuleFactsL.not_def (F : RuleFactsL tabs M r v defs) {w : ID} {x : Value}
    (hw : M.get? w = some x) (hne : w ≠ v) : w ∉ defIds defs := fun h =>
  match F.frame.2.2.1 w h with
  | .inl h => hne h
  | .inr h => by rw [hw] at h; cases h

theorem RuleFactsL.keep (F : RuleFactsL tabs M r v defs) {w : ID} {x : Value}
    (hw : M.get? w = some x) (hne : w ≠ v) : (putAll M defs).get? w = some x := by
  rw [F.frame.1 w (F.not_def hw hne), hw]

theorem RuleFactsL.keepAtom (F : RuleFactsL tabs M r v defs) {w : ID} {x : Value}
    (hw : M.get? w = some x) (ha : termVL tabs x = false) : (putAll M defs).get? w = some x := by
  refine F.keep hw fun h => ?_
  subst h; rw [F.hxv] at hw; cases hw; rw [F.hterm] at ha; cases ha

theorem RuleFactsL.fields (F : RuleFactsL tabs M r v defs) (L : ID → Val) :
    FieldsOKL tabs M F.I (semEnvL tabs M F.I L) := by
  intro p w x hm hx
  refine ⟨?_, ?_, ?_⟩ <;> simp [semEnvL, envL, F.at_eq hm, hx]

theorem RuleFactsL.typed (F : RuleFactsL tabs M r v defs) {ρ : ID → Val}
    (hT : TypedL true M.get? tabs ρ) : TypedL true (putAll M defs).get? tabs ρ := by
  intro a ha hsome
  by_cases hd : a ∈ defIds defs
  · obtain ⟨u, hu, ht, -⟩ := F.frame.2.2.2 a hd
    exact absurd ⟨u, hu, ht⟩ ha
  · have he := F.frame.1 a hd
    have hshape : shapeL true (putAll M defs).get? tabs a = shapeL true M.get? tabs a := by
      simp [shapeL, he]
    rw [hshape]
    exact hT a (fun ⟨u, hu, ht⟩ => ha ⟨u, by rw [he]; exact hu, ht⟩) (he ▸ hsome)

theorem RuleFactsL.closed (F : RuleFactsL tabs M r v defs) {C : ID → Prop} (hC : DefClosed M C) :
    DefClosed (putAll M defs) (fun y => C y ∨ (C v ∧ y ∈ defIds defs)) := by
  have hfr := F.frame
  have hnew : ∀ y, C v → y ∈ defIds defs → ∃ m, (putAll M defs).get? y = some m ∧
      ∀ a ∈ m.args, C a ∨ (C v ∧ a ∈ defIds defs) := by
    intro y hv hy
    obtain ⟨u, hu, -, hargs⟩ := hfr.2.2.2 y hy
    refine ⟨u, hu, fun a ha => ?_⟩
    rcases hargs a ha with ⟨p, hp⟩ | ha'
    · exact .inl (F.hreach C hC.arg hv (p, a) hp)
    · exact .inr ⟨hv, ha'⟩
  intro y hy
  rcases hy with hy | ⟨hv, hy⟩
  · by_cases hd : y ∈ defIds defs
    · obtain ⟨m, hm, -⟩ := hC y hy
      rcases hfr.2.2.1 y hd with rfl | h
      · exact hnew _ hy hd
      · rw [hm] at h; cases h
    · obtain ⟨m, hm, hargs⟩ := hC y hy
      exact ⟨m, by rw [hfr.1 y hd, hm], fun a ha => .inl (hargs a ha)⟩
  · exact hnew y hv hy

theorem RuleFactsL.top_ty (F : RuleFactsL tabs M r v defs) (L : ID → Val) :
    (semEnvL tabs M F.I L).ty [] = shpL tabs F.xv.type := by
  simp only [semEnvL, envL, F.at_top, F.hxv, Option.map_some, Option.getD_some]

/-- **The matched value**: its lowered denotation before the event is refined by the one after. -/
theorem RuleFactsL.top (hs : ArmRule.Sound1 r)
    (F : RuleFactsL tabs M r v defs) {C : ID → Prop} (hC : GoFV.Proof.Pass.Rewrite.ArgClosed M C)
    (hv : C v) {ρ : ID → Val} (hT : TypedL true (putAll M defs).get? tabs ρ) {n B : Nat}
    (hIH : ∀ y, C y → Sem.Refines (denL true M.get? tabs ρ n y)
      (denL true (putAll M defs).get? tabs ρ B y)) :
    Sem.Refines (denL true M.get? tabs ρ (n + 1) v)
      (denL true (putAll M defs).get? tabs ρ (B + stepK r) v) := by
  -- the semantic instance
  let e' := semEnvL tabs M F.I (denL true (putAll M defs).get? tabs ρ B)
  have hIC : ∀ p w, (p, w) ∈ F.I → C w := fun p w h => F.hreach C hC hv (p, w) h
  have hσ : ∀ x, (stσL tabs M r F.I x).erase = (sigmaL tabs e' r.pat x).erase :=
    sigmaL_erase (e := envL tabs M F.I) (e' := e') rfl rfl r.pat
  have hev : ∀ x, (stEvL tabs M r defs F.I x).erase =
      (evalE (stVtysL r) (sigmaL tabs e' r.pat) (stOrL tabs r defs) e'
        (Pat.denL tabs e' [] r.pat) x).erase :=
    evalE_erase (e := envL tabs M F.I) (e' := e') _ _ rfl rfl hσ _ _
  have hF := F.fields (denL true (putAll M defs).get? tabs ρ B)
  have hTop := F.top_ty (denL true (putAll M defs).get? tabs ρ B)
  have hdefw : ∀ p w x, (p, w) ∈ F.I → p ≠ [] → M.get? w = some x →
      (putAll M defs).get? w = some x := fun p w x hm hp hx => F.keep hx (F.ne_v hm hp)
  -- the hypotheses of `ArmRule.Sound1`
  have hbt : Oracle.BoolTyped (stOrL tabs r defs) := oracleL_boolTyped _ _ _ _
  have hwf := wf_of (e := envL tabs M F.I) (e' := e') rfl [] r.pat F.hwf
  have hcons := cons_of (pat := r.pat) (I := F.I) (e := envL tabs M F.I) (e' := e')
    rfl rfl hev hσ (fun x w p' h hn => sigmaL_leaf h hn)
    (fun p p' h => by simp only [e', semEnvL, h]) F.hS [] r.pat (fun _ h => h) F.hcons
  have hcond := cond_of hev F.hcond
  have htyped : GoFV.Proof.Rules.Pat.typed e' [] r.pat :=
    typed_ofL (Q := fun p => p ≠ []) (fun _ _ => List.cons_ne_nil _ _) (fun p => rfl)
      (fun p w x hm hp hx => by
        show (denL true _ tabs ρ B (F.I.at p)).hasTy _ = true
        rw [F.at_eq hm]
        exact den_hasTyL hT B (hdefw p w x hm hp hx))
      F.hnodup r.pat [] v F.hmatch (.inr (by rw [F.hpat]; rfl)) F.hleaves
  have hargs : GoFV.Proof.Rules.Pat.argsOK e'.ty [] r.pat = true := F.hargs
  have htopok : Pat.topOKL (e'.ty []) r.pat = true := F.htop
  have hsound := fun hcs => hs.2 tabs e' (stOrL tabs r defs) hbt hwf hcons hcond htyped hargs
    htopok F.hargsL hcs F.hfit F.hadr F.hrng
  -- lower bound
  have hlow : Sem.Refines (denL true M.get? tabs ρ (n + 1) v)
      ((Pat.rawL tabs e' r.pat).retypeL (e'.ty [])) := by
    have h1 := den_le_patDenL (n := n) hF (fun p w hm k hk => by
        show Sem.Refines _ (denL true _ tabs ρ B (F.I.at p))
        rw [F.at_eq hm]
        exact Sem.Refines.trans (denL_fuel_mono _ _ _ _ k n w hk) (hIH w (hIC p w hm)))
      r.pat [] v (n + 1) F.hmatch (Nat.le_refl _) (.inr (by rw [F.hpat]; rfl))
    rw [F.hpat] at h1 ⊢
    simp only [Pat.denL, Pat.rawL] at h1 ⊢
    exact h1
  -- values bound on the semantic side
  have hleafU : ∀ p w, (p, w) ∈ F.I → Sem.Refines (e'.leaf p)
      (denL true (putAll M defs).get? tabs ρ B w) := fun p w hm => by
    show Sem.Refines (denL true _ tabs ρ B (F.I.at p)) _
    rw [F.at_eq hm]; exact Sem.Refines.refl _
  obtain ⟨S, hS⟩ : ∃ S, S = GoFV.Proof.Pass.Rewrite.Pat.sz r.pat := ⟨_, rfl⟩
  have hσ2 : ∀ x, Good (fun w p => p ≠ [] ∧
      Sem.Refines w (denL true (putAll M defs).get? tabs ρ (B + S) (F.I.at p)))
      (sigmaL tabs e' r.pat x) := by
    intro x
    have hm := F.hmatch
    have hS' : GoFV.Proof.Pass.Rewrite.Pat.sz r.pat ≤ S := by omega
    rw [F.hpat] at hm hS' ⊢
    exact sigmaL_good_top (Q := fun p => p ≠ []) (P := fun w p => p ≠ [] ∧
        Sem.Refines w (denL true (putAll M defs).get? tabs ρ (B + S) (F.I.at p))) (S := S)
      (fun _ _ => List.cons_ne_nil _ _)
      (fun p w hm' hp => ⟨hp, by
        show Sem.Refines (denL true _ tabs ρ B (F.I.at p)) _
        exact denL_fuel_mono _ _ _ _ _ _ _ (by omega)⟩)
      (fun q p w hm' hp hsz => ⟨hp, by
        rw [F.at_eq hm'.mem]
        exact patDen_le_denL (Q := fun p => p ≠ []) (fun _ _ => List.cons_ne_nil _ _) hF
          hdefw hleafU q p w _ hm' hp (by omega)⟩) hm hS' x
  have hev2 : ∀ x, Good (fun w p => p ≠ [] →
      Sem.Refines w (denL true (putAll M defs).get? tabs ρ (B + S) (F.I.at p)))
      (evalE (stVtysL r) (sigmaL tabs e' r.pat) (stOrL tabs r defs) e'
        (Pat.denL tabs e' [] r.pat) x) :=
    evalE_good _ _ _ (fun x => good_mono (fun w p h _ => h.2) (hσ2 x)) (fun h => absurd rfl h)
      (fun x => good_of_flat (oracleL_flat _ _ _ _ x))
  rcases F.result with hR | hR
  · -- copy
    obtain ⟨R⟩ := hR
    have hpos := R.hpos
    obtain ⟨w0, hst⟩ : ∃ w0, stEvL tabs M r defs F.I R.ce = .val w0 (some R.p) := by
      revert hpos; cases stEvL tabs M r defs F.I R.ce <;> simp [DV.pos?]
    have h' := hev R.ce
    rw [hst] at h'
    have hp : R.p ≠ [] := fun h => R.hne (by rw [h, F.at_top])
    have hcases : ∀ d : DV, (DV.val w0 (some R.p)).erase = d.erase →
        Good (fun w p => p ≠ [] →
          Sem.Refines w (denL true (putAll M defs).get? tabs ρ (B + S) (F.I.at p))) d →
        Sem.Refines (d.valOr ((stOrL tabs r defs).val R.ce))
          (denL true (putAll M defs).get? tabs ρ (B + S) (F.I.at R.p)) := by
      intro d hd hg
      rcases DV.erase_eq_cases hd with rfl | ⟨v1, v2, p1, h1, rfl⟩
      · exact hg.1 w0 R.p rfl hp
      · cases h1; exact hg.1 v2 R.p rfl hp
    have hup := hcases _ h' (hev2 R.ce)
    obtain ⟨y, hy, hyt, hsh⟩ : ∃ y, M.get? (F.I.at R.p) = some y ∧ y.type = R.u.type ∧
        GoFV.Opt.RewriteCheck.copyCompat (shpL tabs y.type) (shpL tabs F.xv.type) = true := by
      have := R.hty
      cases h : M.get? (F.I.at R.p) with
      | none => rw [h] at this; cases this
      | some y =>
        rw [h] at this
        simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at this
        exact ⟨y, rfl, this.1, this.2⟩
    have hcs : GoFV.Proof.Low.copyShapeOK (evalE (stVtysL r) (sigmaL tabs e' r.pat)
        (stOrL tabs r defs) e' (Pat.denL tabs e' [] r.pat)) e' r.result := by
      rw [R.hres]
      simp only [GoFV.Proof.Low.copyShapeOK]
      split
      · rename_i w p heq
        have h2 := h'
        rw [heq, DV.erase_val, DV.erase_val] at h2
        simp only [DV.val.injEq, Option.some.injEq, true_and] at h2
        subst h2
        rw [hTop]
        simp only [e', semEnvL, envL, hy, Option.map_some, Option.getD_some]
        exact hsh
      · trivial
    have hsound := hsound hcs
    rw [R.hres] at hsound
    have hkeep := F.keep hy R.hne
    have hdv : (putAll M defs).get? v = some R.u := by rw [R.put, get?_put]; simp
    have hK : B + stepK r = (B + S + 1) + 1 := by simp [stepK, resLen, R.hres, hS]; omega
    rw [hK, denT_succ hdv (termVL_of_copy R.hop), R.hargs, R.hop]
    simp only [List.map_cons, List.map_nil, Array.toList, opValL_copy]
    rw [← hyt, ← shapeL_of (tabs := tabs) hkeep, den_retypeL hT _ _ (by rw [hkeep]; rfl)]
    exact hlow.trans (hsound.trans (hup.trans (denL_fuel_mono _ _ _ _ _ _ _ (by omega))))
  · -- build
    obtain ⟨R⟩ := hR
    have hsound := hsound (by rw [R.hres]; trivial)
    rw [R.hres] at hsound
    have hTy : e'.ty [] = shpL tabs F.xv.type := hTop
    have key : ∀ f k (hk : k < R.nodes.length),
        Sem.Refines (nodeDenL tabs e' r.pat (evalE (stVtysL r) (sigmaL tabs e' r.pat)
            (stOrL tabs r defs) e' (Pat.denL tabs e' [] r.pat))
          (stOrL tabs r defs) (sigmaL tabs e' r.pat) (e'.ty []) R.nodes f k)
        (denL true (putAll M defs).get? tabs ρ (B + S + f) (R.us[k]'(R.hlen ▸ hk)).id) := by
      intro f
      induction f with
      | zero => intro k hk; exact .poison _
      | succ f ih =>
        intro k hk
        have hk' : k < R.us.length := R.hlen ▸ hk
        obtain ⟨hop, ht, hty, hai, hax, hsz, hargs⟩ := nodeOKL_facts (R.hnode k hk hk')
        rw [nodeDenL_succ _ _ _ _ _ _ _ _ f k R.nodes[k] (List.getElem?_eq_getElem hk)]
        rw [show B + S + (f + 1) = (B + S + f) + 1 by omega, denT_succ (R.get k hk') ht]
        rw [← hTy] at hty
        rw [← tySelL_eq hev, ← aiSelL_eq hev, ← hty, ← hai, ← hop]
        have hax' : nodeAuxL e' r.pat (stOrL tabs r defs) R.nodes[k].aux = R.us[k].aux := by
          rw [hax]; rfl
        rw [hax']
        apply retypeL_mono
        apply opValL_mono_term ht
        refine refinesList_idx (by simp [hsz]) fun j h1 h2 => ?_
        have harg := hargs j h1 (by simpa using h2)
        simp only [Array.getElem_toList]
        cases hn : R.nodes[k].args[j] with
        | var x =>
          rw [hn] at harg
          simp only [argID, Option.map_eq_some_iff] at harg
          obtain ⟨p, hp, hpa⟩ := harg
          simp only [argValL]
          obtain ⟨w0, hw0⟩ : ∃ w0, stσL tabs M r F.I x = .val w0 (some p) := by
            revert hp; cases stσL tabs M r F.I x <;> simp [DV.pos?]
          have hx := hσ x
          rw [hw0] at hx
          rcases DV.erase_eq_cases hx with h2 | ⟨v1, v2, p1, h1, h2⟩
          · rw [← h2]
            have := (hσ2 x).1 w0 p h2.symm
            rw [← hpa]
            exact this.2.trans (denL_fuel_mono _ _ _ _ _ _ _ (by omega))
          · cases h1
            rw [h2]
            have := (hσ2 x).1 v2 p h2
            rw [← hpa]
            exact this.2.trans (denL_fuel_mono _ _ _ _ _ _ _ (by omega))
        | node j' =>
          rw [hn] at harg
          simp only [argID] at harg
          simp only [argValL]
          obtain ⟨hj', hj'e⟩ := List.getElem?_eq_some_iff.1 harg
          simp only [List.length_map] at hj'
          rw [← hj'e]
          simp only [List.getElem_map]
          exact ih j' (R.hlen ▸ hj')
        | expr _ =>
          rw [hn] at harg
          simp [argID] at harg
    have h0 := key R.nodes.length 0 R.len
    have hid := R.id0 (R.hlen ▸ R.len)
    simp only [hid] at h0
    refine hlow.trans (hsound.trans (h0.trans (denL_fuel_mono _ _ _ _ _ _ _ ?_)))
    simp [stepK, resLen, R.hres, hS]; omega

/-- **One rule event**: on a set closed under arguments, the lowered denotations after the event
refine those before, with the fuel multiplied by `stepK r`. -/
theorem RuleFactsL.step (hs : ArmRule.Sound1 r)
    (F : RuleFactsL tabs M r v defs) {C : ID → Prop} (hC : DefClosed M C) {ρ : ID → Val}
    (hT : TypedL true M.get? tabs ρ) :
    ∀ n y, C y → Sem.Refines (denL true M.get? tabs ρ n y)
      (denL true (putAll M defs).get? tabs ρ (n * stepK r) y) := by
  have hT' := F.typed hT
  intro n
  induction n with
  | zero => intro y _; exact .poison _
  | succ n ih =>
    intro y hy
    by_cases hyv : y = v
    · subst hyv
      rw [Nat.succ_mul]
      exact F.top hs hC.arg hy hT' ih
    · obtain ⟨m, hm, hargs⟩ := hC y hy
      have hkeep := F.keep hm hyv
      have hK : (n + 1) * stepK r = (n * stepK r + (stepK r - 1)) + 1 := by
        rw [Nat.succ_mul]; simp only [stepK]; omega
      rw [hK]
      by_cases ht : termVL tabs m = true
      · rw [denT_succ hm ht, denT_succ hkeep ht]
        exact retypeL_mono _ (opValL_mono_term ht _ (GoFV.Proof.AtomSim.refinesList_map fun a ha =>
          (ih a (hargs a (Array.mem_toList_iff.1 ha))).trans
            (denL_fuel_mono _ _ _ _ _ _ _ (by omega))))
      · have h1 : ¬ IsTermL tabs M.get? y := fun ⟨u, hu, hu'⟩ => by
          rw [hm] at hu; cases hu; exact ht hu'
        have h2 : ¬ IsTermL tabs (putAll M defs).get? y := fun ⟨u, hu, hu'⟩ => by
          rw [hkeep] at hu; cases hu; exact ht hu'
        rw [denL_succ_atom h1, denL_succ_atom h2]; exact Sem.Refines.refl _

end Step

end GoFV.Proof.Low.Val
