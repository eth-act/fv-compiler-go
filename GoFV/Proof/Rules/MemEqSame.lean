import GoFV.Proof.Rules.ConstString
import GoFV.Proof.PtrAddr
import GoFV.Rules.Generated.Generic.Values06
import GoFV.Rules.Generated.Generic.Values08

/-!
# Rule lemmas: `MemEq` of the same pointer (`generic.rules:1592`) or of length 0 (`:1590`),
`NeqPtr` of a pointer and an offset of it (`generic.rules:1680`)

`(MemEq p q _ _) && isSamePtr(p, q) => (ConstBool [true])` under `Rule.SoundT` (`DenT.lean`):
`FrameOK`, which the rewrite validator checks on the instance (`condFrameOK`: `p` and `q` match
the same value), says that the leaves bound to `p` and `q` are equal. `memEq` reads the same bytes
twice, so it is `poison` or `true` (`memEq_self`; issue #69).

`(MemEq _ _ (Const64 [0]) _) => (ConstBool [true])` under `Rule.Sound`: a read of no bytes is
`#[]` at any pointer (`Mem.read`), so two such reads are equal and poison-free; the length
constant at any type shape is `0` or not an integer (`retype_i64_zero`), and `memEq` is `poison`
or `true` (`memEq_len0`).

`(NeqPtr (AddPtr p1 o1) p2) && isSamePtr(p1, p2) => (IsNonNil o1)`: `p1` and `p2` are the same
leaf, a pointer `p` (`Pat.argsOK`: `AddPtr`'s pointer argument), and the offset a 64-bit integer
`k`; `p + k` is `poison` outside `p`'s window and otherwise compares equal to `p` iff `k = 0`
(`ptr_add_eq_self`), which `IsNonNil k` negates. `Pat.argsOK` also gives the `AddPtr` a pointer
shape: at `uintptr` it would compare by the concrete address, and a pointer that does not convert
back to itself (a frame temporary) would differ from its own address.
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

section

variable [GoFV.SSA.Sem.Addrs]

theorem memEq_self (x n m : Val) :
    memEq [x, x, n, m] = .poison ∨ memEq [x, x, n, m] = .bool true := by
  unfold memEq
  split
  · rename_i p q w k mm heq
    simp only [List.cons.injEq] at heq
    obtain ⟨rfl, h, -⟩ := heq
    cases h
    split
    · rename_i a b ha hb
      rw [ha] at hb; cases hb
      split
      · rename_i bs cs h1 h2
        rw [h1] at h2; cases h2
        split
        · exact .inl rfl
        · exact .inr (by simp)
      · exact .inl rfl
    · exact .inl rfl
  · exact .inl rfl
/-- `generic.rules:1592`: `(MemEq p q _ _) && isSamePtr(p, q) => (ConstBool <typ.Bool> [true])` -/
theorem r_generic_1592_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_1592 := by
  refine ⟨rfl, fun tabs e or _ => ?_⟩
  intro σ ev hfr _ _ _ hty _ _ _
  obtain ⟨p, q, hp, hq, hpq⟩ := hfr.2.2.1 (0, 1)
    (by simp [GoFV.Rules.Generated.Generic.r_generic_1592, samePtrVars])
  simp [GoFV.Rules.Generated.Generic.r_generic_1592, Pat.leafPos, Pat.leafPoss] at hp hq
  subst hp hq
  clear hfr
  simp only [GoFV.Rules.Generated.Generic.r_generic_1592, Pat.rawT, Pat.densT, Pat.denT,
    opVal, reduceCtorEq, ite_false, reduceEvalPure, hpq, Nat.zero_add, Nat.reduceAdd] at hty ⊢
  simp only [resDenT, nodeDenT, List.length_cons, List.length_nil, List.getElem?_cons_zero,
    List.map_cons, List.map_nil]
  have hb : ev (.field (.rsv .typ) "Bool" (.named "*types.Type")) = .ty .bool := by
    dsimp only [ev, evalE, fieldE]; simp only [rule_helper, Option.map_some, Option.getD_some]
  have ht : ev (.lit .bool (.bool true)) = .bool true := rfl
  rw [hb, ht]
  simp only [opVal, reduceCtorEq, ite_false, reduceEvalPure, toAuxIntD, reduceAuxType,
    Option.getD_some]
  rcases memEq_self (e.leaf [1]) (e.leaf [2]) (e.leaf [3]) with h | h <;> rw [h]
  · exact Refines.poison _
  · simp [Conv.constBool, Val.retype]
    exact Refines.refl _

private theorem retype_i64_zero {t : Ty} {w : Width} {k : BitVec w.bits}
    (h : Val.retype t (Val.i64 0) = .int w k) : k.toNat = 0 := by
  cases t <;> simp only [Val.retype, reduceCtorEq] at h
  · split at h
    · cases h; simp
    · cases h
  · cases h; rfl

/-- `MemEq` of length 0 (at any type shape of the length constant) is `poison` or `true`. -/
private theorem memEq_len0 (t : Ty) (a b m : Val) :
    Refines (memEq [a, b, Val.retype t (Val.i64 0), m]) (.bool true) := by
  unfold memEq
  split
  · rename_i p q w k mm heq
    simp only [List.cons.injEq] at heq
    obtain ⟨rfl, rfl, hk, rfl, -⟩ := heq
    rw [retype_i64_zero hk]
    have hr : ∀ (m : Mem) p, m.read p 0 = some #[] := fun _ _ => rfl
    split
    · simp only [hr, Array.any_empty, Bool.or_false, Bool.false_eq_true, ite_false,
        beq_self_eq_true]
      exact Refines.bool true
    · exact Refines.poison _
  · exact Refines.poison _

/-- `generic.rules:1590`: `(MemEq _ _ (Const64 [0]) _) => (ConstBool <typ.Bool> [true])` -/
theorem r_generic_1590_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1590 := by
  rule_unfold
  (try rule_ands)
  (try rule_clear_oracle)
  (try rule_norm)
  (try rule_ands)
  all_goals (repeat rule_split1)
  all_goals (try rule_widths)
  exact memEq_len0 _ _ _ _

/-- `p + k` is `p` iff `k = 0`. -/
theorem ptr_add_eq_self (p : Ptr) (k : BitVec 64) : (p.add k).eq p = (k == 0) := by
  simp only [Ptr.eq, Ptr.add, beq_self_eq_true, Bool.true_and]
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor <;> intro h <;> bv_omega

/-- `generic.rules:1680`: `(NeqPtr (AddPtr p1 o1) p2) && isSamePtr(p1, p2) => (IsNonNil o1)` -/
theorem r_generic_1680_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_1680 := by
  refine ⟨rfl, fun tabs e or _ => ?_⟩
  intro σ ev hfr hwf hcons hcond hty htyped hargs hnn
  obtain ⟨p, q, hp, hq, hpq⟩ := hfr.2.2.1 (1, 2)
    (by simp [GoFV.Rules.Generated.Generic.r_generic_1680, samePtrVars])
  simp [GoFV.Rules.Generated.Generic.r_generic_1680, Pat.leafPos, Pat.leafPoss] at hp hq
  subst hp hq
  clear hfr
  simp only [GoFV.Rules.Generated.Generic.r_generic_1680, Pat.rawT, Pat.densT, Pat.denT,
    opVal, reduceCtorEq, ite_false, reduceEvalPure, hpq, Nat.zero_add] at hty ⊢
  simp only [resDenT, nodeDenT, List.length_cons, List.length_nil, List.getElem?_cons_zero,
    List.map_cons, List.map_nil]
  simp only [GoFV.Rules.Generated.Generic.r_generic_1680, Pat.argsOK, Pat.argsOKs, argShapeOk,
    Nat.zero_add, beq_self_eq_true, ↓reduceIte, Nat.reduceBEq, Nat.reduceBNe, Bool.false_or,
    Bool.and_eq_true, and_true, Bool.false_eq_true] at hargs
  simp only [GoFV.Rules.Generated.Generic.r_generic_1680, Pat.typed, Pat.typeds,
    Nat.zero_add, and_true] at htyped
  have hs : (σ 0).valOr (or.val (Expr.var 0)) = e.leaf [1, 0] := by
    simp [σ, sigmaT, Pat.bindsT, Pat.bindssT, GoFV.Rules.Generated.Generic.r_generic_1680,
      DV.valOr, List.lookup]
  rw [hs, opVal_pure (by decide)]
  obtain ⟨⟨-, ⟨hPty, hA⟩, hOty⟩, -⟩ := hargs
  obtain ⟨⟨hP0, hO0⟩, -⟩ := htyped
  obtain ⟨elA, hA'⟩ := isPtrTy_iff.1 hA
  obtain ⟨elP, hP'⟩ := isPtrTy_iff.1 hPty
  rw [hpq, hP'] at hP0
  rw [isInt64Ty_iff.1 hOty] at hO0
  rw [hA'] at hty ⊢
  have hn : ∀ x, evalPure .IsNonNil (e.ty []) 0 none [x] = PtrOps.isNonNil [x] := fun _ => rfl
  rw [hn]
  have hr0 : Val.retype (.ptr elA) .poison = .poison := rfl
  rcases val_of_hasTy_ptr hP0 with hl | ⟨y, hl⟩ | ⟨p, hl⟩ <;> rw [hl] at hty ⊢
  · simp only [PtrOps.addPtr, hr0, PtrOps.eqPtr, Val.asPtrWord]; exact Refines.poison _
  · rcases val_of_hasTy_int64 hO0 with ho | ⟨x, ho⟩ | ⟨q, ho, -⟩ <;> rw [ho] at hty ⊢
    · simp only [PtrOps.addPtr, asOffset, hr0, PtrOps.eqPtr, Val.asPtrWord]
      exact Refines.poison _
    · have hri : ∀ z, Val.retype (.ptr elA) (.int .w64 z) = .int .w64 z := fun _ => rfl
      by_cases hw : ((Ptr.ofAddr y).add (BitVec.signExtend 64 x)).inWindow = true
      · have h1 : PtrOps.wordRes y (BitVec.signExtend 64 x) =
            .int .w64 (y + BitVec.signExtend 64 x) := by
          unfold PtrOps.wordRes; rw [if_pos hw]
        simp only [PtrOps.addPtr, asOffset, h1, hri, PtrOps.eqPtr, Val.asPtrWord,
          Ptr.ofAddr_add_of_inWindow hw, ptr_add_eq_self, PtrOps.isNonNil] at hty ⊢
        have hx : ((BitVec.signExtend 64 x == 0) != true) = (x != 0) := by
          have h64 : BitVec.signExtend 64 x = x := BitVec.signExtend_eq x
          rw [h64]
          show ((x == (0 : BitVec 64)) != true) = !(x == (0 : BitVec 64))
          cases (x == (0 : BitVec 64)) <;> rfl
        rw [hx] at hty ⊢
        exact refines_retype_of_hasTy hty
      · have h1 : PtrOps.wordRes y (BitVec.signExtend 64 x) = .poison := by
          unfold PtrOps.wordRes; rw [if_neg hw]
        simp only [PtrOps.addPtr, asOffset, h1, hr0, PtrOps.eqPtr, Val.asPtrWord]
        exact Refines.poison _
    · simp only [PtrOps.addPtr, asOffset, hr0, PtrOps.eqPtr, Val.asPtrWord]
      exact Refines.poison _
  rcases val_of_hasTy_int64 hO0 with ho | ⟨x, ho⟩ | ⟨q, ho, -⟩ <;> rw [ho] at hty ⊢
  · simp only [PtrOps.addPtr, asOffset, hr0, PtrOps.eqPtr, Val.asPtrWord]
    exact Refines.poison _
  · simp only [PtrOps.addPtr, asOffset, PtrOps.ptrRes] at hty ⊢
    by_cases hw : (p.add (BitVec.signExtend 64 x)).inWindow = true
    · simp only [hw, ↓reduceIte, Ptr.word_retype_ptr, PtrOps.eqPtr, Ptr.word_asPtrWord hw]
        at hty ⊢
      simp only [Val.asPtrWord, ptr_add_eq_self, PtrOps.isNonNil] at hty ⊢
      have hx : ((BitVec.signExtend 64 x == 0) != true) = (x != 0) := by
        have h64 : BitVec.signExtend 64 x = x := BitVec.signExtend_eq x
        rw [h64]
        show ((x == (0 : BitVec 64)) != true) = !(x == (0 : BitVec 64))
        cases (x == (0 : BitVec 64)) <;> rfl
      rw [hx] at hty ⊢
      exact refines_retype_of_hasTy hty
    · simp only [hw, Bool.false_eq_true, ↓reduceIte, hr0, PtrOps.eqPtr, Val.asPtrWord]
      exact Refines.poison _
  · simp only [PtrOps.addPtr, asOffset, hr0, PtrOps.eqPtr, Val.asPtrWord]
    exact Refines.poison _

end

open scoped GoFV.SSA.Sem.Fixed

/-! ## Non-vacuity (`rule-sat` draws no tables) -/

/-- `generic.rules:1592` at `MemEq p p 0 mem` (an empty comparison is valid at any pointer; `p`
the heap block's address word `2^40`). -/
theorem inst_r_generic_1592 : Rule.InstT GoFV.Rules.Generated.Generic.r_generic_1592 {}
    { leaf := fun p => if p = [2] then .int .w64 0 else if p = [3] then .mem {} else
        .int .w64 (2 ^ 40)
      ty := fun p => if p = [] then .bool else if p = [2] then .int .w64 else
        if p = [3] then .mem else .ptr none
      auxInt := fun _ => 0, aux := fun _ => none }
    (Oracle.const true) := by
  refine ⟨Oracle.const_boolTyped true, ?_⟩
  simp [GoFV.Rules.Generated.Generic.r_generic_1592, FrameOK, Result.nodes, samePtrVars, sameLeaves,
    numElem1Vars, shiftAmt?, Pat.leafPos, Pat.leafPoss, Pat.rawT, Pat.densT, Pat.denT, sigmaT,
    Pat.bindsT, Pat.bindssT, emptyStrVars, opVal, memEq, Mem.read, Val.asPtrWord]
  rule_eval
  refine ⟨fun ae x h => ?_, fun ae b h => ?_⟩
  · subst h; simp [lenVar?]
  · subst h; simp

/-- `generic.rules:1590` at `MemEq p p 0 mem` (`p` the heap block's address word `2^40`). -/
theorem inst_r_generic_1590 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_1590
    (PEnv.ofLists [([0], .i64 (2 ^ 40)), ([1], .i64 (2 ^ 40)), ([3], .mem {})]
      [([], .bool), ([0], .ptr none), ([1], .ptr none), ([2], .int .w64), ([3], .mem)] (.int .w64) [])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_1590]
  rule_eval
  simp [memEq, Mem.read, Val.asPtrWord, Val.hasTy]

/-- `generic.rules:1680` at `p + 8 != p` for a heap pointer `p` (its address word `2^40`). -/
theorem inst_r_generic_1680 : Rule.InstT GoFV.Rules.Generated.Generic.r_generic_1680 {}
    { leaf := fun p => if p = [1, 0] then .int .w64 8 else .int .w64 (2 ^ 40)
      ty := fun p => if p = [] then .bool else if p = [1, 0] then .int .w64 else .ptr none
      auxInt := fun _ => 0, aux := fun _ => none }
    (Oracle.const true) := by
  refine ⟨Oracle.const_boolTyped true, ?_⟩
  simp [GoFV.Rules.Generated.Generic.r_generic_1680, FrameOK, Result.nodes, samePtrVars, sameLeaves,
    numElem1Vars, shiftAmt?, Pat.leafPos, Pat.leafPoss, Pat.rawT, Pat.densT, Pat.denT,
    emptyStrVars, opVal]
  rule_eval
  refine fun h => absurd (congrArg (fun v => match v with | Val.poison => true | _ => false) h) ?_
  decide +kernel

end GoFV.Proof.Rules
