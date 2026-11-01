import GoFV.Proof.Rules.ConstString
import GoFV.Rules.Generated.Generic.Values06

/-!
# Rule lemma: `MemEq` of the same pointer (`generic.rules:1592`)

`(MemEq p q _ _) && isSamePtr(p, q) => (ConstBool [true])` under `Rule.SoundT` (`DenT.lean`):
`FrameOK`, which the rewrite validator checks on the instance (`condFrameOK`: `p` and `q` match
the same value), says that the leaves bound to `p` and `q` are equal. `memEq` reads the same bytes
twice, so it is `poison` or `true` (`memEq_self`; issue #69).
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

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
      · exact .inl rfl
      · exact .inr (by simp)
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

/-! ## Non-vacuity (`rule-sat` draws no tables) -/

/-- `generic.rules:1592` at `MemEq p p 0 mem` (an empty comparison is valid at any pointer). -/
theorem inst_r_generic_1592 : Rule.InstT GoFV.Rules.Generated.Generic.r_generic_1592 {}
    { leaf := fun p => if p = [2] then .int .w64 0 else if p = [3] then .mem {} else
        .ptr ⟨.heap 0, 0⟩
      ty := fun p => if p = [] then .bool else if p = [2] then .int .w64 else
        if p = [3] then .mem else .ptr none
      auxInt := fun _ => 0, aux := fun _ => none }
    (Oracle.const true) := by
  refine ⟨Oracle.const_boolTyped true, ?_⟩
  simp [GoFV.Rules.Generated.Generic.r_generic_1592, FrameOK, Result.nodes, samePtrVars,
    numElem1Vars, shiftAmt?, Pat.leafPos, Pat.leafPoss, Pat.rawT, Pat.densT, Pat.denT, sigmaT,
    Pat.bindsT, Pat.bindssT, emptyStrVars, opVal, memEq, Mem.read]
  rule_eval
  refine ⟨fun ae x h => ?_, fun ae b h => ?_⟩
  · subst h; simp [lenVar?]
  · subst h; simp

end GoFV.Proof.Rules
