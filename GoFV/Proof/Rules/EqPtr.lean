import GoFV.Proof.Rules.Tactic
import GoFV.Proof.Rules.NonVacuous
import GoFV.Proof.Rules.ConstString
import GoFV.Rules.Generated.Generic.Values03
import GoFV.Rules.Generated.Generic.Values04
import GoFV.Rules.Generated.Generic.Values08

variable [GoFV.SSA.Sem.Addrs]

/-!
# Rule lemmas: `EqPtr`/`NeqPtr` against `ConstNil`

`Rule.Sound` (`GoFV/Proof/Rules/Den.lean`) of the P2 rules comparing a pointer with the nil
pointer (`docs/proofs/rules.md`). By `Pat.argsOK` both arguments are pointer words (a pointer
or a 64-bit integer, `uintptr` itabs), so the nil constant reads as the nil pointer
(`null_word`) and the other argument is `poison`, an integer or a pointer
(`val_of_hasTy_word`); pointer equality compares block and offset (#156), so equality with nil
is `Ptr.isNil` (`null_eq`; an integer address is nil iff it is 0, `ofAddr_isNil`), which
`IsNonNil` negates. A pointer word equals itself (`ptr_eq_self`; `generic.rules:1646`, `:1647`).

`generic.rules:1689` (`(IsNonNil (Addr _)) => (ConstBool [true])`) under `Rule.SoundT`: the
`Addr` is `addrVal` of its aux, a global's address (not nil) or `poison`.
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

/-- `generic.rules:1684`: `(NeqPtr (ConstNil) p) => (IsNonNil p)` -/
theorem r_generic_1684_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1684 := by
  rule_unfold
  obtain ⟨h0, h1⟩ := hat
  have hn := null_word h0
  generalize Val.retype (e.ty [0]) (Val.i64 0) = n at hn hty ⊢
  rcases val_of_hasTy_word h1 hlt with hl | ⟨x, hl⟩ | ⟨p, hl⟩ <;> rw [hl] at hty ⊢
  · simp only [PtrOps.eqPtr, hn]; simp only [Val.asPtrWord]; exact Refines.poison _
  all_goals
    simp only [PtrOps.eqPtr, hn] at hty ⊢
    simp only [Val.asPtrWord, PtrOps.isNonNil, null_eq, ofAddr_isNil,
      Bool.bne_true, not_beq_bne] at hty ⊢
    exact refines_retype_of_hasTy hty

/-- `generic.rules:1683`: `(EqPtr (ConstNil) p) => (Not (IsNonNil p))` -/
theorem r_generic_1683_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1683 := by
  rule_unfold
  obtain ⟨h0, h1⟩ := hat
  have hn := null_word h0
  generalize Val.retype (e.ty [0]) (Val.i64 0) = n at hn hty ⊢
  rcases val_of_hasTy_word h1 hlt with hl | ⟨x, hl⟩ | ⟨p, hl⟩ <;> rw [hl] at hty ⊢
  · simp only [PtrOps.eqPtr, hn]; simp only [Val.asPtrWord]; exact Refines.poison _
  all_goals
    simp only [PtrOps.eqPtr, hn] at hty ⊢
    simp only [Val.asPtrWord, PtrOps.isNonNil, null_eq, ofAddr_isNil,
      Cmp.not, bool1, Val.retype, Val.asBool, Bool.bne_false] at hty ⊢
    try simp only [bne, Bool.not_not] at hty ⊢
    exact refines_retype_of_hasTy hty

theorem ptr_eq_self (p : Ptr) : p.eq p = true := by
  simp [Ptr.eq]

/-- `generic.rules:1646`: `(EqPtr x x) => (ConstBool [true])` -/
theorem r_generic_1646_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1646 := by
  rule_unfold
  rw [hc] at hty ⊢
  have hb : PtrOps.eqPtr false [e.leaf [0], e.leaf [0]] = .poison ∨
      PtrOps.eqPtr false [e.leaf [0], e.leaf [0]] = .bool true := by
    rcases val_of_hasTy_word hat.1 hlt.1 with hl | ⟨x, hl⟩ | ⟨p, hl⟩ <;> rw [hl] <;>
      simp [PtrOps.eqPtr, Val.asPtrWord, ptr_eq_self]
  rcases hb with hb | hb <;> rw [hb] at hty ⊢
  · exact Refines.poison _
  · exact refines_retype_of_hasTy hty

/-- `generic.rules:1646` at a global pointer. -/
theorem inst_r_generic_1646 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_1646
    (PEnv.ofLists [([0], .ptr ⟨.global "g", 8⟩), ([1], .ptr ⟨.global "g", 8⟩)] [([], .bool)] (.ptr none) [])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_1646]
  rule_eval
  simp [PtrOps.eqPtr, Val.asPtrWord, ptr_eq_self]

/-- `generic.rules:1647`: `(NeqPtr x x) => (ConstBool [false])` -/
theorem r_generic_1647_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1647 := by
  rule_unfold
  rw [hc] at hty ⊢
  have hb : PtrOps.eqPtr true [e.leaf [0], e.leaf [0]] = .poison ∨
      PtrOps.eqPtr true [e.leaf [0], e.leaf [0]] = .bool false := by
    rcases val_of_hasTy_word hat.1 hlt.1 with hl | ⟨x, hl⟩ | ⟨p, hl⟩ <;> rw [hl] <;>
      simp [PtrOps.eqPtr, Val.asPtrWord, ptr_eq_self]
  rcases hb with hb | hb <;> rw [hb] at hty ⊢
  · exact Refines.poison _
  · exact refines_retype_of_hasTy hty

/-- `generic.rules:1647` at a global pointer. -/
theorem inst_r_generic_1647 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_1647
    (PEnv.ofLists [([0], .ptr ⟨.global "g", 8⟩), ([1], .ptr ⟨.global "g", 8⟩)] [([], .bool)] (.ptr none) [])
    (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_1647]
  rule_eval
  simp [PtrOps.eqPtr, Val.asPtrWord, ptr_eq_self]

/-- `generic.rules:1687`: `(IsNonNil (ConstNil)) => (ConstBool [false])` -/
theorem r_generic_1687_sound : Rule.Sound GoFV.Rules.Generated.Generic.r_generic_1687 := by
  rule_unfold
  obtain ⟨hr, -⟩ := wordShape_ptr hat
  simp only [hr] at hty ⊢
  simp only [Val.retype, PtrOps.isNonNil, Ptr.isNil, Ptr.null] at hty ⊢
  exact refines_retype_of_hasTy hty

/-- `generic.rules:1687` at a pointer-typed `ConstNil`. -/
theorem inst_r_generic_1687 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_1687
    (PEnv.ofLists [] [([], .bool)] (.ptr none) []) (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_1687]
  rule_eval
  simp [PtrOps.isNonNil, Ptr.isNil, Ptr.null, Val.retype]

/-- `generic.rules:1687` at a `uintptr`-typed `ConstNil` (a word argument, `argShapeOk`). -/
theorem inst_r_generic_1687_i64 : Rule.Inst GoFV.Rules.Generated.Generic.r_generic_1687
    (PEnv.ofLists [] [([], .bool)] (.int .w64) []) (Oracle.const true) := by
  simp [GoFV.Rules.Generated.Generic.r_generic_1687]
  rule_eval
  simp [PtrOps.isNonNil, Ptr.isNil, Ptr.null, Val.retype]

/-- `generic.rules:1689`: `(IsNonNil (Addr _) ) => (ConstBool [true])` -/
theorem r_generic_1689_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_1689 := by
  refine ⟨rfl, fun tabs e or _ => ?_⟩
  intro σ ev hfr hwf hcons hcond hty htyped hargs hnn
  simp only [GoFV.Rules.Generated.Generic.r_generic_1689, Pat.rawT, Pat.densT, Pat.denT,
    opVal_addr] at hty ⊢
  simp only [resDenT, nodeDenT, List.length_cons, List.length_nil, List.getElem?_cons_zero,
    List.map_nil]
  simp only [GoFV.Rules.Generated.Generic.r_generic_1689, Pat.argsOK, Pat.argsOKs, reduceArgShapeOk,
    Bool.and_eq_true, and_true, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, isPtrTy_iff,
    isInt64Ty_iff] at hargs
  obtain ⟨hr, -⟩ := wordShape_ptr hargs
  rw [opVal_pure (by decide)] at hty ⊢
  rw [opVal_pure (by decide)]
  simp only [hr] at hty ⊢
  have ha : Val.retype (.ptr none) (addrVal tabs (e.aux [0])) = .poison ∨
      ∃ n, Val.retype (.ptr none) (addrVal tabs (e.aux [0])) = .ptr ⟨.global n, 0⟩ := by
    unfold addrVal; split
    · exact .inr ⟨_, rfl⟩
    · exact .inl rfl
  have hc : (toAuxIntD Op.ConstBool.auxType (ev (Expr.lit GoTy.bool (Lit.bool true)))).getD
      (or.auxInt (Expr.lit GoTy.bool (Lit.bool true))) = 1 := by
    dsimp only [ev, evalE]; rfl
  rw [hc]
  rcases ha with ha | ⟨n, ha⟩ <;> rw [ha] at hty ⊢
  · exact .poison _
  · simp only [reduceEvalPure, PtrOps.isNonNil, Ptr.isNil] at hty ⊢
    have hb : (Blk.global n == Blk.nil) = false := rfl
    have hcb : Conv.constBool 1 = .bool true := rfl
    simp only [hb, Bool.false_and, Bool.not_false, hcb] at hty ⊢
    exact refines_retype_of_hasTy hty

/-- `generic.rules:1689` at `IsNonNil (Addr {go:string.hi} SB)`. -/
theorem inst_r_generic_1689 : Rule.InstT GoFV.Rules.Generated.Generic.r_generic_1689 hiSymTabs
    { leaf := fun _ => .poison
      ty := fun p => if p = [] then .bool else if p = [0] then .ptr (some 1) else .int .w64
      auxInt := fun _ => 0, aux := fun _ => some 1 }
    (Oracle.const true) := by
  refine ⟨Oracle.const_boolTyped true, ?_⟩
  simp [GoFV.Rules.Generated.Generic.r_generic_1689, FrameOK, Result.nodes, strDataVar?, lenVar?,
    sameLeaves, shiftAmt?, auxVar?, Pat.auxPos, Pat.auxPoss, Field.bindsVar, hiSymTabs,
    Tables.aux?, Pat.rawT, Pat.densT, Pat.denT, opVal, addrVal]
  rule_eval
  refine ⟨⟨fun ae x h => ?_, fun ae b h => ?_⟩, ?_⟩
  · subst h; simp
  · subst h; simp
  · simp [Val.retype, PtrOps.isNonNil, Ptr.word, Ptr.convertible, Ptr.inWindow, Blk.window?]

end GoFV.Proof.Rules
