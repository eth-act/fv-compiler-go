import GoFV.Proof.Rules.ConstString
import GoFV.Proof.Rules.SelMake

/-!
# Rule lemma: the masked slice pointer (`generic.rules:1053`)

`(SliceMake (AddPtr <t> x (And64 y (Slicemask _))) w:(Const64 [c]) z) && c > 0 =>
(SliceMake (AddPtr <t> x y) w z)` under `Rule.SoundT` (`DenT.lean`). Go's justification ("len >
0 implies cap > 0 implies Slicemask is all 1") needs the `Slicemask` argument to be the
capacity `z`, which the pattern does not say: `sameLeaves` names the two positions and
`FrameOK` makes them equal (the rewrite validator checks it on the instance,
`RewriteCheck.condFrameOK`). `Pat.argsOK` gives the `SliceMake` a slice shape, so the matched
value having it (`hty`) means `0 ≤ len ≤ cap`; `c > 0` makes the capacity positive, its
`Slicemask` all ones (or no 64-bit integer at the `Slicemask`'s type), and `y & -1` is `y` or
`poison` (`and64_allOnes_or`). Both slices then agree, except that the matched pointer may be
`poison`.
-/

namespace GoFV.Proof.Rules

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules

/-- `AddPtr` of a `poison` offset is `poison`. -/
theorem addPtr_poison (x : Val) : PtrOps.addPtr [x, .poison] = .poison := by
  cases x with
  | int w v => cases w <;> rfl
  | _ => rfl

/-- A `Slicemask` of a positive 64-bit integer, retyped at any shape, read as a 64-bit
integer: all ones, or no 64-bit integer. -/
theorem slicemask_pos_asInt (T : Ty) {c : BitVec 64} (hc : c.msb = false) (h0 : c ≠ 0) :
    (Val.retype T (match T.width? with
      | some w => Int.slicemask w [.int .w64 c]
      | none => .poison)).asInt .w64 = none ∨
    (Val.retype T (match T.width? with
      | some w => Int.slicemask w [.int .w64 c]
      | none => .poison)).asInt .w64 = some (-1) := by
  cases T with
  | int w =>
    cases w
    case w64 =>
      right
      have hm : Int.slicemask .w64 [.int .w64 c] = .int .w64 (-1) := by
        simp only [Int.slicemask, int1, Val.asInt_int, hc, h0, Bool.false_eq_true, ↓reduceIte]
      show (Val.retype (.int .w64) (Int.slicemask .w64 [.int .w64 c])).asInt .w64 = _
      rw [hm, Val.retype_of_hasTy rfl, Val.asInt_int]
    all_goals (left; rfl)
  | _ => left; rfl

/-- `And64` with a value that is all ones or no 64-bit integer: `poison`, or the other
argument, a 64-bit integer. -/
theorem and64_allOnes_or {y s : Val}
    (h : s.asInt .w64 = none ∨ s.asInt .w64 = some (-1)) :
    Int.and .w64 [y, s] = .poison ∨ ∃ v, y = .int .w64 v ∧ Int.and .w64 [y, s] = y := by
  unfold Int.and int2
  rcases h with h | h
  · left; simp [h]
  · cases y with
    | int w v =>
      cases w
      case w64 =>
        right; refine ⟨v, rfl, ?_⟩
        dsimp only
        rw [Val.asInt_int, h]
        simp [BitVec.neg_one_eq_allOnes]
      all_goals (left; dsimp only; rw [h]; simp [Val.asInt])
    | _ => left; dsimp only; rw [h]; simp [Val.asInt]

theorem r_generic_1053_sound : Rule.SoundT GoFV.Rules.Generated.Generic.r_generic_1053 := by
  refine ⟨rfl, fun tabs e or _ => ?_⟩
  intro σ ev hfr hwf hcons hcond hty htyped hargs hnn
  have hz : e.leaf [0, 1, 1, 0] = e.leaf [2] :=
    hfr.2.2.2.2 ([0, 1, 1, 0], [2]) (by simp [GoFV.Rules.Generated.Generic.r_generic_1053, sameLeaves])
  clear hfr
  simp only [GoFV.Rules.Generated.Generic.r_generic_1053, Pat.rawT, Pat.densT, Pat.denT,
    opVal, reduceCtorEq, ite_false, reduceEvalPure, hz, Nat.zero_add, Nat.reduceAdd] at hty ⊢
  simp only [resDenT, nodeDenT, List.length_cons, List.length_nil, List.getElem?_cons_zero,
    List.getElem?_cons_succ, List.map_cons, List.map_nil, opVal, reduceCtorEq, ite_false,
    reduceEvalPure]
  simp only [GoFV.Rules.Generated.Generic.r_generic_1053, Pat.argsOK, Pat.argsOKs, argShapeOk,
    Nat.zero_add, beq_self_eq_true, ↓reduceIte, Nat.reduceBEq, Nat.reduceBNe, Bool.false_or,
    Bool.and_eq_true, and_true, Bool.false_eq_true, Nat.reduceAdd] at hargs
  simp only [GoFV.Rules.Generated.Generic.r_generic_1053, Pat.typed, Pat.typeds,
    Nat.zero_add, and_true, Nat.reduceAdd] at htyped
  obtain ⟨⟨⟨hS, h0⟩, ⟨-, hA⟩, hAnd, -, -, -⟩, ⟨-, h1⟩, -, h2⟩ := hargs
  obtain ⟨el, hS⟩ := isSliceTy_iff.1 hS
  rw [hS] at h0 h1 h2 hty ⊢
  obtain ⟨elA, hA⟩ := isPtrTy_iff.1 hA
  rw [int64_of_makeArgOk h1 (.inl rfl)] at hty ⊢
  rw [isInt64Ty_iff.1 hAnd] at hty ⊢
  have hs0 : ev (.var 0) = .ty (e.ty [0]) := by
    simp [ev, evalE, σ, sigmaT, Pat.bindsT, Pat.bindssT, GoFV.Rules.Generated.Generic.r_generic_1053]
  have hs1 : (σ 1).valOr (or.val (Expr.var 1)) = e.leaf [0, 0] := by
    simp [σ, sigmaT, Pat.bindsT, Pat.bindssT, GoFV.Rules.Generated.Generic.r_generic_1053,
      DV.valOr, List.lookup, Pat.denT]
  have hs2 : (σ 2).valOr (or.val (Expr.var 2)) = e.leaf [0, 1, 0] := by
    simp [σ, sigmaT, Pat.bindsT, Pat.bindssT, GoFV.Rules.Generated.Generic.r_generic_1053,
      DV.valOr, List.lookup, Pat.denT]
  have hs4 : (σ 4).valOr (or.val (Expr.var 4)) =
      Val.retype (e.ty [1]) (Conv.const Width.w64 (e.auxInt [1])) := by
    simp [σ, sigmaT, Pat.bindsT, Pat.bindssT, GoFV.Rules.Generated.Generic.r_generic_1053,
      DV.valOr, List.lookup, Pat.denT, Pat.densT, opVal, reduceEvalPure]
  have hs5 : (σ 5).valOr (or.val (Expr.var 5)) = e.leaf [2] := by
    simp [σ, sigmaT, Pat.bindsT, Pat.bindssT, GoFV.Rules.Generated.Generic.r_generic_1053,
      DV.valOr, List.lookup, Pat.denT]
  dsimp only [condHolds, GoFV.Rules.Generated.Generic.r_generic_1053, rule_unfold_ds] at hcond
  try simp only [rule_helper, rule_unfold_s] at hcond
  rw [hs0, hs1, hs2, hs4, hs5, int64_of_makeArgOk h1 (.inl rfl), hA]
  rw [hA] at hty
  dsimp only
  have hpos : 0 < (e.auxInt [1]).toInt := by
    simpa [ev, evalE, σ, sigmaT, Pat.bindsT, Pat.bindssT,
      GoFV.Rules.Generated.Generic.r_generic_1053, List.lookup, auxIntDV, binE, litDV, binDV,
      intBin] using hcond
  have hL : Val.retype (.int .w64) (Conv.const .w64 (e.auxInt [1])) =
      .int .w64 (BitVec.ofInt 64 (e.auxInt [1]).toInt) := Val.retype_of_hasTy rfl
  rw [hL] at hty ⊢
  generalize e.leaf [2] = C at hty ⊢
  generalize hP : Val.retype (.ptr elA) (PtrOps.addPtr [e.leaf [0, 0], e.leaf [0, 1, 0]]) = P'
  have hmake : ∀ vs, Comp.make vs = .agg vs := fun _ => rfl
  rw [hmake] at hty
  rw [hmake, hmake]
  obtain ⟨p, l, c, heq, -, hl, hcm, hlc⟩ := Val.hasTy_agg_slice.1 hty
  simp only [List.cons.injEq, Val.int.injEq, heq_eq_eq, true_and, and_true] at heq
  obtain ⟨-, hlv, rfl⟩ := heq
  have hl0 : l.toNat ≠ 0 := by
    rw [← hlv, BitVec.toNat_ofInt]
    have h1 := Int64.toInt_le (e.auxInt [1])
    have h2 : Int64.maxValue.toInt = 2 ^ 63 - 1 := by decide
    simp only [Width.bits] at h1 ⊢
    omega
  have hc0 : c ≠ 0 := by
    intro h; subst h; simp at hlc; exact hl0 hlc
  generalize hs : Val.retype (e.ty [1, 1, 0]) _ = s at hty ⊢
  have hsA : s.asInt .w64 = none ∨ s.asInt .w64 = some (-1) := by
    rw [← hs]; exact slicemask_pos_asInt _ hcm hc0
  rcases and64_allOnes_or (y := e.leaf [0, 1, 0]) hsA with h | ⟨v, hy, h⟩ <;> rw [h] at hty ⊢
  · have hr0 : Val.retype (.int .w64) .poison = .poison := rfl
    have hr1 : Val.retype (.ptr elA) .poison = .poison := rfl
    rw [hr0, addPtr_poison, hr1, hlv]
    have hok : Val.sliceOK [P'.retypePtr, .int .w64 l, .int .w64 c] = true := by
      simp [Val.sliceOK, hl, hcm, BitVec.ule, hlc]
    have hr : Val.retype (.slice el) (.agg [P', .int .w64 l, .int .w64 c]) =
        .agg [P'.retypePtr, .int .w64 l, .int .w64 c] := by
      show Val.ofSlice [P'.retypePtr, (Val.int .w64 l).retypeI64, (Val.int .w64 c).retypeI64] = _
      rw [Val.retypeI64_int, Val.retypeI64_int, Val.ofSlice_of_ok hok]
    rw [hr]
    exact .agg (.cons (.poison _) (.cons (Refines.refl _) (.cons (Refines.refl _) .nil)))
  · rw [hy] at hP hty ⊢
    have hr : Val.retype (.int .w64) (.int .w64 v) = .int .w64 v := Val.retype_of_hasTy rfl
    rw [hr, hP] at hty ⊢
    rw [Val.retype_of_hasTy hty]
    exact Refines.refl _

/-! ## Non-vacuity -/

theorem inst_r_generic_1053 : Rule.InstT GoFV.Rules.Generated.Generic.r_generic_1053 {}
    { leaf := fun p => if p = [0, 0] then .int .w64 (2 ^ 40) else
        if p = [0, 1, 0] then .int .w64 8 else .int .w64 5
      ty := fun p => if p = [] then .slice none else
        if p = [0] ∨ p = [0, 0] then .ptr none else .int .w64
      auxInt := fun p => if p = [1] then 3 else 0, aux := fun _ => none }
    (Oracle.const true) := by
  refine ⟨Oracle.const_boolTyped true, ?_⟩
  simp [GoFV.Rules.Generated.Generic.r_generic_1053, FrameOK, Result.nodes, samePtrVars,
    sameLeaves, numElem1Vars, shiftAmt?, Pat.leafPos, Pat.leafPoss, Pat.rawT, Pat.densT, Pat.denT,
    emptyStrVars, opVal]
  rule_eval
  simp [sigmaT, Pat.bindsT, Pat.bindssT, List.lookup, auxIntDV, Comp.make]

end GoFV.Proof.Rules
