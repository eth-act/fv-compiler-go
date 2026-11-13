import GoFV.Proof.Pass.RewriteTermNonNeg

variable [GoFV.SSA.Sem.Addrs]

/-!
# Integer-valued terms on the definitions (issue #69)

The rewrite validator decides structurally that a value is an integer or `poison` in every
evaluation (`GoFV.Opt.RewriteCheck.intD`: an op of `intTable` at an integer type, or a
`CondSelect`/`Copy` of such values). `intD_den`: then every evaluation of it as a term
(`GoFV.Proof.Term.den`, any fuel, any atom valuation) is one (`Intish`); `intDW_den`: at the
integer type of width `w`, an integer of width `w` or `poison`. It gives the `CondSelect` into
arithmetic rules (`generic.rules:2321–2394`) their leaf fact at 64 bits
(`GoFV.Proof.Rules.condMathFacts`), where the 64-bit integer shape may hold a pointer without
an integer form.
-/

namespace GoFV.Proof.Pass.Rewrite

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck GoFV.Proof.Term

/-- An integer (of any width) or `poison`. -/
def Intish (v : Val) : Prop := v = .poison ∨ ∃ w x, v = .int w x

theorem intish_int1 (w : Width) (f : BitVec w.bits → Val) (hf : ∀ x, Intish (f x))
    (args : List Val) : Intish (Sem.int1 w f args) := by
  unfold Sem.int1
  split
  · split
    · exact hf _
    · exact .inl rfl
  · exact .inl rfl

theorem intish_int2 (w : Width) (f : BitVec w.bits → BitVec w.bits → Val)
    (hf : ∀ x y, Intish (f x y)) (args : List Val) : Intish (Sem.int2 w f args) := by
  unfold Sem.int2
  split
  · split
    · exact hf _ _
    · exact .inl rfl
  · exact .inl rfl

theorem intish_shift (w a : Width) (b : Bool) (f : BitVec w.bits → Nat → BitVec w.bits)
    (args : List Val) : Intish (Shift.shift w a b f args) := by
  unfold Shift.shift
  split
  · split
    · split
      · exact .inl rfl
      · exact .inr ⟨_, _, rfl⟩
    · exact .inl rfl
  · exact .inl rfl

theorem intish_boolToUint8 (args : List Val) : Intish (Conv.boolToUint8 args) := by
  unfold Conv.boolToUint8
  split
  · split
    · exact .inr ⟨_, _, rfl⟩
    · exact .inl rfl
  · exact .inl rfl

/-- Every op of `intTable` evaluates to an integer or `poison`, on any arguments, and is a
term op evaluated by `evalPure`. -/
theorem intTable_sound : ∀ op ∈ intTable, (∀ ty ai ax args, Intish (evalPure op ty ai ax args)) ∧
    GoFV.Proof.Rules.frameOp op = false ∧ termOp op = true := by
  simp only [intTable, List.forall_mem_cons, List.forall_mem_nil, and_true]
  repeat' apply And.intro
  all_goals first
    | rfl
    | (intro _ h; simp at h)
    | (intro ty ai ax args
       first
       | exact .inr ⟨_, _, rfl⟩
       | exact intish_int2 _ _ (fun _ _ => .inr ⟨_, _, rfl⟩) args
       | exact intish_int1 _ _ (fun _ => .inr ⟨_, _, rfl⟩) args
       | exact intish_shift _ _ _ _ args
       | exact intish_boolToUint8 args)

theorem intTable_mem {op : Op} (h : intTable.contains op = true) : op ∈ intTable := by
  simpa using h

/-- A `CondSelect` of argument values whose first two are integers or `poison`. -/
theorem intish_condSelect {l : List ID} {f : ID → Val} {a b : ID} (ha : l[0]? = some a)
    (hb : l[1]? = some b) (h0 : Intish (f a)) (h1 : Intish (f b)) :
    Intish (Cmp.condSelect (l.map f)) := by
  unfold Cmp.condSelect
  split
  · rename_i x y c heq
    have hx := congrArg (·[0]?) heq
    have hy := congrArg (·[1]?) heq
    simp only [List.getElem?_map, ha, hb, Option.map_some, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.some.injEq] at hx hy
    subst hx hy
    split
    · exact h0
    · exact h1
    · exact .inl rfl
  · exact .inl rfl

/-- A `Copy` of an argument value that is an integer or `poison`. -/
theorem intish_copy {l : List ID} {f : ID → Val} {a : ID} (ha : l[0]? = some a)
    (h0 : Intish (f a)) : Intish (match l.map f with | [x] => x | _ => .poison) := by
  split
  · rename_i x heq
    have hx := congrArg (·[0]?) heq
    simp only [List.getElem?_map, ha, Option.map_some, List.getElem?_cons_zero,
      Option.some.injEq] at hx
    subst hx
    exact h0
  · exact .inl rfl

/-- A `retype` at an integer shape keeps an integer or `poison` one. -/
theorem intish_retype {v : Val} (hv : Intish v) (w : Width) : Intish (v.retype (.int w)) := by
  rcases hv with rfl | ⟨w', x, rfl⟩
  · exact .inl rfl
  · simp only [Val.retype]
    split
    · exact .inr ⟨_, _, rfl⟩
    · exact .inl rfl

/-- A `retype` at the integer shape of width `w` of an integer or `poison` is an integer of
width `w` or `poison`. -/
theorem intAt_retype {v : Val} (hv : Intish v) (w : Width) :
    v.retype (.int w) = .poison ∨ ∃ x, v.retype (.int w) = .int w x := by
  rcases hv with rfl | ⟨w', x, rfl⟩
  · exact .inl rfl
  · simp only [Val.retype]
    split
    · exact .inr ⟨_, rfl⟩
    · exact .inl rfl

theorem isIntTy_eq {t : Ty} (h : isIntTy t = true) : ∃ w, t = .int w := by
  unfold isIntTy at h
  split at h
  · exact ⟨_, rfl⟩
  · cases h

/-- The value of an `intD` node before its type's `retype`: an integer or `poison`. -/
theorem intD_pre (tabs : Tables) (D : ID → Option Value) (ρ : ID → Val) {k n : Nat} {x : ID}
    {v : Value} (hD : D x = some v) (h : intD tabs D (k + 1) x = true)
    (IH : ∀ y, intD tabs D k y = true → Intish (den D tabs ρ n y)) :
    termOp v.op = true ∧ (∃ w, tabs.ty v.type = .int w) ∧
      Intish (GoFV.Proof.Rules.opVal tabs v.op (tabs.ty v.type) v.auxInt v.aux
        (v.args.toList.map (den D tabs ρ n))) := by
  simp only [intD, hD, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  obtain ⟨⟨ht, hint⟩, h⟩ := h
  refine ⟨ht, isIntTy_eq hint, ?_⟩
  rcases h with (hop | ⟨hop, h⟩) | ⟨hop, h⟩
  · obtain ⟨hsem, hfr, -⟩ := intTable_sound _ (intTable_mem hop)
    rw [GoFV.Proof.Rules.opVal_pure hfr]
    exact hsem _ _ _ _
  · have hfr : GoFV.Proof.Rules.frameOp v.op = false := by rw [hop]; rfl
    rw [GoFV.Proof.Rules.opVal_pure hfr, hop]
    revert h
    cases ha : v.args[0]? with
    | none => intro h; cases h
    | some a =>
      cases hb : v.args[1]? with
      | none => intro h; cases h
      | some b =>
        intro h
        simp only [Bool.and_eq_true] at h
        exact intish_condSelect (by simpa using ha) (by simpa using hb) (IH _ h.1) (IH _ h.2)
  · have hfr : GoFV.Proof.Rules.frameOp v.op = false := by rw [hop]; rfl
    rw [GoFV.Proof.Rules.opVal_pure hfr, hop]
    revert h
    cases ha : v.args[0]? with
    | none => intro h; cases h
    | some a =>
      intro h
      exact intish_copy (by simpa using ha) (IH _ h)

/-- **`intD` decided on the definitions is a fact about every evaluation**: an integer or
`poison`. -/
theorem intD_den (tabs : Tables) (D : ID → Option Value) (ρ : ID → Val) :
    ∀ k n x, intD tabs D k x = true → Intish (den D tabs ρ n x)
  | 0, _, _, h => by simp [intD] at h
  | _ + 1, 0, _, _ => .inl rfl
  | k + 1, n + 1, x, h => by
    cases hD : D x with
    | none => simp [intD, hD] at h
    | some v =>
      obtain ⟨ht, ⟨w, hw⟩, hpre⟩ := intD_pre tabs D ρ hD h (intD_den tabs D ρ k n)
      simp only [den, hD, ht, ite_true]
      rw [hw] at hpre ⊢
      exact intish_retype hpre w

/-- `intDW`: every evaluation is an integer of width `w` or `poison`. -/
theorem intDW_den (tabs : Tables) (D : ID → Option Value) (ρ : ID → Val) {w : Width} {k : Nat}
    {x : ID} (h : intDW tabs D w k x = true) (n : Nat) :
    den D tabs ρ n x = .poison ∨ ∃ y, den D tabs ρ n x = .int w y := by
  unfold intDW at h
  cases hD : D x with
  | none => rw [hD] at h; cases h
  | some v =>
    rw [hD] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨hw, h⟩ := h
    cases n with
    | zero => exact .inl rfl
    | succ n =>
      cases k with
      | zero => simp [intD] at h
      | succ k =>
        obtain ⟨ht, -, hpre⟩ := intD_pre tabs D ρ hD h (intD_den tabs D ρ k n)
        simp only [den, hD, ht, ite_true]
        rw [isIntW_eq hw] at hpre ⊢
        exact intAt_retype hpre w

/-- A value of an integer shape narrower than 64 bits is an integer of that width or `poison`
(a pointer has no narrow integer shape). -/
theorem intAt_of_hasTy {v : Val} {w : Width} (h : v.hasTy (.int w) = true) (hw : w ≠ .w64) :
    v = .poison ∨ ∃ x, v = .int w x := by
  cases v with
  | poison => exact .inl rfl
  | int w' x =>
    simp only [Val.hasTy, beq_iff_eq] at h
    subst h
    exact .inr ⟨x, rfl⟩
  | ptr p => cases w <;> simp_all [Val.hasTy]
  | _ => simp [Val.hasTy] at h

/-- `intLeafD`: every evaluation of the leaf is an integer of width `w` or `poison`. -/
theorem intLeafD_den (tabs : Tables) (D : ID → Option Value) (ρ : ID → Val)
    (hT : Term.Typed D tabs ρ) {w : Width} {x : ID} (h : intLeafD tabs D w x = true) (n : Nat) :
    den D tabs ρ n x = .poison ∨ ∃ y, den D tabs ρ n x = .int w y := by
  unfold intLeafD at h
  split at h
  · rename_i hw
    subst hw
    exact intDW_den tabs D ρ h n
  · rename_i hw
    cases hD : D x with
    | none => rw [hD] at h; cases h
    | some v =>
      rw [hD] at h
      have ht := den_hasTy hT n hD
      rw [isIntW_eq h] at ht
      exact intAt_of_hasTy ht hw

end GoFV.Proof.Pass.Rewrite
