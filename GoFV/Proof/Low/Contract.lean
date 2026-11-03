import GoFV.Proof.Low.RuleL
import GoFV.Opt.FmaContract

/-!
# The contraction relation (decision on #384, issue #385)

`Contract f f'`: `f'` is `f` with some of its values that have one of the twelve `useFMA` rule
shapes (`GoFV.Opt.FmaContract.fmaOf`) replaced by the rule's fused multiply-add
(`GoFV.Opt.FmaContract.contractAt`). The `lower` theorem holds up to it
(`GoFV.Proof.Low.lower_refines`). A contracted generic function's atoms are its own, so they are
generic (`contractAll_atoms`): the fused values are terms (`termVL`).
-/

namespace GoFV.Proof.Low

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.FmaContract

/-- `f'` is a contraction of `f` at the `useFMA` shapes. -/
def Contract (f f' : Func) : Prop := ∃ C, f' = contractAt f C

theorem Contract.refl_of {f : Func} (h : contractAt f [] = f) : Contract f f := ⟨[], h.symm⟩

/-- The ops `fmaOf` produces. -/
def fusedOp (o : Op) : Bool :=
  o == .ARM64FMADDD || o == .ARM64FMADDS || o == .ARM64FMSUBD || o == .ARM64FMSUBS ||
  o == .ARM64FNMADDD || o == .ARM64FNMADDS || o == .ARM64FNMSUBD || o == .ARM64FNMSUBS

theorem fusedOp_ite (c : Bool) {a b : Op} (ha : fusedOp a = true) (hb : fusedOp b = true) :
    fusedOp (if c then a else b) = true := by cases c <;> assumption

theorem fusedOp_fmadd (d : Bool) : fusedOp (fmadd d) = true := by cases d <;> rfl
theorem fusedOp_fmsub (d : Bool) : fusedOp (fmsub d) = true := by cases d <;> rfl
theorem fusedOp_fnmadd (d : Bool) : fusedOp (fnmadd d) = true := by cases d <;> rfl
theorem fusedOp_fnmsub (d : Bool) : fusedOp (fnmsub d) = true := by cases d <;> rfl

theorem fmaOf_op {f : Func} {v w : Value} (h : fmaOf f v = some w) : fusedOp w.op = true := by
  unfold fmaOf at h
  simp only at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h
       first
         | exact fusedOp_fmsub _ | exact fusedOp_fmadd _ | exact fusedOp_fnmadd _
         | exact fusedOp_fnmsub _
         | exact fusedOp_ite _ (fusedOp_fmsub _) (fusedOp_fmadd _)
         | exact fusedOp_ite _ (fusedOp_fmadd _) (fusedOp_fmsub _)
         | exact fusedOp_ite _ (fusedOp_fnmadd _) (fusedOp_fnmsub _))

/-- An `armTerm` op that is neither generic, `MOVDaddr`, an activation op nor a root is a term. -/
theorem termVL_of_arm (tabs : Tables) {w : Value}
    (h : (!w.op.generic && w.op != .ARM64MOVDaddr && GoFV.Opt.LowerTerm.armTerm w.op &&
      !GoFV.Opt.LowerTerm.actOp w.op && !isRoot w.op) = true) : termVL tabs w = true := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨hg, hm⟩, ha⟩, hact⟩, hr⟩ := h
  unfold termVL
  have hm' : (w.op == .ARM64MOVDaddr) = false := by simpa using hm
  simp only [hg, hm', ha, hact, hr, ldOp?_of_act hact, Option.isSome_none, Bool.false_eq_true,
    ite_false, Bool.not_false, Bool.and_self]

/-- A fused op is a term of lowered SSA. -/
theorem termVL_fused (tabs : Tables) {w : Value} (h : fusedOp w.op = true) : termVL tabs w = true := by
  unfold fusedOp at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with ((((((h | h) | h) | h) | h) | h) | h) | h <;>
    exact termVL_of_arm tabs (by rw [h]; decide)

/-- The values of a contraction: the input's, or a fused value of one. -/
theorem contractAt_value {f : Func} {C : List ID} {x : ID} {u : Value}
    (h : (contractAt f C).value? x = some u) :
    f.value? x = some u ∨ (∃ v, f.value? x = some v ∧ fmaOf f v = some u) := by
  unfold contractAt Func.value? at h
  simp only [Array.getElem?_mapIdx, Option.join_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨o, ho, hu⟩ := h
  cases o with
  | none => cases hu
  | some v =>
    unfold Func.value?
    simp only [ho, Option.join_some]
    dsimp only at hu
    split at hu
    · cases hf : fmaOf f v with
      | none => rw [hf] at hu; cases hu; exact .inl rfl
      | some w => rw [hf] at hu; cases hu; exact .inr ⟨v, rfl, hf⟩
    · cases hu; exact .inl rfl

/-- The atoms of a contraction of a generic function are generic. -/
theorem contractAt_atoms {f : Func} (hf : f.lowered = false) (C : List ID) (tabs : Tables)
    {x : ID} {u : Value} (hx : (contractAt f C).value? x = some u) (ht : termVL tabs u = false) :
    u.op.generic = true := by
  rcases contractAt_value hx with h | ⟨v, -, hw⟩
  · exact Func.generic_of_lowered hf h
  · rw [termVL_fused tabs (fmaOf_op hw)] at ht; cases ht

end GoFV.Proof.Low
