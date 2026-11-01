import GoFV.Proof.AtomSimDen

/-!
# Term denotations: monotonicity, shapes and copies (issue #113)

Facts about `GoFV.Proof.Term.den` used by the soundness proof of the rewrite validator
(`GoFV.Proof.Pass.RewriteTerm`): `den` is monotone in the fuel and the valuation
(`den_mono`), every denotation is fixed by `retype` at its value's shape under `Typed`
(`den_retype`), so it has a sized shape (`den_hasTy`), and a value reached through compatible
`Copy`s (`copyReach`) has a larger denotation at the same fuel (`copyReach_den`).
-/

namespace GoFV.Proof.Pass.Rewrite

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck GoFV.Proof.Term GoFV.Proof.AtomSim

/-! ## Type shapes -/

mutual
theorem tyEq_sound : ∀ {a b : Ty}, GoFV.Opt.CSE.tyEq a b = true → a = b
  | .int w, .int w', h => by simp only [GoFV.Opt.CSE.tyEq, beq_iff_eq] at h; rw [h]
  | .bool, .bool, _ | .mem, .mem, _ | .other, .other, _ | .empty, .empty, _ => rfl
  | .tuple ts, .tuple ts', h => by
    simp only [GoFV.Opt.CSE.tyEq] at h; rw [tysEq_sound h]
  | .ptr e, .ptr e', h => by simp only [GoFV.Opt.CSE.tyEq, beq_iff_eq] at h; rw [h]
  | .agg fs n, .agg fs' n', h => by
    simp only [GoFV.Opt.CSE.tyEq, Bool.and_eq_true, beq_iff_eq] at h
    rw [fieldsEq_sound h.1, h.2]
  | .blob n, .blob n', h => by simp only [GoFV.Opt.CSE.tyEq, beq_iff_eq] at h; rw [h]
  | .opaque n, .opaque n', h => by simp only [GoFV.Opt.CSE.tyEq, beq_iff_eq] at h; rw [h]
  | .int _, .bool, h | .int _, .mem, h | .int _, .tuple _, h | .int _, .other, h
  | .int _, .ptr _, h | .int _, .agg _ _, h | .int _, .blob _, h | .int _, .empty, h
  | .int _, .opaque _, h
  | .bool, .int _, h | .bool, .mem, h | .bool, .tuple _, h | .bool, .other, h
  | .bool, .ptr _, h | .bool, .agg _ _, h | .bool, .blob _, h | .bool, .empty, h
  | .bool, .opaque _, h
  | .mem, .int _, h | .mem, .bool, h | .mem, .tuple _, h | .mem, .other, h
  | .mem, .ptr _, h | .mem, .agg _ _, h | .mem, .blob _, h | .mem, .empty, h
  | .mem, .opaque _, h
  | .tuple _, .int _, h | .tuple _, .bool, h | .tuple _, .mem, h | .tuple _, .other, h
  | .tuple _, .ptr _, h | .tuple _, .agg _ _, h | .tuple _, .blob _, h | .tuple _, .empty, h
  | .tuple _, .opaque _, h
  | .other, .int _, h | .other, .bool, h | .other, .mem, h | .other, .tuple _, h
  | .other, .ptr _, h | .other, .agg _ _, h | .other, .blob _, h | .other, .empty, h
  | .other, .opaque _, h
  | .ptr _, .int _, h | .ptr _, .bool, h | .ptr _, .mem, h | .ptr _, .tuple _, h
  | .ptr _, .other, h | .ptr _, .agg _ _, h | .ptr _, .blob _, h | .ptr _, .empty, h
  | .ptr _, .opaque _, h
  | .agg _ _, .int _, h | .agg _ _, .bool, h | .agg _ _, .mem, h | .agg _ _, .tuple _, h
  | .agg _ _, .other, h | .agg _ _, .ptr _, h | .agg _ _, .blob _, h | .agg _ _, .empty, h
  | .agg _ _, .opaque _, h
  | .blob _, .int _, h | .blob _, .bool, h | .blob _, .mem, h | .blob _, .tuple _, h
  | .blob _, .other, h | .blob _, .ptr _, h | .blob _, .agg _ _, h | .blob _, .empty, h
  | .blob _, .opaque _, h
  | .empty, .int _, h | .empty, .bool, h | .empty, .mem, h | .empty, .tuple _, h
  | .empty, .other, h | .empty, .ptr _, h | .empty, .agg _ _, h | .empty, .blob _, h
  | .empty, .opaque _, h
  | .opaque _, .int _, h | .opaque _, .bool, h | .opaque _, .mem, h | .opaque _, .tuple _, h
  | .opaque _, .other, h | .opaque _, .ptr _, h | .opaque _, .agg _ _, h
  | .opaque _, .blob _, h | .opaque _, .empty, h => by simp [GoFV.Opt.CSE.tyEq] at h
theorem tysEq_sound : ∀ {a b : List Ty}, GoFV.Opt.CSE.tysEq a b = true → a = b
  | [], [], _ => rfl
  | t :: ts, t' :: ts', h => by
    simp only [GoFV.Opt.CSE.tysEq, Bool.and_eq_true] at h
    rw [tyEq_sound h.1, tysEq_sound h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [GoFV.Opt.CSE.tysEq] at h
theorem fieldsEq_sound : ∀ {a b : List (Nat × Ty)}, GoFV.Opt.CSE.fieldsEq a b = true → a = b
  | [], [], _ => rfl
  | (o, t) :: fs, (o', t') :: fs', h => by
    simp only [GoFV.Opt.CSE.fieldsEq, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1.1, tyEq_sound h.1.2, fieldsEq_sound h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [GoFV.Opt.CSE.fieldsEq] at h
end

theorem retype_other (v : Val) : v.retype .other = v := by
  cases v <;> rfl

theorem retype_poison (t : Ty) : Val.poison.retype t = .poison := by
  cases t with
  | int w => cases w <;> rfl
  | _ => rfl

theorem retype_ptr_elem (e e' : Option Nat) (v : Val) : v.retype (.ptr e) = v.retype (.ptr e') := by
  cases v with
  | int w _ => cases w <;> rfl
  | _ => rfl

/-- A `Copy` of a compatible shape (`copyCompat`) is the identity on a value fixed by its
argument's shape. -/
theorem retype_copyCompat {s t : Ty} (h : copyCompat s t = true) {z : Val} (hz : z.retype t = z) :
    z.retype s = z := by
  unfold copyCompat at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · rw [tyEq_sound h, hz]
  · simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases s <;> simp at h1
    cases t <;> simp at h2
    rename_i e e'
    rw [retype_ptr_elem e e', hz]

/-- Integer and boolean shapes (the shapes of rule leaves, `leavesOK`). -/
def sized : Ty → Bool
  | .int _ | .bool => true
  | _ => false

/-- A value retyped at an integer or boolean shape has that shape. -/
theorem retype_hasTy (hr : RetypeShapes) (v : Val) {s : Ty} (hs : sized s = true) :
    (v.retype s).hasTy s = true := by
  rcases s with w | _ | _ | _ | _ | _ | _ | _ | _ | _ <;> simp [sized] at hs
  · exact hr v w
  · cases v <;> rfl

/-! ## `den` -/

/-- `den` is monotone in the fuel and the valuation. -/
theorem den_mono (D : ID → Option Value) (tabs : Tables) {ρ ρ' : ID → Val} (hρ : ValRef ρ ρ') :
    ∀ (n m : Nat) (x : ID), n ≤ m → Sem.Refines (den D tabs ρ n x) (den D tabs ρ' m x)
  | 0, _, _, _ => .poison _
  | n + 1, 0, _, h => absurd h (by omega)
  | n + 1, m + 1, x, h => by
    by_cases ht : IsTerm D x
    · obtain ⟨v, hx, hv⟩ := ht
      rw [den_succ_term hx hv, den_succ_term hx hv]
      exact retype_mono _ (evalPure_mono _ _ _ _
        (refinesList_map fun a _ => den_mono D tabs hρ n m a (by omega)))
    · rw [den_succ_atom ht, den_succ_atom ht]; exact hρ x

/-- Under `Typed`, a denotation is fixed by `retype` at its value's shape. -/
theorem den_retype {D : ID → Option Value} {tabs : Tables} {ρ : ID → Val} (hT : Term.Typed D tabs ρ) :
    ∀ (k : Nat) (a : ID), (den D tabs ρ k a).retype (shape D tabs a) = den D tabs ρ k a
  | 0, _ => retype_poison _
  | k + 1, a => by
    by_cases ht : IsTerm D a
    · obtain ⟨v, hv, hop⟩ := ht
      rw [den_succ_term hv hop]
      simp only [shape, hv, Option.map_some, Option.getD_some]
      exact GoFV.Proof.retype_idem _ _
    · rw [den_succ_atom ht]; exact hT a ht

theorem shape_of {D : ID → Option Value} {tabs : Tables} {a : ID} {y : Value} (h : D a = some y) :
    shape D tabs a = tabs.ty y.type := by
  simp only [shape, h, Option.map_some, Option.getD_some]

theorem den_hasTy (hr : RetypeShapes) {D : ID → Option Value} {tabs : Tables} {ρ : ID → Val}
    (hT : Term.Typed D tabs ρ) (k : Nat) (a : ID) {s : Ty} (hsa : shape D tabs a = s)
    (hs : sized s = true) : (den D tabs ρ k a).hasTy s = true := by
  rw [← den_retype hT k a, hsa]
  exact retype_hasTy hr _ hs

theorem termOp_copy : termOp .Copy = true := by decide

theorem toList_of_size_one {α : Type} [Inhabited α] {a : Array α} (h : a.size = 1) :
    a.toList = [a[0]!] := by
  rcases a with ⟨l⟩
  match l, h with
  | [b], _ => rfl

/-- The denotation of a `Copy` of a compatible shape is its argument's, one fuel lower. -/
theorem den_copy {D : ID → Option Value} {tabs : Tables} {ρ : ID → Val} (hT : Term.Typed D tabs ρ)
    {a : ID} {x y : Value} (hx : D a = some x) (hop : x.op = .Copy) (hsz : x.args.size = 1)
    (hy : D x.args[0]! = some y) (hc : copyCompat (tabs.ty x.type) (tabs.ty y.type) = true)
    (k : Nat) : den D tabs ρ (k + 1) a = den D tabs ρ k x.args[0]! := by
  rw [den_succ_term hx (by rw [hop]; exact termOp_copy), toList_of_size_one hsz, hop]
  show (den D tabs ρ k x.args[0]!).retype (tabs.ty x.type) = _
  apply retype_copyCompat hc
  rw [← shape_of (tabs := tabs) hy]
  exact den_retype hT k _

/-- A value reached through compatible copies has a larger denotation at the same fuel. -/
theorem copyReach_den {M : Defs} {tabs : Tables} {ρ : ID → Val} (hT : Term.Typed M.get? tabs ρ) :
    ∀ (N : Nat) (a w : ID), copyReach tabs M N a w = true →
      ∀ k, Sem.Refines (den M.get? tabs ρ k a) (den M.get? tabs ρ k w)
  | 0, a, w, h, k => by
    simp only [copyReach, beq_iff_eq] at h; subst h; exact Sem.Refines.refl _
  | N + 1, a, w, h, k => by
    simp only [copyReach, Bool.or_eq_true, beq_iff_eq] at h
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
            rw [den_copy hT hx hop hsz hy' hy k]
            exact Sem.Refines.trans (den_fuel_mono _ _ _ k (k + 1) _ (by omega))
              (copyReach_den hT N _ w hr (k + 1))

end GoFV.Proof.Pass.Rewrite
