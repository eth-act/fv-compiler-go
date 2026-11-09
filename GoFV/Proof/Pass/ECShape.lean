import GoFV.Proof.Pass.ECDefs
import GoFV.Proof.Retype
import GoFV.Proof.Eval

variable [GoFV.SSA.Sem.Addrs]

/-!
# Shapes up to pointers' element sizes (issue #28)

`ECCheck.eqE` compares shapes with every pointer's element size forgotten (`ECCheck.erase`):
`hasTy` and `retype` do not look at it (`hasTy_erase`, `retype_erase`), so shapes that are
`eqE` type values alike (`eqE_hasTy`, `eqE_retype`). `shapeOf_eq`: the shape the checker reads
for a value is the one the semantics uses (`Ctx.tys`).
-/

namespace GoFV.Proof.EC

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.ECCheck

mutual
theorem hasTy_erase : ∀ (t : Ty) (v : Val), v.hasTy (erase t) = v.hasTy t
  | .ptr _, v => by
    cases v with
    | int w x => cases w <;> rfl
    | _ => rfl
  | .agg fs n, v => by
    cases v with
    | agg vs =>
      simp only [erase, Val.hasTy]
      exact hasTyList_eraseFields fs vs
    | _ => rfl
  | .tuple ts, v => by
    cases v with
    | tuple vs =>
      simp only [erase, Val.hasTy]
      exact hasTyPre_eraseList ts vs
    | _ => rfl
  | .int _, v => rfl
  | .bool, v => rfl
  | .mem, v => rfl
  | .other, v => rfl
  | .blob _, v => rfl
  | .empty, v => rfl
  | .opaque _, v => rfl
  | .str, v => rfl
  | .slice _, v => by cases v <;> rfl
theorem hasTyList_eraseFields : ∀ (fs : List (Nat × Ty)) (vs : List Val),
    Val.hasTyList vs ((eraseFields fs).map (·.2)) = Val.hasTyList vs (fs.map (·.2))
  | [], vs => rfl
  | (o, t) :: fs, [] => rfl
  | (o, t) :: fs, v :: vs => by
    simp only [eraseFields, List.map_cons, Val.hasTyList]
    rw [hasTy_erase t v, hasTyList_eraseFields fs vs]
theorem hasTyPre_eraseList : ∀ (ts : List Ty) (vs : List Val),
    Val.hasTyPre vs (eraseList ts) = Val.hasTyPre vs ts
  | [], vs => by cases vs <;> rfl
  | t :: ts, [] => rfl
  | t :: ts, v :: vs => by
    simp only [eraseList, Val.hasTyPre]
    rw [hasTy_erase t v, hasTyPre_eraseList ts vs]
end

mutual
theorem retype_erase : ∀ (t : Ty) (v : Val), v.retype (erase t) = v.retype t
  | .ptr _, v => by
    cases v with
    | int w x => cases w <;> rfl
    | _ => rfl
  | .agg fs n, v => by
    cases v with
    | agg vs =>
      simp only [erase, Val.retype]
      rw [retypeFields_eraseFields fs vs]
    | poison => rfl
    | _ => rfl
  | .tuple ts, v => by
    cases v with
    | tuple vs =>
      simp only [erase, Val.retype]
      rw [retypePre_eraseList ts vs]
    | poison => rfl
    | _ => rfl
  | .int _, v => rfl
  | .bool, v => rfl
  | .mem, v => rfl
  | .other, v => rfl
  | .blob _, v => rfl
  | .empty, v => rfl
  | .opaque _, v => rfl
  | .str, v => rfl
  | .slice _, v => by
    cases v with
    | agg vs =>
      match vs with
      | [_, _, _] => rfl
      | [] | [_] | [_, _] | _ :: _ :: _ :: _ :: _ => rfl
    | _ => rfl
theorem retypeFields_eraseFields : ∀ (fs : List (Nat × Ty)) (vs : List Val),
    Val.retypeFields (eraseFields fs) vs = Val.retypeFields fs vs
  | [], [] => rfl
  | [], _ :: _ => rfl
  | (o, t) :: fs, [] => rfl
  | (o, t) :: fs, v :: vs => by
    simp only [eraseFields, Val.retypeFields]
    rw [retype_erase t v, retypeFields_eraseFields fs vs]
theorem retypePre_eraseList : ∀ (ts : List Ty) (vs : List Val),
    Val.retypePre (eraseList ts) vs = Val.retypePre ts vs
  | [], vs => rfl
  | t :: ts, [] => rfl
  | t :: ts, v :: vs => by
    simp only [eraseList, Val.retypePre]
    rw [retype_erase t v, retypePre_eraseList ts vs]
end

theorem eqE_hasTy {s t : Ty} (h : eqE s t = true) (v : Val) : v.hasTy s = v.hasTy t := by
  rw [← hasTy_erase s, Ty.eq_of_beq h, hasTy_erase]

theorem eqE_retype {s t : Ty} (h : eqE s t = true) (v : Val) : v.retype s = v.retype t := by
  rw [← retype_erase s, Ty.eq_of_beq h, retype_erase]

mutual
theorem Ty.beq_refl : ∀ t : Ty, Ty.beq t t = true
  | .int w => by simp [Ty.beq]
  | .bool => rfl
  | .mem => rfl
  | .tuple ts => by simp only [Ty.beq]; exact Ty.beqList_refl ts
  | .other => rfl
  | .ptr e => by simp [Ty.beq]
  | .agg fs n => by simp only [Ty.beq, Bool.and_eq_true, beq_self_eq_true, and_true]; exact Ty.beqFields_refl fs
  | .blob n => by simp [Ty.beq]
  | .empty => rfl
  | .opaque n => by simp [Ty.beq]
  | .str => rfl
  | .slice e => by simp [Ty.beq]
theorem Ty.beqList_refl : ∀ ts : List Ty, Ty.beqList ts ts = true
  | [] => rfl
  | t :: ts => by simp only [Ty.beqList, Bool.and_eq_true]; exact ⟨Ty.beq_refl t, Ty.beqList_refl ts⟩
theorem Ty.beqFields_refl : ∀ fs : List (Nat × Ty), Ty.beqFields fs fs = true
  | [] => rfl
  | (o, t) :: fs => by
    simp only [Ty.beqFields, Bool.and_eq_true, beq_self_eq_true, true_and]
    exact ⟨Ty.beq_refl t, Ty.beqFields_refl fs⟩
end

theorem eqE_refl (t : Ty) : eqE t t = true := Ty.beq_refl _

theorem eqE_symm {s t : Ty} (h : eqE s t = true) : eqE t s = true := by
  unfold eqE at *; rw [Ty.eq_of_beq h]; exact Ty.beq_refl _

/-- The shape the checker reads for value `x` of `g` (`shapeOf`) is the shape of `x`'s register
(`Ctx.tys`). -/
theorem shapeOf_eq (tabs : Tables) (g : Func) (x : ID) :
    shapeOf (typeShapes tabs) g x = (Ctx.make tabs g).tys[x]?.getD .other := by
  unfold shapeOf
  cases hx : g.value? x with
  | some w => rw [tys_of_value hx]; simp only [valueTy, typeShapes_getD, Option.getD_some]
  | none =>
    simp only [valueTy]
    unfold Func.value? at hx
    simp only [Ctx.make, Array.getElem?_map]
    cases hv : g.valueTab[x]? with
    | none => rfl
    | some o =>
      rw [hv] at hx; simp at hx; subst hx; rfl

end GoFV.Proof.EC
