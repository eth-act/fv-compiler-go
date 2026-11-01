import GoFV.SSA.Sem.Val

/-!
# Decidable equality of type shapes

`Ty` is a nested inductive (fields are a `List (Nat × Ty)`), for which `deriving DecidableEq`
does not apply; `Ty.beq` compares shapes structurally (kernel-evaluable) and `Ty.eq_of_beq`
gives its soundness. Checkers that compare the shapes of two types use it.
-/

namespace GoFV.SSA.Sem

mutual
/-- Structural equality of shapes. -/
def Ty.beq : Ty → Ty → Bool
  | .int w, .int w' => w == w'
  | .bool, .bool => true
  | .mem, .mem => true
  | .tuple ts, .tuple ts' => Ty.beqList ts ts'
  | .other, .other => true
  | .ptr e, .ptr e' => e == e'
  | .agg fs n, .agg fs' n' => Ty.beqFields fs fs' && n == n'
  | .blob n, .blob n' => n == n'
  | .empty, .empty => true
  | .opaque n, .opaque n' => n == n'
  | .str, .str => true
  | .slice e, .slice e' => e == e'
  | _, _ => false
def Ty.beqList : List Ty → List Ty → Bool
  | [], [] => true
  | t :: ts, t' :: ts' => Ty.beq t t' && Ty.beqList ts ts'
  | _, _ => false
def Ty.beqFields : List (Nat × Ty) → List (Nat × Ty) → Bool
  | [], [] => true
  | (o, t) :: fs, (o', t') :: fs' => o == o' && Ty.beq t t' && Ty.beqFields fs fs'
  | _, _ => false
end

mutual
theorem Ty.eq_of_beq : {t t' : Ty} → Ty.beq t t' = true → t = t'
  | .int w, .int w', h => by simp only [Ty.beq, beq_iff_eq] at h; rw [h]
  | .bool, .bool, _ => rfl
  | .mem, .mem, _ => rfl
  | .tuple ts, .tuple ts', h => by
    simp only [Ty.beq] at h; rw [Ty.eq_of_beqList h]
  | .other, .other, _ => rfl
  | .ptr e, .ptr e', h => by simp only [Ty.beq, beq_iff_eq] at h; rw [h]
  | .agg fs n, .agg fs' n', h => by
    simp only [Ty.beq, Bool.and_eq_true, beq_iff_eq] at h
    rw [Ty.eq_of_beqFields h.1, h.2]
  | .blob n, .blob n', h => by simp only [Ty.beq, beq_iff_eq] at h; rw [h]
  | .empty, .empty, _ => rfl
  | .opaque n, .opaque n', h => by simp only [Ty.beq, beq_iff_eq] at h; rw [h]
  | .str, .str, _ => rfl
  | .slice e, .slice e', h => by simp only [Ty.beq, beq_iff_eq] at h; rw [h]
  | .str, .int _, h | .str, .bool, h | .str, .mem, h | .str, .tuple _, h | .str, .other, h
  | .str, .ptr _, h | .str, .agg _ _, h | .str, .blob _, h | .str, .empty, h
  | .str, .opaque _, h | .str, .slice _, h => by simp [Ty.beq] at h
  | .slice _, .int _, h | .slice _, .bool, h | .slice _, .mem, h | .slice _, .tuple _, h
  | .slice _, .other, h | .slice _, .ptr _, h | .slice _, .agg _ _, h | .slice _, .blob _, h
  | .slice _, .empty, h | .slice _, .opaque _, h | .slice _, .str, h => by simp [Ty.beq] at h
  | .int _, .str, h | .bool, .str, h | .mem, .str, h | .tuple _, .str, h | .other, .str, h
  | .ptr _, .str, h | .agg _ _, .str, h | .blob _, .str, h | .empty, .str, h
  | .opaque _, .str, h => by simp [Ty.beq] at h
  | .int _, .slice _, h | .bool, .slice _, h | .mem, .slice _, h | .tuple _, .slice _, h
  | .other, .slice _, h | .ptr _, .slice _, h | .agg _ _, .slice _, h | .blob _, .slice _, h
  | .empty, .slice _, h | .opaque _, .slice _, h => by simp [Ty.beq] at h
  | .int _, .bool, h | .int _, .mem, h | .int _, .tuple _, h | .int _, .other, h
  | .int _, .ptr _, h | .int _, .agg _ _, h | .int _, .blob _, h | .int _, .empty, h
  | .int _, .opaque _, h => by simp [Ty.beq] at h
  | .bool, .int _, h | .bool, .mem, h | .bool, .tuple _, h | .bool, .other, h
  | .bool, .ptr _, h | .bool, .agg _ _, h | .bool, .blob _, h | .bool, .empty, h
  | .bool, .opaque _, h => by simp [Ty.beq] at h
  | .mem, .int _, h | .mem, .bool, h | .mem, .tuple _, h | .mem, .other, h
  | .mem, .ptr _, h | .mem, .agg _ _, h | .mem, .blob _, h | .mem, .empty, h
  | .mem, .opaque _, h => by simp [Ty.beq] at h
  | .tuple _, .int _, h | .tuple _, .bool, h | .tuple _, .mem, h | .tuple _, .other, h
  | .tuple _, .ptr _, h | .tuple _, .agg _ _, h | .tuple _, .blob _, h | .tuple _, .empty, h
  | .tuple _, .opaque _, h => by simp [Ty.beq] at h
  | .other, .int _, h | .other, .bool, h | .other, .mem, h | .other, .tuple _, h
  | .other, .ptr _, h | .other, .agg _ _, h | .other, .blob _, h | .other, .empty, h
  | .other, .opaque _, h => by simp [Ty.beq] at h
  | .ptr _, .int _, h | .ptr _, .bool, h | .ptr _, .mem, h | .ptr _, .tuple _, h
  | .ptr _, .other, h | .ptr _, .agg _ _, h | .ptr _, .blob _, h | .ptr _, .empty, h
  | .ptr _, .opaque _, h => by simp [Ty.beq] at h
  | .agg _ _, .int _, h | .agg _ _, .bool, h | .agg _ _, .mem, h | .agg _ _, .tuple _, h
  | .agg _ _, .other, h | .agg _ _, .ptr _, h | .agg _ _, .blob _, h | .agg _ _, .empty, h
  | .agg _ _, .opaque _, h => by simp [Ty.beq] at h
  | .blob _, .int _, h | .blob _, .bool, h | .blob _, .mem, h | .blob _, .tuple _, h
  | .blob _, .other, h | .blob _, .ptr _, h | .blob _, .agg _ _, h | .blob _, .empty, h
  | .blob _, .opaque _, h => by simp [Ty.beq] at h
  | .empty, .int _, h | .empty, .bool, h | .empty, .mem, h | .empty, .tuple _, h
  | .empty, .other, h | .empty, .ptr _, h | .empty, .agg _ _, h | .empty, .blob _, h
  | .empty, .opaque _, h => by simp [Ty.beq] at h
  | .opaque _, .int _, h | .opaque _, .bool, h | .opaque _, .mem, h | .opaque _, .tuple _, h
  | .opaque _, .other, h | .opaque _, .ptr _, h | .opaque _, .agg _ _, h
  | .opaque _, .blob _, h | .opaque _, .empty, h => by simp [Ty.beq] at h
theorem Ty.eq_of_beqList : {ts ts' : List Ty} → Ty.beqList ts ts' = true → ts = ts'
  | [], [], _ => rfl
  | t :: ts, t' :: ts', h => by
    simp only [Ty.beqList, Bool.and_eq_true] at h
    rw [Ty.eq_of_beq h.1, Ty.eq_of_beqList h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [Ty.beqList] at h
theorem Ty.eq_of_beqFields : {fs fs' : List (Nat × Ty)} → Ty.beqFields fs fs' = true → fs = fs'
  | [], [], _ => rfl
  | (o, t) :: fs, (o', t') :: fs', h => by
    simp only [Ty.beqFields, Bool.and_eq_true, beq_iff_eq] at h
    rw [h.1.1, Ty.eq_of_beq h.1.2, Ty.eq_of_beqFields h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [Ty.beqFields] at h
end

end GoFV.SSA.Sem
