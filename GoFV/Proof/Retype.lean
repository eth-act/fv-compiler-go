import GoFV.SSA.Sem.Layout

/-!
# `Val.retype` gives a value of the shape

`Val.retype_hasTy`: `(v.retype t).hasTy t` for every value and shape (#108): a misfit becomes
`poison`; an address-less pointer is kept at the 64-bit integer shape, which `hasTy` accepts.
`Val.retype_of_hasTy`: a value of the shape is unchanged; so `retype` is idempotent
(`Val.retype_idem`).
-/

namespace GoFV.SSA.Sem

mutual
/-- **Every retyped value has the shape.** -/
theorem Val.retype_hasTy : ∀ (t : Ty) (v : Val), (v.retype t).hasTy t = true
  | t, .poison => by cases t <;> rfl
  | .int w', .int w x => by
    unfold Val.retype
    split
    · simp [Val.hasTy]
    · rfl
  | .int w', .ptr p => by
    cases w' with
    | w64 =>
      unfold Val.retype
      cases h : p.addr? with
      | some a => simp [Val.hasTy]
      | none => simp [Val.hasTy, h]
    | _ => rfl
  | .ptr e, .int w x => by cases w <;> rfl
  | .ptr e, .ptr p => rfl
  | .bool, .bool b => rfl
  | .mem, .mem m => rfl
  | .tuple ts, .tuple vs => by
    unfold Val.retype
    cases h : Val.retypePre ts vs with
    | none => rfl
    | some vs' => simp only [Val.hasTy]; exact Val.retypePre_hasTy ts vs vs' h
  | .agg fs n, .agg vs => by
    unfold Val.retype
    cases h : Val.retypeFields fs vs with
    | none => rfl
    | some vs' => simp only [Val.hasTy]; exact Val.retypeFields_hasTy fs vs vs' h
  | .blob n, .blob bs => by
    unfold Val.retype
    split
    · rename_i hl; simpa [Val.hasTy] using hl
    · rfl
  | .empty, .empty => rfl
  | .int _, .bool _ | .int _, .mem _ | .int _, .tuple _ | .int _, .agg _ | .int _, .blob _
  | .int _, .empty => rfl
  | .bool, .int _ _ | .bool, .mem _ | .bool, .tuple _ | .bool, .ptr _ | .bool, .agg _
  | .bool, .blob _ | .bool, .empty => rfl
  | .mem, .int _ _ | .mem, .bool _ | .mem, .tuple _ | .mem, .ptr _ | .mem, .agg _
  | .mem, .blob _ | .mem, .empty => rfl
  | .tuple _, .int _ _ | .tuple _, .bool _ | .tuple _, .mem _ | .tuple _, .ptr _
  | .tuple _, .agg _ | .tuple _, .blob _ | .tuple _, .empty => rfl
  | .other, .int _ _ | .other, .bool _ | .other, .mem _ | .other, .tuple _ | .other, .ptr _
  | .other, .agg _ | .other, .blob _ | .other, .empty => rfl
  | .ptr _, .bool _ | .ptr _, .mem _ | .ptr _, .tuple _ | .ptr _, .agg _ | .ptr _, .blob _
  | .ptr _, .empty => rfl
  | .agg _ _, .int _ _ | .agg _ _, .bool _ | .agg _ _, .mem _ | .agg _ _, .tuple _
  | .agg _ _, .ptr _ | .agg _ _, .blob _ | .agg _ _, .empty => rfl
  | .blob _, .int _ _ | .blob _, .bool _ | .blob _, .mem _ | .blob _, .tuple _
  | .blob _, .ptr _ | .blob _, .agg _ | .blob _, .empty => rfl
  | .empty, .int _ _ | .empty, .bool _ | .empty, .mem _ | .empty, .tuple _ | .empty, .ptr _
  | .empty, .agg _ | .empty, .blob _ => rfl
  | .opaque _, .int _ _ | .opaque _, .bool _ | .opaque _, .mem _ | .opaque _, .tuple _
  | .opaque _, .ptr _ | .opaque _, .agg _ | .opaque _, .blob _ | .opaque _, .empty => rfl

theorem Val.retypePre_hasTy : ∀ (ts : List Ty) (vs vs' : List Val),
    Val.retypePre ts vs = some vs' → Val.hasTyPre vs' ts = true
  | [], _, vs', _ => by cases vs' <;> rfl
  | _ :: _, [], _, h => by simp [Val.retypePre] at h
  | t :: ts, v :: vs, vs', h => by
    unfold Val.retypePre at h
    cases h' : Val.retypePre ts vs with
    | none => rw [h'] at h; cases h
    | some ws =>
      rw [h'] at h; cases h
      simp only [Val.hasTyPre, Val.retype_hasTy t v, Val.retypePre_hasTy ts vs ws h',
        Bool.and_self]

theorem Val.retypeFields_hasTy : ∀ (fs : List (Nat × Ty)) (vs vs' : List Val),
    Val.retypeFields fs vs = some vs' → Val.hasTyList vs' (fs.map (·.2)) = true
  | [], [], vs', h => by cases h; rfl
  | [], _ :: _, _, h => by simp [Val.retypeFields] at h
  | _ :: _, [], _, h => by simp [Val.retypeFields] at h
  | (o, t) :: fs, v :: vs, vs', h => by
    unfold Val.retypeFields at h
    cases h' : Val.retypeFields fs vs with
    | none => rw [h'] at h; cases h
    | some ws =>
      rw [h'] at h; cases h
      simp only [List.map_cons, Val.hasTyList, Val.retype_hasTy t v,
        Val.retypeFields_hasTy fs vs ws h', Bool.and_self]
end

mutual
/-- **A value of the shape is unchanged.** -/
theorem Val.retype_of_hasTy : ∀ {t : Ty} {v : Val}, v.hasTy t = true → v.retype t = v
  | t, .poison, _ => by cases t <;> rfl
  | .int w', .int w x, h => by
    simp only [Val.hasTy, beq_iff_eq] at h; subst h
    simp [Val.retype, BitVec.setWidth_eq]
  | .int w', .ptr p, h => by
    cases w' with
    | w64 =>
      simp only [Val.hasTy, Option.isNone_iff_eq_none] at h
      unfold Val.retype; rw [h]
    | _ => simp [Val.hasTy] at h
  | .ptr _, .ptr _, _ => rfl
  | .bool, .bool _, _ => rfl
  | .mem, .mem _, _ => rfl
  | .tuple ts, .tuple vs, h => by
    simp only [Val.hasTy] at h
    unfold Val.retype; rw [Val.retypePre_of_hasTy h]
  | .agg fs n, .agg vs, h => by
    simp only [Val.hasTy] at h
    unfold Val.retype; rw [Val.retypeFields_of_hasTy h]
  | .blob n, .blob bs, h => by
    simp only [Val.hasTy] at h
    unfold Val.retype; simp [h]
  | .empty, .empty, _ => rfl
  | .int _, .bool _, h | .int _, .mem _, h | .int _, .tuple _, h | .int _, .agg _, h
  | .int _, .blob _, h | .int _, .empty, h => by simp [Val.hasTy] at h
  | .bool, .int _ _, h | .bool, .mem _, h | .bool, .tuple _, h | .bool, .ptr _, h
  | .bool, .agg _, h | .bool, .blob _, h | .bool, .empty, h => by simp [Val.hasTy] at h
  | .mem, .int _ _, h | .mem, .bool _, h | .mem, .tuple _, h | .mem, .ptr _, h
  | .mem, .agg _, h | .mem, .blob _, h | .mem, .empty, h => by simp [Val.hasTy] at h
  | .tuple _, .int _ _, h | .tuple _, .bool _, h | .tuple _, .mem _, h | .tuple _, .ptr _, h
  | .tuple _, .agg _, h | .tuple _, .blob _, h | .tuple _, .empty, h => by simp [Val.hasTy] at h
  | .other, .int _ _, h | .other, .bool _, h | .other, .mem _, h | .other, .tuple _, h
  | .other, .ptr _, h | .other, .agg _, h | .other, .blob _, h | .other, .empty, h => by
    simp [Val.hasTy] at h
  | .ptr _, .int _ _, h | .ptr _, .bool _, h | .ptr _, .mem _, h | .ptr _, .tuple _, h
  | .ptr _, .agg _, h | .ptr _, .blob _, h | .ptr _, .empty, h => by simp [Val.hasTy] at h
  | .agg _ _, .int _ _, h | .agg _ _, .bool _, h | .agg _ _, .mem _, h | .agg _ _, .tuple _, h
  | .agg _ _, .ptr _, h | .agg _ _, .blob _, h | .agg _ _, .empty, h => by simp [Val.hasTy] at h
  | .blob _, .int _ _, h | .blob _, .bool _, h | .blob _, .mem _, h | .blob _, .tuple _, h
  | .blob _, .ptr _, h | .blob _, .agg _, h | .blob _, .empty, h => by simp [Val.hasTy] at h
  | .empty, .int _ _, h | .empty, .bool _, h | .empty, .mem _, h | .empty, .tuple _, h
  | .empty, .ptr _, h | .empty, .agg _, h | .empty, .blob _, h => by simp [Val.hasTy] at h
  | .opaque _, .int _ _, h | .opaque _, .bool _, h | .opaque _, .mem _, h
  | .opaque _, .tuple _, h | .opaque _, .ptr _, h | .opaque _, .agg _, h
  | .opaque _, .blob _, h | .opaque _, .empty, h => by simp [Val.hasTy] at h

theorem Val.retypePre_of_hasTy : ∀ {ts : List Ty} {vs : List Val},
    Val.hasTyPre vs ts = true → Val.retypePre ts vs = some vs
  | [], _, _ => rfl
  | _ :: _, [], h => by simp [Val.hasTyPre] at h
  | t :: ts, v :: vs, h => by
    simp only [Val.hasTyPre, Bool.and_eq_true] at h
    simp only [Val.retypePre, Val.retypePre_of_hasTy h.2, Option.map_some,
      Val.retype_of_hasTy h.1]

theorem Val.retypeFields_of_hasTy : ∀ {fs : List (Nat × Ty)} {vs : List Val},
    Val.hasTyList vs (fs.map (·.2)) = true → Val.retypeFields fs vs = some vs
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [Val.hasTyList] at h
  | _ :: _, [], h => by simp [Val.hasTyList] at h
  | (o, t) :: fs, v :: vs, h => by
    simp only [List.map_cons, Val.hasTyList, Bool.and_eq_true] at h
    simp only [Val.retypeFields, Val.retypeFields_of_hasTy h.2, Option.map_some,
      Val.retype_of_hasTy h.1]
end

theorem Val.retype_idem (t : Ty) (v : Val) : (v.retype t).retype t = v.retype t :=
  Val.retype_of_hasTy (Val.retype_hasTy t v)

/-- The statement the rule interpreter needs (#108, #113). -/
theorem Val.retype_int_hasTy (v : Val) (w : Width) : (v.retype (.int w)).hasTy (.int w) = true :=
  Val.retype_hasTy _ v

end GoFV.SSA.Sem
