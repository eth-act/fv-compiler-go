import GoFV.Proof.Low.RuleL
import GoFV.Proof.ValRefine
import GoFV.Proof.Retype

/-!
# `Val.widen` and `movAddr` are monotone (issue #385)

`Val.retypeL t v = (v.widen t).retype t`: `widen_mono` (refinement passes through the widening),
`widen_of_hasTy` (a value of shape `t` is not widened, so `Val.retypeL` is idempotent), and
`retype_le_widen` (the widening only changes values Phase 1's `Val.retype` makes `poison`, tuples
componentwise). `movAddr_mono'`: `MOVDaddr` without a frame variable. Used by
`GoFV.Proof.Low.ArmMono`.
-/

namespace GoFV.Proof.Low.Mono

open GoFV.SSA GoFV.SSA.Sem

theorem movAddr_mono' (tabs : Tables) (ai : Int64) (ax : Option AuxRef) {as bs : List Val}
    (hr : RefinesList as bs) : Refines (movAddr tabs ai ax as) (movAddr tabs ai ax bs) := by
  rcases hr with _ | ⟨h1, _ | ⟨_, _⟩⟩
  · exact .poison _
  · cases ax with
    | some n => exact Refines.refl _
    | none => cases h1 <;> first | exact .poison _ | exact Refines.refl _
  · exact .poison _


theorem widenList_nil (vs : List Val) : Val.widenList [] vs = vs := by cases vs <;> rfl

mutual
theorem widen_mono : ∀ (t : Ty) {v v' : Val}, Refines v v' → Refines (v.widen t) (v'.widen t)
  | t, _, _, .poison _ => by cases t <;> exact .poison _
  | _, _, _, .int _ _ => Refines.refl _
  | _, _, _, .bool _ => Refines.refl _
  | _, _, _, .ptr _ => Refines.refl _
  | _, _, _, .empty => Refines.refl _
  | t, _, _, .mem h => by cases t <;> exact .mem h
  | t, _, _, .agg h => by cases t <;> exact .agg h
  | t, _, _, .blob h => by cases t <;> exact .blob h
  | t, _, _, .tuple h => by
    cases t with
    | tuple ts => exact .tuple (widenList_mono ts h)
    | _ => exact .tuple h

theorem widenList_mono : ∀ (ts : List Ty) {vs vs' : List Val}, RefinesList vs vs' →
    RefinesList (Val.widenList ts vs) (Val.widenList ts vs')
  | [], vs, vs', h => by rw [widenList_nil, widenList_nil]; exact h
  | _ :: _, _, _, .nil => .nil
  | t :: ts, _, _, .cons h hs => .cons (widen_mono t h) (widenList_mono ts hs)
end

mutual
theorem widen_of_hasTy : ∀ (t : Ty) (v : Val), v.hasTy t = true → v.widen t = v
  | t, .poison, _ => by cases t <;> rfl
  | t, .int w x, h => by
    cases t with
    | int w' => cases w <;> cases w' <;> first | rfl | first | cases h | simp [Val.hasTy] at h
    | ptr e => cases w <;> first | rfl | first | cases h | simp [Val.hasTy] at h
    | _ => rfl
  | t, .bool b, h => by cases t <;> first | rfl | first | cases h | simp [Val.hasTy] at h
  | t, .mem _, _ => by cases t <;> rfl
  | t, .ptr _, _ => by cases t <;> rfl
  | t, .agg _, _ => by cases t <;> rfl
  | t, .blob _, _ => by cases t <;> rfl
  | t, .empty, _ => by cases t <;> rfl
  | t, .tuple vs, h => by
    cases t with
    | tuple ts =>
      show Val.tuple (Val.widenList ts vs) = .tuple vs
      rw [widenList_of_hasTyPre ts vs h]
    | _ => rfl

theorem widenList_of_hasTyPre : ∀ (ts : List Ty) (vs : List Val), Val.hasTyPre vs ts = true →
    Val.widenList ts vs = vs
  | [], vs, _ => by cases vs <;> rfl
  | _ :: _, [], _ => rfl
  | t :: ts, v :: vs, h => by
    simp only [Val.hasTyPre, Bool.and_eq_true] at h
    show Val.widen t v :: Val.widenList ts vs = v :: vs
    rw [widen_of_hasTy t v h.1, widenList_of_hasTyPre ts vs h.2]
end

mutual
theorem retype_le_widen : ∀ (t : Ty) (v : Val), Refines (v.retype t) ((v.widen t).retype t)
  | t, .poison => by cases t <;> exact .poison _
  | t, .int w x => by
    cases t with
    | int w' => cases w <;> cases w' <;> first | exact .poison _ | exact Refines.refl _
    | ptr e => cases w <;> first | exact .poison _ | exact Refines.refl _
    | _ => exact Refines.refl _
  | t, .bool _ => by cases t <;> first | exact .poison _ | exact Refines.refl _
  | t, .mem _ => by cases t <;> exact Refines.refl _
  | t, .ptr _ => by cases t <;> exact Refines.refl _
  | t, .agg _ => by cases t <;> exact Refines.refl _
  | t, .blob _ => by cases t <;> exact Refines.refl _
  | t, .empty => by cases t <;> exact Refines.refl _
  | t, .tuple vs => by
    cases t with
    | tuple ts =>
      show Refines (Val.retype (.tuple ts) (.tuple vs))
        (Val.retype (.tuple ts) (.tuple (Val.widenList ts vs)))
      unfold Val.retype
      have hr := retypePre_widen ts vs
      cases ha : Val.retypePre ts vs <;> cases hb : Val.retypePre ts (Val.widenList ts vs) <;>
        rw [ha, hb] at hr
      · exact .poison _
      · cases hr
      · cases hr
      · cases hr with | some hw => exact .tuple hw
    | _ => exact Refines.refl _

theorem retypePre_widen : ∀ (ts : List Ty) (vs : List Val),
    Option.Rel RefinesList (Val.retypePre ts vs) (Val.retypePre ts (Val.widenList ts vs))
  | [], vs => by cases vs <;> exact .some (RefinesList.refl _)
  | _ :: _, [] => .none
  | t :: ts, v :: vs => by
    show Option.Rel RefinesList ((Val.retypePre ts vs).map (Val.retype t v :: ·))
      ((Val.retypePre ts (Val.widenList ts vs)).map (Val.retype t (Val.widen t v) :: ·))
    have hr := retypePre_widen ts vs
    revert hr
    generalize Val.retypePre ts vs = o
    generalize Val.retypePre ts (Val.widenList ts vs) = o'
    intro hr
    cases hr with
    | none => exact .none
    | some hw => exact .some (.cons (retype_le_widen t v) hw)
end

end GoFV.Proof.Low.Mono
