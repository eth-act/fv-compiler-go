import GoFV.Proof.ProveCheck.Rng
import GoFV.Proof.ProveCheck.Tabs
import GoFV.Proof.AtomSimDen

/-!
# Values of terms, as prove's validator reads them (issue #24)

Small facts about `Term.den` and the value families: a defined (non-`poison`) value keeps its
value at more fuel (`den_stable_int`, `den_stable_bool`); `retype` at an integer or boolean
shape; the shapes of terms and typed atoms (`den_int_shape`); unfolding the integer families
(`int1_eq`, `int2_eq`).
-/

namespace GoFV.Proof.ProveCheck

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck GoFV.Opt.ProveCheck GoFV.Proof.Term
  GoFV.Proof.AtomSim

theorem Width.one_le (w : Width) : 1 ≤ w.bits := by cases w <;> decide

theorem refines_int {w : Width} {y : BitVec w.bits} {v : Val} (h : Sem.Refines (.int w y) v) :
    v = .int w y := by
  cases h; rfl

theorem refines_bool {b : Bool} {v : Val} (h : Sem.Refines (.bool b) v) : v = .bool b := by
  cases h; rfl

section
variable {D : ID → Option Value} {tabs : Tables} {ρ : ID → Val}

theorem den_stable_int {n K : Nat} {x : ID} {w : Width} {y : BitVec w.bits}
    (h : den D tabs ρ n x = .int w y) (hK : n ≤ K) : den D tabs ρ K x = .int w y :=
  refines_int (h ▸ den_fuel_mono D tabs ρ n K x hK)

theorem den_stable_bool {n K : Nat} {x : ID} {b : Bool}
    (h : den D tabs ρ n x = .bool b) (hK : n ≤ K) : den D tabs ρ K x = .bool b :=
  refines_bool (h ▸ den_fuel_mono D tabs ρ n K x hK)

/-- Two defined values of `x` at different fuel are equal. -/
theorem den_int_unique {n m : Nat} {x : ID} {w : Width} {y y' : BitVec w.bits}
    (h : den D tabs ρ n x = .int w y) (h' : den D tabs ρ m x = .int w y') : y = y' := by
  rcases Nat.le_total n m with hm | hm
  · have := den_stable_int h hm; rw [h'] at this; cases this; rfl
  · have := den_stable_int h' hm; rw [h] at this; cases this; rfl

end

theorem val_int_inj {w w' : Width} {x : BitVec w.bits} {y : BitVec w'.bits}
    (h : Val.int w x = Val.int w' y) : ∃ e : w = w', e ▸ x = y := by
  cases h; exact ⟨rfl, rfl⟩

theorem asInt_eq {v : Val} {w : Width} {x : BitVec w.bits} (h : v.asInt w = some x) :
    v = .int w x := by
  cases v with
  | int w' y =>
    simp only [Val.asInt] at h
    split at h
    · rename_i e; subst e; cases h; rfl
    · cases h
  | _ => simp [Val.asInt] at h

theorem asBool_eq {v : Val} {b : Bool} (h : v.asBool = some b) : v = .bool b := by
  cases v <;> simp [Val.asBool] at h; subst h; rfl

theorem int1_eq {w : Width} {f : BitVec w.bits → Val} {args : List Val} {v : Val}
    (h : Sem.int1 w f args = v) (hv : v ≠ .poison) :
    ∃ a x, args = [a] ∧ a = .int w x ∧ f x = v := by
  unfold Sem.int1 at h
  split at h
  · rename_i a
    cases ha : a.asInt w with
    | none => rw [ha] at h; exact absurd h.symm hv
    | some x => rw [ha] at h; exact ⟨a, x, rfl, asInt_eq ha, h⟩
  · exact absurd h.symm hv

theorem int2_eq {w : Width} {f : BitVec w.bits → BitVec w.bits → Val} {args : List Val} {v : Val}
    (h : Sem.int2 w f args = v) (hv : v ≠ .poison) :
    ∃ a b x y, args = [a, b] ∧ a = .int w x ∧ b = .int w y ∧ f x y = v := by
  unfold Sem.int2 at h
  split at h
  · rename_i a b
    cases ha : a.asInt w with
    | none => rw [ha] at h; exact absurd h.symm hv
    | some x =>
      cases hb : b.asInt w with
      | none => rw [ha, hb] at h; exact absurd h.symm hv
      | some y => rw [ha, hb] at h; exact ⟨a, b, x, y, rfl, asInt_eq ha, asInt_eq hb, h⟩
  · exact absurd h.symm hv

theorem retype_int_self (w : Width) (x : BitVec w.bits) : (Val.int w x).retype (.int w) = .int w x := by
  simp [Val.retype, BitVec.setWidth_eq]

theorem retype_poison' (t : Ty) : Val.poison.retype t = .poison := by cases t <;> rfl

theorem retype_bool_eq {t : Ty} {b v : Bool} (h : (Val.bool b).retype t = .bool v) : b = v := by
  cases t <;> simp [Val.retype] at h; exact h

/-- A `bool`-or-`poison` value retyped stays `bool`-or-`poison`. -/
theorem retype_bool_or {t : Ty} {z : Val} {b : Bool} (h : z = .poison ∨ z = .bool b) :
    z.retype t = .poison ∨ z.retype t = .bool b := by
  rcases h with rfl | rfl
  · exact .inl (retype_poison' t)
  · cases t <;> simp [Val.retype]

theorem width_some {t : Ty} {w : Width} (h : t.width? = some w) : t = .int w := by
  cases t <;> simp [Ty.width?] at h; subst h; rfl

/-- A value retyped at shape `t` that is a `w`-bit integer: `t` is `int w`. -/
theorem retype_int_shape {t : Ty} {z : Val} {w : Width} {y : BitVec w.bits}
    (h : z.retype t = .int w y) : t = .int w := by
  have := Val.retype_hasTy t z
  rw [h] at this
  cases t <;> simp [Val.hasTy] at this
  subst this; rfl

/-- The value of a term or typed atom that is a `w`-bit integer has shape `int w`. -/
theorem den_int_shape {D : ID → Option Value} {tabs : Tables} {ρ : ID → Val}
    (hty : Term.Typed D tabs ρ) {n : Nat} {a : ID} {u : Value} (hu : D a = some u) {w : Width}
    {y : BitVec w.bits} (h : den D tabs ρ n a = .int w y) : tabs.ty u.type = .int w := by
  cases n with
  | zero => simp [den] at h
  | succ n =>
    by_cases ht : termOp u.op = true
    · rw [den_succ_term hu ht] at h; exact retype_int_shape h
    · have hat : ¬ IsTerm D a := fun ⟨v, hv, hv'⟩ => by rw [hu] at hv; cases hv; exact ht hv'
      rw [den_succ_atom hat] at h
      have := hty a hat (by rw [hu]; rfl)
      rw [h] at this
      have hs : shape D tabs a = tabs.ty u.type := by simp [shape, hu]
      rw [hs] at this
      exact retype_int_shape this

end GoFV.Proof.ProveCheck
