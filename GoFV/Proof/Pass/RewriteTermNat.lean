import GoFV.Opt.RewriteCheck

/-!
# `natShape`: the op's raw result has the value's shape (issue #113)

`evalPure_natShape`: when `RewriteCheck.natShape op ty` holds (a boolean op at `bool`, an
integer op of width `w` at `int w`), `evalPure op ty …` has shape `ty` for all arguments, which
is the hypothesis `(Pat.raw e r.pat).hasTy (e.ty [])` of `Rule.Sound`.
-/

namespace GoFV.Proof.Pass.Rewrite

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck

theorem int1_hasTy {w : Width} {t : Ty} {f : BitVec w.bits → Val} (hf : ∀ x, (f x).hasTy t = true)
    (args : List Val) : (int1 w f args).hasTy t = true := by
  unfold int1; split
  · split
    · exact hf _
    · rfl
  · rfl

theorem int2_hasTy {w : Width} {t : Ty} {f : BitVec w.bits → BitVec w.bits → Val}
    (hf : ∀ x y, (f x y).hasTy t = true) (args : List Val) : (int2 w f args).hasTy t = true := by
  unfold int2; split
  · split
    · exact hf _ _
    · rfl
  · rfl

theorem int3_hasTy {w : Width} {t : Ty} {f : BitVec w.bits → BitVec w.bits → BitVec w.bits → Val}
    (hf : ∀ x y z, (f x y z).hasTy t = true) (args : List Val) : (int3 w f args).hasTy t = true := by
  unfold int3; split
  · split
    · exact hf _ _ _
    · rfl
  · rfl

theorem bool1_hasTy (f : Bool → Bool) (args : List Val) : (bool1 f args).hasTy .bool = true := by
  unfold bool1; split
  · split <;> rfl
  · rfl

theorem bool2_hasTy (f : Bool → Bool → Bool) (args : List Val) :
    (bool2 f args).hasTy .bool = true := by
  unfold bool2; split
  · split <;> rfl
  · rfl

theorem andB_hasTy (args : List Val) : (Cmp.andB args).hasTy .bool = true := by
  unfold Cmp.andB; split
  · split <;> rfl
  · rfl

theorem orB_hasTy (args : List Val) : (Cmp.orB args).hasTy .bool = true := by
  unfold Cmp.orB; split
  · split <;> rfl
  · rfl

theorem inBounds_hasTy (s : Bool) (args : List Val) : (Cmp.inBounds s args).hasTy .bool = true := by
  unfold Cmp.inBounds; split
  · split
    · split <;> rfl
    · rfl
  · rfl

theorem shift_hasTy {w a : Width} {b : Bool} {f : BitVec w.bits → Nat → BitVec w.bits}
    (args : List Val) : (Shift.shift w a b f args).hasTy (.int w) = true := by
  unfold Shift.shift; split
  · split
    · split
      · rfl
      · simp [Val.hasTy]
    · rfl
  · rfl

theorem rotateLeft_hasTy (w : Width) (args : List Val) :
    (Int.rotateLeft w args).hasTy (.int w) = true := by
  unfold Int.rotateLeft; split
  · split
    · simp [Val.hasTy]
    · rfl
  · rfl

theorem boolToUint8_hasTy (args : List Val) : (Conv.boolToUint8 args).hasTy (.int .w8) = true := by
  unfold Conv.boolToUint8; split
  · split <;> rfl
  · rfl

/-- Closes `(evalPure op ty …).hasTy ty = true` for a concrete op and shape. -/
macro "natshape_close" : tactic => `(tactic| first
  | exact int2_hasTy (fun _ _ => by (repeat' split) <;> rfl) _
  | exact int1_hasTy (fun _ => by (repeat' split) <;> rfl) _
  | exact int3_hasTy (fun _ _ _ => by (repeat' split) <;> rfl) _
  | exact bool2_hasTy _ _
  | exact bool1_hasTy _ _
  | exact andB_hasTy _
  | exact orB_hasTy _
  | exact inBounds_hasTy _ _
  | exact shift_hasTy _
  | exact rotateLeft_hasTy _ _
  | exact boolToUint8_hasTy _
  | rfl)

/-- **`natShape`**: the raw value of an op checked by `natShape` has the shape `ty`. -/
theorem evalPure_natShape {op : Op} {ty : Ty} (ai : Int64) (ax : Option AuxRef) (args : List Val)
    (h : natShape op ty = true) : (evalPure op ty ai ax args).hasTy ty = true := by
  cases ty with
  | bool =>
    replace h : boolOp op = true := h
    cases op <;> first | exact absurd h (by decide) | natshape_close
  | int w =>
    replace h : intOpWidth op w = true := h
    cases op <;> first
      | exact absurd h (by decide)
      | (cases w <;> first | exact absurd h (by decide) | natshape_close)
  | _ => exact absurd h (by simp [natShape])

end GoFV.Proof.Pass.Rewrite
