import GoFV.Opt.RewriteCheck
import GoFV.Proof.Retype
import GoFV.Proof.Pass.RewriteTermDen

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

theorem eqPtr_hasTy (neg : Bool) (args : List Val) :
    (PtrOps.eqPtr neg args).hasTy .bool = true := by
  unfold PtrOps.eqPtr; split
  · split <;> rfl
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
  | exact eqPtr_hasTy _ _
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

/-! ## Pointer ops (`ptrTop`) -/

theorem eq_of_isPtrTy {t : Ty} (h : GoFV.Proof.Rules.isPtrTy t = true) : ∃ e, t = .ptr e := by
  unfold GoFV.Proof.Rules.isPtrTy at h; split at h <;> first | exact ⟨_, rfl⟩ | cases h

theorem eq_of_isInt64Ty {t : Ty} (h : GoFV.Proof.Rules.isInt64Ty t = true) : t = .int .w64 := by
  unfold GoFV.Proof.Rules.isInt64Ty at h; split at h <;> first | rfl | cases h

theorem isPtrTy_hasTy {t : Ty} (ht : GoFV.Proof.Rules.isPtrTy t = true) (p : Ptr) :
    (Val.ptr p).hasTy t = true := by
  obtain ⟨_, rfl⟩ := eq_of_isPtrTy ht; rfl

theorem int_not_hasTy_ptr {t : Ty} (ht : GoFV.Proof.Rules.isPtrTy t = true) {w : Width}
    {x : BitVec w.bits} : (Val.int w x).hasTy t = false := by
  obtain ⟨_, rfl⟩ := eq_of_isPtrTy ht; rfl

/-- A value of a 64-bit integer shape is `poison`, a 64-bit integer or a pointer. -/
theorem of_hasTy_int64 {t : Ty} (ht : GoFV.Proof.Rules.isInt64Ty t = true) {a : Val}
    (ha : a.hasTy t = true) : a = .poison ∨ (∃ x, a = .int .w64 x) ∨ ∃ p, a = .ptr p := by
  rw [eq_of_isInt64Ty ht] at ha
  cases a with
  | poison => exact .inl rfl
  | int w x => cases w <;> first | exact .inr (.inl ⟨x, rfl⟩) | simp [Val.hasTy] at ha
  | ptr p => exact .inr (.inr ⟨p, rfl⟩)
  | _ => simp [Val.hasTy] at ha

/-- A value of a pointer shape is `poison` or a pointer. -/
theorem of_hasTy_ptr {t : Ty} (ht : GoFV.Proof.Rules.isPtrTy t = true) {a : Val}
    (ha : a.hasTy t = true) : a = .poison ∨ ∃ p, a = .ptr p := by
  obtain ⟨_, rfl⟩ := eq_of_isPtrTy ht
  cases a with
  | poison => exact .inl rfl
  | ptr p => exact .inr ⟨p, rfl⟩
  | _ => simp [Val.hasTy] at ha

/-- **`ptrTop`**: a pointer op whose first argument has the shape `argShapeOk` asks for has the
shape `ty`. -/
theorem evalPure_ptrTop {op : Op} {ty : Ty} (ai : Int64) (ax : Option AuxRef) (args : List Val)
    (h : ptrTop op ty = true)
    (h0 : ∀ a, args.head? = some a →
      ∃ t, GoFV.Proof.Rules.argShapeOk op ty 0 t = true ∧ a.hasTy t = true) :
    (evalPure op ty ai ax args).hasTy ty = true := by
  cases op
  case OffPtr =>
    simp only [ptrTop] at h
    show (PtrOps.offPtr ai args).hasTy ty = true
    unfold PtrOps.offPtr
    split
    · unfold PtrOps.ptrRes; split
      · exact isPtrTy_hasTy h _
      · rfl
    · obtain ⟨t, ht, hx⟩ := h0 _ rfl
      simp only [GoFV.Proof.Rules.argShapeOk, bne_self_eq_false, Bool.false_or] at ht
      rw [int_not_hasTy_ptr ht] at hx; cases hx
    · rfl
  case AddPtr =>
    simp only [ptrTop] at h
    show (PtrOps.addPtr args).hasTy ty = true
    unfold PtrOps.addPtr
    split
    · split
      · unfold PtrOps.ptrRes; split
        · exact isPtrTy_hasTy h _
        · rfl
      · rfl
    · obtain ⟨t, ht, hx⟩ := h0 _ rfl
      simp only [GoFV.Proof.Rules.argShapeOk, beq_self_eq_true, ite_true] at ht
      rw [int_not_hasTy_ptr ht] at hx; cases hx
    · rfl
  case PtrIndex =>
    simp only [ptrTop] at h
    show (PtrOps.ptrIndex _ args).hasTy ty = true
    unfold PtrOps.ptrIndex
    split
    · split
      · unfold PtrOps.ptrRes; split
        · exact isPtrTy_hasTy h _
        · rfl
      · rfl
    · rfl
  case Convert =>
    simp only [ptrTop, Bool.or_eq_true] at h
    show (PtrOps.convert ty args).hasTy ty = true
    unfold PtrOps.convert
    split
    · rename_i x m
      obtain ⟨t, ht, hx⟩ := h0 _ rfl
      simp only [GoFV.Proof.Rules.argShapeOk, bne_self_eq_false, Bool.false_or,
        GoFV.Proof.Rules.convArgOk] at ht
      split
      · split
        · rfl
        · rfl
      · rfl
      · rename_i hne1 hne2
        rcases h with h | h
        · obtain ⟨el, rfl⟩ := eq_of_isPtrTy h
          simp only [GoFV.Proof.Rules.convArgOk] at ht
          rcases of_hasTy_int64 ht hx with rfl | ⟨y, rfl⟩ | ⟨p, rfl⟩
          · rfl
          · exact (hne2 el y rfl rfl).elim
          · rfl
        · have hw := eq_of_isInt64Ty h
          subst hw
          simp only [GoFV.Proof.Rules.convArgOk] at ht
          rcases of_hasTy_ptr ht hx with rfl | ⟨p, rfl⟩
          · rfl
          · exact (hne1 p rfl rfl).elim
    · rfl
  all_goals exact absurd h (by simp [ptrTop])

/-- The value of a pattern node has its instance type's shape when its leaves do. -/
theorem den_hasTy_typed {tabs : Tables} {e : GoFV.Proof.Rules.PEnv} :
    ∀ (p : GoFV.Proof.Rules.Path) (q : GoFV.Rules.Pat), GoFV.Proof.Rules.Pat.typed e p q →
      (GoFV.Proof.Rules.Pat.denT tabs e p q).hasTy (e.ty p) = true
  | p, .op .., _ => by simp only [GoFV.Proof.Rules.Pat.denT]; exact Val.retype_hasTy _ _
  | _, .wild, h | _, .bind _, h | _, .same _, h => h

/-- The raw value of a pattern whose top op is checked by `ptrTop` has the top type's shape. -/
theorem raw_ptrTop {tabs : Tables} {e : GoFV.Proof.Rules.PEnv} {o : Op} {nm : Option Nat}
    {pty pai pax : GoFV.Rules.Field} {par : GoFV.Rules.Arity} {args : List GoFV.Rules.Pat}
    {cm : Bool} (hf : GoFV.Proof.Rules.frameOp o = false) (hp : ptrTop o (e.ty []) = true)
    (ht : GoFV.Proof.Rules.Pat.typed e [] (.op o nm pty pai pax par args cm))
    (ha : GoFV.Proof.Rules.Pat.argsOK e.ty [] (.op o nm pty pai pax par args cm) = true) :
    (GoFV.Proof.Rules.Pat.rawT tabs e (.op o nm pty pai pax par args cm)).hasTy (e.ty []) = true := by
  simp only [GoFV.Proof.Rules.Pat.rawT, GoFV.Proof.Rules.opVal_pure hf]
  apply evalPure_ptrTop _ _ _ hp
  intro a hh
  cases args with
  | nil => simp [GoFV.Proof.Rules.Pat.densT] at hh
  | cons q qs =>
    simp only [GoFV.Proof.Rules.Pat.densT, List.head?_cons, Option.some.injEq] at hh
    subst hh
    simp only [GoFV.Proof.Rules.Pat.typed, GoFV.Proof.Rules.Pat.typeds] at ht
    simp only [GoFV.Proof.Rules.Pat.argsOK, GoFV.Proof.Rules.Pat.argsOKs, Bool.and_eq_true] at ha
    exact ⟨_, ha.1.1, den_hasTy_typed _ _ ht.1⟩

/-- **`constTop`**: a constant composite op checked by `constTop` has the shape `ty` (its value
does not depend on the auxint, aux or arguments). -/
theorem evalPure_constTop {op : Op} {ty : Ty} (ai : Int64) (ax : Option AuxRef) (args : List Val)
    (h : constTop op ty = true) : (evalPure op ty ai ax args).hasTy ty = true := by
  simp only [constTop, Bool.and_eq_true] at h
  obtain ⟨ho, h⟩ := h
  cases op <;> first | exact absurd ho (by decide) | exact h

theorem frameOp_false {o : Op} (h1 : o ≠ .Addr) (h2 : o ≠ .ConstString) :
    GoFV.Proof.Rules.frameOp o = false := by
  unfold GoFV.Proof.Rules.frameOp
  cases h : o == .Addr <;> cases h' : o == .ConstString <;> simp_all

theorem natShape_frame {ty : Ty} : natShape .Addr ty = false ∧ natShape .ConstString ty = false := by
  cases ty <;> exact ⟨rfl, rfl⟩

/-- The raw value of a table-evaluated top op checked by `frameTop` has the top type's shape. -/
theorem rawT_frameTop {tabs : Tables} {e : GoFV.Proof.Rules.PEnv} {o : Op} {nm : Option Nat}
    {pty pai pax : GoFV.Rules.Field} {par : GoFV.Rules.Arity} {args : List GoFV.Rules.Pat}
    {cm : Bool} (hp : frameTop o (e.ty []) = true) :
    (GoFV.Proof.Rules.Pat.rawT tabs e (.op o nm pty pai pax par args cm)).hasTy (e.ty []) = true := by
  simp only [frameTop, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hp
  simp only [GoFV.Proof.Rules.Pat.rawT]
  rcases hp with ⟨rfl, hp⟩ | ⟨rfl, hp⟩
  · rw [GoFV.Proof.Rules.opVal_addr]
    obtain ⟨el, he⟩ := eq_of_isPtrTy hp
    rw [he]; unfold GoFV.Proof.Rules.addrVal
    split <;> rfl
  · rw [GoFV.Proof.Rules.opVal_constString, tyEq_sound hp]
    unfold GoFV.Proof.Rules.strVal
    split
    · rename_i s d _
      cases s.size == 0 <;> rfl
    · rfl

/-- **`topOK`**: the raw value of a pattern whose top op `topOK` accepts has the top type's
shape. -/
theorem raw_topOK {tabs : Tables} {e : GoFV.Proof.Rules.PEnv} {o : Op} {nm : Option Nat}
    {pty pai pax : GoFV.Rules.Field} {par : GoFV.Rules.Arity} {args : List GoFV.Rules.Pat}
    {cm : Bool} (hp : topOK o (e.ty []) = true)
    (ht : GoFV.Proof.Rules.Pat.typed e [] (.op o nm pty pai pax par args cm))
    (ha : GoFV.Proof.Rules.Pat.argsOK e.ty [] (.op o nm pty pai pax par args cm) = true) :
    (GoFV.Proof.Rules.Pat.rawT tabs e (.op o nm pty pai pax par args cm)).hasTy (e.ty []) = true := by
  simp only [topOK, Bool.or_eq_true] at hp
  rcases hp with ((hp | hp) | hp) | hp
  · have hf : GoFV.Proof.Rules.frameOp o = false := frameOp_false
      (by rintro rfl; rw [natShape_frame.1] at hp; cases hp)
      (by rintro rfl; rw [natShape_frame.2] at hp; cases hp)
    simp only [GoFV.Proof.Rules.Pat.rawT, GoFV.Proof.Rules.opVal_pure hf]
    exact evalPure_natShape _ _ _ hp
  · have hf : GoFV.Proof.Rules.frameOp o = false := frameOp_false
      (by rintro rfl; cases hp) (by rintro rfl; cases hp)
    exact raw_ptrTop hf hp ht ha
  · have hf : GoFV.Proof.Rules.frameOp o = false := frameOp_false
      (by rintro rfl; cases hp) (by rintro rfl; cases hp)
    simp only [GoFV.Proof.Rules.Pat.rawT, GoFV.Proof.Rules.opVal_pure hf]
    exact evalPure_constTop _ _ _ hp
  · exact rawT_frameTop hp

end GoFV.Proof.Pass.Rewrite
