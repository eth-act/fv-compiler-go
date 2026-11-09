import GoFV.Proof.Pass.DAEAvoid
import GoFV.Proof.Retype

variable [GoFV.SSA.Sem.Addrs]

/-!
# dead auto elim: related registers

`VR U vS vT`: the target register `vT` is the source's `vS`, or both are memories equal outside
the blocks `U` (`Mem.EqOff`), or both are tuples (call results, `MakeResult`) related
componentwise. Related values have the same shape (`VR.hasTy`), encoding (`VR.encode`) and
poison (`VR.hasPoison`); `retype` keeps them related (`VR.retype`); a related value that is
neither a memory nor a tuple is equal (`VR.eq`).
-/

namespace GoFV.Proof.DAE

open GoFV.SSA GoFV.SSA.Sem

mutual
/-- Related registers. -/
inductive VR (U : Blk → Prop) : Val → Val → Prop where
  | refl (v : Val) : VR U v v
  | mem {m m' : Mem} : Mem.EqOff U m m' → VR U (.mem m) (.mem m')
  | tuple {vs ws : List Val} : VRL U vs ws → VR U (.tuple vs) (.tuple ws)
/-- Related lists of registers. -/
inductive VRL (U : Blk → Prop) : List Val → List Val → Prop where
  | nil : VRL U [] []
  | cons {a b : Val} {as bs : List Val} : VR U a b → VRL U as bs → VRL U (a :: as) (b :: bs)
end

variable {U : Blk → Prop}

theorem VRL.refl : (vs : List Val) → VRL U vs vs
  | [] => .nil
  | v :: vs => .cons (.refl v) (VRL.refl vs)

theorem VRL.append : {as bs cs ds : List Val} → VRL U as bs → VRL U cs ds →
    VRL U (as ++ cs) (bs ++ ds)
  | _, _, _, _, .nil, h' => h'
  | _, _, _, _, .cons h1 t, h' => .cons h1 (VRL.append t h')

theorem VRL.length : {as bs : List Val} → VRL U as bs → bs.length = as.length
  | _, _, .nil => rfl
  | _, _, .cons _ t => by simp [VRL.length t]

theorem VRL.get : {as bs : List Val} → VRL U as bs →
    ∀ {i : Nat} {a : Val}, as[i]? = some a → ∃ b, bs[i]? = some b ∧ VR U a b
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons h1 _, 0, _, hi => by simp at hi; subst hi; exact ⟨_, rfl, h1⟩
  | _, _, .cons _ t, i + 1, _, hi => VRL.get t (by simpa using hi)

theorem VRL.getD {as bs : List Val} (h : VRL U as bs) (i : Nat) :
    VR U (as.getD i .poison) (bs.getD i .poison) := by
  cases ha : as[i]? with
  | none =>
    have hb : bs[i]? = none := by
      rw [List.getElem?_eq_none_iff] at ha ⊢; rw [h.length]; exact ha
    simp [List.getD, ha, hb]; exact .refl _
  | some a =>
    obtain ⟨b, hb, hab⟩ := h.get ha
    simp [List.getD, ha, hb]; exact hab

theorem VRL.dropLast : {as bs : List Val} → VRL U as bs → VRL U as.dropLast bs.dropLast
  | _, _, .nil => .nil
  | _, _, .cons _ .nil => .nil
  | _, _, .cons h1 (.cons h2 t) => .cons h1 (VRL.dropLast (.cons h2 t))

theorem VRL.getLast? : {as bs : List Val} → VRL U as bs →
    (as.getLast? = none ∧ bs.getLast? = none) ∨
      ∃ a b, as.getLast? = some a ∧ bs.getLast? = some b ∧ VR U a b
  | _, _, .nil => .inl ⟨rfl, rfl⟩
  | _, _, .cons h1 .nil => .inr ⟨_, _, rfl, rfl, h1⟩
  | _, _, .cons _ (.cons h2 t) => by
    rcases VRL.getLast? (.cons h2 t) with ⟨h3, -⟩ | ⟨x, y, hx, hy, hxy⟩
    · simp at h3
    · refine .inr ⟨x, y, ?_, ?_, hxy⟩
      · rw [List.getLast?_cons_cons]; exact hx
      · rw [List.getLast?_cons_cons]; exact hy

/-- A related value that is neither a memory nor a tuple is the source's. -/
theorem VR.eq {a b : Val} (h : VR U a b) (hm : ∀ m, a ≠ .mem m) (ht : ∀ vs, a ≠ .tuple vs) :
    b = a := by
  cases h with
  | refl => rfl
  | mem => exact absurd rfl (hm _)
  | tuple => exact absurd rfl (ht _)

theorem VR.mem_inv {m : Mem} {b : Val} (h : VR U (.mem m) b) :
    ∃ m', b = .mem m' ∧ Mem.EqOff U m m' := by
  cases h with
  | refl => exact ⟨m, rfl, EqOff.refl U m⟩
  | mem h => exact ⟨_, rfl, h⟩

theorem VR.tuple_inv {vs : List Val} {b : Val} (h : VR U (.tuple vs) b) :
    ∃ ws, b = .tuple ws ∧ VRL U vs ws := by
  cases h with
  | refl => exact ⟨vs, rfl, VRL.refl vs⟩
  | tuple h => exact ⟨_, rfl, h⟩

/-! ## Retyping -/

mutual
theorem VR.retype : {a b : Val} → VR U a b → (t : Ty) → VR U (a.retype t) (b.retype t)
  | _, _, .refl _, _ => .refl _
  | _, _, .mem h, t => by
    cases t with
    | mem => exact .mem h
    | int w => cases w <;> exact .refl _
    | _ => exact .refl _
  | _, _, .tuple (vs := vs) (ws := ws) h, t => by
    cases t with
    | tuple ts =>
      unfold Val.retype
      rcases VRL.retypePre h ts with ⟨h1, h2⟩ | ⟨vs', ws', h1, h2, h3⟩
      · rw [h1, h2]; exact .refl _
      · rw [h1, h2]; exact .tuple h3
    | int w => cases w <;> exact .refl _
    | _ => exact .refl _
theorem VRL.retypePre : {as bs : List Val} → VRL U as bs → (ts : List Ty) →
    (Val.retypePre ts as = none ∧ Val.retypePre ts bs = none) ∨
      ∃ as' bs', Val.retypePre ts as = some as' ∧ Val.retypePre ts bs = some bs' ∧ VRL U as' bs'
  | _, _, h, [] => .inr ⟨_, _, rfl, rfl, h⟩
  | _, _, .nil, _ :: _ => .inl ⟨rfl, rfl⟩
  | _, _, .cons (a := a) (b := b) h1 t, t0 :: ts => by
    simp only [Val.retypePre]
    rcases VRL.retypePre t ts with ⟨h2, h3⟩ | ⟨as', bs', h2, h3, h4⟩
    · rw [h2, h3]; exact .inl ⟨rfl, rfl⟩
    · rw [h2, h3]; exact .inr ⟨_, _, rfl, rfl, .cons (VR.retype h1 t0) h4⟩
end

/-! ## Shapes, encodings, poison -/

mutual
theorem VR.hasTy : {a b : Val} → VR U a b → (t : Ty) → b.hasTy t = a.hasTy t
  | _, _, .refl _, _ => rfl
  | _, _, .mem _, t => by cases t <;> rfl
  | _, _, .tuple h, t => by
    cases t with
    | tuple ts => simp only [Val.hasTy]; exact VRL.hasTyPre h ts
    | _ => rfl
theorem VRL.hasTyPre : {as bs : List Val} → VRL U as bs → (ts : List Ty) →
    Val.hasTyPre bs ts = Val.hasTyPre as ts
  | _, _, _, [] => by simp [Val.hasTyPre]
  | _, _, .nil, _ :: _ => rfl
  | _, _, .cons h t, t0 :: ts => by
    simp only [Val.hasTyPre, VR.hasTy h t0, VRL.hasTyPre t ts]
end

theorem VR.encode {a b : Val} (h : VR U a b) (t : Ty) : encode t b = encode t a := by
  cases h with
  | refl => rfl
  | mem => rw [encode_mem, encode_mem]
  | tuple => rw [encode_tuple, encode_tuple]

mutual
theorem VR.hasPoison : {a b : Val} → VR U a b → b.hasPoison = a.hasPoison
  | _, _, .refl _ => rfl
  | _, _, .mem _ => rfl
  | _, _, .tuple h => by simp only [Val.hasPoison]; exact VRL.anyPoison h
theorem VRL.anyPoison : {as bs : List Val} → VRL U as bs → Val.anyPoison bs = Val.anyPoison as
  | _, _, .nil => rfl
  | _, _, .cons h t => by simp only [Val.anyPoison, VR.hasPoison h, VRL.anyPoison t]
end

end GoFV.Proof.DAE
