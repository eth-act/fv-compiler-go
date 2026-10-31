import GoFV.Proof.Frame

/-!
# Facts about one value's evaluation

* `evalValue_typed`: a value's result is fixed by `Val.retype` at its own type shape, so every
  register of a run is (`Typed`, preserved by `enterBlock`: `typed_enter`).
* `evalValue_copy`: a `Copy` yields its argument at the copy's shape.
* `evalValue_eq_of_args`: two values with the same op, aux, auxint and ID whose arguments hold
  the same registers evaluate alike (in contexts agreeing on the value's shape, the tables and
  the parameters).
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem

theorem retype_idem (t : Ty) (v : Val) : (v.retype t).retype t = v.retype t := by
  cases t <;> cases v <;> try rfl
  rename_i w' w x
  by_cases h : w'.bits ≤ w.bits
  · simp [Val.retype, h]
  · simp [Val.retype, h]

theorem retype_of_hasTy {t : Ty} {v : Val} (h : v.hasTy t = true) : v.retype t = v := by
  cases t <;> cases v <;> try rfl
  rename_i w' w x
  simp only [Val.hasTy, beq_iff_eq] at h
  subst h
  simp [Val.retype]

/-- Every register of a frame is fixed by `retype` at its value's shape. -/
def Typed (ctx : Ctx) (fr : Frame) : Prop :=
  ∀ (x : ID) (y : Val), fr.regs[x]? = some (some y) → y.retype (ctx.tys[x]?.getD .other) = y

theorem typed_replicate (ctx : Ctx) (n : Nat) (fr : Frame) (h : fr.regs = Array.replicate n none) :
    Typed ctx fr := fun x y hx => by
  rw [h, Array.getElem?_replicate] at hx
  split at hx <;> cases hx

theorem argVal_typed {ctx : Ctx} {fr : Frame} {n : AuxRef} {off : Int} {ty : Ty} {y : Val}
    (h : argVal ctx fr n off ty = .ok y) : y.retype ty = y := by
  unfold argVal at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
      split
      · rename_i hc
        simp only [Bool.and_eq_true] at hc
        exact retype_of_hasTy hc.2
      · cases ty <;> rfl

theorem callExtern_typed {env : Env} {callee : String} {args : List Val} {y : Val} (t : Ty)
    (h : callExtern env callee args = .ok y) : y.retype t = y := by
  unfold callExtern at h
  simp only at h
  split at h
  · simp only [bind, Res.bind] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h; cases t <;> rfl
        · cases h
        · cases h
  · cases h

theorem panicBounds_not_ok {k : Int64} {args : List Val} {y : Val} :
    panicBounds k args ≠ .ok y := by
  unfold panicBounds
  split <;> nofun

/-- A value's result is fixed by `retype` at its own shape. -/
theorem evalValue_typed {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {y : Val}
    (h : evalValue env ctx fr v = .ok y) : y.retype (ctx.tys[v.id]?.getD .other) = y := by
  unfold evalValue at h
  cases hm : v.args.toList.mapM (fun a =>
      Res.ofOption s!"v{v.id}: argument v{a} has no value" (fr.regs[a]?).join) with
  | panic e m => rw [hm] at h; cases h
  | stuck msg => rw [hm] at h; cases h
  | ok argv =>
    rw [hm] at h
    simp only [bind, Res.bind] at h
    split at h
    · cases h; cases (ctx.tys[v.id]?.getD .other) <;> rfl
    · split at h
      · exact argVal_typed h
      · cases h
    · split at h
      · exact argVal_typed h
      · cases h
    · exact absurd h panicBounds_not_ok
    · split at h
      · exact callExtern_typed _ h
      · cases h
    · split at h
      · exact callExtern_typed _ h
      · cases h
    · split at h
      · cases h
      · cases h; exact retype_idem _ _

theorem evalValue_copy {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {w : ID} {y : Val}
    (hop : v.op = .Copy) (ha : v.args = #[w]) (hw : fr.regs[w]? = some (some y)) :
    evalValue env ctx fr v = .ok (y.retype (ctx.tys[v.id]?.getD .other)) := by
  unfold evalValue
  rw [ha]
  simp only [List.mapM_cons, List.mapM_nil, hw, Option.join, bind, Res.bind, Res.ofOption, pure, hop]
  rfl

theorem mapM_ofOption_eq {m m' : ID → String} {r r' : ID → Option Val} :
    ∀ {l l' : List ID}, l.length = l'.length →
      (∀ (k : Nat) a, l[k]? = some a → ∃ a' y, l'[k]? = some a' ∧ r a = some y ∧ r' a' = some y) →
      l.mapM (fun a => Res.ofOption (m a) (r a)) = l'.mapM (fun a => Res.ofOption (m' a) (r' a))
  | [], [], _, _ => rfl
  | a :: l, a' :: l', hl, h => by
    obtain ⟨b, y, hb, hy, hy'⟩ := h 0 a rfl
    cases hb
    rw [List.mapM_cons, List.mapM_cons, hy, hy',
      mapM_ofOption_eq (l := l) (l' := l') (by simpa using hl) (fun k x hx => h (k + 1) x hx)]
    rfl
  | [], _ :: _, hl, _ => nomatch hl
  | _ :: _, [], hl, _ => nomatch hl

theorem argVal_params {ctx ctx' : Ctx} (h : ctx'.params = ctx.params) (fr : Frame) (n : AuxRef)
    (off : Int) (ty : Ty) : argVal ctx' fr n off ty = argVal ctx fr n off ty := by
  unfold argVal; rw [h]

theorem evalValue_eq_of_args {env : Env} {ctx ctx' : Ctx} {fr fr' : Frame} {v v' : Value}
    (hop : v'.op = v.op) (haux : v'.aux = v.aux) (hai : v'.auxInt = v.auxInt) (hid : v'.id = v.id)
    (hsz : v'.args.size = v.args.size)
    (hargs : ∀ (k : Nat) (a : ID), v.args[k]? = some a →
      ∃ a' y, v'.args[k]? = some a' ∧ fr.regs[a]? = some (some y) ∧ fr'.regs[a']? = some (some y))
    (hfr : fr' = { fr with regs := fr'.regs }) (hty : ctx'.tys[v.id]? = ctx.tys[v.id]?)
    (htabs : ctx'.tabs = ctx.tabs) (hpar : ctx'.params = ctx.params) :
    evalValue env ctx' fr' v' = evalValue env ctx fr v := by
  unfold evalValue
  rw [mapM_ofOption_eq (l := v'.args.toList) (l' := v.args.toList)
    (m := fun a => s!"v{v'.id}: argument v{a} has no value")
    (m' := fun a => s!"v{v.id}: argument v{a} has no value")
    (r := fun a => (fr'.regs[a]?).join) (r' := fun a => (fr.regs[a]?).join) (by simp [hsz])
    (fun k a' ha' => by
      have hk : k < v.args.size := by
        have := (List.getElem?_eq_some_iff.1 ha').1; simp at this; omega
      obtain ⟨a'', y, h1, h2, h3⟩ := hargs k v.args[k] (by simp [hk])
      rw [Array.getElem?_toList] at ha'
      rw [ha'] at h1; cases h1
      exact ⟨v.args[k], y, by simp [hk], by simp [h3], by simp [h2]⟩)]
  rw [hop, haux, hai, hid, hty, htabs, hfr]
  simp only [argVal_regs, argVal_params hpar]

theorem tys_make {tabs : Tables} {f : Func} {x : ID} {v : Value} (h : f.value? x = some v) :
    (Ctx.make tabs f).tys[x]? = some (tabs.ty v.type) := by
  unfold Func.value? at h
  simp only [Ctx.make, Array.getElem?_map]
  cases hx : f.valueTab[x]? with
  | none => rw [hx] at h; cases h
  | some o => rw [hx] at h; simp at h; subst h; rfl

end GoFV.Proof
