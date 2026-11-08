import GoFV.SSA.Sem.RunLoc

variable [GoFV.SSA.Sem.Addrs]

/-!
# What `LocCtx.signOf` reads of a function

`runLoc`'s `MOVDreg`/`MOVDnop` (`movdLoc`) copy the upper bits of their argument's register as
`LocCtx.signOf` determines them: a `LoadReg` by its type, a `Copy` through its argument, any other
value as under `runL` (`Arm64.signExtendsIn`: its op, or a selector of `LDPSW`). `signView val? o`
is what `signOf` reads of value `o` of the value table `val?` (`signOf_succ`); two contexts with the
same tables whose functions have the same `signView` at every ID have the same `signOf`
(`signOf_congr`).
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem

/-- What `LocCtx.signOf` reads of a value. -/
inductive SignView where
  | load (t : TypeRef)
  | copy (a : Option ID)
  | other (b : Bool)
  deriving DecidableEq

/-- What `LocCtx.signOf` reads of value `o` (`none`: absent) of the value table `val?`. -/
def signView (val? : ID → Option Value) : Option Value → SignView
  | some u =>
    match u.op with
    | .LoadReg => .load u.type
    | .Copy => .copy u.args[0]?
    | _ => .other (Arm64.signExtendsIn val? u)
  | none => .other false

/-- One step of `signOf`, through `signView`. -/
def signStep (tabs : Tables) (rec : ID → Bool) : SignView → Bool
  | .load t => typeSigned tabs t
  | .copy (some a) => rec a
  | .copy none => false
  | .other b => b

theorem signOf_succ (lc : LocCtx) (n : Nat) (id : ID) :
    lc.signOf (n + 1) id =
      signStep lc.ctx.tabs (lc.signOf n) (signView lc.ctx.f.value? (lc.ctx.f.value? id)) := by
  unfold LocCtx.signOf
  cases lc.ctx.f.value? id with
  | none => rfl
  | some u =>
    simp only [signView]
    split <;> rename_i h <;> simp only [h] <;> try rfl
    · cases u.args[0]? <;> rfl

/-- Two contexts with the same tables and `signView`s have the same `signOf`. -/
theorem signOf_congr {lc lc' : LocCtx} (ht : lc.ctx.tabs = lc'.ctx.tabs)
    (h : ∀ id, signView lc.ctx.f.value? (lc.ctx.f.value? id) =
      signView lc'.ctx.f.value? (lc'.ctx.f.value? id)) :
    ∀ n id, lc.signOf n id = lc'.signOf n id := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro id
    rw [signOf_succ, signOf_succ, h id, ht]
    have : lc.signOf n = lc'.signOf n := funext ih
    rw [this]

end GoFV.Proof
