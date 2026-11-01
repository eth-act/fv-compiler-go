import GoFV.Proof.Pass.WBEval
import GoFV.Proof.Enter

/-!
# Entering a block whose values satisfy a register property (issue #36)

`enter_Q`: a listed block of a well-formed function whose `Phi`s read arguments satisfying a
register property `Q` (after `retype`), and whose other values satisfy `LocalQ` with their
arguments outside the block in a set `S` of registers satisfying `Q`, is entered successfully;
afterwards every value of the block and of `S` holds a register satisfying `Q`, and the
registers outside the block are unchanged. `enter_Q_panic`: if the schedule is
`pre ++ r :: post`, the values of `pre` satisfy `LocalQ` and `r` panics on every frame whose
argument registers satisfy `Q`, the entry panics.
-/

namespace GoFV.Proof.WB

open GoFV.SSA GoFV.SSA.Sem

section
variable {ce : CheckEnv} {tabs : Tables} {g : Func} {env : Env} {fr0 : Frame}
  {Q : ID → Val → Prop}

theorem enter_Q (hwg : WF ce g) {cid : ID} {C : Block} (hc : cid ∈ g.blocks)
    (hC : g.block? cid = some C) (hsch : ∃ o, schedule g C = some o) {F : Frame} {e : Nat}
    (hF : F = { fr0 with regs := F.regs }) (hs : F.regs.size = g.valueTab.size)
    (hphi : ∀ x ∈ C.values, ∀ v, g.value? x = some v → v.op = .Phi →
      ∃ a z, v.args[e]? = some a ∧ F.regs[a]? = some (some z) ∧
        Q x (z.retype ((Ctx.make tabs g).tys[x]?.getD .other)))
    (S : ID → Prop) (hS : ∀ a, S a → ∃ z, F.regs[a]? = some (some z) ∧ Q a z)
    (hSC : ∀ a, S a → a ∉ C.values)
    (hloc : ∀ x ∈ C.values, ∀ v, g.value? x = some v → v.op ≠ .Phi →
      LocalQ env (Ctx.make tabs g) fr0 Q x)
    (hargs : ∀ x ∈ C.values, ∀ v, g.value? x = some v → v.op ≠ .Phi →
      ∀ a ∈ v.args, a ∉ C.values → S a) :
    ∃ F', enterBlock env (Ctx.make tabs g) F C e = .ok F' ∧ F' = { fr0 with regs := F'.regs } ∧
      F'.regs.size = F.regs.size ∧
      (∀ a, (S a ∨ a ∈ C.values) → ∃ z, F'.regs[a]? = some (some z) ∧ Q a z) ∧
      (∀ a, a ∉ C.values → F'.regs[a]? = F.regs[a]?) := by
  sorry

theorem enter_Q_panic (hwg : WF ce g) {cid : ID} {C : Block} (hc : cid ∈ g.blocks)
    (hC : g.block? cid = some C) {o : Array ID} (ho : schedule g C = some o)
    {pre post : List ID} {r : ID} (hsplit : o.toList = pre ++ r :: post) {F : Frame} {e : Nat}
    (hF : F = { fr0 with regs := F.regs }) (hs : F.regs.size = g.valueTab.size)
    (hphi : ∀ x ∈ C.values, ∀ v, g.value? x = some v → v.op = .Phi →
      ∃ a z, v.args[e]? = some a ∧ F.regs[a]? = some (some z) ∧
        Q x (z.retype ((Ctx.make tabs g).tys[x]?.getD .other)))
    (S : ID → Prop) (hS : ∀ a, S a → ∃ z, F.regs[a]? = some (some z) ∧ Q a z)
    (hSC : ∀ a, S a → a ∉ C.values)
    (hloc : ∀ x ∈ pre, LocalQ env (Ctx.make tabs g) fr0 Q x)
    (hargs : ∀ x ∈ C.values, ∀ v, g.value? x = some v → v.op ≠ .Phi →
      ∀ a ∈ v.args, a ∉ C.values → S a)
    {ep : Panic} {m : Mem}
    (hr : ∀ g' : Frame, g' = { fr0 with regs := g'.regs } →
      (∀ a ∈ argsF g r, ∃ z, g'.regs[a]? = some (some z) ∧ Q a z) →
      stepV env (Ctx.make tabs g) g' r = .panic ep m) :
    enterBlock env (Ctx.make tabs g) F C e = .panic ep m := by
  sorry

end

end GoFV.Proof.WB
