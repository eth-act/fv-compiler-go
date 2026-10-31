import GoFV.SSA.Sem.Run
import GoFV.Proof.Order

/-!
# Evaluating a block's values against a reference frame

`evalAll` evaluates a list of values in order, storing each result. The lemmas here compare one
run of `evalAll` with a *reference frame* `G` that already holds the expected value of every
listed value: if each value, evaluated in any frame that agrees with `G` on its arguments,
yields its expected value (a purely local obligation), and the list is a dependency order,
then `evalAll` ends in a frame that agrees with `G` (`evalAll_ref_ok`), or panics where the
reference says so (`evalAll_ref_panic`). Pass proofs take `G` from the source run.
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem

/-- One step of `evalAll`: value `id` evaluated in frame `fr`. -/
def stepV (env : Env) (ctx : Ctx) (fr : Frame) (id : ID) : Res Val :=
  match ctx.f.value? id with
  | none => .stuck s!"v{id} is not in the function"
  | some v => evalValue env ctx fr v

/-- `fr` with value `id` set to `x`. -/
def _root_.GoFV.SSA.Sem.Frame.set (fr : Frame) (id : ID) (x : Val) : Frame :=
  { fr with regs := fr.regs.set! id (some x) }

theorem evalAll_nil (env : Env) (ctx : Ctx) (fr : Frame) : evalAll env ctx fr [] = .ok fr := rfl

theorem evalAll_cons (env : Env) (ctx : Ctx) (fr : Frame) (id : ID) (ids : List ID) :
    evalAll env ctx fr (id :: ids) =
      match stepV env ctx fr id with
      | .ok x => evalAll env ctx (fr.set id x) ids
      | .panic e m => .panic e m
      | .stuck msg => .stuck msg := by
  conv => lhs; rw [evalAll]
  unfold stepV
  cases ctx.f.value? id <;> rfl

theorem evalAll_append (env : Env) (ctx : Ctx) (l1 l2 : List ID) :
    ∀ fr, evalAll env ctx fr (l1 ++ l2) =
      match evalAll env ctx fr l1 with
      | .ok fr' => evalAll env ctx fr' l2
      | .panic e m => .panic e m
      | .stuck msg => .stuck msg := by
  induction l1 with
  | nil => intro fr; rfl
  | cons id ids ih =>
    intro fr
    rw [List.cons_append, evalAll_cons, evalAll_cons]
    split
    · exact ih _
    · rfl
    · rfl

/-- `g` and `G` agree on the activation's inputs and on the registers of `P`. -/
structure Agree (g G : Frame) (P : ID → Prop) : Prop where
  args : g.args = G.args
  mem0 : g.mem0 = G.mem0
  regs : ∀ a, P a → g.regs[a]? = G.regs[a]?

/-- Each listed value's arguments are not listed at or after it. -/
def TopoRem (D : ID → List ID) : List ID → Prop
  | [] => True
  | x :: s => (∀ a ∈ D x, a ∉ x :: s) ∧ TopoRem D s

theorem topoRem_of {D : ID → List ID} : ∀ {o : List ID}, o.Nodup →
    (∀ (j : Nat) y, o[j]? = some y → ∀ a ∈ D y, a ∈ o → ∃ i < j, o[i]? = some a) →
    TopoRem D o
  | [], _, _ => trivial
  | x :: s, hn, hb => by
    have hxs : x ∉ s := (List.nodup_cons.1 hn).1
    refine ⟨fun a ha hmem => ?_, topoRem_of (List.nodup_cons.1 hn).2 fun j y hy a ha hs => ?_⟩
    · obtain ⟨i, hi, _⟩ := hb 0 x rfl a ha hmem
      exact absurd hi (Nat.not_lt_zero _)
    · obtain ⟨i, hi, hai⟩ := hb (j + 1) y (by simpa using hy) a ha (List.mem_cons_of_mem _ hs)
      cases i with
      | zero => cases hai; exact absurd hs hxs
      | succ i => exact ⟨i, by omega, by simpa using hai⟩

theorem Order.Topo.topoRem {N : ID → Prop} {D : ID → List ID} {o : List ID}
    (ht : Order.Topo N D o) : TopoRem D o :=
  topoRem_of ht.nodup fun j y hy a ha hmem => ht.before j y hy a ha ((ht.mem a).1 hmem)

theorem Frame.set_regs_self {fr : Frame} {id : ID} {x : Val} (h : id < fr.regs.size) :
    (fr.set id x).regs[id]? = some (some x) := by
  simp [Frame.set, h]

theorem Frame.set_regs_ne {fr : Frame} {id a : ID} {x : Val} (h : id ≠ a) :
    (fr.set id x).regs[a]? = fr.regs[a]? := by
  simp [Frame.set, Array.getElem?_setIfInBounds_ne h]

/-- **Reference evaluation, no panic.** If `g` agrees with `G` outside the list `o`, `o` is a
dependency order (`TopoRem`), and every listed value, evaluated in any frame agreeing with `G`
on its arguments, yields its value in `G`, then `evalAll` succeeds in a frame agreeing with `G`
everywhere. -/
theorem evalAll_ref_ok {env : Env} {ctx : Ctx} {G : Frame} {D : ID → List ID}
    (hloc : ∀ x ∈ o, ∃ v, G.regs[x]? = some (some v) ∧
      ∀ g, Agree g G (· ∈ D x) → stepV env ctx g x = .ok v) :
    ∀ {g : Frame}, o.Nodup → TopoRem D o → Agree g G (· ∉ o) → g.regs.size = G.regs.size →
      ∃ g', evalAll env ctx g o = .ok g' ∧ Agree g' G (fun _ => True) ∧
        g'.regs.size = G.regs.size := by
  induction o with
  | nil =>
    intro g _ _ ha hs
    exact ⟨g, rfl, ⟨ha.args, ha.mem0, fun a _ => ha.regs a (List.not_mem_nil)⟩, hs⟩
  | cons x s ih =>
    intro g hn ht ha hs
    obtain ⟨v, hGx, hstep⟩ := hloc x List.mem_cons_self
    have hx : stepV env ctx g x = .ok v :=
      hstep g ⟨ha.args, ha.mem0, fun a hD => ha.regs a (ht.1 a hD)⟩
    have hxlt : x < g.regs.size := by
      rw [hs]
      rcases Nat.lt_or_ge x G.regs.size with h | h
      · exact h
      · rw [Array.getElem?_eq_none h] at hGx; cases hGx
    rw [evalAll_cons, hx]
    refine ih (fun y hy => hloc y (List.mem_cons_of_mem _ hy)) (List.nodup_cons.1 hn).2 ht.2
      ⟨ha.args, ha.mem0, fun a ha' => ?_⟩ (by simp [Frame.set, hs])
    by_cases hax : a = x
    · subst hax; rw [Frame.set_regs_self hxlt, hGx]
    · rw [Frame.set_regs_ne (Ne.symm hax)]
      exact ha.regs a (by simp [hax, ha'])

/-- **Reference evaluation up to a panic.** As `evalAll_ref_ok` for the prefix `pre`, then
value `r`, evaluated in any frame agreeing with `G` on its arguments, panics. -/
theorem evalAll_ref_panic {env : Env} {ctx : Ctx} {G : Frame} {D : ID → List ID}
    {pre post : List ID} {r : ID} {e : Panic} {m : Mem}
    (hloc : ∀ x ∈ pre, ∃ v, G.regs[x]? = some (some v) ∧
      ∀ g, Agree g G (· ∈ D x) → stepV env ctx g x = .ok v)
    (hr : ∀ g, Agree g G (· ∈ D r) → stepV env ctx g r = .panic e m)
    {g : Frame} (hn : pre.Nodup) (ht : TopoRem D pre) (ha : Agree g G (· ∉ pre))
    (hs : g.regs.size = G.regs.size) :
    evalAll env ctx g (pre ++ r :: post) = .panic e m := by
  obtain ⟨g', h1, h2, _⟩ := evalAll_ref_ok hloc hn ht ha hs
  rw [evalAll_append, h1]
  show evalAll env ctx g' (r :: post) = _
  rw [evalAll_cons, hr g' ⟨h2.args, h2.mem0, fun a _ => h2.regs a trivial⟩]

end GoFV.Proof
