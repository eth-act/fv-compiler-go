import GoFV.SSA.Sem.Run
import GoFV.Proof.Order

/-!
# Evaluating a block's values: `evalAll` basics

`evalAll` evaluates a list of values in order, storing each result: its unfolding
(`evalAll_cons`, `evalAll_append`), single register updates (`Frame.set`) and dependency orders
in the form the evaluation lemmas use (`TopoRem`). The comparisons with a reference frame are in
`GoFV.Proof.Sim`.
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

end GoFV.Proof
