import GoFV.Proof.Pass.NilRel
import GoFV.Proof.Pass.CSEBlock

/-!
# nilcheckelim: evaluating the changed values

`NN q`: a nil check passes on `q` (the condition of `memRoot`'s `NilCheck` case). A nil check
that passed on `q` returned `q` (`nilCheck_ok`); a nil check on a value `NN` holds of never
panics and passes on any memory (`nilCheck_nn`). So a `NilCheck p` whose pointer some earlier
nil check passed on evaluates to the pointer, as the `Copy` of that check does, and an
`IsNonNil p` to `true`, as `ConstBool [1]` does.
-/

namespace GoFV.Proof.Nil

open GoFV.SSA GoFV.SSA.Sem GoFV.Proof.CSE

/-- A nil check passes on `q`. -/
def NN : Val → Prop
  | .ptr p => p.isNil = false
  | .int .w64 x => x ≠ 0
  | _ => False

theorem evalOp_nilCheck {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (h : v.op = .NilCheck) : evalOp env ctx fr v argv ty = memRoot ctx v argv := by
  simp only [evalOp, h]

/-- A nil check that passes returns its pointer, which it passes on. -/
theorem nilCheck_ok {ctx : Ctx} {n : Value} {argv : List Val} {r : Val} (hn : n.op = .NilCheck)
    (h : memRoot ctx n argv = .ok r) : ∃ a, argv = [r, a] ∧ NN r := by
  unfold memRoot at h
  rw [hn] at h
  split at h <;> (try simp only [reduceCtorEq] at *)
  all_goals first
    | (split at h <;> cases h <;> rename_i hh <;> exact ⟨_, rfl, by simpa [NN] using hh⟩)
    | (split at h <;> cases h)
    | skip

theorem nilCheck_nn {ctx : Ctx} {n : Value} {q a : Val} (hn : n.op = .NilCheck) (hq : NN q) :
    (∀ e m, memRoot ctx n [q, a] ≠ .panic e m) ∧ (∀ m, a = .mem m → memRoot ctx n [q, a] = .ok q) := by
  match q, hq with
  | .ptr p, hq =>
    simp only [NN] at hq
    constructor
    · intro e m h
      unfold memRoot at h; rw [hn] at h
      split at h <;> (try simp only [reduceCtorEq] at *) <;> (try split at h) <;> simp_all
    · rintro m rfl
      unfold memRoot; rw [hn]; simp [hq]
  | .int .w64 x, hq =>
    simp only [NN] at hq
    constructor
    · intro e m h
      unfold memRoot at h; rw [hn] at h
      split at h <;> (try simp only [reduceCtorEq] at *) <;> (try split at h) <;> simp_all
    · rintro m rfl
      unfold memRoot; rw [hn]; simp only [beq_iff_eq, hq, ite_false]


/-- A value no nil check panics on and that pointer arithmetic keeps so: a pointer into an
allocation, an integer address of one, or any non-address value. -/
def Safe : Val → Prop
  | .ptr q => q.blk ≠ .nil
  | .int .w64 x => (Ptr.ofAddr x).blk ≠ .nil
  | _ => True

theorem ofAddr_zero : (Ptr.ofAddr 0).blk = .nil := by decide

/-- No nil check panics on a `Safe` value. -/
theorem nilCheck_safe {ctx : Ctx} {n : Value} {q b : Val} (hn : n.op = .NilCheck) (hq : Safe q)
    {e : Panic} {m : Mem} : memRoot ctx n [q, b] ≠ .panic e m := by
  intro h
  unfold memRoot at h
  rw [hn] at h
  split at h <;> (try simp only [reduceCtorEq] at *) <;> (try split at h) <;> try simp_all [Safe]
  all_goals sorry

/-- A nil check that passes returns a `Safe` value (it checked the pointer points into an
allocation). -/
theorem nilCheck_ok_safe {ctx : Ctx} {n : Value} {argv : List Val} {r : Val}
    (hn : n.op = .NilCheck) (h : memRoot ctx n argv = .ok r) : Safe r := by
  sorry

/-- `Safe` survives taking a pointer shape. -/
theorem safe_retype_ptr {v : Val} (e : Option Nat) (h : Safe v) : Safe (v.retype (.ptr e)) := by
  match v, h with
  | .int .w64 x, h => simpa [Val.retype, Safe] using h
  | .ptr q, h => simpa [Val.retype, Safe] using h
  | .int .w8 x, _ | .int .w16 x, _ | .int .w32 x, _ | .bool _, _ | .mem _, _ | .tuple _, _
  | .agg _, _ | .blob _, _ | .empty, _ | .poison, _ => simp [Val.retype, Safe]

end GoFV.Proof.Nil
