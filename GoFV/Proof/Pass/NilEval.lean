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

/-- A nil check passes on `q`: a pointer into an allocation, or an address `Ptr.ofAddr` maps
into one (§6: a check of any pointer into `Blk.nil` panics). -/
def NN : Val → Prop
  | .ptr p => p.blk ≠ .nil
  | .int .w64 x => (Ptr.ofAddr x).blk ≠ .nil
  | _ => False

theorem evalOp_nilCheck {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val}
    {ty : Ty} (h : v.op = .NilCheck) : evalOp env ctx fr v argv ty = memRoot ctx v argv := by
  simp only [evalOp, h]

/-- `NN` through `Val.asPtrWord`: the word reads as a pointer outside `Blk.nil`. -/
theorem nn_iff {q : Val} : NN q ↔ ∃ p, q.asPtrWord = some p ∧ p.blk ≠ .nil := by
  rcases q with ⟨_ | _ | _ | _, x⟩ | _ | _ | _ | q | _ | _ | _ | _ <;>
    simp [NN, Val.asPtrWord]

/-- A nil check that passes returns its pointer, which it passes on. -/
theorem nilCheck_ok {ctx : Ctx} {n : Value} {argv : List Val} {r : Val} (hn : n.op = .NilCheck)
    (h : memRoot ctx n argv = .ok r) : ∃ a, argv = [r, a] ∧ NN r := by
  obtain ⟨a, m, p, rfl, hp, he⟩ := memRoot_nilCheck_res hn h (fun _ => nofun)
  by_cases hb : p.blk = .nil
  · simp [hb] at he
  · simp only [hb, beq_iff_eq, ↓reduceIte, Res.ok.injEq] at he
    subst he
    exact ⟨_, rfl, nn_iff.2 ⟨p, hp, hb⟩⟩

/-- A nil check that panics does so on a pointer or address it does not pass on, with its
memory argument. -/
theorem nilCheck_panic {ctx : Ctx} {n : Value} {argv : List Val} {e : Panic} {m : Mem}
    (hn : n.op = .NilCheck) (h : memRoot ctx n argv = .panic e m) :
    ∃ q, argv = [q, .mem m] ∧ e = .nilDeref ∧ ¬ NN q ∧
      ((∃ p, q = .ptr p) ∨ ∃ x, q = .int .w64 x) := by
  obtain ⟨a, m', p, rfl, hp, he⟩ := memRoot_nilCheck_res hn h (fun _ => nofun)
  by_cases hb : p.blk = .nil
  · simp only [hb, beq_self_eq_true, ↓reduceIte, Res.panic.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨a, rfl, rfl, fun hn => ?_, ?_⟩
    · obtain ⟨p', hp', hb'⟩ := nn_iff.1 hn
      rw [hp] at hp'; cases hp'; exact hb' hb
    · rcases a with ⟨_ | _ | _ | _, x⟩ | _ | _ | _ | q | _ | _ | _ | _ <;>
        simp_all [Val.asPtrWord]
  · simp [hb] at he

/-- A nil check panics on a pointer or address it does not pass on. -/
theorem nilCheck_panic_of {ctx : Ctx} {n : Value} {q : Val} {m : Mem} (hn : n.op = .NilCheck)
    (hq : ¬ NN q) (hs : (∃ p, q = .ptr p) ∨ ∃ x, q = .int .w64 x) :
    memRoot ctx n [q, .mem m] = .panic .nilDeref m := by
  rcases hs with ⟨p, rfl⟩ | ⟨x, rfl⟩
  · simp only [NN, Classical.not_not] at hq
    unfold memRoot; rw [hn]; simp [Val.asPtrWord, hq]
  · simp only [NN, Classical.not_not] at hq
    unfold memRoot; rw [hn]; simp [Val.asPtrWord, hq]

/-- A nil check on a value it passes on returns it, on any memory, and never panics. -/
theorem nilCheck_nn {ctx : Ctx} {n : Value} {q a : Val} (hn : n.op = .NilCheck) (hq : NN q) :
    (∀ e m, memRoot ctx n [q, a] ≠ .panic e m) ∧
      (∀ m, a = .mem m → memRoot ctx n [q, a] = .ok q) := by
  refine ⟨fun e m h => ?_, fun m ha => ?_⟩
  · obtain ⟨q', hq', -, hnn, -⟩ := nilCheck_panic hn h
    simp only [List.cons.injEq] at hq'
    rw [hq'.1] at hq; exact hnn hq
  · subst ha
    obtain ⟨p, hp, hb⟩ := nn_iff.1 hq
    unfold memRoot; rw [hn]; simp [hp, hb]

/-- A value no nil check panics on and that pointer arithmetic keeps so: a pointer into an
allocation, an integer address of one, or any non-address value. -/
def Safe : Val → Prop
  | .ptr q => q.blk ≠ .nil
  | .int .w64 x => (Ptr.ofAddr x).blk ≠ .nil
  | _ => True

theorem ofAddr_zero : (Ptr.ofAddr 0).blk = .nil := by decide

theorem nn_of_safe {q : Val} (hq : Safe q) (hs : (∃ p, q = .ptr p) ∨ ∃ x, q = .int .w64 x) :
    NN q := by
  rcases hs with ⟨p, rfl⟩ | ⟨x, rfl⟩
  · exact hq
  · exact hq

/-- No nil check panics on a `Safe` value. -/
theorem nilCheck_safe {ctx : Ctx} {n : Value} {q b : Val} (hn : n.op = .NilCheck) (hq : Safe q)
    {e : Panic} {m : Mem} : memRoot ctx n [q, b] ≠ .panic e m := by
  intro h
  obtain ⟨q', hq', -, hnn, hs⟩ := nilCheck_panic hn h
  simp only [List.cons.injEq] at hq'
  rw [← hq'.1] at hs hnn
  exact hnn (nn_of_safe hq hs)

/-- A nil check that passes returns a `Safe` value (it checked the pointer points into an
allocation). -/
theorem nilCheck_ok_safe {ctx : Ctx} {n : Value} {argv : List Val} {r : Val}
    (hn : n.op = .NilCheck) (h : memRoot ctx n argv = .ok r) : Safe r := by
  obtain ⟨-, -, hr⟩ := nilCheck_ok hn h
  unfold NN at hr
  split at hr
  · exact hr
  · exact hr
  · exact hr.elim

/-- `Safe` survives taking a pointer shape. -/
theorem safe_retype_ptr {v : Val} (e : Option Nat) (h : Safe v) : Safe (v.retype (.ptr e)) := by
  match v, h with
  | .int .w64 x, h => simpa [Val.retype, Safe] using h
  | .ptr q, h => simpa [Val.retype, Safe] using h
  | .int .w8 x, _ | .int .w16 x, _ | .int .w32 x, _ | .bool _, _ | .mem _, _ | .tuple _, _
  | .agg _, _ | .blob _, _ | .empty, _ | .poison, _ => simp [Val.retype, Safe]

end GoFV.Proof.Nil
