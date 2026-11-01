import GoFV.Proof.Sim

/-!
# Simulation by macro steps

`runLoop_simIH`: a simulation where one step of the relation may cover several source block
entries (a source path through blocks a pass merged into one target block) and any number of
target block entries. The step obligation (`hsim`) receives the induction hypothesis
`SimUpTo R n`: every related pair of states simulates for at most `n` source block entries; it
must show the pair simulates for `n + 1`. A step lemma unfolds the source's first block entries
with `runLoop_goto`, the target's with `simUpTo_goto`, and closes with the hypothesis at the
states where the relation holds again.
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem

/-- Related states simulate for runs of at most `n` source block entries: every defined source
run is refined by a target run with some fuel. -/
def SimUpTo (env : Env) (ctxS ctxT : Ctx) (R : Frame → ID → Nat → Frame → ID → Nat → Prop)
    (n : Nat) : Prop :=
  ∀ fuel, fuel ≤ n → ∀ frS bS iS frT bT iT, R frS bS iS frT bT iT →
    (runLoop env ctxS fuel frS bS iS).Defined →
      ∃ fuelT, OutcomeRefines ctxS.act (runLoop env ctxS fuel frS bS iS) (runLoop env ctxT fuelT frT bT iT)

/-- **Macro-step simulation.** -/
theorem runLoop_simIH {env : Env} {ctxS ctxT : Ctx}
    (R : Frame → ID → Nat → Frame → ID → Nat → Prop)
    (hsim : ∀ n, SimUpTo env ctxS ctxT R n → ∀ frS bS iS frT bT iT, R frS bS iS frT bT iT →
      (runLoop env ctxS (n + 1) frS bS iS).Defined →
        ∃ fuelT, OutcomeRefines ctxS.act (runLoop env ctxS (n + 1) frS bS iS)
          (runLoop env ctxT fuelT frT bT iT)) :
    ∀ fuel frS bS iS frT bT iT, R frS bS iS frT bT iT → (runLoop env ctxS fuel frS bS iS).Defined →
      ∃ fuelT, OutcomeRefines ctxS.act (runLoop env ctxS fuel frS bS iS) (runLoop env ctxT fuelT frT bT iT) := by
  have hall : ∀ n, SimUpTo env ctxS ctxT R n := by
    intro n
    induction n with
    | zero =>
      intro fuel hf _ _ _ _ _ _ _ hd
      rw [Nat.le_zero.1 hf] at hd; exact hd.elim
    | succ n ih =>
      intro fuel hf frS bS iS frT bT iT hR hd
      rcases Nat.lt_or_ge fuel (n + 1) with h | h
      · exact ih fuel (by omega) frS bS iS frT bT iT hR hd
      · obtain rfl : fuel = n + 1 := by omega
        exact hsim n ih frS bS iS frT bT iT hR hd
  intro fuel frS bS iS frT bT iT hR hd
  exact hall fuel fuel (Nat.le_refl _) frS bS iS frT bT iT hR hd

/-- A source block entry that continues along an edge. -/
theorem runLoop_goto {env : Env} {ctx : Ctx} {fuel : Nat} {fr fr' : Frame} {b : ID} {i : Nat}
    {e : Edge} (h : blockStep env ctx fr b i = .goto fr' e) :
    runLoop env ctx (fuel + 1) fr b i = runLoop env ctx fuel fr' e.b e.i :=
  (runLoop_blockStep env ctx fuel fr b i).1 fr' e h

theorem runLoop_ret {env : Env} {ctx : Ctx} {fuel : Nat} {fr : Frame} {b : ID} {i : Nat}
    {rs : List Val} {m : Mem} (h : blockStep env ctx fr b i = .ret rs m) :
    runLoop env ctx (fuel + 1) fr b i = .returned rs m :=
  (runLoop_blockStep env ctx fuel fr b i).2.1 rs m h

theorem runLoop_panic {env : Env} {ctx : Ctx} {fuel : Nat} {fr : Frame} {b : ID} {i : Nat}
    {e : Panic} {m : Mem} (h : blockStep env ctx fr b i = .panic e m) :
    runLoop env ctx (fuel + 1) fr b i = .panicked e m :=
  (runLoop_blockStep env ctx fuel fr b i).2.2.1 e m h

theorem runLoop_stuck {env : Env} {ctx : Ctx} {fuel : Nat} {fr : Frame} {b : ID} {i : Nat}
    (h : blockStep env ctx fr b i = .stuck) : ¬ (runLoop env ctx (fuel + 1) fr b i).Defined :=
  (runLoop_blockStep env ctx fuel fr b i).2.2.2 h

/-- The target continues along an edge: a refinement by the run from the next state is one by
the run from this state. -/
theorem refines_goto {env : Env} {ctx : Ctx} {act : Nat} {o : Outcome} {fr fr' : Frame} {b : ID} {i : Nat}
    {e : Edge} (h : blockStep env ctx fr b i = .goto fr' e)
    (hr : ∃ fuel, OutcomeRefines act o (runLoop env ctx fuel fr' e.b e.i)) :
    ∃ fuel, OutcomeRefines act o (runLoop env ctx fuel fr b i) := by
  obtain ⟨fuel, h'⟩ := hr
  exact ⟨fuel + 1, by rw [runLoop_goto h]; exact h'⟩

/-- A source run with no fuel left is not defined. -/
theorem runLoop_zero_not_defined {env : Env} {ctx : Ctx} {fr : Frame} {b : ID} {i : Nat} :
    ¬ (runLoop env ctx 0 fr b i).Defined := fun h => h

end GoFV.Proof
