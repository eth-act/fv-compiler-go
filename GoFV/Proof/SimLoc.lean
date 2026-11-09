import GoFV.Proof.CongLoc

variable [GoFV.SSA.Sem.Addrs]

/-!
# Simulation over `runLoc`

`GoFV.Proof.SimL` for the allocated runner `runLoopLoc`: one block entry (`blockStepLoc`,
`runLoopLoc_blockStep`), lock-step simulation (`runLoopLoc_sim`), simulation by macro steps
(`runLoopLoc_simIH`, `SimUpToLoc`), and the lift of a simulation of the loops from the entries
to `RefinesLoc` (`refinesLoc_of_loop`). Related states are equal machine states in the
passes proven so far, so the simulations conclude equal outcomes.

Block-level helpers:

* `enterListLoc_append`: running a concatenation of value lists;
* `stepTermLoc_plain`: a `Plain` block without controls goes to its first successor and
  leaves the state alone;
* `stepTermL_succs`, `NextRelLoc`: a terminator does not read its successors' targets: replacing
  them (`{b with succs := ss}`) relates the outcomes index by index.
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem

/-! ## Block steps -/

/-- The result of one block entry of `runLoopLoc`. -/
inductive StepLoc where
  | goto (s : LocState) (e : Edge)
  | ret (rs : List Val) (m : Mem)
  | panic (e : Panic) (m : Mem)
  | stuck

/-- One block entry of `runLoopLoc`: run block `bid`'s values, then its terminator. -/
def blockStepLoc (env : Env) (lc : LocCtx) (s : LocState) (bid : ID) : StepLoc :=
  match lc.ctx.f.block? bid with
  | none => .stuck
  | some b =>
    match enterBlockLoc env lc s b with
    | .panic e m => .panic e m
    | .stuck _ => .stuck
    | .ok s =>
      match stepTermLoc lc s b with
      | .ok (.goto e, s) => .goto s e
      | .ok (.ret rs m, _) => .ret rs m
      | .panic e m => .panic e m
      | .stuck _ => .stuck

/-- `runLoopLoc` through `blockStepLoc`. -/
theorem runLoopLoc_blockStep (env : Env) (lc : LocCtx) (fuel : Nat) (s : LocState) (bid : ID) :
    (∀ s' e, blockStepLoc env lc s bid = .goto s' e →
      runLoopLoc env lc (fuel + 1) s bid = runLoopLoc env lc fuel s' e.b) ∧
    (∀ rs m, blockStepLoc env lc s bid = .ret rs m →
      runLoopLoc env lc (fuel + 1) s bid = .returned rs m) ∧
    (∀ e m, blockStepLoc env lc s bid = .panic e m →
      runLoopLoc env lc (fuel + 1) s bid = .panicked e m) ∧
    (blockStepLoc env lc s bid = .stuck → ¬ (runLoopLoc env lc (fuel + 1) s bid).Defined) := by
  rw [runLoopLoc_succ]
  unfold blockStepLoc
  cases lc.ctx.f.block? bid with
  | none =>
    exact ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h), fun _ _ h => (nomatch h),
      fun _ h => h.elim⟩
  | some b =>
    simp only
    cases enterBlockLoc env lc s b with
    | panic e m =>
      refine ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h), ?_, fun h => (nomatch h)⟩
      intro _ _ h; cases h; rfl
    | stuck msg =>
      exact ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h), fun _ _ h => (nomatch h),
        fun _ h => h.elim⟩
    | ok s1 =>
      simp only
      cases stepTermLoc lc s1 b with
      | ok p =>
        obtain ⟨n, s2⟩ := p
        cases n with
        | goto e =>
          refine ⟨?_, fun _ _ h => (nomatch h), fun _ _ h => (nomatch h), fun h => (nomatch h)⟩
          intro _ _ h; cases h; rfl
        | ret rs m =>
          refine ⟨fun _ _ h => (nomatch h), ?_, fun _ _ h => (nomatch h), fun h => (nomatch h)⟩
          intro _ _ h; cases h; rfl
      | panic e m =>
        refine ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h), ?_, fun h => (nomatch h)⟩
        intro _ _ h; cases h; rfl
      | stuck msg =>
        exact ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h), fun _ _ h => (nomatch h),
          fun _ h => h.elim⟩

theorem runLoopLoc_goto {env : Env} {lc : LocCtx} {fuel : Nat} {s s' : LocState} {b : ID}
    {e : Edge} (h : blockStepLoc env lc s b = .goto s' e) :
    runLoopLoc env lc (fuel + 1) s b = runLoopLoc env lc fuel s' e.b :=
  (runLoopLoc_blockStep env lc fuel s b).1 s' e h

theorem runLoopLoc_ret {env : Env} {lc : LocCtx} {fuel : Nat} {s : LocState} {b : ID}
    {rs : List Val} {m : Mem} (h : blockStepLoc env lc s b = .ret rs m) :
    runLoopLoc env lc (fuel + 1) s b = .returned rs m :=
  (runLoopLoc_blockStep env lc fuel s b).2.1 rs m h

theorem runLoopLoc_panic {env : Env} {lc : LocCtx} {fuel : Nat} {s : LocState} {b : ID}
    {e : Panic} {m : Mem} (h : blockStepLoc env lc s b = .panic e m) :
    runLoopLoc env lc (fuel + 1) s b = .panicked e m :=
  (runLoopLoc_blockStep env lc fuel s b).2.2.1 e m h

theorem runLoopLoc_stuck {env : Env} {lc : LocCtx} {fuel : Nat} {s : LocState} {b : ID}
    (h : blockStepLoc env lc s b = .stuck) : ¬ (runLoopLoc env lc (fuel + 1) s b).Defined :=
  (runLoopLoc_blockStep env lc fuel s b).2.2.2 h

/-! ## Lock-step simulation -/

/-- The target's block step matches the source's: the same return or panic, or a jump to
related states and blocks (anything when the source is stuck). -/
def StepSimLoc (R : LocState → ID → LocState → ID → Prop) : StepLoc → StepLoc → Prop
  | .goto s e, t => ∃ s' e', t = .goto s' e' ∧ R s e.b s' e'.b
  | .ret rs m, t => t = .ret rs m
  | .panic e m, t => t = .panic e m
  | .stuck, _ => True

/-- **Lock-step simulation** over `runLoopLoc`. -/
theorem runLoopLoc_sim {env : Env} {lcS lcT : LocCtx} (R : LocState → ID → LocState → ID → Prop)
    (hsim : ∀ sS bS sT bT, R sS bS sT bT →
      StepSimLoc R (blockStepLoc env lcS sS bS) (blockStepLoc env lcT sT bT)) :
    ∀ fuel sS bS sT bT, R sS bS sT bT → (runLoopLoc env lcS fuel sS bS).Defined →
      runLoopLoc env lcT fuel sT bT = runLoopLoc env lcS fuel sS bS := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ h; exact h.elim
  | succ n ih =>
    intro sS bS sT bT hR hd
    have hs := hsim sS bS sT bT hR
    obtain ⟨g1, r1, p1, s1⟩ := runLoopLoc_blockStep env lcS n sS bS
    obtain ⟨g2, r2, p2, -⟩ := runLoopLoc_blockStep env lcT n sT bT
    cases hS : blockStepLoc env lcS sS bS with
    | goto sS' e =>
      rw [hS] at hs
      obtain ⟨sT', e', hT, hR'⟩ := hs
      rw [g1 _ _ hS] at hd ⊢
      rw [g2 _ _ hT]
      exact ih _ _ _ _ hR' hd
    | ret rs m =>
      rw [hS] at hs
      rw [r1 _ _ hS, r2 _ _ hs]
    | panic e m =>
      rw [hS] at hs
      rw [p1 _ _ hS, p2 _ _ hs]
    | stuck => exact absurd hd (s1 hS)

/-! ## Macro steps -/

/-- Related states simulate for `runLoopLoc` runs of at most `n` source block entries. -/
def SimUpToLoc (env : Env) (lcS lcT : LocCtx) (R : LocState → ID → LocState → ID → Prop)
    (n : Nat) : Prop :=
  ∀ fuel, fuel ≤ n → ∀ sS bS sT bT, R sS bS sT bT → (runLoopLoc env lcS fuel sS bS).Defined →
    ∃ fuelT, runLoopLoc env lcT fuelT sT bT = runLoopLoc env lcS fuel sS bS

/-- **Macro-step simulation** over `runLoopLoc`. -/
theorem runLoopLoc_simIH {env : Env} {lcS lcT : LocCtx}
    (R : LocState → ID → LocState → ID → Prop)
    (hsim : ∀ n, SimUpToLoc env lcS lcT R n → ∀ sS bS sT bT, R sS bS sT bT →
      (runLoopLoc env lcS (n + 1) sS bS).Defined →
        ∃ fuelT, runLoopLoc env lcT fuelT sT bT = runLoopLoc env lcS (n + 1) sS bS) :
    ∀ fuel sS bS sT bT, R sS bS sT bT → (runLoopLoc env lcS fuel sS bS).Defined →
      ∃ fuelT, runLoopLoc env lcT fuelT sT bT = runLoopLoc env lcS fuel sS bS := by
  have hall : ∀ n, SimUpToLoc env lcS lcT R n := by
    intro n
    induction n with
    | zero =>
      intro fuel hf _ _ _ _ _ hd
      rw [Nat.le_zero.1 hf] at hd; exact hd.elim
    | succ n ih =>
      intro fuel hf sS bS sT bT hR hd
      rcases Nat.lt_or_ge fuel (n + 1) with h | h
      · exact ih fuel (by omega) sS bS sT bT hR hd
      · obtain rfl : fuel = n + 1 := by omega
        exact hsim n ih sS bS sT bT hR hd
  intro fuel sS bS sT bT hR hd
  exact hall fuel fuel (Nat.le_refl _) sS bS sT bT hR hd

/-! ## From the loops to `RefinesLoc` -/

/-- `entryFrame` reads of its context the activation's layout and the size of the value
table. -/
theorem entryFrame_ctxW {env : Env} {ctx ctx' : Ctx} (ht : ctx.tabs = ctx'.tabs)
    (hpt : ctx.paramTys = ctx'.paramTys) (hl : ctx.locals = ctx'.locals) (ha : ctx.act = ctx'.act)
    (hsize : ctx.f.valueTab.size = ctx'.f.valueTab.size) (args : List Val) (mem : Mem) :
    entryFrame env ctx args mem = entryFrame env ctx' args mem := by
  unfold entryFrame frameMem frameAllocs
  rw [ht, hpt, hl, ha, hsize]

/-- The initial machine state of `runCtxLoc`. -/
def initLoc (env : Env) (lc : LocCtx) (args : List Val) (mem : Mem) : LocState :=
  let fr := entryFrame env lc.ctx args mem
  { fr, regs := Array.replicate ARM64.registers.size .poison, flags := .poison, slots := [],
    mem := .mem fr.mem0 }

theorem runCtxLoc_eq (env : Env) (lc : LocCtx) (args : List Val) (mem : Mem) (fuel : Nat) :
    runCtxLoc env lc args mem fuel =
      if args.length != lc.ctx.params.size then
        .stuck s!"{args.length} arguments for {lc.ctx.params.size} parameters"
      else finish env lc.ctx.outs lc.ctx.defers lc.ctx.act
        (runLoopLoc env lc fuel (initLoc env lc args mem) lc.ctx.f.entry) := rfl

/-- **A simulation of the loops from the entries gives `RefinesLoc`**: two `runLoc` contexts
with the same layout and initial states, whose target loop, from the target's entry, reaches
every defined outcome of the source loop from the source's entry. -/
theorem refinesLoc_of_loop {tabs tabs' : Tables} {f f' : Func}
    (hw : LocCtxW (LocCtx.make tabs f) (LocCtx.make tabs' f'))
    (hsize : f.valueTab.size = f'.valueTab.size)
    (hloop : ∀ env args mem fuel,
      (runLoopLoc env (LocCtx.make tabs f) fuel (initLoc env (LocCtx.make tabs f) args mem)
        f.entry).Defined →
      ∃ fuelT, runLoopLoc env (LocCtx.make tabs' f') fuelT
          (initLoc env (LocCtx.make tabs f) args mem) f'.entry =
        runLoopLoc env (LocCtx.make tabs f) fuel (initLoc env (LocCtx.make tabs f) args mem)
          f.entry) :
    RefinesLoc tabs' f' tabs f := by
  intro env args mem fuel hd
  have hsz : (LocCtx.make tabs f).ctx.f.valueTab.size =
      (LocCtx.make tabs' f').ctx.f.valueTab.size := by
    show (Ctx.makeL tabs f).f.valueTab.size = (Ctx.makeL tabs' f').f.valueTab.size
    unfold Ctx.makeL; split <;> split <;> exact hsize
  have hent : ∀ (t : Tables) (g : Func), (LocCtx.make t g).ctx.f.entry = g.entry := by
    intro t g
    show (Ctx.makeL t g).f.entry = g.entry
    unfold Ctx.makeL; split <;> rfl
  have hinit : initLoc env (LocCtx.make tabs' f') args mem =
      initLoc env (LocCtx.make tabs f) args mem := by
    unfold initLoc
    rw [entryFrame_ctxW hw.tabs.symm hw.paramTys.symm hw.locals.symm hw.act.symm hsz.symm]
  unfold runLoc at hd ⊢
  rw [runCtxLoc_eq] at hd
  have hp : (LocCtx.make tabs f).ctx.params = (LocCtx.make tabs' f').ctx.params := hw.params
  by_cases h : (args.length != (LocCtx.make tabs f).ctx.params.size) = true
  · simp only [h, ↓reduceIte] at hd; exact hd.elim
  · simp only [h, Bool.false_eq_true, ↓reduceIte, hent] at hd
    obtain ⟨fuelT, hT⟩ := hloop env args mem fuel (finish_defined hd)
    refine ⟨fuelT, ?_⟩
    rw [runCtxLoc_eq, runCtxLoc_eq, ← hp]
    simp only [h, Bool.false_eq_true, ↓reduceIte, hent, hinit, hT, ← hw.outs, ← hw.defers,
      ← hw.act]
    exact OutcomeRefines.refl hd

/-! ## Block helpers -/

theorem enterListLoc_append (env : Env) (lc : LocCtx) :
    ∀ (s : LocState) (l1 l2 : List ID), enterListLoc env lc s (l1 ++ l2) =
      match enterListLoc env lc s l1 with
      | .ok s' => enterListLoc env lc s' l2
      | .panic e m => .panic e m
      | .stuck msg => .stuck msg := by
  intro s l1 l2
  induction l1 generalizing s with
  | nil => rfl
  | cons id ids ih =>
    simp only [List.cons_append, enterListLoc]
    cases lc.ctx.f.value? id with
    | none => rfl
    | some v =>
      simp only
      cases stepLoc env lc s v with
      | ok s' => exact ih s'
      | panic e m => rfl
      | stuck msg => rfl

/-- A `Plain` block without controls goes to its first successor and leaves the state alone. -/
theorem stepTermLoc_plain (lc : LocCtx) (s : LocState) {b : Block} {e : Edge}
    (hk : b.kind = .Plain) (hc : b.controls = #[]) (he : b.succs[0]? = some e) :
    stepTermLoc lc s b = .ok (.goto e, s) := by
  unfold stepTermLoc
  have : stepTermL s.fr b = .ok (.goto e) := by
    unfold stepTermL stepTerm succ
    rw [hk]
    simp only [he]
    rfl
  have hf : ∀ (x : Array (Option Val)) (g : ID → Array (Option Val) →
      Res (ForInStep (Array (Option Val)))), forIn (#[] : Array ID) x g = .ok x := fun _ _ => rfl
  simp only [hc, hf]
  show (stepTermL s.fr b >>= fun n => pure (n, s)) = _
  rw [this]
  rfl

/-- The outcomes of two terminators that differ in their successors' targets (`R` relates the
edges they jump along). -/
inductive NextRelLoc (R : Edge → Edge → Prop) : Res Next → Res Next → Prop
  | goto {e e' : Edge} : R e e' → NextRelLoc R (.ok (.goto e)) (.ok (.goto e'))
  | ret (rs : List Val) (m : Mem) : NextRelLoc R (.ok (.ret rs m)) (.ok (.ret rs m))
  | panic (e : Panic) (m : Mem) : NextRelLoc R (.panic e m) (.panic e m)
  | stuck (msg msg' : String) : NextRelLoc R (.stuck msg) (.stuck msg')

private theorem nextRel_bind {R : Edge → Edge → Prop} {α : Type} (x : Res α)
    {k k' : α → Res Next} (h : ∀ a, NextRelLoc R (k a) (k' a)) :
    NextRelLoc R (x >>= k) (x >>= k') := by
  cases x with
  | ok a => exact h a
  | panic e m => exact .panic e m
  | stuck msg => exact .stuck msg msg

/-- `e` and `e'` are the successors of the same index of `b` and of successor array `ss`. -/
def SuccIdx (b : Block) (ss : Array Edge) (e e' : Edge) : Prop :=
  ∃ k : Nat, b.succs[k]? = some e ∧ ss[k]? = some e'

/-- **A terminator does not read its successors' targets**: with other successors `ss` (as
many), `stepTermL` goes along the successor of the same index, or does the same. -/
theorem stepTermL_succs (fr : Frame) (b : Block) (ss : Array Edge)
    (hs : ss.size = b.succs.size) :
    NextRelLoc (SuccIdx b ss) (stepTermL fr b) (stepTermL fr { b with succs := ss }) := by
  have hsucc : ∀ k, NextRelLoc (SuccIdx b ss) (succ b k) (succ { b with succs := ss } k) := by
    intro k
    unfold succ
    dsimp only
    cases h1 : b.succs[k]? with
    | none =>
      have : ss[k]? = none := by
        rw [Array.getElem?_eq_none_iff] at h1 ⊢; omega
      rw [this]; exact .stuck _ _
    | some e =>
      have hk : k < ss.size := by
        have := (Array.getElem?_eq_some_iff.1 h1).1; omega
      rw [Array.getElem?_eq_getElem hk]
      exact .goto ⟨k, h1, Array.getElem?_eq_getElem hk⟩
  have hctl : ∀ k, control fr { b with succs := ss } k = control fr b k := fun _ => rfl
  unfold stepTermL stepTerm
  simp only [hctl]
  split <;> split
  all_goals first
    | exact hsucc _
    | exact .stuck _ _
    | refine nextRel_bind _ fun a => ?_
  all_goals (repeat' split)
  all_goals first | exact hsucc _ | exact .stuck _ _ | exact .ret _ _

end GoFV.Proof
