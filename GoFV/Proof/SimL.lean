import GoFV.Proof.RefineL
import GoFV.Proof.Sim
import GoFV.Proof.SimIH

/-!
# Simulation over `runL`

`GoFV.Proof.Sim` and `GoFV.Proof.SimIH` for the lowered runner `runLoopL md` (any mode `md`):
one block entry (`blockStepL`), lock-step simulation (`runLoopL_simE`, `runLoopL_sim`),
simulation by macro steps (`runLoopL_simIH`, `SimUpToL`), and evaluation of a block's values
against a reference frame (`evalAllL_ref`, `evalAllL_ref_panic`, `evalAllL_panic_split`). The
step results (`Step`) and step relations (`StepSimE`, `StepSim`, `RefOK`) are Phase 1's.
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem

/-! ## Values -/

/-- One step of `evalAllL`: value `id` evaluated in frame `fr`. -/
def stepVL (md : LMode) (env : Env) (ctx : Ctx) (fr : Frame) (id : ID) : Res Val :=
  match ctx.f.value? id with
  | none => .stuck s!"v{id} is not in the function"
  | some v => evalValueL md env ctx fr v

theorem stepVL_of {md : LMode} {env : Env} {ctx : Ctx} {fr : Frame} {id : ID} {v : Value}
    (h : ctx.f.value? id = some v) : stepVL md env ctx fr id = evalValueL md env ctx fr v := by
  unfold stepVL; rw [h]

theorem evalAllL_cons (md : LMode) (env : Env) (ctx : Ctx) (fr : Frame) (id : ID) (ids : List ID) :
    evalAllL md env ctx fr (id :: ids) =
      match stepVL md env ctx fr id with
      | .ok x => evalAllL md env ctx (fr.set id x) ids
      | .panic e m => .panic e m
      | .stuck msg => .stuck msg := by
  conv => lhs; rw [evalAllL]
  unfold stepVL
  cases ctx.f.value? id <;> rfl

theorem evalAllL_append (md : LMode) (env : Env) (ctx : Ctx) (l1 l2 : List ID) :
    ∀ fr, evalAllL md env ctx fr (l1 ++ l2) =
      match evalAllL md env ctx fr l1 with
      | .ok fr' => evalAllL md env ctx fr' l2
      | .panic e m => .panic e m
      | .stuck msg => .stuck msg := by
  induction l1 with
  | nil => intro fr; rfl
  | cons id ids ih =>
    intro fr
    rw [List.cons_append, evalAllL_cons, evalAllL_cons]
    split
    · exact ih _
    · rfl
    · rfl

/-! ## Block steps -/

/-- One block entry of `runLoopL`: enter block `bid` along edge `i`, then its terminator. -/
def blockStepL (md : LMode) (env : Env) (ctx : Ctx) (fr : Frame) (bid : ID) (i : Nat) : Step :=
  match ctx.f.block? bid with
  | none => .stuck
  | some b =>
    match enterBlockL md env ctx fr b i with
    | .panic e m => .panic e m
    | .stuck _ => .stuck
    | .ok fr =>
      match stepTermL fr b with
      | .ok (.goto e) => .goto fr e
      | .ok (.ret rs m) => .ret rs m
      | .panic e m => .panic e m
      | .stuck _ => .stuck

/-- `runLoopL` through `blockStepL`. -/
theorem runLoopL_blockStep (md : LMode) (env : Env) (ctx : Ctx) (fuel : Nat) (fr : Frame)
    (bid : ID) (i : Nat) :
    (∀ fr' e, blockStepL md env ctx fr bid i = .goto fr' e →
      runLoopL md env ctx (fuel + 1) fr bid i = runLoopL md env ctx fuel fr' e.b e.i) ∧
    (∀ rs m, blockStepL md env ctx fr bid i = .ret rs m →
      runLoopL md env ctx (fuel + 1) fr bid i = .returned rs m) ∧
    (∀ e m, blockStepL md env ctx fr bid i = .panic e m →
      runLoopL md env ctx (fuel + 1) fr bid i = .panicked e m) ∧
    (blockStepL md env ctx fr bid i = .stuck →
      ¬ (runLoopL md env ctx (fuel + 1) fr bid i).Defined) := by
  rw [runLoopL_succ]
  unfold blockStepL
  cases ctx.f.block? bid with
  | none =>
    exact ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h), fun _ _ h => (nomatch h),
      fun _ h => h.elim⟩
  | some b =>
    simp only
    cases enterBlockL md env ctx fr b i with
    | panic e m =>
      refine ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h), ?_, fun h => (nomatch h)⟩
      intro _ _ h; cases h; rfl
    | stuck msg =>
      exact ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h), fun _ _ h => (nomatch h),
        fun _ h => h.elim⟩
    | ok fr' =>
      simp only
      cases stepTermL fr' b with
      | ok n =>
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

theorem runLoopL_goto {md : LMode} {env : Env} {ctx : Ctx} {fuel : Nat} {fr fr' : Frame} {b : ID}
    {i : Nat} {e : Edge} (h : blockStepL md env ctx fr b i = .goto fr' e) :
    runLoopL md env ctx (fuel + 1) fr b i = runLoopL md env ctx fuel fr' e.b e.i :=
  (runLoopL_blockStep md env ctx fuel fr b i).1 fr' e h

theorem runLoopL_ret {md : LMode} {env : Env} {ctx : Ctx} {fuel : Nat} {fr : Frame} {b : ID}
    {i : Nat} {rs : List Val} {m : Mem} (h : blockStepL md env ctx fr b i = .ret rs m) :
    runLoopL md env ctx (fuel + 1) fr b i = .returned rs m :=
  (runLoopL_blockStep md env ctx fuel fr b i).2.1 rs m h

theorem runLoopL_panic {md : LMode} {env : Env} {ctx : Ctx} {fuel : Nat} {fr : Frame} {b : ID}
    {i : Nat} {e : Panic} {m : Mem} (h : blockStepL md env ctx fr b i = .panic e m) :
    runLoopL md env ctx (fuel + 1) fr b i = .panicked e m :=
  (runLoopL_blockStep md env ctx fuel fr b i).2.2.1 e m h

theorem runLoopL_stuck {md : LMode} {env : Env} {ctx : Ctx} {fuel : Nat} {fr : Frame} {b : ID}
    {i : Nat} (h : blockStepL md env ctx fr b i = .stuck) :
    ¬ (runLoopL md env ctx (fuel + 1) fr b i).Defined :=
  (runLoopL_blockStep md env ctx fuel fr b i).2.2.2 h

/-! ## Lock-step simulation -/

/-- **Lock-step simulation** over `runLoopL`, the target's block and edge index related to the
source's (the modes of source and target may differ). -/
theorem runLoopL_simE {mdS mdT : LMode} {env : Env} {ctxS ctxT : Ctx} {P : Mem → Mem → Prop}
    (R : Frame → ID → Nat → Frame → ID → Nat → Prop)
    (hsim : ∀ frS bS iS frT bT iT, R frS bS iS frT bT iT →
      StepSimE P R (blockStepL mdS env ctxS frS bS iS) (blockStepL mdT env ctxT frT bT iT)) :
    ∀ fuel frS bS iS frT bT iT, R frS bS iS frT bT iT →
      (runLoopL mdS env ctxS fuel frS bS iS).Defined →
      LoopRefines P (runLoopL mdS env ctxS fuel frS bS iS)
        (runLoopL mdT env ctxT fuel frT bT iT) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ h; exact h.elim
  | succ n ih =>
    intro frS bS iS frT bT iT hR hd
    have hs := hsim frS bS iS frT bT iT hR
    obtain ⟨g1, r1, p1, s1⟩ := runLoopL_blockStep mdS env ctxS n frS bS iS
    obtain ⟨g2, r2, p2, -⟩ := runLoopL_blockStep mdT env ctxT n frT bT iT
    cases hS : blockStepL mdS env ctxS frS bS iS with
    | goto frS' e =>
      rw [hS] at hs
      obtain ⟨frT', e', hT, hR'⟩ := hs
      rw [g1 _ _ hS] at hd ⊢
      rw [g2 _ _ hT]
      exact ih _ _ _ _ _ _ hR' hd
    | ret rs m =>
      rw [hS] at hs
      obtain ⟨rs', m', hT, hr, hm⟩ := hs
      rw [r1 _ _ hS, r2 _ _ hT]
      exact .returned hr hm
    | panic e m =>
      rw [hS] at hs
      obtain ⟨m', hT, hm⟩ := hs
      rw [p1 _ _ hS, p2 _ _ hT]
      exact .panicked e hm
    | stuck => exact absurd hd (s1 hS)

/-- **Lock-step simulation** over `runLoopL` along the same edges. -/
theorem runLoopL_sim {mdS mdT : LMode} {env : Env} {ctxS ctxT : Ctx}
    (R : Frame → Frame → ID → Nat → Prop)
    (hsim : ∀ frS frT bid i, R frS frT bid i →
      StepSim R (blockStepL mdS env ctxS frS bid i) (blockStepL mdT env ctxT frT bid i)) :
    ∀ fuel frS frT bid i, R frS frT bid i → (runLoopL mdS env ctxS fuel frS bid i).Defined →
      LoopRefines Eq (runLoopL mdS env ctxS fuel frS bid i)
        (runLoopL mdT env ctxT fuel frT bid i) := by
  intro fuel frS frT bid i hR hd
  refine runLoopL_simE (fun frS bS iS frT bT iT => bT = bS ∧ iT = iS ∧ R frS frT bS iS)
    (fun frS bS iS frT bT iT ⟨hb, hi, hR⟩ => ?_) fuel frS bid i frT bid i ⟨rfl, rfl, hR⟩ hd
  rw [hb, hi]
  have hs := hsim frS frT bS iS hR
  revert hs
  generalize blockStepL mdS env ctxS frS bS iS = sS
  generalize blockStepL mdT env ctxT frT bS iS = sT
  cases sS with
  | goto frS' e => rintro ⟨frT', hT, hR'⟩; exact ⟨frT', e, hT, rfl, rfl, hR'⟩
  | ret rs m => rintro ⟨rs', hT, hr⟩; exact ⟨rs', m, hT, hr, Mem.Refines.refl m⟩
  | panic e m => intro hT; exact ⟨m, hT, rfl⟩
  | stuck => exact id

/-! ## Macro steps -/

/-- Related states simulate for `runLoopL` runs of at most `n` source block entries. -/
def SimUpToL (mdS mdT : LMode) (env : Env) (ctxS ctxT : Ctx)
    (R : Frame → ID → Nat → Frame → ID → Nat → Prop) (n : Nat) : Prop :=
  ∀ fuel, fuel ≤ n → ∀ frS bS iS frT bT iT, R frS bS iS frT bT iT →
    (runLoopL mdS env ctxS fuel frS bS iS).Defined →
      ∃ fuelT, LoopRefines Eq (runLoopL mdS env ctxS fuel frS bS iS)
        (runLoopL mdT env ctxT fuelT frT bT iT)

/-- **Macro-step simulation** over `runLoopL`. -/
theorem runLoopL_simIH {mdS mdT : LMode} {env : Env} {ctxS ctxT : Ctx}
    (R : Frame → ID → Nat → Frame → ID → Nat → Prop)
    (hsim : ∀ n, SimUpToL mdS mdT env ctxS ctxT R n → ∀ frS bS iS frT bT iT,
      R frS bS iS frT bT iT → (runLoopL mdS env ctxS (n + 1) frS bS iS).Defined →
        ∃ fuelT, LoopRefines Eq (runLoopL mdS env ctxS (n + 1) frS bS iS)
          (runLoopL mdT env ctxT fuelT frT bT iT)) :
    ∀ fuel frS bS iS frT bT iT, R frS bS iS frT bT iT →
      (runLoopL mdS env ctxS fuel frS bS iS).Defined →
      ∃ fuelT, LoopRefines Eq (runLoopL mdS env ctxS fuel frS bS iS)
        (runLoopL mdT env ctxT fuelT frT bT iT) := by
  have hall : ∀ n, SimUpToL mdS mdT env ctxS ctxT R n := by
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

/-- The target continues along an edge: a refinement by the run from the next state is one by
the run from this state. -/
theorem refinesL_goto {md : LMode} {env : Env} {ctx : Ctx} {Rel : Outcome → Outcome → Prop}
    {o : Outcome} {fr fr' : Frame} {b : ID} {i : Nat} {e : Edge}
    (h : blockStepL md env ctx fr b i = .goto fr' e)
    (hr : ∃ fuel, Rel o (runLoopL md env ctx fuel fr' e.b e.i)) :
    ∃ fuel, Rel o (runLoopL md env ctx fuel fr b i) := by
  obtain ⟨fuel, h'⟩ := hr
  exact ⟨fuel + 1, by rw [runLoopL_goto h]; exact h'⟩

/-! ## Evaluation against a reference frame -/

/-- Each listed value, evaluated in a frame of the activation of `G` that agrees with `G` on its
arguments, yields its register in `G` (`LocalOK` for `runL`). -/
def LocalOKL (md : LMode) (env : Env) (ctx : Ctx) (G : Frame) (o : List ID) : Prop :=
  ∀ x ∈ o, ∃ y, G.regs[x]? = some (some y) ∧
    ∀ g : Frame, g = { G with regs := g.regs } → (∀ a ∈ argsF ctx.f x, g.regs[a]? = G.regs[a]?) →
      stepVL md env ctx g x = .ok y

theorem evalAllL_ref {md : LMode} {env : Env} {ctx : Ctx} {G : Frame} :
    ∀ {o : List ID} {S : ID → Prop} {g : Frame}, LocalOKL md env ctx G o →
      RefOK (argsF ctx.f) S o →
      (∀ a, S a → g.regs[a]? = G.regs[a]?) → g = { G with regs := g.regs } →
      g.regs.size = G.regs.size →
      ∃ g', evalAllL md env ctx g o = .ok g' ∧ g' = { G with regs := g'.regs } ∧
        g'.regs.size = G.regs.size ∧ (∀ a, (S a ∨ a ∈ o) → g'.regs[a]? = G.regs[a]?) ∧
        (∀ a, a ∉ o → g'.regs[a]? = g.regs[a]?)
  | [], _, g, _, _, hS, hg, hs =>
    ⟨g, rfl, hg, hs, fun a ha => ha.elim (hS a) (fun h => absurd h List.not_mem_nil),
      fun _ _ => rfl⟩
  | x :: s, S, g, hl, ⟨hx, hr⟩, hS, hg, hs => by
    obtain ⟨y, hGx, hstep⟩ := hl x List.mem_cons_self
    have hxs := hstep g hg fun a ha => hS a (hx a ha)
    have hxlt : x < g.regs.size := by
      rw [hs]
      rcases Nat.lt_or_ge x G.regs.size with h | h
      · exact h
      · rw [Array.getElem?_eq_none h] at hGx; cases hGx
    rw [evalAllL_cons, hxs]
    obtain ⟨g', h1, h2, h3, h4, h5⟩ := evalAllL_ref (S := fun a => S a ∨ a = x) (g := g.set x y)
      (fun z hz => hl z (List.mem_cons_of_mem _ hz)) hr
      (fun a ha => by
        rcases ha with ha | rfl
        · by_cases hax : x = a
          · subst hax; rw [Frame.set_regs_self hxlt, hGx]
          · rw [Frame.set_regs_ne hax]; exact hS a ha
        · rw [Frame.set_regs_self hxlt, hGx])
      (by rw [hg]; rfl) (by simp [Frame.set, hs])
    refine ⟨g', h1, h2, h3, fun a ha => h4 a ?_, fun a ha => ?_⟩
    · rcases ha with ha | ha
      · exact .inl (.inl ha)
      · rcases List.mem_cons.1 ha with rfl | ha
        · exact .inl (.inr rfl)
        · exact .inr ha
    · have has : a ∉ s := fun h => ha (List.mem_cons_of_mem _ h)
      have hxa : x ≠ a := fun h => ha (h ▸ List.mem_cons_self)
      rw [h5 a has, Frame.set_regs_ne hxa]

theorem evalAllL_ref_panic {md : LMode} {env : Env} {ctx : Ctx} {G : Frame} {pre post : List ID}
    {r : ID} {S : ID → Prop} {g : Frame} {e : Panic} {m : Mem}
    (hl : LocalOKL md env ctx G pre) (href : RefOK (argsF ctx.f) S pre)
    (hS : ∀ a, S a → g.regs[a]? = G.regs[a]?) (hg : g = { G with regs := g.regs })
    (hs : g.regs.size = G.regs.size)
    (hrargs : ∀ a ∈ argsF ctx.f r, S a ∨ a ∈ pre)
    (hr : ∀ g' : Frame, g' = { G with regs := g'.regs } →
      (∀ a ∈ argsF ctx.f r, g'.regs[a]? = G.regs[a]?) → stepVL md env ctx g' r = .panic e m) :
    evalAllL md env ctx g (pre ++ r :: post) = .panic e m := by
  obtain ⟨g', h1, h2, -, h4, -⟩ := evalAllL_ref hl href hS hg hs
  rw [evalAllL_append, h1]
  show evalAllL md env ctx g' (r :: post) = _
  rw [evalAllL_cons, hr g' h2 fun a ha => h4 a (hrargs a ha)]

/-- Where a source `evalAllL` panics: after an evaluated prefix, at one value. -/
theorem evalAllL_panic_split {md : LMode} {env : Env} {ctx : Ctx} {e : Panic} {m : Mem} :
    ∀ {o : List ID} {g : Frame}, evalAllL md env ctx g o = .panic e m →
      ∃ pre r post g', o = pre ++ r :: post ∧ evalAllL md env ctx g pre = .ok g' ∧
        stepVL md env ctx g' r = .panic e m
  | [], _, h => nomatch h
  | x :: s, g, h => by
    rw [evalAllL_cons] at h
    cases hx : stepVL md env ctx g x with
    | ok y =>
      rw [hx] at h
      obtain ⟨pre, r, post, g', ho, h1, h2⟩ := evalAllL_panic_split h
      refine ⟨x :: pre, r, post, g', by rw [ho]; rfl, ?_, h2⟩
      rw [evalAllL_cons, hx]; exact h1
    | panic e' m' =>
      rw [hx] at h; cases h
      exact ⟨[], x, s, g, rfl, rfl, hx⟩
    | stuck msg => rw [hx] at h; cases h

end GoFV.Proof
