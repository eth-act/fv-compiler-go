import GoFV.Proof.Frame
import GoFV.Proof.Refine

/-!
# Lock-step simulation

`blockStep` is one block entry of `runLoop` (enter the block, run its terminator).
`runLoop_simE`: if a relation `R` between source and target states at block entries is
preserved by every source block step that does not get stuck (`StepSimE`: the target takes an
edge to related states, returns refined results or panics alike), then every defined source
`runLoop` is refined by the target's with the same fuel. The target may enter another block or
along another edge index (passes that delete edges shift predecessor indices); `runLoop_sim`
(`StepSim`) is the case of the same edges.

`evalAll_ref` / `evalAll_ref_panic`: evaluating a list of values against a reference frame `G`
(the source's frame): if each listed value, in any frame agreeing with `G` on its arguments,
yields its `G` register (`LocalOK`), and its arguments are already agreed (`S`) or listed
before it (`RefOK`), the target's `evalAll` ends agreeing with `G` (or panics where the
reference says so). `evalAll_panic_split`: where a source `evalAll` panics.
-/

namespace GoFV.Proof

open GoFV.SSA GoFV.SSA.Sem

/-- The result of one block entry. -/
inductive Step where
  | goto (fr : Frame) (e : Edge)
  | ret (rs : List Val) (m : Mem)
  | panic (e : Panic) (m : Mem)
  | stuck

/-- One block entry of `runLoop`: enter block `bid` along edge `i`, then its terminator. -/
def blockStep (env : Env) (ctx : Ctx) (fr : Frame) (bid : ID) (i : Nat) : Step :=
  match ctx.f.block? bid with
  | none => .stuck
  | some b =>
    match enterBlock env ctx fr b i with
    | .panic e m => .panic e m
    | .stuck _ => .stuck
    | .ok fr =>
      match stepTerm fr b with
      | .ok (.goto e) => .goto fr e
      | .ok (.ret rs m) => .ret rs m
      | .panic e m => .panic e m
      | .stuck _ => .stuck

/-- `runLoop` through `blockStep`. -/
theorem runLoop_blockStep (env : Env) (ctx : Ctx) (fuel : Nat) (fr : Frame) (bid : ID) (i : Nat) :
    (∀ fr' e, blockStep env ctx fr bid i = .goto fr' e →
      runLoop env ctx (fuel + 1) fr bid i = runLoop env ctx fuel fr' e.b e.i) ∧
    (∀ rs m, blockStep env ctx fr bid i = .ret rs m →
      runLoop env ctx (fuel + 1) fr bid i = .returned rs m) ∧
    (∀ e m, blockStep env ctx fr bid i = .panic e m →
      runLoop env ctx (fuel + 1) fr bid i = .panicked e m) ∧
    (blockStep env ctx fr bid i = .stuck → ¬ (runLoop env ctx (fuel + 1) fr bid i).Defined) := by
  rw [runLoop_succ]
  unfold blockStep
  cases hb : ctx.f.block? bid with
  | none =>
    exact ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h), fun _ _ h => (nomatch h),
      fun _ h => h.elim⟩
  | some b =>
    simp only
    cases he : enterBlock env ctx fr b i with
    | panic e m =>
      refine ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h), ?_, fun h => (nomatch h)⟩
      intro _ _ h; cases h; rfl
    | stuck msg =>
      exact ⟨fun _ _ h => (nomatch h), fun _ _ h => (nomatch h), fun _ _ h => (nomatch h),
        fun _ h => h.elim⟩
    | ok fr' =>
      simp only
      cases ht : stepTerm fr' b with
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

/-- The target's step matches a source step, possibly along another edge (`R frS bS iS frT bT
iT` relates the source entering block `bS` along edge `iS` and the target entering `bT` along
`iT`; passes that delete edges shift predecessor indices). Returns and panics may end in a
refined memory (`Mem.Refines`: a rewrite may make a poison value defined, which may be stored). -/
def StepSimE (R : Frame → ID → Nat → Frame → ID → Nat → Prop) : Step → Step → Prop
  | .goto frS e, sT => ∃ frT e', sT = .goto frT e' ∧ R frS e.b e.i frT e'.b e'.i
  | .ret rs m, sT => ∃ rs' m', sT = .ret rs' m' ∧ RefinesList rs rs' ∧ Mem.Refines m m'
  | .panic e m, sT => ∃ m', sT = .panic e m' ∧ Mem.Refines m m'
  | .stuck, _ => True

/-- **Lock-step simulation**, the target's block and edge index related to the source's. -/
theorem runLoop_simE {env : Env} {ctxS ctxT : Ctx} {act : Nat}
    (R : Frame → ID → Nat → Frame → ID → Nat → Prop)
    (hsim : ∀ frS bS iS frT bT iT, R frS bS iS frT bT iT →
      StepSimE R (blockStep env ctxS frS bS iS) (blockStep env ctxT frT bT iT)) :
    ∀ fuel frS bS iS frT bT iT, R frS bS iS frT bT iT → (runLoop env ctxS fuel frS bS iS).Defined →
      OutcomeRefines act (runLoop env ctxS fuel frS bS iS) (runLoop env ctxT fuel frT bT iT) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ _ _ h; exact h.elim
  | succ n ih =>
    intro frS bS iS frT bT iT hR hd
    have hs := hsim frS bS iS frT bT iT hR
    obtain ⟨g1, r1, p1, s1⟩ := runLoop_blockStep env ctxS n frS bS iS
    obtain ⟨g2, r2, p2, -⟩ := runLoop_blockStep env ctxT n frT bT iT
    cases hS : blockStep env ctxS frS bS iS with
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
      exact .panicked e (hm.dropFrames act)
    | stuck => exact absurd hd (s1 hS)

/-- The target's step matches a source step along the same edge (`R` relates the states at
block entries). -/
def StepSim (R : Frame → Frame → ID → Nat → Prop) : Step → Step → Prop
  | .goto frS e, sT => ∃ frT, sT = .goto frT e ∧ R frS frT e.b e.i
  | .ret rs m, sT => ∃ rs', sT = .ret rs' m ∧ RefinesList rs rs'
  | .panic e m, sT => sT = .panic e m
  | .stuck, _ => True

/-- **Lock-step simulation** along the same edges. -/
theorem runLoop_sim {env : Env} {ctxS ctxT : Ctx} {act : Nat} (R : Frame → Frame → ID → Nat → Prop)
    (hsim : ∀ frS frT bid i, R frS frT bid i →
      StepSim R (blockStep env ctxS frS bid i) (blockStep env ctxT frT bid i)) :
    ∀ fuel frS frT bid i, R frS frT bid i → (runLoop env ctxS fuel frS bid i).Defined →
      OutcomeRefines act (runLoop env ctxS fuel frS bid i) (runLoop env ctxT fuel frT bid i) := by
  intro fuel frS frT bid i hR hd
  refine runLoop_simE (fun frS bS iS frT bT iT => bT = bS ∧ iT = iS ∧ R frS frT bS iS)
    (fun frS bS iS frT bT iT ⟨hb, hi, hR⟩ => ?_) fuel frS bid i frT bid i ⟨rfl, rfl, hR⟩ hd
  rw [hb, hi]
  have hs := hsim frS frT bS iS hR
  revert hs
  generalize blockStep env ctxS frS bS iS = sS
  generalize blockStep env ctxT frT bS iS = sT
  cases sS with
  | goto frS' e => rintro ⟨frT', hT, hR'⟩; exact ⟨frT', e, hT, rfl, rfl, hR'⟩
  | ret rs m => rintro ⟨rs', hT, hr⟩; exact ⟨rs', m, hT, hr, Mem.Refines.refl m⟩
  | panic e m => intro hT; exact ⟨m, hT, Mem.Refines.refl m⟩
  | stuck => exact id

/-! ## Evaluation against a reference frame -/

/-- Every listed value's arguments are in `S` or listed before it. -/
def RefOK (D : ID → List ID) : (ID → Prop) → List ID → Prop
  | _, [] => True
  | S, x :: s => (∀ a ∈ D x, S a) ∧ RefOK D (fun a => S a ∨ a = x) s

/-- Each listed value, evaluated in a frame of the activation of `G` that agrees with `G` on its
arguments, yields its register in `G`. -/
def LocalOK (env : Env) (ctx : Ctx) (G : Frame) (o : List ID) : Prop :=
  ∀ x ∈ o, ∃ y, G.regs[x]? = some (some y) ∧
    ∀ g : Frame, g = { G with regs := g.regs } → (∀ a ∈ argsF ctx.f x, g.regs[a]? = G.regs[a]?) →
      stepV env ctx g x = .ok y

theorem evalAll_ref {env : Env} {ctx : Ctx} {G : Frame} :
    ∀ {o : List ID} {S : ID → Prop} {g : Frame}, LocalOK env ctx G o → RefOK (argsF ctx.f) S o →
      (∀ a, S a → g.regs[a]? = G.regs[a]?) → g = { G with regs := g.regs } →
      g.regs.size = G.regs.size →
      ∃ g', evalAll env ctx g o = .ok g' ∧ g' = { G with regs := g'.regs } ∧
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
    rw [evalAll_cons, hxs]
    obtain ⟨g', h1, h2, h3, h4, h5⟩ := evalAll_ref (S := fun a => S a ∨ a = x) (g := g.set x y)
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

theorem evalAll_ref_panic {env : Env} {ctx : Ctx} {G : Frame} {pre post : List ID} {r : ID}
    {S : ID → Prop} {g : Frame} {e : Panic} {m : Mem}
    (hl : LocalOK env ctx G pre) (href : RefOK (argsF ctx.f) S pre)
    (hS : ∀ a, S a → g.regs[a]? = G.regs[a]?) (hg : g = { G with regs := g.regs })
    (hs : g.regs.size = G.regs.size)
    (hrargs : ∀ a ∈ argsF ctx.f r, S a ∨ a ∈ pre)
    (hr : ∀ g' : Frame, g' = { G with regs := g'.regs } →
      (∀ a ∈ argsF ctx.f r, g'.regs[a]? = G.regs[a]?) → stepV env ctx g' r = .panic e m) :
    evalAll env ctx g (pre ++ r :: post) = .panic e m := by
  obtain ⟨g', h1, h2, -, h4, -⟩ := evalAll_ref hl href hS hg hs
  rw [evalAll_append, h1]
  show evalAll env ctx g' (r :: post) = _
  rw [evalAll_cons, hr g' h2 fun a ha => h4 a (hrargs a ha)]

/-- Where a source `evalAll` panics: after an evaluated prefix, at one value. -/
theorem evalAll_panic_split {env : Env} {ctx : Ctx} {e : Panic} {m : Mem} :
    ∀ {o : List ID} {g : Frame}, evalAll env ctx g o = .panic e m →
      ∃ pre r post g', o = pre ++ r :: post ∧ evalAll env ctx g pre = .ok g' ∧
        stepV env ctx g' r = .panic e m
  | [], _, h => nomatch h
  | x :: s, g, h => by
    rw [evalAll_cons] at h
    cases hx : stepV env ctx g x with
    | ok y =>
      rw [hx] at h
      obtain ⟨pre, r, post, g', ho, h1, h2⟩ := evalAll_panic_split h
      refine ⟨x :: pre, r, post, g', by rw [ho]; rfl, ?_, h2⟩
      rw [evalAll_cons, hx]; exact h1
    | panic e' m' =>
      rw [hx] at h; cases h
      exact ⟨[], x, s, g, rfl, rfl, hx⟩
    | stuck msg => rw [hx] at h; cases h

end GoFV.Proof
