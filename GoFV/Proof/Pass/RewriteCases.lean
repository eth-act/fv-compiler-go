import GoFV.Opt.RewriteCheck

/-!
# What a checked rewrite pass returns (issue #113)

`checkedRewrite t` returns either its input with the input's tables, or a result the validator
(`GoFV.Opt.RewriteCheck.validate`) accepted in the result's tables, which the input cannot tell
from its own (`GoFV.Opt.tabsAgree`), against the rewrite log and a function `g` obtained from the
input by the layers of `RewriteCheck.layers` (`LayerChain`: steps of nil-check eliminations,
`RewriteCheck.nilOK`, Load-of-Store forwardings, `RewriteCheck.fwdRel`, and struct-store splits,
`RewriteCheck.ssRel`, all issue #151); a validated result has the atom, closure and replay facts
the refinement proof consumes.
-/

namespace GoFV.Proof.Pass.Rewrite

open GoFV.SSA GoFV.Opt GoFV.Rules

/-- The steps of `RewriteCheck.layersOK` from `f` to `g` (`f0` the pass's input): each a layer
`RewriteCheck.layerOK` accepts. -/
inductive LayerChain (penv : PassEnv) (tabs : Tables) (f0 : Func) : Func → Func → Prop
  | refl (f : Func) : LayerChain penv tabs f0 f f
  | step {L : RewriteCheck.Layer} {f f' g : Func} :
      RewriteCheck.layerOK penv tabs f0 L f f' = true → LayerChain penv tabs f0 f' g →
      LayerChain penv tabs f0 f g

theorem layersOK_cases {t : Interp.Table} {penv : PassEnv} {f0 : Func} {out : PassOut} :
    ∀ (Ls : List RewriteCheck.Layer) (f : Func) (log : Array RwEvent),
      RewriteCheck.layersOK penv t f0 out Ls f log = true →
      ∃ g log', LayerChain penv out.tables f0 f g ∧
        RewriteCheck.validate out.tables t g out.func log' = true
  | [], f, log, h => ⟨f, log, .refl f, h⟩
  | L :: Ls, f, log, h => by
    rw [RewriteCheck.layersOK] at h
    split at h
    next f' log' _ =>
    split at h
    · exact layersOK_cases Ls f log h
    · rw [Bool.and_eq_true] at h
      obtain ⟨g, l, hc, hv⟩ := layersOK_cases Ls f' log' h.2
      exact ⟨g, l, .step h.1 hc, hv⟩

/-- What an accepted run (`checkedRun`) returns. -/
theorem checkedRun_cases {t : Interp.Table} {penv : PassEnv} {f : Func} {out : PassOut}
    (h : checkedRun t penv f = .ok (some out)) :
    tabsAgree penv.tables out.tables f = true ∧
      ∃ g log, LayerChain penv out.tables f f g ∧
        RewriteCheck.validate out.tables t g out.func log = true := by
  unfold checkedRun at h
  cases hr : rewriteRun t true true penv f with
  | error e => simp [hr, bind, Except.bind] at h
  | ok r =>
    obtain ⟨o, n, log⟩ := r
    simp only [hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h
    split at h
    · next hv =>
      cases h
      rw [RewriteCheck.accepts, Bool.and_eq_true] at hv
      exact ⟨hv.1, layersOK_cases _ _ _ hv.2⟩
    · cases h

/-- The replay reads only the table's value and block rules. -/
theorem replay_congr {t T : Interp.Table} (hv : T.values = t.values) (hb : T.blocks = t.blocks)
    (tabs : Tables) (f : Func) :
    ∀ (M : RewriteCheck.Defs) (B : RewriteCheck.BMap) (evs : List RwEvent),
      RewriteCheck.replay tabs T f M B evs = RewriteCheck.replay tabs t f M B evs
  | _, _, [] => rfl
  | M, B, ev :: evs => by
    cases ev <;> simp only [RewriteCheck.replay, hv, hb, replay_congr hv hb tabs f _ _ evs]

/-- The validator reads only the table's value and block rules (the layers read the others). -/
theorem validate_congr {t T : Interp.Table} (hv : T.values = t.values) (hb : T.blocks = t.blocks)
    (tabs : Tables) (f g : Func) (log : Array RwEvent) :
    RewriteCheck.validate tabs T f g log = RewriteCheck.validate tabs t f g log := by
  simp only [RewriteCheck.validate, replay_congr hv hb]

/-- The tables `checkedRewrite` tries have `t`'s value and block rules. -/
theorem checkedTiers_rules {t T : Interp.Table} (h : T ∈ checkedTiers t) :
    T.values = t.values ∧ T.blocks = t.blocks := by
  simp only [checkedTiers, List.mem_cons, List.mem_append] at h
  rcases h with rfl | (h | h) | h
  · exact ⟨rfl, rfl⟩
  all_goals
    split at h
    · cases h
    · simp only [List.mem_singleton] at h; subst h; exact ⟨rfl, rfl⟩

theorem checkedFirst_cases {t : Interp.Table} {penv : PassEnv} {f : Func} {out : PassOut} :
    ∀ (Ts : List Interp.Table), (∀ T ∈ Ts, T.values = t.values ∧ T.blocks = t.blocks) →
      checkedFirst penv f Ts = .ok (some out) →
      tabsAgree penv.tables out.tables f = true ∧
        ∃ g log, LayerChain penv out.tables f f g ∧
          RewriteCheck.validate out.tables t g out.func log = true
  | [], _, h => by simp [checkedFirst, pure, Except.pure] at h
  | T :: Ts, hT, h => by
    simp only [checkedFirst, bind, Except.bind] at h
    cases h1 : checkedRun T penv f with
    | error e => simp [h1] at h
    | ok r =>
      cases r with
      | some o =>
        simp only [h1, pure, Except.pure, Except.ok.injEq, Option.some.injEq] at h
        subst h
        obtain ⟨hta, g, log, hc, hv⟩ := checkedRun_cases h1
        obtain ⟨hvs, hbs⟩ := hT T List.mem_cons_self
        exact ⟨hta, g, log, hc, by rwa [validate_congr hvs hbs] at hv⟩
      | none =>
        simp only [h1] at h
        exact checkedFirst_cases Ts (fun T' hT' => hT T' (List.mem_cons_of_mem _ hT')) h

theorem checkedRewrite_cases {t : Interp.Table} {penv : PassEnv} {f : Func} {out : PassOut}
    (h : checkedRewrite t penv f = .ok out) :
    (out.func = f ∧ out.tables = penv.tables) ∨
      (tabsAgree penv.tables out.tables f = true ∧
        ∃ g log, LayerChain penv out.tables f f g ∧
          RewriteCheck.validate out.tables t g out.func log = true) := by
  unfold checkedRewrite at h
  cases h1 : checkedFirst penv f (checkedTiers t) with
  | error e => simp [h1, bind, Except.bind] at h
  | ok r =>
    simp only [h1, bind, Except.bind] at h
    cases r with
    | some o =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact .inr (checkedFirst_cases _ (fun _ hT => checkedTiers_rules hT) h1)
    | none =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h; exact .inl ⟨rfl, rfl⟩

/-- A table without nil-check eliminations (`Interp.Table.nilChecks`) has no nil-check events. -/
theorem nilEvent?_none {t : Interp.Table} (h : t.nilChecks = #[]) (f : Func) (ev : RwEvent) :
    RewriteCheck.nilEvent? t f ev = none := by
  cases ev with
  | rule v i b d =>
    simp only [RewriteCheck.nilEvent?, h]
    split
    · split
      · split <;> simp
      · rfl
    · rfl
  | _ => rfl

theorem nilPre_none {t : Interp.Table} (h : t.nilChecks = #[]) (tabs : Tables) (sel : Bool)
    (f : Func) (log : Array RwEvent) : RewriteCheck.nilPre t tabs sel f log = (f, log) := by
  have key : ∀ (l : List RwEvent) (acc : Array RwEvent),
      l.foldl (RewriteCheck.nilStep t tabs sel f) (f, acc) = (f, acc ++ l.toArray) := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons ev l ih =>
      intro acc
      rw [List.foldl_cons, RewriteCheck.nilStep, nilEvent?_none h]
      dsimp only
      rw [ih]; simp
  unfold RewriteCheck.nilPre
  rw [← Array.foldl_toList, key]
  simp

/-- A table without Load-of-Store forwardings (`Interp.Table.loads`) has no forwarding events. -/
theorem fwdEvent?_none {t : Interp.Table} (h : t.loads = #[]) (f : Func) (ev : RwEvent) :
    RewriteCheck.fwdEvent? t f ev = none := by
  cases ev with
  | rule v i b d =>
    simp only [RewriteCheck.fwdEvent?, h]
    split
    · split
      · split <;> simp
      · rfl
    · rfl
  | _ => rfl

theorem fwdPre_none {t : Interp.Table} (h : t.loads = #[]) (tabs : Tables) (sel : Bool)
    (f : Func) (log : Array RwEvent) : RewriteCheck.fwdPre t tabs sel f log = (f, log) := by
  have key : ∀ (l : List RwEvent) (acc : Array RwEvent),
      l.foldl (RewriteCheck.fwdStep t tabs sel f) (f, acc) = (f, acc ++ l.toArray) := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons ev l ih =>
      intro acc
      rw [List.foldl_cons, RewriteCheck.fwdStep, fwdEvent?_none h]
      dsimp only
      rw [ih]; simp
  unfold RewriteCheck.fwdPre
  rw [← Array.foldl_toList, key]
  simp

/-- A table without struct-store splits (`Interp.Table.structStores`) has no split events. -/
theorem ssEvent?_none {t : Interp.Table} (h : t.structStores = #[]) (f : Func) (ev : RwEvent) :
    RewriteCheck.ssEvent? t f ev = none := by
  cases ev with
  | rule v i b d =>
    simp only [RewriteCheck.ssEvent?, h]
    split
    · split
      · split <;> simp
      · rfl
    · rfl
  | _ => rfl

theorem ssPre_none {t : Interp.Table} (h : t.structStores = #[]) (f : Func) (log : Array RwEvent) :
    RewriteCheck.ssPre t f log = (f, log) := by
  have key : ∀ (l : List RwEvent) (acc : Array RwEvent),
      l.foldl (RewriteCheck.ssStep t) (f, acc) = (f, acc ++ l.toArray) := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons ev l ih =>
      intro acc
      rw [List.foldl_cons, RewriteCheck.ssStep, ssEvent?_none h]
      dsimp only
      rw [ih]; simp
  unfold RewriteCheck.ssPre
  rw [← Array.foldl_toList, key]
  simp

/-- Layers without events are skipped: `layersOK` is `validate`. -/
theorem layersOK_none {t : Interp.Table} {penv : PassEnv} {f0 : Func} {out : PassOut} {f : Func}
    {log : Array RwEvent} :
    ∀ (Ls : List RewriteCheck.Layer), (∀ L ∈ Ls, L.pre t out.tables f log = (f, log)) →
      RewriteCheck.layersOK penv t f0 out Ls f log =
        RewriteCheck.validate out.tables t f out.func log
  | [], _ => by rw [RewriteCheck.layersOK]
  | L :: Ls, h => by
    rw [RewriteCheck.layersOK, h L List.mem_cons_self]
    simp only [beq_self_eq_true, ite_true]
    exact layersOK_none Ls (fun L' hL' => h L' (List.mem_cons_of_mem _ hL'))

/-- `checkedRewrite_cases` for a table without nil-check eliminations, forwardings and
struct-store splits. -/
theorem checkedRewrite_cases_noNil {t : Interp.Table} (h0 : t.nilChecks = #[])
    (h1 : t.loads = #[]) (h2 : t.structStores = #[]) {penv : PassEnv}
    {f : Func} {out : PassOut} (h : checkedRewrite t penv f = .ok out) :
    (out.func = f ∧ out.tables = penv.tables) ∨
      (tabsAgree penv.tables out.tables f = true ∧
        ∃ log, RewriteCheck.validate out.tables t f out.func log = true) := by
  have hT : checkedTiers t = [t] := by simp [checkedTiers, h0, h1, h2]
  unfold checkedRewrite at h
  rw [hT] at h
  simp only [checkedFirst, bind, Except.bind] at h
  cases h3 : checkedRun t penv f with
  | error e => simp [h3] at h
  | ok r =>
    simp only [h3] at h
    cases r with
    | none =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      exact .inl ⟨rfl, rfl⟩
    | some o =>
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      unfold checkedRun at h3
      cases hr : rewriteRun t true true penv f with
      | error e => simp [hr, bind, Except.bind] at h3
      | ok r =>
        obtain ⟨o', n, log⟩ := r
        simp only [hr, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h3
        split at h3
        · next hv =>
          cases h3
          rw [RewriteCheck.accepts, Bool.and_eq_true] at hv
          refine .inr ⟨hv.1, log, ?_⟩
          rw [← layersOK_none (penv := penv) (f0 := f) RewriteCheck.layers]
          · exact hv.2
          · intro L _
            cases L with
            | nil sel => exact nilPre_none h0 _ sel f log
            | fwd sel => exact fwdPre_none h1 _ sel f log
            | ss => exact ssPre_none h2 f log
        · cases h3

theorem validate_parts {tabs : Tables} {t : Interp.Table} {f g : Func} {log : Array RwEvent}
    (hv : RewriteCheck.validate tabs t f g log = true) :
    RewriteCheck.atomsOK f g = true ∧ RewriteCheck.closedOK f = true ∧
      RewriteCheck.closedOK g = true := by
  unfold RewriteCheck.validate at hv
  simp only [Bool.and_eq_true] at hv
  exact ⟨hv.1.1.1, hv.1.1.2, hv.1.2⟩

end GoFV.Proof.Pass.Rewrite
