import GoFV.Opt.RewriteCheck

/-!
# What a checked rewrite pass returns (issue #113)

`checkedRewrite t` returns either its input with the input's tables, or a result the validator
accepted in the result's tables, which the input cannot tell from its own (`GoFV.Opt.tabsAgree`):
`RewriteCheck.segsOK` with a table of `t`'s value and block rules, i.e. on each segment of the
rewrite log between phi eliminations (issue #69), `RewriteCheck.layersOK`: the validator
(`GoFV.Opt.RewriteCheck.validate`) against the segment and a function `g` obtained from the
segment's input by the layers of `RewriteCheck.layers` (`LayerChain`: steps of nil-check
eliminations, `RewriteCheck.nilOK`, Load-of-Store forwardings, `RewriteCheck.fwdRel`, struct-load
expansions, `RewriteCheck.validate`, and struct-store splits, `RewriteCheck.ssRel`, all issue
#151); a validated result has the atom, closure and replay facts the refinement proof consumes.
-/

namespace GoFV.Proof.Pass.Rewrite

open GoFV.SSA GoFV.Opt GoFV.Rules

/-- The replay reads only the table's value and block rules. -/
theorem replay_congr {t T : Interp.Table} (hv : T.values = t.values) (hb : T.blocks = t.blocks)
    (tabs : Tables) (f : Func) (lax : Bool) :
    ∀ (M : RewriteCheck.Defs) (B : RewriteCheck.BMap) (evs : List RwEvent),
      RewriteCheck.replay tabs T f lax M B evs = RewriteCheck.replay tabs t f lax M B evs
  | _, _, [] => rfl
  | M, B, ev :: evs => by
    cases ev <;> simp only [RewriteCheck.replay, hv, hb, replay_congr hv hb tabs f lax _ _ evs]

/-- The validator reads only the table's value and block rules (the layers read the others). -/
theorem validate_congr {t T : Interp.Table} (hv : T.values = t.values) (hb : T.blocks = t.blocks)
    (tabs : Tables) (f g : Func) (log : Array RwEvent) :
    RewriteCheck.validate tabs T f g log = RewriteCheck.validate tabs t f g log := by
  simp only [RewriteCheck.validate, replay_congr hv hb]

/-- The steps of `RewriteCheck.layersOK` from `f` to `g` (`f0` the pass's input, `t` the table
whose value and block rules the expansion steps are validated with): each a layer
`RewriteCheck.layerOK` accepts. -/
inductive LayerChain (penv : PassEnv) (tabs : Tables) (f0 : Func) (t : Interp.Table) :
    Func → Func → Prop
  | refl (f : Func) : LayerChain penv tabs f0 t f f
  /-- Nil-check eliminations. -/
  | nil {f f' g : Func} : RewriteCheck.nilOK penv tabs f0 f f' = true →
      LayerChain penv tabs f0 t f' g → LayerChain penv tabs f0 t f g
  /-- Load-of-Store forwardings. -/
  | fwd {f f' g : Func} :
      RewriteCheck.fwdRel tabs (RewriteCheck.roPass penv.tables penv.frontend f0) f f' = true →
      RewriteCheck.fwdRoOK tabs (RewriteCheck.roPass penv.tables penv.frontend f0) f = true →
      checkOK { tabs := tabs, typs := penv.typs } f' = true →
      LayerChain penv tabs f0 t f' g → LayerChain penv tabs f0 t f g
  /-- Validated rewrite events (struct-load expansions). -/
  | rw {f f' g : Func} {evs : Array RwEvent} : RewriteCheck.validate tabs t f f' evs = true →
      checkOK { tabs := tabs, typs := penv.typs } f' = true →
      LayerChain penv tabs f0 t f' g → LayerChain penv tabs f0 t f g
  /-- Struct-store splits. -/
  | ss {f f' g : Func} : RewriteCheck.ssRel tabs f f' = true →
      checkOK { tabs := tabs, typs := penv.typs } f' = true →
      LayerChain penv tabs f0 t f' g → LayerChain penv tabs f0 t f g
  /-- Segment rewrites. -/
  | seg {f f' g : Func} : RewriteCheck.segRel tabs f f' = true →
      RewriteCheck.roSegsOK tabs (RewriteCheck.roPass penv.tables penv.frontend f0) f f' = true →
      checkOK { tabs := tabs, typs := penv.typs } f' = true →
      LayerChain penv tabs f0 t f' g → LayerChain penv tabs f0 t f g
  /-- `Phi` selections. -/
  | ps {f f' g : Func} : RewriteCheck.psRel tabs f f' = true →
      checkOK { tabs := tabs, typs := penv.typs } f' = true →
      LayerChain penv tabs f0 t f' g → LayerChain penv tabs f0 t f g

/-- A chain validated with a table `T` is one with a table of the same value and block rules. -/
theorem LayerChain.congr {penv : PassEnv} {tabs : Tables} {f0 : Func} {t T : Interp.Table}
    (hv : T.values = t.values) (hb : T.blocks = t.blocks) {f g : Func}
    (h : LayerChain penv tabs f0 T f g) : LayerChain penv tabs f0 t f g := by
  induction h with
  | refl f => exact .refl f
  | nil h _ ih => exact .nil h ih
  | fwd h hr hc _ ih => exact .fwd h hr hc ih
  | rw h hc _ ih => exact .rw (by rwa [validate_congr hv hb] at h) hc ih
  | ss h hc _ ih => exact .ss h hc ih
  | seg h hr hc _ ih => exact .seg h hr hc ih
  | ps h hc _ ih => exact .ps h hc ih

theorem layersOK_cases {t : Interp.Table} {penv : PassEnv} {f0 : Func} {out : PassOut} :
    ∀ (Ls : List RewriteCheck.Layer) (f : Func) (log : Array RwEvent),
      RewriteCheck.layersOK penv t f0 out Ls f log = true →
      ∃ g log', LayerChain penv out.tables f0 t f g ∧
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
      have hL := h.1
      refine ⟨g, l, ?_, hv⟩
      cases L with
      | nil sel => exact .nil hL hc
      | fwd sel =>
        simp only [RewriteCheck.layerOK, Bool.and_eq_true] at hL
        exact .fwd hL.1.1 hL.1.2 hL.2 hc
      | sl =>
        simp only [RewriteCheck.layerOK, Bool.and_eq_true] at hL
        exact .rw hL.1 hL.2 hc
      | ss =>
        simp only [RewriteCheck.layerOK, Bool.and_eq_true] at hL
        exact .ss hL.1 hL.2 hc
      | ld =>
        simp only [RewriteCheck.layerOK, Bool.and_eq_true] at hL
        exact .rw hL.1 hL.2 hc
      | seg =>
        simp only [RewriteCheck.layerOK, Bool.and_eq_true] at hL
        exact .seg hL.1.1 hL.1.2 hL.2 hc
      | ps =>
        simp only [RewriteCheck.layerOK, Bool.and_eq_true] at hL
        exact .ps hL.1 hL.2 hc

/-- What an accepted run (`checkedRun`) returns. -/
theorem checkedRun_cases {t : Interp.Table} {penv : PassEnv} {f : Func} {out : PassOut}
    (h : checkedRun t penv f = .ok (some out)) :
    tabsAgree penv.tables out.tables f = true ∧
      ∃ log : Array RwEvent, RewriteCheck.segsOK penv t f out f #[] log.toList = true := by
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
      exact ⟨hv.1, log, hv.2⟩
    · cases h

/-- The tables `checkedRewrite` tries have `t`'s value and block rules. -/
theorem checkedTiers_rules {t T : Interp.Table} (h : T ∈ checkedTiers t) :
    T.values = t.values ∧ T.blocks = t.blocks := by
  simp only [checkedTiers, List.mem_cons, List.mem_append] at h
  rcases h with rfl | (((h | h) | h) | h) | h
  · exact ⟨rfl, rfl⟩
  all_goals
    split at h
    · cases h
    · simp only [List.mem_singleton] at h; subst h; exact ⟨rfl, rfl⟩

theorem checkedFirst_cases {t : Interp.Table} {penv : PassEnv} {f : Func} {out : PassOut} :
    ∀ (Ts : List Interp.Table), (∀ T ∈ Ts, T.values = t.values ∧ T.blocks = t.blocks) →
      checkedFirst penv f Ts = .ok (some out) →
      tabsAgree penv.tables out.tables f = true ∧
        ∃ T : Interp.Table, T.values = t.values ∧ T.blocks = t.blocks ∧
          ∃ log : Array RwEvent, RewriteCheck.segsOK penv T f out f #[] log.toList = true
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
        obtain ⟨hta, log, hs⟩ := checkedRun_cases h1
        obtain ⟨hvs, hbs⟩ := hT T List.mem_cons_self
        exact ⟨hta, T, hvs, hbs, log, hs⟩
      | none =>
        simp only [h1] at h
        exact checkedFirst_cases Ts (fun T' hT' => hT T' (List.mem_cons_of_mem _ hT')) h

theorem checkedRewrite_cases {t : Interp.Table} {penv : PassEnv} {f : Func} {out : PassOut}
    (h : checkedRewrite t penv f = .ok out) :
    (out.func = f ∧ out.tables = penv.tables) ∨
      (tabsAgree penv.tables out.tables f = true ∧
        ∃ T : Interp.Table, T.values = t.values ∧ T.blocks = t.blocks ∧
          ∃ log : Array RwEvent, RewriteCheck.segsOK penv T f out f #[] log.toList = true) := by
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

/-- Without phi eliminations and snapshots, `segsOK` is `layersOK` on the whole log. -/
theorem segsOK_noPhi {t : Interp.Table} {penv : PassEnv} {f0 : Func} {out : PassOut} (f : Func) :
    ∀ (evs : List RwEvent) (seg : Array RwEvent), (∀ ev ∈ evs, RewriteCheck.notPhiElim ev = true) →
      RewriteCheck.segsOK penv t f0 out f seg evs =
        RewriteCheck.layersOK penv t f0 out RewriteCheck.layers f (seg ++ evs.toArray)
  | [], seg, _ => by simp [RewriteCheck.segsOK]
  | ev :: evs, seg, h => by
    have ih := segsOK_noPhi (t := t) (penv := penv) (f0 := f0) (out := out) f evs (seg.push ev)
      (fun e he => h e (List.mem_cons_of_mem _ he))
    have ha : seg.push ev ++ evs.toArray = seg ++ (ev :: evs).toArray := by
      apply Array.ext'; simp
    cases ev with
    | phielim v d pre => cases h _ List.mem_cons_self
    | snap pre => cases h _ List.mem_cons_self
    | _ => simp only [RewriteCheck.segsOK]; rw [ih, ha]

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
  have key : ∀ (ro : List (String × GoFV.SSA.Sem.Alloc)) (l : List RwEvent) (acc : Array RwEvent),
      l.foldl (RewriteCheck.fwdStep t tabs ro sel f) (f, acc) = (f, acc ++ l.toArray) := by
    intro ro l
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
      l.foldl (RewriteCheck.ssStep t f) (f, acc) = (f, acc ++ l.toArray) := by
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

/-- A table without segment rules (`Interp.Table.segs`) has no segment events. -/
theorem segEvent?_none {t : Interp.Table} (h : t.segs = #[]) (f : Func) (ev : RwEvent) :
    RewriteCheck.segEvent? t f ev = none := by
  cases ev with
  | rule v i b d =>
    simp only [RewriteCheck.segEvent?, h]
    split
    · split
      · split <;> simp_all
      · rfl
    · rfl
  | _ => rfl

theorem segPre_none {t : Interp.Table} (h : t.segs = #[]) (f : Func) (log : Array RwEvent) :
    RewriteCheck.segPre t f log = (f, log) := by
  have key : ∀ (l : List RwEvent) (acc : Array RwEvent),
      l.foldl (RewriteCheck.segStep t f) (f, acc) = (f, acc ++ l.toArray) := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons ev l ih =>
      intro acc
      rw [List.foldl_cons, RewriteCheck.segStep, segEvent?_none h]
      dsimp only
      rw [ih]; simp
  unfold RewriteCheck.segPre
  rw [← Array.foldl_toList, key]
  simp

/-- A table without `Phi` selections (`Interp.Table.phiSels`) has no selection events. -/
theorem psEvent?_none {t : Interp.Table} (h : t.phiSels = #[]) (f : Func) (ev : RwEvent) :
    RewriteCheck.psEvent? t f ev = none := by
  cases ev with
  | rule v i b d =>
    simp only [RewriteCheck.psEvent?, h]
    split
    · split
      · simp
      · rfl
    · rfl
  | _ => rfl

theorem psPre_none {t : Interp.Table} (h : t.phiSels = #[]) (f : Func) (log : Array RwEvent) :
    RewriteCheck.psPre t f log = (f, log) := by
  have key : ∀ (l : List RwEvent) (acc : Array RwEvent),
      l.foldl (RewriteCheck.psStep t f) (f, acc) = (f, acc ++ l.toArray) := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons ev l ih =>
      intro acc
      rw [List.foldl_cons, RewriteCheck.psStep, psEvent?_none h]
      dsimp only
      rw [ih]; simp
  unfold RewriteCheck.psPre
  rw [← Array.foldl_toList, key]
  simp

/-- A table without struct-load expansions (`Interp.Table.structLoads`) has no expansion
events. -/
theorem slEvent?_none {t : Interp.Table} (h : t.structLoads = #[]) (tabs : Tables) (f : Func)
    (prior : Array RwEvent) (ev : RwEvent) : RewriteCheck.slEvent? t tabs f prior ev = none := by
  cases ev with
  | rule v i b d =>
    simp only [RewriteCheck.slEvent?, h]
    split
    · simp
    · rfl
  | _ => rfl

theorem slPre_none {t : Interp.Table} (h : t.structLoads = #[]) (tabs : Tables) (f : Func)
    (log : Array RwEvent) : RewriteCheck.slPre t tabs f log = (f, log) := by
  have key : ∀ (l : List RwEvent) (acc tk : Array RwEvent),
      l.foldl (RewriteCheck.slStep t tabs f) (f, acc, tk) = (f, acc ++ l.toArray, tk) := by
    intro l
    induction l with
    | nil => intro acc tk; simp
    | cons ev l ih =>
      intro acc tk
      rw [List.foldl_cons, RewriteCheck.slStep, slEvent?_none h]
      dsimp only
      rw [ih]; simp
  unfold RewriteCheck.slPre RewriteCheck.slRun
  rw [← Array.foldl_toList, key]
  simp

/-- A function without `Load`s and `Make`s (`RewriteCheck.ssMakeOp`) has no value-rule `Load`
expansion events nor copy-argument replacements of a `Load`'s argument or by a `Load`. -/
theorem ldPre_none {t : Interp.Table} {tabs : Tables} {f : Func}
    (hf : f.valueTab.all (fun o => o.all fun w =>
      w.op != .Load && !RewriteCheck.ssMakeOp w.op) = true)
    (log : Array RwEvent) : RewriteCheck.ldPre t tabs f log = (f, log) := by
  have hget : ∀ y w, RewriteCheck.Defs.get? f.valueTab y = some w →
      w.op ≠ .Load ∧ RewriteCheck.ssMakeOp w.op = false := by
    intro y w h
    unfold RewriteCheck.Defs.get? at h
    cases hy : f.valueTab[y]? with
    | none => rw [hy] at h; cases h
    | some o =>
      rw [hy] at h
      have hall := (Array.all_eq_true_iff_forall_mem.1 hf) o (Array.mem_of_getElem? hy)
      cases o with
      | none => cases h
      | some w' =>
        simp only [Option.join_some, Option.some.injEq] at h
        subst h
        simpa using hall
  have hTgt : ∀ y u, RewriteCheck.Defs.get? f.valueTab y = some u →
      RewriteCheck.ldTarget f.valueTab u = false := by
    intro y u hu
    unfold RewriteCheck.ldTarget
    obtain ⟨h1, -⟩ := hget y u hu
    have h1' : (u.op == .Load) = false := by simpa using h1
    rw [h1', Bool.false_or]
    cases ha : u.args[0]? with
    | none => simp
    | some a =>
      cases hw : RewriteCheck.Defs.get? f.valueTab a with
      | none => simp [hw]
      | some w =>
        obtain ⟨h2, h3⟩ := hget a w hw
        simp [hw, h2, h3]
  have key : ∀ (l : List RwEvent) (rest : Array RwEvent),
      l.foldl (RewriteCheck.ldStep t tabs f)
          { g := f, M := f.valueTab, taken := #[], rest := rest } =
        { g := f, M := f.valueTab, taken := #[], rest := rest ++ l.toArray } := by
    intro l
    induction l with
    | nil => intro rest; simp
    | cons ev l ih =>
      intro rest
      rw [List.foldl_cons]
      have hstep : RewriteCheck.ldStep t tabs f
          { g := f, M := f.valueTab, taken := #[], rest := rest } ev =
          { g := f, M := f.valueTab, taken := #[], rest := rest.push ev } := by
        unfold RewriteCheck.ldStep
        cases ev with
        | rule v i b d =>
          dsimp only
          cases hv : RewriteCheck.Defs.get? f.valueTab v with
          | none => rfl
          | some u => simp [hTgt v u hv]
        | copyArg v i src =>
          dsimp only
          cases hv : RewriteCheck.Defs.get? f.valueTab v with
          | none => rfl
          | some u =>
            cases hs : RewriteCheck.Defs.get? f.valueTab src with
            | none => rfl
            | some w =>
              obtain ⟨h1, -⟩ := hget v u hv
              obtain ⟨h2, -⟩ := hget src w hs
              simp [h1, h2]
        | _ => rfl
      rw [hstep, ih]; simp
  unfold RewriteCheck.ldPre RewriteCheck.ldRun
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

/-- `checkedRewrite_cases` for a table without nil-check eliminations, forwardings, struct-load
expansions, struct-store splits, segment rules and `Phi` selections, on a function without
`Load`s and `Make`s whose rewrite logs no phi elimination. -/
theorem checkedRewrite_cases_noNil {t : Interp.Table} (h0 : t.nilChecks = #[])
    (h1 : t.loads = #[]) (h2 : t.structStores = #[]) (h4 : t.structLoads = #[])
    (h5 : t.segs = #[]) (h6 : t.phiSels = #[]) {penv : PassEnv}
    {f : Func} {out : PassOut}
    (hld : f.valueTab.all (fun o => o.all fun w =>
      w.op != .Load && !RewriteCheck.ssMakeOp w.op) = true)
    (hphi : ∀ r, rewriteRun t true true penv f = .ok r → RewriteCheck.noPhiElim r.2.2 = true)
    (h : checkedRewrite t penv f = .ok out) :
    (out.func = f ∧ out.tables = penv.tables) ∨
      (tabsAgree penv.tables out.tables f = true ∧
        ∃ log, RewriteCheck.validate out.tables t f out.func log = true) := by
  have hT : checkedTiers t = [t] := by simp [checkedTiers, h0, h1, h2, h5, h6]
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
          have hn := hphi _ hr
          unfold RewriteCheck.noPhiElim at hn
          rw [segsOK_noPhi f log.toList #[]
            (fun ev hev => (Array.all_eq_true_iff_forall_mem.1 hn) ev (Array.mem_toList_iff.1 hev))]
            at hv
          simp only [Array.toArray_toList, Array.empty_append] at hv
          rw [← layersOK_none (penv := penv) (f0 := f) RewriteCheck.layers]
          · exact hv.2
          · intro L hL
            cases L with
            | nil sel => exact nilPre_none h0 _ sel f log
            | fwd sel => exact fwdPre_none h1 _ sel f log
            | sl => exact slPre_none h4 _ f log
            | ss => exact ssPre_none h2 f log
            | ld => exact ldPre_none hld log
            | seg => exact segPre_none h5 f log
            | ps => exact psPre_none h6 f log
        · cases h3

theorem validate_parts {tabs : Tables} {t : Interp.Table} {f g : Func} {log : Array RwEvent}
    (hv : RewriteCheck.validate tabs t f g log = true) :
    RewriteCheck.atomsOK f g = true ∧ RewriteCheck.closedOK f = true ∧
      RewriteCheck.closedOK g = true := by
  unfold RewriteCheck.validate at hv
  simp only [Bool.and_eq_true] at hv
  exact ⟨hv.1.1.1, hv.1.1.2, hv.1.2⟩

end GoFV.Proof.Pass.Rewrite
