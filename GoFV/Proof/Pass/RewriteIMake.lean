import GoFV.Proof.Pass.RewriteLoadSel

/-!
# Replaying an `IMake` of a `StructMake` (issue #69)

A rule event accepted by `RewriteCheck.imsOK` (`(IMake _typ (StructMake ___)) =>
imakeOfStructMake(v)`, `generic.rules:981`, `dec.rules:102`, `GoFV.Proof.Rules.imsShape`)
redefines `v = IMake t s`, `s` a `StructMake` of an aggregate shape, as `Copy w`, `w` a fresh
`IMake t a` of `v`'s type with `a` an argument of `s`. `v`'s shape is an interface's (`imsTy`:
two fields, the second a word), and a value retyped at an aggregate shape is `poison` at a word
shape (`retype_word_agg`), so the data word of `v` is `poison` and `w` refines `v`.
`IMFacts.step`: on a set closed under arguments, every denotation after the event refines the
one before, with three times the fuel. `ReplayInv.imake`: the event keeps the replay invariant.
-/

namespace GoFV.Proof.Pass.Rewrite

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck GoFV.Proof.Term GoFV.Proof.AtomSim

/-- A value retyped at an aggregate shape is `poison` at a word shape. -/
theorem retype_word_agg {t : Ty} (ht : (GoFV.Proof.Rules.isPtrTy t ||
    GoFV.Proof.Rules.isInt64Ty t) = true) (fs : List (Nat × Ty)) (n : Nat) (z : Val) :
    (z.retype (.agg fs n)).retype t = .poison := by
  have hw : ∀ vs : List Val, (Val.agg vs).retype t = .poison := by
    intro vs
    cases t with
    | ptr e => rfl
    | int w => cases w <;> first | rfl | simp [GoFV.Proof.Rules.isPtrTy,
        GoFV.Proof.Rules.isInt64Ty] at ht
    | _ => simp [GoFV.Proof.Rules.isPtrTy, GoFV.Proof.Rules.isInt64Ty] at ht
  cases z with
  | agg vs =>
    simp only [Val.retype]
    split
    · exact hw _
    · exact retype_poison t
  | _ => simp [Val.retype]

theorem imsTy_spec {T : Ty} (h : imsTy T = true) :
    ∃ o0 t0 o1 t1 m, T = .agg [(o0, t0), (o1, t1)] m ∧
      (GoFV.Proof.Rules.isPtrTy t1 || GoFV.Proof.Rules.isInt64Ty t1) = true := by
  unfold imsTy at h
  split at h
  · rename_i p o1 t1 m
    exact ⟨p.1, p.2, o1, t1, m, rfl, h⟩
  · cases h

/-- What `imsOK` establishes about an event `(v, [u0, w])`. -/
structure IMFacts (tabs : Tables) (M : Defs) (v : ID) (u0 w : Value) where
  x : Value
  y : Value
  t : ID
  s : ID
  a : ID
  hx : M.get? v = some x
  hxargs : x.args.toList = [t, s]
  hwargs : w.args.toList = [t, a]
  hy : M.get? s = some y
  hxop : x.op = .IMake
  hyop : y.op = .StructMake
  hyty : ∃ fs n, tabs.ty y.type = .agg fs n
  hxty : imsTy (tabs.ty x.type) = true
  hid : u0.id = v
  huop : u0.op = .Copy
  huargs : u0.args = #[w.id]
  huty : u0.type = x.type
  hwF : M.get? w.id = none
  hwop : w.op = .IMake
  hwty : w.type = x.type
  ha : a ∈ y.args
  hasome : (M.get? a).isSome

theorem imFacts {tabs : Tables} {M : Defs} {v : ID} {defs : List Value}
    (h : imsOK tabs M v defs = true) :
    ∃ u0 w, defs = [u0, w] ∧ Nonempty (IMFacts tabs M v u0 w) := by
  unfold imsOK at h
  split at h
  next x u0 w hx =>
    split at h
    next t s t' a hxargs hwargs =>
      split at h
      next y hy =>
        simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none,
          Array.contains_iff_mem] at h
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hxop, hyop⟩, hyty⟩, hxty⟩, hid⟩, huop⟩, huargs⟩, huty⟩, -⟩, -⟩,
          hwF⟩, hwop⟩, hwty⟩, htt⟩, ha⟩, hasome⟩ := h
        subst htt
        refine ⟨u0, w, rfl, ⟨⟨x, y, t', s, a, hx, hxargs, hwargs, hy, hxop, hyop, ?_, hxty, hid,
          huop, huargs, huty, hwF, hwop, hwty, ha, hasome⟩⟩⟩
        revert hyty; cases tabs.ty y.type <;> simp
      next => simp at h
    next => simp at h
  next => simp at h

section IM

variable {tabs : Tables} {M : Defs} {v : ID} {u0 w : Value}

theorem IMFacts.w_ne (F : IMFacts tabs M v u0 w) : w.id ≠ v := fun h => by
  have := F.hwF; rw [h, F.hx] at this; cases this

theorem IMFacts.nodup (F : IMFacts tabs M v u0 w) : ([u0, w].map (·.id)).Nodup := by
  simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, F.hid, List.nodup_nil, and_true, not_false_eq_true]
  exact fun h => F.w_ne h.symm

theorem IMFacts.get_v (F : IMFacts tabs M v u0 w) : (putAll M [u0, w]).get? v = some u0 := by
  have := get?_putAll_mem [u0, w] M u0 F.nodup List.mem_cons_self
  rwa [F.hid] at this

theorem IMFacts.get_w (F : IMFacts tabs M v u0 w) : (putAll M [u0, w]).get? w.id = some w :=
  get?_putAll_mem _ M w F.nodup (by simp)

theorem IMFacts.mem_ids (F : IMFacts tabs M v u0 w) {y : ID} :
    y ∈ [u0, w].map (·.id) ↔ y = v ∨ y = w.id := by
  simp [F.hid]

theorem IMFacts.get_other (F : IMFacts tabs M v u0 w) {y : ID} (hy : y ≠ v)
    (hm : (M.get? y).isSome) : (putAll M [u0, w]).get? y = M.get? y := by
  apply get?_putAll_not
  rw [F.mem_ids]
  rintro (h | h)
  · exact hy h
  · subst h; rw [F.hwF] at hm; cases hm

/-- The defined IDs of the event are term nodes after it. -/
theorem IMFacts.def_term (F : IMFacts tabs M v u0 w) {y : ID}
    (hy : y ∈ [u0, w].map (·.id)) : IsTerm (putAll M [u0, w]).get? y := by
  rcases F.mem_ids.1 hy with rfl | rfl
  · exact ⟨_, F.get_v, by rw [F.huop]; rfl⟩
  · exact ⟨_, F.get_w, by rw [F.hwop]; rfl⟩

theorem IMFacts.typed (F : IMFacts tabs M v u0 w) {ρ : ID → Val}
    (hT : Term.Typed M.get? tabs ρ) : Term.Typed (putAll M [u0, w]).get? tabs ρ := by
  intro b hb hsome
  by_cases hd : b ∈ [u0, w].map (·.id)
  · exact absurd (F.def_term hd) hb
  have hget := get?_putAll_not [u0, w] M b hd
  have hs : shape (putAll M [u0, w]).get? tabs b = shape M.get? tabs b := by
    simp only [shape, hget]
  rw [hs]
  exact hT b (fun h => hb (by unfold IsTerm at h ⊢; rw [hget]; exact h))
    (by rw [← hget]; exact hsome)

/-- The interface's type and the field are in a set closed under arguments that holds `v`. -/
theorem IMFacts.ta_mem (F : IMFacts tabs M v u0 w) {C : ID → Prop} (hC : DefClosed M C)
    (hv : C v) : C F.t ∧ C F.a := by
  obtain ⟨z, hz, hargs⟩ := hC v hv
  rw [F.hx] at hz; cases hz
  have ht : C F.t := hargs _ (Array.mem_toList_iff.1 (by rw [F.hxargs]; simp))
  have hs : C F.s := hargs _ (Array.mem_toList_iff.1 (by rw [F.hxargs]; simp))
  obtain ⟨z', hz', hargs'⟩ := hC F.s hs
  rw [F.hy] at hz'; cases hz'
  exact ⟨ht, hargs' _ F.ha⟩

theorem IMFacts.closed (F : IMFacts tabs M v u0 w) {C : ID → Prop} (hC : DefClosed M C) :
    DefClosed (putAll M [u0, w]) (fun y => C y ∨ (C v ∧ y ∈ defIds [u0, w])) := by
  have hdef : ∀ y, y ∈ defIds [u0, w] ↔ y = v ∨ y = w.id := fun y => F.mem_ids
  have hnew : C v → ∀ y, y = v ∨ y = w.id → ∃ z,
      (putAll M [u0, w]).get? y = some z ∧
      ∀ b ∈ z.args, C b ∨ (C v ∧ b ∈ defIds [u0, w]) := by
    intro hv y hy
    obtain ⟨ht, ha⟩ := F.ta_mem hC hv
    rcases hy with rfl | rfl
    · refine ⟨u0, F.get_v, fun b hb => ?_⟩
      rw [F.huargs] at hb
      simp only [List.mem_toArray, List.mem_singleton] at hb
      exact .inr ⟨hv, (hdef b).2 (.inr hb)⟩
    · refine ⟨w, F.get_w, fun b hb => ?_⟩
      have hb' : b ∈ w.args.toList := Array.mem_toList_iff.2 hb
      rw [F.hwargs] at hb'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb'
      rcases hb' with rfl | rfl
      · exact .inl ht
      · exact .inl ha
  intro y hy
  rcases hy with hy | ⟨hv, hy⟩
  · by_cases hyv : y = v
    · subst hyv; exact hnew hy _ (.inl rfl)
    obtain ⟨z, hz, hargs⟩ := hC y hy
    exact ⟨z, by rw [F.get_other hyv (by rw [hz]; rfl), hz], fun b hb => .inl (hargs b hb)⟩
  · exact hnew hv y ((hdef y).1 hy)

/-- The `StructMake`'s denotation is `poison` at a word shape. -/
theorem IMFacts.s_word (F : IMFacts tabs M v u0 w) {t1 : Ty}
    (ht : (GoFV.Proof.Rules.isPtrTy t1 || GoFV.Proof.Rules.isInt64Ty t1) = true)
    (ρ : ID → Val) : ∀ n, (den M.get? tabs ρ n F.s).retype t1 = .poison
  | 0 => retype_poison t1
  | n + 1 => by
    obtain ⟨fs, k, hk⟩ := F.hyty
    rw [den_succ_term F.hy (by rw [F.hyop]; rfl), hk]
    exact retype_word_agg ht fs k _

/-- **An `IMake`-of-`StructMake` event refines the denotations of a closed set**, with three
times the fuel. -/
theorem IMFacts.step (F : IMFacts tabs M v u0 w) {C : ID → Prop} (hC : DefClosed M C)
    {ρ : ID → Val} : ∀ n y, C y →
      Sem.Refines (den M.get? tabs ρ n y) (den (putAll M [u0, w]).get? tabs ρ (3 * n) y) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n IH => ?_
  intro y hy
  rcases n with _ | n
  · exact .poison _
  · obtain ⟨z, hz, hargs⟩ := hC y hy
    by_cases hyv : y = v
    · subst hyv
      rw [F.hx] at hz; cases hz
      obtain ⟨ht, -⟩ := F.ta_mem hC hy
      obtain ⟨o0, t0, o1, t1, m, hxt, hw⟩ := imsTy_spec F.hxty
      have iht := IH n (by omega) F.t ht
      rw [den_succ_term F.hx (by rw [F.hxop]; rfl), F.hxop, F.hxargs,
        GoFV.Proof.Rules.opVal_pure (op := .IMake) rfl, hxt,
        show 3 * (n + 1) = (3 * n + 1) + 1 + 1 by omega,
        den_succ_term F.get_v (by rw [F.huop]; rfl), F.huop, F.huargs, F.huty, hxt,
        GoFV.Proof.Rules.opVal_pure (op := .Copy) rfl]
      simp only [List.toList_toArray, List.map_cons, List.map_nil]
      rw [den_succ_term F.get_w (by rw [F.hwop]; rfl), F.hwop, F.hwargs, F.hwty, hxt,
        GoFV.Proof.Rules.opVal_pure (op := .IMake) rfl]
      simp only [List.map_cons, List.map_nil]
      have hcp : ∀ (ty : Ty) (ai : Int64) (ax : Option AuxRef) (q : Val),
          Sem.evalPure .Copy ty ai ax [q] = q := fun _ _ _ _ => rfl
      have hmk : ∀ (ty : Ty) (ai : Int64) (ax : Option AuxRef) (A B : Val),
          Sem.evalPure .IMake ty ai ax [A, B] = .agg [A, B] := fun _ _ _ _ _ => rfl
      have hrt : ∀ (A B : Val), (Val.agg [A, B]).retype (.agg [(o0, t0), (o1, t1)] m) =
          .agg [A.retype t0, B.retype t1] := fun _ _ => by
        simp [Val.retype, Val.retypeFields]
      simp only [hcp, hmk, Val.retype_idem, hrt, F.s_word hw ρ n]
      exact .agg (.cons (retype_mono t0 (iht.trans (den_fuel_mono _ _ _ _ _ _ (by omega))))
        (.cons (.poison _) .nil))
    · have hget := F.get_other hyv (by rw [hz]; rfl)
      have ih : ∀ b ∈ z.args, ∀ k, 3 * n ≤ k →
          Sem.Refines (den M.get? tabs ρ n b) (den (putAll M [u0, w]).get? tabs ρ k b) :=
        fun b hb k hk => (IH n (by omega) b (hargs b hb)).trans
          (den_fuel_mono _ _ _ _ _ _ hk)
      by_cases ht : termOp z.op = true
      · rw [den_succ_term hz ht, show 3 * (n + 1) = (3 * n + 2) + 1 by omega,
          den_succ_term (by rw [hget]; exact hz) ht]
        exact retype_mono _ (GoFV.Proof.Rules.opVal_mono _ _ _ _ _ (refinesList_map fun b hb =>
          ih b (Array.mem_toList_iff.1 hb) _ (by omega)))
      · have h1 : ¬ IsTerm M.get? y := fun ⟨u, hu, hut⟩ => by
          rw [hz] at hu; cases hu; exact ht hut
        have h2 : ¬ IsTerm (putAll M [u0, w]).get? y := fun ⟨u, hu, hut⟩ => by
          rw [hget, hz] at hu; cases hu; exact ht hut
        rw [show 3 * (n + 1) = (3 * n + 2) + 1 by omega, den_succ_atom h1, den_succ_atom h2]
        exact Sem.Refines.refl _

theorem ReplayInv.imake {D₀ : ID → Option Value} {C₀ C : ID → Prop}
    (hI : ReplayInv tabs D₀ C₀ M C) (F : IMFacts tabs M v u0 w) :
    ReplayInv tabs D₀ C₀ (putAll M [u0, w])
      (fun y => C y ∨ (C v ∧ y ∈ defIds [u0, w])) where
  closed := F.closed hI.closed
  sub := fun y h => .inl (hI.sub y h)
  typed := fun ρ h => F.typed (hI.typed ρ h)
  denRef := fun y hy => den_compose (g := (3 * ·)) (hI.denRef y hy) hI.typed
    fun _ _ n => F.step hI.closed n y (hI.sub y hy)
  atoms := fun y a hy ha hargs => by
    obtain ⟨a', ha', hat, hsz, hrest⟩ := hI.atoms y a hy ha hargs
    have hyv : y ≠ v := fun h => by
      rw [h, F.hx] at ha'; cases ha'; rw [F.hxop] at hat; cases hat
    refine ⟨a', by rw [F.get_other hyv (by rw [ha']; rfl)]; exact ha', hat, hsz,
      fun i hi => ⟨.inl (hrest i hi).1, ?_⟩⟩
    exact den_compose (g := (3 * ·)) (hrest i hi).2 hI.typed
      fun _ _ n => F.step hI.closed n _ (hrest i hi).1

end IM

end GoFV.Proof.Pass.Rewrite
