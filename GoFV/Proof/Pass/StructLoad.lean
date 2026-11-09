import GoFV.Proof.Pass.RewriteTermReplay
import GoFV.Proof.Pass.StructLoadMem

variable [GoFV.SSA.Sem.Addrs]

/-!
# Replaying a struct-load expansion (issue #151)

A rule event accepted by `RewriteCheck.structLoadOK` (`rewriteStructLoad`, `generic.rules:974`)
redefines the `Load <agg fs n> ptr mem` `v` as `StructMake` of fresh `Load <tᵢ> (OffPtr [oᵢ] ptr)
mem`. `SLFacts.step`: on a set closed under arguments, every denotation after the event refines
the one before, with three times the fuel (`StructLoad.structLoad_ref` at `v`, monotonicity
elsewhere). `ReplayInv.structLoad`: the event keeps the replay invariant.
-/

namespace GoFV.Proof.Pass.Rewrite

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck GoFV.Proof.Term GoFV.Proof.AtomSim
open GoFV.Proof.Pass.StructLoad (Fields fieldVal structLoad_ref)

/-- What `structLoadOK` establishes about an event `(v, x' :: ds)`. -/
structure SLFacts (tabs : Tables) (M : Defs) (v : ID) (x' : Value) (ds : List Value) where
  x : Value
  fs : List (Nat × Ty)
  n : Nat
  ptr : ID
  mem : ID
  hx : M.get? v = some x
  hty : tabs.ty x.type = .agg fs n
  hargs : x.args = #[ptr, mem]
  hop : x.op = .Load
  hid' : x'.id = v
  hop' : x'.op = .StructMake
  hty' : x'.type = x.type
  hlay : layoutsOK n fs = true
  hoff : ∀ f ∈ fs, f.1 < n
  hfresh : ∀ d ∈ ds, M.get? d.id = none
  hnodup : (ds.map (·.id)).Nodup
  hfields : slFieldsOK tabs ptr mem fs x'.args.toList ds = true

theorem slFacts {tabs : Tables} {M : Defs} {v : ID} {defs : List Value}
    (h : structLoadOK tabs M v defs = true) :
    ∃ x' ds, defs = x' :: ds ∧ Nonempty (SLFacts tabs M v x' ds) := by
  unfold structLoadOK at h
  split at h
  · rename_i x x' ds hx
    split at h
    · rename_i fs n ptr mem hty hargs
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
        Option.isNone_iff_eq_none, List.mem_map, and_assoc] at h
      obtain ⟨hop, -, hid', hop', hty', hlay, hoff, hfresh, hnd, hfields⟩ := h
      have hargs' : x.args = #[ptr, mem] := Array.ext' (by simpa using hargs)
      exact ⟨x', ds, rfl, ⟨⟨x, fs, n, ptr, mem, hx, hty, hargs', hop, hid', hop', hty', hlay, hoff,
        fun d hd => hfresh d.id ⟨d, hd, rfl⟩, hnd, hfields⟩⟩⟩
    · cases h
  · cases h

/-- The values `slFieldsOK` accepts: per field an `OffPtr [o] ptr`, then a `Load` of it. -/
theorem slFields_mem {tabs : Tables} {ptr mem : ID} :
    ∀ (fs : List (Nat × Ty)) (as : List ID) (ds : List Value),
      slFieldsOK tabs ptr mem fs as ds = true →
      (∀ d ∈ ds, (d.op = .OffPtr ∧ d.args = #[ptr]) ∨
        (d.op = .Load ∧ ∃ o ∈ ds, d.args = #[o.id, mem])) ∧ ∀ a ∈ as, a ∈ ds.map (·.id)
  | [], [], [], _ => by simp
  | (o, t) :: fs, a :: as, op :: ld :: ds, h => by
    simp only [slFieldsOK, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
    obtain ⟨hop, hpa, -, -, hld, hla, -, ha, hrest⟩ := h
    obtain ⟨h1, h2⟩ := slFields_mem fs as ds hrest
    refine ⟨fun d hd => ?_, fun b hb => ?_⟩
    · rcases List.mem_cons.1 hd with rfl | hd
      · exact .inl ⟨hop, hpa⟩
      rcases List.mem_cons.1 hd with rfl | hd
      · exact .inr ⟨hld, op, List.mem_cons_self, hla⟩
      rcases h1 d hd with h | ⟨hl, o', ho', he⟩
      · exact .inl h
      · exact .inr ⟨hl, o', List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ho'), he⟩
    · rcases List.mem_cons.1 hb with rfl | hb
      · simp [ha]
      · simp only [List.map_cons, List.mem_cons]
        exact .inr (.inr (h2 b hb))
  | [], _ :: _, _, h | [], [], _ :: _, h | _ :: _, [], _, h | _ :: _, _ :: _, [], h
  | _ :: _, _ :: _, [_], h => by simp [slFieldsOK] at h

section SL

variable {tabs : Tables} {M : Defs} {v : ID} {x' : Value} {ds : List Value}

theorem SLFacts.v_notin (F : SLFacts tabs M v x' ds) : v ∉ ds.map (·.id) := by
  intro h
  obtain ⟨d, hd, he⟩ := List.mem_map.1 h
  have := F.hfresh d hd
  rw [he, F.hx] at this
  cases this

theorem SLFacts.nodup (F : SLFacts tabs M v x' ds) : ((x' :: ds).map (·.id)).Nodup := by
  rw [List.map_cons, List.nodup_cons, F.hid']
  exact ⟨F.v_notin, F.hnodup⟩

theorem SLFacts.get_v (F : SLFacts tabs M v x' ds) : (putAll M (x' :: ds)).get? v = some x' := by
  have := get?_putAll_mem (x' :: ds) M x' F.nodup List.mem_cons_self
  rwa [F.hid'] at this

theorem SLFacts.get_d (F : SLFacts tabs M v x' ds) {d : Value} (hd : d ∈ ds) :
    (putAll M (x' :: ds)).get? d.id = some d :=
  get?_putAll_mem (x' :: ds) M d F.nodup (List.mem_cons_of_mem _ hd)

theorem SLFacts.mem_ids (F : SLFacts tabs M v x' ds) {y : ID} :
    y ∈ (x' :: ds).map (·.id) ↔ y = v ∨ y ∈ ds.map (·.id) := by
  rw [List.map_cons, List.mem_cons, F.hid']

theorem SLFacts.get_other (F : SLFacts tabs M v x' ds) {y : ID} (hy : y ≠ v)
    (hm : (M.get? y).isSome) : (putAll M (x' :: ds)).get? y = M.get? y := by
  apply get?_putAll_not
  rw [F.mem_ids]
  rintro (h | h)
  · exact hy h
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 h
    rw [F.hfresh d hd] at hm
    cases hm

theorem SLFacts.ds_term (F : SLFacts tabs M v x' ds) {d : Value} (hd : d ∈ ds) :
    termOp d.op = true := by
  rcases (slFields_mem _ _ _ F.hfields).1 d hd with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl

theorem SLFacts.x_term (F : SLFacts tabs M v x' ds) : termOp F.x.op = true := by
  rw [F.hop]; rfl

theorem SLFacts.x'_term (F : SLFacts tabs M v x' ds) : termOp x'.op = true := by
  rw [F.hop']; rfl

/-- The defined IDs of the event are term nodes after it. -/
theorem SLFacts.def_term (F : SLFacts tabs M v x' ds) {y : ID} (hy : y ∈ (x' :: ds).map (·.id)) :
    IsTerm (putAll M (x' :: ds)).get? y := by
  rcases F.mem_ids.1 hy with rfl | h
  · exact ⟨_, F.get_v, F.x'_term⟩
  · obtain ⟨d, hd, rfl⟩ := List.mem_map.1 h
    exact ⟨d, F.get_d hd, F.ds_term hd⟩

theorem SLFacts.typed (F : SLFacts tabs M v x' ds) {ρ : ID → Val}
    (hT : Term.Typed M.get? tabs ρ) : Term.Typed (putAll M (x' :: ds)).get? tabs ρ := by
  intro a ha hsome
  by_cases hd : a ∈ (x' :: ds).map (·.id)
  · exact absurd (F.def_term hd) ha
  have hget := get?_putAll_not (x' :: ds) M a hd
  have hs : shape (putAll M (x' :: ds)).get? tabs a = shape M.get? tabs a := by
    simp only [shape, hget]
  rw [hs]
  exact hT a (fun h => ha (by unfold IsTerm at h ⊢; rw [hget]; exact h))
    (by rw [← hget]; exact hsome)

theorem SLFacts.closed (F : SLFacts tabs M v x' ds) {C : ID → Prop} (hC : DefClosed M C) :
    DefClosed (putAll M (x' :: ds)) (fun y => C y ∨ (C v ∧ y ∈ defIds (x' :: ds))) := by
  have hargsC : C v → C F.ptr ∧ C F.mem := fun hv => by
    obtain ⟨m, hm, hargs⟩ := hC v hv
    rw [F.hx] at hm; cases hm
    exact ⟨hargs _ (by rw [F.hargs]; simp), hargs _ (by rw [F.hargs]; simp)⟩
  obtain ⟨hds, has⟩ := slFields_mem _ _ _ F.hfields
  have hv_case : C v → ∃ m, (putAll M (x' :: ds)).get? v = some m ∧
      ∀ a ∈ m.args, C a ∨ (C v ∧ a ∈ defIds (x' :: ds)) := fun hv =>
    ⟨_, F.get_v, fun a ha => .inr ⟨hv, by
      unfold defIds; rw [F.mem_ids]
      exact .inr (has a (Array.mem_toList_iff.2 ha))⟩⟩
  intro y hy
  rcases hy with hy | ⟨hv, hy⟩
  · by_cases hyv : y = v
    · subst hyv; exact hv_case hy
    obtain ⟨m, hm, hargs⟩ := hC y hy
    exact ⟨m, by rw [F.get_other hyv (by rw [hm]; rfl), hm], fun a ha => .inl (hargs a ha)⟩
  · unfold defIds at hy
    rcases F.mem_ids.1 hy with rfl | h
    · exact hv_case hv
    obtain ⟨d, hd, rfl⟩ := List.mem_map.1 h
    refine ⟨d, F.get_d hd, fun a ha => ?_⟩
    rcases hds d hd with ⟨-, he⟩ | ⟨-, o, ho, he⟩
    · rw [he] at ha
      simp only [List.mem_toArray, List.mem_singleton] at ha
      subst ha; exact .inl (hargsC hv).1
    · rw [he] at ha
      simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact .inr ⟨hv, by unfold defIds; rw [F.mem_ids]; exact .inr (List.mem_map_of_mem ho)⟩
      · exact .inl (hargsC hv).2

theorem evalPure_load (ty : Ty) (ai : Int64) (ax : Option AuxRef) (args : List Val) :
    evalPure .Load ty ai ax args = loadOp ty args := rfl

theorem evalPure_offPtr (ty : Ty) (ai : Int64) (ax : Option AuxRef) (args : List Val) :
    evalPure .OffPtr ty ai ax args = PtrOps.offPtr ai args := rfl

theorem evalPure_structMake (ty : Ty) (ai : Int64) (ax : Option AuxRef) (args : List Val) :
    evalPure .StructMake ty ai ax args = Comp.make args := rfl

/-- The `StructMake`'s arguments denote the field loads `structLoad_ref` asks for. -/
theorem sl_fields {D : ID → Option Value} {ρ : ID → Val} {k : Nat} {ptr mem : ID} :
    ∀ (fs : List (Nat × Ty)) (as : List ID) (ds : List Value),
      slFieldsOK tabs ptr mem fs as ds = true → (∀ d ∈ ds, D d.id = some d) →
      Fields (fun w f => ∃ e, w = fieldVal (den D tabs ρ k ptr) (den D tabs ρ (k + 1) mem) f.1
        (.ptr e) f.2) (as.map (den D tabs ρ (k + 2))) fs
  | [], [], [], _, _ => trivial
  | (o, t) :: fs, a :: as, op :: ld :: ds, h, hD => by
    simp only [slFieldsOK, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
    obtain ⟨hop, hpa, hai, hpt, hld, hla, hlt, ha, hrest⟩ := h
    refine ⟨?_, sl_fields fs as ds hrest fun d hd =>
      hD d (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hd))⟩
    obtain ⟨e, he⟩ : ∃ e, tabs.ty op.type = .ptr e := by
      revert hpt; cases tabs.ty op.type <;> simp
    refine ⟨e, ?_⟩
    have hDop := hD op List.mem_cons_self
    have hDld := hD ld (List.mem_cons_of_mem _ List.mem_cons_self)
    rw [ha, den_succ_term hDld (by rw [hld]; rfl), tyEq_sound hlt, hla, hld]
    simp only [List.toList_toArray, List.map_cons, List.map_nil]
    rw [den_succ_term hDop (by rw [hop]; rfl), hpa, he, hai, hop]
    simp only [List.toList_toArray, List.map_cons, List.map_nil]
    rw [GoFV.Proof.Rules.opVal_pure (op := .Load) rfl,
      GoFV.Proof.Rules.opVal_pure (op := .OffPtr) rfl, evalPure_load, evalPure_offPtr]
    rfl
  | [], _ :: _, _, h, _ | [], [], _ :: _, h, _ | _ :: _, [], _, h, _ | _ :: _, _ :: _, [], h, _
  | _ :: _, _ :: _, [_], h, _ => by simp [slFieldsOK] at h

/-- **A struct-load event refines the denotations of a closed set**, with three times the fuel. -/
theorem SLFacts.step (F : SLFacts tabs M v x' ds) {C : ID → Prop} (hC : DefClosed M C)
    {ρ : ID → Val} : ∀ n y, C y →
      Sem.Refines (den M.get? tabs ρ n y) (den (putAll M (x' :: ds)).get? tabs ρ (3 * n) y)
  | 0, _, _ => .poison _
  | n + 1, y, hy => by
    obtain ⟨m, hm, hargs⟩ := hC y hy
    have ih : ∀ a ∈ m.args, ∀ k, 3 * n ≤ k →
        Sem.Refines (den M.get? tabs ρ n a) (den (putAll M (x' :: ds)).get? tabs ρ k a) :=
      fun a ha k hk => (SLFacts.step F hC n a (hargs a ha)).trans (den_fuel_mono _ _ _ _ _ _ hk)
    by_cases hyv : y = v
    · subst hyv
      rw [F.hx] at hm; cases hm
      have hp : F.ptr ∈ F.x.args := by rw [F.hargs]; simp
      have hmm : F.mem ∈ F.x.args := by rw [F.hargs]; simp
      have ihp := ih _ hp (3 * n) (Nat.le_refl _)
      have ihm := ih _ hmm (3 * n + 1) (by omega)
      rw [den_succ_term F.hx F.x_term, show 3 * (n + 1) = (3 * n + 2) + 1 by omega,
        den_succ_term F.get_v F.x'_term, F.hop, F.hop', F.hty', F.hty, F.hargs,
        GoFV.Proof.Rules.opVal_pure (op := .Load) rfl,
        GoFV.Proof.Rules.opVal_pure (op := .StructMake) rfl, evalPure_structMake]
      simp only [List.toList_toArray, List.map_cons, List.map_nil]
      refine (retype_mono _ (evalPure_mono _ _ _ _ (.cons ihp (.cons ihm .nil)))).trans ?_
      rw [evalPure_load]
      exact structLoad_ref F.hlay F.hoff _ _
        (sl_fields _ _ _ F.hfields fun d hd => F.get_d hd)
    · have hget := F.get_other hyv (by rw [hm]; rfl)
      by_cases ht : termOp m.op = true
      · rw [den_succ_term hm ht, show 3 * (n + 1) = (3 * n + 2) + 1 by omega,
          den_succ_term (by rw [hget]; exact hm) ht]
        exact retype_mono _ (GoFV.Proof.Rules.opVal_mono _ _ _ _ _ (refinesList_map fun a ha =>
          ih a (Array.mem_toList_iff.1 ha) _ (by omega)))
      · have h1 : ¬ IsTerm M.get? y := fun ⟨u, hu, hut⟩ => by
          rw [hm] at hu; cases hu; exact ht hut
        have h2 : ¬ IsTerm (putAll M (x' :: ds)).get? y := fun ⟨u, hu, hut⟩ => by
          rw [hget, hm] at hu; cases hu; exact ht hut
        rw [show 3 * (n + 1) = (3 * n + 2) + 1 by omega, den_succ_atom h1, den_succ_atom h2]
        exact Sem.Refines.refl _

theorem ReplayInv.structLoad {D₀ : ID → Option Value} {C₀ C : ID → Prop}
    (hI : ReplayInv tabs D₀ C₀ M C) (F : SLFacts tabs M v x' ds) :
    ReplayInv tabs D₀ C₀ (putAll M (x' :: ds)) (fun y => C y ∨ (C v ∧ y ∈ defIds (x' :: ds))) where
  closed := F.closed hI.closed
  sub := fun y h => .inl (hI.sub y h)
  typed := fun ρ h => F.typed (hI.typed ρ h)
  denRef := fun y hy => den_compose (g := (3 * ·)) (hI.denRef y hy) hI.typed
    fun _ _ n => F.step hI.closed n y (hI.sub y hy)
  atoms := fun y a hy ha hargs => by
    obtain ⟨a', ha', hat, hsz, hrest⟩ := hI.atoms y a hy ha hargs
    have hyv : y ≠ v := fun h => by
      rw [h, F.hx] at ha'; cases ha'; rw [F.x_term] at hat; cases hat
    refine ⟨a', by rw [F.get_other hyv (by rw [ha']; rfl)]; exact ha', hat, hsz,
      fun i hi => ⟨.inl (hrest i hi).1, ?_⟩⟩
    exact den_compose (g := (3 * ·)) (hrest i hi).2 hI.typed
      fun _ _ n => F.step hI.closed n _ (hrest i hi).1

end SL

end GoFV.Proof.Pass.Rewrite
