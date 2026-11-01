import GoFV.Proof.Pass.StructLoad
import GoFV.Proof.Pass.RewriteMakeSel
import GoFV.Proof.Rules.SelLoad

/-!
# Replaying a selection of a `Load` (issue #17)

A rule event accepted by `RewriteCheck.loadSelOK` (an unconditional selection of a `Load` with
an `@b` result, `loadSelShape`: `(StructSelect [i] x:(Load <t> ptr mem)) => @x.Block (Load
<v.Type> (OffPtr <v.Type.PtrTo()> [t.FieldOff(int(i))] ptr) mem)`, `dec.rules:141`, and the
`ArraySelect` form `:132`) redefines the selection `v` of component `k` of `s = Load <agg fs n>
p m` as `Copy top`, `top` a fresh `Load` of field `k`'s shape on a fresh `OffPtr [o] p`, `o` the
field's offset. `LSFacts.step`: on a set closed under arguments, every denotation after the
event refines the one before, with three times the fuel (`selLoad_ref` at `v`: component `k` of
the `Load` is refined by the field's `Load` at its offset; monotonicity elsewhere).
`ReplayInv.loadSel`: the event keeps the replay invariant.
-/

namespace GoFV.Proof.Pass.Rewrite

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck GoFV.Proof.Term GoFV.Proof.AtomSim
open GoFV.Proof.Pass.StructLoad (fieldVal)

/-- What `loadSelOK` establishes about an event `(v, [u0, top, off])`. -/
structure LSFacts (tabs : Tables) (M : Defs) (v : ID) (u0 top off : Value) where
  x : Value
  s : ID
  y : Value
  k : Nat
  fs : List (Nat × Ty)
  n : Nat
  p : ID
  m : ID
  o : Nat
  t : Ty
  hx : M.get? v = some x
  hxargs : x.args.toList = [s]
  hk : selIndex? x.op x.auxInt = some k
  hy : M.get? s = some y
  hyty : tabs.ty y.type = .agg fs n
  hyargs : y.args.toList = [p, m]
  hfk : fs[k]? = some (o, t)
  hyop : y.op = .Load
  hlay : layoutsOK n fs = true
  hoff : ∀ f ∈ fs, f.1 < n
  hid : u0.id = v
  huop : u0.op = .Copy
  huargs : u0.args = #[top.id]
  huty : u0.type = x.type
  htopF : M.get? top.id = none
  hoffF : M.get? off.id = none
  hne : top.id ≠ off.id
  htop : top.op = .Load
  htargs : top.args = #[off.id, m]
  httyp : tabs.ty top.type = t
  hcc : copyCompat (tabs.ty x.type) (tabs.ty top.type) = true
  hoop : off.op = .OffPtr
  hoargs : off.args = #[p]
  hoai : off.auxInt = Int64.ofNat o
  hopt : ∃ e, tabs.ty off.type = .ptr e

theorem lsFacts {tabs : Tables} {M : Defs} {v : ID} {defs : List Value}
    (h : loadSelOK tabs M v defs = true) :
    ∃ u0 top off, defs = [u0, top, off] ∧ Nonempty (LSFacts tabs M v u0 top off) := by
  unfold loadSelOK at h
  split at h
  · rename_i x u0 top off hx
    split at h
    · rename_i s k hxargs hk
      split at h
      · rename_i y hy
        split at h
        · rename_i fs n p m hyty hyargs
          split at h
          · rename_i o t hfk
            simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq,
              Option.isNone_iff_eq_none, bne_iff_ne, ne_eq] at h
            obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hyop, hlay⟩, hoff⟩, hid⟩, huop⟩, huargs⟩, huty⟩, -⟩,
              -⟩, htopF⟩, hoffF⟩, hne⟩, htop⟩, htargs⟩, htt⟩, hcc⟩, hoop⟩, hoargs⟩, hoai⟩,
              hopt⟩ := h
            refine ⟨u0, top, off, rfl, ⟨⟨x, s, y, k, fs, n, p, m, o, t, hx, hxargs, hk, hy, hyty,
              hyargs, hfk, hyop, hlay, hoff, hid, huop, huargs, huty, htopF, hoffF, hne, htop,
              htargs, tyEq_sound htt, hcc, hoop, hoargs, hoai, ?_⟩⟩⟩
            revert hopt; cases tabs.ty off.type <;> simp
          · cases h
        · cases h
      · cases h
    · cases h
  · cases h

section LS

variable {tabs : Tables} {M : Defs} {v : ID} {u0 top off : Value}

theorem LSFacts.top_ne (F : LSFacts tabs M v u0 top off) : top.id ≠ v := fun h => by
  have := F.htopF; rw [h, F.hx] at this; cases this

theorem LSFacts.off_ne (F : LSFacts tabs M v u0 top off) : off.id ≠ v := fun h => by
  have := F.hoffF; rw [h, F.hx] at this; cases this

theorem LSFacts.nodup (F : LSFacts tabs M v u0 top off) : ([u0, top, off].map (·.id)).Nodup := by
  simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons, List.not_mem_nil,
    or_false, F.hid, List.nodup_nil, and_true, not_or]
  exact ⟨⟨fun h => F.top_ne h.symm, fun h => F.off_ne h.symm⟩, F.hne, not_false⟩

theorem LSFacts.get_v (F : LSFacts tabs M v u0 top off) :
    (putAll M [u0, top, off]).get? v = some u0 := by
  have := get?_putAll_mem [u0, top, off] M u0 F.nodup List.mem_cons_self
  rwa [F.hid] at this

theorem LSFacts.get_top (F : LSFacts tabs M v u0 top off) :
    (putAll M [u0, top, off]).get? top.id = some top :=
  get?_putAll_mem _ M top F.nodup (by simp)

theorem LSFacts.get_off (F : LSFacts tabs M v u0 top off) :
    (putAll M [u0, top, off]).get? off.id = some off :=
  get?_putAll_mem _ M off F.nodup (by simp)

theorem LSFacts.mem_ids (F : LSFacts tabs M v u0 top off) {y : ID} :
    y ∈ [u0, top, off].map (·.id) ↔ y = v ∨ y = top.id ∨ y = off.id := by
  simp [F.hid]

theorem LSFacts.get_other (F : LSFacts tabs M v u0 top off) {y : ID} (hy : y ≠ v)
    (hm : (M.get? y).isSome) : (putAll M [u0, top, off]).get? y = M.get? y := by
  apply get?_putAll_not
  rw [F.mem_ids]
  rintro (h | h | h)
  · exact hy h
  · subst h; rw [F.htopF] at hm; cases hm
  · subst h; rw [F.hoffF] at hm; cases hm

theorem LSFacts.x_term (F : LSFacts tabs M v u0 top off) : termOp F.x.op = true := (sel_facts F.hk).1

/-- The defined IDs of the event are term nodes after it. -/
theorem LSFacts.def_term (F : LSFacts tabs M v u0 top off) {y : ID}
    (hy : y ∈ [u0, top, off].map (·.id)) : IsTerm (putAll M [u0, top, off]).get? y := by
  rcases F.mem_ids.1 hy with rfl | rfl | rfl
  · exact ⟨_, F.get_v, by rw [F.huop]; rfl⟩
  · exact ⟨_, F.get_top, by rw [F.htop]; rfl⟩
  · exact ⟨_, F.get_off, by rw [F.hoop]; rfl⟩

theorem LSFacts.typed (F : LSFacts tabs M v u0 top off) {ρ : ID → Val}
    (hT : Term.Typed M.get? tabs ρ) : Term.Typed (putAll M [u0, top, off]).get? tabs ρ := by
  intro a ha hsome
  by_cases hd : a ∈ [u0, top, off].map (·.id)
  · exact absurd (F.def_term hd) ha
  have hget := get?_putAll_not [u0, top, off] M a hd
  have hs : shape (putAll M [u0, top, off]).get? tabs a = shape M.get? tabs a := by
    simp only [shape, hget]
  rw [hs]
  exact hT a (fun h => ha (by unfold IsTerm at h ⊢; rw [hget]; exact h))
    (by rw [← hget]; exact hsome)

/-- The `Load`'s pointer and memory are in a set closed under arguments that holds `v`. -/
theorem LSFacts.pm_mem (F : LSFacts tabs M v u0 top off) {C : ID → Prop} (hC : DefClosed M C)
    (hv : C v) : C F.s ∧ C F.p ∧ C F.m := by
  obtain ⟨w, hw, hargs⟩ := hC v hv
  rw [F.hx] at hw; cases hw
  have hs : C F.s := hargs _ (Array.mem_toList_iff.1 (by rw [F.hxargs]; exact List.mem_singleton_self _))
  obtain ⟨w', hw', hargs'⟩ := hC F.s hs
  rw [F.hy] at hw'; cases hw'
  exact ⟨hs, hargs' _ (Array.mem_toList_iff.1 (by rw [F.hyargs]; simp)),
    hargs' _ (Array.mem_toList_iff.1 (by rw [F.hyargs]; simp))⟩

theorem LSFacts.closed (F : LSFacts tabs M v u0 top off) {C : ID → Prop} (hC : DefClosed M C) :
    DefClosed (putAll M [u0, top, off]) (fun y => C y ∨ (C v ∧ y ∈ defIds [u0, top, off])) := by
  have hdef : ∀ y, y ∈ defIds [u0, top, off] ↔ y = v ∨ y = top.id ∨ y = off.id :=
    fun y => F.mem_ids
  have hnew : C v → ∀ y, y = v ∨ y = top.id ∨ y = off.id → ∃ w,
      (putAll M [u0, top, off]).get? y = some w ∧
      ∀ a ∈ w.args, C a ∨ (C v ∧ a ∈ defIds [u0, top, off]) := by
    intro hv y hy
    obtain ⟨-, hp, hm⟩ := F.pm_mem hC hv
    rcases hy with rfl | rfl | rfl
    · refine ⟨u0, F.get_v, fun a ha => ?_⟩
      rw [F.huargs] at ha
      simp only [List.mem_toArray, List.mem_singleton] at ha
      exact .inr ⟨hv, (hdef a).2 (.inr (.inl ha))⟩
    · refine ⟨top, F.get_top, fun a ha => ?_⟩
      rw [F.htargs] at ha
      simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact .inr ⟨hv, (hdef _).2 (.inr (.inr rfl))⟩
      · exact .inl hm
    · refine ⟨off, F.get_off, fun a ha => ?_⟩
      rw [F.hoargs] at ha
      simp only [List.mem_toArray, List.mem_singleton] at ha
      subst ha; exact .inl hp
  intro y hy
  rcases hy with hy | ⟨hv, hy⟩
  · by_cases hyv : y = v
    · subst hyv; exact hnew hy _ (.inl rfl)
    obtain ⟨w, hw, hargs⟩ := hC y hy
    exact ⟨w, by rw [F.get_other hyv (by rw [hw]; rfl), hw], fun a ha => .inl (hargs a ha)⟩
  · exact hnew hv y ((hdef y).1 hy)

/-- `fieldVal` is monotone in the pointer and the memory. -/
theorem fieldVal_mono {P P' Mv Mv' : Val} (hP : Sem.Refines P P') (hM : Sem.Refines Mv Mv')
    (o : Nat) (pt t : Ty) : Sem.Refines (fieldVal P Mv o pt t) (fieldVal P' Mv' o pt t) := by
  unfold fieldVal
  rw [← evalPure_load t 0 none, ← evalPure_load t 0 none, ← evalPure_offPtr pt _ none,
    ← evalPure_offPtr pt _ none]
  exact retype_mono _ (evalPure_mono _ _ _ _
    (.cons (retype_mono _ (evalPure_mono _ _ _ _ (.cons hP .nil))) (.cons hM .nil)))

/-- **A selection-of-`Load` event refines the denotations of a closed set**, with three times
the fuel. -/
theorem LSFacts.step (F : LSFacts tabs M v u0 top off) {C : ID → Prop} (hC : DefClosed M C)
    {ρ : ID → Val} (hT : Term.Typed M.get? tabs ρ) : ∀ n y, C y →
      Sem.Refines (den M.get? tabs ρ n y) (den (putAll M [u0, top, off]).get? tabs ρ (3 * n) y) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n IH => ?_
  intro y hy
  rcases n with _ | n
  · exact .poison _
  · obtain ⟨w, hw, hargs⟩ := hC y hy
    by_cases hyv : y = v
    · subst hyv
      rw [F.hx] at hw; cases hw
      obtain ⟨-, hp, hm⟩ := F.pm_mem hC hy
      rw [den_succ_term F.hx F.x_term, GoFV.Proof.Rules.opVal_pure (sel_facts F.hk).2.1,
        (sel_facts F.hk).2.2, F.hxargs]
      simp only [List.map_cons, List.map_nil]
      cases n with
      | zero =>
        rw [show Comp.select F.k [den M.get? tabs ρ 0 F.s] = .poison from rfl, retype_poison]
        exact .poison _
      | succ n =>
        have ihp := (IH n (by omega) F.p hp).trans
          (den_fuel_mono _ _ _ (3 * n) (3 * n + 3) _ (by omega))
        have ihm := (IH n (by omega) F.m hm).trans
          (den_fuel_mono _ _ _ (3 * n) (3 * n + 4) _ (by omega))
        have hT' := F.typed hT
        rw [den_succ_term F.hy (by rw [F.hyop]; rfl), F.hyop, F.hyty, F.hyargs,
          GoFV.Proof.Rules.opVal_pure (op := .Load) rfl, evalPure_load]
        simp only [List.map_cons, List.map_nil]
        have hcc' : copyCompat (tabs.ty u0.type) (tabs.ty top.type) = true := by
          rw [F.huty]; exact F.hcc
        rw [show 3 * (n + 1 + 1) = (3 * n + 5) + 1 by omega,
          den_copy hT' F.get_v F.huop (by rw [F.huargs]; rfl)
            (by rw [F.huargs]; exact F.get_top) hcc',
          show (u0.args[0]! : ID) = top.id by rw [F.huargs]; rfl,
          show 3 * n + 5 = (3 * n + 4) + 1 by omega,
          den_succ_term F.get_top (by rw [F.htop]; rfl), F.htop, F.httyp, F.htargs,
          GoFV.Proof.Rules.opVal_pure (op := .Load) rfl, evalPure_load]
        simp only [List.toList_toArray, List.map_cons, List.map_nil]
        obtain ⟨e, he⟩ := F.hopt
        rw [show 3 * n + 4 = (3 * n + 3) + 1 by omega,
          den_succ_term F.get_off (by rw [F.hoop]; rfl), F.hoop, he, F.hoai, F.hoargs,
          GoFV.Proof.Rules.opVal_pure (op := .OffPtr) rfl, evalPure_offPtr]
        simp only [List.toList_toArray, List.map_cons, List.map_nil]
        have hsel := retype_mono (tabs.ty F.x.type)
          (GoFV.Proof.Rules.selLoad_ref F.hlay F.hoff (den M.get? tabs ρ n F.p)
            (den M.get? tabs ρ n F.m) F.hfk e)
        have hfix : (fieldVal (den M.get? tabs ρ n F.p) (den M.get? tabs ρ n F.m) F.o (.ptr e)
            F.t).retype (tabs.ty F.x.type) =
            fieldVal (den M.get? tabs ρ n F.p) (den M.get? tabs ρ n F.m) F.o (.ptr e) F.t := by
          apply retype_copyCompat (F.httyp ▸ F.hcc)
          unfold fieldVal; exact Val.retype_idem _ _
        rw [hfix] at hsel
        exact hsel.trans (fieldVal_mono ihp ihm F.o (.ptr e) F.t)
    · have hget := F.get_other hyv (by rw [hw]; rfl)
      have ih : ∀ a ∈ w.args, ∀ k, 3 * n ≤ k →
          Sem.Refines (den M.get? tabs ρ n a) (den (putAll M [u0, top, off]).get? tabs ρ k a) :=
        fun a ha k hk => (IH n (by omega) a (hargs a ha)).trans
          (den_fuel_mono _ _ _ _ _ _ hk)
      by_cases ht : termOp w.op = true
      · rw [den_succ_term hw ht, show 3 * (n + 1) = (3 * n + 2) + 1 by omega,
          den_succ_term (by rw [hget]; exact hw) ht]
        exact retype_mono _ (GoFV.Proof.Rules.opVal_mono _ _ _ _ _ (refinesList_map fun a ha =>
          ih a (Array.mem_toList_iff.1 ha) _ (by omega)))
      · have h1 : ¬ IsTerm M.get? y := fun ⟨u, hu, hut⟩ => by
          rw [hw] at hu; cases hu; exact ht hut
        have h2 : ¬ IsTerm (putAll M [u0, top, off]).get? y := fun ⟨u, hu, hut⟩ => by
          rw [hget, hw] at hu; cases hu; exact ht hut
        rw [show 3 * (n + 1) = (3 * n + 2) + 1 by omega, den_succ_atom h1, den_succ_atom h2]
        exact Sem.Refines.refl _

theorem ReplayInv.loadSel {D₀ : ID → Option Value} {C₀ C : ID → Prop}
    (hI : ReplayInv tabs D₀ C₀ M C) (F : LSFacts tabs M v u0 top off) :
    ReplayInv tabs D₀ C₀ (putAll M [u0, top, off])
      (fun y => C y ∨ (C v ∧ y ∈ defIds [u0, top, off])) where
  closed := F.closed hI.closed
  sub := fun y h => .inl (hI.sub y h)
  typed := fun ρ h => F.typed (hI.typed ρ h)
  denRef := fun y hy => den_compose (g := (3 * ·)) (hI.denRef y hy) hI.typed
    fun _ hρ n => F.step hI.closed hρ n y (hI.sub y hy)
  atoms := fun y a hy ha hargs => by
    obtain ⟨a', ha', hat, hsz, hrest⟩ := hI.atoms y a hy ha hargs
    have hyv : y ≠ v := fun h => by
      rw [h, F.hx] at ha'; cases ha'; rw [F.x_term] at hat; cases hat
    refine ⟨a', by rw [F.get_other hyv (by rw [ha']; rfl)]; exact ha', hat, hsz,
      fun i hi => ⟨.inl (hrest i hi).1, ?_⟩⟩
    exact den_compose (g := (3 * ·)) (hrest i hi).2 hI.typed
      fun _ hρ n => F.step hI.closed hρ n _ (hrest i hi).1

end LS

end GoFV.Proof.Pass.Rewrite
