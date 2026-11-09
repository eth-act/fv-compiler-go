import GoFV.Proof.Pass.RewriteTermStep
import GoFV.Proof.Rules.AllSound

variable [GoFV.SSA.Sem.Addrs]

/-!
# Replaying the log refines the denotations (issue #113)

`replay_inv`: along a successful `replay` of the log, starting from the input's value table
`D₀`, the values of a set `C₀` closed under arguments keep a refining denotation
(`ReplayInv`), and the atoms of `D₀` whose arguments are in `C₀` keep their fields while their
arguments (rewritten only by `copyArg` events, through compatible copies) keep refining
denotations. Rule events use `RuleFacts.step` and `Rule.SoundTop` of the table's rule
(`ofRuleSet_sound`; the variadic selections `Rule.MakeSel` are `RewriteMakeSel.lean`'s).
-/

namespace GoFV.Proof.Pass.Rewrite

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck GoFV.Proof.Term GoFV.Proof.AtomSim
open GoFV.Rules (Pat Rule RuleSet RwEvent BlockRule)

/-! ## The rule table -/

theorem ofRuleSet_values (s : RuleSet) : (GoFV.Rules.Interp.Table.ofRuleSet s).values =
    s.values.foldl (fun values (p : Op × List Rule) =>
      values.set! p.1.ctorIdx (p.2.toArray.map GoFV.Rules.Interp.CRule.ofRule))
      (Array.replicate (Op.all.size + 1) #[]) := by
  unfold GoFV.Rules.Interp.Table.ofRuleSet
  simp

theorem foldl_rows (L : List (Op × List Rule)) : ∀ (l : List (Op × List Rule)), (∀ p ∈ l, p ∈ L) →
    ∀ (A : Array (Array GoFV.Rules.Interp.CRule)),
    (∀ (k : Nat) row, A[k]? = some row →
      row = #[] ∨ ∃ p ∈ L, row = p.2.toArray.map GoFV.Rules.Interp.CRule.ofRule) →
    ∀ (k : Nat) row, (l.foldl (fun values (p : Op × List Rule) =>
        values.set! p.1.ctorIdx (p.2.toArray.map GoFV.Rules.Interp.CRule.ofRule)) A)[k]? = some row →
      row = #[] ∨ ∃ p ∈ L, row = p.2.toArray.map GoFV.Rules.Interp.CRule.ofRule
  | [], _, _, hA => hA
  | p :: l, hl, A, hA => by
    simp only [List.foldl_cons]
    refine foldl_rows L l (fun q hq => hl q (List.mem_cons_of_mem _ hq)) _ (fun k row h => ?_)
    simp only [Array.set!, Array.getElem?_setIfInBounds] at h
    split at h
    · split at h
      · cases h; exact .inr ⟨p, hl p List.mem_cons_self, rfl⟩
      · cases h
    · exact hA k row h

/-- Every rule of the table of a sound rule set is sound or a validated variadic selection. -/
theorem ofRuleSet_sound {s : RuleSet} (hs : s.AllSound) {k i : Nat} {cr : GoFV.Rules.Interp.CRule}
    (h : ((GoFV.Rules.Interp.Table.ofRuleSet s).values[k]?).bind (·[i]?) = some cr) :
    GoFV.Proof.Rules.Rule.Checked cr.rule := by
  cases hk : (GoFV.Rules.Interp.Table.ofRuleSet s).values[k]? with
  | none => rw [hk] at h; cases h
  | some row =>
    rw [hk] at h
    simp only [Option.bind_some] at h
    rw [ofRuleSet_values] at hk
    rcases foldl_rows s.values s.values (fun _ h => h) _ (fun k row h => by
        rw [Array.getElem?_replicate] at h
        split at h
        · cases h; exact .inl rfl
        · cases h) k row hk with rfl | ⟨p, hp, rfl⟩
    · simp at h
    · have hm := Array.mem_of_getElem? h
      simp only [Array.mem_map, List.mem_toArray] at hm
      obtain ⟨r, hr, rfl⟩ := hm
      exact hs.1 p hp r hr

theorem ofRuleSet_blocks (s : RuleSet) : (GoFV.Rules.Interp.Table.ofRuleSet s).blocks =
    s.blocks.foldl (fun blocks (p : BlockKind × List BlockRule) =>
      blocks.set! p.1.ctorIdx p.2.toArray)
      (Array.replicate (BlockKind.all.size + 1) #[]) := by
  unfold GoFV.Rules.Interp.Table.ofRuleSet
  simp

theorem foldl_brows (L : List (BlockKind × List BlockRule)) :
    ∀ (l : List (BlockKind × List BlockRule)), (∀ p ∈ l, p ∈ L) →
    ∀ (A : Array (Array BlockRule)),
    (∀ (k : Nat) row, A[k]? = some row → row = #[] ∨ ∃ p ∈ L, row = p.2.toArray) →
    ∀ (k : Nat) row, (l.foldl (fun blocks (p : BlockKind × List BlockRule) =>
        blocks.set! p.1.ctorIdx p.2.toArray) A)[k]? = some row →
      row = #[] ∨ ∃ p ∈ L, row = p.2.toArray
  | [], _, _, hA => hA
  | p :: l, hl, A, hA => by
    simp only [List.foldl_cons]
    refine foldl_brows L l (fun q hq => hl q (List.mem_cons_of_mem _ hq)) _ (fun k row h => ?_)
    simp only [Array.set!, Array.getElem?_setIfInBounds] at h
    split at h
    · split at h
      · cases h; exact .inr ⟨p, hl p List.mem_cons_self, rfl⟩
      · cases h
    · exact hA k row h

/-- Every block rule of the table of a sound rule set is sound. -/
theorem ofRuleSet_blockSound {s : RuleSet} (hs : s.AllSound) {k i : Nat} {br : BlockRule}
    (h : ((GoFV.Rules.Interp.Table.ofRuleSet s).blocks[k]?).bind (·[i]?) = some br) :
    GoFV.Proof.Rules.BlockRule.Sound br := by
  cases hk : (GoFV.Rules.Interp.Table.ofRuleSet s).blocks[k]? with
  | none => rw [hk] at h; cases h
  | some row =>
    rw [hk] at h
    simp only [Option.bind_some] at h
    rw [ofRuleSet_blocks] at hk
    rcases foldl_brows s.blocks s.blocks (fun _ h => h) _ (fun k row h => by
        rw [Array.getElem?_replicate] at h
        split at h
        · cases h; exact .inl rfl
        · cases h) k row hk with rfl | ⟨p, hp, rfl⟩
    · simp at h
    · have hm := Array.mem_of_getElem? h
      simp only [List.mem_toArray] at hm
      exact hs.2 p hp br hm

/-! ## `copyArg` events -/

theorem copyReach_closed {tabs : Tables} {M : Defs} {C : ID → Prop} (hC : DefClosed M C) :
    ∀ (N : Nat) (a w : ID), copyReach tabs M N a w = true → C a → C w
  | 0, a, w, h, ha => by simp only [copyReach, beq_iff_eq] at h; exact h ▸ ha
  | N + 1, a, w, h, ha => by
    simp only [copyReach, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact ha
    · cases hx : M.get? a with
      | none => rw [hx] at h; cases h
      | some x =>
        rw [hx] at h
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨⟨-, hsz⟩, -⟩, hr⟩ := h
        obtain ⟨m, hm, hargs⟩ := hC a ha
        rw [hx] at hm; cases hm
        exact copyReach_closed hC N _ w hr (hargs _ (Array.mem_toList_iff.1 (by
          rw [toList_of_size_one hsz]; exact List.mem_singleton_self _)))

theorem copyReachW_closed {tabs : Tables} {M : Defs} {C : ID → Prop} (hC : DefClosed M C)
    {N : Nat} {a w : ID} (h : copyReachW tabs M N a w = true) (ha : C a) : C w := by
  unfold copyReachW at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · exact copyReach_closed hC N a w h ha
  · cases hx : M.get? a with
    | none => rw [hx] at h; cases h
    | some x =>
      rw [hx] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨⟨⟨-, hsz⟩, -⟩, -⟩, hr⟩ := h
      obtain ⟨m, hm, hargs⟩ := hC a ha
      rw [hx] at hm; cases hm
      exact copyReach_closed hC N _ w hr (hargs _ (Array.mem_toList_iff.1 (by
        rw [toList_of_size_one hsz]; exact List.mem_singleton_self _)))

section CopyArg

variable {tabs : Tables} {M : Defs} {v : ID} {x : Value} {i : Nat} {src : ID}

/-- The definitions after a `copyArg` event. -/
def copyPut (M : Defs) (v : ID) (x : Value) (i : Nat) (src : ID) (h : i < x.args.size) : Defs :=
  M.put v { x with args := x.args.set i src h }

theorem copyPut_get (hi : i < x.args.size) (y : ID) : (copyPut M v x i src hi).get? y =
    if y = v then some { x with args := x.args.set i src hi } else M.get? y := get?_put _ _ _ _

theorem copyPut_isTerm (hx : M.get? v = some x) (hi : i < x.args.size) (y : ID) :
    IsTerm (copyPut M v x i src hi).get? y ↔ IsTerm M.get? y := by
  simp only [IsTerm, copyPut_get]
  split
  · subst y; rw [hx]
    constructor
    · rintro ⟨u, hu, ht⟩; cases hu; exact ⟨x, rfl, ht⟩
    · rintro ⟨u, hu, ht⟩; cases hu; exact ⟨_, rfl, ht⟩
  · exact Iff.rfl

theorem copyPut_typed (hx : M.get? v = some x) (hi : i < x.args.size) {ρ : ID → Val}
    (hT : Term.Typed M.get? tabs ρ) : Term.Typed (copyPut M v x i src hi).get? tabs ρ := by
  intro a ha hsome
  have hs : shape (copyPut M v x i src hi).get? tabs a = shape M.get? tabs a := by
    simp only [shape, copyPut_get]; split
    · subst a; rw [hx]; rfl
    · rfl
  have hsome' : (M.get? a).isSome = true := by
    rw [copyPut_get] at hsome; split at hsome
    · subst a; rw [hx]; rfl
    · exact hsome
  rw [hs]
  exact hT a (fun h => ha ((copyPut_isTerm hx hi a).2 h)) hsome'

theorem copyPut_closed (hx : M.get? v = some x) (hi : i < x.args.size)
    (hr : copyReachW tabs M M.size x.args[i] src = true) {C : ID → Prop} (hC : DefClosed M C) :
    DefClosed (copyPut M v x i src hi) C := by
  intro y hy
  obtain ⟨m, hm, hargs⟩ := hC y hy
  rw [copyPut_get]
  split
  · subst y; rw [hx] at hm; cases hm
    refine ⟨_, rfl, fun a ha => ?_⟩
    rcases Array.mem_or_eq_of_mem_set (w := hi) ha with ha | rfl
    · exact hargs a ha
    · exact copyReachW_closed hC hr (hargs _ (Array.getElem_mem hi))
  · exact ⟨m, hm, hargs⟩

/-- A `copyArg` event refines the denotations of a closed set. -/
theorem copyPut_den (hx : M.get? v = some x) (hi : i < x.args.size)
    (hr : copyReachW tabs M M.size x.args[i] src = true) {C : ID → Prop} (hC : DefClosed M C)
    {ρ : ID → Val} (hT : Term.Typed M.get? tabs ρ) :
    ∀ n y, C y → Sem.Refines (den M.get? tabs ρ n y) (den (copyPut M v x i src hi).get? tabs ρ n y)
  | 0, _, _ => .poison _
  | n + 1, y, hy => by
    obtain ⟨m, hm, hargs⟩ := hC y hy
    by_cases ht : IsTerm M.get? y
    · have ht' := (copyPut_isTerm (src := src) hx hi y).2 ht
      obtain ⟨m', hm', hop⟩ := ht
      rw [hm] at hm'; cases hm'
      by_cases hyv : y = v
      · rw [hyv] at hm ⊢
        rw [hx] at hm; cases hm
        have hnew : (copyPut M v x i src hi).get? v = some { x with args := x.args.set i src hi } := by
          rw [copyPut_get]; simp
        rw [den_succ_term hx hop, den_succ_term hnew hop]
        apply retype_mono; apply GoFV.Proof.Rules.opVal_mono
        refine refinesList_idx (by simp) fun j h1 h2 => ?_
        simp only [Array.getElem_toList, Array.getElem_set]
        split
        · rename_i hij; subst hij
          exact (copyReachW_den hT hr n).trans
            (copyPut_den hx hi hr hC hT n src (copyReachW_closed hC hr
              (hargs _ (Array.getElem_mem hi))))
        · exact copyPut_den hx hi hr hC hT n _ (hargs _ (Array.getElem_mem _))
      · have hkeep : (copyPut M v x i src hi).get? y = some m := by
          rw [copyPut_get]; simp [hyv, hm]
        rw [den_succ_term hm hop, den_succ_term hkeep hop]
        exact retype_mono _ (GoFV.Proof.Rules.opVal_mono _ _ _ _ _ (refinesList_map fun a ha =>
          copyPut_den hx hi hr hC hT n a (hargs a (Array.mem_toList_iff.1 ha))))
    · have ht' : ¬ IsTerm (copyPut M v x i src hi).get? y := fun h =>
        ht ((copyPut_isTerm hx hi y).1 h)
      rw [den_succ_atom ht, den_succ_atom ht']; exact Sem.Refines.refl _

end CopyArg

theorem set_getElem! {xs : Array ID} {i j : Nat} {w : ID} (h : i < xs.size) (hj : j < xs.size) :
    (xs.set i w h)[j]! = if i = j then w else xs[j]! := by
  rw [getElem!_pos (xs.set i w h) j (by simpa using hj), getElem!_pos xs j hj, Array.getElem_set]

/-! ## The replay invariant -/

/-- What holds along the replay from the definitions `D₀` and a closed set `C₀`: the current
definitions `M` with a set `C ⊇ C₀` closed under arguments; refining denotations of `C₀`; the
atoms of `D₀` with arguments in `C₀` keep being atoms with refining arguments. -/
structure ReplayInv (tabs : Tables) (D₀ : ID → Option Value) (C₀ : ID → Prop) (M : Defs)
    (C : ID → Prop) : Prop where
  closed : DefClosed M C
  sub : ∀ y, C₀ y → C y
  typed : ∀ ρ, Term.Typed D₀ tabs ρ → Term.Typed M.get? tabs ρ
  denRef : ∀ y, C₀ y → ∀ n, ∃ m, ∀ ρ, Term.Typed D₀ tabs ρ →
    Sem.Refines (den D₀ tabs ρ n y) (den M.get? tabs ρ m y)
  atoms : ∀ y a, D₀ y = some a → termOp a.op = false → (∀ b ∈ a.args, C₀ b) →
    ∃ a', M.get? y = some a' ∧ termOp a'.op = false ∧ a'.args.size = a.args.size ∧
      ∀ i < a.args.size, C a'.args[i]! ∧ ∀ n, ∃ m, ∀ ρ, Term.Typed D₀ tabs ρ →
        Sem.Refines (den D₀ tabs ρ n a.args[i]!) (den M.get? tabs ρ m a'.args[i]!)

theorem ReplayInv.init {tabs : Tables} {M : Defs} {C₀ : ID → Prop} (hC : DefClosed M C₀) :
    ReplayInv tabs M.get? C₀ M C₀ where
  closed := hC
  sub := fun _ h => h
  typed := fun _ h => h
  denRef := fun _ _ n => ⟨n, fun _ _ => Sem.Refines.refl _⟩
  atoms := fun y a hy ha hargs => ⟨a, hy, ha, rfl, fun i hi =>
    ⟨hargs _ (by rw [getElem!_pos a.args i hi]; exact Array.getElem_mem hi),
      fun n => ⟨n, fun _ _ => Sem.Refines.refl _⟩⟩⟩

section Inv

variable {tabs : Tables} {D₀ : ID → Option Value} {C₀ : ID → Prop} {M : Defs} {C : ID → Prop}

/-- Compose a refinement from `D₀` with one step `M → M'`. -/
theorem den_compose {M' : Defs} {y y' : ID} {g : Nat → Nat}
    (h1 : ∀ n, ∃ m, ∀ ρ, Term.Typed D₀ tabs ρ →
      Sem.Refines (den D₀ tabs ρ n y) (den M.get? tabs ρ m y'))
    (hty : ∀ ρ, Term.Typed D₀ tabs ρ → Term.Typed M.get? tabs ρ)
    (h2 : ∀ ρ, Term.Typed M.get? tabs ρ → ∀ n,
      Sem.Refines (den M.get? tabs ρ n y') (den M'.get? tabs ρ (g n) y')) :
    ∀ n, ∃ m, ∀ ρ, Term.Typed D₀ tabs ρ →
      Sem.Refines (den D₀ tabs ρ n y) (den M'.get? tabs ρ m y') := by
  intro n
  obtain ⟨m, hm⟩ := h1 n
  exact ⟨g m, fun ρ hρ => (hm ρ hρ).trans (h2 ρ (hty ρ hρ) m)⟩

theorem ReplayInv.rule {r : Rule} {v : ID} {defs : List Value} (hI : ReplayInv tabs D₀ C₀ M C)
    (hs : GoFV.Proof.Rules.Rule.SoundTop r) (F : RuleFacts tabs M r v defs) :
    ReplayInv tabs D₀ C₀ (putAll M defs) (fun y => C y ∨ (C v ∧ y ∈ defIds defs)) where
  closed := F.closed hI.closed
  sub := fun y h => .inl (hI.sub y h)
  typed := fun ρ h => F.typed (hI.typed ρ h)
  denRef := fun y hy => den_compose (hI.denRef y hy) hI.typed
    fun ρ hρ n => F.step hs hI.closed hρ n y (hI.sub y hy)
  atoms := fun y a hy ha hargs => by
    obtain ⟨a', ha', hat, hsz, hrest⟩ := hI.atoms y a hy ha hargs
    refine ⟨a', F.keepAtom ha' hat, hat, hsz, fun i hi => ⟨.inl (hrest i hi).1, ?_⟩⟩
    exact den_compose (hrest i hi).2 hI.typed
      fun ρ hρ n => F.step hs hI.closed hρ n _ (hrest i hi).1

theorem ReplayInv.copy {v : ID} {x : Value} {i : Nat} {src : ID} (hI : ReplayInv tabs D₀ C₀ M C)
    (hx : M.get? v = some x) (hi : i < x.args.size)
    (hr : copyReachW tabs M M.size x.args[i] src = true) :
    ReplayInv tabs D₀ C₀ (copyPut M v x i src hi) C where
  closed := copyPut_closed hx hi hr hI.closed
  sub := hI.sub
  typed := fun ρ h => copyPut_typed hx hi (hI.typed ρ h)
  denRef := fun y hy => den_compose (hI.denRef y hy) hI.typed
    fun ρ hρ n => copyPut_den hx hi hr hI.closed hρ n y (hI.sub y hy)
  atoms := fun y a hy ha hargs => by
    obtain ⟨a', ha', hat, hsz, hrest⟩ := hI.atoms y a hy ha hargs
    have hstep : ∀ z, C z → ∀ ρ, Term.Typed M.get? tabs ρ → ∀ n,
        Sem.Refines (den M.get? tabs ρ n z) (den (copyPut M v x i src hi).get? tabs ρ n z) :=
      fun z hz ρ hρ n => copyPut_den hx hi hr hI.closed hρ n z hz
    by_cases hyv : y = v
    · rw [hyv] at ha'; rw [hx] at ha'; cases ha'
      refine ⟨{ x with args := x.args.set i src hi }, by rw [copyPut_get]; simp [hyv], hat,
        by simpa using hsz, fun j hj => ?_⟩
      have hj' : j < x.args.size := hsz ▸ hj
      simp only [set_getElem! hi hj']
      split
      · rename_i hij; subst hij
        have hold := (hrest i hj).1
        rw [getElem!_pos x.args i hi] at hold
        have hsrc := copyReachW_closed hI.closed hr hold
        refine ⟨hsrc, ?_⟩
        have h1 := (hrest i hj).2
        rw [getElem!_pos x.args i hi] at h1
        intro n
        obtain ⟨m, hm⟩ := h1 n
        exact ⟨m, fun ρ hρ => (hm ρ hρ).trans ((copyReachW_den (hI.typed ρ hρ) hr m).trans
          (hstep src hsrc ρ (hI.typed ρ hρ) m))⟩
      · exact ⟨(hrest j hj).1, den_compose (hrest j hj).2 hI.typed
          fun ρ hρ n => hstep _ (hrest j hj).1 ρ hρ n⟩
    · refine ⟨a', by rw [copyPut_get]; simp [hyv, ha'], hat, hsz, fun j hj =>
        ⟨(hrest j hj).1, den_compose (hrest j hj).2 hI.typed
          fun ρ hρ n => hstep _ (hrest j hj).1 ρ hρ n⟩⟩

end Inv

end GoFV.Proof.Pass.Rewrite
