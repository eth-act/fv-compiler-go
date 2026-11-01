import GoFV.Proof.Pass.RewriteTermDen
import GoFV.Proof.Rules.Comm

/-!
# Pattern matches of the rewrite validator (issue #113)

`MatchOK M I q p w`: the instance `I` maps position `p` to `w` and, at every op node of `q`, the
definition of the matched value in `M` is a term node of the pattern's op whose arguments
(possibly the first two swapped, only at commutative ops) are matched by the argument patterns.
`matchPat_ok`: a successful `matchPat` gives it, with pairwise distinct positions, so
`Inst.at` reads the matched values (`inst_at`).

`den_le_patDen`, `patDen_le_den`: the denotation of the matched value bounds the pattern's
denotation `Pat.denT` from below and above when the leaves are bounded accordingly.
-/

namespace GoFV.Proof.Pass.Rewrite

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Opt.RewriteCheck GoFV.Proof.Term GoFV.Proof.AtomSim
open GoFV.Proof.Rules (Path PEnv Pat.denT Pat.densT)

mutual
/-- `I` is a match of `q` at `p` on value `w` in `M`. -/
def MatchOK (M : Defs) (I : Inst) : Pat → Path → ID → Prop
  | .op o _ _ _ _ _ args _, p, w => (p, w) ∈ I ∧ ∃ x, M.get? w = some x ∧ x.op = o ∧
      termOp o = true ∧ ∃ ids : List ID,
        (ids = x.args.toList ∨ (o ∈ commOps ∧ ids = swap01 x.args.toList)) ∧
        MatchOKs M I args p 0 ids
  | _, p, w => (p, w) ∈ I
/-- `I` is a match of the argument patterns `i, i+1, …` of the node at `p` on `ids`. -/
def MatchOKs (M : Defs) (I : Inst) : List Pat → Path → Nat → List ID → Prop
  | [], _, _, [] => True
  | q :: qs, p, i, a :: as => MatchOK M I q (i :: p) a ∧ MatchOKs M I qs p (i + 1) as
  | _, _, _, _ => False
end

theorem MatchOK.mem {M : Defs} {I : Inst} {q : Pat} {p : Path} {w : ID} (h : MatchOK M I q p w) :
    (p, w) ∈ I := by
  cases q <;> simp only [MatchOK] at h <;> first | exact h | exact h.1

mutual
theorem MatchOK.mono {M : Defs} {I J : Inst} (hIJ : ∀ a ∈ I, a ∈ J) :
    ∀ {q : Pat} {p : Path} {w : ID}, MatchOK M I q p w → MatchOK M J q p w
  | .op _ _ _ _ _ _ _ _, _, _, ⟨hm, x, hx, ho, ht, ids, hids, hs⟩ =>
    ⟨hIJ _ hm, x, hx, ho, ht, ids, hids, MatchOKs.mono hIJ hs⟩
  | .wild, _, _, h => hIJ _ h
  | .bind _, _, _, h => hIJ _ h
  | .same _, _, _, h => hIJ _ h
theorem MatchOKs.mono {M : Defs} {I J : Inst} (hIJ : ∀ a ∈ I, a ∈ J) :
    ∀ {qs : List Pat} {p : Path} {i : Nat} {ids : List ID}, MatchOKs M I qs p i ids →
      MatchOKs M J qs p i ids
  | [], _, _, [], _ => trivial
  | _ :: _, _, _, _ :: _, ⟨h1, h2⟩ => ⟨MatchOK.mono hIJ h1, MatchOKs.mono hIJ h2⟩
  | [], _, _, _ :: _, h => h.elim
  | _ :: _, _, _, [], h => h.elim
end

/-! ## `matchPat` -/

theorem append_cons_ne {l : List Nat} {i : Nat} {p : Path} : l ++ i :: p ≠ p := by
  intro h
  have := congrArg List.length h
  simp at this
  omega

theorem append_cons_inj {l l' : List Nat} {i j : Nat} {p : Path} (h : l ++ i :: p = l' ++ j :: p) :
    i = j := by
  have h' : (l ++ [i]) ++ p = (l' ++ [j]) ++ p := by simpa using h
  have := congrArg List.getLast? (List.append_cancel_right h')
  simpa using this

/-- Keys of a match at `p` extend `p`. -/
def KeysAt (I : Inst) (p : Path) : Prop := ∀ k ∈ I.map Prod.fst, ∃ l, k = l ++ p

/-- Keys of the matches of argument patterns `i, i+1, …` of the node at `p`. -/
def KeysFrom (I : Inst) (p : Path) (i : Nat) : Prop :=
  ∀ k ∈ I.map Prod.fst, ∃ l j, i ≤ j ∧ k = l ++ j :: p

theorem matchPat_op {M : Defs} {o : Op} {nm : Option Nat} {ty ai ax : GoFV.Rules.Field} {ar : Arity}
    {args : List Pat} {comm : Bool} {p : Path} {w : ID} {sw sw' : List Bool} {I : Inst}
    (h : matchPat M (.op o nm ty ai ax ar args comm) p w sw = some (I, sw')) :
    ∃ x, M.get? w = some x ∧ x.op = o ∧ termOp o = true ∧ ∃ ids sw1 J,
      (ids = x.args.toList ∨ (o ∈ commOps ∧ ids = swap01 x.args.toList)) ∧
      matchPats M args p 0 ids sw1 = some (J, sw') ∧ I = (p, w) :: J := by
  cases ar <;> simp only [matchPat, Bool.not_true, Bool.not_false, Bool.or_false, Bool.or_true,
      ↓reduceIte] at h
  all_goals
    split at h
    · cases h
    · rename_i x hx
      first
      | cases h
      | (split at h
         · cases h
         · rename_i hc
           have hop : x.op = o := Classical.byContradiction fun hne => hc (by simp [hne])
           have ht : termOp o = true := Classical.byContradiction fun hne => hc (by simp [hne])
           refine ⟨x, hx, hop, ht, ?_⟩
           split at h
           · cases h
           · rename_i I0 sw0 heq
             cases h
             refine ⟨_, _, I0, ?_, heq, rfl⟩
             rcases comm with _ | _
             · simp only [Bool.false_eq_true, ↓reduceIte]
               first | exact .inl rfl | exact .inl trivial
             · cases sw with
               | nil => first | exact .inl rfl | exact .inl trivial
               | cons c sw2 =>
                 simp only [↓reduceIte]
                 by_cases hcc : (c && commOps.contains o) = true
                 · simp only [hcc, ↓reduceIte]
                   simp only [Bool.and_eq_true] at hcc
                   exact .inr ⟨List.contains_iff_mem.1 hcc.2, by first | rfl | trivial⟩
                 · simp only [hcc, Bool.false_eq_true, ↓reduceIte]
                   first | exact .inl rfl | exact .inl trivial)

mutual
theorem matchPat_ok {M : Defs} :
    ∀ {q : Pat} {p : Path} {w : ID} {sw sw' : List Bool} {I : Inst},
      matchPat M q p w sw = some (I, sw') →
        MatchOK M I q p w ∧ KeysAt I p ∧ (I.map Prod.fst).Nodup ∧ I.head? = some (p, w)
  | .op o nm ty ai ax ar args comm, p, w, sw, sw', I, h => by
    obtain ⟨x, hx, hop, ht, ids, sw1, J, hids, hJ, rfl⟩ := matchPat_op h
    obtain ⟨hm, hk, hn⟩ := matchPats_ok hJ
    refine ⟨⟨List.mem_cons_self, x, hx, hop, ht, ids, hids,
      MatchOKs.mono (fun a ha => List.mem_cons_of_mem _ ha) hm⟩, ?_, ?_, rfl⟩
    · intro k hk'
      simp only [List.map_cons, List.mem_cons] at hk'
      rcases hk' with rfl | hk'
      · exact ⟨[], rfl⟩
      · obtain ⟨l, j, _, rfl⟩ := hk k hk'
        exact ⟨l ++ [j], by simp⟩
    · simp only [List.map_cons, List.nodup_cons]
      refine ⟨fun hp => ?_, hn⟩
      obtain ⟨l, j, _, hl⟩ := hk p hp
      exact append_cons_ne hl.symm
  | .wild, p, w, sw, sw', I, h => by
    simp only [matchPat, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    exact ⟨List.mem_singleton_self _, fun k hk => ⟨[], by simpa using hk⟩, by simp, rfl⟩
  | .bind _, p, w, sw, sw', I, h => by
    simp only [matchPat, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    exact ⟨List.mem_singleton_self _, fun k hk => ⟨[], by simpa using hk⟩, by simp, rfl⟩
  | .same _, p, w, sw, sw', I, h => by
    simp only [matchPat, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    exact ⟨List.mem_singleton_self _, fun k hk => ⟨[], by simpa using hk⟩, by simp, rfl⟩
theorem matchPats_ok {M : Defs} :
    ∀ {qs : List Pat} {p : Path} {i : Nat} {ids : List ID} {sw sw' : List Bool} {J : Inst},
      matchPats M qs p i ids sw = some (J, sw') →
        MatchOKs M J qs p i ids ∧ KeysFrom J p i ∧ (J.map Prod.fst).Nodup
  | [], p, i, [], sw, sw', J, h => by
    simp only [matchPats, Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -⟩ := h
    exact ⟨trivial, by simp [KeysFrom], by simp⟩
  | q :: qs, p, i, a :: as, sw, sw', J, h => by
    simp only [matchPats] at h
    split at h
    · cases h
    · rename_i I1 sw1 h1
      split at h
      · cases h
      · rename_i J2 sw2 h2
        cases h
        obtain ⟨m1, k1, n1, -⟩ := matchPat_ok h1
        obtain ⟨m2, k2, n2⟩ := matchPats_ok h2
        refine ⟨⟨MatchOK.mono (fun x hx => List.mem_append_left _ hx) m1,
          MatchOKs.mono (fun x hx => List.mem_append_right _ hx) m2⟩, ?_, ?_⟩
        · intro k hk
          simp only [List.map_append, List.mem_append] at hk
          rcases hk with hk | hk
          · obtain ⟨l, rfl⟩ := k1 k hk
            exact ⟨l, i, Nat.le_refl _, by simp⟩
          · obtain ⟨l, j, hj, rfl⟩ := k2 k hk
            exact ⟨l, j, by omega, rfl⟩
        · rw [List.map_append, List.nodup_append]
          refine ⟨n1, n2, fun a ha b hb hab => ?_⟩
          subst hab
          obtain ⟨l, rfl⟩ := k1 a ha
          obtain ⟨l', j, hj, hl⟩ := k2 _ hb
          have := append_cons_inj (by simpa using hl)
          omega
  | [], _, _, _ :: _, _, _, _, h => by simp [matchPats] at h
  | _ :: _, _, _, [], _, _, _, h => by simp [matchPats] at h
end

/-- With distinct positions, `Inst.at` reads a matched position. -/
theorem inst_at : ∀ {I : Inst} {p : Path} {w : ID}, (p, w) ∈ I → (I.map Prod.fst).Nodup →
    I.at p = w
  | (k, b) :: I, p, w, hm, hn => by
    simp only [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 hm with h | h
    · cases h; simp [Inst.at, List.lookup]
    · have hk : k ≠ p := fun hk => hn.1 (hk ▸ List.mem_map_of_mem (f := Prod.fst) h)
      have := inst_at h hn.2
      simp only [Inst.at, List.lookup] at this ⊢
      have : (p == k) = false := by simpa using fun h => hk h.symm
      simp only [this]
      assumption

/-! ## Commutative ops -/

theorem commOps_eq : commOps = GoFV.Proof.Rules.commOpsP1 := rfl

theorem map_swap01 {α β : Type} (f : α → β) : ∀ l : List α, (swap01 l).map f = swap01 (l.map f)
  | _ :: _ :: _ => rfl
  | [] => rfl
  | [_] => rfl

theorem evalPure_swap {o : Op} (ho : o ∈ commOps) (t : Ty) (a : Int64) (x : Option AuxRef) :
    ∀ vs : List Val, evalPure o t a x (swap01 vs) = evalPure o t a x vs
  | p :: q :: rest => (GoFV.Proof.Rules.commOpsP1_sound o (commOps_eq ▸ ho) t a x p q rest).symm
  | [] => rfl
  | [_] => rfl

theorem frameOp_of_comm {o : Op} (ho : o ∈ commOps) : GoFV.Proof.Rules.frameOp o = false := by
  have := List.all_eq_true.1
    (show commOps.all (fun o => !GoFV.Proof.Rules.frameOp o) = true by decide) o ho
  simpa using this

theorem opVal_ids {tabs : Tables} {o : Op} {ids l : List ID}
    (h : ids = l ∨ (o ∈ commOps ∧ ids = swap01 l)) (t : Ty) (a : Int64) (x : Option AuxRef)
    (f : ID → Val) :
    GoFV.Proof.Rules.opVal tabs o t a x (ids.map f) = GoFV.Proof.Rules.opVal tabs o t a x (l.map f) := by
  rcases h with rfl | ⟨ho, rfl⟩
  · rfl
  · rw [GoFV.Proof.Rules.opVal_pure (frameOp_of_comm ho), GoFV.Proof.Rules.opVal_pure (frameOp_of_comm ho),
      map_swap01, evalPure_swap ho]

/-! ## Denotation bounds -/

section Bounds

variable {M : Defs} {I : Inst} {tabs : Tables} {e : PEnv}

/-- The instance's node fields are those of the matched definitions. -/
def FieldsOK (M : Defs) (I : Inst) (tabs : Tables) (e : PEnv) : Prop :=
  ∀ p w x, (p, w) ∈ I → M.get? w = some x →
    e.ty p = tabs.ty x.type ∧ e.auxInt p = x.auxInt ∧ e.aux p = x.aux

/-- Pattern node: an op. -/
def isOpPat : Pat → Bool
  | .op .. => true
  | _ => false

mutual
/-- **Lower bound**: the matched value's denotation refines the pattern's, when the leaves'
denotations (at fuel `≤ n`) refine the instance's leaves. -/
theorem den_le_patDen {ρ : ID → Val} {n : Nat} (hF : FieldsOK M I tabs e)
    (hleaf : ∀ p w, (p, w) ∈ I → ∀ k ≤ n, Sem.Refines (den M.get? tabs ρ k w) (e.leaf p)) :
    ∀ (q : Pat) (p : Path) (w : ID) (k : Nat), MatchOK M I q p w → k ≤ n + 1 →
      (k ≤ n ∨ isOpPat q = true) → Sem.Refines (den M.get? tabs ρ k w) (Pat.denT tabs e p q)
  | .op o nm ty ai ax ar args comm, p, w, k, hm, hk, _ => by
    obtain ⟨hmem, x, hx, hop, ht, ids, hids, hs⟩ := hm
    cases k with
    | zero => exact .poison _
    | succ j =>
      rw [den_succ_term hx (hop ▸ ht)]
      obtain ⟨h1, h2, h3⟩ := hF p w x hmem hx
      simp only [GoFV.Proof.Rules.Pat.denT, h1, h2, h3, hop]
      apply retype_mono
      rw [← opVal_ids hids]
      exact GoFV.Proof.Rules.opVal_mono _ _ _ _ _ (dens_le hF hleaf args p 0 ids j hs (by omega))
  | .wild, p, w, k, hm, hk, hk' => by
    simp only [GoFV.Proof.Rules.Pat.denT]
    exact hleaf p w hm k (by simpa [isOpPat] using hk')
  | .bind _, p, w, k, hm, hk, hk' => by
    simp only [GoFV.Proof.Rules.Pat.denT]
    exact hleaf p w hm k (by simpa [isOpPat] using hk')
  | .same _, p, w, k, hm, hk, hk' => by
    simp only [GoFV.Proof.Rules.Pat.denT]
    exact hleaf p w hm k (by simpa [isOpPat] using hk')
theorem dens_le {ρ : ID → Val} {n : Nat} (hF : FieldsOK M I tabs e)
    (hleaf : ∀ p w, (p, w) ∈ I → ∀ k ≤ n, Sem.Refines (den M.get? tabs ρ k w) (e.leaf p)) :
    ∀ (qs : List Pat) (p : Path) (i : Nat) (ids : List ID) (j : Nat), MatchOKs M I qs p i ids →
      j ≤ n → RefinesList (ids.map (den M.get? tabs ρ j)) (Pat.densT tabs e p i qs)
  | [], _, _, [], _, _, _ => .nil
  | q :: qs, p, i, a :: as, j, ⟨h1, h2⟩, hj =>
    .cons (den_le_patDen hF hleaf q (i :: p) a j h1 (by omega) (.inl hj))
      (dens_le hF hleaf qs p (i + 1) as j h2 hj)
  | [], _, _, _ :: _, _, h, _ => h.elim
  | _ :: _, _, _, [], _, h, _ => h.elim
end

mutual
/-- The size of a pattern (its op nodes). -/
def Pat.sz : Pat → Nat
  | .op _ _ _ _ _ _ args _ => Pat.szs args + 1
  | _ => 0
def Pat.szs : List Pat → Nat
  | [] => 0
  | q :: qs => Pat.sz q + Pat.szs qs
end

mutual
/-- **Upper bound**: below the top, the pattern's denotation is refined by the matched value's
in `D'`, which keeps the matched definitions, when the leaves are refined by their values'
denotations at fuel `B`. -/
theorem patDen_le_den {D' : ID → Option Value} {ρ : ID → Val} {B : Nat}
    (hF : FieldsOK M I tabs e)
    (hD : ∀ p w x, (p, w) ∈ I → p ≠ [] → M.get? w = some x → D' w = some x)
    (hleaf : ∀ p w, (p, w) ∈ I → Sem.Refines (e.leaf p) (den D' tabs ρ B w)) :
    ∀ (q : Pat) (p : Path) (w : ID) (m : Nat), MatchOK M I q p w → p ≠ [] → B + Pat.sz q ≤ m →
      Sem.Refines (Pat.denT tabs e p q) (den D' tabs ρ m w)
  | .op o nm ty ai ax ar args comm, p, w, m, hm, hp, hle => by
    obtain ⟨hmem, x, hx, hop, ht, ids, hids, hs⟩ := hm
    simp only [Pat.sz] at hle
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [den_succ_term (hD p w x hmem hp hx) (hop ▸ ht)]
    obtain ⟨h1, h2, h3⟩ := hF p w x hmem hx
    simp only [GoFV.Proof.Rules.Pat.denT, h1, h2, h3, hop]
    apply retype_mono
    rw [← opVal_ids hids]
    exact GoFV.Proof.Rules.opVal_mono _ _ _ _ _ (dens_le_den hF hD hleaf args p 0 ids j hs (by omega))
  | .wild, p, w, m, hm, _, hle => by
    simp only [GoFV.Proof.Rules.Pat.denT]
    exact Sem.Refines.trans (hleaf p w hm) (den_fuel_mono _ _ _ _ _ _ (by simpa [Pat.sz] using hle))
  | .bind _, p, w, m, hm, _, hle => by
    simp only [GoFV.Proof.Rules.Pat.denT]
    exact Sem.Refines.trans (hleaf p w hm) (den_fuel_mono _ _ _ _ _ _ (by simpa [Pat.sz] using hle))
  | .same _, p, w, m, hm, _, hle => by
    simp only [GoFV.Proof.Rules.Pat.denT]
    exact Sem.Refines.trans (hleaf p w hm) (den_fuel_mono _ _ _ _ _ _ (by simpa [Pat.sz] using hle))
theorem dens_le_den {D' : ID → Option Value} {ρ : ID → Val} {B : Nat}
    (hF : FieldsOK M I tabs e)
    (hD : ∀ p w x, (p, w) ∈ I → p ≠ [] → M.get? w = some x → D' w = some x)
    (hleaf : ∀ p w, (p, w) ∈ I → Sem.Refines (e.leaf p) (den D' tabs ρ B w)) :
    ∀ (qs : List Pat) (p : Path) (i : Nat) (ids : List ID) (j : Nat), MatchOKs M I qs p i ids →
      B + Pat.szs qs ≤ j →
      RefinesList (Pat.densT tabs e p i qs) (ids.map (den D' tabs ρ j))
  | [], _, _, [], _, _, _ => .nil
  | q :: qs, p, i, a :: as, j, ⟨h1, h2⟩, hj => by
    simp only [Pat.szs] at hj
    exact .cons (patDen_le_den hF hD hleaf q (i :: p) a j h1 (List.cons_ne_nil _ _) (by omega))
      (dens_le_den hF hD hleaf qs p (i + 1) as j h2 (by omega))
  | [], _, _, _ :: _, _, h, _ => h.elim
  | _ :: _, _, _, [], _, h, _ => h.elim
end

end Bounds

end GoFV.Proof.Pass.Rewrite
