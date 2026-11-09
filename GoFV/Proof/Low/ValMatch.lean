import GoFV.Proof.Low.DenL
import GoFV.Proof.Pass.RewriteTerm

variable [GoFV.SSA.Sem.Addrs]

/-!
# Pattern matches of the lowering validator (issue #385)

The lowered counterparts of `GoFV/Proof/Pass/RewriteTermMatch.lean` and `RewriteTermPat.lean`
for `GoFV.Opt.LowerCheck.matchPatL` (a swapped pattern matched argument for argument, every op
node a term `termVL`) and the lowered denotation `GoFV.Proof.Low.Pat.denL` (in lowered mode,
`denL true`): `MatchOKL`, `matchPatL_ok`, the denotation bounds `den_le_patDenL` /
`patDen_le_denL`, and the facts about `Pat.bindsL` (`sigmaL_erase`, `bindsL_good`,
`sigmaL_leaf`) and `leavesOK` (`typed_ofL`). The positions where the upper bound and the bound
values are asked for are those of a predicate `Q` closed under argument positions (`p ≠ []` for a
rule event, which redefines the top; anything for a block-rule event).
-/

namespace GoFV.Proof.Low.Val

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Opt.RewriteCheck GoFV.Opt.LowerCheck GoFV.Proof.Term
open GoFV.Proof.Low
open GoFV.Proof.Pass.Rewrite (KeysAt KeysFrom append_cons_ne append_cons_inj inst_at Good
  good_of_flat lookup_mem lookup_map auxIntDV_flat ArgClosed isOpPat)
open GoFV.Proof.Rules (Path PEnv DV)

theorem auxIntDVL_flat (aty : AuxType) (i : Int64) : (auxIntDVL aty i).flat = true := by
  unfold auxIntDVL; split
  · unfold ccDV; split <;> rfl
  · rfl
  · exact auxIntDV_flat _ _

/-- `denL` in lowered mode at a term node. -/
theorem denT_succ {D : ID → Option Value} {tabs : Tables} {ρ : ID → Val} {n : Nat} {x : ID}
    {v : Value} (hx : D x = some v) (ht : termVL tabs v = true) :
    denL true D tabs ρ (n + 1) x = (opValL tabs v.op (shpL tabs v.type) v.auxInt v.aux
      (v.args.toList.map (denL true D tabs ρ n))).retypeL (shpL tabs v.type) := by
  rw [denL_succ_term hx ht]; rfl

/-! ## Matches -/

mutual
/-- `I` is a match of `q` at `p` on value `w` in `M`: op nodes are terms of the pattern's op whose
arguments are matched in order. -/
def MatchOKL (tabs : Tables) (M : Defs) (I : Inst) : Pat → Path → ID → Prop
  | .op o _ _ _ _ _ args _, p, w => (p, w) ∈ I ∧ ∃ x, M.get? w = some x ∧ x.op = o ∧
      termVL tabs x = true ∧ MatchOKsL tabs M I args p 0 x.args.toList
  | _, p, w => (p, w) ∈ I
/-- `I` is a match of the argument patterns `i, i+1, …` of the node at `p` on `ids`. -/
def MatchOKsL (tabs : Tables) (M : Defs) (I : Inst) : List Pat → Path → Nat → List ID → Prop
  | [], _, _, [] => True
  | q :: qs, p, i, a :: as => MatchOKL tabs M I q (i :: p) a ∧ MatchOKsL tabs M I qs p (i + 1) as
  | _, _, _, _ => False
end

theorem MatchOKL.mem {tabs : Tables} {M : Defs} {I : Inst} {q : Pat} {p : Path} {w : ID}
    (h : MatchOKL tabs M I q p w) : (p, w) ∈ I := by
  cases q <;> simp only [MatchOKL] at h <;> first | exact h | exact h.1

mutual
theorem MatchOKL.mono {tabs : Tables} {M : Defs} {I J : Inst} (hIJ : ∀ a ∈ I, a ∈ J) :
    ∀ {q : Pat} {p : Path} {w : ID}, MatchOKL tabs M I q p w → MatchOKL tabs M J q p w
  | .op _ _ _ _ _ _ _ _, _, _, ⟨hm, x, hx, ho, ht, hs⟩ =>
    ⟨hIJ _ hm, x, hx, ho, ht, MatchOKsL.mono hIJ hs⟩
  | .wild, _, _, h => hIJ _ h
  | .bind _, _, _, h => hIJ _ h
  | .same _, _, _, h => hIJ _ h
theorem MatchOKsL.mono {tabs : Tables} {M : Defs} {I J : Inst} (hIJ : ∀ a ∈ I, a ∈ J) :
    ∀ {qs : List Pat} {p : Path} {i : Nat} {ids : List ID}, MatchOKsL tabs M I qs p i ids →
      MatchOKsL tabs M J qs p i ids
  | [], _, _, [], _ => trivial
  | _ :: _, _, _, _ :: _, ⟨h1, h2⟩ => ⟨MatchOKL.mono hIJ h1, MatchOKsL.mono hIJ h2⟩
  | [], _, _, _ :: _, h => h.elim
  | _ :: _, _, _, [], h => h.elim
end

theorem matchPatL_op {tabs : Tables} {M : Defs} {o : Op} {nm : Option Nat}
    {ty ai ax : GoFV.Rules.Field} {ar : Arity} {args : List Pat} {comm : Bool} {p : Path} {w : ID}
    {I : Inst} (h : matchPatL tabs M (.op o nm ty ai ax ar args comm) p w = some I) :
    ∃ x, M.get? w = some x ∧ x.op = o ∧ termVL tabs x = true ∧ ∃ J,
      matchPatsL tabs M args p 0 x.args.toList = some J ∧ I = (p, w) :: J := by
  cases ar <;> simp only [matchPatL, Bool.not_true, Bool.not_false, Bool.or_false, Bool.or_true,
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
           have ht : termVL tabs x = true :=
             Classical.byContradiction fun hne => hc (by simp [hne])
           refine ⟨x, hx, hop, ht, ?_⟩
           split at h
           · cases h
           · rename_i J hJ
             cases h
             exact ⟨J, hJ, rfl⟩)

mutual
theorem matchPatL_ok {tabs : Tables} {M : Defs} :
    ∀ {q : Pat} {p : Path} {w : ID} {I : Inst}, matchPatL tabs M q p w = some I →
      MatchOKL tabs M I q p w ∧ KeysAt I p ∧ (I.map Prod.fst).Nodup ∧ I.head? = some (p, w)
  | .op o nm ty ai ax ar args comm, p, w, I, h => by
    obtain ⟨x, hx, hop, ht, J, hJ, rfl⟩ := matchPatL_op h
    obtain ⟨hm, hk, hn⟩ := matchPatsL_ok hJ
    refine ⟨⟨List.mem_cons_self, x, hx, hop, ht,
      MatchOKsL.mono (fun a ha => List.mem_cons_of_mem _ ha) hm⟩, ?_, ?_, rfl⟩
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
  | .wild, p, w, I, h | .bind _, p, w, I, h | .same _, p, w, I, h => by
    simp only [matchPatL, Option.some.injEq] at h; subst h
    exact ⟨List.mem_singleton_self _, fun k hk => ⟨[], by simpa using hk⟩, by simp, rfl⟩
theorem matchPatsL_ok {tabs : Tables} {M : Defs} :
    ∀ {qs : List Pat} {p : Path} {i : Nat} {ids : List ID} {J : Inst},
      matchPatsL tabs M qs p i ids = some J →
        MatchOKsL tabs M J qs p i ids ∧ KeysFrom J p i ∧ (J.map Prod.fst).Nodup
  | [], p, i, [], J, h => by
    simp only [matchPatsL, Option.some.injEq] at h; subst h
    exact ⟨trivial, by simp [KeysFrom], by simp⟩
  | q :: qs, p, i, a :: as, J, h => by
    simp only [matchPatsL] at h
    split at h
    · cases h
    · rename_i I1 h1
      split at h
      · cases h
      · rename_i J2 h2
        cases h
        obtain ⟨m1, k1, n1, -⟩ := matchPatL_ok h1
        obtain ⟨m2, k2, n2⟩ := matchPatsL_ok h2
        refine ⟨⟨MatchOKL.mono (fun x hx => List.mem_append_left _ hx) m1,
          MatchOKsL.mono (fun x hx => List.mem_append_right _ hx) m2⟩, ?_, ?_⟩
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
  | [], _, _, _ :: _, _, h => by simp [matchPatsL] at h
  | _ :: _, _, _, [], _, h => by simp [matchPatsL] at h
end

mutual
theorem matchPatL_closed {tabs : Tables} {M : Defs} {C : ID → Prop} (hC : ArgClosed M C) :
    ∀ {q : Pat} {p : Path} {w : ID} {I : Inst},
      matchPatL tabs M q p w = some I → C w → ∀ y ∈ I, C y.2
  | .op o nm ty ai ax ar args comm, p, w, I, h, hw => by
    obtain ⟨x, hx, -, -, J, hJ, rfl⟩ := matchPatL_op h
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact hw
    · exact matchPatsL_closed hC hJ (fun a ha => hC w x hw hx a (Array.mem_toList_iff.1 ha)) y hy
  | .wild, p, w, I, h, hw | .bind _, p, w, I, h, hw | .same _, p, w, I, h, hw => by
    simp only [matchPatL, Option.some.injEq] at h; subst h
    intro y hy; simp only [List.mem_singleton] at hy; subst hy; exact hw
theorem matchPatsL_closed {tabs : Tables} {M : Defs} {C : ID → Prop} (hC : ArgClosed M C) :
    ∀ {qs : List Pat} {p : Path} {i : Nat} {ids : List ID} {J : Inst},
      matchPatsL tabs M qs p i ids = some J → (∀ a ∈ ids, C a) → ∀ y ∈ J, C y.2
  | [], p, i, [], J, h, _ => by
    simp only [matchPatsL, Option.some.injEq] at h; subst h
    intro y hy; cases hy
  | q :: qs, p, i, a :: as, J, h, hids => by
    simp only [matchPatsL] at h
    split at h
    · cases h
    · rename_i I1 h1
      split at h
      · cases h
      · rename_i J2 h2
        cases h
        intro y hy
        rcases List.mem_append.1 hy with hy | hy
        · exact matchPatL_closed hC h1 (hids a List.mem_cons_self) y hy
        · exact matchPatsL_closed hC h2 (fun b hb => hids b (List.mem_cons_of_mem _ hb)) y hy
  | [], _, _, _ :: _, _, h, _ => by simp [matchPatsL] at h
  | _ :: _, _, _, [], _, h, _ => by simp [matchPatsL] at h
end

/-! ## Denotation bounds -/

section Bounds

variable {tabs : Tables} {M : Defs} {I : Inst} {e : PEnv}

/-- The instance's node fields are those of the matched definitions, at the lowered shapes. -/
def FieldsOKL (tabs : Tables) (M : Defs) (I : Inst) (e : PEnv) : Prop :=
  ∀ p w x, (p, w) ∈ I → M.get? w = some x →
    e.ty p = shpL tabs x.type ∧ e.auxInt p = x.auxInt ∧ e.aux p = x.aux

mutual
/-- **Lower bound**: the matched value's lowered denotation refines the pattern's, when the
leaves' denotations (at fuel `≤ n`) refine the instance's leaves. -/
theorem den_le_patDenL {ρ : ID → Val} {n : Nat} (hF : FieldsOKL tabs M I e)
    (hleaf : ∀ p w, (p, w) ∈ I → ∀ k ≤ n, Sem.Refines (denL true M.get? tabs ρ k w) (e.leaf p)) :
    ∀ (q : Pat) (p : Path) (w : ID) (k : Nat), MatchOKL tabs M I q p w → k ≤ n + 1 →
      (k ≤ n ∨ isOpPat q = true) → Sem.Refines (denL true M.get? tabs ρ k w) (Pat.denL tabs e p q)
  | .op o nm ty ai ax ar args comm, p, w, k, hm, hk, _ => by
    obtain ⟨hmem, x, hx, hop, ht, hs⟩ := hm
    cases k with
    | zero => exact .poison _
    | succ j =>
      rw [denT_succ hx ht]
      obtain ⟨h1, h2, h3⟩ := hF p w x hmem hx
      simp only [Pat.denL, h1, h2, h3, ← hop]
      exact retypeL_mono _ (opValL_mono_term ht _ (densL_le hF hleaf args p 0 _ j hs (by omega)))
  | .wild, p, w, k, hm, _, hk' | .bind _, p, w, k, hm, _, hk' | .same _, p, w, k, hm, _, hk' => by
    simp only [Pat.denL]
    exact hleaf p w hm k (by simpa [isOpPat] using hk')
theorem densL_le {ρ : ID → Val} {n : Nat} (hF : FieldsOKL tabs M I e)
    (hleaf : ∀ p w, (p, w) ∈ I → ∀ k ≤ n, Sem.Refines (denL true M.get? tabs ρ k w) (e.leaf p)) :
    ∀ (qs : List Pat) (p : Path) (i : Nat) (ids : List ID) (j : Nat), MatchOKsL tabs M I qs p i ids →
      j ≤ n → RefinesList (ids.map (denL true M.get? tabs ρ j)) (Pat.densL tabs e p i qs)
  | [], _, _, [], _, _, _ => .nil
  | q :: qs, p, i, a :: as, j, ⟨h1, h2⟩, hj =>
    .cons (den_le_patDenL hF hleaf q (i :: p) a j h1 (by omega) (.inl hj))
      (densL_le hF hleaf qs p (i + 1) as j h2 hj)
  | [], _, _, _ :: _, _, h, _ => h.elim
  | _ :: _, _, _, [], _, h, _ => h.elim
end

mutual
/-- **Upper bound**: at the positions of `Q`, the pattern's denotation is refined by the matched
value's in `D'`, which keeps the matched definitions there, when the leaves are refined by their
values' denotations at fuel `B`. -/
theorem patDen_le_denL {D' : ID → Option Value} {ρ : ID → Val} {B : Nat} {Q : Path → Prop}
    (hQ : ∀ i p, Q (i :: p)) (hF : FieldsOKL tabs M I e)
    (hD : ∀ p w x, (p, w) ∈ I → Q p → M.get? w = some x → D' w = some x)
    (hleaf : ∀ p w, (p, w) ∈ I → Sem.Refines (e.leaf p) (denL true D' tabs ρ B w)) :
    ∀ (q : Pat) (p : Path) (w : ID) (m : Nat), MatchOKL tabs M I q p w → Q p →
      B + GoFV.Proof.Pass.Rewrite.Pat.sz q ≤ m →
      Sem.Refines (Pat.denL tabs e p q) (denL true D' tabs ρ m w)
  | .op o nm ty ai ax ar args comm, p, w, m, hm, hp, hle => by
    obtain ⟨hmem, x, hx, hop, ht, hs⟩ := hm
    simp only [GoFV.Proof.Pass.Rewrite.Pat.sz] at hle
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [denT_succ (hD p w x hmem hp hx) ht]
    obtain ⟨h1, h2, h3⟩ := hF p w x hmem hx
    simp only [Pat.denL, h1, h2, h3, ← hop]
    exact retypeL_mono _ (opValL_mono_term ht _ (densL_le_denL hQ hF hD hleaf args p 0 _ j hs (by omega)))
  | .wild, p, w, m, hm, _, hle | .bind _, p, w, m, hm, _, hle | .same _, p, w, m, hm, _, hle => by
    simp only [Pat.denL]
    exact (hleaf p w hm).trans (denL_fuel_mono _ _ _ _ _ _ _
      (by simpa [GoFV.Proof.Pass.Rewrite.Pat.sz] using hle))
theorem densL_le_denL {D' : ID → Option Value} {ρ : ID → Val} {B : Nat} {Q : Path → Prop}
    (hQ : ∀ i p, Q (i :: p)) (hF : FieldsOKL tabs M I e)
    (hD : ∀ p w x, (p, w) ∈ I → Q p → M.get? w = some x → D' w = some x)
    (hleaf : ∀ p w, (p, w) ∈ I → Sem.Refines (e.leaf p) (denL true D' tabs ρ B w)) :
    ∀ (qs : List Pat) (p : Path) (i : Nat) (ids : List ID) (j : Nat), MatchOKsL tabs M I qs p i ids →
      B + GoFV.Proof.Pass.Rewrite.Pat.szs qs ≤ j →
      RefinesList (Pat.densL tabs e p i qs) (ids.map (denL true D' tabs ρ j))
  | [], _, _, [], _, _, _ => .nil
  | q :: qs, p, i, a :: as, j, ⟨h1, h2⟩, hj => by
    simp only [GoFV.Proof.Pass.Rewrite.Pat.szs] at hj
    exact .cons (patDen_le_denL hQ hF hD hleaf q (i :: p) a j h1 (hQ i p) (by omega))
      (densL_le_denL hQ hF hD hleaf qs p (i + 1) as j h2 (by omega))
  | [], _, _, _ :: _, _, h, _ => h.elim
  | _ :: _, _, _, [], _, h, _ => h.elim
end

end Bounds

/-! ## Bindings -/

section Binds

variable {e e' : PEnv} {tabs tabs' : Tables}

omit [GoFV.SSA.Sem.Addrs] in
mutual
/-- The bindings of two instances with the same node fields agree up to the values of `DV.val`,
also under two address assignments `A`, `B` (the checker's static instance is evaluated at
`Addrs.fixed`, `LowerCheck.ruleOK1`). -/
theorem bindsL_erase {A B : GoFV.SSA.Sem.Addrs} (hty : e.ty = e'.ty) (hai : e.auxInt = e'.auxInt) :
    ∀ (p : Path) (q : Pat), (@Pat.bindsL A tabs e p q).map (fun a => (a.1, a.2.erase)) =
      (@Pat.bindsL B tabs' e' p q).map (fun a => (a.1, a.2.erase))
  | _, .wild | _, .same _ => rfl
  | _, .bind _ => rfl
  | p, .op o nm ty ai _ _ args _ => by
    simp only [Pat.bindsL, List.map_append]
    rw [bindssL_erase hty hai p 0 args]
    congr 1; congr 1; congr 1
    · cases nm <;> rfl
    · cases ty <;> simp [hty]
    · cases ai <;> simp [hai]
theorem bindssL_erase {A B : GoFV.SSA.Sem.Addrs} (hty : e.ty = e'.ty) (hai : e.auxInt = e'.auxInt) :
    ∀ (p : Path) (i : Nat) (qs : List Pat),
      (@Pat.bindssL A tabs e p i qs).map (fun a => (a.1, a.2.erase)) =
      (@Pat.bindssL B tabs' e' p i qs).map (fun a => (a.1, a.2.erase))
  | _, _, [] => rfl
  | p, i, q :: qs => by
    simp only [Pat.bindssL, List.map_append]
    rw [bindsL_erase hty hai (i :: p) q, bindssL_erase hty hai p (i + 1) qs]
end

omit [GoFV.SSA.Sem.Addrs] in
theorem sigmaL_erase {A B : GoFV.SSA.Sem.Addrs} (hty : e.ty = e'.ty) (hai : e.auxInt = e'.auxInt)
    (pat : Pat) (x : Nat) :
    (@sigmaL A tabs e pat x).erase = (@sigmaL B tabs' e' pat x).erase := by
  have h := congrArg (List.lookup x)
    (bindsL_erase (A := A) (B := B) (tabs := tabs) (tabs' := tabs') hty hai [] pat)
  rw [lookup_map, lookup_map] at h
  simp only [sigmaL]
  cases h1 : (@Pat.bindsL A tabs e [] pat).lookup x <;>
    cases h2 : (@Pat.bindsL B tabs' e' [] pat).lookup x <;>
    simp_all [DV.erase]

end Binds

section Good

variable {tabs : Tables} {M : Defs} {I : Inst} {e : PEnv} {P : Val → Path → Prop} {S : Nat}
  {Q : Path → Prop}

mutual
theorem bindsL_good (hQ : ∀ i p, Q (i :: p))
    (hleafP : ∀ p w, (p, w) ∈ I → Q p → P (e.leaf p) p)
    (hopP : ∀ q p w, MatchOKL tabs M I q p w → Q p → GoFV.Proof.Pass.Rewrite.Pat.sz q ≤ S →
      P (Pat.denL tabs e p q) p) :
    ∀ (q : Pat) (p : Path) (w : ID), MatchOKL tabs M I q p w → Q p →
      GoFV.Proof.Pass.Rewrite.Pat.sz q ≤ S → ∀ y ∈ Pat.bindsL tabs e p q, Good P y.2
  | .wild, _, _, _, _, _, y, hy | .same _, _, _, _, _, _, y, hy => by simp [Pat.bindsL] at hy
  | .bind x, p, w, hm, hp, _, y, hy => by
    simp only [Pat.bindsL, List.mem_singleton] at hy
    subst hy
    exact ⟨fun w' p' h => by
      simp only [DV.val.injEq, Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hleafP _ _ hm hp, fun _ h => by cases h⟩
  | .op o nm ty ai ax ar args cm, p, w, hm, hp, hsz, y, hy => by
    simp only [Pat.bindsL, List.mem_append] at hy
    rcases hy with ((hy | hy) | hy) | hy
    · cases nm with
      | none => simp at hy
      | some x =>
        simp only [List.mem_singleton] at hy; subst hy
        exact ⟨fun w' p' h => by
          simp only [DV.val.injEq, Option.some.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact hopP (.op o (some x) ty ai ax ar args cm) p w hm hp hsz, fun _ h => by cases h⟩
    · cases ty <;> simp at hy
      subst hy; exact good_of_flat rfl
    · cases ai <;> simp at hy
      subst hy; exact good_of_flat (auxIntDVL_flat _ _)
    · obtain ⟨-, x, -, -, -, hs⟩ := hm
      exact bindssL_good hQ hleafP hopP args p 0 _ hs
        (by simp only [GoFV.Proof.Pass.Rewrite.Pat.sz] at hsz; omega) y hy
theorem bindssL_good (hQ : ∀ i p, Q (i :: p))
    (hleafP : ∀ p w, (p, w) ∈ I → Q p → P (e.leaf p) p)
    (hopP : ∀ q p w, MatchOKL tabs M I q p w → Q p → GoFV.Proof.Pass.Rewrite.Pat.sz q ≤ S →
      P (Pat.denL tabs e p q) p) :
    ∀ (qs : List Pat) (p : Path) (i : Nat) (ids : List ID), MatchOKsL tabs M I qs p i ids →
      GoFV.Proof.Pass.Rewrite.Pat.szs qs ≤ S → ∀ y ∈ Pat.bindssL tabs e p i qs, Good P y.2
  | [], _, _, _, _, _, y, hy => by simp [Pat.bindssL] at hy
  | q :: qs, p, i, a :: as, ⟨h1, h2⟩, hsz, y, hy => by
    simp only [Pat.bindssL, List.mem_append] at hy
    simp only [GoFV.Proof.Pass.Rewrite.Pat.szs] at hsz
    rcases hy with hy | hy
    · exact bindsL_good hQ hleafP hopP q (i :: p) a h1 (hQ i p) (by omega) y hy
    · exact bindssL_good hQ hleafP hopP qs p (i + 1) as h2 (by omega) y hy
  | _ :: _, _, _, [], h, _, _, _ => h.elim
end

/-- The variables of a pattern whose top position is in `Q` are good. -/
theorem sigmaL_good (hQ : ∀ i p, Q (i :: p))
    (hleafP : ∀ p w, (p, w) ∈ I → Q p → P (e.leaf p) p)
    (hopP : ∀ q p w, MatchOKL tabs M I q p w → Q p → GoFV.Proof.Pass.Rewrite.Pat.sz q ≤ S →
      P (Pat.denL tabs e p q) p)
    {pat : Pat} {v : ID} (hm : MatchOKL tabs M I pat [] v) (h0 : Q [])
    (hS : GoFV.Proof.Pass.Rewrite.Pat.sz pat ≤ S) (x : Nat) : Good P (sigmaL tabs e pat x) := by
  simp only [sigmaL]
  cases hl : (Pat.bindsL tabs e [] pat).lookup x with
  | none => exact good_of_flat rfl
  | some d => exact bindsL_good hQ hleafP hopP pat [] v hm h0 hS (x, d) (lookup_mem hl)

/-- The variables of a pattern with an unnamed top are good. -/
theorem sigmaL_good_top (hQ : ∀ i p, Q (i :: p))
    (hleafP : ∀ p w, (p, w) ∈ I → Q p → P (e.leaf p) p)
    (hopP : ∀ q p w, MatchOKL tabs M I q p w → Q p → GoFV.Proof.Pass.Rewrite.Pat.sz q ≤ S →
      P (Pat.denL tabs e p q) p)
    {o : Op} {ty ai ax : GoFV.Rules.Field} {ar : GoFV.Rules.Arity} {args : List Pat} {cm : Bool}
    {v : ID} (hm : MatchOKL tabs M I (.op o none ty ai ax ar args cm) [] v)
    (hS : GoFV.Proof.Pass.Rewrite.Pat.sz (.op o none ty ai ax ar args cm) ≤ S) (x : Nat) :
    Good P (sigmaL tabs e (.op o none ty ai ax ar args cm) x) := by
  simp only [sigmaL]
  cases hl : (Pat.bindsL tabs e [] (.op o none ty ai ax ar args cm)).lookup x with
  | none => exact good_of_flat rfl
  | some d =>
    have hy := lookup_mem hl
    simp only [Pat.bindsL, List.mem_append] at hy
    simp only [Option.getD_some]
    rcases hy with ((hy | hy) | hy) | hy
    · simp at hy
    · cases ty <;> simp at hy
      obtain ⟨-, rfl⟩ := hy; exact good_of_flat rfl
    · cases ai <;> simp at hy
      obtain ⟨-, rfl⟩ := hy; exact good_of_flat (auxIntDVL_flat _ _)
    · obtain ⟨-, x, -, -, -, hs⟩ := hm
      exact bindssL_good hQ hleafP hopP args [] 0 _ hs
        (by simp only [GoFV.Proof.Pass.Rewrite.Pat.sz] at hS; omega) _ hy

end Good

section Leaf

variable {e : PEnv} {tabs : Tables}

mutual
theorem bindsL_leaf : ∀ (q : Pat) (p : Path), ∀ y ∈ Pat.bindsL tabs e p q, ∀ w p',
    y.2 = .val w (some p') → y.1 ∉ GoFV.Opt.RewriteCheck.Pat.opNames q → w = e.leaf p'
  | .wild, _, y, hy, _, _, _, _ | .same _, _, y, hy, _, _, _, _ => by simp [Pat.bindsL] at hy
  | .bind x, p, y, hy, w, p', h, _ => by
    simp only [Pat.bindsL, List.mem_singleton] at hy
    subst hy
    simp only [DV.val.injEq, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | .op o nm ty ai _ _ args _, p, y, hy, w, p', h, hn => by
    simp only [Pat.bindsL, List.mem_append] at hy
    rcases hy with ((hy | hy) | hy) | hy
    · cases nm with
      | none => simp at hy
      | some x =>
        simp only [List.mem_singleton] at hy; subst hy
        simp [GoFV.Opt.RewriteCheck.Pat.opNames] at hn
    · cases ty <;> simp at hy
      subst hy; cases h
    · cases ai <;> simp at hy
      subst hy; have := auxIntDVL_flat o.auxType (e.auxInt p); simp only at h; rw [h] at this
      cases this
    · refine bindssL_leaf args p 0 y hy w p' h ?_
      intro hc; apply hn
      simp only [GoFV.Opt.RewriteCheck.Pat.opNames, List.mem_append]; exact .inr hc
theorem bindssL_leaf : ∀ (qs : List Pat) (p : Path) (i : Nat), ∀ y ∈ Pat.bindssL tabs e p i qs,
    ∀ w p', y.2 = .val w (some p') → y.1 ∉ GoFV.Opt.RewriteCheck.Pat.opNamess qs → w = e.leaf p'
  | [], _, _, y, hy, _, _, _, _ => by simp [Pat.bindssL] at hy
  | q :: qs, p, i, y, hy, w, p', h, hn => by
    simp only [Pat.bindssL, List.mem_append] at hy
    simp only [GoFV.Opt.RewriteCheck.Pat.opNamess, List.mem_append, not_or] at hn
    rcases hy with hy | hy
    · exact bindsL_leaf q (i :: p) y hy w p' h hn.1
    · exact bindssL_leaf qs p (i + 1) y hy w p' h hn.2
end

theorem sigmaL_leaf {pat : Pat} {x : Nat} {w : Val} {p' : Path}
    (h : sigmaL tabs e pat x = .val w (some p')) (hn : x ∉ GoFV.Opt.RewriteCheck.Pat.opNames pat) :
    w = e.leaf p' := by
  simp only [sigmaL] at h
  cases hl : (Pat.bindsL tabs e [] pat).lookup x with
  | none => rw [hl] at h; cases h
  | some d =>
    rw [hl] at h
    exact bindsL_leaf pat [] (x, d) (lookup_mem hl) w p' h hn

end Leaf

/-! ## Typed leaves -/

mutual
theorem typed_ofL {M : Defs} {I : Inst} {tabs : Tables} {e : PEnv} {Q : Path → Prop}
    (hQ : ∀ i p, Q (i :: p))
    (hty : ∀ p, e.ty p = ((M.get? (I.at p)).map fun x => shpL tabs x.type).getD .other)
    (hleaf : ∀ p w x, (p, w) ∈ I → Q p → M.get? w = some x →
      (e.leaf p).hasTy (shpL tabs x.type) = true)
    (hn : (I.map Prod.fst).Nodup) :
    ∀ (q : Pat) (p : Path) (w : ID), MatchOKL tabs M I q p w → Q p ∨ isOpPat q = true →
      leavesOK M I p q = true → GoFV.Proof.Rules.Pat.typed e p q
  | .op o _ _ _ _ _ args _, p, w, hm, _, h => by
    simp only [leavesOK] at h
    simp only [GoFV.Proof.Rules.Pat.typed]
    obtain ⟨-, x, -, -, -, hs⟩ := hm
    exact typedsL_of hQ hty hleaf hn args p 0 _ hs h
  | .wild, p, w, hm, hp, h | .bind _, p, w, hm, hp, h | .same _, p, w, hm, hp, h => by
    have hp' : Q p := by simpa [isOpPat] using hp
    have hat := inst_at (MatchOKL.mem hm) hn
    simp only [leavesOK, hat] at h
    simp only [GoFV.Proof.Rules.Pat.typed, hty, hat]
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 h
    simp only [hx, Option.map_some, Option.getD_some]
    exact hleaf p w x (MatchOKL.mem hm) hp' hx
theorem typedsL_of {M : Defs} {I : Inst} {tabs : Tables} {e : PEnv} {Q : Path → Prop}
    (hQ : ∀ i p, Q (i :: p))
    (hty : ∀ p, e.ty p = ((M.get? (I.at p)).map fun x => shpL tabs x.type).getD .other)
    (hleaf : ∀ p w x, (p, w) ∈ I → Q p → M.get? w = some x →
      (e.leaf p).hasTy (shpL tabs x.type) = true)
    (hn : (I.map Prod.fst).Nodup) :
    ∀ (qs : List Pat) (p : Path) (i : Nat) (ids : List ID), MatchOKsL tabs M I qs p i ids →
      leavessOK M I p i qs = true → GoFV.Proof.Rules.Pat.typeds e p i qs
  | [], _, _, _, _, _ => by simp only [GoFV.Proof.Rules.Pat.typeds]
  | q :: qs, p, i, a :: as, ⟨h1, h2⟩, h => by
    simp only [leavessOK, Bool.and_eq_true] at h
    simp only [GoFV.Proof.Rules.Pat.typeds]
    exact ⟨typed_ofL hQ hty hleaf hn q (i :: p) a h1 (.inl (hQ i p)) h.1,
      typedsL_of hQ hty hleaf hn qs p (i + 1) as h2 h.2⟩
  | _ :: _, _, _, [], h, _ => h.elim
end

end GoFV.Proof.Low.Val
