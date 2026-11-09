import GoFV.Proof.Pass.RewriteTermEval
import GoFV.Proof.Pass.RewriteTermMatch

variable [GoFV.SSA.Sem.Addrs]

/-!
# The validator's pattern checks give `Rule.Sound`'s hypotheses (issue #113)

For the static instance `e` (`RewriteCheck.env`) and a semantic instance `e'` with the same node
fields: the bindings agree up to the values of `DV.val` (`sigma_erase`); on the semantic side a
bound value is a leaf's or a named op node's (`binds_good`, `binds_leaf`); and `wfOK`, `consOK`,
the condition check and `leavesOK` give `Pat.wf`, `Pat.cons`, `condHolds`, `Pat.typed`.
-/

namespace GoFV.Proof.Pass.Rewrite

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck GoFV.Proof.Term
open GoFV.Rules (Pat)
open GoFV.Proof.Rules (DV PEnv Oracle Path Pat.denT Pat.densT Pat.binds Pat.bindss Pat.bindsT
  Pat.bindssT sigma sigmaT auxIntDV
  Pat.wf Pat.wfs Pat.cons Pat.conss Pat.typed Pat.typeds auxIntOk condHolds)

theorem auxIntDV_flat (aty : AuxType) (i : Int64) : (auxIntDV aty i).flat = true := by
  unfold auxIntDV; split <;> rfl

theorem lookup_map {β γ : Type} (g : β → γ) (x : Nat) :
    ∀ l : List (Nat × β), (l.map fun a => (a.1, g a.2)).lookup x = (l.lookup x).map g
  | [] => rfl
  | (k, b) :: l => by
    simp only [List.map_cons, List.lookup]
    cases x == k
    · exact lookup_map g x l
    · rfl

theorem lookup_mem {β : Type} {x : Nat} {d : β} :
    ∀ {l : List (Nat × β)}, l.lookup x = some d → (x, d) ∈ l
  | (k, b) :: l, h => by
    simp only [List.lookup] at h
    split at h
    · rename_i hk; cases h
      simp only [beq_iff_eq] at hk; subst hk; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (lookup_mem h)

section Binds

variable {e e' : PEnv} {tabs tabs' : Tables}

mutual
theorem binds_erase (hty : e.ty = e'.ty) (hai : e.auxInt = e'.auxInt) :
    ∀ (p : Path) (q : Pat), (Pat.bindsT tabs e p q).map (fun a => (a.1, a.2.erase)) =
      (Pat.bindsT tabs' e' p q).map (fun a => (a.1, a.2.erase))
  | _, .wild | _, .same _ => rfl
  | _, .bind _ => rfl
  | p, .op o nm ty ai _ _ args _ => by
    simp only [Pat.bindsT, List.map_append]
    rw [bindss_erase hty hai p 0 args]
    congr 1; congr 1; congr 1
    · cases nm <;> rfl
    · cases ty <;> simp [hty]
    · cases ai <;> simp [hai]
theorem bindss_erase (hty : e.ty = e'.ty) (hai : e.auxInt = e'.auxInt) :
    ∀ (p : Path) (i : Nat) (qs : List Pat), (Pat.bindssT tabs e p i qs).map (fun a => (a.1, a.2.erase)) =
      (Pat.bindssT tabs' e' p i qs).map (fun a => (a.1, a.2.erase))
  | _, _, [] => rfl
  | p, i, q :: qs => by
    simp only [Pat.bindssT, List.map_append]
    rw [binds_erase hty hai (i :: p) q, bindss_erase hty hai p (i + 1) qs]
end

theorem sigma_erase (hty : e.ty = e'.ty) (hai : e.auxInt = e'.auxInt) (pat : Pat) (x : Nat) :
    (sigmaT tabs e pat x).erase = (sigmaT tabs' e' pat x).erase := by
  have h := congrArg (List.lookup x) (binds_erase (tabs := tabs) (tabs' := tabs') hty hai [] pat)
  rw [lookup_map, lookup_map] at h
  simp only [sigmaT]
  cases h1 : (Pat.bindsT tabs e [] pat).lookup x <;> cases h2 : (Pat.bindsT tabs' e' [] pat).lookup x <;>
    simp_all [DV.erase]

end Binds

/-! ## Bound values on the semantic side -/

section Good

variable {M : Defs} {I : Inst} {e : PEnv} {P : Val → Path → Prop} {S : Nat} {tabs : Tables}

mutual
theorem binds_good
    (hleafP : ∀ p w, (p, w) ∈ I → p ≠ [] → P (e.leaf p) p)
    (hopP : ∀ q p w, MatchOK M I q p w → p ≠ [] → Pat.sz q ≤ S → P (Pat.denT tabs e p q) p) :
    ∀ (q : Pat) (p : Path) (w : ID), MatchOK M I q p w → p ≠ [] → Pat.sz q ≤ S →
      ∀ y ∈ Pat.bindsT tabs e p q, Good P y.2
  | .wild, _, _, _, _, _, y, hy | .same _, _, _, _, _, _, y, hy => by simp [Pat.bindsT] at hy
  | .bind x, p, w, hm, hp, _, y, hy => by
    simp only [Pat.bindsT, List.mem_singleton] at hy
    subst hy
    exact ⟨fun w' p' h => by
      simp only [DV.val.injEq, Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hleafP _ _ hm hp, fun _ h => by cases h⟩
  | .op o nm ty ai ax ar args cm, p, w, hm, hp, hsz, y, hy => by
    simp only [Pat.bindsT, List.mem_append] at hy
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
      subst hy; exact good_of_flat (auxIntDV_flat _ _)
    · obtain ⟨-, x, -, -, -, ids, -, hs⟩ := hm
      exact bindss_good hleafP hopP args p 0 ids hs (by simp only [Pat.sz] at hsz; omega) y hy
theorem bindss_good
    (hleafP : ∀ p w, (p, w) ∈ I → p ≠ [] → P (e.leaf p) p)
    (hopP : ∀ q p w, MatchOK M I q p w → p ≠ [] → Pat.sz q ≤ S → P (Pat.denT tabs e p q) p) :
    ∀ (qs : List Pat) (p : Path) (i : Nat) (ids : List ID), MatchOKs M I qs p i ids →
      Pat.szs qs ≤ S → ∀ y ∈ Pat.bindssT tabs e p i qs, Good P y.2
  | [], _, _, _, _, _, y, hy => by simp [Pat.bindssT] at hy
  | q :: qs, p, i, a :: as, ⟨h1, h2⟩, hsz, y, hy => by
    simp only [Pat.bindssT, List.mem_append] at hy
    simp only [Pat.szs] at hsz
    rcases hy with hy | hy
    · exact binds_good hleafP hopP q (i :: p) a h1 (List.cons_ne_nil _ _) (by omega) y hy
    · exact bindss_good hleafP hopP qs p (i + 1) as h2 (by omega) y hy
  | _ :: _, _, _, [], h, _, _, _ => h.elim
end

/-- The variables of a pattern at the top whose node is unnamed are good. -/
theorem sigma_good
    (hleafP : ∀ p w, (p, w) ∈ I → p ≠ [] → P (e.leaf p) p)
    (hopP : ∀ q p w, MatchOK M I q p w → p ≠ [] → Pat.sz q ≤ S → P (Pat.denT tabs e p q) p)
    {o : Op} {ty ai ax : GoFV.Rules.Field} {ar : GoFV.Rules.Arity} {args : List Pat} {cm : Bool}
    {v : ID} (hm : MatchOK M I (.op o none ty ai ax ar args cm) [] v)
    (hS : Pat.sz (.op o none ty ai ax ar args cm) ≤ S) (x : Nat) :
    Good P (sigmaT tabs e (.op o none ty ai ax ar args cm) x) := by
  simp only [sigmaT]
  cases hl : (Pat.bindsT tabs e [] (.op o none ty ai ax ar args cm)).lookup x with
  | none => exact good_of_flat rfl
  | some d =>
    have hy := lookup_mem hl
    simp only [Pat.bindsT, List.mem_append] at hy
    simp only [Option.getD_some]
    rcases hy with ((hy | hy) | hy) | hy
    · simp at hy
    · cases ty <;> simp at hy
      obtain ⟨-, rfl⟩ := hy; exact good_of_flat rfl
    · cases ai <;> simp at hy
      obtain ⟨-, rfl⟩ := hy; exact good_of_flat (auxIntDV_flat _ _)
    · obtain ⟨-, x, -, -, -, ids, -, hs⟩ := hm
      exact bindss_good hleafP hopP args [] 0 ids hs (by simp only [Pat.sz] at hS; omega) _ hy

end Good

/-! ## Bound values of non-op variables are leaves -/

section Leaf

variable {e : PEnv} {tabs : Tables}

mutual
theorem binds_leaf : ∀ (q : Pat) (p : Path), ∀ y ∈ Pat.bindsT tabs e p q, ∀ w p',
    y.2 = .val w (some p') → y.1 ∉ GoFV.Opt.RewriteCheck.Pat.opNames q → w = e.leaf p'
  | .wild, _, y, hy, _, _, _, _ | .same _, _, y, hy, _, _, _, _ => by simp [Pat.bindsT] at hy
  | .bind x, p, y, hy, w, p', h, _ => by
    simp only [Pat.bindsT, List.mem_singleton] at hy
    subst hy
    simp only [DV.val.injEq, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | .op o nm ty ai _ _ args _, p, y, hy, w, p', h, hn => by
    simp only [Pat.bindsT, List.mem_append] at hy
    rcases hy with ((hy | hy) | hy) | hy
    · cases nm with
      | none => simp at hy
      | some x =>
        simp only [List.mem_singleton] at hy; subst hy
        simp [GoFV.Opt.RewriteCheck.Pat.opNames] at hn
    · cases ty <;> simp at hy
      subst hy; cases h
    · cases ai <;> simp at hy
      subst hy; have := auxIntDV_flat o.auxType (e.auxInt p); simp only at h; rw [h] at this; cases this
    · refine bindss_leaf args p 0 y hy w p' h ?_
      intro hc; apply hn
      simp only [GoFV.Opt.RewriteCheck.Pat.opNames, List.mem_append]; exact .inr hc
theorem bindss_leaf : ∀ (qs : List Pat) (p : Path) (i : Nat), ∀ y ∈ Pat.bindssT tabs e p i qs, ∀ w p',
    y.2 = .val w (some p') → y.1 ∉ GoFV.Opt.RewriteCheck.Pat.opNamess qs → w = e.leaf p'
  | [], _, _, y, hy, _, _, _, _ => by simp [Pat.bindssT] at hy
  | q :: qs, p, i, y, hy, w, p', h, hn => by
    simp only [Pat.bindssT, List.mem_append] at hy
    simp only [GoFV.Opt.RewriteCheck.Pat.opNamess, List.mem_append, not_or] at hn
    rcases hy with hy | hy
    · exact binds_leaf q (i :: p) y hy w p' h hn.1
    · exact bindss_leaf qs p (i + 1) y hy w p' h hn.2
end

theorem sigma_leaf {pat : Pat} {x : Nat} {w : Val} {p' : Path}
    (h : sigmaT tabs e pat x = .val w (some p')) (hn : x ∉ GoFV.Opt.RewriteCheck.Pat.opNames pat) :
    w = e.leaf p' := by
  simp only [sigmaT] at h
  cases hl : (Pat.bindsT tabs e [] pat).lookup x with
  | none => rw [hl] at h; cases h
  | some d =>
    rw [hl] at h
    exact binds_leaf pat [] (x, d) (lookup_mem hl) w p' h hn

end Leaf

/-! ## Checks -/

theorem auxIntOk_of {aty : AuxType} {a : Int64} (h : auxIntOkB aty a = true) : auxIntOk aty a := by
  cases aty <;> simp_all [auxIntOkB, auxIntOk]

mutual
theorem wf_of {e e' : PEnv} (hai : e.auxInt = e'.auxInt) :
    ∀ (p : Path) (q : Pat), wfOK e p q = true → Pat.wf e' p q
  | p, .op o _ _ _ _ _ args _, h => by
    simp only [wfOK, Bool.and_eq_true] at h
    simp only [Pat.wf]
    exact ⟨hai ▸ auxIntOk_of h.1, wfs_of hai p 0 args h.2⟩
  | _, .wild, _ | _, .bind _, _ | _, .same _, _ => by simp only [Pat.wf]
theorem wfs_of {e e' : PEnv} (hai : e.auxInt = e'.auxInt) :
    ∀ (p : Path) (i : Nat) (qs : List Pat), wfsOK e p i qs = true → Pat.wfs e' p i qs
  | _, _, [], _ => by simp only [Pat.wfs]
  | p, i, q :: qs, h => by
    simp only [wfsOK, Bool.and_eq_true] at h
    simp only [Pat.wfs]
    exact ⟨wf_of hai (i :: p) q h.1, wfs_of hai p (i + 1) qs h.2⟩
end

theorem dvTyEq_eq {t : Ty} {d : DV} (h : dvTyEq t d = true) : d = .ty t := by
  unfold dvTyEq at h
  split at h
  · rw [tyEq_sound h]
  · cases h

theorem dvAuxIntEq_eq {a b : DV} (h : dvAuxIntEq a b = true) : a = b := by
  unfold dvAuxIntEq at h
  split at h <;> simp_all

section Cons

variable {pat : Pat} {I : Inst} {e e' : PEnv} {ev ev' : GoFV.Rules.Expr → DV} {σ σ' : Nat → DV}

mutual
theorem cons_of (hty : e.ty = e'.ty) (hai : e.auxInt = e'.auxInt)
    (hev : ∀ x, (ev x).erase = (ev' x).erase) (hσ : ∀ x, (σ x).erase = (σ' x).erase)
    (hsame : ∀ x w p', σ' x = .val w (some p') → x ∉ GoFV.Opt.RewriteCheck.Pat.opNames pat →
      w = e'.leaf p')
    (hleaf : ∀ p p', I.at p = I.at p' → e'.leaf p = e'.leaf p')
    (hS : ∀ x, x ∈ GoFV.Opt.RewriteCheck.Pat.sames pat → x ∉ GoFV.Opt.RewriteCheck.Pat.opNames pat) :
    ∀ (p : Path) (q : Pat), (∀ x ∈ GoFV.Opt.RewriteCheck.Pat.sames q, x ∈ GoFV.Opt.RewriteCheck.Pat.sames pat) →
      consOK ev σ e I p q = true → Pat.cons ev' σ' e' p q
  | _, .wild, _, _ | _, .bind _, _, _ => by simp only [Pat.cons]
  | p, .same x, hsub, h => by
    simp only [consOK] at h
    split at h
    · rename_i v p' hx
      simp only [beq_iff_eq] at h
      have hx' := hσ x
      rw [hx, DV.erase_val] at hx'
      cases hy : σ' x <;> rw [hy] at hx' <;> simp only [DV.erase, reduceCtorEq] at hx'
      rename_i w p''
      simp only [DV.val.injEq] at hx'
      obtain ⟨-, rfl⟩ := hx'
      simp only [Pat.cons, hy]
      have hx := hS x (hsub x (by simp [GoFV.Opt.RewriteCheck.Pat.sames]))
      rw [hsame x w p' hy hx, hleaf p' p h]
    · cases h
  | p, .op o _ ty ai _ _ args _, hsub, h => by
    simp only [consOK, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    simp only [Pat.cons]
    refine ⟨?_, ?_, conss_of hty hai hev hσ hsame hleaf hS p 0 args (fun x hx => hsub x (by
      simpa [GoFV.Opt.RewriteCheck.Pat.sames] using hx)) h3⟩
    · cases ty with
      | eq te =>
        simp only at h1 ⊢
        have h' := hev te
        rw [dvTyEq_eq h1] at h'
        rw [← hty]
        exact dv_eq_of_erase h' rfl
      | _ => trivial
    · cases ai with
      | eq ae =>
        simp only at h2 ⊢
        have h' := hev ae
        rw [← dvAuxIntEq_eq h2] at h'
        rw [← hai]
        exact dv_eq_of_erase h' (auxIntDV_flat _ _)
      | _ => trivial
theorem conss_of (hty : e.ty = e'.ty) (hai : e.auxInt = e'.auxInt)
    (hev : ∀ x, (ev x).erase = (ev' x).erase) (hσ : ∀ x, (σ x).erase = (σ' x).erase)
    (hsame : ∀ x w p', σ' x = .val w (some p') → x ∉ GoFV.Opt.RewriteCheck.Pat.opNames pat →
      w = e'.leaf p')
    (hleaf : ∀ p p', I.at p = I.at p' → e'.leaf p = e'.leaf p')
    (hS : ∀ x, x ∈ GoFV.Opt.RewriteCheck.Pat.sames pat → x ∉ GoFV.Opt.RewriteCheck.Pat.opNames pat) :
    ∀ (p : Path) (i : Nat) (qs : List Pat),
      (∀ x ∈ GoFV.Opt.RewriteCheck.Pat.samess qs, x ∈ GoFV.Opt.RewriteCheck.Pat.sames pat) →
      conssOK ev σ e I p i qs = true → Pat.conss ev' σ' e' p i qs
  | _, _, [], _, _ => by simp only [Pat.conss]
  | p, i, q :: qs, hsub, h => by
    simp only [conssOK, Bool.and_eq_true] at h
    simp only [Pat.conss]
    exact ⟨cons_of hty hai hev hσ hsame hleaf hS (i :: p) q
        (fun x hx => hsub x (by simp [GoFV.Opt.RewriteCheck.Pat.samess, hx])) h.1,
      conss_of hty hai hev hσ hsame hleaf hS p (i + 1) qs
        (fun x hx => hsub x (by simp [GoFV.Opt.RewriteCheck.Pat.samess, hx])) h.2⟩
end

end Cons

theorem cond_of {ev ev' : GoFV.Rules.Expr → DV} (hev : ∀ x, (ev x).erase = (ev' x).erase)
    {c : Option GoFV.Rules.Expr} (h : ∀ x, c = some x → ev x = .bool true) : condHolds ev' c := by
  cases c with
  | none => trivial
  | some c =>
    simp only [condHolds]
    have h' := hev c
    rw [h c rfl] at h'
    exact (dv_eq_of_erase h' rfl).symm

mutual
theorem typed_of {M : Defs} {I : Inst} {tabs : Tables} {e : PEnv}
    (hty : ∀ p, e.ty p = ((M.get? (I.at p)).map fun x => tabs.ty x.type).getD .other)
    (hleaf : ∀ p w x, (p, w) ∈ I → p ≠ [] → M.get? w = some x →
      (e.leaf p).hasTy (tabs.ty x.type) = true)
    (hn : (I.map Prod.fst).Nodup) :
    ∀ (q : Pat) (p : Path) (w : ID), MatchOK M I q p w → p ≠ [] ∨ isOpPat q = true →
      leavesOK M I p q = true → Pat.typed e p q
  | .op o _ _ _ _ _ args _, p, w, hm, _, h => by
    simp only [leavesOK] at h
    simp only [Pat.typed]
    obtain ⟨-, x, -, -, -, ids, -, hs⟩ := hm
    exact typeds_of hty hleaf hn args p 0 ids hs h
  | .wild, p, w, hm, hp, h | .bind _, p, w, hm, hp, h | .same _, p, w, hm, hp, h => by
    have hp' : p ≠ [] := by simpa [isOpPat] using hp
    have hat := inst_at (MatchOK.mem hm) hn
    simp only [leavesOK, hat] at h
    simp only [Pat.typed, hty, hat]
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 h
    simp only [hx, Option.map_some, Option.getD_some]
    exact hleaf p w x (MatchOK.mem hm) hp' hx
theorem typeds_of {M : Defs} {I : Inst} {tabs : Tables} {e : PEnv}
    (hty : ∀ p, e.ty p = ((M.get? (I.at p)).map fun x => tabs.ty x.type).getD .other)
    (hleaf : ∀ p w x, (p, w) ∈ I → p ≠ [] → M.get? w = some x →
      (e.leaf p).hasTy (tabs.ty x.type) = true)
    (hn : (I.map Prod.fst).Nodup) :
    ∀ (qs : List Pat) (p : Path) (i : Nat) (ids : List ID), MatchOKs M I qs p i ids →
      leavessOK M I p i qs = true → Pat.typeds e p i qs
  | [], _, _, _, _, _ => by simp only [Pat.typeds]
  | q :: qs, p, i, a :: as, ⟨h1, h2⟩, h => by
    simp only [leavessOK, Bool.and_eq_true] at h
    simp only [Pat.typeds]
    exact ⟨typed_of hty hleaf hn q (i :: p) a h1 (.inl (List.cons_ne_nil _ _)) h.1,
      typeds_of hty hleaf hn qs p (i + 1) as h2 h.2⟩
  | _ :: _, _, _, [], h, _ => h.elim
end

end GoFV.Proof.Pass.Rewrite
