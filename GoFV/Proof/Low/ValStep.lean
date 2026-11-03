import GoFV.Proof.Low.ValRule

/-!
# One lowering rule event refines the denotations (issue #385)

The lowered counterpart of `GoFV/Proof/Pass/RewriteTermStep.lean`: in lowered mode (`denL true`),
`RuleFactsL.step` shows that on a set closed under arguments every value's denotation after a
validated rule event refines the one before (fuel multiplied by `stepK r`), from
`ArmRule.Sound1 r` at the matched instance (`RuleFactsL.top`). Also the copy lemmas of
`RewriteTermDen.lean` at the lowered shapes (`copyReachL_den`).
-/

namespace GoFV.Proof.Low.Val

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Opt.RewriteCheck GoFV.Opt.LowerCheck GoFV.Proof.Term
open GoFV.Proof.Low
open GoFV.Proof.Pass.Rewrite (putAll get?_putAll_not get?_putAll_mem get?_put defIds resLen stepK
  Good good_of_flat good_mono evalE_good evalE_erase InI DefClosed DefClosed.arg refinesList_idx
  wf_of cons_of cond_of toList_of_size_one isOpPat)
open GoFV.Proof.Rules (Path PEnv DV Oracle evalE)

/-! ## Lowered denotations -/

section Den

variable {D : ID → Option Value} {tabs : Tables} {ρ : ID → Val}

theorem shapeL_of {a : ID} {y : Value} (h : D a = some y) : shapeL true D tabs a = shpL tabs y.type := by
  simp only [shapeL, h, Option.map_some, Option.getD_some]; rfl

/-- Under `TypedL`, the lowered denotation of a defined value is fixed by `retypeL` at its shape. -/
theorem den_retypeL (hT : TypedL true D tabs ρ) :
    ∀ (k : Nat) (a : ID), (D a).isSome = true →
      (denL true D tabs ρ k a).retypeL (shapeL true D tabs a) = denL true D tabs ρ k a
  | 0, _, _ => retypeL_poison _
  | k + 1, a, hd => by
    by_cases ht : IsTermL tabs D a
    · obtain ⟨v, hv, hop⟩ := ht
      rw [denT_succ hv hop, shapeL_of hv]
      exact retypeL_idem _ _
    · rw [denL_succ_atom ht]; exact hT a ht hd

theorem den_hasTyL (hT : TypedL true D tabs ρ) (k : Nat) {a : ID} {y : Value} (hy : D a = some y) :
    (denL true D tabs ρ k a).hasTy (shpL tabs y.type) = true := by
  rw [← den_retypeL hT k a (by rw [hy]; rfl), shapeL_of hy]
  exact retypeL_hasTy _ _

theorem widen_ptr_elem (e e' : Option Nat) (v : Val) : v.widen (.ptr e) = v.widen (.ptr e') := by
  cases v <;> rfl

theorem retypeL_ptr_elem (e e' : Option Nat) (v : Val) :
    v.retypeL (.ptr e) = v.retypeL (.ptr e') := by
  simp only [Val.retypeL, widen_ptr_elem e e' v]
  exact GoFV.Proof.Pass.Rewrite.retype_ptr_elem e e' _

/-- A `Copy` of a compatible shape is the identity on a value fixed at its argument's shape. -/
theorem retypeL_copyCompat {s t : Ty} (h : copyCompatL s t = true) {z : Val} (hz : z.retypeL t = z) :
    z.retypeL s = z := by
  unfold copyCompatL copyCompat at h
  simp only [Bool.or_eq_true] at h
  rcases h with h | h
  · rw [GoFV.Proof.Pass.Rewrite.tyEq_sound h, hz]
  · simp only [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases s <;> simp at h1
    cases t <;> simp at h2
    rename_i e e'
    rw [retypeL_ptr_elem e e', hz]

theorem opValL_copy (tabs : Tables) (ty : Ty) (ai : Int64) (ax : Option AuxRef) (w : Val) :
    opValL tabs .Copy ty ai ax [w] = w := by
  have hg : Op.Copy.generic = true := by decide
  simp only [opValL, hg, ite_true]
  rw [GoFV.Proof.Rules.opVal_pure (by decide)]
  rfl

/-- The lowered denotation of a `Copy` of a compatible shape is its argument's, one fuel lower. -/
theorem den_copyL (hT : TypedL true D tabs ρ) {a : ID} {x y : Value} (hx : D a = some x)
    (hop : x.op = .Copy) (hsz : x.args.size = 1) (hy : D x.args[0]! = some y)
    (hc : copyCompatL (shpL tabs x.type) (shpL tabs y.type) = true) (k : Nat) :
    denL true D tabs ρ (k + 1) a = denL true D tabs ρ k x.args[0]! := by
  rw [denT_succ hx (termVL_of_copy hop), toList_of_size_one hsz, hop]
  simp only [List.map_cons, List.map_nil, opValL_copy]
  apply retypeL_copyCompat hc
  rw [← shapeL_of (tabs := tabs) hy]
  exact den_retypeL hT k _ (by rw [hy]; rfl)

end Den

/-- A value reached through compatible copies has a larger lowered denotation at the same fuel. -/
theorem copyReachL_den {M : Defs} {tabs : Tables} {ρ : ID → Val} (hT : TypedL true M.get? tabs ρ) :
    ∀ (N : Nat) (a w : ID), copyReachL tabs M N a w = true →
      ∀ k, Sem.Refines (denL true M.get? tabs ρ k a) (denL true M.get? tabs ρ k w)
  | 0, a, w, h, k => by
    simp only [copyReachL, beq_iff_eq] at h; subst h; exact Sem.Refines.refl _
  | N + 1, a, w, h, k => by
    simp only [copyReachL, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with rfl | h
    · exact Sem.Refines.refl _
    · cases hx : M.get? a with
      | none => rw [hx] at h; cases h
      | some x =>
        rw [hx] at h
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨⟨hop, hsz⟩, hy⟩, hr⟩ := h
        cases hy' : M.get? x.args[0]! with
        | none => rw [hy'] at hy; cases hy
        | some y =>
          rw [hy'] at hy
          cases k with
          | zero => exact .poison _
          | succ k =>
            rw [den_copyL hT hx hop hsz hy' hy k]
            exact Sem.Refines.trans (denL_fuel_mono _ _ _ _ k (k + 1) _ (by omega))
              (copyReachL_den hT N _ w hr (k + 1))

theorem copyReachL_closed {tabs : Tables} {M : Defs} {C : ID → Prop} (hC : DefClosed M C) :
    ∀ (N : Nat) (a w : ID), copyReachL tabs M N a w = true → C a → C w
  | 0, a, w, h, ha => by simp only [copyReachL, beq_iff_eq] at h; exact h ▸ ha
  | N + 1, a, w, h, ha => by
    simp only [copyReachL, Bool.or_eq_true, beq_iff_eq] at h
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
        exact copyReachL_closed hC N _ w hr (hargs _ (Array.mem_toList_iff.1 (by
          rw [toList_of_size_one hsz]; exact List.mem_singleton_self _)))

/-! ## The denotations of a rule event -/

/-- The semantic instance: the leaves are `L` of the matched values. -/
def semEnvL (tabs : Tables) (M : Defs) (I : Inst) (L : ID → Val) : PEnv :=
  { envL tabs M I with leaf := fun p => L (I.at p) }

section Step

variable {tabs : Tables} {M : Defs} {r : Rule} {v : ID} {defs : List Value}

theorem RuleFactsL.not_def (F : RuleFactsL tabs M r v defs) {w : ID} {x : Value}
    (hw : M.get? w = some x) (hne : w ≠ v) : w ∉ defIds defs := fun h =>
  match F.frame.2.2.1 w h with
  | .inl h => hne h
  | .inr h => by rw [hw] at h; cases h

theorem RuleFactsL.keep (F : RuleFactsL tabs M r v defs) {w : ID} {x : Value}
    (hw : M.get? w = some x) (hne : w ≠ v) : (putAll M defs).get? w = some x := by
  rw [F.frame.1 w (F.not_def hw hne), hw]

theorem RuleFactsL.keepAtom (F : RuleFactsL tabs M r v defs) {w : ID} {x : Value}
    (hw : M.get? w = some x) (ha : termVL tabs x = false) : (putAll M defs).get? w = some x := by
  refine F.keep hw fun h => ?_
  subst h; rw [F.hxv] at hw; cases hw; rw [F.hterm] at ha; cases ha

theorem RuleFactsL.fields (F : RuleFactsL tabs M r v defs) (L : ID → Val) :
    FieldsOKL tabs M F.I (semEnvL tabs M F.I L) := by
  intro p w x hm hx
  refine ⟨?_, ?_, ?_⟩ <;> simp [semEnvL, envL, F.at_eq hm, hx]

theorem RuleFactsL.typed (F : RuleFactsL tabs M r v defs) {ρ : ID → Val}
    (hT : TypedL true M.get? tabs ρ) : TypedL true (putAll M defs).get? tabs ρ := by
  intro a ha hsome
  by_cases hd : a ∈ defIds defs
  · obtain ⟨u, hu, ht, -⟩ := F.frame.2.2.2 a hd
    exact absurd ⟨u, hu, ht⟩ ha
  · have he := F.frame.1 a hd
    have hshape : shapeL true (putAll M defs).get? tabs a = shapeL true M.get? tabs a := by
      simp [shapeL, he]
    rw [hshape]
    exact hT a (fun ⟨u, hu, ht⟩ => ha ⟨u, by rw [he]; exact hu, ht⟩) (he ▸ hsome)

theorem RuleFactsL.closed (F : RuleFactsL tabs M r v defs) {C : ID → Prop} (hC : DefClosed M C) :
    DefClosed (putAll M defs) (fun y => C y ∨ (C v ∧ y ∈ defIds defs)) := by
  have hfr := F.frame
  have hnew : ∀ y, C v → y ∈ defIds defs → ∃ m, (putAll M defs).get? y = some m ∧
      ∀ a ∈ m.args, C a ∨ (C v ∧ a ∈ defIds defs) := by
    intro y hv hy
    obtain ⟨u, hu, -, hargs⟩ := hfr.2.2.2 y hy
    refine ⟨u, hu, fun a ha => ?_⟩
    rcases hargs a ha with ⟨p, hp⟩ | ha'
    · exact .inl (F.hreach C hC.arg hv (p, a) hp)
    · exact .inr ⟨hv, ha'⟩
  intro y hy
  rcases hy with hy | ⟨hv, hy⟩
  · by_cases hd : y ∈ defIds defs
    · obtain ⟨m, hm, -⟩ := hC y hy
      rcases hfr.2.2.1 y hd with rfl | h
      · exact hnew _ hy hd
      · rw [hm] at h; cases h
    · obtain ⟨m, hm, hargs⟩ := hC y hy
      exact ⟨m, by rw [hfr.1 y hd, hm], fun a ha => .inl (hargs a ha)⟩
  · exact hnew y hv hy

theorem RuleFactsL.top_ty (F : RuleFactsL tabs M r v defs) (L : ID → Val) :
    (semEnvL tabs M F.I L).ty [] = shpL tabs F.xv.type := by
  simp only [semEnvL, envL, F.at_top, F.hxv, Option.map_some, Option.getD_some]

/-- **The matched value**: its lowered denotation before the event is refined by the one after. -/
theorem RuleFactsL.top (hs : ArmRule.Sound1 r)
    (F : RuleFactsL tabs M r v defs) {C : ID → Prop} (hC : GoFV.Proof.Pass.Rewrite.ArgClosed M C)
    (hv : C v) {ρ : ID → Val} (hT : TypedL true (putAll M defs).get? tabs ρ) {n B : Nat}
    (hIH : ∀ y, C y → Sem.Refines (denL true M.get? tabs ρ n y)
      (denL true (putAll M defs).get? tabs ρ B y)) :
    Sem.Refines (denL true M.get? tabs ρ (n + 1) v)
      (denL true (putAll M defs).get? tabs ρ (B + stepK r) v) := by
  -- the semantic instance
  let e' := semEnvL tabs M F.I (denL true (putAll M defs).get? tabs ρ B)
  have hIC : ∀ p w, (p, w) ∈ F.I → C w := fun p w h => F.hreach C hC hv (p, w) h
  have hσ : ∀ x, (stσL tabs M r F.I x).erase = (sigmaL tabs e' r.pat x).erase :=
    sigmaL_erase (e := envL tabs M F.I) (e' := e') rfl rfl r.pat
  have hev : ∀ x, (stEvL tabs M r defs F.I x).erase =
      (evalE (stVtysL r) (sigmaL tabs e' r.pat) (stOrL tabs r defs) e'
        (Pat.denL tabs e' [] r.pat) x).erase :=
    evalE_erase (e := envL tabs M F.I) (e' := e') _ _ rfl rfl hσ _ _
  have hF := F.fields (denL true (putAll M defs).get? tabs ρ B)
  have hTop := F.top_ty (denL true (putAll M defs).get? tabs ρ B)
  have hdefw : ∀ p w x, (p, w) ∈ F.I → p ≠ [] → M.get? w = some x →
      (putAll M defs).get? w = some x := fun p w x hm hp hx => F.keep hx (F.ne_v hm hp)
  -- the hypotheses of `ArmRule.Sound1`
  have hbt : Oracle.BoolTyped (stOrL tabs r defs) := oracleL_boolTyped _ _ _ _
  have hwf := wf_of (e := envL tabs M F.I) (e' := e') rfl [] r.pat F.hwf
  have hcons := cons_of (pat := r.pat) (I := F.I) (e := envL tabs M F.I) (e' := e')
    rfl rfl hev hσ (fun x w p' h hn => sigmaL_leaf h hn)
    (fun p p' h => by simp only [e', semEnvL, h]) F.hS [] r.pat (fun _ h => h) F.hcons
  have hcond := cond_of hev F.hcond
  have htyped : GoFV.Proof.Rules.Pat.typed e' [] r.pat :=
    typed_ofL (Q := fun p => p ≠ []) (fun _ _ => List.cons_ne_nil _ _) (fun p => rfl)
      (fun p w x hm hp hx => by
        show (denL true _ tabs ρ B (F.I.at p)).hasTy _ = true
        rw [F.at_eq hm]
        exact den_hasTyL hT B (hdefw p w x hm hp hx))
      F.hnodup r.pat [] v F.hmatch (.inr (by rw [F.hpat]; rfl)) F.hleaves
  have hargs : GoFV.Proof.Rules.Pat.argsOK e'.ty [] r.pat = true := F.hargs
  have htopok : Pat.topOKL (e'.ty []) r.pat = true := F.htop
  have hsound := fun hcs => hs.2 tabs e' (stOrL tabs r defs) hbt hwf hcons hcond htyped hargs
    htopok F.hargsL hcs F.hfit F.hadr
  -- lower bound
  have hlow : Sem.Refines (denL true M.get? tabs ρ (n + 1) v)
      ((Pat.rawL tabs e' r.pat).retypeL (e'.ty [])) := by
    have h1 := den_le_patDenL (n := n) hF (fun p w hm k hk => by
        show Sem.Refines _ (denL true _ tabs ρ B (F.I.at p))
        rw [F.at_eq hm]
        exact Sem.Refines.trans (denL_fuel_mono _ _ _ _ k n w hk) (hIH w (hIC p w hm)))
      r.pat [] v (n + 1) F.hmatch (Nat.le_refl _) (.inr (by rw [F.hpat]; rfl))
    rw [F.hpat] at h1 ⊢
    simp only [Pat.denL, Pat.rawL] at h1 ⊢
    exact h1
  -- values bound on the semantic side
  have hleafU : ∀ p w, (p, w) ∈ F.I → Sem.Refines (e'.leaf p)
      (denL true (putAll M defs).get? tabs ρ B w) := fun p w hm => by
    show Sem.Refines (denL true _ tabs ρ B (F.I.at p)) _
    rw [F.at_eq hm]; exact Sem.Refines.refl _
  obtain ⟨S, hS⟩ : ∃ S, S = GoFV.Proof.Pass.Rewrite.Pat.sz r.pat := ⟨_, rfl⟩
  have hσ2 : ∀ x, Good (fun w p => p ≠ [] ∧
      Sem.Refines w (denL true (putAll M defs).get? tabs ρ (B + S) (F.I.at p)))
      (sigmaL tabs e' r.pat x) := by
    intro x
    have hm := F.hmatch
    have hS' : GoFV.Proof.Pass.Rewrite.Pat.sz r.pat ≤ S := by omega
    rw [F.hpat] at hm hS' ⊢
    exact sigmaL_good_top (Q := fun p => p ≠ []) (P := fun w p => p ≠ [] ∧
        Sem.Refines w (denL true (putAll M defs).get? tabs ρ (B + S) (F.I.at p))) (S := S)
      (fun _ _ => List.cons_ne_nil _ _)
      (fun p w hm' hp => ⟨hp, by
        show Sem.Refines (denL true _ tabs ρ B (F.I.at p)) _
        exact denL_fuel_mono _ _ _ _ _ _ _ (by omega)⟩)
      (fun q p w hm' hp hsz => ⟨hp, by
        rw [F.at_eq hm'.mem]
        exact patDen_le_denL (Q := fun p => p ≠ []) (fun _ _ => List.cons_ne_nil _ _) hF
          hdefw hleafU q p w _ hm' hp (by omega)⟩) hm hS' x
  have hev2 : ∀ x, Good (fun w p => p ≠ [] →
      Sem.Refines w (denL true (putAll M defs).get? tabs ρ (B + S) (F.I.at p)))
      (evalE (stVtysL r) (sigmaL tabs e' r.pat) (stOrL tabs r defs) e'
        (Pat.denL tabs e' [] r.pat) x) :=
    evalE_good _ _ _ (fun x => good_mono (fun w p h _ => h.2) (hσ2 x)) (fun h => absurd rfl h)
      (fun x => good_of_flat (oracleL_flat _ _ _ _ x))
  rcases F.result with hR | hR
  · -- copy
    obtain ⟨R⟩ := hR
    have hpos := R.hpos
    obtain ⟨w0, hst⟩ : ∃ w0, stEvL tabs M r defs F.I R.ce = .val w0 (some R.p) := by
      revert hpos; cases stEvL tabs M r defs F.I R.ce <;> simp [DV.pos?]
    have h' := hev R.ce
    rw [hst] at h'
    have hp : R.p ≠ [] := fun h => R.hne (by rw [h, F.at_top])
    have hcases : ∀ d : DV, (DV.val w0 (some R.p)).erase = d.erase →
        Good (fun w p => p ≠ [] →
          Sem.Refines w (denL true (putAll M defs).get? tabs ρ (B + S) (F.I.at p))) d →
        Sem.Refines (d.valOr ((stOrL tabs r defs).val R.ce))
          (denL true (putAll M defs).get? tabs ρ (B + S) (F.I.at R.p)) := by
      intro d hd hg
      rcases DV.erase_eq_cases hd with rfl | ⟨v1, v2, p1, h1, rfl⟩
      · exact hg.1 w0 R.p rfl hp
      · cases h1; exact hg.1 v2 R.p rfl hp
    have hup := hcases _ h' (hev2 R.ce)
    obtain ⟨y, hy, hyt, hsh⟩ : ∃ y, M.get? (F.I.at R.p) = some y ∧ y.type = R.u.type ∧
        shpL tabs y.type = shpL tabs F.xv.type := by
      have := R.hty
      cases h : M.get? (F.I.at R.p) with
      | none => rw [h] at this; cases this
      | some y =>
        rw [h] at this
        simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at this
        exact ⟨y, rfl, this.1, GoFV.Proof.Pass.Rewrite.tyEq_sound this.2⟩
    have hcs : GoFV.Proof.Low.copyShapeOK (evalE (stVtysL r) (sigmaL tabs e' r.pat)
        (stOrL tabs r defs) e' (Pat.denL tabs e' [] r.pat)) e' r.result := by
      rw [R.hres]
      simp only [GoFV.Proof.Low.copyShapeOK]
      split
      · rename_i w p heq
        have h2 := h'
        rw [heq, DV.erase_val, DV.erase_val] at h2
        simp only [DV.val.injEq, Option.some.injEq, true_and] at h2
        subst h2
        rw [hTop]
        simp only [e', semEnvL, envL, hy, Option.map_some, Option.getD_some]
        exact hsh
      · trivial
    have hsound := hsound hcs
    rw [R.hres] at hsound
    have hkeep := F.keep hy R.hne
    have hdv : (putAll M defs).get? v = some R.u := by rw [R.put, get?_put]; simp
    have hK : B + stepK r = (B + S + 1) + 1 := by simp [stepK, resLen, R.hres, hS]; omega
    rw [hK, denT_succ hdv (termVL_of_copy R.hop), R.hargs, R.hop]
    simp only [List.map_cons, List.map_nil, Array.toList, opValL_copy]
    rw [← hyt, ← shapeL_of (tabs := tabs) hkeep, den_retypeL hT _ _ (by rw [hkeep]; rfl)]
    exact hlow.trans (hsound.trans (hup.trans (denL_fuel_mono _ _ _ _ _ _ _ (by omega))))
  · -- build
    obtain ⟨R⟩ := hR
    have hsound := hsound (by rw [R.hres]; trivial)
    rw [R.hres] at hsound
    have hTy : e'.ty [] = shpL tabs F.xv.type := hTop
    have key : ∀ f k (hk : k < R.nodes.length),
        Sem.Refines (nodeDenL tabs e' r.pat (evalE (stVtysL r) (sigmaL tabs e' r.pat)
            (stOrL tabs r defs) e' (Pat.denL tabs e' [] r.pat))
          (stOrL tabs r defs) (sigmaL tabs e' r.pat) (e'.ty []) R.nodes f k)
        (denL true (putAll M defs).get? tabs ρ (B + S + f) (R.us[k]'(R.hlen ▸ hk)).id) := by
      intro f
      induction f with
      | zero => intro k hk; exact .poison _
      | succ f ih =>
        intro k hk
        have hk' : k < R.us.length := R.hlen ▸ hk
        obtain ⟨hop, ht, hty, hai, hax, hsz, hargs⟩ := nodeOKL_facts (R.hnode k hk hk')
        rw [nodeDenL_succ _ _ _ _ _ _ _ _ f k R.nodes[k] (List.getElem?_eq_getElem hk)]
        rw [show B + S + (f + 1) = (B + S + f) + 1 by omega, denT_succ (R.get k hk') ht]
        rw [← hTy] at hty
        rw [← tySelL_eq hev, ← aiSelL_eq hev, ← hty, ← hai, ← hop]
        have hax' : nodeAuxL e' r.pat (stOrL tabs r defs) R.nodes[k].aux = R.us[k].aux := by
          rw [hax]; rfl
        rw [hax']
        apply retypeL_mono
        apply opValL_mono_term ht
        refine refinesList_idx (by simp [hsz]) fun j h1 h2 => ?_
        have harg := hargs j h1 (by simpa using h2)
        simp only [Array.getElem_toList]
        cases hn : R.nodes[k].args[j] with
        | var x =>
          rw [hn] at harg
          simp only [argID, Option.map_eq_some_iff] at harg
          obtain ⟨p, hp, hpa⟩ := harg
          simp only [argValL]
          obtain ⟨w0, hw0⟩ : ∃ w0, stσL tabs M r F.I x = .val w0 (some p) := by
            revert hp; cases stσL tabs M r F.I x <;> simp [DV.pos?]
          have hx := hσ x
          rw [hw0] at hx
          rcases DV.erase_eq_cases hx with h2 | ⟨v1, v2, p1, h1, h2⟩
          · rw [← h2]
            have := (hσ2 x).1 w0 p h2.symm
            rw [← hpa]
            exact this.2.trans (denL_fuel_mono _ _ _ _ _ _ _ (by omega))
          · cases h1
            rw [h2]
            have := (hσ2 x).1 v2 p h2
            rw [← hpa]
            exact this.2.trans (denL_fuel_mono _ _ _ _ _ _ _ (by omega))
        | node j' =>
          rw [hn] at harg
          simp only [argID] at harg
          simp only [argValL]
          obtain ⟨hj', hj'e⟩ := List.getElem?_eq_some_iff.1 harg
          simp only [List.length_map] at hj'
          rw [← hj'e]
          simp only [List.getElem_map]
          exact ih j' (R.hlen ▸ hj')
        | expr _ =>
          rw [hn] at harg
          simp [argID] at harg
    have h0 := key R.nodes.length 0 R.len
    have hid := R.id0 (R.hlen ▸ R.len)
    simp only [hid] at h0
    refine hlow.trans (hsound.trans (h0.trans (denL_fuel_mono _ _ _ _ _ _ _ ?_)))
    simp [stepK, resLen, R.hres, hS]; omega

/-- **One rule event**: on a set closed under arguments, the lowered denotations after the event
refine those before, with the fuel multiplied by `stepK r`. -/
theorem RuleFactsL.step (hs : ArmRule.Sound1 r)
    (F : RuleFactsL tabs M r v defs) {C : ID → Prop} (hC : DefClosed M C) {ρ : ID → Val}
    (hT : TypedL true M.get? tabs ρ) :
    ∀ n y, C y → Sem.Refines (denL true M.get? tabs ρ n y)
      (denL true (putAll M defs).get? tabs ρ (n * stepK r) y) := by
  have hT' := F.typed hT
  intro n
  induction n with
  | zero => intro y _; exact .poison _
  | succ n ih =>
    intro y hy
    by_cases hyv : y = v
    · subst hyv
      rw [Nat.succ_mul]
      exact F.top hs hC.arg hy hT' ih
    · obtain ⟨m, hm, hargs⟩ := hC y hy
      have hkeep := F.keep hm hyv
      have hK : (n + 1) * stepK r = (n * stepK r + (stepK r - 1)) + 1 := by
        rw [Nat.succ_mul]; simp only [stepK]; omega
      rw [hK]
      by_cases ht : termVL tabs m = true
      · rw [denT_succ hm ht, denT_succ hkeep ht]
        exact retypeL_mono _ (opValL_mono_term ht _ (GoFV.Proof.AtomSim.refinesList_map fun a ha =>
          (ih a (hargs a (Array.mem_toList_iff.1 ha))).trans
            (denL_fuel_mono _ _ _ _ _ _ _ (by omega))))
      · have h1 : ¬ IsTermL tabs M.get? y := fun ⟨u, hu, hu'⟩ => by
          rw [hm] at hu; cases hu; exact ht hu'
        have h2 : ¬ IsTermL tabs (putAll M defs).get? y := fun ⟨u, hu, hu'⟩ => by
          rw [hkeep] at hu; cases hu; exact ht hu'
        rw [denL_succ_atom h1, denL_succ_atom h2]; exact Sem.Refines.refl _

end Step

end GoFV.Proof.Low.Val
