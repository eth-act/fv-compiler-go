import GoFV.Proof.Pass.RewriteTermBlock

/-!
# Soundness of the rewrite validator at the term level (issue #113)

`validate_termRef`: if `RewriteCheck.validate` accepts the output `g` of a rewrite pass run with
the table of a sound rule set on `f`, then the arguments of `g`'s atoms refine, as terms over the
atoms (`GoFV.Proof.Term.TermRef`), those of `f`, and `g`'s terminators, as functions of their
controls' terms, refine `f`'s (`Term.TermStepRef`): the premises `AtomArgsRef` and `TermStepRef`
of the atom simulation (`GoFV.Proof.AtomSim`).

Proof: the values listed in `f` (`listedMarks`, closed under arguments by `closedOK f`) keep
refining denotations, and the replayed terminators refine `f`'s, along the replay of the log
(`replay_inv`, `BInv`); the final definitions and terminators are
those of `g` up to copies in arguments (`finalOK`), whose denotation (over the listed values
of `g`, closed by `closedOK g`) refines theirs (`final_den`); atoms keep their fields
(`atomsOK`).
-/

namespace GoFV.Proof.Pass.Rewrite

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck GoFV.Proof.Term GoFV.Proof.AtomSim
open GoFV.Opt GoFV.Rules

/-! ## Listed values -/

theorem foldl_inv {α β : Type} (P : β → Prop) (f : β → α → β) :
    ∀ (l : List α) (b : β), P b → (∀ b a, a ∈ l → P b → P (f b a)) → P (l.foldl f b)
  | [], _, h, _ => h
  | a :: l, b, h, hf => foldl_inv P f l (f b a) (hf b a List.mem_cons_self h)
      fun b' a' ha' h' => hf b' a' (List.mem_cons_of_mem _ ha') h'

/-- `y` is listed in its own block, a block of `h`. -/
def Marked (h : Func) (y : ID) : Prop :=
  ∃ b ∈ h.blocks, ∃ hb, h.block? b = some hb ∧ y ∈ hb.values ∧ ∃ u, h.value? y = some u ∧ u.block = b

/-- The marks of `listedMarks`. -/
def LM (h : Func) (y : ID) : Prop := (listedMarks h)[y]? = some true

theorem listedMarks_sound (h : Func) : ∀ y, LM h y → Marked h y := by
  unfold LM listedMarks
  rw [← Array.foldl_toList]
  refine foldl_inv (fun L : Array Bool => ∀ y, L[y]? = some true → Marked h y) _ _ _ ?_ ?_
  · intro y hy
    rw [Array.getElem?_replicate] at hy
    split at hy <;> cases hy
  · intro L b hb hL
    split
    · rename_i hbk
      rw [← Array.foldl_toList]
      refine foldl_inv (fun L : Array Bool => ∀ y, L[y]? = some true → Marked h y) _ _ _ hL ?_
      intro L x hx hL' y hy
      split at hy
      · rename_i hxb
        simp only [Array.set!, Array.getElem?_setIfInBounds] at hy
        split at hy
        · rename_i hxy; subst hxy
          simp only [Option.any_eq_true, beq_iff_eq] at hxb
          obtain ⟨u, hu, hub⟩ := hxb
          exact ⟨b, Array.mem_toList_iff.1 hb, _, hbk, Array.mem_toList_iff.1 hx, u, hu, hub⟩
        · exact hL' y hy
      · exact hL' y hy
    · exact hL

theorem listedDefs_of_marked {h : Func} {y : ID} (hm : Marked h y) :
    listedDefs h y = h.value? y := by
  obtain ⟨b, hb, hbk, hbb, hyv, u, hu, hub⟩ := hm
  subst hub
  simp [listedDefs, hu, hbb, hyv, hb]

theorem closedOK_facts {h : Func} (hc : closedOK h = true) : ∀ b ∈ h.blocks, ∀ hb,
    h.block? b = some hb → (∀ c ∈ hb.controls, LM h c) ∧
      ∀ x ∈ hb.values, ∀ u, h.value? x = some u → ∀ a ∈ u.args, LM h a := by
  intro b hb hbk hbb
  unfold closedOK at hc
  have := (Array.all_eq_true_iff_forall_mem.1 hc) b hb
  simp only [hbb, Bool.and_eq_true] at this
  obtain ⟨h1, h2⟩ := this
  refine ⟨fun c hc' => ?_, fun x hx u hu a ha => ?_⟩
  · have := (Array.all_eq_true_iff_forall_mem.1 h1) c hc'
    simpa [LM] using this
  · have := (Array.all_eq_true_iff_forall_mem.1 h2) x hx
    simp only [hu, Option.all_some] at this
    have := (Array.all_eq_true_iff_forall_mem.1 this) a ha
    simpa [LM] using this

theorem marked_closed {h : Func} (hc : closedOK h = true) : DefClosed h.valueTab (LM h) := by
  intro y hy
  obtain ⟨b, hb, hbk, hbb, hyv, u, hu, -⟩ := listedMarks_sound h y hy
  exact ⟨u, hu, (closedOK_facts hc b hb hbk hbb).2 y hyv u hu⟩

/-! ## `atomsOK` and `finalOK` -/

theorem atomsOK_facts {f g : Func} (h : atomsOK f g = true) : ∀ b ∈ g.blocks, ∀ gb,
    g.block? b = some gb → ∃ fb, f.block? b = some fb ∧ fb.id = gb.id ∧
      ∀ x ∈ gb.values, ∀ w, g.value? x = some w → termOp w.op = false →
        x ∈ fb.values ∧ ∃ u, f.value? x = some u ∧ u.op = w.op ∧ u.type = w.type ∧
          u.auxInt = w.auxInt ∧ u.aux = w.aux ∧ u.args.size = w.args.size := by
  intro b hb gb hgb
  unfold atomsOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨-, hbl⟩, -⟩, h⟩ := h
  have := (Array.all_eq_true_iff_forall_mem.1 h) b (hbl ▸ hb)
  rw [hgb] at this
  split at this
  · rename_i fb gb' hfb hgb'
    obtain rfl := Option.some.inj hgb'
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at this
    obtain ⟨hid, ⟨hag, -⟩, -⟩ := this
    refine ⟨fb, hfb, hid, fun x hx w hw hwt => ?_⟩
    have hxa : x ∈ atomsOf g gb := by
      simp only [atomsOf, List.mem_filter, Array.mem_toList_iff, hw, isAtom, hwt]
      exact ⟨hx, rfl⟩
    have := hag x hxa
    simp only [List.contains_iff_mem] at this
    obtain ⟨hxf, hfd⟩ := this
    simp only [atomsOf, List.mem_filter, Array.mem_toList_iff] at hxf
    refine ⟨hxf.1, ?_⟩
    rw [hw] at hfd
    split at hfd
    · rename_i u w' hu hw'
      obtain rfl := Option.some.inj hw'
      simp only [Bool.and_eq_true, beq_iff_eq] at hfd
      obtain ⟨⟨⟨⟨⟨⟨hop, hty⟩, hai⟩, hax⟩, hsz⟩, -⟩, -⟩ := hfd
      exact ⟨u, hu, hop, hty, hai, hax, hsz⟩
    · cases hfd
  · cases this

theorem zip_all_get' {α β : Type} {f : α × β → Bool} :
    ∀ {l1 : List α} {l2 : List β}, (l1.zip l2).all f = true →
      ∀ k (h1 : k < l1.length) (h2 : k < l2.length), f (l1[k], l2[k]) = true
  | a :: l1, b :: l2, h, 0, _, _ => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h; exact h.1
  | a :: l1, b :: l2, h, k + 1, h1, h2 => by
    simp only [List.zip_cons_cons, List.all_cons, Bool.and_eq_true] at h
    exact zip_all_get' h.2 k (by simpa using h1) (by simpa using h2)

/-- `x` is marked by `liveMarks h` (read by the output, closed by `liveOK`). -/
def Live (h : Func) (x : ID) : Prop := (liveMarks h)[x]? = some true

theorem liveOK_facts {h : Func} {L : Array Bool} (hl : liveOK h L = true) : ∀ b ∈ h.blocks, ∀ hb,
    h.block? b = some hb → (∀ c ∈ hb.controls, L[c]? = some true) ∧
      ∀ x ∈ hb.values, ∀ u, h.value? x = some u → (termOp u.op = false ∨ L[x]? = some true) →
        ∀ a ∈ u.args, L[a]? = some true := by
  intro b hb hbk hbb
  unfold liveOK at hl
  have := (Array.all_eq_true_iff_forall_mem.1 hl) b hb
  simp only [hbb, Bool.and_eq_true] at this
  obtain ⟨h1, h2⟩ := this
  refine ⟨fun c hc => ?_, fun x hx u hu hlx a ha => ?_⟩
  · simpa using (Array.all_eq_true_iff_forall_mem.1 h1) c hc
  · have := (Array.all_eq_true_iff_forall_mem.1 h2) x hx
    simp only [hu, Option.all_some, Bool.or_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    rcases this with ⟨ht, hn⟩ | hall
    · rcases hlx with hlx | hlx
      · rw [hlx] at ht; cases ht
      · exact absurd hlx hn
    · simpa using (Array.all_eq_true_iff_forall_mem.1 hall) a ha

theorem finalOK_facts {tabs : Tables} {f g : Func} {M : Defs} {B : BMap}
    (h : finalOK tabs f g M B = true) : liveOK g (liveMarks g) = true ∧
    ∀ b ∈ g.blocks, ∀ gb, g.block? b = some gb → ∃ st fb, bstate f B b = some st ∧
      f.block? b = some fb ∧ gb.kind = st.kind ∧
      gb.succs = (if st.swapped then swapS fb.succs else fb.succs) ∧
      (st.swapped = true → fb.succs.size = 2) ∧ gb.controls.size = st.ctrls.size ∧
      (∀ k (h1 : k < st.ctrls.size) (h2 : k < gb.controls.size),
        copyReach tabs M M.size st.ctrls[k] gb.controls[k] = true) ∧
      ∀ x ∈ gb.values, (Live g x ∨ ∀ u, g.value? x = some u → termOp u.op = false) →
        ∃ m u, M.get? x = some m ∧ g.value? x = some u ∧ u.op = m.op ∧
        u.type = m.type ∧ u.auxInt = m.auxInt ∧ u.aux = m.aux ∧ u.args.size = m.args.size ∧
        ∀ j (h1 : j < m.args.size) (h2 : j < u.args.size),
          copyReachW tabs M M.size m.args[j] u.args[j] = true := by
  unfold finalOK at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hlive, h⟩ := h
  refine ⟨hlive, fun b hb gb hgb => ?_⟩
  have := (Array.all_eq_true_iff_forall_mem.1 h) b hb
  split at this
  · rename_i st fb gb' hst hfb hgb'
    rw [hgb] at hgb'; obtain rfl := Option.some.inj hgb'
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    obtain ⟨⟨⟨⟨hk, hsu⟩, hsz⟩, hc⟩, hv⟩ := this
    have hsu' : gb.succs = (if st.swapped then swapS fb.succs else fb.succs) ∧
        (st.swapped = true → fb.succs.size = 2) := by
      cases hsw : st.swapped <;> simp only [hsw, ite_true, ite_false, Bool.false_eq_true] at hsu ⊢
      · exact ⟨beq_iff_eq.1 hsu, fun h => h.elim⟩
      · simp only [Bool.and_eq_true, beq_iff_eq] at hsu
        exact ⟨hsu.2, fun _ => hsu.1⟩
    refine ⟨st, fb, hst, hfb, hk, hsu'.1, hsu'.2, hsz, fun k h1 h2 => ?_, fun x hx hrd => ?_⟩
    · have := zip_all_get' (f := fun x : ID × ID => copyReach tabs M M.size x.1 x.2) hc k
        (by simpa using h1) (by simpa using h2)
      simpa using this
    · have := (Array.all_eq_true_iff_forall_mem.1 hv) x hx
      split at this
      · rename_i m u hm hu
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at this
        rcases this with this | ⟨ht, hr⟩
        · obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, hop⟩, hty⟩, hai⟩, hax⟩, hsz⟩, hargs⟩ := this
          refine ⟨m, u, hm, hu, hop, hty, hai, hax, hsz, fun j h1 h2 => ?_⟩
          have := zip_all_get (f := fun x : ID × ID => copyReachW tabs M M.size x.1 x.2) hargs
            (by simp [hsz]) j (by simpa using h1) (by simpa using h2)
          simpa using this
        · rcases hrd with hrd | hrd
          · exact absurd hrd hr
          · rw [hrd u hu] at ht; cases ht
      · cases this
  · cases this

/-- An argument of a value listed in a block of `h` that is an atom or read is read. -/
theorem live_arg {h : Func} (hl : liveOK h (liveMarks h) = true) {b : ID} (hb : b ∈ h.blocks)
    {hb' : Block} (hbb : h.block? b = some hb') {y : ID} (hy : y ∈ hb'.values) {u : Value}
    (hu : h.value? y = some u) (hly : termOp u.op = false ∨ Live h y) {a : ID} (ha : a ∈ u.args) :
    Live h a :=
  (liveOK_facts hl b hb hb' hbb).2 y hy u hu hly a ha

/-- A control of a block of `h` is read. -/
theorem live_ctrl {h : Func} (hl : liveOK h (liveMarks h) = true) {b : ID} (hb : b ∈ h.blocks)
    {hb' : Block} (hbb : h.block? b = some hb') {c : ID} (hc : c ∈ hb'.controls) : Live h c :=
  (liveOK_facts hl b hb hb' hbb).1 c hc

/-! ## The final definitions -/

/-- The replayed definitions refine those listed in `g` and read by `g` (`Live`; up to the
copies `finalOK` allows). -/
theorem final_den {tabs : Tables} {f g : Func} {M : Defs} {B : BMap}
    (hfin : finalOK tabs f g M B = true)
    (hcg : closedOK g = true) {ρ ρ' : ID → Val} (hρ : ValRef ρ ρ')
    (hT : Term.Typed M.get? tabs ρ) :
    ∀ n x, LM g x → Live g x →
      Sem.Refines (den M.get? tabs ρ n x) (den (listedDefs g) tabs ρ' n x)
  | 0, _, _, _ => .poison _
  | n + 1, x, hx, hr => by
    have hmk := listedMarks_sound g x hx
    obtain ⟨b, hb, gb, hgb, hxv, -, -, -⟩ := id hmk
    obtain ⟨hlive, hfacts⟩ := finalOK_facts hfin
    obtain ⟨-, -, -, -, -, -, -, -, -, hvals⟩ := hfacts b hb gb hgb
    obtain ⟨m, u, hm, hu, hop, hty, hai, hax, hsz, hargs⟩ := hvals x hxv (.inl hr)
    have hL : listedDefs g x = some u := by rw [listedDefs_of_marked hmk, hu]
    have hcl := (closedOK_facts hcg b hb gb hgb).2 x hxv u hu
    by_cases ht : termOp m.op = true
    · rw [den_succ_term hm ht, den_succ_term hL (hop ▸ ht), hop, hty, hai, hax]
      apply retype_mono; apply GoFV.Proof.Rules.opVal_mono
      refine refinesList_idx (by simp [hsz]) fun j h1 h2 => ?_
      simp only [Array.getElem_toList]
      exact (copyReachW_den hT (hargs j (by simpa using h1) (by simpa using h2)) n).trans
        (final_den hfin hcg hρ hT n _ (hcl _ (Array.getElem_mem _))
          (live_arg hlive hb hgb hxv hu (.inr hr) (Array.getElem_mem _)))
    · have h1 : ¬ IsTerm M.get? x := fun ⟨w, hw, hw'⟩ => by
        rw [hm] at hw; cases hw; exact ht hw'
      have h2 : ¬ IsTerm (listedDefs g) x := fun ⟨w, hw, hw'⟩ => by
        rw [hL] at hw; cases hw; rw [hop] at hw'; exact ht hw'
      rw [den_succ_atom h1, den_succ_atom h2]
      exact hρ x

/-! ## The theorem -/

/-- **Validator soundness (term level)**: an output accepted by `RewriteCheck.validate` with the
table of a sound rule set has the arguments of its atoms refining, as terms over the atoms, those
of the input, and its terminators refining the input's as functions of their controls' terms. -/
theorem validate_termRef {tabs : Tables} {s : RuleSet} {f g : Func} {log : Array RwEvent}
    (hv : RewriteCheck.validate tabs (Interp.Table.ofRuleSet s) f g log = true)
    (hs : s.AllSound) :
    Term.AtomArgsRef tabs f g ∧ Term.TermStepRef tabs f g := by
  unfold validate at hv
  simp only [Bool.and_eq_true] at hv
  obtain ⟨⟨⟨hA, hcf⟩, hcg⟩, hv⟩ := hv
  have hbl : f.blocks = g.blocks := by
    unfold atomsOK at hA; simp only [Bool.and_eq_true, beq_iff_eq] at hA
    exact hA.1.1.2
  split at hv
  · rename_i M B hrep
    obtain ⟨C, hI, hB⟩ := replay_inv (D₀ := f.value?) (C₀ := LM f) hs log.toList _ M _ B _
      hrep (ReplayInv.init (marked_closed hcf)) (BInv.init tabs f (LM f))
    constructor
    · intro b hb gb hgb a ha u hu hat
      obtain ⟨fb, hfb, -, hatoms⟩ := atomsOK_facts hA b hb gb hgb
      obtain ⟨haf, u', hu', hop, hty, hai, hax, hsz⟩ := hatoms a ha u hu hat
      refine ⟨u', hu', hop, hty, hai, hax, hsz, fun i hi => ?_⟩
      have hbf : b ∈ f.blocks := hbl ▸ hb
      have hargsf := (closedOK_facts hcf b hbf fb hfb).2 a haf u' hu'
      obtain ⟨a'', ha'', -, hsz'', hrest⟩ := hI.atoms a u' hu' (hop ▸ hat) hargsf
      obtain ⟨hlive, hfacts⟩ := finalOK_facts hv
      obtain ⟨-, -, -, -, -, -, -, -, -, hvals⟩ := hfacts b hb gb hgb
      obtain ⟨m, w, hm, hw, -, -, -, -, hszw, hargs⟩ := hvals a ha
        (.inr fun w hw => by rw [hu] at hw; cases hw; exact hat)
      have hma : m = a'' := Option.some.inj (hm.symm.trans ha'')
      subst hma
      have huw : u = w := Option.some.inj (hu.symm.trans hw)
      subst huw
      have hi' : i < u'.args.size := hsz ▸ hi
      have hcopy := hargs i (by omega) hi
      have hmark := (closedOK_facts hcg b hb gb hgb).2 a ha u hu u.args[i] (Array.getElem_mem hi)
      intro n
      obtain ⟨k, hk⟩ := (hrest i hi').2 n
      refine ⟨k, fun ρ ρ' hρ hT _ => ?_⟩
      have hTM := hI.typed ρ hT
      rw [getElem!_pos u.args i hi]
      have h1 := hk ρ hT
      rw [getElem!_pos m.args i (by omega)] at h1
      exact h1.trans ((copyReachW_den hTM hcopy k).trans
        (final_den hv hcg hρ hTM k _ hmark (live_arg hlive hb hgb ha hu (.inl hat)
          (Array.getElem_mem hi))))
    · intro b hb fb gb hfb hgb
      obtain ⟨fb', hfb', hid, -⟩ := atomsOK_facts hA b hb gb hgb
      rw [hfb] at hfb'; obtain rfl := Option.some.inj hfb'
      obtain ⟨hlive, hfacts⟩ := finalOK_facts hv
      obtain ⟨st, fb'', hst, hfb'', hk, hsu, -, hsz, hctl, -⟩ := hfacts b hb gb hgb
      rw [hfb] at hfb''; obtain rfl := Option.some.inj hfb''
      have hbf : b ∈ f.blocks := hbl ▸ hb
      obtain ⟨hsw, -, hrel⟩ := hB b fb st hfb (closedOK_facts hcf b hbf fb hfb).1 hst
      refine ⟨fun e he => ?_, fun n => ?_⟩
      · rw [hsu]
        cases hs2 : st.swapped
        · simpa using he
        · have h2 := hsw hs2
          obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 he
          simp only [ite_true, swapS, List.mem_toArray, List.mem_cons, List.mem_singleton,
            List.not_mem_nil, or_false]
          have : j = 0 ∨ j = 1 := by omega
          rcases this with rfl | rfl
          · right; rw [getElem!_pos fb.succs 0 hj]
          · left; rw [getElem!_pos fb.succs 1 hj]
      · obtain ⟨m, hm⟩ := hrel n
        refine ⟨m, fun ρ ρ' hρ hT _ => ?_⟩
        have hTM := hI.typed ρ hT
        refine Res.Rel.trans_next (hm ρ hT) (stepVals_mono (b := stBlock fb st) hk ?_ hid.symm ?_)
        · rw [hsu]; rfl
        · refine refinesList_idx (by simp [hsz]) fun k h1 h2 => ?_
          simp only [Array.getElem_toList]
          have h1' : k < st.ctrls.size := by simpa using h1
          have h2' : k < gb.controls.size := by simpa using h2
          exact (copyReach_den hTM _ _ _ (hctl k h1' h2') m).trans (final_den hv hcg hρ hTM m _
            ((closedOK_facts hcg b hb gb hgb).1 _ (Array.getElem_mem h2'))
            (live_ctrl hlive hb hgb (Array.getElem_mem h2')))
  · cases hv

end GoFV.Proof.Pass.Rewrite
