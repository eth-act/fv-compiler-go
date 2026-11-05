import GoFV.Proof.Low.ValReplay

/-!
# Soundness of the lowering validator at the term level (issue #385)

`validateL_termRef`: if `GoFV.Opt.LowerCheck.validateL` accepts the output `g` of a lowering
rewrite run with the table of a sound lowering rule set (`ArmRuleSet.AllSound`) on `f`, then the
arguments of `g`'s atoms refine, as terms over the atoms in lowered mode, those of the atoms of `f`
they correspond to (`AtomArgsRefL`), and `g`'s terminators refine `f`'s as functions of their
controls' terms (`TermStepRefL`): the premises of the atom simulation. `validateL_parts`: the
other facts `validateL` checks.

Proof (as Phase 1's `GoFV.Proof.Pass.Rewrite.validate_termRef`): `f` is read in its own mode
(`f.lowered`); the valuation `midVal` shapes `f`'s atoms by `Val.retypeL` at their lowered shapes,
so that `f`'s denotations refine their lowered reading (`bridge_den`: `shapesOK` makes the
shapes agree, `retype_le_retypeL`). Along the replay the listed values of `f` keep refining
lowered denotations (`replayL_inv`); the final definitions and terminators are `g`'s up to copies
(`finalOKL`), whose lowered denotation over the listed values of `g` refines theirs
(`final_denL`); `midVal` at an atom listed in `g` is refined by the target valuation, since the
atom of `g` has the type of `f`'s (`atomsOKL`, `mid_le_target`).
-/

namespace GoFV.Proof.Low.Val

open GoFV.SSA GoFV.SSA.Sem GoFV.Rules GoFV.Opt.RewriteCheck GoFV.Opt.LowerCheck GoFV.Proof.Term
open GoFV.Proof.Low
open GoFV.Proof.Pass.Rewrite (LM Marked listedMarks_sound listedDefs_of_marked closedOK_facts
  marked_closed zip_all_get zip_all_get' refinesList_idx)

/-! ## `atomsOKL`, `liveOKL`, `finalOKL` -/

theorem termVL_congr {tabs : Tables} {u m : Value} (hop : u.op = m.op) (hai : u.auxInt = m.auxInt)
    (hax : u.aux = m.aux) : termVL tabs u = termVL tabs m := by
  unfold termVL; rw [hop, hai, hax]

theorem atomsOKL_facts {tabs : Tables} {f g : Func} (h : atomsOKL tabs f g = true) :
    f.blocks = g.blocks ∧ ∀ b ∈ g.blocks, ∀ gb, g.block? b = some gb → ∃ fb, f.block? b = some fb ∧
      fb.id = gb.id ∧ ∀ x ∈ gb.values, ∀ w, g.value? x = some w → termVL tabs w = false →
        x ∈ fb.values ∧ ∃ u, f.value? x = some u ∧ atomPair tabs u w = true ∧ termVL tabs u = false := by
  unfold atomsOKL at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨-, hbl⟩, -⟩, h⟩ := h
  refine ⟨hbl, fun b hb gb hgb => ?_⟩
  have := (Array.all_eq_true_iff_forall_mem.1 h) b (hbl ▸ hb)
  rw [hgb] at this
  split at this
  · rename_i fb gb' hfb hgb'
    obtain rfl := Option.some.inj hgb'
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at this
    obtain ⟨hid, ⟨hag, -⟩, -⟩ := this
    refine ⟨fb, hfb, hid, fun x hx w hw hwt => ?_⟩
    have hxa : x ∈ atomsOfL tabs g gb := by
      simp only [atomsOfL, List.mem_filter, Array.mem_toList_iff, hw, isAtomL, hwt]
      exact ⟨hx, rfl⟩
    have := hag x hxa
    simp only [List.contains_iff_mem] at this
    obtain ⟨hxf, hfd⟩ := this
    simp only [atomsOfL, List.mem_filter, Array.mem_toList_iff] at hxf
    obtain ⟨hxf, hat⟩ := hxf
    refine ⟨hxf, ?_⟩
    rw [hw] at hfd
    split at hfd
    · rename_i u w' hu hw'
      obtain rfl := Option.some.inj hw'
      rw [hu] at hat
      simp only [isAtomL, Bool.not_eq_true'] at hat
      exact ⟨u, hu, hfd, hat⟩
    · cases hfd
  · cases this

theorem atomPair_type {tabs : Tables} {u w : Value} (h : atomPair tabs u w = true) :
    u.type = w.type := by
  unfold atomPair at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.1.2

/-- `x` is marked by `liveMarksL tabs h` (read by the output). -/
def LiveL (tabs : Tables) (h : Func) (x : ID) : Prop := (liveMarksL tabs h)[x]? = some true

theorem liveOKL_facts {tabs : Tables} {h : Func} {L : Array Bool} (hl : liveOKL tabs h L = true) :
    ∀ b ∈ h.blocks, ∀ hb, h.block? b = some hb → (∀ c ∈ hb.controls, L[c]? = some true) ∧
      ∀ x ∈ hb.values, ∀ u, h.value? x = some u → (termVL tabs u = false ∨ L[x]? = some true) →
        ∀ a ∈ u.args, L[a]? = some true := by
  intro b hb hbk hbb
  unfold liveOKL at hl
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

theorem finalOKL_facts {tabs : Tables} {f g : Func} {M : Defs} {B : BMapL}
    (h : finalOKL tabs f g M B = true) : liveOKL tabs g (liveMarksL tabs g) = true ∧
    ∀ b ∈ g.blocks, ∀ gb, g.block? b = some gb → ∃ st fb, bstateL f B b = some st ∧
      f.block? b = some fb ∧ gb.kind = st.kind ∧ gb.auxInt = st.auxInt ∧
      gb.succs = (if st.swapped then swapS fb.succs else fb.succs) ∧
      (st.swapped = true → fb.succs.size = 2) ∧ gb.controls.size = st.ctrls.size ∧
      (∀ k (h1 : k < st.ctrls.size) (h2 : k < gb.controls.size),
        copyReachL tabs M M.size st.ctrls[k] gb.controls[k] = true) ∧
      ∀ x ∈ gb.values, (LiveL tabs g x ∨ ∀ u, g.value? x = some u → termVL tabs u = false) →
        ∃ m u, M.get? x = some m ∧ g.value? x = some u ∧ u.op = m.op ∧
        u.type = m.type ∧ u.auxInt = m.auxInt ∧ u.aux = m.aux ∧ u.args.size = m.args.size ∧
        ∀ j (h1 : j < m.args.size) (h2 : j < u.args.size),
          copyReachL tabs M M.size m.args[j] u.args[j] = true := by
  unfold finalOKL at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hlive, h⟩ := h
  refine ⟨hlive, fun b hb gb hgb => ?_⟩
  have := (Array.all_eq_true_iff_forall_mem.1 h) b hb
  split at this
  · rename_i st fb gb' hst hfb hgb'
    rw [hgb] at hgb'; obtain rfl := Option.some.inj hgb'
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    obtain ⟨⟨⟨⟨⟨hk, hai⟩, hsu⟩, hsz⟩, hc⟩, hv⟩ := this
    have hsu' : gb.succs = (if st.swapped then swapS fb.succs else fb.succs) ∧
        (st.swapped = true → fb.succs.size = 2) := by
      cases hsw : st.swapped <;> simp only [hsw, ite_true, ite_false, Bool.false_eq_true] at hsu ⊢
      · exact ⟨beq_iff_eq.1 hsu, fun h => h.elim⟩
      · simp only [Bool.and_eq_true, beq_iff_eq] at hsu
        exact ⟨hsu.2, fun _ => hsu.1⟩
    refine ⟨st, fb, hst, hfb, hk, hai, hsu'.1, hsu'.2, hsz, fun k h1 h2 => ?_, fun x hx hrd => ?_⟩
    · have := zip_all_get' (f := fun x : ID × ID => copyReachL tabs M M.size x.1 x.2) hc k
        (by simpa using h1) (by simpa using h2)
      simpa using this
    · have := (Array.all_eq_true_iff_forall_mem.1 hv) x hx
      split at this
      · rename_i m u hm hu
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at this
        rcases this with this | ⟨ht, hr⟩
        · obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, hop⟩, hty⟩, hai⟩, hax⟩, hsz⟩, hargs⟩ := this
          refine ⟨m, u, hm, hu, hop, hty, hai, hax, hsz, fun j h1 h2 => ?_⟩
          have := zip_all_get (f := fun x : ID × ID => copyReachL tabs M M.size x.1 x.2) hargs
            (by simp [hsz]) j (by simpa using h1) (by simpa using h2)
          simpa using this
        · rcases hrd with hrd | hrd
          · exact absurd hrd hr
          · rw [hrd u hu] at ht; cases ht
      · cases this
  · cases this

/-! ## The final definitions -/

/-- The replayed definitions refine, in lowered mode, those listed in `g` and read by `g` (up to
the copies `finalOKL` allows), for valuations related at `g`'s listed atoms. -/
theorem final_denL {tabs : Tables} {f g : Func} {M : Defs} {B : BMapL}
    (hfin : finalOKL tabs f g M B = true) (hcg : closedOK g = true) {ρ ρ' : ID → Val}
    (hρ : ∀ a u, listedDefs g a = some u → termVL tabs u = false → Sem.Refines (ρ a) (ρ' a))
    (hT : TypedL true M.get? tabs ρ) :
    ∀ n x, LM g x → LiveL tabs g x →
      Sem.Refines (denL true M.get? tabs ρ n x) (denL true (listedDefs g) tabs ρ' n x)
  | 0, _, _, _ => .poison _
  | n + 1, x, hx, hr => by
    have hmk := listedMarks_sound g x hx
    obtain ⟨b, hb, gb, hgb, hxv, -, -, -⟩ := id hmk
    obtain ⟨hlive, hfacts⟩ := finalOKL_facts hfin
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hvals⟩ := hfacts b hb gb hgb
    obtain ⟨m, u, hm, hu, hop, hty, hai, hax, hsz, hargs⟩ := hvals x hxv (.inl hr)
    have hL : listedDefs g x = some u := by rw [listedDefs_of_marked hmk, hu]
    have hcl := (closedOK_facts hcg b hb gb hgb).2 x hxv u hu
    have htt := termVL_congr (tabs := tabs) hop hai hax
    by_cases ht : termVL tabs m = true
    · rw [denT_succ hm ht, denT_succ hL (htt ▸ ht), hop, hty, hai, hax]
      apply retypeL_mono; apply opValL_mono_term ht
      refine refinesList_idx (by simp [hsz]) fun j h1 h2 => ?_
      simp only [Array.getElem_toList]
      exact (copyReachL_den hT _ _ _ (hargs j (by simpa using h1) (by simpa using h2)) n).trans
        (final_denL hfin hcg hρ hT n _ (hcl _ (Array.getElem_mem _))
          ((liveOKL_facts hlive) b hb gb hgb |>.2 x hxv u hu (.inr hr) _ (Array.getElem_mem _)))
    · have hmf : termVL tabs m = false := by simpa using ht
      have h1 : ¬ IsTermL tabs M.get? x := fun ⟨w, hw, hw'⟩ => by
        rw [hm] at hw; cases hw; exact ht hw'
      have h2 : ¬ IsTermL tabs (listedDefs g) x := fun ⟨w, hw, hw'⟩ => by
        rw [hL] at hw; cases hw; rw [htt] at hw'; exact ht hw'
      rw [denL_succ_atom h1, denL_succ_atom h2]
      exact hρ x u hL (htt ▸ hmf)

/-! ## From `f`'s mode to lowered mode -/

/-- The valuation of `f`'s atoms read in lowered mode: shaped by `Val.retypeL` at their lowered
shapes. -/
def midVal (tabs : Tables) (f : Func) (ρ : ID → Val) (a : ID) : Val :=
  match f.value? a with
  | some u => if termVL tabs u then ρ a else (ρ a).retypeL (shpL tabs u.type)
  | none => ρ a

theorem shapesOK_get {tabs : Tables} {f : Func} (h : shapesOK tabs f = true) {x : ID} {v : Value}
    (hv : f.value? x = some v) : shpL tabs v.type = tabs.ty v.type := by
  unfold Func.value? at hv
  have ho : f.valueTab[x]? = some (some v) := Option.join_eq_some_iff.1 hv
  have hm := Array.mem_of_getElem? ho
  have := (Array.all_eq_true_iff_forall_mem.1 h) _ hm
  exact GoFV.Proof.Pass.Rewrite.tyEq_sound this

theorem mid_typed (tabs : Tables) (f : Func) (ρ : ID → Val) :
    TypedL true f.value? tabs (midVal tabs f ρ) := by
  intro a ha hsome
  cases hu : f.value? a with
  | none => rw [hu] at hsome; cases hsome
  | some u =>
    have hut : termVL tabs u = false := by
      cases h : termVL tabs u
      · rfl
      · exact absurd ⟨u, hu, h⟩ ha
    rw [shapeL_of hu]
    simp only [midVal, hu, hut, Bool.false_eq_true, ite_false]
    exact retypeL_idem _ _

/-- `midVal` keeps the frame addresses of `f`'s `LocalAddr`s (`FrameVals`): `poison` and an
address word at a word shape are fixed by `retypeL` there. -/
theorem mid_frame {tabs : Tables} {f : Func} {ρ : ID → Val} {act : Nat}
    (hF : FrameVals tabs act f.value? ρ) : FrameVals tabs act f.value? (midVal tabs f ρ) := by
  intro a l n hl hop hax
  have hlt : termVL tabs l = false := termVL_localAddr tabs l hop
  simp only [midVal, hl, hlt, Bool.false_eq_true, ite_false]
  rcases hF a l n hl hop hax with h | ⟨h, hw⟩
  · exact .inl (by rw [h]; exact retypeL_poison _)
  · exact .inr ⟨by rw [h]; exact word_retypeL (wordShape_cases hw) _, hw⟩

theorem mid_le {tabs : Tables} {f : Func} {ρ : ID → Val}
    (hsh : f.lowered = true ∨ shapesOK tabs f = true) (hT : TypedL f.lowered f.value? tabs ρ) :
    ∀ a, ¬ IsTermL tabs f.value? a → Sem.Refines (ρ a) (midVal tabs f ρ a) := by
  intro a ha
  cases hu : f.value? a with
  | none => simp only [midVal, hu]; exact Sem.Refines.refl _
  | some u =>
    have hut : termVL tabs u = false := by
      cases h : termVL tabs u
      · rfl
      · exact absurd ⟨u, hu, h⟩ ha
    simp only [midVal, hu, hut, Bool.false_eq_true, ite_false]
    have h1 := hT a ha (by rw [hu]; rfl)
    simp only [shapeL, hu, Option.map_some, Option.getD_some] at h1
    cases hl : f.lowered
    · rw [hl] at h1
      have hs : shpL tabs u.type = tabs.ty u.type := by
        rcases hsh with h | h
        · rw [hl] at h; cases h
        · exact shapesOK_get h hu
      rw [hs]
      have h1' : (ρ a).retype (tabs.ty u.type) = ρ a := h1
      conv => lhs; rw [← h1']
      exact retype_le_retypeL _ _
    · rw [hl] at h1
      have h1' : (ρ a).retypeL (shpL tabs u.type) = ρ a := h1
      rw [h1']; exact Sem.Refines.refl _

/-- **The bridge**: `f`'s terms in its own mode refine their lowered reading under `midVal`. -/
theorem bridge_den {tabs : Tables} {f : Func} {ρ : ID → Val}
    (hsh : f.lowered = true ∨ shapesOK tabs f = true) (hT : TypedL f.lowered f.value? tabs ρ) :
    ∀ n x, Sem.Refines (denL f.lowered f.value? tabs ρ n x)
      (denL true f.value? tabs (midVal tabs f ρ) n x)
  | 0, _ => .poison _
  | n + 1, x => by
    by_cases ht : IsTermL tabs f.value? x
    · obtain ⟨v, hv, hvt⟩ := ht
      rw [denL_succ_term hv hvt, denT_succ hv hvt]
      have hshp : shp f.lowered tabs v.type = shpL tabs v.type := by
        unfold shp
        cases hl : f.lowered
        · rcases hsh with h | h
          · rw [hl] at h; cases h
          · exact (shapesOK_get h hv).symm
        · rfl
      rw [hshp]
      have hargs := opValL_mono_term hvt (shpL tabs v.type)
        (GoFV.Proof.AtomSim.refinesList_map (l := v.args.toList)
          fun a _ => bridge_den hsh hT n a)
      unfold rty
      revert hargs
      cases f.lowered <;> intro hargs <;> simp only [Bool.false_eq_true, ite_false, ite_true]
      · exact (retype_mono _ hargs).trans (retype_le_retypeL _ _)
      · exact retypeL_mono _ hargs
    · rw [denL_succ_atom ht, denL_succ_atom ht]
      exact mid_le hsh hT x ht

/-- `midVal` at an atom listed in `g` is refined by a target valuation fixed at `g`'s atoms. -/
theorem mid_le_target {tabs : Tables} {f g : Func} (hA : atomsOKL tabs f g = true)
    {ρ ρ' : ID → Val} (hρ : ValRef ρ ρ') (hT' : TypedL true (listedDefs g) tabs ρ') :
    ∀ a u, listedDefs g a = some u → termVL tabs u = false →
      Sem.Refines (midVal tabs f ρ a) (ρ' a) := by
  intro a u hL hut
  unfold listedDefs at hL
  cases hg : g.value? a with
  | none => rw [hg] at hL; cases hL
  | some w =>
    rw [hg] at hL
    simp only [Option.filter, Bool.and_eq_true, List.contains_iff_mem] at hL
    split at hL
    · rename_i hc
      have hwu := Option.some.inj hL
      subst hwu
      obtain ⟨hb, hbv⟩ := hc
      have hb' : w.block ∈ g.blocks := by simpa using hb
      cases hgb : g.block? w.block with
      | none => rw [hgb] at hbv; cases hbv
      | some gb =>
        rw [hgb] at hbv
        simp only [Option.any_some, Array.contains_iff_mem] at hbv
        obtain ⟨fb, -, -, hat⟩ := (atomsOKL_facts hA).2 w.block hb' gb hgb
        obtain ⟨-, u', hu', hp, hu't⟩ := hat a hbv w hg hut
        have hty := atomPair_type hp
        simp only [midVal, hu', hu't, Bool.false_eq_true, ite_false]
        have hL' : listedDefs g a = some w := by
          simp [listedDefs, hg, Option.filter, hb, hb', hgb, hbv]
        have hnt : ¬ IsTermL tabs (listedDefs g) a := fun ⟨y, hy, hy'⟩ => by
          rw [hL'] at hy; cases hy; rw [hut] at hy'; cases hy'
        have h1 := hT' a hnt (by rw [hL']; rfl)
        rw [shapeL_of hL'] at h1
        have h1' : (ρ' a).retypeL (shpL tabs w.type) = ρ' a := h1
        rw [hty, ← h1']
        exact retypeL_mono _ (hρ a)
    · cases hL

/-! ## The theorems -/

/-- The facts `validateL` checks besides the replay. -/
theorem _root_.GoFV.Proof.Low.validateL_parts {tabs : Tables} {t : GoFV.Rules.Interp.Table}
    {f g : Func} {log : Array RwEvent} (hv : validateL tabs t f g log = true) :
    g.lowered = true ∧ (f.lowered = true ∨ shapesOK tabs f = true) ∧
    atomsOKL tabs f g = true ∧ closedOK f = true ∧ closedOK g = true := by
  unfold validateL at hv
  simp only [Bool.and_eq_true, Bool.or_eq_true] at hv
  obtain ⟨⟨⟨⟨⟨hg, hf⟩, hA⟩, hcf⟩, hcg⟩, -⟩ := hv
  exact ⟨hg, hf, hA, hcf, hcg⟩

/-- **Validator soundness (term level)**: an output accepted by `validateL` with the table of a
sound lowering rule set has the arguments of its atoms refining, as lowered terms over the atoms,
those of the input's corresponding atoms, and its terminators refining the input's as functions
of their controls' terms. -/
theorem _root_.GoFV.Proof.Low.validateL_termRef {s : RuleSet} (hs : ArmRuleSet.AllSound s)
    {tabs : Tables} {f g : Func} {log : Array RwEvent}
    (hv : validateL tabs (GoFV.Rules.Interp.Table.ofRuleSet s) f g log = true) :
    AtomArgsRefL tabs f g ∧ TermStepRefL tabs f g := by
  obtain ⟨hgl, hsh, hA, hcf, hcg⟩ := validateL_parts hv
  unfold validateL at hv
  simp only [Bool.and_eq_true] at hv
  obtain ⟨-, hv⟩ := hv
  obtain ⟨hbl, hAf⟩ := atomsOKL_facts hA
  split at hv
  · rename_i M B hrep
    obtain ⟨C, hI, hB⟩ := replayL_inv (D₀ := f.value?) (C₀ := LM f) hs (fun _ => rfl) log.toList
      _ M _ B _ hrep (ReplayInvL.init (marked_closed hcf)) (BInvL.init tabs f (LM f))
    obtain ⟨hlive, hfacts⟩ := finalOKL_facts hv
    have hTM : ∀ ρ, TypedL true M.get? tabs (midVal tabs f ρ) :=
      fun ρ => hI.typed _ (mid_typed tabs f ρ)
    constructor
    · intro b hb gb hgb a ha u hu hat
      obtain ⟨fb, hfb, -, hatoms⟩ := hAf b hb gb hgb
      obtain ⟨haf, u', hu', hp, hu't⟩ := hatoms a ha u hu hat
      refine ⟨u', hu', hp, ?_⟩
      have hbf : b ∈ f.blocks := hbl ▸ hb
      have hargsf := (closedOK_facts hcf b hbf fb hfb).2 a haf u' hu'
      obtain ⟨a'', ha'', -, hrest⟩ := hI.atoms a u' hu' hu't hargsf
      obtain ⟨-, -, -, -, -, -, -, -, -, -, hvals⟩ := hfacts b hb gb hgb
      obtain ⟨m, w, hm, hw, hop, -, hai, hax, hszw, hargs⟩ := hvals a ha
        (.inr fun w hw => by rw [hu] at hw; cases hw; exact hat)
      have hma : m = a'' := Option.some.inj (hm.symm.trans ha'')
      subst hma
      have huw : u = w := Option.some.inj (hu.symm.trans hw)
      subst huw
      rcases hrest with hfree | ⟨hsz'', hrest⟩
      · exact .inl (by rw [argFree_congr hop hax]; exact hfree)
      refine .inr fun i hi => ?_
      have hi' : i < u'.args.size := by omega
      have hcopy := hargs i (by omega) hi
      have hmark := (closedOK_facts hcg b hb gb hgb).2 a ha u hu u.args[i] (Array.getElem_mem hi)
      have hlv : LiveL tabs g u.args[i] :=
        (liveOKL_facts hlive) b hb gb hgb |>.2 a ha u hu (.inl hat) _ (Array.getElem_mem hi)
      intro n
      obtain ⟨k, hk⟩ := (hrest i hi').2 n
      refine ⟨k, fun ρ ρ' hρ hT hT' hF => ?_⟩
      rw [hgl] at hT'
      rw [hgl, getElem!_pos u.args i hi]
      have h1 := hk (midVal tabs f ρ) (mid_typed tabs f ρ) (mid_frame hF)
      rw [getElem!_pos m.args i (by omega),
        stArg_congr (u := u') (i := i) hop.symm hai.symm hax.symm] at h1
      exact ArgRel.trans_left (bridge_den hsh hT n _) (h1.trans_right
        ((copyReachL_den (hTM ρ) _ _ _ hcopy k).trans
          (final_denL hv hcg (mid_le_target hA hρ hT') (hTM ρ) k _ hmark hlv)))
    · intro b hb fb gb hfb hgb
      obtain ⟨fb', hfb', hid, -⟩ := hAf b hb gb hgb
      rw [hfb] at hfb'; obtain rfl := Option.some.inj hfb'
      obtain ⟨st, fb'', hst, hfb'', hk, hai, hsu, -, hsz, hctl, -⟩ := hfacts b hb gb hgb
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
        refine ⟨m, fun ρ ρ' hρ hT hT' hF => ?_⟩
        rw [hgl] at hT' ⊢
        refine Res.Rel.trans_next (stepValsL_mono rfl rfl rfl rfl
          (GoFV.Proof.AtomSim.refinesList_map fun c _ => bridge_den hsh hT n c)) ?_
        refine Res.Rel.trans_next (hm (midVal tabs f ρ) (mid_typed tabs f ρ) (mid_frame hF))
          (stepValsL_mono (b := stBlockL fb st) hk hai hsu hid.symm ?_)
        refine refinesList_idx (by simp [hsz]) fun k h1 h2 => ?_
        simp only [Array.getElem_toList]
        have h1' : k < st.ctrls.size := by simpa using h1
        have h2' : k < gb.controls.size := by simpa using h2
        exact (copyReachL_den (hTM ρ) _ _ _ (hctl k h1' h2') m).trans
          (final_denL hv hcg (mid_le_target hA hρ hT') (hTM ρ) m _
            ((closedOK_facts hcg b hb gb hgb).1 _ (Array.getElem_mem h2'))
            ((liveOKL_facts hlive) b hb gb hgb |>.1 _ (Array.getElem_mem h2')))
  · cases hv

end GoFV.Proof.Low.Val
