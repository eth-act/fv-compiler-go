import GoFV.Proof.Pass.RewriteTermReplay

/-!
# Soundness of the rewrite validator at the term level (issue #113)

`validate_termRef`: if `RewriteCheck.validate` accepts the output `g` of a rewrite pass run with
the table of a sound rule set on `f`, then the arguments of `g`'s atoms and `g`'s controls
refine, as terms over the atoms (`GoFV.Proof.Term.TermRef`), those of `f`: the premises
`AtomArgsRef` and `ControlsRef` of the atom simulation (`GoFV.Proof.AtomSim`).

Proof: the values listed in `f` (`listedMarks`, closed under arguments by `closedOK f`) keep
refining denotations along the replay of the log (`replay_inv`); the final definitions are
those of `g` up to copies in arguments (`finalOK`), whose denotation (over the listed values
of `g`, closed by `closedOK g`) refines theirs (`final_den`); atoms keep their fields
(`atomsOK`).
-/

namespace GoFV.Proof.Pass.Rewrite

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt.RewriteCheck GoFV.Proof.Term GoFV.Proof.AtomSim
open GoFV.Rules (RuleSet RwEvent)

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
    g.block? b = some gb → ∃ fb, f.block? b = some fb ∧ fb.controls.size = gb.controls.size ∧
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
    obtain ⟨⟨⟨⟨-, -⟩, -⟩, hcs⟩, ⟨⟨hag, -⟩, -⟩⟩ := this
    refine ⟨fb, hfb, hcs, fun x hx w hw hwt => ?_⟩
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

theorem finalOK_facts {tabs : Tables} {f g : Func} {M : Defs} (h : finalOK tabs f g M = true) :
    ∀ b ∈ g.blocks, ∀ gb, g.block? b = some gb → ∃ fb, f.block? b = some fb ∧
      (∀ k (h1 : k < fb.controls.size) (h2 : k < gb.controls.size),
        copyReach tabs M M.size fb.controls[k] gb.controls[k] = true) ∧
      ∀ x ∈ gb.values, ∃ m u, M.get? x = some m ∧ g.value? x = some u ∧ u.op = m.op ∧
        u.type = m.type ∧ u.auxInt = m.auxInt ∧ u.aux = m.aux ∧ u.args.size = m.args.size ∧
        ∀ j (h1 : j < m.args.size) (h2 : j < u.args.size),
          copyReach tabs M M.size m.args[j] u.args[j] = true := by
  intro b hb gb hgb
  unfold finalOK at h
  have := (Array.all_eq_true_iff_forall_mem.1 h) b hb
  split at this
  · rename_i fb gb' hfb hgb'
    rw [hgb] at hgb'; obtain rfl := Option.some.inj hgb'
    simp only [Bool.and_eq_true] at this
    obtain ⟨hc, hv⟩ := this
    refine ⟨fb, hfb, fun k h1 h2 => ?_, fun x hx => ?_⟩
    · have := zip_all_get' (f := fun x : ID × ID => copyReach tabs M M.size x.1 x.2) hc k
        (by simpa using h1) (by simpa using h2)
      simpa using this
    · have := (Array.all_eq_true_iff_forall_mem.1 hv) x hx
      split at this
      · rename_i m u hm hu
        simp only [Bool.and_eq_true, beq_iff_eq] at this
        obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, hop⟩, hty⟩, hai⟩, hax⟩, hsz⟩, hargs⟩ := this
        refine ⟨m, u, hm, hu, hop, hty, hai, hax, hsz, fun j h1 h2 => ?_⟩
        have := zip_all_get (f := fun x : ID × ID => copyReach tabs M M.size x.1 x.2) hargs
          (by simp [hsz]) j (by simpa using h1) (by simpa using h2)
        simpa using this
      · cases this
  · cases this

end GoFV.Proof.Pass.Rewrite
