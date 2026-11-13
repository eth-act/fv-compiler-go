import GoFV.Opt.CopyZero
import GoFV.Proof.Pass.CopyElimPass
import GoFV.Proof.AtomSim

variable [GoFV.SSA.Sem.Addrs]

/-!
# copyelim on zero-size values (issue #69)

`copyelim_refines_zero`: when `CopyZero.zeroGuard` accepts the input `f`, copyelim's output
refines `f` under monotone contracts. The output `g` is related by copyelim's relation to
`k := zeroReset tabs f` (`copyRelB_sound`), and `k` lies in the old fragment `EmptyFrag`, so `g`
refines `k` (`CopyElim.refines_of_rel`). `k` refines `f` by the atom simulation
(`AtomSim.atomSim_refines`). The two have the same atoms with the same fields
(`atomArgsRef_zeroReset`) and the same controls (`termStepRef_zeroReset`), and every listed value
of `k` refines `f`'s as a term (`den_zeroReset`). A reset value is `Empty`, i.e. `.empty`, and the
source value of shape `empty` it replaces is `.empty` or `poison` (`refines_retype_empty`).
-/

namespace GoFV.Proof.CopyZero

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.CopyZero GoFV.Proof.CopyElim GoFV.Proof.Term GoFV.Proof.Dom

/-! ## `copyRelB` decides `CopyRel` -/

theorem argRelB_sound {g : Func} {a w : ID} (h : argRelB g a w = true) : ArgRel g a w := by
  unfold argRelB at h
  simp only [Bool.or_eq_true, beq_iff_eq, Option.any_eq_true, Bool.and_eq_true] at h
  rcases h with h | ⟨u, hu, hop, hargs⟩
  · exact .inl h
  · exact .inr ⟨u, hu, hop, hargs⟩

theorem zeroSizeB_sound {tabs : Tables} {t : TypeRef} (h : zeroSizeB tabs t = true) :
    zeroSizeAggregate tabs t = .ok true := by
  unfold zeroSizeB at h
  split at h
  · assumption
  · cases h

theorem valRelB_sound {tabs : Tables} {g : Func} {kv gv : Value} (h : valRelB tabs g kv gv = true) :
    ValRel tabs g kv gv := by
  unfold valRelB at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Array.all_eq_true_iff_forall_mem, Array.isEmpty_iff] at h
  rcases h with (⟨⟨⟨⟨hop, hax⟩, hai⟩, hsz⟩, hall⟩ | ⟨⟨⟨hph, hcp⟩, h1⟩, hargs⟩) | ⟨⟨hz, he⟩, hn⟩
  · refine .same hop hax hai hsz fun k a ha => ?_
    obtain ⟨hk, hka⟩ := Array.getElem?_eq_some_iff.1 ha
    have hkg : k < gv.args.size := by omega
    refine ⟨gv.args[k], by simp [hkg], ?_⟩
    have := argRelB_sound (hall k hk)
    rwa [getElem!_pos kv.args k hk, getElem!_pos gv.args k hkg, hka] at this
  · have hw : gv.args = #[gv.args[0]!] := by
      apply Array.ext
      · simp [h1]
      · intro j hj _
        simp [h1] at hj; subst hj; simp [getElem!_pos gv.args 0 (by omega)]
    exact .phi _ hph hcp hw fun a ha => argRelB_sound (hargs a ha)
  · exact .empty (zeroSizeB_sound hz) he hn

theorem valueRelB_sound {tabs : Tables} {k g : Func} {x : ID} (H : valueRelB tabs k g x = true) :
    (∀ kv, k.value? x = some kv → ∃ gv, g.value? x = some gv ∧ gv.block = kv.block ∧
      gv.type = kv.type ∧ ValRel tabs g kv gv) ∧
    (∀ gv w, g.value? x = some gv → gv.op = .Copy → gv.args = #[w] →
      ∃ wv, g.value? w = some wv ∧ RetypeInto (tabs.ty wv.type) (tabs.ty gv.type)) := by
  unfold valueRelB at H
  rw [Bool.and_eq_true] at H
  obtain ⟨H1, H2⟩ := H
  constructor
  · intro kv hkv
    rw [hkv] at H1
    cases hgv : g.value? x with
    | none => rw [hgv] at H1; cases H1
    | some gv =>
      rw [hgv] at H1
      simp only [Bool.and_eq_true, beq_iff_eq] at H1
      exact ⟨gv, rfl, H1.1.1, H1.1.2, valRelB_sound H1.2⟩
  · intro gv w hgv hop hargs
    rw [hgv] at H2
    simp only [Option.all_some, Bool.or_eq_true, bne_iff_ne, ne_eq] at H2
    have hsz : gv.args.size = 1 := by rw [hargs]; rfl
    have h0 : gv.args[0]! = w := by rw [hargs]; rfl
    rcases H2 with (h | h) | h
    · exact absurd hop h
    · exact absurd hsz h
    · rw [h0] at h
      obtain ⟨wv, hwv, hr⟩ := (Option.any_eq_true _ _).1 h
      exact ⟨wv, hwv, retypeIntoB_sound hr⟩

/-- **`copyRelB` decides copyelim's relation.** -/
theorem copyRelB_sound {tabs : Tables} {k g : Func} (H : copyRelB tabs k g = true) :
    CopyRel tabs k g := by
  unfold copyRelB at H
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true'] at H
  obtain ⟨⟨⟨hcfg, hown⟩, hsz⟩, hbl⟩ := H
  have hblk : ∀ bid ∈ k.blocks, ((DomCert.make k).depthOf bid).isSome → ∀ kb,
      k.block? bid = some kb →
      ∃ gb, g.block? bid = some gb ∧ gb.kind = kb.kind ∧ gb.values = kb.values ∧
        gb.controls.size = kb.controls.size ∧
        (∀ i < kb.controls.size, argRelB g kb.controls[i]! gb.controls[i]! = true) ∧
        ∀ x ∈ kb.values, valueRelB tabs k g x = true := by
    intro bid hb ht kb hkb
    have := hbl bid hb
    simp only [DomCert.Cert.inTree, ht, Bool.not_true, Bool.false_or, hkb] at this
    cases hgb : g.block? bid with
    | none => rw [hgb] at this; cases this
    | some gb =>
      rw [hgb] at this
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
        Array.all_eq_true'] at this
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := this
      exact ⟨gb, rfl, h1, h2, h3, h4, h5⟩
  refine ⟨hcfg, hown, hsz, ?_, ?_, ?_⟩
  · intro bid hb ht kb hkb
    obtain ⟨gb, hgb, h1, h2, h3, h4, -⟩ := hblk bid hb ht kb hkb
    refine ⟨gb, hgb, h1, h2, h3, fun j c hc => ?_⟩
    obtain ⟨hj, hjc⟩ := Array.getElem?_eq_some_iff.1 hc
    have hjg : j < gb.controls.size := by omega
    refine ⟨gb.controls[j], by simp [hjg], ?_⟩
    have := argRelB_sound (h4 j hj)
    rwa [getElem!_pos kb.controls j hj, getElem!_pos gb.controls j hjg, hjc] at this
  · intro bid hb ht kb hkb x hx kv hkv
    obtain ⟨-, -, -, -, -, -, h5⟩ := hblk bid hb ht kb hkb
    exact (valueRelB_sound (h5 x hx)).1 kv hkv
  · intro bid hb ht kb hkb x hx gv w hgv hop hargs
    obtain ⟨-, -, -, -, -, -, h5⟩ := hblk bid hb ht kb hkb
    exact (valueRelB_sound (h5 x hx)).2 gv w hgv hop hargs

/-! ## `zeroReset` -/

section
variable (tabs : Tables) (f : Func)

theorem zeroReset_blocks : (zeroReset tabs f).blocks = f.blocks := rfl
theorem zeroReset_block? (b : ID) : (zeroReset tabs f).block? b = f.block? b := rfl
theorem zeroReset_cfgView : DomCert.cfgView (zeroReset tabs f) = DomCert.cfgView f := rfl

/-- A value of `zeroReset tabs f` is `f`'s, `zr`-reset, with some use count. -/
theorem zeroReset_value? (x : ID) :
    ∃ n, (zeroReset tabs f).value? x = (f.value? x).map fun v => { zr tabs v with uses := n } := by
  refine ⟨(useTab { f with valueTab := f.valueTab.map (·.map (zr tabs)) })[x]!, ?_⟩
  unfold zeroReset Func.value?
  simp only [Array.getElem?_mapIdx, Array.getElem?_map]
  cases f.valueTab[x]? with
  | none => rfl
  | some o => cases o <;> rfl

end

theorem resetB_ty {tabs : Tables} {v : Value} (h : resetB tabs v = true) : tabs.ty v.type = .empty := by
  unfold resetB at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨-, h⟩, -⟩ := h
  split at h
  · assumption
  · cases h

theorem resetB_term {tabs : Tables} {v : Value} (h : resetB tabs v = true) :
    RewriteCheck.termOp v.op = true := by
  unfold resetB at h
  simp only [Bool.and_eq_true] at h
  exact h.2

/-- A value retyped at shape `empty` is `.empty` or `poison`: it refines `.empty`. -/
theorem refines_retype_empty (y : Val) : Sem.Refines (y.retype .empty) .empty := by
  cases y <;> first | exact .empty | exact .poison _

theorem opVal_empty (tabs : Tables) :
    (GoFV.Proof.Rules.opVal tabs .Empty .empty 0 none []).retype .empty = .empty := by
  rfl

private theorem listedDefs_of {g : Func} {c : ID} {cv : Value} (hc : g.value? c = some cv)
    (hl : g.blocks.contains cv.block = true ∧ (g.block? cv.block).any (·.values.contains c) = true) :
    listedDefs g c = some cv := by
  simp only [listedDefs, hc, Option.filter, hl.1, hl.2, Bool.and_self, ↓reduceIte]

/-- **Every listed value of `zeroReset tabs f` refines `f`'s as a term.** -/
theorem den_zeroReset {ce : CheckEnv} {tabs : Tables} {f : Func} (hwf : WF ce f)
    (ρ ρ' : ID → Val) (hρ : ValRef ρ ρ') :
    ∀ n x, Listed f x →
      Sem.Refines (den f.value? tabs ρ n x) (den (listedDefs (zeroReset tabs f)) tabs ρ' n x)
  | 0, _, _ => .poison _
  | n + 1, x, ⟨bid, b, hb, hx⟩ => by
    obtain ⟨fv, hfv, -, hblk⟩ := hwf.valueId bid b hb x hx
    obtain ⟨u, hu⟩ := zeroReset_value? tabs f x
    rw [hfv, Option.map_some] at hu
    have hl : listedDefs (zeroReset tabs f) x = some { zr tabs fv with uses := u } := by
      apply listedDefs_of hu
      have hzb : (zr tabs fv).block = fv.block := by unfold zr; split <;> rfl
      simp only [hzb, hblk, zeroReset_blocks, zeroReset_block?, hb.2, Option.any_some]
      exact ⟨Array.contains_iff_mem.2 hb.1, Array.contains_iff_mem.2 hx⟩
    by_cases hr : resetB tabs fv = true
    · have hz : zr tabs fv = { fv with op := .Empty, args := #[], auxInt := 0, aux := none } := by
        unfold zr; rw [if_pos hr]
      rw [hz] at hl
      rw [AtomSim.den_succ_term hfv (resetB_term hr), AtomSim.den_succ_term hl (show RewriteCheck.termOp Op.Empty = true by decide)]
      simp only [resetB_ty hr, Array.toList_empty, List.map_nil]
      rw [opVal_empty]
      exact refines_retype_empty _
    · have hz : zr tabs fv = fv := by unfold zr; rw [if_neg hr]
      rw [hz] at hl
      by_cases ht : RewriteCheck.termOp fv.op = true
      · rw [AtomSim.den_succ_term hfv ht, AtomSim.den_succ_term hl ht]
        refine retype_mono _ (GoFV.Proof.Rules.opVal_mono _ _ _ _ _ ?_)
        exact AtomSim.refinesList_map fun a ha =>
          den_zeroReset hwf ρ ρ' hρ n a (hwf.argListed bid b x fv ⟨hb, hx, hfv⟩ a
            (Array.mem_toList_iff.1 ha))
      · have hf : ¬ IsTerm f.value? x := fun ⟨v, hv, hv'⟩ => by
          rw [hfv] at hv; cases hv; exact ht hv'
        have hk : ¬ IsTerm (listedDefs (zeroReset tabs f)) x := fun ⟨v, hv, hv'⟩ => by
          rw [hl] at hv; cases hv; exact ht hv'
        rw [AtomSim.den_succ_atom hf, AtomSim.den_succ_atom hk]
        exact hρ x

theorem termRef_zeroReset {ce : CheckEnv} {tabs : Tables} {f : Func} (hwf : WF ce f) {x : ID}
    (hx : Listed f x) : TermRef f.value? tabs x (listedDefs (zeroReset tabs f)) tabs x :=
  fun n => ⟨n, fun ρ ρ' hρ _ _ => den_zeroReset hwf ρ ρ' hρ n x hx⟩

/-- The atoms of `zeroReset tabs f` are `f`'s, with arguments refining as terms. -/
theorem atomArgsRef_zeroReset {ce : CheckEnv} {tabs : Tables} {f : Func} (hwf : WF ce f) :
    AtomArgsRef tabs f (zeroReset tabs f) := by
  intro b hb gb hgb a ha u hu ht
  rw [zeroReset_blocks] at hb
  rw [zeroReset_block?] at hgb
  obtain ⟨fv, hfv, -, -⟩ := hwf.valueId b gb ⟨hb, hgb⟩ a ha
  obtain ⟨n, hn⟩ := zeroReset_value? tabs f a
  rw [hfv, Option.map_some, hu] at hn
  cases hn
  have hr : resetB tabs fv = false := by
    cases hr : resetB tabs fv
    · rfl
    · simp only [zr, hr, ite_true] at ht; cases ht
  have hz : zr tabs fv = fv := by unfold zr; rw [hr]; rfl
  simp only [hz]
  refine ⟨fv, hfv, rfl, rfl, rfl, rfl, rfl, fun i hi => ?_⟩
  exact termRef_zeroReset hwf (hwf.argListed b gb a fv ⟨⟨hb, hgb⟩, ha, hfv⟩ _
    (by rw [getElem!_pos fv.args i hi]; exact Array.getElem_mem hi))

/-- The terminators of `zeroReset tabs f` are `f`'s. -/
theorem termStepRef_zeroReset {ce : CheckEnv} {tabs : Tables} {f : Func} (hwf : WF ce f) :
    TermStepRef tabs f (zeroReset tabs f) := by
  refine ControlsRef.toTermStepRef (fun b hb fb gb hfb hgb => ?_)
    (fun b _ fb gb hfb hgb => by
      rw [zeroReset_block?, hfb] at hgb; cases hgb; exact ⟨rfl, rfl, rfl⟩)
  rw [zeroReset_blocks] at hb
  rw [zeroReset_block?, hfb] at hgb
  cases hgb
  refine ⟨rfl, fun k hk => termRef_zeroReset hwf (hwf.ctrlListed b fb ⟨hb, hfb⟩ _
    (by rw [getElem!_pos fb.controls k hk]; exact Array.getElem_mem hk))⟩

/-! ## The theorem -/

private theorem ok_of_toBool {ε : Type} {e : Except ε Unit} (h : e.toBool = true) : e = .ok () := by
  cases e with
  | error _ => cases h
  | ok u => cases u; rfl

/-- **copyelim refines its input in its second fragment** (`zeroGuard`: zero-size `Load`s,
copies and selections that phielim resets to `Empty`). -/
theorem copyelim_refines_zero {penv : PassEnv} {f : Func} {out : PassOut} {ce ce' : CheckEnv}
    (h : copyelimPass penv f = .ok out) (hf : check ce f = .ok ())
    (hg : check ce' out.func = .ok ()) (hz : zeroGuard penv f = true) :
    RefinesUnder Env.Mono out.tables out.func penv.tables f := by
  simp only [copyelimPass, Pass.ofFunc, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i g hcp
    cases h
    unfold zeroGuard at hz
    simp only [hcp, Bool.and_eq_true] at hz
    obtain ⟨⟨⟨⟨⟨hck, hef⟩, hat⟩, hcf⟩, hck'⟩, hrel⟩ := hz
    have hk := ok_of_toBool hck
    have hwf := check_wf hf
    have h1 := AtomSim.atomSim_refines hf hk hat hcf hck' (atomArgsRef_zeroReset hwf)
      (termStepRef_zeroReset hwf)
    have h2 : Refines penv.tables g penv.tables (zeroReset penv.tables f) := refines_of_rel
      { wf := ⟨_, check_wf hk⟩, wg := ⟨ce', check_wf hg⟩,
        cf := certOK_of_check (check_domCert hk), cg := certOK_of_check (check_domCert hg),
        rel := copyRelB_sound hrel, frag := emptyFrag_of hef }
    exact h1.trans (h2.under _)

end GoFV.Proof.CopyZero
