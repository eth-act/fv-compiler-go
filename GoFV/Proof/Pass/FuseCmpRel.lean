import GoFV.Opt.Fuse.ComparisonsCheck
import GoFV.Proof.Agree
import GoFV.Proof.Checked
import GoFV.Proof.Pass.FusePlainRel

/-!
# fuseComparisons: what the step checker establishes

`CRel f g st`: `g` is `f` with one comparison fusion at the site `st` (`Cmp.relB` holds). The
lemmas unfold the checker into facts: the shape of `p`, `b` and `s` (`shape`), the new value
(`newv`), speculation safety of `b`'s values (`spec`), the values (`value`: unchanged, except the
`Phi`s of `s`, which lose `p`'s argument by swap-removal and agree along `p`'s and `b`'s edges),
the other blocks (`block_out`) and the function's frame (`top`). `swapRemove_get`: the argument
of a swap-removed array at a remapped index.
-/

namespace GoFV.Proof.FuseCmp

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.Fuse GoFV.Opt.Fuse.Cmp GoFV.Proof

/-- One checked comparison fusion at site `st`. -/
structure CRel (f g : Func) (st : Site) : Prop where
  site : site f g st.b = st
  rel : relB f g st.b = true

variable {f g : Func} {st : Site}

/-- The checker's conjuncts. -/
theorem CRel.parts (h : CRel f g st) :
    st.shapeOK f g = true ∧ st.newOK f g = true ∧ specSafeBlock f st.b = true ∧
      (∀ x, x < f.valueTab.size → x ≠ st.nv → st.valueOK f g x = true) ∧
      (∀ x ∈ f.blocks, x ≠ st.p → x ≠ st.b → st.blockOK f g x = true) ∧
      g.blocks = f.blocks ∧ g.entry = f.entry ∧ g.ownAux = f.ownAux ∧ st.placeOK f = true := by
  have hr := h.rel
  unfold relB at hr
  rw [h.site] at hr
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    beq_iff_eq] at hr
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hsh, hnew⟩, hpl⟩, hsp⟩, hval⟩, hblk⟩, hbl⟩, hent⟩, hown⟩ := hr
  refine ⟨hsh, hnew, hsp, fun x hx hne => ?_, fun x hx hp hb => ?_, by simpa using hbl, hent,
    hown, hpl⟩
  · rcases hval x hx with h' | h'
    · exact absurd h' hne
    · exact h'
  · rcases (Array.all_eq_true'.1 hblk) x hx |> Bool.or_eq_true_iff.1 with h' | h'
    · rcases Bool.or_eq_true_iff.1 h' with h'' | h''
      · exact absurd (by simpa using h'') hp
      · exact absurd (by simpa using h'') hb
    · exact h'

/-- `p` and `b` are listed; `b` is no tree ancestor of `p`. -/
theorem CRel.place (h : CRel f g st) :
    st.b ∈ f.blocks ∧ st.p ∈ f.blocks ∧ (DomCert.make f).anc st.b st.p = false := by
  have hp := h.parts.2.2.2.2.2.2.2.2
  unfold Site.placeOK at hp
  simp only [Bool.and_eq_true, Array.contains_iff_mem, Bool.not_eq_true'] at hp
  exact ⟨hp.1.1, hp.1.2, hp.2⟩

/-- The shape of `p`, `b` and `s` in `f`, of `p` and `b` in `g`. -/
theorem CRel.shape (h : CRel f g st) :
    ∃ B P S B' P', f.block? st.b = some B ∧ f.block? st.p = some P ∧ f.block? st.s = some S ∧
      g.block? st.b = some B' ∧ g.block? st.p = some P' ∧
      st.kp < 2 ∧ st.i = 1 - st.kp ∧ st.p ≠ st.b ∧ st.s ≠ st.b ∧ st.s ≠ st.p ∧
      B.kind = .If ∧ P.kind = .If ∧ B.preds = #[⟨st.p, st.kp⟩] ∧
      B.controls = #[st.bc] ∧ P.controls = #[st.pc] ∧ B.succs.size = 2 ∧ P.succs.size = 2 ∧
      P.succs[st.i]? = some ⟨st.s, st.jp⟩ ∧ B.succs[st.i]? = some ⟨st.s, st.jb⟩ ∧
      S.preds.size = st.n + 1 ∧
      B'.id = st.b ∧ B'.values = B.values.push st.nv ∧ B'.kind = .If ∧
      B'.controls = #[st.nv] ∧ B'.succs = B.succs.map st.remapE ∧
      (schedule g B').isSome ∧
      P'.id = st.p ∧ P'.values = P.values ∧ P'.kind = .Plain ∧ P'.succs[0]? = some ⟨st.b, 0⟩ := by
  have hs := h.parts.1
  unfold Site.shapeOK at hs
  split at hs
  · rename_i B P S B' P' hB hP hS hB' hP'
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq,
      and_assoc] at hs
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
      h19, h20, h21, h22, h23, h24, h25⟩ := hs
    exact ⟨B, P, S, B', P', hB, hP, hS, hB', hP', h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
      h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25⟩
  · cases hs

/-- The new value. -/
theorem CRel.newv (h : CRel f g st) :
    g.valueTab.size = f.valueTab.size ∧ st.nv < f.valueTab.size ∧ f.value? st.nv = none ∧
      ∃ w, g.value? st.nv = some w ∧ w.id = st.nv ∧ w.op = newOp st.i ∧
        w.args = #[st.pc, st.bc] := by
  have hn := h.parts.2.1
  unfold Site.newOK at hn
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Option.isNone_iff_eq_none] at hn
  obtain ⟨⟨⟨hsz, hlt⟩, hnone⟩, hw⟩ := hn
  refine ⟨hsz, hlt, hnone, ?_⟩
  split at hw
  · rename_i w hw'
    simp only [Bool.and_eq_true, beq_iff_eq] at hw
    exact ⟨w, hw', hw.1.1, hw.1.2, hw.2⟩
  · cases hw

/-- The values of `b` are speculation-safe. -/
theorem CRel.spec (h : CRel f g st) {B : Block} (hB : f.block? st.b = some B) :
    ∀ x ∈ B.values, ∃ v, f.value? x = some v ∧ specSafeOp v.op = true := by
  have hs := h.parts.2.2.1
  unfold specSafeBlock at hs
  rw [hB, Array.all_eq_true'] at hs
  intro x hx
  have := hs x hx
  split at this
  · rename_i v hv; exact ⟨v, hv, this⟩
  · cases this

/-- **The values.** Every value but `nv` keeps what the semantics reads, except the arguments
of the `Phi`s of `s`, which lose `p`'s argument by swap-removal and agree along `p`'s and `b`'s
edges. A value missing in `f` is missing in `g` (but for `nv`). -/
theorem CRel.value (h : CRel f g st) {x : ID} (hx : x ≠ st.nv) :
    (f.value? x = none → g.value? x = none) ∧
    ∀ v, f.value? x = some v → ∃ w, g.value? x = some w ∧ w.id = v.id ∧ w.type = v.type ∧
      w.aux = v.aux ∧ w.auxInt = v.auxInt ∧ w.op = v.op ∧
      (v.op = .Phi → x ∈ (valsOf f st.s).toList →
        w.args = swapRemove v.args st.jp ∧ v.args[st.jp]? = v.args[st.jb]?) ∧
      (¬ (v.op = .Phi ∧ x ∈ (valsOf f st.s).toList) → w.args = v.args) := by
  obtain ⟨hsz, -, -, -⟩ := h.newv
  have hval := h.parts.2.2.2.1
  have hplain : Plain.valueOK f g x = true →
      (f.value? x = none → g.value? x = none) ∧
      ∀ v, f.value? x = some v → ∃ w, g.value? x = some w ∧ w.id = v.id ∧ w.type = v.type ∧
        w.aux = v.aux ∧ w.auxInt = v.auxInt ∧ w.op = v.op ∧ w.args = v.args := by
    intro hv
    unfold Plain.valueOK at hv
    refine ⟨fun hf => ?_, fun v hf => ?_⟩
    · rw [hf] at hv
      cases hg : g.value? x with
      | none => rfl
      | some _ => rw [hg] at hv; cases hv
    · rw [hf] at hv
      cases hg : g.value? x with
      | none => rw [hg] at hv; cases hv
      | some w =>
        rw [hg] at hv
        unfold Plain.sameV at hv
        simp only [Bool.and_eq_true, beq_iff_eq] at hv
        obtain ⟨⟨⟨⟨⟨hid, hty⟩, haux⟩, hai⟩, hop⟩, hargs⟩ := hv
        exact ⟨w, rfl, hid, hty, haux, hai, hop, hargs⟩
  rcases Nat.lt_or_ge x f.valueTab.size with hlt | hge
  · have hv := hval x hlt hx
    unfold Site.valueOK at hv
    cases hf : f.value? x with
    | none =>
      rw [hf] at hv
      exact ⟨fun _ => (hplain hv).1 hf, fun _ h' => nomatch h'⟩
    | some v =>
      rw [hf] at hv
      simp only at hv
      split at hv
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq, Array.contains_iff_mem] at hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hv
        obtain ⟨hagree, hw⟩ := hv
        refine ⟨fun h' => (nomatch h'), fun v' hv' => ?_⟩
        cases hv'
        split at hw
        · rename_i w hw'
          simp only [Bool.and_eq_true, beq_iff_eq] at hw
          obtain ⟨⟨⟨⟨⟨hid, hty⟩, haux⟩, hai⟩, hop⟩, hargs⟩ := hw
          exact ⟨w, hw', hid, hty, haux, hai, hop, fun _ _ => ⟨hargs, hagree⟩,
            fun hn => absurd ⟨hc.1, Array.mem_toList_iff.2 hc.2⟩ hn⟩
        · cases hw
      · rename_i hc
        obtain ⟨-, h2⟩ := hplain hv
        refine ⟨fun h' => (nomatch h'), fun v' hv' => ?_⟩
        cases hv'
        obtain ⟨w, hw, h1, h2', h3, h4, h5, h6⟩ := h2 v hf
        refine ⟨w, hw, h1, h2', h3, h4, h5, fun hp hs => absurd ?_ hc, fun _ => h6⟩
        simp only [Bool.and_eq_true, beq_iff_eq, Array.contains_iff_mem]
        exact ⟨hp, Array.mem_toList_iff.1 hs⟩
  · have h1 : f.value? x = none := by simp [Func.value?, Array.getElem?_eq_none hge]
    have h2 : g.value? x = none := by
      simp [Func.value?, Array.getElem?_eq_none (show g.valueTab.size ≤ x by omega)]
    exact ⟨fun _ => h2, fun _ h' => by rw [h1] at h'; cases h'⟩

/-- A listed block other than `p` and `b` is unchanged but for `remapE`. -/
theorem CRel.block_out (h : CRel f g st) {x : ID} (hx : x ∈ f.blocks) (hp : x ≠ st.p)
    (hb : x ≠ st.b) :
    ∃ fb gb, f.block? x = some fb ∧ g.block? x = some gb ∧ gb.id = fb.id ∧
      gb.values = fb.values ∧ gb.kind = fb.kind ∧ gb.controls = fb.controls ∧
      gb.succs = fb.succs.map st.remapE := by
  have h' := h.parts.2.2.2.2.1 x hx hp hb
  unfold Site.blockOK at h'
  cases hf : f.block? x with
  | none => rw [hf] at h'; cases h'
  | some fb =>
    cases hg : g.block? x with
    | none => rw [hf, hg] at h'; cases h'
    | some gb =>
      rw [hf, hg] at h'
      simp only [Bool.and_eq_true, beq_iff_eq] at h'
      obtain ⟨⟨⟨⟨hid, hv⟩, hk⟩, hc⟩, hs⟩ := h'
      exact ⟨fb, gb, rfl, rfl, hid, hv, hk, hc, hs⟩

/-! ## Swap-removal -/

theorem swapRemove_get {a : Array ID} {n j k : Nat} (hsz : a.size = n + 1) (hj : j ≤ n)
    (hk : k ≠ j) : (swapRemove a j)[if k = n then j else k]? = a[k]? := by
  unfold swapRemove
  rw [hsz, Nat.add_sub_cancel, Array.getElem?_pop, Array.size_set!, hsz, Nat.add_sub_cancel]
  by_cases hkn : k = n
  · subst hkn
    have hjn : j < k := Nat.lt_of_le_of_ne hj (Ne.symm hk)
    simp only [ite_true, hjn, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_self_of_lt (show j < a.size by omega)]
    rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)]
    rfl
  · simp only [hkn, ite_false]
    by_cases hkl : k < n
    · simp only [hkl, ite_true, Array.set!_eq_setIfInBounds,
        Array.getElem?_setIfInBounds_ne (Ne.symm hk)]
    · simp only [hkl, ite_false]
      rw [Array.getElem?_eq_none (by omega)]

end GoFV.Proof.FuseCmp
