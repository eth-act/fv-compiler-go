import GoFV.Opt.Fuse.ComparisonsCheck
import GoFV.Proof.Agree
import GoFV.Proof.Checked
import GoFV.Proof.Pass.FusePlainRel

variable [GoFV.SSA.Sem.Addrs]

/-!
# fuseComparisons: what the step checker establishes

`CRel f g st`: `g` is `f` with one comparison fusion at the site `st` (`Cmp.relB` holds). The
lemmas unfold the checker into facts: the shape of `p`, `b` and `s` (`shape`), the new value
(`newv`), speculation safety of `b`'s values (`spec`), the values (`value`: unchanged in what is
read, except the `Phi`s of `s`, which lose `p`'s argument by swap-removal and agree along `p`'s
and `b`'s edges), the touched blocks (`gblock`: `Site.expect`), the others (`block_same`) and the
function's frame. `swapRemove_get`: an entry of a swap-removed array at a remapped index.
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
      st.valTabOK f g = true ∧ (∀ x ∈ [st.p, st.b, st.s, st.q], st.blockOK f g x = true) ∧
      tabEq f.blockTab g.blockTab st.touched = true ∧ tabEq g.blocks f.blocks (fun _ => false) = true ∧
      g.entry = f.entry ∧ g.ownAux = f.ownAux := by
  have hr := h.rel
  unfold relB at hr
  rw [h.site] at hr
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at hr
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hsh, hnew⟩, hsp⟩, hval⟩, hblk⟩, htab⟩, hbl⟩, hent⟩, hown⟩ := hr
  exact ⟨hsh, hnew, hsp, hval, hblk, htab, hbl, hent, hown⟩

theorem CRel.blocks (h : CRel f g st) : g.blocks = f.blocks := by
  obtain ⟨hsz, hi⟩ := tabEq_spec h.parts.2.2.2.2.2.2.1
  exact Array.ext_getElem? fun i => (hi i rfl).symm

theorem CRel.entry (h : CRel f g st) : g.entry = f.entry := h.parts.2.2.2.2.2.2.2.1

theorem CRel.ownAux (h : CRel f g st) : g.ownAux = f.ownAux := h.parts.2.2.2.2.2.2.2.2

/-- An untouched block's table entry is unchanged. -/
theorem CRel.block_same (h : CRel f g st) {x : ID} (hx : st.touched x = false) :
    g.block? x = f.block? x := by
  obtain ⟨-, hi⟩ := tabEq_spec h.parts.2.2.2.2.2.1
  unfold Func.block?; rw [hi x hx]

/-- A touched block's table entry is `expect`ed. -/
theorem CRel.gblock (h : CRel f g st) {x : ID} (hx : x ∈ [st.p, st.b, st.s, st.q]) :
    ∃ X, f.block? x = some X ∧ g.block? x = some (st.expect x X) := by
  have hb := h.parts.2.2.2.2.1 x hx
  unfold Site.blockOK at hb
  split at hb
  · rename_i X X' hX hX'
    simp only [beq_iff_eq] at hb
    exact ⟨X, hX, by rw [hX', hb]⟩
  · cases hb

/-- The shape of `p`, `b` and `s` in `f`. -/
theorem CRel.shape (h : CRel f g st) :
    ∃ B P S B', f.block? st.b = some B ∧ f.block? st.p = some P ∧ f.block? st.s = some S ∧
      g.block? st.b = some B' ∧
      st.b ∈ f.blocks ∧ st.kp < 2 ∧ st.i = 1 - st.kp ∧ st.p ≠ st.b ∧ st.s ≠ st.b ∧ st.s ≠ st.p ∧
      B.kind = .If ∧ P.kind = .If ∧ B.preds = #[⟨st.p, st.kp⟩] ∧
      B.controls = #[st.bc] ∧ P.controls = #[st.pc] ∧ B.succs.size = 2 ∧ P.succs.size = 2 ∧
      P.succs[st.i]? = some ⟨st.s, st.jp⟩ ∧ B.succs[st.i]? = some ⟨st.s, st.jb⟩ ∧
      S.preds.size = st.n + 1 ∧ S.preds[st.n]?.map (·.b) = some st.q ∧
      (schedule g B').isSome := by
  have hs := h.parts.1
  unfold Site.shapeOK at hs
  obtain ⟨B, hB⟩ : ∃ B, f.block? st.b = some B := by
    cases hB : f.block? st.b with
    | none => rw [hB] at hs; cases hs
    | some B => exact ⟨B, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, f.block? st.p = some P := by
    cases hP : f.block? st.p with
    | none => rw [hB, hP] at hs; cases hs
    | some P => exact ⟨P, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S, f.block? st.s = some S := by
    cases hS : f.block? st.s with
    | none => rw [hB, hP, hS] at hs; cases hs
    | some S => exact ⟨S, rfl⟩
  obtain ⟨B', hB'⟩ : ∃ B', g.block? st.b = some B' := by
    cases hB' : g.block? st.b with
    | none => rw [hB, hP, hS, hB'] at hs; cases hs
    | some B' => exact ⟨B', rfl⟩
  rw [hB, hP, hS, hB'] at hs
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq,
    Array.contains_iff_mem, and_assoc] at hs
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := hs
  exact ⟨B, P, S, B', hB, hP, hS, hB', h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14, h15, h16, h17⟩

theorem ctrlOK_spec {c : ID} {t : TypeRef} (h : Site.ctrlOK f c t = true) :
    ∃ v, f.value? c = some v ∧ v.op ≠ .Phi ∧ v.type = t := by
  unfold Site.ctrlOK at h
  split at h
  · rename_i v hv
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h
    exact ⟨v, hv, h.1, h.2⟩
  · cases h

/-- The new value. -/
theorem CRel.newv (h : CRel f g st) :
    g.valueTab.size = f.valueTab.size ∧ st.nv < f.valueTab.size ∧ f.value? st.nv = none ∧
      ∃ w, g.value? st.nv = some w ∧ w.id = st.nv ∧ w.op = newOp st.i ∧
        w.args = #[st.pc, st.bc] ∧ w.block = st.b ∧
        (∃ v, f.value? st.pc = some v ∧ v.op ≠ .Phi ∧ v.type = w.type) ∧
        (∃ v, f.value? st.bc = some v ∧ v.op ≠ .Phi ∧ v.type = w.type) := by
  have hn := h.parts.2.1
  unfold Site.newOK at hn
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Option.isNone_iff_eq_none] at hn
  obtain ⟨⟨⟨hsz, hlt⟩, hnone⟩, hw⟩ := hn
  refine ⟨hsz, hlt, hnone, ?_⟩
  split at hw
  · rename_i w hw'
    simp only [Bool.and_eq_true, beq_iff_eq] at hw
    obtain ⟨⟨⟨⟨⟨hid, hop⟩, hargs⟩, hblk⟩, hpc⟩, hbc⟩ := hw
    exact ⟨w, hw', hid, hop, hargs, hblk, ctrlOK_spec hpc, ctrlOK_spec hbc⟩
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

theorem entryFast_eq {o o' : Option Value} : st.entryFast o o' = st.entryOK o o' := by
  unfold Site.entryFast
  split <;> simp [withPtrEq]

theorem sameW_spec {v w : Value} (h : sameW v w = true) :
    w.id = v.id ∧ w.type = v.type ∧ w.aux = v.aux ∧ w.auxInt = v.auxInt ∧ w.op = v.op ∧
      w.args = v.args ∧ w.block = v.block := by
  unfold sameW at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

/-- **The values.** Every value but `nv` keeps what the semantics reads, except the arguments
of the `Phi`s of `s`, which lose `p`'s argument by swap-removal and agree along `p`'s and `b`'s
edges. A value missing in `f` is missing in `g` (but for `nv`). -/
theorem CRel.value (h : CRel f g st) {x : ID} (hx : x ≠ st.nv) :
    (f.value? x = none → g.value? x = none) ∧
    ∀ v, f.value? x = some v → ∃ w, g.value? x = some w ∧ w.id = v.id ∧ w.type = v.type ∧
      w.aux = v.aux ∧ w.auxInt = v.auxInt ∧ w.op = v.op ∧ w.block = v.block ∧
      (v.op = .Phi → v.block = st.s →
        w.args = swapRemove v.args st.jp ∧ v.args[st.jp]? = v.args[st.jb]?) ∧
      (¬ (v.op = .Phi ∧ v.block = st.s) → w.args = v.args) := by
  obtain ⟨hsz, -, -, -⟩ := h.newv
  have hval := h.parts.2.2.2.1
  unfold Site.valTabOK at hval
  rw [Bool.and_eq_true, beq_iff_eq] at hval
  have hE : st.entryOK (f.value? x) (g.value? x) = true := by
    rcases Nat.lt_or_ge x f.valueTab.size with hlt | hge
    · have := nat_all_spec hval.2 x hlt
      rw [Bool.or_eq_true, beq_iff_eq] at this
      rcases this with h' | h'
      · exact absurd h' hx
      · rw [entryFast_eq, getElem!_pos f.valueTab x hlt,
          getElem!_pos g.valueTab x (hval.1 ▸ hlt)] at h'
        unfold Func.value?
        rw [Array.getElem?_eq_getElem hlt, Array.getElem?_eq_getElem (hval.1 ▸ hlt)]
        exact h'
    · unfold Func.value?
      rw [Array.getElem?_eq_none hge, Array.getElem?_eq_none (by omega)]
      rfl
  unfold Site.entryOK at hE
  refine ⟨fun hf => ?_, fun v hf => ?_⟩
  · rw [hf] at hE
    cases hg : g.value? x with
    | none => rfl
    | some _ => rw [hg] at hE; cases hE
  · rw [hf] at hE
    cases hg : g.value? x with
    | none => rw [hg] at hE; cases hE
    | some w =>
      rw [hg] at hE
      simp only at hE
      split at hE
      · rename_i hph
        simp only [Site.sPhi, Bool.and_eq_true, beq_iff_eq] at hph
        rw [Bool.and_eq_true, beq_iff_eq] at hE
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := sameW_spec hE.2
        exact ⟨w, rfl, h1, h2, h3, h4, h5, h7, fun _ _ => ⟨h6, hE.1⟩,
          fun hn => absurd hph hn⟩
      · rename_i hph
        simp only [Site.sPhi, Bool.and_eq_true, beq_iff_eq] at hph
        obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := sameW_spec hE
        exact ⟨w, rfl, h1, h2, h3, h4, h5, h7, fun a b => absurd ⟨a, b⟩ hph, fun _ => h6⟩

/-! ## Swap-removal -/

theorem swapRemove_size {α : Type} [Inhabited α] {a : Array α} {j : Nat} :
    (swapRemove a j).size = a.size - 1 := by
  unfold swapRemove; simp

theorem swapRemove_get {α : Type} [Inhabited α] {a : Array α} {n j k : Nat} (hsz : a.size = n + 1)
    (hj : j ≤ n) (hk : k ≠ j) : (swapRemove a j)[if k = n then j else k]? = a[k]? := by
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

/-- An entry of a swap-removed array comes from the source: the last one at `j`, others at
their index. -/
theorem swapRemove_get_inv {α : Type} [Inhabited α] {a : Array α} {n j k : Nat} {x : α}
    (hsz : a.size = n + 1) (hj : j ≤ n) (h : (swapRemove a j)[k]? = some x) :
    k < n ∧ (k = j → a[n]? = some x) ∧ (k ≠ j → a[k]? = some x) := by
  unfold swapRemove at h
  rw [hsz, Nat.add_sub_cancel, Array.getElem?_pop, Array.size_set!, hsz, Nat.add_sub_cancel] at h
  by_cases hkn : k < n
  · simp only [hkn, ite_true, Array.set!_eq_setIfInBounds] at h
    refine ⟨hkn, fun hkj => ?_, fun hkj => ?_⟩
    · subst hkj
      rw [Array.getElem?_setIfInBounds_self_of_lt (by omega)] at h
      rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)] at h
      rw [Array.getElem?_eq_getElem (by omega)]
      exact h
    · rwa [Array.getElem?_setIfInBounds_ne (Ne.symm hkj)] at h
  · simp only [hkn, ite_false] at h; cases h

end GoFV.Proof.FuseCmp
