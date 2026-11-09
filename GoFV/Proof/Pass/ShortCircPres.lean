import GoFV.Proof.Pass.ShortCircSpec
import GoFV.Proof.WFCheck
import GoFV.Proof.Merge

variable [GoFV.SSA.Sem.Addrs]

/-!
# Checked `shortcircuitBlock`: the result is well formed

`Setup.wfg`: `scOK` no longer runs `wfDomCheck` on the result (issue #147); its well-formedness
follows from `f`'s and the checker's local facts. The blocks outside `K` and the values listed
outside `K` are those of `f` (`frameOK`: `block_out`, `gval_out`), so `f`'s facts carry over to
them; the blocks of `K` pass the per-block loops of `wfCheck` (`wfKOK`), and an edge between a
block of `K` and one outside keeps its indices. An argument is listed: a register outside `b`'s
values keeps its block (`listed_keep`); a moved phi is listed in a block entered from `b` or `t`
(`closeOK`, `moved_listed`); the arguments of `K`'s blocks pass `useOK` (`domKOK`).
-/

namespace GoFV.Proof.ShortCirc

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.ShortCircuit GoFV.Proof Dom

/-! ## Well-formedness helpers -/

theorem listedIn_of {ce : CheckEnv} {f : Func} (hwf : WF ce f) {a : ID} (hl : Listed f a) :
    listedIn f a = true := by
  obtain ⟨v, Bk, ⟨hv, -⟩, hvb, hBk, ha, -⟩ := blockOf_listed hwf hl
  unfold listedIn; rw [hv]; simp only
  rw [hvb, valsOf_eq hBk]; exact contains_iff.2 ha

theorem listed_of_mem {ce : CheckEnv} {f : Func} (hwf : WF ce f) {B : ID} {fB : Block}
    (hBm : B ∈ f.blocks) (hfB : f.block? B = some fB) {x : ID} (hx : x ∈ fB.values) :
    Listed f x := ⟨B, fB, ⟨hBm, hfB⟩, hx⟩

theorem value_of_mem {ce : CheckEnv} {f : Func} (hwf : WF ce f) {B : ID} {fB : Block}
    (hBm : B ∈ f.blocks) (hfB : f.block? B = some fB) {x : ID} (hx : x ∈ fB.values) :
    ∃ v, f.value? x = some v ∧ v.id = x ∧ v.block = B :=
  hwf.valueId B fB ⟨hBm, hfB⟩ x hx

theorem argListed_of {ce : CheckEnv} {f : Func} (hwf : WF ce f) {B : ID} {fB : Block}
    (hBm : B ∈ f.blocks) (hfB : f.block? B = some fB) {x : ID} (hx : x ∈ fB.values) {v : Value}
    (hv : f.value? x = some v) {a : ID} (ha : a ∈ v.args) : Listed f a :=
  hwf.argListed B fB x v ⟨⟨hBm, hfB⟩, hx, hv⟩ a ha

theorem value_of_listed {ce : CheckEnv} {f : Func} (hwf : WF ce f) {a : ID} (hl : Listed f a) :
    ∃ v, f.value? a = some v := by
  obtain ⟨B, Bk, ⟨hBm, hBk⟩, ha⟩ := hl
  obtain ⟨v, hv, -⟩ := hwf.valueId B Bk ⟨hBm, hBk⟩ a ha
  exact ⟨v, hv⟩

theorem mem_nodesOf_iff {ce : CheckEnv} {h : Func} (hwf : WF ce h) {B : ID} {Bk : Block}
    (hBm : B ∈ h.blocks) (hBk : h.block? B = some Bk) {x : ID} :
    x ∈ Info.nodesOf h Bk ↔ x ∈ Bk.values ∧ ∃ v, h.value? x = some v ∧ v.op ≠ .Phi := by
  rw [mem_nodesOf]
  constructor
  · rintro ⟨hx, hp⟩
    obtain ⟨v, hv, -⟩ := value_of_mem hwf hBm hBk hx
    exact ⟨hx, v, hv, (isPhiIn_false hv).1 hp⟩
  · rintro ⟨hx, v, hv, hp⟩
    exact ⟨hx, (isPhiIn_false hv).2 hp⟩

theorem args_get_mem {v : Value} {k : Nat} {a : ID} (h : v.args[k]? = some a) : a ∈ v.args :=
  Array.mem_of_getElem? h

theorem look_map_eq (I : Info) {h : ID → Option ID} {v w : ID}
    (hl : I.look (I.vs.map h) v = some w) : h v = some w := by
  unfold Info.look at hl
  cases hi : I.vs.findIdx? (· == v) with
  | none => rw [hi] at hl; cases hl
  | some i =>
    rw [hi] at hl
    obtain ⟨hlt, hx⟩ := Array.findIdx?_eq_some_iff_getElem.1 hi
    have hv : I.vs[i] = v := by simpa using hx.1
    simp only [Option.bind_some, Array.getElem?_map, Array.getElem?_eq_getElem hlt,
      Option.map_some, Option.join_some, hv] at hl
    exact hl

theorem look_map (I : Info) {h : ID → Option ID} (hh : ∀ v w, h v = some w → w = v) {v w : ID}
    (hl : I.look (I.vs.map h) v = some w) : w = v :=
  hh v w (look_map_eq I hl)

theorem look_dflt {tabs : Tables} {f g : Func} {s : Site} {v w : ID}
    (hl : (infoOf tabs f g s).look (infoOf tabs f g s).dflt v = some w) : w = v :=
  look_map _ (fun v w h => by dsimp only at h; split at h <;> cases h; rfl) hl

/-- A default fact `(v, v)`: `v` left `b` and is listed in `g` (by its table entry). -/
theorem dflt_spec {tabs : Tables} {f g : Func} {s : Site} {v : ID}
    (hl : (infoOf tabs f g s).look (infoOf tabs f g s).dflt v = some v) :
    (g.getV v).block ≠ s.b ∧ listedIn g v = true := by
  have h := look_map_eq _ hl
  dsimp only at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hc
    exact ⟨hc.1.1, hc.1.2⟩
  · cases h

theorem allIdx_spec {α : Type} {a : Array α} {p : Nat → α → Bool} (h : allIdx a p = true)
    {i : Nat} {x : α} (hx : a[i]? = some x) : p i x = true := by
  unfold allIdx at h
  have hi := (Array.getElem?_eq_some_iff.1 hx).1
  have := List.all_eq_true.1 h i (List.mem_range.2 hi)
  rw [hx] at this
  simpa using this

/-- A table entry listed in its block. -/
theorem listedIn_spec {h : Func} {x : ID} (hl : listedIn h x = true) :
    ∃ v Bk, h.value? x = some v ∧ h.block? v.block = some Bk ∧ x ∈ Bk.values := by
  unfold listedIn at hl
  split at hl
  · rename_i v hv
    unfold valsOf at hl
    cases hB : h.block? v.block with
    | none => rw [hB] at hl; simp at hl
    | some Bk =>
      rw [hB] at hl
      exact ⟨v, Bk, hv, hB, contains_iff.1 hl⟩
  · cases hl

theorem blockOf_of {h : Func} {x : ID} {v : Value} (hv : h.value? x = some v) :
    DomCert.blockOf h x = v.block := by
  unfold DomCert.blockOf; rw [hv]; rfl

/-! ## The new checks, as propositions -/

namespace SCI

variable (I : Info) {f g : Func}

theorem redir_iff {B iT : Nat} : I.redir B iT = true ↔ B = I.t ∧ iT = I.tn := by
  unfold Info.redir; simp

theorem srcIdx_of {B iT : Nat} (h : ¬ (B = I.s.b ∧ iT = I.s.cidx)) : I.srcIdx B iT = iT := by
  unfold Info.srcIdx
  split
  · rename_i h'; simp only [Bool.and_eq_true, beq_iff_eq] at h'; exact absurd ⟨h'.1.1, h'.1.2⟩ h
  · rfl

theorem wfKOK_some {B : ID} {fB : Block} (hfB : f.block? B = some fB)
    (h : I.wfKOK f g B = true) : ∃ gB, g.block? B = some gB := by
  unfold Info.wfKOK at h
  rw [hfB] at h
  cases hg : g.block? B with
  | none => rw [hg] at h; cases h
  | some gB => exact ⟨gB, rfl⟩

theorem wfKOK_spec {B : ID} {fB gB : Block} (hfB : f.block? B = some fB)
    (hgB : g.block? B = some gB) (h : I.wfKOK f g B = true) :
    (B = g.entry → gB.preds = #[]) ∧
    (∀ (i : Nat) (e : Edge), gB.preds[i]? = some e →
      (∃ P : Block, g.block? e.b = some P ∧ P.succs[e.i]? = some ⟨B, i⟩) ∧
      (e.b = I.s.p ∨ ∃ e' ∈ fB.preds, e'.b = e.b)) ∧
    (∀ (j : Nat) (e : Edge), gB.succs[j]? = some e →
      (∃ C : Block, g.block? e.b = some C ∧ C.preds[e.i]? = some ⟨B, j⟩) ∧
      (e.b = I.t ∨ ∃ e' ∈ fB.succs, e'.b = e.b)) ∧
    (∀ (i : Nat) (e : Edge), fB.preds[i]? = some e → e.b ∉ I.K → gB.preds[i]? = some e) ∧
    (∀ (j : Nat) (e : Edge), fB.succs[j]? = some e → e.b ∉ I.K → gB.succs[j]? = some e) ∧
    (∀ x ∈ gB.values, ∃ v, g.value? x = some v ∧ v.id = x ∧ WFCheck.valueOK gB v = true) ∧
    (gB.values = fB.values ∨ gB.values.toList.Nodup) := by
  unfold Info.wfKOK at h
  rw [hfB, hgB] at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, Array.isEmpty_iff,
    Array.all_eq_true', beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  refine ⟨fun he => h1.resolve_left (fun h => h he), fun i e he => ?_, fun j e he => ?_,
    fun i e he hK => ?_, fun j e he hK => ?_, fun x hx => ?_, h7⟩
  · have := allIdx_spec h2 he
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Array.any_eq_true'] at this
    obtain ⟨hl, hm⟩ := this
    refine ⟨?_, ?_⟩
    · unfold Info.predLinkOK at hl
      cases hP : g.block? e.b with
      | none => rw [hP] at hl; cases hl
      | some P => rw [hP] at hl; exact ⟨P, rfl, by simpa using hl⟩
    · rcases hm with (hm | hm) | ⟨e', he', hb⟩
      · exact .inr ⟨e, Array.mem_of_getElem? hm, rfl⟩
      · exact .inl hm
      · exact .inr ⟨e', he', hb⟩
  · have := allIdx_spec h3 he
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Array.any_eq_true'] at this
    obtain ⟨hl, hm⟩ := this
    refine ⟨?_, ?_⟩
    · unfold Info.succLinkOK at hl
      cases hC : g.block? e.b with
      | none => rw [hC] at hl; cases hl
      | some C => rw [hC] at hl; exact ⟨C, rfl, by simpa using hl⟩
    · rcases hm with (hm | hm) | ⟨e', he', hb⟩
      · exact .inr ⟨e, Array.mem_of_getElem? hm, rfl⟩
      · exact .inl hm
      · exact .inr ⟨e', he', hb⟩
  · have := allIdx_spec h4 he
    simp only [Bool.or_eq_true, contains_iff, beq_iff_eq] at this
    exact this.resolve_left hK
  · have := allIdx_spec h5 he
    simp only [Bool.or_eq_true, contains_iff, beq_iff_eq] at this
    exact this.resolve_left hK
  · have := h6 x hx
    cases hv : g.value? x with
    | none => rw [hv] at this; cases this
    | some v =>
      rw [hv] at this
      simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq] at this
      exact ⟨v, rfl, this.1, this.2⟩

theorem availAt_spec {P w : ID} (h : I.availAt f P w = true) :
    w ∉ I.bvals ∧ ∃ z ∈ I.bvals, isPhiIn f z = true ∧ ∃ (j : Nat) (e : Edge),
      (f.getB I.s.b).preds[j]? = some e ∧ e.b = P ∧ (f.getV z).args[j]? = some w := by
  unfold Info.availAt at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', contains_false, Array.any_eq_true',
    List.any_eq_true, List.mem_range, beq_iff_eq] at h
  obtain ⟨hw, z, hz, hp, j, hj, hb, ha⟩ := h
  have hj' : j < (f.getB I.s.b).preds.size := hj
  refine ⟨hw, z, hz, hp, j, (f.getB I.s.b).preds[j], Array.getElem?_eq_getElem hj', ?_, ha⟩
  rw [Array.getElem?_eq_getElem hj'] at hb
  simpa using hb

theorem dsOK_spec (h : I.dsOK g = true) :
    ∀ Y ∈ I.dS, Y = I.s.b ∨ (Y ≠ g.entry ∧ ∀ e ∈ (g.getB Y).preds, e.b ∈ I.dS) := by
  unfold Info.dsOK at h
  simp only [Array.all_eq_true', Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, bne_iff_ne,
    ne_eq, contains_iff] at h
  exact h

theorem closeOK_spec (h : I.closeOK g = true) {v : ID} (hv : v ∈ I.vs)
    (hd : I.look I.dflt v = some v) :
    (g.getV v).block ∈ I.region ∧ I.t ∈ I.region ∧
    ((g.getV v).block = I.t ∨ ∃ e ∈ (g.getB (g.getV v).block).preds, e.b = I.s.b ∨ e.b = I.t) ∧
    (∀ e ∈ (g.getB I.s.b).succs, e.b ∈ I.region) ∧
    ∀ r ∈ I.region, r ≠ (g.getV v).block → ∀ e ∈ (g.getB r).succs, e.b ∈ I.region := by
  unfold Info.closeOK at h
  have := Array.all_eq_true'.1 h v hv
  simp only [hd, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, contains_iff,
    Bool.or_eq_true, beq_iff_eq, Array.any_eq_true', Array.all_eq_true'] at this
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := this
  exact ⟨h1, h2, h3, h4, fun r hr hne => (h5 r hr).resolve_left hne⟩

theorem useOK_spec {P w : ID} {a? : Option ID} {rd : Bool} (h : I.useOK f g P w a? rd = true) :
    (a? = some w ∧ w ∉ I.bvals) ∨
    (listedIn g w = true ∧ (DomCert.blockOf g w = P ∨
      (a? = some w ∧ rd = false ∧ I.freeArg w = true ∧ P ≠ I.s.b ∧ P ∉ I.region) ∨
      I.availAt f P w = true ∨
      (P ∈ I.dS ∧ (g.getB I.s.b).preds.isEmpty = false ∧
        ∀ e ∈ (g.getB I.s.b).preds, I.availAt f e.b w = true))) := by
  unfold Info.useOK at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', contains_false,
    bne_iff_ne, ne_eq, contains_iff, Array.all_eq_true'] at h
  rcases h with h | ⟨hl, h⟩
  · exact .inl h
  · refine .inr ⟨hl, ?_⟩
    rcases h with ((h | ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩) | h) | ⟨⟨h1, h2⟩, h3⟩
    · exact .inl h
    · exact .inr (.inl ⟨h1, h2, h3, h4, h5⟩)
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr ⟨h1, h2, h3⟩))

/-- The source facts behind `phiSrc`. -/
theorem phiSrc_spec {fB : Block} {fx? : Option Value} {B iT : Nat} {e : Edge} {a : ID}
    (h : I.phiSrc fB fx? B iT e = some a) :
    ∃ fv, fx? = some fv ∧ fv.op = .Phi ∧
      ((I.redir B iT = true ∧ (fB.preds[I.s.te.i]?.map (·.b)) = some I.s.b ∧
          fv.args[I.s.te.i]? = some a) ∨
        (I.redir B iT = false ∧ fB.preds[I.srcIdx B iT]? = some e ∧
          fv.args[I.srcIdx B iT]? = some a)) := by
  unfold Info.phiSrc at h
  cases hx : fx? with
  | none => rw [hx] at h; cases h
  | some fv =>
    rw [hx] at h
    simp only [Option.bind_some] at h
    refine ⟨fv, rfl, ?_⟩
    by_cases hp : fv.op = .Phi
    · refine ⟨hp, ?_⟩
      simp only [hp, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h
      cases hr : I.redir B iT
      · rw [hr] at h
        simp only [Bool.false_eq_true, ↓reduceIte] at h
        split at h
        · rename_i he; exact .inr ⟨rfl, by simpa using he, h⟩
        · cases h
      · rw [hr] at h
        simp only [↓reduceIte] at h
        split at h
        · rename_i he; exact .inl ⟨rfl, by simpa using he, h⟩
        · cases h
    · simp [hp] at h

theorem nodeSrc_spec {fx? : Option Value} {k : Nat} {a : ID} (h : Info.nodeSrc fx? k = some a) :
    ∃ fv, fx? = some fv ∧ fv.op ≠ .Phi ∧ fv.args[k]? = some a := by
  unfold Info.nodeSrc at h
  cases hx : fx? with
  | none => rw [hx] at h; cases h
  | some fv =>
    rw [hx] at h
    simp only [Option.bind_some] at h
    by_cases hp : fv.op = .Phi
    · rw [if_pos (by simpa using hp)] at h; cases h
    · rw [if_neg (by simpa using hp)] at h; exact ⟨fv, rfl, hp, h⟩

/-- **The uses of a block of `K`** (`domKOK`): each argument and control passes `useOK`, with the
source's register at the same place. -/
theorem domKOK_spec {B : ID} (h : I.domKOK f g B = true) :
    (∀ x ∈ (g.getB B).values, (g.getV x).op = .Phi →
      ∀ (iT : Nat) (e : Edge) (w : ID), (g.getB B).preds[iT]? = some e →
        (g.getV x).args[iT]? = some w →
        ∃ a? : Option ID, I.useOK f g e.b w a? (I.redir B iT) = true ∧ ∀ a, a? = some a →
          x ∈ (f.getB B).values ∧ ∃ fv, f.value? x = some fv ∧ fv.op = .Phi ∧
            ((I.redir B iT = true ∧ ((f.getB B).preds[I.s.te.i]?.map (·.b)) = some I.s.b ∧
                fv.args[I.s.te.i]? = some a) ∨
              (I.redir B iT = false ∧ (f.getB B).preds[I.srcIdx B iT]? = some e ∧
                fv.args[I.srcIdx B iT]? = some a))) ∧
    (∀ x ∈ (g.getB B).values, (g.getV x).op ≠ .Phi →
      ∀ (k : Nat) (w : ID), (g.getV x).args[k]? = some w →
        ∃ a? : Option ID, I.useOK f g B w a? false = true ∧ ∀ a, a? = some a →
          x ∈ (f.getB B).values ∧ ∃ fv, f.value? x = some fv ∧ fv.op ≠ .Phi ∧
            fv.args[k]? = some a) ∧
    (∀ (k : Nat) (c : ID), (g.getB B).controls[k]? = some c →
      I.useOK f g B c (f.getB B).controls[k]? false = true) := by
  unfold Info.domKOK at h
  simp only [Bool.and_eq_true, Array.all_eq_true'] at h
  obtain ⟨hv, hc⟩ := h
  have hfx : ∀ x ∈ (g.getB B).values, ∀ fv,
      (if ((g.getB B).values == (f.getB B).values || (f.getB B).values.contains x) = true
        then f.value? x else none) = some fv → x ∈ (f.getB B).values ∧ f.value? x = some fv := by
    intro x hx fv h
    split at h
    · rename_i hc
      refine ⟨?_, h⟩
      simp only [Bool.or_eq_true, beq_iff_eq, contains_iff] at hc
      rcases hc with hc | hc
      · rw [← hc]; exact hx
      · exact hc
    · cases h
  refine ⟨fun x hx hp iT e w he hw => ?_, fun x hx hp k w hw => ?_,
    fun k c hk => allIdx_spec hc hk⟩
  · have := hv x hx
    rw [if_pos (by simpa using hp)] at this
    have := allIdx_spec this he
    rw [hw] at this
    simp only [Option.all_some] at this
    refine ⟨_, this, fun a ha => ?_⟩
    obtain ⟨fv, hf, hop, hr⟩ := phiSrc_spec I ha
    obtain ⟨hxf, hfv⟩ := hfx x hx fv hf
    exact ⟨hxf, fv, hfv, hop, hr⟩
  · have := hv x hx
    rw [if_neg (by simpa using hp)] at this
    have := allIdx_spec this hw
    refine ⟨_, this, fun a ha => ?_⟩
    obtain ⟨fv, hf, hop, hr⟩ := nodeSrc_spec ha
    obtain ⟨hxf, hfv⟩ := hfx x hx fv hf
    exact ⟨hxf, fv, hfv, hop, hr⟩

end SCI

theorem blockOK_spec {I : Info} {f g : Func} {T : FactTab} {B : ID} {fB gB : Block}
    (hBg : B ∈ g.blocks) (hfB : f.block? B = some fB) (hgB : g.block? B = some gB)
    (h : I.blockOK f g T B = true) :
    fB.id = B ∧ gB.id = B ∧ ((gB.preds = #[] ∧ B = I.s.b) ∨
      (gB.kind = fB.kind ∧ gB.controls.size = fB.controls.size ∧
        (B ∈ I.region ∨ B = I.s.b ∨ ((I.factsOf T B).1 = I.dflt ∧ (I.factsOf T B).2 = I.dflt)) ∧
        I.newOK f fB gB = true ∧
        I.nodesOK f g fB gB (I.factsOf T B).1 (I.factsOf T B).2
          (I.region.contains B || B == I.s.b) = true ∧
        Info.schedOK f g fB gB = true ∧
        I.outOK f g fB gB (I.factsOf T B).1 (I.factsOf T B).2 = true ∧
        I.succOK fB gB B = true ∧
        (∀ (k : Nat) (c' c : ID), gB.controls[k]? = some c' → fB.controls[k]? = some c →
          I.argRel f g fB gB (I.factsOf T B).1 (I.factsOf T B).2 c' c = true) ∧
        ∀ iT, iT < max 1 gB.preds.size →
          (I.redir B iT = true ∨ fB.preds[(I.edgeIn f T B gB iT).1]? = gB.preds[iT]?) ∧
          I.phisOK f g fB gB (I.factsOf T B).1 iT (I.edgeIn f T B gB iT).1
            (I.edgeIn f T B gB iT).2 (I.region.contains B) = true)) := by
  unfold Info.blockOK at h
  rw [contains_iff.2 hBg, hfB, hgB] at h
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  rcases Bool.or_eq_true_iff.1 h3 with h3 | h3
  · simp only [Bool.and_eq_true, beq_iff_eq, Array.isEmpty_iff] at h3
    exact .inl h3
  · refine .inr ?_
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, contains_iff,
      List.all_eq_true, List.mem_range, Array.all_eq_true'] at h3
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hk, hc⟩, hd⟩, hn⟩, hno⟩, hs⟩, ho⟩, hsu⟩, hcr⟩, hph⟩ := h3
    refine ⟨hk, hc, ?_, hn, ?_, hs, ho, hsu, fun k c' c hc' hc0 => ?_, fun iT hiT => ?_⟩
    · rcases hd with (hd | hd) | ⟨hd1, hd2⟩
      · exact .inl hd
      · exact .inr (.inl hd)
      · exact .inr (.inr ⟨hd1, hd2⟩)
    · simpa [contains_iff, Bool.or_eq_true, beq_iff_eq] using hno
    · have hk1 : k < gB.controls.size := (Array.getElem?_eq_some_iff.1 hc').1
      have hk2 : k < fB.controls.size := (Array.getElem?_eq_some_iff.1 hc0).1
      have := hcr (gB.controls[k], fB.controls[k])
        (Array.mem_iff_getElem.2 ⟨k, by simp only [Array.size_zip]; omega, by simp⟩)
      rw [Array.getElem?_eq_some_iff.1 hc' |>.2, Array.getElem?_eq_some_iff.1 hc0 |>.2] at this
      exact this
    · obtain ⟨h1, h2⟩ := hph iT hiT
      refine ⟨?_, by simpa [contains_iff] using h2⟩
      rcases h1 with h1 | h1
      · exact .inl h1
      · exact .inr h1

/-! ## The frame -/

namespace Info

theorem frameOK_tabs {I : Info} {f g : Func} (h : I.frameOK f g = true) :
    tabEqBy (fun a b => decide (a = b)) (fun _ => by simp) f.blockTab g.blockTab
      (I.K.contains ·) = true ∧
    tabEqBy sameEntry sameEntry_refl f.valueTab g.valueTab
      (fun x => I.K.contains (f.getV x).block || (f.value? x).isNone) = true := by
  unfold Info.frameOK at h
  exact Bool.and_eq_true_iff.1 h

end Info

namespace Setup

variable {ce : CheckEnv} {tabs : Tables} {f g : Func} {s : Site} (S : Setup ce tabs f g s)
include S

set_option hygiene false in
local notation "𝓘" => infoOf tabs f g s
set_option hygiene false in
local notation "𝓣" => Info.factTab (infoOf tabs f g s) f g

theorem block_out {B : ID} (hBK : B ∉ (𝓘).K) : g.block? B = f.block? B := by
  have h := tabEqBy_spec (Info.frameOK_tabs S.frameOK).1 B (by simpa [contains_iff] using hBK)
  simp only [decide_eq_true_eq] at h
  exact h.symm

theorem value_out {x : ID} {fx : Value} (hfx : f.value? x = some fx) (hf : fx.block ∉ (𝓘).K) :
    sameEntry (f.value? x) (g.value? x) = true := by
  have h := tabEqBy_spec (Info.frameOK_tabs S.frameOK).2 x (by
    simp only [Bool.or_eq_false_iff, hfx, Option.isNone_some, and_true]
    rw [getV_of hfx]; simpa [contains_iff] using hf)
  simpa [Func.value?] using h

theorem region_spec {r : ID} (hr : r ∈ (𝓘).region) :
    r ≠ s.b ∧ r ≠ g.entry ∧ r ∈ (𝓘).K ∧ ∀ e ∈ (g.getB r).preds,
      e.b ∈ (𝓘).region ∨ e.b = s.b ∨ (r = s.te.b ∧ e = ⟨s.p, s.pi⟩) := by
  have h := S.regionOK
  unfold Info.regionOK at h
  have := Array.all_eq_true'.1 h r hr
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, contains_iff, Array.all_eq_true',
    Bool.or_eq_true, beq_iff_eq] at this
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := this
  exact ⟨h1, h2, h3, fun e he => by simpa [or_assoc] using h4 e he⟩

theorem redir_spec : (g.getB s.te.b).preds.size = (𝓘).tn + 1 ∧
    (g.getB s.te.b).preds[(𝓘).tn]? = some ⟨s.p, s.pi⟩ := by
  have h := S.redirOK
  unfold Info.redirOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.2, h.2⟩

theorem scan_spec {B : ID} (hBg : B ∈ g.blocks) (hBK : B ∉ (𝓘).K) :
    (∀ c ∈ (g.getB B).controls, (𝓘).freeArg c = true) ∧
      ∀ x ∈ (g.getB B).values, ∀ a ∈ (g.getV x).args, (𝓘).freeArg a = true := by
  have h := S.scanOK
  unfold Info.scanOK at h
  simp only [Array.all_eq_true'] at h
  have := h B hBg
  simp only [Bool.or_eq_true, contains_iff, hBK, false_or] at this
  have hgd : ∀ {α : Type} (a : Array (Option α)) (i : Nat), a.getD i none = (a[i]?).join := by
    intro α a i
    unfold Array.getD
    split
    · rename_i hi; rw [Array.getElem?_eq_getElem hi]; rfl
    · rename_i hi; rw [Array.getElem?_eq_none (by omega)]; rfl
  rw [hgd] at this
  change (g.block? B).all _ = true at this
  unfold Func.getB
  cases hB : g.block? B with
  | none =>
    have h1 : (default : Block).controls = #[] := rfl
    have h2 : (default : Block).values = #[] := rfl
    simp [h1, h2]
  | some gB =>
    rw [hB] at this
    simp only [Option.all_some, Bool.and_eq_true, Array.all_eq_true'] at this
    refine ⟨this.1, fun x hx a ha => ?_⟩
    have h2 := this.2 x hx
    rw [hgd] at h2
    change (g.value? x).all _ = true at h2
    unfold Func.getV at ha
    cases hv : g.value? x with
    | none =>
      have h3 : (default : Value).args = #[] := rfl
      rw [hv] at ha; simp [h3] at ha
    | some v =>
      rw [hv] at h2 ha
      simp only [Option.all_some, Array.all_eq_true'] at h2
      exact h2 a ha

omit S in
theorem freeArg_spec {a : ID} (h : (𝓘).freeArg a = true) :
    a ∉ (𝓘).bvals ∨ (a ∈ (𝓘).vs ∧ (𝓘).look (𝓘).dflt a = some a) := by
  unfold Info.freeArg at h
  simpa [Bool.or_eq_true, contains_iff, Bool.and_eq_true, beq_iff_eq] using h

/-- `p`, `t` and `b` are blocks of `f`. -/
theorem sites_in : s.p ∈ f.blocks ∧ s.te.b ∈ f.blocks ∧ s.b ∈ f.blocks := by
  obtain ⟨Bb, hBb, hbm, -, -, -, -, -, hpr, -, -, -, top, cv, chain, par, c, cc, -, -, -, -, -,
    -, -, -, -, -, hsucc, -⟩ := S.pre
  obtain ⟨j, hj⟩ : ∃ j, Bb.succs[j]? = some s.te := ⟨_, hsucc⟩
  exact ⟨(S.wf.predLink s.b Bb ⟨hbm, hBb⟩ _ _ hpr).1, (S.wf.succLink s.b Bb ⟨hbm, hBb⟩ j _ hj).1,
    hbm⟩

/-- A listed block of `f`: in both tables, with its ID, unchanged outside `K`. -/
theorem gblock {B : ID} (hBm : B ∈ f.blocks) :
    ∃ fB gB, f.block? B = some fB ∧ g.block? B = some gB ∧ fB.id = B ∧ gB.id = B ∧
      (B ∉ (𝓘).K → gB = fB) := by
  obtain ⟨fB, hfB, hid⟩ := S.wf.blockId B hBm
  by_cases hK : B ∈ (𝓘).K
  · obtain ⟨gB, hgB⟩ := SCI.wfKOK_some _ hfB (S.wfKOK hK)
    have hBg : B ∈ g.blocks := by rw [S.gblocks]; exact hBm
    exact ⟨fB, gB, hfB, hgB, hid, (blockOK_spec hBg hfB hgB (S.blockOK hK)).2.1,
      fun h => absurd hK h⟩
  · exact ⟨fB, fB, hfB, by rw [S.block_out hK, hfB], hid, hid, fun _ => rfl⟩

/-- A value listed outside `K` in `f` is the same entry in `g` (but for use counts). -/
theorem gval_out {B : ID} (hBm : B ∈ f.blocks) (hBK : B ∉ (𝓘).K) {fB : Block}
    (hfB : f.block? B = some fB) {x : ID} (hx : x ∈ fB.values) :
    ∃ fx gx, f.value? x = some fx ∧ g.value? x = some gx ∧ fx.id = x ∧ fx.block = B ∧
      gx.id = x ∧ gx.block = B ∧ gx.op = fx.op ∧ gx.type = fx.type ∧ gx.aux = fx.aux ∧
      gx.auxInt = fx.auxInt ∧ gx.args = fx.args := by
  obtain ⟨fx, hfx, hfid, hfb⟩ := S.wf.valueId B fB ⟨hBm, hfB⟩ x hx
  have h := S.value_out hfx (by rw [hfb]; exact hBK)
  rw [hfx] at h
  rcases sameEntry_spec h with ⟨h1, -⟩ | ⟨v, v', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  · cases h1
  · cases h1
    exact ⟨fx, v', hfx, h2, hfid, hfb, h3.trans hfid, h9.trans hfb, h4, h5, h6, h7, h8⟩

theorem vals_out {B : ID} (hBm : B ∈ f.blocks) (hBK : B ∉ (𝓘).K) {fB : Block}
    (hfB : f.block? B = some fB) {x : ID} (hx : x ∈ fB.values) :
    ∃ fx gx, f.value? x = some fx ∧ g.value? x = some gx ∧ fx.id = x ∧ gx.id = fx.id ∧
      gx.op = fx.op ∧ gx.type = fx.type ∧ gx.aux = fx.aux ∧ gx.auxInt = fx.auxInt ∧
      gx.args = fx.args := by
  obtain ⟨fx, gx, hfx, hgx, hfid, -, hgid, -, h1, h2, h3, h4, h5⟩ := S.gval_out hBm hBK hfB hx
  exact ⟨fx, gx, hfx, hgx, hfid, hgid.trans hfid.symm, h1, h2, h3, h4, h5⟩

theorem notb_out {B : ID} (hBm : B ∈ f.blocks) (hBK : B ∉ (𝓘).K) {fB : Block}
    (hfB : f.block? B = some fB) {x : ID} (hx : x ∈ fB.values) : x ∉ (𝓘).bvals := by
  intro hb
  obtain ⟨Bb, hBb, hbm, -, hvals, -⟩ := S.pre
  rw [← hvals] at hb
  have := S.wf.valueOnce B fB s.b Bb ⟨hBm, hfB⟩ ⟨hbm, hBb⟩ x hx hb
  exact hBK (this ▸ S.bK)

/-- **A register outside `b`'s values keeps its block**, listed there in both functions. -/
theorem listed_keep {a : ID} (hl : Listed f a) (hab : a ∉ (𝓘).bvals) :
    ∃ C fC gC, C ∈ f.blocks ∧ f.block? C = some fC ∧ g.block? C = some gC ∧ a ∈ fC.values ∧
      a ∈ gC.values := by
  obtain ⟨C, fC, ⟨hCm, hfC⟩, ha⟩ := hl
  obtain ⟨fC', gC, hfC', hgC, -, -, hout⟩ := S.gblock hCm
  rw [hfC] at hfC'; cases hfC'
  refine ⟨C, fC, gC, hCm, hfC, hgC, ha, ?_⟩
  by_cases hK : C ∈ (𝓘).K
  · have hCg : C ∈ g.blocks := by rw [S.gblocks]; exact hCm
    rcases (blockOK_spec hCg hfC hgC (S.blockOK hK)).2.2 with
      ⟨-, hCb⟩ | ⟨-, -, -, -, hnodes, -, -, -, -, hph⟩
    · exfalso; apply hab
      obtain ⟨Bb, hBb, -, -, hvals, -⟩ := S.pre
      subst hCb
      simp only [infoOf_s] at hfC
      rw [hBb] at hfC; cases hfC
      rw [← hvals]; exact ha
    · cases hp : isPhiIn f a
      · exact (mem_nodesOf.1 ((SCI.nodesOK_spec _ hnodes).1 a (mem_nodesOf.2 ⟨ha, hp⟩)).1).1
      · have := (SCI.phisOK_spec _ (hph 0 (by omega)).2).2.1 a ha hp
        exact Classical.byContradiction fun hn => hab (this.2 hn)
  · rw [hout hK]; exact ha

theorem listed_keep' {a : ID} (hl : Listed f a) (hab : a ∉ (𝓘).bvals) : Listed g a := by
  obtain ⟨C, -, gC, hCm, -, hgC, -, hg⟩ := S.listed_keep hl hab
  exact ⟨C, gC, ⟨by rw [S.gblocks]; exact hCm, hgC⟩, hg⟩

/-! ## `WF ce g` -/

theorem g_blockId : ∀ bid ∈ g.blocks, ∃ b, g.block? bid = some b ∧ b.id = bid := by
  intro bid hbm
  rw [S.gblocks] at hbm
  obtain ⟨-, gB, -, hgB, -, hid, -⟩ := S.gblock hbm
  exact ⟨gB, hgB, hid⟩

/-- A listed block of `g`: its `f` block, and its `wfKOK` facts if in `K`. -/
theorem gblock' {bid : ID} {gB : Block} (hb : BlockIn g bid gB) :
    ∃ fB, bid ∈ f.blocks ∧ f.block? bid = some fB ∧ (bid ∉ (𝓘).K → gB = fB) := by
  obtain ⟨hbm, hgB⟩ := hb
  rw [S.gblocks] at hbm
  obtain ⟨fB, gB', hfB, hgB', -, -, hout⟩ := S.gblock hbm
  rw [hgB] at hgB'; cases hgB'
  exact ⟨fB, hbm, hfB, hout⟩

theorem g_valueId : ∀ bid b, BlockIn g bid b → ∀ vid ∈ b.values,
    ∃ v, g.value? vid = some v ∧ v.id = vid ∧ v.block = bid := by
  intro bid gB hb vid hv
  obtain ⟨fB, hbm, hfB, hout⟩ := S.gblock' hb
  by_cases hK : bid ∈ (𝓘).K
  · obtain ⟨-, -, -, -, -, hvals, -⟩ := SCI.wfKOK_spec _ hfB hb.2 (S.wfKOK hK)
    obtain ⟨v, hv', hid, hok⟩ := hvals vid hv
    obtain ⟨-, gB', -, hgB', -, hgid, -⟩ := S.gblock hbm
    rw [hb.2] at hgB'; cases hgB'
    exact ⟨v, hv', hid, by rw [(WFCheckFacts.valueOK_spec hok).2.2.1, hgid]⟩
  · rw [hout hK] at hv
    obtain ⟨-, gx, -, hgx, -, -, hgid, hgb, -⟩ := S.gval_out hbm hK hfB hv
    exact ⟨gx, hgx, hgid, hgb⟩

/-- A value listed in `g`: per-op shape facts in `K`, `f`'s value outside. -/
theorem gvalue_cases {bid : ID} {gB : Block} {vid : ID} {v : Value} (hv : ValueIn g bid gB vid v) :
    ∃ fB, bid ∈ f.blocks ∧ f.block? bid = some fB ∧
      ((bid ∈ (𝓘).K ∧ WFCheck.valueOK gB v = true) ∨
        (bid ∉ (𝓘).K ∧ gB = fB ∧ ∃ fv, ValueIn f bid fB vid fv ∧ v.op = fv.op ∧
          v.args = fv.args ∧ v.auxInt = fv.auxInt)) := by
  obtain ⟨hb, hvid, hgv⟩ := hv
  obtain ⟨fB, hbm, hfB, hout⟩ := S.gblock' hb
  refine ⟨fB, hbm, hfB, ?_⟩
  by_cases hK : bid ∈ (𝓘).K
  · obtain ⟨-, -, -, -, -, hvals, -⟩ := SCI.wfKOK_spec _ hfB hb.2 (S.wfKOK hK)
    obtain ⟨v', hv', -, hok⟩ := hvals vid hvid
    rw [hgv] at hv'; cases hv'
    exact .inl ⟨hK, hok⟩
  · have he := hout hK
    subst he
    obtain ⟨fx, gx, hfx, hgx, -, -, -, -, h1, -, -, h4, h5⟩ := S.gval_out hbm hK hfB hvid
    rw [hgv] at hgx; cases hgx
    exact .inr ⟨hK, rfl, fx, ⟨⟨hbm, hfB⟩, hvid, hfx⟩, h1, h5, h4⟩

theorem g_valuesNodup : ∀ bid b, BlockIn g bid b → b.values.toList.Nodup := by
  intro bid gB hb
  obtain ⟨fB, hbm, hfB, hout⟩ := S.gblock' hb
  by_cases hK : bid ∈ (𝓘).K
  · rcases (SCI.wfKOK_spec _ hfB hb.2 (S.wfKOK hK)).2.2.2.2.2.2 with h | h
    · rw [h]; exact S.wf.valuesNodup bid fB ⟨hbm, hfB⟩
    · exact h
  · rw [hout hK]; exact S.wf.valuesNodup bid fB ⟨hbm, hfB⟩

theorem g_valueOnce : ∀ bid1 b1 bid2 b2, BlockIn g bid1 b1 → BlockIn g bid2 b2 →
    ∀ vid, vid ∈ b1.values → vid ∈ b2.values → bid1 = bid2 := by
  intro bid1 b1 bid2 b2 h1 h2 vid hv1 hv2
  obtain ⟨v, hv, -, hb⟩ := S.g_valueId bid1 b1 h1 vid hv1
  obtain ⟨v', hv', -, hb'⟩ := S.g_valueId bid2 b2 h2 vid hv2
  rw [hv] at hv'; cases hv'
  rw [← hb, hb']

theorem g_predLink : ∀ bid b, BlockIn g bid b → ∀ (i : Nat) (e : Edge), b.preds[i]? = some e →
    e.b ∈ g.blocks ∧ ∃ p, g.block? e.b = some p ∧ p.succs[e.i]? = some ⟨bid, i⟩ := by
  intro bid gB hb i e he
  obtain ⟨fB, hbm, hfB, hout⟩ := S.gblock' hb
  rw [S.gblocks]
  by_cases hK : bid ∈ (𝓘).K
  · obtain ⟨-, hp, -⟩ := SCI.wfKOK_spec _ hfB hb.2 (S.wfKOK hK)
    obtain ⟨hl, hm⟩ := hp i e he
    refine ⟨?_, hl⟩
    rcases hm with hm | ⟨e', he', hb'⟩
    · rw [hm]; exact S.sites_in.1
    · obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 he'
      rw [← hb']; exact (S.wf.predLink bid fB ⟨hbm, hfB⟩ k e' hk).1
  · rw [hout hK] at he
    obtain ⟨hem, fP, hfP, hPs⟩ := S.wf.predLink bid fB ⟨hbm, hfB⟩ i e he
    refine ⟨hem, ?_⟩
    obtain ⟨fP', gP, hfP', hgP, -, -, hout'⟩ := S.gblock hem
    rw [hfP] at hfP'; cases hfP'
    refine ⟨gP, hgP, ?_⟩
    by_cases hK' : e.b ∈ (𝓘).K
    · exact (SCI.wfKOK_spec _ hfP hgP (S.wfKOK hK')).2.2.2.2.1 _ _ hPs hK
    · rw [hout' hK']; exact hPs

theorem g_succLink : ∀ bid b, BlockIn g bid b → ∀ (j : Nat) (e : Edge), b.succs[j]? = some e →
    e.b ∈ g.blocks ∧ ∃ c, g.block? e.b = some c ∧ c.preds[e.i]? = some ⟨bid, j⟩ := by
  intro bid gB hb j e he
  obtain ⟨fB, hbm, hfB, hout⟩ := S.gblock' hb
  rw [S.gblocks]
  by_cases hK : bid ∈ (𝓘).K
  · obtain ⟨-, -, hs, -⟩ := SCI.wfKOK_spec _ hfB hb.2 (S.wfKOK hK)
    obtain ⟨hl, hm⟩ := hs j e he
    refine ⟨?_, hl⟩
    rcases hm with hm | ⟨e', he', hb'⟩
    · rw [hm]; exact S.sites_in.2.1
    · obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 he'
      rw [← hb']; exact (S.wf.succLink bid fB ⟨hbm, hfB⟩ k e' hk).1
  · rw [hout hK] at he
    obtain ⟨hem, fC, hfC, hCp⟩ := S.wf.succLink bid fB ⟨hbm, hfB⟩ j e he
    refine ⟨hem, ?_⟩
    obtain ⟨fC', gC, hfC', hgC, -, -, hout'⟩ := S.gblock hem
    rw [hfC] at hfC'; cases hfC'
    refine ⟨gC, hgC, ?_⟩
    by_cases hK' : e.b ∈ (𝓘).K
    · exact (SCI.wfKOK_spec _ hfC hgC (S.wfKOK hK')).2.2.2.1 _ _ hCp hK
    · rw [hout' hK']; exact hCp

/-- A moved phi (default fact) is listed in `g`: in a block entered from `b` or `t`. -/
theorem moved_listed {v : ID} (hv : v ∈ (𝓘).vs) (hd : (𝓘).look (𝓘).dflt v = some v) :
    Listed g v := by
  obtain ⟨-, hl⟩ := dflt_spec hd
  obtain ⟨gv, Bk, hgv, hBk, hw⟩ := listedIn_spec hl
  obtain ⟨hMr, -, hMe, -⟩ := SCI.closeOK_spec _ S.closeOK hv hd
  rw [getV_of hgv] at hMe
  refine ⟨gv.block, Bk, ⟨?_, hBk⟩, hw⟩
  rcases hMe with hM | ⟨e, he, hb⟩
  · rw [hM, S.gblocks]; exact S.sites_in.2.1
  · have hMK := (S.region_spec (getV_of hgv ▸ hMr)).2.2.1
    rw [getB_of hBk] at he
    obtain ⟨fM, hfM⟩ : ∃ fM, f.block? gv.block = some fM := by
      have := S.wfKOK hMK
      unfold Info.wfKOK at this
      rw [hBk] at this
      cases hf : f.block? gv.block with
      | none => rw [hf] at this; cases this
      | some fM => exact ⟨fM, rfl⟩
    obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 he
    obtain ⟨⟨P, hP, hPs⟩, -⟩ := (SCI.wfKOK_spec _ hfM hBk (S.wfKOK hMK)).2.1 k e hk
    have heb : e.b ∈ g.blocks := by
      rw [S.gblocks]
      rcases hb with hb | hb
      · rw [hb]; exact S.sites_in.2.2
      · rw [hb]; exact S.sites_in.2.1
    exact (S.g_succLink e.b P ⟨heb, hP⟩ e.i _ hPs).1

/-- An argument of a `Phi` of `b` in `f` along an edge, outside `b`'s values, is listed in `g`. -/
theorem avail_listed {P w : ID} (h : (𝓘).availAt f P w = true) : Listed g w := by
  obtain ⟨hw, z, hz, hp, j, e, -, -, ha⟩ := SCI.availAt_spec _ h
  obtain ⟨Bb, hBb, hbm, -, hvals, -⟩ := S.pre
  obtain ⟨fz, hfz, -⟩ := isPhiIn_iff.1 hp
  rw [getV_of hfz] at ha
  exact S.listed_keep' (argListed_of S.wf hbm hBb (hvals ▸ hz) hfz (args_get_mem ha)) hw

/-- A use passing `useOK` at a listed block reads a listed register. -/
theorem useOK_listed {P w : ID} {a? : Option ID} {rd : Bool} (hP : P ∈ g.blocks)
    (h : (𝓘).useOK f g P w a? rd = true) (hsrc : ∀ a, a? = some a → Listed f a) :
    Listed g w := by
  rcases SCI.useOK_spec _ h with ⟨ha, hb⟩ | ⟨hl, h⟩
  · exact S.listed_keep' (hsrc w ha) hb
  · obtain ⟨v, Bk, hv, hBk, hw⟩ := listedIn_spec hl
    rcases h with h | ⟨ha, -, hfree, -, -⟩ | h | ⟨-, hne, h⟩
    · rw [blockOf_of hv] at h
      rw [h] at hBk
      exact ⟨P, Bk, ⟨hP, hBk⟩, hw⟩
    · rcases freeArg_spec hfree with hb | ⟨hvs, hd⟩
      · exact S.listed_keep' (hsrc w ha) hb
      · exact S.moved_listed hvs hd
    · exact S.avail_listed h
    · have hpos : 0 < (g.getB s.b).preds.size := by
        rcases Nat.eq_zero_or_pos (g.getB s.b).preds.size with h0 | h0
        · simp [Array.isEmpty, h0] at hne
        · exact h0
      exact S.avail_listed (h _ (Array.getElem_mem hpos))

theorem g_argListed : ∀ bid b vid v, ValueIn g bid b vid v → ∀ a ∈ v.args, Listed g a := by
  intro bid gB vid v hv a ha
  obtain ⟨⟨hbm, hgB⟩, hvid, hgv⟩ := hv
  obtain ⟨fB, hbf, hfB, hout⟩ := S.gblock' ⟨hbm, hgB⟩
  obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 ha
  have hgv' : g.getV vid = v := getV_of hgv
  by_cases hK : bid ∈ (𝓘).K
  · have hd := SCI.domKOK_spec _ (S.domKOK hK)
    rw [getB_of hgB, getB_of hfB] at hd
    by_cases hp : v.op = .Phi
    · obtain ⟨-, -, -, -, -, hvals, -⟩ := SCI.wfKOK_spec _ hfB hgB (S.wfKOK hK)
      obtain ⟨v', hv', -, hok⟩ := hvals vid hvid
      rw [hgv] at hv'; cases hv'
      have hsz := (WFCheckFacts.valueOK_spec hok).2.2.2 hp
      have hkl : k < gB.preds.size := hsz ▸ (Array.getElem?_eq_some_iff.1 hk).1
      obtain ⟨a?, hu, hsrc⟩ := hd.1 vid hvid (by rw [hgv']; exact hp) k gB.preds[k] a
        (Array.getElem?_eq_getElem hkl) (by rw [hgv']; exact hk)
      refine S.useOK_listed (S.g_predLink bid gB ⟨hbm, hgB⟩ k _
        (Array.getElem?_eq_getElem hkl)).1 hu fun a' h' => ?_
      obtain ⟨hxf, fv, hfv, -, hr⟩ := hsrc a' h'
      rcases hr with ⟨-, -, hr⟩ | ⟨-, -, hr⟩
      · exact argListed_of S.wf hbf hfB hxf hfv (args_get_mem hr)
      · exact argListed_of S.wf hbf hfB hxf hfv (args_get_mem hr)
    · obtain ⟨a?, hu, hsrc⟩ := hd.2.1 vid hvid (by rw [hgv']; exact hp) k a (by rw [hgv']; exact hk)
      refine S.useOK_listed hbm hu fun a' h' => ?_
      obtain ⟨hxf, fv, hfv, -, hr⟩ := hsrc a' h'
      exact argListed_of S.wf hbf hfB hxf hfv (args_get_mem hr)
  · have he := hout hK
    subst he
    have hfree := (S.scan_spec hbm hK).2 vid (by rw [getB_of hgB]; exact hvid) a
      (by rw [hgv']; exact ha)
    rcases freeArg_spec hfree with hb | ⟨hvs, hd⟩
    · obtain ⟨fx, gx, hfx, hgx, -, -, -, -, -, -, -, -, hargs⟩ := S.gval_out hbf hK hfB hvid
      rw [hgv] at hgx; cases hgx
      exact S.listed_keep' (argListed_of S.wf hbf hfB hvid hfx (hargs ▸ ha)) hb
    · exact S.moved_listed hvs hd

theorem g_ctrlListed : ∀ bid b, BlockIn g bid b → ∀ c ∈ b.controls, Listed g c := by
  intro bid gB hb c hc
  obtain ⟨fB, hbf, hfB, hout⟩ := S.gblock' hb
  obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 hc
  by_cases hK : bid ∈ (𝓘).K
  · have hd := (SCI.domKOK_spec _ (S.domKOK hK)).2.2
    rw [getB_of hb.2, getB_of hfB] at hd
    exact S.useOK_listed hb.1 (hd k c hk) fun a h' =>
      S.wf.ctrlListed bid fB ⟨hbf, hfB⟩ a (Array.mem_of_getElem? h')
  · have he := hout hK
    subst he
    have hfree := (S.scan_spec hb.1 hK).1 c (by rw [getB_of hb.2]; exact hc)
    rcases freeArg_spec hfree with hb' | ⟨hvs, hd⟩
    · exact S.listed_keep' (S.wf.ctrlListed bid gB ⟨hbf, hfB⟩ c hc) hb'
    · exact S.moved_listed hvs hd

/-- **The result is well formed**, without a check of the whole result. -/
theorem wfg : WF ce g where
  blockId := S.g_blockId
  blocksNodup := by rw [S.gblocks]; exact S.wf.blocksNodup
  valueId := S.g_valueId
  valuesNodup := S.g_valuesNodup
  valueOnce := S.g_valueOnce
  predLink := S.g_predLink
  succLink := S.g_succLink
  arity := fun bid b vid v hv hn => by
    obtain ⟨fB, -, -, h⟩ := S.gvalue_cases hv
    rcases h with ⟨-, hok⟩ | ⟨-, -, fv, hfv, hop, hargs, -⟩
    · exact (WFCheckFacts.valueOK_spec hok).1 hn
    · rw [hargs, hop]; exact S.wf.arity _ _ _ _ hfv (hop ▸ hn)
  phiArity := fun bid b vid v hv hp => by
    obtain ⟨fB, -, -, h⟩ := S.gvalue_cases hv
    rcases h with ⟨-, hok⟩ | ⟨-, hb, fv, hfv, hop, hargs, -⟩
    · exact (WFCheckFacts.valueOK_spec hok).2.2.2 hp
    · rw [hargs, hb]; exact S.wf.phiArity _ _ _ _ hfv (hop ▸ hp)
  boolAux := fun bid b vid v hv hn => by
    obtain ⟨fB, -, -, h⟩ := S.gvalue_cases hv
    rcases h with ⟨-, hok⟩ | ⟨-, -, fv, hfv, hop, -, haux⟩
    · exact (WFCheckFacts.valueOK_spec hok).2.1 hn
    · rw [haux]; exact S.wf.boolAux _ _ _ _ hfv (hop ▸ hn)
  argListed := S.g_argListed
  ctrlListed := S.g_ctrlListed
  entry := by rw [S.gentry, S.gblocks]; exact S.wf.entry
  entryPreds := fun b hb => by
    rw [S.gentry] at hb
    by_cases hK : f.entry ∈ (𝓘).K
    · obtain ⟨fE, hfE, -⟩ := S.wf.blockId f.entry S.wf.entry
      have := (SCI.wfKOK_spec _ hfE hb (S.wfKOK hK)).1 S.gentry.symm
      rw [this]; rfl
    · rw [S.block_out hK] at hb
      exact S.wf.entryPreds b hb

/-- A register outside `b`'s values has the same block in both functions. -/
theorem blockOf_keep {a : ID} (hl : Listed f a) (hab : a ∉ (𝓘).bvals) :
    DomCert.blockOf g a = DomCert.blockOf f a := by
  obtain ⟨C, fC, gC, hCm, hfC, hgC, hf, hg⟩ := S.listed_keep hl hab
  obtain ⟨fv, hfv, -, hfb⟩ := S.wf.valueId C fC ⟨hCm, hfC⟩ a hf
  obtain ⟨gv, hgv, -, hgb⟩ := S.wfg.valueId C gC ⟨by rw [S.gblocks]; exact hCm, hgC⟩ a hg
  rw [blockOf_of hfv, blockOf_of hgv, hfb, hgb]

end Setup

end GoFV.Proof.ShortCirc
