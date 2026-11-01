import GoFV.Proof.Pass.ShortCircSetup

/-!
# Checked `shortcircuitBlock`: the per-block checks as propositions

The Boolean parts of `Info.blockOK` (`phisOK`, `nodesOK`, `argRel`, `outOK`, `succOK`, `newOK`,
`schedOK`) and the global checks (`redirOK`, `regionOK`, `frameOK`, `exitOK`, `scanOK`) turned
into the facts the simulation and the use-dominance proof read.
-/

namespace GoFV.Proof.ShortCirc

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.ShortCircuit GoFV.Proof Dom

namespace SCI

variable (I : Info) {f g : Func} {fB gB : Block} {pin out : Facts}

theorem argRel_iff {w a : ID} :
    I.argRel f g fB gB pin out w a = true ↔
      (w ∈ Info.nodesOf g gB ∧ I.home f g fB out w = some a) ∨
      (w ∉ Info.nodesOf g gB ∧ a ∉ Info.nodesOf f fB ∧ I.pinRel f g fB gB pin w a = true) := by
  unfold Info.argRel
  by_cases h : (Info.nodesOf g gB).contains w = true
  · simp only [h, ↓reduceIte, beq_iff_eq]
    have := contains_iff.1 h
    constructor
    · intro h'; exact .inl ⟨this, h'⟩
    · rintro (⟨-, h'⟩ | ⟨h', -⟩)
      · exact h'
      · exact absurd this h'
  · simp only [h, ↓reduceIte, Bool.false_eq_true, Bool.and_eq_true, Bool.not_eq_true',
      contains_false]
    have : w ∉ Info.nodesOf g gB := fun hm => h (contains_iff.2 hm)
    constructor
    · rintro ⟨h1, h2⟩; exact .inr ⟨this, h1, h2⟩
    · rintro (⟨h', -⟩ | ⟨-, h1, h2⟩)
      · exact absurd h' this
      · exact ⟨h1, h2⟩

/-- **The `Phi`s along a target edge** (`phisOK`). -/
theorem phisOK_spec {iT iS : Nat} {E : Facts} {inR : Bool}
    (h : I.phisOK f g fB gB pin iT iS E inR = true) :
    (∀ z ∈ gB.values, isPhiIn g z = true →
      (z ∈ fB.values → isPhiIn f z = true ∧ I.tyEq (g.getV z).type (f.getV z).type = true ∧
        ∃ w a, (g.getV z).args[iT]? = some w ∧ (f.getV z).args[iS]? = some a ∧
          I.trans E a = some w) ∧
      (z ∉ fB.values → ∃ v ∈ I.vs, I.look pin v = some z)) ∧
    (∀ y ∈ fB.values, isPhiIn f y = true →
      (y ∈ gB.values → isPhiIn g y = true ∨
        (y ∈ I.bvals ∧ (((g.getV y).op = .Invalid ∧ (g.getV y).args = #[]) ∨
          ((g.getV y).op = .Copy ∧ I.tyEq (g.getV y).type (f.getV y).type = true ∧
            (g.getV y).args.size = 1 ∧ ∃ w a, (g.getV y).args[0]? = some w ∧
              (f.getV y).args[iS]? = some a ∧ I.trans E a = some w ∧ w ∉ gB.values)))) ∧
      (y ∉ gB.values → y ∈ I.bvals)) ∧
    (∀ v ∈ I.vs, ∀ w, I.look pin v = some w →
      (w ∈ gB.values → isPhiIn g w = true ∧ w ∉ fB.values ∧
        I.tyEq (g.getV w).type (f.getV v).type = true ∧ (inR = true ∨ v ∈ fB.values) ∧
        ∃ a', (g.getV w).args[iT]? = some a' ∧
          (v ∈ fB.values → ∃ a, (f.getV v).args[iS]? = some a ∧ I.trans E a = some a') ∧
          (v ∉ fB.values → I.look E v = some a')) ∧
      (w ∉ gB.values →
        (v ∈ fB.values → ∃ a, (f.getV v).args[iS]? = some a ∧ I.trans E a = some w ∧
          I.tyEq (f.getV a).type (f.getV v).type = true) ∧
        (v ∉ fB.values → I.look E v = some w))) := by
  unfold Info.phisOK at h
  simp only [Bool.and_eq_true, Array.all_eq_true'] at h
  obtain ⟨⟨hz, hy⟩, hv⟩ := h
  refine ⟨fun z hzm hph => ⟨fun hzf => ?_, fun hzf => ?_⟩, fun y hym hph => ⟨fun hyg => ?_, fun hyg => ?_⟩,
    fun v hvm w hw => ⟨fun hwg => ?_, fun hwg => ?_⟩⟩
  · have := hz z hzm
    simp only [hph, Bool.not_true, Bool.false_or, contains_iff.2 hzf, ↓reduceIte,
      Bool.and_eq_true] at this
    obtain ⟨⟨h1, h2⟩, h3⟩ := this
    refine ⟨h1, h2, ?_⟩
    split at h3
    · rename_i w a hw ha
      exact ⟨w, a, hw, ha, by simpa using h3⟩
    · cases h3
  · have := hz z hzm
    simp only [hph, Bool.not_true, Bool.false_or, ↓reduceIte] at this
    rw [if_neg (by simpa [contains_iff] using hzf)] at this
    simp only [Array.any_eq_true', beq_iff_eq] at this
    exact this
  · have := hy y hym
    simp only [hph, Bool.not_true, Bool.false_or, contains_iff.2 hyg, ↓reduceIte,
      Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Array.isEmpty_iff] at this
    rcases this with h1 | ⟨h1, h2⟩
    · exact .inl h1
    · refine .inr ⟨contains_iff.1 h1, ?_⟩
      rcases h2 with h2 | h2
      · exact .inl h2
      · obtain ⟨⟨⟨h3, h4⟩, h5⟩, h6⟩ := h2
        refine .inr ⟨h3, h4, h5, ?_⟩
        split at h6
        · rename_i w a hw ha
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', contains_false] at h6
          exact ⟨w, a, hw, ha, h6.1, h6.2⟩
        · cases h6
  · have := hy y hym
    simp only [hph, Bool.not_true, Bool.false_or] at this
    rw [if_neg (by simpa [contains_iff] using hyg)] at this
    exact contains_iff.1 this
  · have := hv v hvm
    simp only [hw, contains_iff.2 hwg, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true',
      contains_false, Bool.or_eq_true, contains_iff] at this
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := this
    refine ⟨h1, h2, h3, h4, ?_⟩
    split at h5
    · rename_i a' ha'
      refine ⟨a', ha', fun hvf => ?_, fun hvf => ?_⟩
      · simp only [hvf, ↓reduceIte] at h5
        split at h5
        · rename_i a ha; exact ⟨a, ha, by simpa using h5⟩
        · cases h5
      · rw [if_neg (by simpa using hvf)] at h5
        simpa using h5
    · cases h5
  · have := hv v hvm
    simp only [hw] at this
    rw [if_neg (by simpa [contains_iff] using hwg)] at this
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', contains_false] at this
    obtain ⟨h1, h2⟩ := this
    refine ⟨fun hvf => ?_, fun hvf => ?_⟩
    · simp only [contains_iff.2 hvf, ↓reduceIte] at h1
      rcases h2 with h2 | h2
      · exact absurd hvf h2
      split at h1
      · rename_i a ha
        simp only [ha] at h2
        exact ⟨a, ha, by simpa using h1, h2⟩
      · cases h1
    · rw [if_neg (by simpa [contains_iff] using hvf)] at h1
      simpa using h1

theorem sameNode_spec {x : ID} (h : I.sameNode f g fB gB pin out x = true) :
    (g.getV x).op = (f.getV x).op ∧ (g.getV x).type = (f.getV x).type ∧
    (g.getV x).aux = (f.getV x).aux ∧ (g.getV x).auxInt = (f.getV x).auxInt ∧
    (g.getV x).args.size = (f.getV x).args.size ∧
    ∀ (k : Nat) (w a : ID), (g.getV x).args[k]? = some w → (f.getV x).args[k]? = some a →
      I.argRel f g fB gB pin out w a = true := by
  unfold Info.sameNode at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, h3, h4, h5, fun k w a hw ha => ?_⟩
  have hk : k < (g.getV x).args.size := (Array.getElem?_eq_some_iff.1 hw).1
  have hk' : k < (f.getV x).args.size := (Array.getElem?_eq_some_iff.1 ha).1
  have := h6 ((g.getV x).args[k], (f.getV x).args[k])
    (Array.mem_iff_getElem.2 ⟨k, by simp only [Array.size_zip]; omega, by simp⟩)
  rw [Array.getElem?_eq_some_iff.1 hw |>.2, Array.getElem?_eq_some_iff.1 ha |>.2] at this
  exact this

theorem carrierOK_spec {inRb : Bool} {x : ID} (h : I.carrierOK f g fB gB pin out inRb x = true) :
    ∃ v, I.home f g fB out x = some v ∧ inRb = true ∧ (g.getV x).op = .Copy ∧
      I.tyEq (g.getV x).type (f.getV v).type = true ∧ (g.getV x).args.size = 1 ∧
      ∃ w, (g.getV x).args[0]? = some w ∧
        (w ∈ Info.nodesOf g gB → I.home f g fB out w = some v) ∧
        (w ∉ Info.nodesOf g gB → I.look pin v = some w) := by
  unfold Info.carrierOK at h
  split at h
  · rename_i v hv
    obtain ⟨h1, h5⟩ := Eq.mp (Bool.and_eq_true _ _) h
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h1
    refine ⟨v, hv, h1, h2, h3, h4, ?_⟩
    split at h5
    · rename_i w hw
      refine ⟨w, hw, fun hwn => ?_, fun hwn => ?_⟩
      · have hc : (Info.nodesOf g gB).contains w = true := contains_iff.2 hwn
        simp only [hc, ↓reduceIte] at h5
        simpa using h5
      · have hc : (Info.nodesOf g gB).contains w = false := by simpa [contains_iff] using hwn
        simp only [hc, Bool.false_eq_true, ↓reduceIte] at h5
        simpa using h5
    · cases h5
  · cases h

/-- **A target non-`Phi` of a checked block** (`nodeOK`). -/
theorem nodeOK_spec {inRb : Bool} {x : ID} (h : I.nodeOK f g fB gB pin out inRb x = true) :
    (x ∈ fB.values ∧ isPhiIn f x = false → I.sameNode f g fB gB pin out x = true) ∧
    (¬ (x ∈ fB.values ∧ isPhiIn f x = false) → (g.getV x).op = .Invalid →
      (g.getV x).args = #[] ∧ (x ∉ fB.values ∨ x ∈ I.bvals)) ∧
    (¬ (x ∈ fB.values ∧ isPhiIn f x = false) → (g.getV x).op ≠ .Invalid → x ∈ fB.values →
      x ∈ I.bvals ∧ (g.getV x).op = .Copy) ∧
    (¬ (x ∈ fB.values ∧ isPhiIn f x = false) → (g.getV x).op ≠ .Invalid → x ∉ fB.values →
      I.carrierOK f g fB gB pin out inRb x = true) := by
  unfold Info.nodeOK at h
  refine ⟨fun hxs => ?_, fun hxs hinv => ?_, fun hxs hinv hxf => ?_, fun hxs hinv hxf => ?_⟩
  · have hc : (fB.values.contains x && !isPhiIn f x) = true := by
      simp [contains_iff, hxs.1, hxs.2]
    simpa only [hc, ↓reduceIte] using h
  · have hc : (fB.values.contains x && !isPhiIn f x) = false := by
      simpa [contains_iff] using hxs
    have hi : ((g.getV x).op == .Invalid) = true := by simpa using hinv
    simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
    simp only [hi, ↓reduceIte] at h
    simpa only [Bool.and_eq_true, Array.isEmpty_iff, Bool.or_eq_true, Bool.not_eq_true',
      contains_false, contains_iff] using h
  · have hc : (fB.values.contains x && !isPhiIn f x) = false := by
      simpa [contains_iff] using hxs
    have hi : ((g.getV x).op == .Invalid) = false := by simpa using hinv
    have hf : fB.values.contains x = true := contains_iff.2 hxf
    simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
    simp only [hi, Bool.false_eq_true, ↓reduceIte] at h
    simp only [hf, ↓reduceIte] at h
    simpa only [Bool.and_eq_true, beq_iff_eq, contains_iff] using h
  · have hc : (fB.values.contains x && !isPhiIn f x) = false := by
      simpa [contains_iff] using hxs
    have hi : ((g.getV x).op == .Invalid) = false := by simpa using hinv
    have hf : fB.values.contains x = false := by simpa [contains_iff] using hxf
    simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
    simp only [hi, Bool.false_eq_true, ↓reduceIte] at h
    simpa only [hf, Bool.false_eq_true, ↓reduceIte] using h

/-- **The non-`Phi`s of a checked block** (`nodesOK`). -/
theorem nodesOK_spec {inRb : Bool} (h : I.nodesOK f g fB gB pin out inRb = true) :
    (∀ y ∈ Info.nodesOf f fB, y ∈ Info.nodesOf g gB ∧ I.home f g fB out y = some y) ∧
    ∀ x ∈ Info.nodesOf g gB, I.nodeOK f g fB gB pin out inRb x = true := by
  unfold Info.nodesOK at h
  obtain ⟨hS, hT⟩ := Eq.mp (Bool.and_eq_true _ _) h
  refine ⟨fun y hy => ?_, Array.all_eq_true'.1 hT⟩
  have := Array.all_eq_true'.1 hS y hy
  simpa only [Bool.and_eq_true, beq_iff_eq, contains_iff] using this

/-- **The facts at the end of a checked block** (`outOK`). -/
theorem outOK_spec (h : I.outOK f g fB gB pin out = true) :
    ∀ v ∈ I.vs, ∀ w, I.look out v = some w →
      (w ∈ Info.nodesOf g gB → I.home f g fB out w = some v) ∧
      (w ∉ Info.nodesOf g gB → I.look pin v = some w) := by
  unfold Info.outOK at h
  simp only [Array.all_eq_true'] at h
  intro v hv w hw
  have := h v hv
  simp only [hw] at this
  refine ⟨fun hwn => ?_, fun hwn => ?_⟩
  · have hc' : (Info.nodesOf g gB).contains w = true := contains_iff.2 hwn
    simp only [hc', ↓reduceIte] at this
    simpa using this
  · have hc' : (Info.nodesOf g gB).contains w = false := by simpa [contains_iff] using hwn
    simp only [hc', Bool.false_eq_true, ↓reduceIte] at this
    simpa using this

/-- **The successors of a checked block** (`succOK`). -/
theorem succOK_spec {B : ID} (h : I.succOK fB gB B = true) :
    gB.succs.size = fB.succs.size ∧ ∀ k e' e, gB.succs[k]? = some e' → fB.succs[k]? = some e →
      (B = I.s.p ∧ k = I.s.pi ∧ e' = ⟨I.t, I.tn⟩ ∧ e = ⟨I.s.b, I.s.cidx⟩) ∨
      (e'.b = e.b ∧ e.i = I.srcIdx e.b e'.i ∧ I.redir e'.b e'.i = false) := by
  unfold Info.succOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  refine ⟨h.1, fun k e' e he' he => ?_⟩
  have hk : k < gB.succs.size := (Array.getElem?_eq_some_iff.1 he').1
  have := h.2 k hk
  simp only [he', he, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at this
  rcases this with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ | ⟨⟨h1, h2⟩, h3⟩
  · exact .inl ⟨h1, h2, h3, h4⟩
  · exact .inr ⟨h1, h2, h3⟩

/-- **New values of a checked block** (`newOK`). -/
theorem newOK_spec (h : I.newOK f fB gB = true) :
    ∀ x ∈ gB.values, x ∈ fB.values ∨ x ∈ I.bvals ∨ listedIn f x = false := by
  unfold Info.newOK at h
  simp only [Array.all_eq_true', Bool.or_eq_true, Bool.not_eq_true', contains_iff, or_assoc] at h
  exact h

end SCI

/-- The schedule scan: along the list, every root comes after every value before it. -/
theorem schedScan_spec {pos : ID → Nat} {root : ID → Bool} :
    ∀ {m : Option Nat} {l : List ID}, Info.schedScan pos root m l = true →
      ∀ (k : Nat) (r : ID), l[k]? = some r → root r = true →
        (∀ x, m = some x → x < pos r) ∧ ∀ (j : Nat) (y : ID), j < k → l[j]? = some y → pos y < pos r
  | _, [], _, k, r, hr, _ => by simp at hr
  | m, x :: rest, h, k, r, hr, hroot => by
    unfold Info.schedScan at h
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    obtain ⟨h1, h2⟩ := h
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hr
      subst hr
      rcases h1 with h1 | h1
      · rw [h1] at hroot; cases hroot
      · refine ⟨fun x hx => ?_, fun j y hj => absurd hj (by omega)⟩
        subst hx; simpa using h1
    | succ k =>
      simp only [List.getElem?_cons_succ] at hr
      obtain ⟨ih1, ih2⟩ := schedScan_spec h2 k r hr hroot
      have hmax := ih1 _ rfl
      refine ⟨fun y hy => ?_, fun j y hj hy => ?_⟩
      · subst hy; simp at hmax; omega
      · cases j with
        | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hy
          subst hy; omega
        | succ j => exact ih2 j y (by omega) hy

namespace SCI

variable (I : Info) {f g : Func} {fB gB : Block}

/-- **The schedules of a checked block** (`schedOK`): if the source panics at a root, every source
value the target lists before it, the source lists before it too. -/
theorem schedOK_spec (h : Info.schedOK f g fB gB = true) :
    ∃ oS oT, Sem.schedule f fB = some oS ∧ Sem.schedule g gB = some oT ∧
      ∀ (k : Nat) (r : ID), (oT.toList.filter ((Info.nodesOf f fB).contains ·))[k]? = some r →
        Sem.prio (f.getV r).op ≠ 0 →
        ∀ (j : Nat) (y : ID), j < k →
          (oT.toList.filter ((Info.nodesOf f fB).contains ·))[j]? = some y →
          oS.toList.idxOf y < oS.toList.idxOf r := by
  unfold Info.schedOK at h
  split at h
  · rename_i oS oT hS hT
    refine ⟨oS, oT, hS, hT, fun k r hr hroot j y hj hy => ?_⟩
    exact (schedScan_spec h k r hr (by simpa using hroot)).2 j y hj hy
  · cases h

end SCI

end GoFV.Proof.ShortCirc
