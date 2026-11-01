import GoFV.Proof.Pass.PhiOptRel
import GoFV.Proof.DomCert

/-!
# phiopt's checker: what its parts say

Declarative readings of the Bool parts of `prel`: `listedIn`, `avail` (a value placed in a
strict ancestor of the block in the certified tree, not listed in the block), `constB`,
`constI`, `isNew`, `newOK` (new values are `Not`/`CvtBoolToUint8`, never `Phi`s), `facts`.
-/

namespace GoFV.Proof.PhiOpt

open GoFV.SSA GoFV.Opt GoFV.Opt.PhiOpt GoFV.SSA.DomCert

theorem listedIn_iff {f : Func} {b x : ID} :
    listedIn f b x = true ↔ ∃ blk, f.block? b = some blk ∧ x ∈ blk.values := by
  unfold listedIn
  cases f.block? b <;> simp

theorem not_listedIn {f : Func} {b x : ID} {blk : Block} (hb : f.block? b = some blk)
    (h : listedIn f b x = false) : x ∉ blk.values := fun hx => by
  have := listedIn_iff.2 ⟨blk, hb, hx⟩
  rw [h] at this; cases this

/-- What `avail` says. -/
theorem avail_spec {f : Func} {b x : ID} (h : avail f b x = true) :
    ∃ v blk, f.value? x = some v ∧ v.block ∈ f.blocks ∧ f.block? v.block = some blk ∧
      x ∈ blk.values ∧ (make f).anc v.block b = true ∧ v.block ≠ b ∧ listedIn f b x = false := by
  unfold avail at h
  cases hv : f.value? x with
  | none => rw [hv] at h; cases h
  | some v =>
    rw [hv] at h
    simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq,
      Array.contains_iff_mem] at h
    obtain ⟨⟨⟨⟨hm, hl⟩, ha⟩, hne⟩, hnl⟩ := h
    obtain ⟨blk, hb, hx⟩ := listedIn_iff.1 hl
    exact ⟨v, blk, rfl, hm, hb, hx, ha, hne, hnl⟩

theorem isBoolTy_spec {tabs : Tables} {t : TypeRef} (h : isBoolTy tabs t = true) :
    tabs.ty t = .bool := by
  unfold isBoolTy at h
  split at h
  · assumption
  · cases h

theorem constB_spec {tabs : Tables} {f : Func} {a : ID} {d : Bool} (h : constB tabs f a d = true) :
    ∃ u, f.value? a = some u ∧ u.op = .ConstBool ∧ (u.auxInt != 0) = d ∧
      tabs.ty u.type = .bool := by
  unfold constB at h
  cases hu : f.value? a with
  | none => rw [hu] at h; cases h
  | some u =>
    rw [hu] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨u, rfl, h.1.1, h.1.2, isBoolTy_spec h.2⟩

theorem constI_spec {tabs : Tables} {f : Func} {a : ID} {w : Sem.Width} {k : Int64}
    (h : constI tabs f a w k = true) :
    ∃ u, f.value? a = some u ∧ u.op = constOp w ∧ tabs.ty u.type = .int w ∧ u.auxInt = k := by
  unfold constI at h
  cases hu : f.value? a with
  | none => rw [hu] at h; cases h
  | some u =>
    rw [hu] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨u, rfl, h1, ?_, h3⟩
    unfold intW at h2
    split at h2
    · rename_i w' hw; cases h2; exact hw
    · cases h2

theorem isNew_spec {f g : Func} {b x : ID} (h : isNew f g b x = true) :
    f.value? x = none ∧ ∃ blk, g.block? b = some blk ∧ x ∈ blk.values := by
  unfold isNew at h
  simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  exact ⟨h.1, listedIn_iff.1 h.2⟩

/-- What a new value is. -/
theorem newOK_spec {f g : Func} {b x : ID} (h : newOK f g b x = true) :
    ∃ nv a, g.value? x = some nv ∧ nv.id = x ∧ nv.args = #[a] ∧
      ((nv.op = .Not ∧ avail f b a = true) ∨
       (nv.op = .CvtBoolToUint8 ∧ (avail f b a = true ∨
         (isNew f g b a = true ∧ ∃ u c, g.value? a = some u ∧ u.op = .Not ∧ u.args = #[c] ∧
           avail f b c = true)))) := by
  unfold newOK at h
  cases hv : g.value? x with
  | none => rw [hv] at h; cases h
  | some nv =>
    rw [hv] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hid, hsz⟩, h⟩ := h
    have hargs : nv.args = #[nv.args[0]!] := by
      apply Array.ext
      · simpa using hsz
      · intro k h1 h2
        have hk : k = 0 := by simp at h2; omega
        subst hk
        simp [getElem!_pos nv.args 0 h1]
    refine ⟨nv, nv.args[0]!, rfl, hid, hargs, ?_⟩
    by_cases hn : nv.op = .Not
    · simp only [hn, ite_true] at h
      exact .inl ⟨hn, h⟩
    · simp only [hn, ↓reduceIte] at h
      by_cases hc : nv.op = .CvtBoolToUint8
      · simp only [hc, ite_true, Bool.or_eq_true, Bool.and_eq_true,
          Option.any_eq_true] at h
        refine .inr ⟨hc, ?_⟩
        rcases h with h | ⟨hnew, u, hu, hop⟩
        · exact .inl h
        · simp only [beq_iff_eq] at hop
          obtain ⟨⟨hop, husz⟩, hav⟩ := hop
          have huargs : u.args = #[u.args[0]!] := by
            apply Array.ext
            · simpa using husz
            · intro k h1 h2
              have hk : k = 0 := by simp at h2; omega
              subst hk
              simp [getElem!_pos u.args 0 h1]
          exact .inr ⟨hnew, u, u.args[0]!, hu, hop, huargs, hav⟩
      · simp only [hc, ↓reduceIte] at h; cases h

/-- A new value is not a `Phi`. -/
theorem newOK_not_phi {f g : Func} {b x : ID} (h : newOK f g b x = true) {nv : Value}
    (hv : g.value? x = some nv) : nv.op ≠ .Phi := by
  obtain ⟨nv', a, hv', -, -, hop⟩ := newOK_spec h
  rw [hv] at hv'; cases hv'
  rcases hop with ⟨hop, -⟩ | ⟨hop, -⟩ <;> rw [hop] <;> decide

theorem facts_spec {f : Func} {b c : ID} {d0 d1 : Bool} (h : facts f b c = some (d0, d1)) :
    edgeFact f c (f.blocks.size + 1) b 0 = some d0 ∧
      edgeFact f c (f.blocks.size + 1) b 1 = some d1 := by
  unfold facts at h
  simp only at h
  split at h
  · rename_i e0 e1 h0 h1; cases h; exact ⟨h0, h1⟩
  · cases h

/-- The fuel of the checker's edge facts. -/
abbrev fuelOf (f : Func) : Nat := f.blocks.size + 1

/-- A boolean form yields arm `a` when its control `c` holds `d` (`armOK`). -/
def BoolArm (tabs : Tables) (f : Func) (b c : ID) (gv : Value) (a : ID) (d : Bool) : Prop :=
  (gv.op = .Copy ∧ gv.args = #[c] ∧ armB tabs f c a d d = true) ∨
  (gv.op = .Not ∧ gv.args = #[c] ∧ armB tabs f c a d (!d) = true) ∨
  (∃ n, gv.op = .OrB ∧ gv.args = #[c, n] ∧ avail f b n = true ∧
    (if d then armB tabs f c a d true = true else a = n)) ∨
  (∃ n, gv.op = .AndB ∧ gv.args = #[c, n] ∧ avail f b n = true ∧
    (if d then a = n else armB tabs f c a d false = true))

theorem args_one {v : Value} (h : v.args.size = 1) : v.args = #[v.args[0]!] := by
  apply Array.ext
  · simpa using h
  · intro k h1 h2
    have hk : k = 0 := by simp at h2; omega
    subst hk
    simp [getElem!_pos v.args 0 h1]

theorem args_two {v : Value} (h : v.args.size = 2) : v.args = #[v.args[0]!, v.args[1]!] := by
  apply Array.ext
  · simpa using h
  · intro k h1 h2
    have hk : k = 0 ∨ k = 1 := by simp at h2; omega
    rcases hk with rfl | rfl
    · simp [getElem!_pos v.args 0 h1]
    · simp [getElem!_pos v.args 1 h1]

theorem armOK_spec {tabs : Tables} {f : Func} {b c a : ID} {gv : Value} {d : Bool} (hc : gv.args[0]? = some c)
    (h : armOK tabs f b c gv a d = true) : BoolArm tabs f b c gv a d := by
  unfold armOK at h
  simp only [beq_iff_eq] at h
  have hc0 : ∀ hs : 0 < gv.args.size, gv.args[0]! = c := fun hs => by
    rw [getElem!_pos gv.args 0 hs]; simpa [hs] using hc
  by_cases h1 : gv.op = .Copy
  · simp only [h1, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at h
    have := args_one h.1
    rw [hc0 (by rw [h.1]; omega)] at this
    exact .inl ⟨h1, this, h.2⟩
  simp only [h1, ↓reduceIte] at h
  by_cases h2 : gv.op = .Not
  · simp only [h2, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at h
    have := args_one h.1
    rw [hc0 (by rw [h.1]; omega)] at this
    exact .inr (.inl ⟨h2, this, h.2⟩)
  simp only [h2, ↓reduceIte] at h
  by_cases h3 : gv.op = .OrB
  · simp only [h3, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hs, hav⟩, hd⟩ := h
    have := args_two hs
    rw [hc0 (by rw [hs]; omega)] at this
    refine .inr (.inr (.inl ⟨_, h3, this, hav, ?_⟩))
    cases d <;> simpa using hd
  simp only [h3, ↓reduceIte] at h
  by_cases h4 : gv.op = .AndB
  · simp only [h4, ↓reduceIte, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hs, hav⟩, hd⟩ := h
    have := args_two hs
    rw [hc0 (by rw [hs]; omega)] at this
    refine .inr (.inr (.inr ⟨_, h4, this, hav, ?_⟩))
    cases d <;> simpa using hd
  simp only [h4, ↓reduceIte] at h; cases h

/-- phioptint's shape: `gv = extOp w cv`, `cv = CvtBoolToUint8 x` new, `x = c` (`neg` false)
or a new `Not c` (`neg` true), `c` available, the `Phi` of width `w`. -/
def IntShape (tabs : Tables) (f g : Func) (b : ID) (fv gv : Value) (w : Sem.Width) (c : ID)
    (neg : Bool) : Prop :=
  tabs.ty fv.type = .int w ∧ gv.op = extOp w ∧ avail f b c = true ∧
  ∃ cv cvv x, gv.args = #[cv] ∧ isNew f g b cv = true ∧ g.value? cv = some cvv ∧
    cvv.op = .CvtBoolToUint8 ∧ tabs.ty cvv.type = .int .w8 ∧ cvv.args = #[x] ∧
    ((x = c ∧ neg = false) ∨
      (isNew f g b x = true ∧ ∃ nv, g.value? x = some nv ∧ nv.op = .Not ∧ nv.args = #[c] ∧
        tabs.ty nv.type = .bool ∧ neg = true))

/-- The form of a rewritten `Phi` and what it yields on each edge. -/
def Form (tabs : Tables) (f g : Func) (b : ID) (fv gv : Value) : Prop :=
  (tabs.ty fv.type = .bool ∧ ∃ c, gv.args[0]? = some c ∧ avail f b c = true ∧
    ∀ i a, fv.args[i]? = some a → ∃ d, edgeFact f c (fuelOf f) b i = some d ∧
      BoolArm tabs f b c gv a d) ∨
  (∃ w c neg, IntShape tabs f g b fv gv w c neg ∧
    ∀ i a, fv.args[i]? = some a → ∃ d, edgeFact f c (fuelOf f) b i = some d ∧
      constI tabs f a w (if d != neg then 1 else 0) = true)

theorem intW_spec {tabs : Tables} {t : TypeRef} {w : Sem.Width} (h : intW tabs t = some w) :
    tabs.ty t = .int w := by
  unfold intW at h
  split at h
  · cases h; assumption
  · cases h

theorem edge_two {fv : Value} {i : Nat} {a : ID} (hs : fv.args.size = 2)
    (h : fv.args[i]? = some a) : (i = 0 ∧ a = fv.args[0]!) ∨ (i = 1 ∧ a = fv.args[1]!) := by
  have hi : i < 2 := by have := (Array.getElem?_eq_some_iff.1 h).1; omega
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · left; refine ⟨rfl, ?_⟩; rw [getElem!_pos fv.args 0 (by omega)]
    exact (Array.getElem?_eq_some_iff.1 h).2.symm
  · right; refine ⟨rfl, ?_⟩; rw [getElem!_pos fv.args 1 (by omega)]
    exact (Array.getElem?_eq_some_iff.1 h).2.symm

theorem intArms_spec {tabs : Tables} {f : Func} {b : ID} {w : Sem.Width} {fv : Value} {c : ID}
    {neg : Bool} (hs : fv.args.size = 2) (h : intArms tabs f b w fv.args[0]! fv.args[1]! c neg = true) :
    avail f b c = true ∧ ∀ i a, fv.args[i]? = some a → ∃ d, edgeFact f c (fuelOf f) b i = some d ∧
      constI tabs f a w (if d != neg then 1 else 0) = true := by
  unfold intArms at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hav, h⟩ := h
  refine ⟨hav, fun i a ha => ?_⟩
  split at h
  · rename_i d0 d1 hf
    obtain ⟨h0, h1⟩ := facts_spec hf
    simp only [Bool.and_eq_true] at h
    rcases edge_two hs ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨d0, h0, h.1⟩
    · exact ⟨d1, h1, h.2⟩
  · cases h

/-- **What a rewritten `Phi` is.** -/
theorem rewriteOK_spec {tabs : Tables} {f g : Func} {fv gv : Value}
    (h : rewriteOK tabs f g fv gv = true) :
    fv.op = .Phi ∧ gv.op ≠ .Phi ∧ fv.args.size = 2 ∧
      (∃ fb, f.block? fv.block = some fb ∧ fb.preds.size = 2) ∧ Form tabs f g fv.block fv gv := by
  unfold rewriteOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨hphi, hnp⟩, hs⟩, hp⟩, hf⟩ := h
  refine ⟨hphi, hnp, hs, ?_, ?_⟩
  · revert hp
    cases f.block? fv.block <;> simp
  rcases hf with hb | hi
  · left
    unfold boolForm at hb
    simp only [Bool.and_eq_true] at hb
    obtain ⟨hty, hb⟩ := hb
    refine ⟨isBoolTy_spec hty, ?_⟩
    split at hb
    · cases hb
    · rename_i c hc
      simp only [Bool.and_eq_true] at hb
      obtain ⟨hav, hb⟩ := hb
      refine ⟨c, hc, hav, fun i a ha => ?_⟩
      split at hb
      · cases hb
      · rename_i d0 d1 hfa
        obtain ⟨h0, h1⟩ := facts_spec hfa
        simp only [Bool.and_eq_true] at hb
        rcases edge_two hs ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨d0, h0, armOK_spec hc hb.1⟩
        · exact ⟨d1, h1, armOK_spec hc hb.2⟩
  · right
    unfold intForm at hi
    split at hi
    · rename_i w cv hw hcv
      have hcv' : gv.args = #[cv] := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hi
        have h0 : gv.args[0]! = cv := by
          rw [getElem!_pos gv.args 0 (by rw [hi.1.1.2]; omega)]
          exact (Array.getElem?_eq_some_iff.1 hcv).2
        rw [← h0]; exact args_one hi.1.1.2
      simp only [Bool.and_eq_true, beq_iff_eq] at hi
      obtain ⟨⟨⟨hop, -⟩, hnew⟩, hi⟩ := hi
      split at hi
      · rename_i cvv hcvv
        simp only [Bool.and_eq_true, beq_iff_eq] at hi
        obtain ⟨⟨⟨hcop, hcty⟩, hcs⟩, hi⟩ := hi
        have hx := args_one hcs
        split at hi
        · rename_i hxn
          split at hi
          · rename_i nv hnv
            simp only [Bool.and_eq_true, beq_iff_eq] at hi
            obtain ⟨⟨⟨hnop, hns⟩, hnty⟩, hi⟩ := hi
            obtain ⟨hav, hall⟩ := intArms_spec hs hi
            exact ⟨w, _, true, ⟨intW_spec hw, hop, hav, cv, cvv, _, hcv', hnew, hcvv, hcop,
              intW_spec hcty, hx, .inr ⟨hxn, nv, hnv, hnop, args_one hns, isBoolTy_spec hnty, rfl⟩⟩,
              hall⟩
          · cases hi
        · obtain ⟨hav, hall⟩ := intArms_spec hs hi
          exact ⟨w, _, false, ⟨intW_spec hw, hop, hav, cv, cvv, _, hcv', hnew, hcvv, hcop,
            intW_spec hcty, hx, .inl ⟨rfl, rfl⟩⟩, hall⟩
      · cases hi
    · cases hi

end GoFV.Proof.PhiOpt
