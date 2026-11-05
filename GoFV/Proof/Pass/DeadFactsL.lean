import GoFV.Proof.Pass.DeadRelL
import GoFV.Proof.Pass.DeadEdgeWF
import GoFV.Proof.Pass.DeadTail

/-!
# deadcode's steps keep `DeadRelL` and `lowered`

`runL` facts of deadcode's two `DeadRel` steps (`GoFV.Proof.Pass.DeadcodePass`):

* the edge removal (`EI`): every value keeps its op and every block its `auxInt` (`kview`), the
  kept blocks keep all their values (`deadRelL_of_ei`); a value is an arm64 op and a block has an
  arm64 kind in one iff in the other (`First` becomes `Plain`), so `lowered` is kept
  (`lowered_ei`, through `lowered_iff`);
* the tail after copyelim (`deadTail`): values keep their ops (`Sk`, `freeDead_spec`), blocks
  their `auxInt` (`BA`: no step of `pruneNames`, `unlink`, `moveStmts`, `freeDead` changes a
  block's `auxInt`), and a dropped value of a kept block is not live, while every
  `PanickingL false` op is a liveness root (`panickingL_root`, `live_root`): `deadTail_relL`.
-/

open Std.Do

set_option mvcgen.warning false

namespace GoFV.Proof.Dead

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof GoFV.Proof.CopyElim

/-! ## `lowered` -/

theorem lowered_iff (f : Func) : f.lowered = true ↔
    (∃ x v, f.value? x = some v ∧ v.op.generic = false) ∨
      (∃ y b, f.block? y = some b ∧ b.kind.isArm64 = true) := by
  unfold Func.lowered Func.value? Func.block?
  simp only [Bool.or_eq_true, Array.any_eq_true]
  apply or_congr
  · constructor
    · rintro ⟨i, hi, h⟩
      revert h
      cases hv : f.valueTab[i] with
      | none => intro h; cases h
      | some v =>
        intro h
        refine ⟨i, v, by rw [Array.getElem?_eq_getElem hi, hv]; rfl, by simpa using h⟩
    · rintro ⟨x, v, hx, hg⟩
      cases hxo : f.valueTab[x]? with
      | none => rw [hxo] at hx; cases hx
      | some o =>
        rw [hxo] at hx
        obtain ⟨hlt, heq⟩ := Array.getElem?_eq_some_iff.1 hxo
        refine ⟨x, hlt, ?_⟩
        rw [heq]
        cases o with
        | none => cases hx
        | some v' => cases hx; simp [hg]
  · constructor
    · rintro ⟨i, hi, h⟩
      revert h
      cases hb : f.blockTab[i] with
      | none => intro h; cases h
      | some b =>
        intro h
        exact ⟨i, b, by rw [Array.getElem?_eq_getElem hi, hb]; rfl, h⟩
    · rintro ⟨y, b, hy, ha⟩
      cases hyo : f.blockTab[y]? with
      | none => rw [hyo] at hy; cases hy
      | some o =>
        rw [hyo] at hy
        obtain ⟨hlt, heq⟩ := Array.getElem?_eq_some_iff.1 hyo
        refine ⟨y, hlt, ?_⟩
        rw [heq]
        cases o with
        | none => cases hy
        | some b' => cases hy; exact ha

/-- Two functions whose values are arm64 ops and blocks arm64 kinds at the same IDs are lowered
alike. -/
theorem lowered_eq_of {f F : Func}
    (hv : ∀ x v, F.value? x = some v → ∃ v', f.value? x = some v' ∧ v'.op = v.op)
    (hv' : ∀ x v, f.value? x = some v → ∃ v', F.value? x = some v' ∧ v'.op = v.op)
    (hb : ∀ y b, F.block? y = some b → ∃ b', f.block? y = some b' ∧ b'.kind.isArm64 = b.kind.isArm64)
    (hb' : ∀ y b, f.block? y = some b → ∃ b', F.block? y = some b' ∧
      b'.kind.isArm64 = b.kind.isArm64) :
    F.lowered = f.lowered := by
  have key : F.lowered = true ↔ f.lowered = true := by
    rw [lowered_iff, lowered_iff]
    constructor
    · rintro (⟨x, v, hx, hg⟩ | ⟨y, b, hy, ha⟩)
      · obtain ⟨v', h1, h2⟩ := hv x v hx; exact .inl ⟨x, v', h1, by rw [h2]; exact hg⟩
      · obtain ⟨b', h1, h2⟩ := hb y b hy; exact .inr ⟨y, b', h1, by rw [h2]; exact ha⟩
    · rintro (⟨x, v, hx, hg⟩ | ⟨y, b, hy, ha⟩)
      · obtain ⟨v', h1, h2⟩ := hv' x v hx; exact .inl ⟨x, v', h1, by rw [h2]; exact hg⟩
      · obtain ⟨b', h1, h2⟩ := hb' y b hy; exact .inr ⟨y, b', h1, by rw [h2]; exact ha⟩
  cases h1 : F.lowered <;> cases h2 : f.lowered <;> simp_all

/-! ## The edge removal -/

section

variable {f F : Func} {r : Array Bool}

private theorem isArm64_first_plain {k k' : BlockKind}
    (h : k' = k ∨ (r.getD y false = true ∧ k = .First ∧ k' = .Plain)) : k'.isArm64 = k.isArm64 := by
  rcases h with h | ⟨-, h1, h2⟩
  · rw [h]
  · rw [h1, h2]; rfl

/-- **The edge removal keeps `lowered`.** -/
theorem lowered_ei (hE : EI f r F) : F.lowered = f.lowered := by
  refine lowered_eq_of (fun x v hx => ?_) (fun x v hx => ?_) (fun y b hy => ?_) (fun y b hy => ?_)
  · obtain ⟨v0, hv0, hn⟩ := ei_value hE hx
    exact ⟨v0, hv0, (noArgs_parts hn).1.symm⟩
  · obtain ⟨u0, hu0, hn⟩ := noArgs_some (hE.vals x).symm (vw_of_value? hx)
    obtain ⟨v0, hv0, rfl⟩ := vw_eq_some hu0
    exact ⟨v0, hv0, (noArgs_parts hn).1.symm⟩
  · have hs := hE.pres y
    rw [hy] at hs
    cases hf : f.block? y with
    | none => rw [hf] at hs; cases hs
    | some b0 =>
      refine ⟨b0, rfl, ?_⟩
      have hk := hE.kind y
      rw [getB_of_block? hy, getB_of_block? hf] at hk
      exact (isArm64_first_plain hk).symm
  · have hs := hE.pres y
    rw [hy] at hs
    cases hF : F.block? y with
    | none => rw [hF] at hs; cases hs
    | some b0 =>
      refine ⟨b0, rfl, ?_⟩
      have hk := hE.kind y
      rw [getB_of_block? hy, getB_of_block? hF] at hk
      exact isArm64_first_plain hk

/-- **The edge removal keeps `DeadRelL`**, for any kept blocks. -/
theorem deadRelL_of_ei {K : ID → Prop} (hE : EI f r F) : DeadRelL f F K := by
  refine ⟨fun x gv hgv => ?_, fun bid _ gb fb hgb hfb => ?_,
    fun bid _ gb fb hgb hfb x hx hxn => ?_, fun x gv _ hgv hs => ?_⟩
  · obtain ⟨v0, hv0, hn⟩ := ei_value hE hgv
    exact ⟨v0, hv0, (noArgs_parts hn).1⟩
  · have := congrArg Block.auxInt (hE.kv bid)
    rw [getB_of_block? hgb, getB_of_block? hfb] at this
    exact this
  · rw [← getB_of_block? hgb, ei_values hE, getB_of_block? hfb] at hxn
    exact absurd hx hxn
  · obtain ⟨v0, hv0, hn⟩ := ei_value hE hgv
    have hop : gv.op = v0.op := (noArgs_parts hn).1
    have hnp : (strip v0).op ≠ .Phi := by
      show v0.op ≠ .Phi
      rw [← hop]; rcases hs with h | h <;> rw [h] <;> decide
    have h1 := hE.nonphi x (strip v0) (vw_of_value? hv0) hnp
    rw [vw_of_value? hgv] at h1
    exact ⟨v0, hv0, strip_args (Option.some.inj h1)⟩

end

/-! ## The tail: block `auxInt`s -/

/-- `G`'s blocks are blocks of `F` with the same `auxInt`. -/
def BA (F G : Func) : Prop :=
  ∀ bid gb, G.block? bid = some gb → ∃ fb, F.block? bid = some fb ∧ gb.auxInt = fb.auxInt

theorem BA.refl (F : Func) : BA F F := fun _ gb h => ⟨gb, h, rfl⟩

theorem BA.of_tab {F G H : Func} (h : BA F G) (ht : H.blockTab = G.blockTab) : BA F H :=
  fun bid gb hb => h bid gb (by unfold Func.block? at hb ⊢; rw [← ht]; exact hb)

theorem BA.trans {F G H : Func} (h1 : BA F G) (h2 : BA G H) : BA F H := fun bid hb hh => by
  obtain ⟨gb, hg, e2⟩ := h2 bid hb hh
  obtain ⟨fb, hf, e1⟩ := h1 bid gb hg
  exact ⟨fb, hf, e2.trans e1⟩

theorem BA.modB {F G : Func} (h : BA F G) (b : ID) (k : Block → Block)
    (hk : ∀ u, (k u).auxInt = u.auxInt) : BA F (G.modB b k) := fun x gb hx => by
  have hb : (G.modB b k).block? x = if b = x then (G.block? x).map k else G.block? x := by
    unfold Func.modB Func.block?
    simp only [Array.getElem?_modify]
    split
    · cases G.blockTab[x]? with
      | none => rfl
      | some o => cases o <;> rfl
    · rfl
  rw [hb] at hx
  split at hx
  · obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.1 hx
    obtain ⟨fb, hfb, e⟩ := h x u hu
    exact ⟨fb, hfb, (hk u).trans e⟩
  · exact h x gb hx

theorem blockTab_foldl_decUses (xs : Array ID) (G : Func) :
    (xs.foldl Func.decUses G).blockTab = G.blockTab := by
  rw [← Array.foldl_toList]
  induction xs.toList generalizing G with
  | nil => rfl
  | cons a as ih => exact ih (G.decUses a)

theorem BA.resetArgs {F G : Func} (h : BA F G) (v : ID) : BA F (G.resetArgs v) :=
  h.of_tab (blockTab_foldl_decUses _ G)

theorem BA.resetControls {F G : Func} (h : BA F G) (b : ID) : BA F (G.resetControls b) := by
  unfold Func.resetControls
  exact (h.of_tab (blockTab_foldl_decUses _ G)).modB b _ fun _ => rfl

theorem unlink_ba {r live : Array Bool} {f g : Func} {p p' : XPosMap}
    (h : Deadcode.unlink r live f p = .ok (g, p')) : BA f g := by
  unfold Deadcode.unlink at h
  dsimp only at h
  obtain ⟨s, hs, h⟩ := CheckFacts.bind_ok h
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj h)
  refine forIn'_range_mono (fun s : Func × XPosMap => BA f s.1) ?_ (BA.refl f) hs
  intro i hi s s' hI hb
  split at hb <;>
  · obtain ⟨t, ht, hb⟩ := CheckFacts.bind_ok hb
    cases Except.ok.inj hb
    refine CheckFacts.forIn_array_inv (fun _ t => BA f t.1) ?_ ?_ ht
    · first | with_reducible exact hI | exact hI.resetControls _
    · intro pre x t t' hI hb
      split at hb
      · have hI2 := hI.resetArgs x
        split at hb
        · obtain ⟨q, -, hb⟩ := CheckFacts.bind_ok hb
          exact ⟨_, (Except.ok.inj hb).symm, hI2⟩
        · exact ⟨_, (Except.ok.inj hb).symm, hI2⟩
      · exact ⟨_, (Except.ok.inj hb).symm, hI⟩

theorem move_ba {o : Array ID} {f g : Func} {p p' : XPosMap}
    (h : Deadcode.moveStmts o f p = (g, p')) : BA f g := by
  apply Id.of_wp_run_eq h (fun res => BA f res.1)
  mvcgen
  case inv1 => exact ⇓⟨_, g, _⟩ => ⌜BA f g⌝
  case inv2 => exact ⇓⟨_, g⟩ => ⌜BA f g⌝
  all_goals mleave
  all_goals first
    | exact BA.refl f
    | (rename_i hI
       first
        | exact hI
        | exact hI.of_tab rfl
        | exact hI.modB _ _ fun _ => rfl)

theorem freeDead_ba {r live : Array Bool} {F g : Func} (h : Deadcode.freeDead r live F = .ok g) :
    BA F g := by
  unfold Deadcode.freeDead at h
  dsimp only at h
  obtain ⟨G1, h1, h⟩ := CheckFacts.bind_ok h
  have hI1 := CheckFacts.forIn_array_inv (fun _ G => BA F G) (BA.refl F) ?_ h1
  rotate_left
  · intro pre b G G' hB hb
    obtain ⟨s, hs, hb⟩ := CheckFacts.bind_ok hb
    cases Except.ok.inj hb
    have hJ := CheckFacts.forIn_array_inv
      (fun _ (t : Func × Array ID) => t.1.blockTab = G.blockTab) rfl ?_ hs
    rotate_left
    · intro pre x t t' htB hb
      split at hb
      · exact ⟨_, (Except.ok.inj hb).symm, htB⟩
      · exact ⟨_, (Except.ok.inj hb).symm, (freeValue_fr _ _).2.trans htB⟩
    exact ⟨_, rfl, (hB.of_tab hJ).modB _ _ fun _ => rfl⟩
  obtain ⟨s2, h2, h⟩ := CheckFacts.bind_ok h
  cases Except.ok.inj h
  have hK := CheckFacts.forIn_array_inv (fun _ (t : Func × Array ID) => BA F t.1) hI1 ?_ h2
  rotate_left
  · intro pre b t t' hB hb
    split at hb
    · exact ⟨_, (Except.ok.inj hb).symm, hB⟩
    · split at hb
      · obtain ⟨_, hth, -⟩ := CheckFacts.bind_ok hb
        cases hth
      · refine ⟨_, (Except.ok.inj hb).symm, fun x gb hx => hB x gb (join_set_none hx)⟩
  exact hK.of_tab rfl

/-! ## The tail: `DeadRelL` -/

/-- Every op that may panic under `runL` is a liveness root. -/
theorem panickingL_root {op : Op} (h : PanickingL false op) :
    (op.call || op.hasSideEffects || op.nilCheck) = true := by
  rcases h with h | h | ⟨h, -⟩
  · simp [h]
  · simp [h]
  · cases h

/-- **deadcode after copyelim keeps `DeadRelL`.** -/
theorem deadTail_relL {tabs : Tables} {r : Array Bool} {f g : Func}
    (hsize : f.valueTab.size ≤ f.vidLast + 1)
    (h : deadTail tabs r f = .ok g) : DeadRelL f g (· ∈ g.blocks) := by
  unfold deadTail at h
  generalize hlo : f.liveValuesOrder tabs r = lo at h
  obtain ⟨live, order⟩ := lo
  dsimp only at h
  split at h
  · rename_i pending _
    obtain ⟨⟨f2, p2⟩, hu, h⟩ := CheckFacts.bind_ok h
    dsimp only at h
    generalize hm : Deadcode.moveStmts order f2 p2 = mm at h
    obtain ⟨f3, p3⟩ := mm
    dsimp only at h
    have S1 : Sk r live f (Deadcode.pruneNames live f) :=
      ⟨rfl, rfl, rfl, rfl, fun _ gb h => ⟨gb, h, BSk.refl⟩, fun _ gv h => ⟨gv, h, VSk.refl⟩⟩
    have S3 := (S1.trans (unlink_sk hu)).trans (move_sk hm)
    have S : Sk r live f { f3 with cache := { f3.cache with lineStarts := some p3.toCache } } :=
      S3.trans ⟨rfl, rfl, rfl, rfl, fun _ gb h => ⟨gb, h, BSk.refl⟩, fun _ gv h => ⟨gv, h, VSk.refl⟩⟩
    have B : BA f { f3 with cache := { f3.cache with lineStarts := some p3.toCache } } :=
      ((((BA.refl f).of_tab (G := f) (H := Deadcode.pruneNames live f) rfl).trans
        (unlink_ba hu)).trans (move_ba hm)).of_tab rfl
    generalize { f3 with cache := { f3.cache with lineStarts := some p3.toCache } } = F at S B h
    obtain ⟨-, -, -, hVal, hBm, hBlk⟩ := freeDead_spec h
    have hB := B.trans (freeDead_ba h)
    have hlive : live = (f.liveValuesOrder tabs r).1 := by rw [hlo]
    refine ⟨fun x gv hgv => ?_, fun bid _ gb fb hgb hfb => ?_,
      fun bid hm gb fb hgb hfb x hx hnx fv hfv hpan => ?_,
      fun x gv ⟨bid, gb, ⟨hbm, hgb⟩, hx⟩ hgv _ => ?_⟩
    · obtain ⟨fv, hfv, ho, -⟩ := S.value x gv (hVal x gv hgv)
      exact ⟨fv, hfv, ho⟩
    · obtain ⟨fb', hfb', e⟩ := hB bid gb hgb
      rw [hfb] at hfb'; cases hfb'
      exact e
    · obtain ⟨hmF, hr⟩ := hBm bid hm
      obtain ⟨b3, hb3, -, -, -, hv⟩ := hBlk bid gb hmF hgb
      obtain ⟨fb', hfb', -, -, hv', -⟩ := S.block bid b3 hb3
      rw [hfb] at hfb'; cases hfb'
      have hl := live_root (t := tabs) hsize (S.blocks ▸ hmF) hr hfb hx hfv (panickingL_root hpan)
      rw [← hlive] at hl
      exact hnx (by rw [hv, hv']; exact Array.mem_filter.2 ⟨hx, hl⟩)
    · obtain ⟨hmF, -⟩ := hBm bid hbm
      obtain ⟨b3, -, -, -, -, hv⟩ := hBlk bid gb hmF hgb
      have hx' : x ∈ b3.values.filter (live.getD · false) := hv ▸ hx
      have hl : live.getD x false = true := (Array.mem_filter.1 hx').2
      obtain ⟨fv, hfv, -, -, -, -, -, ha⟩ := S.value x gv (hVal x gv hgv)
      exact ⟨fv, hfv, ha hl⟩
  · cases h

end GoFV.Proof.Dead
