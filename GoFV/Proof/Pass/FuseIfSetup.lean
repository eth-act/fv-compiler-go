import GoFV.Proof.Pass.FuseIfRel
import GoFV.Proof.Pass.FuseIfEnter
import GoFV.Proof.Merge
import GoFV.Proof.DomRel

variable [GoFV.SSA.Sem.Addrs]

/-!
# fuseBlockIf: the setting of one checked rewrite

`Setup ce f g s R`: `f` is well formed with its uses dominated on paths, and `g` is the checked
`fuseBlockIf` rewrite of `f` at the site `s` with the reset values `R` (`IRel`). The two
functions differ on the values `X = s.inX f R` (the reset values and the arms' values).
Consequences for the simulation: the unchanged values (`value_nR`, `value_R`), the arms
(`arm_spec`), the removed edge (`rm_src`, `succ_ok`), the target's predecessor index for a source
edge (`IdxRel`, `phi_idx`) and the related blocks (`brel_other`, `brel_b`) with their free
values' arguments (`freeDef_other`, `freeDef_b`).
-/

namespace GoFV.Proof.FuseIf

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.Fuse GoFV.Opt.Fuse.IfC GoFV.Proof Dom

/-- See the module doc. -/
structure Setup (ce : CheckEnv) (f g : Func) (s : Site) (R : List ID) : Prop where
  wf : WF ce f
  dom : UseDom f
  rel : IRel f g s R

/-- The target's predecessor index for the source's `i` at block `y`. -/
def tIdx (s : Site) (f : Func) (y : ID) (i : Nat) : Nat := if y = s.rmT f then s.rmI f i else i

/-- The edge indices the simulation relates: renumbered at `rmT` (never the removed `rmJ`), or
the join block entered along side 0 by the source and along side 1 by the target. -/
def IdxRel (s : Site) (f : Func) (y iS iT : Nat) : Prop :=
  ((y ≠ s.rmT f ∨ iS ≠ s.rmJ f) ∧ iT = tIdx s f y iS) ∨
    (y = s.ss ∧ iS = s.j0 ∧ iT = tIdx s f s.ss s.j1)

theorem rmE_eq (s : Site) (f : Func) (e : Edge) : s.rmE f e = ⟨e.b, tIdx s f e.b e.i⟩ := by
  obtain ⟨b, i⟩ := e
  unfold Site.rmE tIdx Site.rmI
  by_cases hb : b = s.rmT f <;> by_cases hi : i = s.last f <;> simp [hb, hi]

theorem phiRm_spec {s : Site} {f : Func} {fa ga : Array ID} (h : s.phiRm f fa ga = true) {i : Nat}
    (hi : i ≠ s.rmJ f) {a : ID} (ha : fa[i]? = some a) : ga[s.rmI f i]? = some a := by
  unfold Site.phiRm at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at h
  have hlt : i < fa.size := (Array.getElem?_eq_some_iff.1 ha).1
  rcases h.2 i hlt with h' | h'
  · exact absurd h' hi
  · rw [ha] at h'
    exact h'

variable {ce : CheckEnv} {f g : Func} {s : Site} {R : List ID}

namespace Setup

variable (S : Setup ce f g s R) {fr : Frame}
include S

theorem domR : DomRel f (Reachable f) (SDom f) := S.dom.domRel

/-- The `If` block. -/
theorem bB : ∃ B, f.block? s.b = some B ∧ B.kind = .If ∧ B.controls = #[s.c] ∧
    B.succs = #[s.e0, s.e1] := S.rel.bBlock

/-- An edge of a listed block ends at a listed block, the matching predecessor entry. -/
theorem succ_pred {p : ID} (hp : p ∈ f.blocks) {P : Block} (hP : f.block? p = some P) {k : Nat}
    {e : Edge} (hk : P.succs[k]? = some e) :
    e.b ∈ f.blocks ∧ ∃ C, f.block? e.b = some C ∧ C.preds[e.i]? = some ⟨p, k⟩ :=
  S.wf.succLink p P ⟨hp, hP⟩ k e hk

omit S in
/-- An arm: a speculation-safe `Plain` block with the single successor `ss` at `j`. -/
theorem arm_spec {a : ID} {e : Edge} {j : Nat} (h : s.sideOK f (some a) e j = true) :
    e.b = a ∧ a ≠ s.b ∧ a ≠ s.ss ∧ ∃ A, f.block? a = some A ∧ A.kind = .Plain ∧
      A.succs = #[⟨s.ss, j⟩] ∧ ∀ x ∈ A.values, ∃ v, f.value? x = some v ∧ specSafeOp v.op = true := by
  unfold Site.sideOK Site.armOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨he, hab⟩, has⟩, hA⟩ := h
  refine ⟨he, hab, has, ?_⟩
  split at hA
  · rename_i A hA'
    simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true'] at hA
    refine ⟨A, hA', hA.1.1, hA.1.2, fun x hx => ?_⟩
    have := hA.2 x hx
    split at this
    · rename_i v hv; exact ⟨v, hv, this⟩
    · cases this
  · cases hA

omit S in
theorem direct_spec {e : Edge} {j : Nat} (h : s.sideOK f none e j = true) : e = ⟨s.ss, j⟩ := by
  unfold Site.sideOK at h
  simpa using h

theorem e0_mem : s.e0.b ∈ f.blocks ∧ ∃ C, f.block? s.e0.b = some C ∧ C.preds[s.e0.i]? = some ⟨s.b, 0⟩ := by
  obtain ⟨B, hB, -, -, hsu⟩ := S.bB
  exact S.succ_pred S.rel.bIn hB (by rw [hsu]; rfl)

theorem e1_mem : s.e1.b ∈ f.blocks ∧ ∃ C, f.block? s.e1.b = some C ∧ C.preds[s.e1.i]? = some ⟨s.b, 1⟩ := by
  obtain ⟨B, hB, -, -, hsu⟩ := S.bB
  exact S.succ_pred S.rel.bIn hB (by rw [hsu]; rfl)

/-- Arms are listed. -/
theorem arm0_mem {a : ID} (h : s.arm0 = some a) : a ∈ f.blocks := by
  have hs := S.rel.side0; rw [h] at hs
  obtain ⟨he, -⟩ := arm_spec hs
  rw [← he]; exact S.e0_mem.1

theorem arm1_mem {a : ID} (h : s.arm1 = some a) : a ∈ f.blocks := by
  have hs := S.rel.side1; rw [h] at hs
  obtain ⟨he, -⟩ := arm_spec hs
  rw [← he]; exact S.e1_mem.1

theorem rmT_mem : s.rmT f ∈ f.blocks := by
  unfold Site.rmT
  split
  · rename_i a ha
    split
    · exact S.rel.ssIn
    · exact S.arm0_mem ha
  · exact S.rel.ssIn

theorem rmT_eq_ss (h : s.rmT f = s.ss) : s.rmJ f = s.j0 := by
  unfold Site.rmJ
  unfold Site.rmT at h
  cases ha : s.arm0 with
  | none => rfl
  | some a =>
    rw [ha] at h
    simp only at h ⊢
    split
    · rfl
    · rename_i hu
      simp only [hu] at h
      have hs := S.rel.side0; rw [ha] at hs
      exact absurd h (arm_spec hs).2.2.1

/-- **The removed edge** comes from `b` (along successor 0) or from an unlinked arm. -/
theorem rm_src : ∃ C, f.block? (s.rmT f) = some C ∧ (C.preds[s.rmJ f]? = some ⟨s.b, 0⟩ ∨
    ∃ a, s.unlinked f = true ∧ s.arm0 = some a ∧ C.preds[s.rmJ f]? = some ⟨a, 0⟩) := by
  have hs0 := S.rel.side0
  obtain ⟨-, C0, hC0, hp0⟩ := S.e0_mem
  unfold Site.rmT Site.rmJ
  cases ha : s.arm0 with
  | none =>
    rw [ha] at hs0
    have he := direct_spec hs0
    rw [he] at hC0 hp0
    exact ⟨C0, hC0, .inl hp0⟩
  | some a =>
    rw [ha] at hs0
    obtain ⟨he, -, -, A, hA, -, hAs, -⟩ := arm_spec hs0
    simp only
    split
    · rename_i hu
      obtain ⟨-, C, hC, hp⟩ := S.succ_pred (S.arm0_mem ha) hA (k := 0) (by rw [hAs]; rfl)
      exact ⟨C, hC, .inr ⟨a, hu, rfl, hp⟩⟩
    · rw [he] at hC0
      exact ⟨C0, hC0, .inl hp0⟩

/-- An edge of a block other than `b` and an unlinked arm is not the removed one and enters no
unlinked arm. -/
theorem succ_ok {p : ID} (hp : p ∈ f.blocks) {P : Block} (hP : f.block? p = some P) {k : Nat}
    {e : Edge} (hk : P.succs[k]? = some e) (hpb : p ≠ s.b ∨ k ≠ 0)
    (hpa : ¬ (s.unlinked f = true ∧ s.arm0 = some p)) :
    (e.b ≠ s.rmT f ∨ e.i ≠ s.rmJ f) ∧ ¬ (s.unlinked f = true ∧ s.arm0 = some e.b) := by
  obtain ⟨-, C, hC, hpC⟩ := S.succ_pred hp hP hk
  refine ⟨?_, fun ⟨hu, ha⟩ => ?_⟩
  · by_cases h1 : e.b = s.rmT f
    · by_cases h2 : e.i = s.rmJ f
      · exfalso
        obtain ⟨C', hC', hsrc⟩ := S.rm_src
        rw [← h1, hC] at hC'; cases hC'
        rw [← h2, hpC] at hsrc
        rcases hsrc with h | ⟨a, hu, ha, h⟩
        · cases h; exact hpb.elim (fun h => h rfl) (fun h => h rfl)
        · cases h; exact hpa ⟨hu, ha⟩
      · exact .inr h2
    · exact .inl h1
  · unfold Site.unlinked at hu
    rw [ha] at hu
    simp only [hC, Option.map_some, Option.some_beq_some, beq_iff_eq] at hu
    rw [hu] at hpC
    have h0 : e.i = 0 := by
      rcases Nat.lt_or_ge e.i 1 with h' | h'
      · omega
      · rw [Array.getElem?_eq_none (by simpa using h')] at hpC; cases hpC
    rw [h0] at hpC
    simp at hpC
    exact hpb.elim (fun h => h hpC.1.symm) (fun h => h hpC.2.symm)

omit S in
theorem not_panicking_phi : ¬ Panicking .Phi := by unfold Panicking; decide

omit S in
theorem specSafe_invalid : specSafeOp .Invalid = true := by decide

/-- A value of a listed block is in `valsOf` of exactly that block (among listed blocks). -/
theorem mem_vals_iff {y : ID} (hy : y ∈ f.blocks) {Y : Block} (hY : f.block? y = some Y)
    {x : ID} (hx : x ∈ Y.values) {z : ID} (hz : z ∈ f.blocks) : x ∈ valsOf f z ↔ z = y := by
  constructor
  · intro h
    unfold valsOf at h
    cases hZ : f.block? z with
    | none => rw [hZ] at h; simp at h
    | some Z =>
      rw [hZ] at h
      exact S.wf.valueOnce z Z y Y ⟨hz, hZ⟩ ⟨hy, hY⟩ x (by simpa using h) hx
  · rintro rfl; rw [valsOf_eq hY]; exact hx

omit S in
theorem armVal_spec {x : ID} (h : s.armVal f x = true) :
    ∃ a, (s.arm0 = some a ∨ s.arm1 = some a) ∧ x ∈ valsOf f a := by
  unfold Site.armVal at h
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · cases ha : s.arm0 with
    | none => rw [ha] at h; cases h
    | some a => rw [ha] at h; exact ⟨a, .inl rfl, by simpa using h⟩
  · cases ha : s.arm1 with
    | none => rw [ha] at h; cases h
    | some a => rw [ha] at h; exact ⟨a, .inr rfl, by simpa using h⟩

/-- An arm's values are speculation-safe. -/
theorem arm_val {a : ID} (ha : s.arm0 = some a ∨ s.arm1 = some a) {x : ID}
    (hx : x ∈ valsOf f a) :
    a ∈ f.blocks ∧ a ≠ s.b ∧ ∃ A, f.block? a = some A ∧ x ∈ A.values ∧
      ∃ v, f.value? x = some v ∧ specSafeOp v.op = true := by
  have hs : s.sideOK f (some a) s.e0 s.j0 = true ∨ s.sideOK f (some a) s.e1 s.j1 = true := by
    rcases ha with ha | ha
    · have := S.rel.side0; rw [ha] at this; exact .inl this
    · have := S.rel.side1; rw [ha] at this; exact .inr this
  have hm : a ∈ f.blocks := ha.elim S.arm0_mem S.arm1_mem
  rcases hs with hs | hs <;>
  · obtain ⟨-, hab, -, A, hA, -, -, hsafe⟩ := arm_spec hs
    rw [valsOf_eq hA] at hx
    exact ⟨hm, hab, A, hA, hx, hsafe x hx⟩

/-- A value outside `R`: unchanged in what the semantics reads (a `Phi` of `rmT`: its
arguments renumbered), reading nothing of `X`. -/
theorem value_nR {x : ID} {fv : Value} (hfv : f.value? x = some fv) (hR : x ∉ R) :
    ∃ gv, g.value? x = some gv ∧ gv.id = fv.id ∧ gv.type = fv.type ∧ gv.aux = fv.aux ∧
      gv.auxInt = fv.auxInt ∧ gv.op = fv.op ∧ (∀ a ∈ gv.args, s.inX f R a = false) ∧
      (fv.op = .Phi → x ∈ valsOf f (s.rmT f) → s.phiRm f fv.args gv.args = true) ∧
      ((fv.op = .Phi → x ∉ valsOf f (s.rmT f)) → gv.args = fv.args) := by
  have h := S.rel.value x (lt_of_value? hfv)
  unfold Site.valueOK at h
  have hc : R.contains x = false := by simpa using hR
  rw [hc, Bool.false_or, hfv] at h
  cases hgv : g.value? x with
  | none => rw [hgv] at h; cases h
  | some gv =>
    rw [hgv] at h
    simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨⟨⟨hid, hty⟩, haux⟩, hai⟩, hop⟩, hX⟩, hrest⟩ := h
    refine ⟨gv, rfl, hid, hty, haux, hai, hop, hX, fun hp hm => ?_, fun hn => ?_⟩
    · split at hrest
      · exact hrest
      · rename_i hc'
        exact absurd ⟨hp, Array.contains_iff_mem.2 hm⟩ hc'
    · split at hrest
      · rename_i hc'
        simp only [Bool.and_eq_true, beq_iff_eq, Array.contains_iff_mem] at hc'
        exact absurd hc'.2 (hn hc'.1)
      · simpa using hrest

/-- A reset value: `Invalid` without arguments in `g`, a `Phi` or pure in `f`. -/
theorem value_R {x : ID} (hx : x ∈ R) : ∃ fv gv, f.value? x = some fv ∧ g.value? x = some gv ∧
    gv.id = x ∧ gv.op = .Invalid ∧ gv.args = #[] ∧ (fv.op = .Phi ∨ prio fv.op = 0) := by
  have h := S.rel.reset x hx
  unfold Site.resetOK at h
  split at h
  · rename_i u v hu hv
    simp only [Bool.and_eq_true, beq_iff_eq, Array.isEmpty_iff, Bool.or_eq_true] at h
    exact ⟨u, v, hu, hv, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩
  · cases h

/-- An unlinked arm's values are `Invalid` without arguments in `g`. -/
theorem arm0_inv (hu : s.unlinked f = true) {a : ID} (ha : s.arm0 = some a) {x : ID}
    (hx : x ∈ valsOf f a) : ∃ gv, g.value? x = some gv ∧ gv.id = x ∧ gv.op = .Invalid ∧
      gv.args = #[] := by
  have h := S.rel.arm0Inv hu a ha x hx
  unfold Site.invalidIn at h
  split at h
  · rename_i v hv
    simp only [Bool.and_eq_true, beq_iff_eq, Array.isEmpty_iff] at h
    exact ⟨v, hv, h.1.1, h.1.2, h.2⟩
  · cases h

/-- **A free value** (of `X`): speculation-safe in `g`, not panicking in `f`; reset (no
arguments) or an arm's value, unchanged, reading nothing of `X`. -/
theorem free_val {x : ID} (hX : s.inX f R x = true) :
    ∃ fv gv, f.value? x = some fv ∧ g.value? x = some gv ∧ specSafeOp gv.op = true ∧
      ¬ Panicking fv.op ∧ (gv.args = #[] ∨ (fv.op ≠ .Phi ∧ gv.args = fv.args ∧
        (∀ a ∈ gv.args, s.inX f R a = false) ∧
        ∃ a, (s.arm0 = some a ∨ s.arm1 = some a) ∧ x ∈ valsOf f a)) := by
  by_cases hxR : x ∈ R
  · obtain ⟨fv, gv, hfv, hgv, -, hop, hargs, hfp⟩ := S.value_R hxR
    refine ⟨fv, gv, hfv, hgv, by rw [hop]; exact specSafe_invalid, fun hp => ?_, .inl hargs⟩
    rcases hfp with h | h
    · rw [h] at hp; exact not_panicking_phi hp
    · exact prio_panicking hp h
  · have hav : s.armVal f x = true := by
      unfold Site.inX at hX
      simpa [hxR] using hX
    obtain ⟨a, ha, hxa⟩ := armVal_spec hav
    obtain ⟨-, -, A, hA, hxA, v, hv, hsafe⟩ := S.arm_val ha hxa
    obtain ⟨gv, hgv, -, -, -, -, hop, hgX, -, heq⟩ := S.value_nR hv hxR
    have hnp := specSafe_not_phi hsafe
    exact ⟨v, gv, hv, hgv, by rw [hop]; exact hsafe, specSafe_not_panicking hsafe,
      .inr ⟨hnp, heq fun h => absurd h hnp, hgX, a, ha, hxa⟩⟩

theorem phis_agree {x : ID} (hx : x ∈ valsOf f s.ss) {v : Value} (hv : f.value? x = some v)
    (hp : v.op = .Phi) : ∃ a, v.args[s.j0]? = some a ∧ v.args[s.j1]? = some a := by
  have h := S.rel.phis
  unfold Site.phisOK at h
  have := (Array.all_eq_true'.1 h) x hx
  rw [hv] at this
  simp only [hp, bne_self_eq_false, Bool.false_or] at this
  split at this
  · rename_i a a' h0 h1
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    exact ⟨a, h0, this.1 ▸ h1⟩
  · cases this

/-- **A `Phi` along related edge indices** reads the same argument in both functions. -/
theorem phi_idx {y : ID} (hy : y ∈ f.blocks) {Y : Block} (hY : f.block? y = some Y) {x : ID}
    (hx : x ∈ Y.values) {fv gv : Value} (hfv : f.value? x = some fv) (hph : fv.op = .Phi)
    (hrm : fv.op = .Phi → x ∈ valsOf f (s.rmT f) → s.phiRm f fv.args gv.args = true)
    (heq : (fv.op = .Phi → x ∉ valsOf f (s.rmT f)) → gv.args = fv.args) {iS iT : Nat}
    (hI : IdxRel s f y iS iT) {a : ID} (ha : fv.args[iS]? = some a) : gv.args[iT]? = some a := by
  have key : ∀ i a', (y ≠ s.rmT f ∨ i ≠ s.rmJ f) → fv.args[i]? = some a' →
      gv.args[tIdx s f y i]? = some a' := by
    intro i a' hne hi
    unfold tIdx
    by_cases hyr : y = s.rmT f
    · rw [if_pos hyr]
      have hm := (S.mem_vals_iff hy hY hx S.rmT_mem).2 hyr.symm
      exact phiRm_spec (hrm hph hm) (hne.resolve_left (fun h => h hyr)) hi
    · rw [if_neg hyr, heq fun _ hm => hyr ((S.mem_vals_iff hy hY hx S.rmT_mem).1 hm).symm]
      exact hi
  rcases hI with ⟨hne, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact key iS a hne ha
  · obtain ⟨a0, h0, h1⟩ := S.phis_agree (by rw [valsOf_eq hY]; exact hx) hfv hph
    rw [ha] at h0; cases h0
    refine key s.j1 a ?_ h1
    by_cases h : s.ss = s.rmT f
    · exact .inr (by rw [S.rmT_eq_ss h.symm]; exact fun e => S.rel.j_ne e.symm)
    · exact .inl h

/-- The blocks of `g` (every listed block but an unlinked arm). -/
theorem block_core {y : ID} (hy : y ∈ f.blocks)
    (hna : ¬ (s.unlinked f = true ∧ s.arm0 = some y)) :
    ∃ Y Y', f.block? y = some Y ∧ g.block? y = some Y' ∧ Y'.id = Y.id ∧
      Y'.preds = s.predsOf f y Y.preds ∧
      (∀ c ∈ Y'.controls, s.inX f R c = false) ∧ (∃ o, Sem.schedule g Y' = some o) ∧
      (y = s.b → Y'.kind = .Plain ∧ Y'.controls = #[] ∧ Y'.succs = #[s.rmE f s.e1] ∧
        Y'.values = Y.values ++
          (if s.unlinked f then (s.arm0.map (valsOf f)).getD #[] else #[])) ∧
      (y ≠ s.b → Y'.values = Y.values ∧ Y'.kind = Y.kind ∧ Y'.controls = Y.controls ∧
        Y'.succs = Y.succs.map (s.rmE f)) := by
  have h := S.rel.block y hy
  unfold Site.blockOK at h
  have h0 : (s.unlinked f && s.arm0 == some y) = false := by
    cases hu : s.unlinked f
    · rfl
    · simpa using fun ha => hna ⟨hu, ha⟩
  rw [h0] at h
  simp only [Bool.false_eq_true, ite_false] at h
  split at h
  · rename_i Y Y' hY hY'
    simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true', Bool.not_eq_true'] at h
    obtain ⟨⟨⟨⟨hid, hpr⟩, hc⟩, hsc⟩, hrest⟩ := h
    refine ⟨Y, Y', hY, hY', hid, hpr, hc, Option.isSome_iff_exists.1 hsc, fun hb => ?_,
      fun hb => ?_⟩
    · split at hrest
      · simp only [Bool.and_eq_true, beq_iff_eq, Array.isEmpty_iff] at hrest
        exact ⟨hrest.1.1.1, hrest.1.1.2, hrest.1.2, hrest.2⟩
      · rename_i hc'; exact absurd (by simp [hb]) hc'
    · split at hrest
      · rename_i hc'; exact absurd (by simpa using hc') hb
      · simp only [Bool.and_eq_true, beq_iff_eq] at hrest
        exact ⟨hrest.1.1.1, hrest.1.1.2, hrest.1.2, hrest.2⟩
  · cases h

theorem b_ne_arm {a : ID} (ha : s.arm0 = some a ∨ s.arm1 = some a) : s.b ≠ a := by
  rcases ha with ha | ha
  · have hs := S.rel.side0; rw [ha] at hs; exact (arm_spec hs).2.1.symm
  · have hs := S.rel.side1; rw [ha] at hs; exact (arm_spec hs).2.1.symm

theorem not_dead_b : ¬ (s.unlinked f = true ∧ s.arm0 = some s.b) :=
  fun ⟨_, ha⟩ => S.b_ne_arm (.inl ha) rfl

/-- **A related block other than `b`.** -/
theorem brel_other {y : ID} (hy : y ∈ f.blocks) (hyb : y ≠ s.b)
    (hna : ¬ (s.unlinked f = true ∧ s.arm0 = some y)) {Y Y' : Block}
    (hY : f.block? y = some Y) (hY' : g.block? y = some Y') {iS iT : Nat}
    (hI : IdxRel s f y iS iT) :
    BRel f g (s.inX f R) Y Y' iS iT ∧ Y'.kind = Y.kind ∧ Y'.controls = Y.controls ∧
      Y'.succs = Y.succs.map (s.rmE f) ∧ (∀ c ∈ Y.controls, s.inX f R c = false) := by
  obtain ⟨Y1, Y1', hY1, hY1', hid, -, hc, hsc, -, hrest⟩ := S.block_core hy hna
  rw [hY] at hY1; cases hY1
  rw [hY'] at hY1'; cases hY1'
  obtain ⟨hv, hk, hcs, hsu⟩ := hrest hyb
  refine ⟨⟨hid, ⟨#[], by rw [hv]; simp, fun _ h => by simp at h⟩, fun x hx hX => ?_,
    fun x hx hX => ?_, fun x hx hX fv hfv => ?_, hsc⟩, hk, hcs, hsu, fun c hcm => hc c (hcs ▸ hcm)⟩
  · obtain ⟨fv, hfv, -⟩ := S.wf.valueId y Y ⟨hy, hY⟩ x hx
    have hxR : x ∉ R := fun h => by unfold Site.inX at hX; simp [h] at hX
    obtain ⟨gv, hgv, hid', hty, haux, hai, hop, hgX, hrm, heq⟩ := S.value_nR hfv hxR
    refine ⟨fv, gv, hfv, hgv, hid', hop, haux, hai, hty, hgX, fun hn => heq fun h => absurd h hn,
      fun hp a ha => ?_⟩
    exact S.phi_idx hy hY hx hfv hp hrm heq hI ha
  · obtain ⟨fv, gv, -, hgv, hs, -⟩ := S.free_val hX
    exact ⟨gv, hgv, hs⟩
  · obtain ⟨fv', gv, hfv', -, -, hnp, -⟩ := S.free_val hX
    rw [hfv] at hfv'; cases hfv'; exact hnp

/-- **The block `b`**, related to `b` of `g` along the same index. -/
theorem brel_b {B Bg : Block} (hB : f.block? s.b = some B) (hBg : g.block? s.b = some Bg)
    (i : Nat) :
    BRel f g (s.inX f R) B Bg i i ∧ Bg.kind = .Plain ∧ Bg.controls = #[] ∧
      Bg.succs = #[s.rmE f s.e1] ∧ FreeDef g (s.inX f R) Bg fr := by
  obtain ⟨B1, Bg1, hB1, hBg1, hid, -, -, hsc, hrest, -⟩ := S.block_core S.rel.bIn S.not_dead_b
  rw [hB] at hB1; cases hB1
  rw [hBg] at hBg1; cases hBg1
  obtain ⟨hk, hcs, hsu, hv⟩ := hrest rfl
  -- a value of `b` is no arm's
  have hnarm : ∀ x ∈ B.values, s.armVal f x = false := by
    intro x hx
    cases hav : s.armVal f x
    · rfl
    · obtain ⟨a, ha, hxa⟩ := armVal_spec hav
      have := (S.mem_vals_iff S.rel.bIn hB hx (S.arm_val ha hxa).1).1 hxa
      exact absurd this.symm (S.b_ne_arm ha)
  -- the added values: an unlinked arm's
  have hex : ∀ x ∈ (if s.unlinked f then (s.arm0.map (valsOf f)).getD #[] else #[]),
      s.unlinked f = true ∧ ∃ a, s.arm0 = some a ∧ x ∈ valsOf f a := by
    intro x hx
    split at hx
    · rename_i hu
      cases ha : s.arm0 with
      | none => rw [ha] at hx; simp at hx
      | some a => rw [ha] at hx; exact ⟨hu, a, rfl, hx⟩
    · simp at hx
  have hXin : ∀ x ∈ Bg.values, s.inX f R x = true → ∃ gv, g.value? x = some gv ∧
      specSafeOp gv.op = true ∧ gv.args = #[] := by
    intro x hx hX
    rw [hv] at hx
    rcases Array.mem_append.1 hx with hx | hx
    · have hxR : x ∈ R := by
        unfold Site.inX at hX; simpa [hnarm x hx] using hX
      obtain ⟨-, gv, -, hgv, -, hop, hargs, -⟩ := S.value_R hxR
      exact ⟨gv, hgv, by rw [hop]; exact specSafe_invalid, hargs⟩
    · obtain ⟨hu, a, ha, hxa⟩ := hex x hx
      obtain ⟨gv, hgv, -, hop, hargs⟩ := S.arm0_inv hu ha hxa
      exact ⟨gv, hgv, by rw [hop]; exact specSafe_invalid, hargs⟩
  refine ⟨⟨hid, ⟨_, hv, fun x hx => ?_⟩, fun x hx hX => ?_, fun x hx hX => ?_,
    fun x hx hX fv hfv => ?_, hsc⟩, hk, hcs, hsu, fun x hx hX gv hgv a ha => ?_⟩
  · obtain ⟨hu, a, ha, hxa⟩ := hex x hx
    unfold Site.inX Site.armVal; simp [ha, hxa]
  · obtain ⟨fv, hfv, -⟩ := S.wf.valueId s.b B ⟨S.rel.bIn, hB⟩ x hx
    have hxR : x ∉ R := fun h => by unfold Site.inX at hX; simp [h] at hX
    obtain ⟨gv, hgv, hid', hty, haux, hai, hop, hgX, -, heq⟩ := S.value_nR hfv hxR
    have hnrm : x ∉ valsOf f (s.rmT f) := fun hm => by
      have := (S.mem_vals_iff S.rel.bIn hB hx S.rmT_mem).1 hm
      unfold Site.rmT at this
      split at this
      · split at this
        · exact S.rel.ss_ne_b this
        · rename_i a ha _; exact S.b_ne_arm (.inl ha) this.symm
      · exact S.rel.ss_ne_b this
    have hargs := heq fun _ => hnrm
    exact ⟨fv, gv, hfv, hgv, hid', hop, haux, hai, hty, hgX, fun _ => hargs,
      fun _ a ha => by rw [hargs]; exact ha⟩
  · obtain ⟨gv, hgv, hs, -⟩ := hXin x hx hX
    exact ⟨gv, hgv, hs⟩
  · have hxR : x ∈ R := by unfold Site.inX at hX; simpa [hnarm x hx] using hX
    obtain ⟨fv', -, hfv', -, -, -, -, hfp⟩ := S.value_R hxR
    rw [hfv] at hfv'; cases hfv'
    intro hp
    rcases hfp with h | h
    · rw [h] at hp; exact not_panicking_phi hp
    · exact prio_panicking hp h
  · obtain ⟨gv', hgv', -, hargs⟩ := hXin x hx hX
    rw [hgv] at hgv'; cases hgv'
    rw [hargs] at ha; simp at ha

end Setup

end GoFV.Proof.FuseIf
