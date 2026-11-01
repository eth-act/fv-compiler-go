import GoFV.Proof.AtomSimStep

/-!
# Value sets of the atom simulation (issue #113)

The hypotheses (`Hyp`: both functions well formed with certified dominator trees, `atomsOK`,
the two `TermRef` premises), the value sets the frame relation speaks about (`SAnc`: placed in
a strict ancestor of the block; `PhiOf`: a `Phi` of the block), their closure under the
arguments of term nodes (`closed_sanc`), atoms of `g` as atoms of `f` (`gatom_f`), `DenOK`
along a list of term nodes in one frame (`denOK_terms`), and list facts about prefixes of
schedules.
-/

namespace GoFV.Proof.AtomSim

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Proof.Dom GoFV.Opt.RewriteCheck GoFV.Proof.Term

/-- The hypotheses of the atom simulation. -/
structure Hyp (tabs : Tables) (f g : Func) (ce ce' : CheckEnv) : Prop where
  wf : WF ce f
  wg : WF ce' g
  cf : CertOK f
  cg : CertOK g
  ok : AtomsOK f g
  args : AtomArgsRef tabs f g
  ctrls : ControlsRef tabs f g

/-- `x` is placed in a strict ancestor of `b`. -/
def SAnc (h : Func) (b x : ID) : Prop :=
  ∃ v, Placed h x v ∧ Anc (make h) v.block b ∧ v.block ≠ b

/-- `x` is placed in an ancestor of `b`. -/
def AncV (h : Func) (b x : ID) : Prop := ∃ v, Placed h x v ∧ Anc (make h) v.block b

/-- `x` is a `Phi` of block `hb`. -/
def PhiOf (h : Func) (hb : Block) (x : ID) : Prop :=
  x ∈ hb.values ∧ ∃ v, h.value? x = some v ∧ v.op = .Phi

/-! ## Placed values -/

theorem placed_listed {h : Func} {x : ID} {v : Value} (hp : Placed h x v) :
    listedDefs h x = some v := by
  obtain ⟨hv, hb, blk, hblk, hx⟩ := hp
  unfold listedDefs
  rw [hv, Option.filter_eq_some_iff]
  refine ⟨rfl, ?_⟩
  simp only [Bool.and_eq_true, Array.contains_iff_mem, hb, hblk, Option.any_some, hx,
    and_self]

theorem listed_placed {h : Func} {x : ID} {v : Value} (hl : listedDefs h x = some v) :
    Placed h x v := by
  unfold listedDefs at hl
  rw [Option.filter_eq_some_iff] at hl
  obtain ⟨hv, hc⟩ := hl
  simp only [Bool.and_eq_true, Array.contains_iff_mem] at hc
  obtain ⟨hb, hc⟩ := hc
  cases hblk : h.block? v.block with
  | none => rw [hblk] at hc; cases hc
  | some blk =>
    rw [hblk] at hc
    simp only [Option.any_some, Array.contains_iff_mem] at hc
    exact ⟨hv, hb, blk, hblk, hc⟩

theorem placed_val {h : Func} {x : ID} {v w : Value} (hp : Placed h x v) (hw : h.value? x = some w) :
    w = v := by
  rw [hp.1] at hw; cases hw; rfl

theorem placed_of_listed {ce : CheckEnv} {h : Func} (hwf : WF ce h) {a : ID} (ha : Listed h a) :
    ∃ v, Placed h a v ∧ blockOf h a = v.block := by
  obtain ⟨bid, b, ⟨hbm, hbb⟩, hab⟩ := ha
  obtain ⟨v, hp, -, -⟩ := placed_of_mem hwf hbm hbb hab
  exact ⟨v, hp, blockOf_placed hp⟩

/-- A value placed in block `c` is not listed in another block `b`. -/
theorem not_mem_of_placed {ce : CheckEnv} {h : Func} (hwf : WF ce h) {x : ID} {v : Value}
    (hp : Placed h x v) {b : ID} {hb : Block} (hbm : b ∈ h.blocks) (hbb : h.block? b = some hb)
    (hne : v.block ≠ b) : x ∉ hb.values := fun hx => by
  obtain ⟨-, hvb, blk, hblk, hxv⟩ := hp
  exact hne (hwf.valueOnce _ _ _ _ ⟨hvb, hblk⟩ ⟨hbm, hbb⟩ x hxv hx)

/-- The value placed at `x` in block `b` (listed there). -/
theorem placed_in {ce : CheckEnv} {h : Func} (hwf : WF ce h) {b : ID} {hb : Block}
    (hbm : b ∈ h.blocks) (hbb : h.block? b = some hb) {x : ID} (hx : x ∈ hb.values) {v : Value}
    (hv : h.value? x = some v) : Placed h x v ∧ v.block = b ∧ v.id = x := by
  obtain ⟨v', hp, hb', hid⟩ := placed_of_mem hwf hbm hbb hx
  rw [hp.1] at hv; cases hv
  exact ⟨hp, hb', hid⟩

/-- The arguments of a non-`Phi` value placed in a tree block are placed in ancestors. -/
theorem arg_anc {ce : CheckEnv} {h : Func} (hwf : WF ce h) (hc : CertOK h) {x : ID} {v : Value}
    (hp : Placed h x v) (ht : ((make h).depthOf v.block).isSome) (hphi : v.op ≠ .Phi) {a : ID}
    (ha : a ∈ v.args) : ∃ va, Placed h a va ∧ Anc (make h) va.block v.block := by
  obtain ⟨hv, hbm, blk, hblk, hx⟩ := hp
  have hu := uses hc hbm hblk ht hx hv hphi ha
  obtain ⟨va, hpa, hba⟩ := placed_of_listed hwf (hwf.argListed _ _ _ _ ⟨⟨hbm, hblk⟩, hx, hv⟩ a ha)
  rw [hba] at hu
  exact ⟨va, hpa, hu⟩

theorem termOp_phi : termOp .Phi = false := by decide

/-- Placed values of strict ancestors are closed under the arguments of term nodes. -/
theorem closed_sanc {ce : CheckEnv} {h : Func} (hwf : WF ce h) (hc : CertOK h) {b : ID}
    {D : ID → Option Value} (hD : ∀ x v w, Placed h x v → D x = some w → w = v) :
    Closed D (SAnc h b) := by
  intro x ⟨v, hp, hanc, hne⟩ w hw ht a ha
  have hwv := hD x v w hp hw
  subst hwv
  have hphi : w.op ≠ .Phi := fun he => by rw [he, termOp_phi] at ht; cases ht
  obtain ⟨va, hpa, hanc'⟩ := arg_anc hwf hc hp (Anc.left hc.parents hanc) hphi ha
  refine ⟨va, hpa, Anc.trans hc.parents hanc' hanc, fun he => ?_⟩
  rw [he] at hanc'
  exact hne (Anc.antisymm hc.parents hanc hanc')

theorem closed_sanc_f {ce : CheckEnv} {f : Func} (hwf : WF ce f) (hc : CertOK f) (b : ID) :
    Closed f.value? (SAnc f b) :=
  closed_sanc hwf hc fun _ _ _ hp hw => placed_val hp hw

theorem closed_sanc_g {ce : CheckEnv} {g : Func} (hwf : WF ce g) (hc : CertOK g) (b : ID) :
    Closed (listedDefs g) (SAnc g b) :=
  closed_sanc hwf hc fun _ _ _ hp hw => by rw [placed_listed hp] at hw; cases hw; rfl

/-! ## Atoms of `g` -/

/-- An atom placed in `g` is placed in the same block of `f` with the same fields. -/
theorem gatom_f {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} (H : Hyp tabs f g ce ce')
    {a : ID} {w : Value} (hp : Placed g a w) (ht : termOp w.op = false) :
    ∃ u, Placed f a u ∧ SameAtom u w := by
  obtain ⟨hw, hbm, blk, hblk, hx⟩ := hp
  have hbm' : w.block ∈ f.blocks := by rw [H.ok.blocks]; exact hbm
  obtain ⟨fc, gc, hfc, hgc, hBA⟩ := H.ok.block w.block hbm'
  rw [hblk] at hgc; cases hgc
  obtain ⟨hxf, u, hu, hs⟩ := hBA.sub a hx w hw ht
  refine ⟨u, ⟨hu, ?_, fc, ?_, hxf⟩, hs⟩
  · rw [hs.2.2.2.2.2.1]; exact hbm'
  · rw [hs.2.2.2.2.2.1]; exact hfc

/-- The shape of an atom of `g` is its shape in `f`. -/
theorem shape_atom {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} (H : Hyp tabs f g ce ce')
    {a : ID} (hat : ¬ IsTerm (listedDefs g) a) :
    shape (listedDefs g) tabs a = .other ∨ shape (listedDefs g) tabs a = shape f.value? tabs a := by
  cases hl : listedDefs g a with
  | none => left; simp [shape, hl]
  | some w =>
    right
    have ht : termOp w.op = false := by
      cases h : termOp w.op
      · rfl
      · exact absurd ⟨w, hl, h⟩ hat
    obtain ⟨u, hpu, hs⟩ := gatom_f H (listed_placed hl) ht
    simp [shape, hl, hpu.1, hs.2.1]

/-- An atom the target defines has the source's shape. -/
theorem shape_atom_def {tabs : Tables} {f g : Func} {ce ce' : CheckEnv} (H : Hyp tabs f g ce ce')
    {a : ID} (hat : ¬ IsTerm (listedDefs g) a) (hdef : (listedDefs g a).isSome) :
    shape (listedDefs g) tabs a = shape f.value? tabs a := by
  cases hl : listedDefs g a with
  | none => rw [hl] at hdef; cases hdef
  | some w =>
    have ht : termOp w.op = false := by
      cases h : termOp w.op
      · rfl
      · exact absurd ⟨w, hl, h⟩ hat
    obtain ⟨u, hpu, hs⟩ := gatom_f H (listed_placed hl) ht
    simp [shape, hl, hpu.1, hs.2.1]

/-! ## `DenOK` in one frame -/

theorem DenOK.frame {D : ID → Option Value} {tabs : Tables} {fr fr' : Frame} {V : ID → Prop}
    (h : DenOK D tabs fr V) (hk : ∀ a, V a → fr'.regs[a]? = fr.regs[a]?) : DenOK D tabs fr' V :=
  (h.extend (W := fun _ => False) hk fun _ h => h.elim).iff fun _ => ⟨fun h => h.elim id False.elim,
    fun h => Or.inl h⟩

/-- Term nodes listed after their arguments, with their values over the registers. -/
def TermsOK (D : ID → Option Value) (tabs : Tables) (fr : Frame) : (ID → Prop) → List ID → Prop
  | _, [] => True
  | V, x :: s => Reg fr x ∧
      (∀ v, D x = some v → termOp v.op = true → (∀ a ∈ v.args, V a) ∧
        fr.regs[x]? = some (some ((evalPure v.op (tabs.ty v.type) v.auxInt v.aux
          (v.args.toList.map (rv fr))).retype (tabs.ty v.type)))) ∧
      TermsOK D tabs fr (fun a => V a ∨ a = x) s

theorem denOK_terms {D : ID → Option Value} {tabs : Tables} {fr : Frame} :
    ∀ {L : List ID} {V : ID → Prop}, DenOK D tabs fr V → TermsOK D tabs fr V L →
      DenOK D tabs fr (fun a => V a ∨ a ∈ L)
  | [], V, h, _ => h.iff fun a => ⟨.inl, fun h => h.elim id fun h => absurd h List.not_mem_nil⟩
  | x :: s, V, h, ⟨hreg, hterm, hs⟩ => by
    have h1 : DenOK D tabs fr (fun a => V a ∨ a = x) := by
      by_cases hxV : V x
      · exact h.iff fun a => ⟨.inl, fun h => h.elim id fun he => he ▸ hxV⟩
      · by_cases ht : IsTerm D x
        · obtain ⟨v, hv, hop⟩ := ht
          obtain ⟨hargs, hr⟩ := hterm v hv hop
          exact h.term (fun _ _ => rfl) hxV hv hop hargs hr
        · exact h.extend (W := fun a => a = x) (fun _ _ => rfl) fun a ha _ => ha ▸ ⟨ht, hreg⟩
    exact (denOK_terms h1 hs).iff fun a => by simp only [List.mem_cons, or_assoc]

/-! ## Lists -/

theorem topoRem_mid {D : ID → List ID} {x : ID} {s : List ID} :
    ∀ {d : List ID}, TopoRem D (d ++ x :: s) → ∀ a ∈ D x, a ∉ x :: s
  | [], h => h.1
  | _ :: d, h => topoRem_mid (d := d) h.2

theorem topoRem_prefix {D : ID → List ID} {s : List ID} :
    ∀ {d : List ID}, TopoRem D (d ++ s) → TopoRem D d
  | [], _ => trivial
  | x :: d, ⟨h1, h2⟩ => ⟨fun a ha hm => h1 a ha (by
      rcases List.mem_cons.1 hm with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ hm)), topoRem_prefix h2⟩

/-- An argument listed in a dependency order is listed before. -/
theorem topoRem_before {D : ID → List ID} {x a : ID} {d s : List ID}
    (h : TopoRem D (d ++ x :: s)) (ha : a ∈ D x) (hm : a ∈ d ++ x :: s) : a ∈ d := by
  rcases List.mem_append.1 hm with hm | hm
  · exact hm
  · exact absurd hm (topoRem_mid h a ha)

theorem append_cons_inj {r : ID} :
    ∀ {A B C E : List ID}, r ∉ A → r ∉ C → A ++ r :: B = C ++ r :: E → A = C
  | [], _, [], _, _, _, _ => rfl
  | [], _, c :: C, _, _, hC, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) hC
  | a :: A, _, [], _, hA, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) hA
  | a :: A, _, c :: C, _, hA, hC, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    rw [h.1, append_cons_inj (fun hm => hA (List.mem_cons_of_mem _ hm))
      (fun hm => hC (List.mem_cons_of_mem _ hm)) h.2]

/-- Two orders with the same filtered sequence agree, filtered, before an element of it. -/
theorem filter_prefix {p q : ID → Bool} {pre post preT postT : List ID} {r : ID}
    (h : (pre ++ r :: post).filter p = (preT ++ r :: postT).filter q) (hp : p r = true)
    (hq : q r = true) (hr : r ∉ pre) (hrT : r ∉ preT) : pre.filter p = preT.filter q := by
  rw [List.filter_append, List.filter_append, List.filter_cons_of_pos hp,
    List.filter_cons_of_pos hq] at h
  exact append_cons_inj (fun hm => hr (List.mem_filter.1 hm).1)
    (fun hm => hrT (List.mem_filter.1 hm).1) h

/-! ## Terminators and schedule nodes -/

theorem succ_mem {b : Block} {k : Nat} {e : Edge} (h : Sem.succ b k = .ok (.goto e)) :
    e ∈ b.succs := by
  unfold Sem.succ at h
  cases hk : b.succs[k]? with
  | none => rw [hk] at h; cases h
  | some e' => rw [hk] at h; cases h; exact Array.mem_of_getElem? hk

theorem stepTerm_goto_mem {fr : Frame} {b : Block} {e : Edge}
    (h : stepTerm fr b = .ok (.goto e)) : e ∈ b.succs := by
  unfold stepTerm at h
  cases hb : b.kind <;> simp only [hb] at h
  all_goals first
    | (cases h; done)
    | exact succ_mem h
    | (cases hc0 : Sem.control fr b 0 with
        | ok v =>
          rw [hc0] at h
          simp only [bind, Res.bind] at h
          split at h <;> first | (cases h; done) | exact succ_mem h | (split at h <;> first
            | (cases h; done) | (split at h <;> cases h))
        | panic e m => rw [hc0] at h; cases h
        | stuck msg => rw [hc0] at h; cases h)

/-- The schedule node of a non-`Phi` value of the block. -/
theorem nodeOf_schedNodes {f : Func} {b : Block} (hown : ValuesOwn f b)
    (hnd : b.values.toList.Nodup) {x : ID} {v : Value} (hx : x ∈ b.values)
    (hv : f.value? x = some v) (hp : v.op ≠ .Phi) :
    nodeOf (schedNodes f b).toList x = some ⟨x, v.args, prio v.op⟩ := by
  obtain ⟨v', hv', hvid⟩ := hown x hx
  rw [hv] at hv'; cases hv'
  have hm : (⟨v.id, v.args, prio v.op⟩ : SNode) ∈ (schedNodes f b).toList :=
    mem_schedNodes.2 ⟨x, hx, v, hv, hp, rfl⟩
  have := nodeOf_of_mem (schedNodes_ids hown hnd) hm
  rw [hvid] at this; exact this

end GoFV.Proof.AtomSim
