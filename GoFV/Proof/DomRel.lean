import GoFV.Proof.DomCert
import GoFV.Proof.WFCheck

/-!
# Abstract dominance (`DomRel`) and path dominance (`SDom`)

`DomRel f T A`: `A a b` (`a` dominates `b`) is a partial order on the blocks `T` rooted at the
entry, closed along edges (a strict dominator of a successor dominates the edge's source) and
covering every use (the block of an argument or control dominates the using block; for argument
`i` of a `Phi`, predecessor `i`). These are the facts the dominance-based simulation lemmas
(`GoFV.Proof.Avail`) use. Two instances:

* the certified dominator tree (`CertOK.domRel`: `T` the tree blocks, `A = Anc (make f)`);
* **path dominance** (`UseDom.domRel`: `T` the blocks reachable from the entry, `SDom f a b`:
  `a` lies on every path from the entry to `b`), from `UseDom f`, the use facts on paths
  (`use_dominated`, a consequence of `check`). Unlike the certificate, `UseDom` speaks about paths
  only, so a rewrite whose paths map back onto the input's paths keeps it (no dominator tree of
  the result is needed: `GoFV.Proof.FusePlain.useDom_pres`).
-/

namespace GoFV.Proof.Dom

open GoFV.SSA GoFV.SSA.DomCert

/-- `A` is a dominance relation of `f` on the blocks `T` (see the module doc). -/
structure DomRel (f : Func) (T : ID → Prop) (A : ID → ID → Prop) : Prop where
  entry : T f.entry
  entry_anc : ∀ {a : ID}, A a f.entry → a = f.entry
  left : ∀ {a b : ID}, A a b → T a
  right : ∀ {a b : ID}, A a b → T b
  refl : ∀ {b : ID}, T b → A b b
  trans : ∀ {a b d : ID}, A a b → A b d → A a d
  antisymm : ∀ {a b : ID}, A a b → A b a → a = b
  /-- A successor of a covered block is covered; its strict dominators dominate the source. -/
  edge : ∀ {p : ID} {blk : Block} {e : Edge}, p ∈ f.blocks → f.block? p = some blk → T p → e ∈ blk.succs →
    T e.b ∧ ∀ a, A a e.b → a ≠ e.b → A a p
  uses : ∀ {b : ID} {blk : Block}, b ∈ f.blocks → f.block? b = some blk → T b → ∀ {vid : ID} {v : Value}, vid ∈ blk.values →
    f.value? vid = some v → v.op ≠ .Phi → ∀ {a : ID}, a ∈ v.args → A (blockOf f a) b
  phiUse : ∀ {b : ID} {blk : Block}, b ∈ f.blocks → f.block? b = some blk → T b → ∀ {vid : ID} {v : Value}, vid ∈ blk.values →
    f.value? vid = some v → v.op = .Phi → ∀ {i : Nat} {a : ID} {e : Edge}, v.args[i]? = some a →
    blk.preds[i]? = some e → T e.b → A (blockOf f a) e.b
  ctrlUse : ∀ {b : ID} {blk : Block}, b ∈ f.blocks → f.block? b = some blk → T b → ∀ {x : ID}, x ∈ blk.controls →
    A (blockOf f x) b

/-- The certified dominator tree is a dominance relation. -/
theorem CertOK.domRel {f : Func} (hc : CertOK f) :
    DomRel f (fun b => ((make f).depthOf b).isSome) (Anc (make f)) where
  entry := by simp [entry_depth hc.parents]
  entry_anc := anc_of_entry hc.parents
  left := Anc.left hc.parents
  right := Anc.right
  refl := anc_refl
  trans := Anc.trans hc.parents
  antisymm := Anc.antisymm hc.parents
  edge := fun hp hb ht he =>
    let h := Dom.edge hc hp hb ht he
    ⟨h.2.1, fun _ ha hne => Anc.trans hc.parents (ha.up hc.parents hne) h.2.2⟩
  uses := fun hm hb ht _ _ hv hvv hphi _ ha => Dom.uses hc hm hb ht hv hvv hphi ha
  phiUse := fun hm hb ht _ _ hv hvv hphi _ _ _ ha he hpt => Dom.phiUse hc hm hb ht hv hvv hphi ha he hpt
  ctrlUse := fun hm hb ht _ hx => Dom.ctrlUse hc hm hb ht hx

/-! ## Path dominance -/

/-- The use facts on paths (`use_dominated`): on every path from the entry to a listed block,
the block of every argument of a non-`Phi` and of every control occurs; for argument `i` of a
`Phi`, it occurs on every path to predecessor `i`. -/
def UseDom (f : Func) : Prop :=
  ∀ b blk, b ∈ f.blocks → f.block? b = some blk →
    (∀ l, Reach f b l → ∀ vid ∈ blk.values, ∀ v, f.value? vid = some v → v.op ≠ .Phi →
      ∀ a ∈ v.args, blockOf f a ∈ l) ∧
    (∀ l, Reach f b l → ∀ x ∈ blk.controls, blockOf f x ∈ l) ∧
    (∀ vid ∈ blk.values, ∀ v, f.value? vid = some v → v.op = .Phi →
      ∀ (i : Nat) (a : ID) (e : Edge) (l : List ID), v.args[i]? = some a →
        blk.preds[i]? = some e → Reach f e.b l → blockOf f a ∈ l)

/-- Use dominance of a well-formed function with a passing certificate (`use_dominated_of`). -/
theorem UseDom.of_cert {ce : CheckEnv} {f : Func} (hwf : WF ce f) (hc : CertOK f) : UseDom f :=
  fun _ _ hbm hb => use_dominated_of hwf hc hbm hb

theorem useDom_of_check {ce : CheckEnv} {f : Func} (h : check ce f = .ok ()) : UseDom f :=
  UseDom.of_cert (ce := ce) (check_wf h) (certOK_of_check (check_domCert h))

/-- **The invariant of the checked CFG passes** (issue #147): `f` is well formed and its uses
are dominated on paths. The slim input check `wfDomCheck` establishes it once per pass
(`WFDom.of_wfDomCheck`; `check` too, `WFDom.of_check`); every checked step keeps it, so no
intermediate function is checked. -/
structure WFDom (ce : CheckEnv) (f : Func) : Prop where
  wf : WF ce f
  dom : UseDom f

theorem WFDom.of_check {ce : CheckEnv} {f : Func} (h : check ce f = .ok ()) : WFDom ce f :=
  ⟨check_wf h, useDom_of_check h⟩

/-- **A passing slim input check gives the invariant** of the checked CFG passes. -/
theorem WFDom.of_wfDomCheck {ce : CheckEnv} {f : Func} (h : wfDomCheck f = .ok ()) :
    WFDom ce f :=
  ⟨wfDomCheck_wf h, UseDom.of_cert (ce := ce) (wfDomCheck_wf h)
    (certOK_of_check (wfDomCheck_domCert h))⟩

/-- `b` is reachable from the entry. -/
def Reachable (f : Func) (b : ID) : Prop := ∃ l, Reach f b l

/-- `a` lies on every path from the entry to the reachable block `b`. -/
def SDom (f : Func) (a b : ID) : Prop := Reachable f b ∧ ∀ l, Reach f b l → a ∈ l

variable {f : Func}

theorem Reach.head {b : ID} {l : List ID} (h : Reach f b l) : ∃ t, l = b :: t := by
  cases h with
  | entry => exact ⟨[], rfl⟩
  | step _ _ _ => exact ⟨_, rfl⟩

theorem Reach.mem_self {b : ID} {l : List ID} (h : Reach f b l) : b ∈ l := by
  obtain ⟨t, rfl⟩ := h.head; exact List.mem_cons_self

/-- A block on a path ends a prefix of the path. -/
theorem Reach.suffix {b : ID} {l : List ID} (h : Reach f b l) {y : ID} (hy : y ∈ l) :
    ∃ pre t, l = pre ++ t ∧ Reach f y t := by
  induction h with
  | entry =>
    rw [List.mem_singleton] at hy; subst hy
    exact ⟨[], _, rfl, .entry⟩
  | @step p l blk e hr hb he ih =>
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨[], _, rfl, .step hr hb he⟩
    · obtain ⟨pre, t, rfl, ht⟩ := ih hy
      exact ⟨e.b :: pre, t, rfl, ht⟩

/-- A block on a path is listed. -/
theorem Reach.mem {ce : CheckEnv} (hwf : WF ce f) {b : ID} {l : List ID} (h : Reach f b l) :
    b ∈ f.blocks := by
  induction h with
  | entry => exact hwf.entry
  | @step p l blk e _ hb he ih =>
    obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 he
    exact (hwf.succLink p blk ⟨ih, hb⟩ j e hj).1

theorem Reach.length_pos {b : ID} {l : List ID} (h : Reach f b l) : 0 < l.length := by
  obtain ⟨t, rfl⟩ := h.head; simp

theorem SDom.trans {a b d : ID} (h1 : SDom f a b) (h2 : SDom f b d) : SDom f a d := by
  refine ⟨h2.1, fun l hl => ?_⟩
  obtain ⟨pre, t, rfl, ht⟩ := hl.suffix (h2.2 l hl)
  exact List.mem_append_right _ (h1.2 t ht)

theorem SDom.left {a b : ID} (h : SDom f a b) : Reachable f a := by
  obtain ⟨l, hl⟩ := h.1
  obtain ⟨-, t, -, ht⟩ := hl.suffix (h.2 l hl)
  exact ⟨t, ht⟩

theorem SDom.refl {b : ID} (h : Reachable f b) : SDom f b b := ⟨h, fun _ hl => hl.mem_self⟩

theorem SDom.antisymm {a b : ID} (h1 : SDom f a b) (h2 : SDom f b a) : a = b := by
  refine Classical.byContradiction fun hne => ?_
  -- every path to `a` holds a strictly shorter path to `a`
  have key : ∀ n l, l.length ≤ n → Reach f a l → False := by
    intro n
    induction n with
    | zero => intro l hl hr; have := hr.length_pos; omega
    | succ n ih =>
      intro l hl hr
      obtain ⟨pre, t, rfl, ht⟩ := hr.suffix (h2.2 l hr)
      obtain ⟨pre', t', ht_eq, ht'⟩ := ht.suffix (h1.2 t ht)
      obtain ⟨tt, htt⟩ := ht.head
      obtain ⟨tt', htt'⟩ := ht'.head
      have hpre : pre' ≠ [] := by
        rintro rfl
        rw [List.nil_append, htt] at ht_eq
        rw [htt'] at ht_eq
        exact hne (List.cons.inj ht_eq).1.symm
      have hlen : t'.length < t.length := by
        rw [ht_eq, List.length_append]
        have := List.length_pos_iff.2 hpre
        omega
      exact ih t' (by rw [List.length_append] at hl; omega) ht'
  obtain ⟨l, hl⟩ := h1.left
  exact key l.length l (Nat.le_refl _) hl

/-- **Path dominance is a dominance relation** wherever the use facts hold on paths. -/
theorem UseDom.domRel (hu : UseDom f) : DomRel f (Reachable f) (SDom f) where
  entry := ⟨_, .entry⟩
  entry_anc := fun h => List.mem_singleton.1 (h.2 _ .entry)
  left := SDom.left
  right := fun h => h.1
  refl := SDom.refl
  trans := SDom.trans
  antisymm := SDom.antisymm
  edge := fun _ hb ht he => by
    obtain ⟨l, hl⟩ := ht
    refine ⟨⟨_, .step hl hb he⟩, fun a ha hne => ⟨⟨l, hl⟩, fun l' hl' => ?_⟩⟩
    rcases List.mem_cons.1 (ha.2 _ (.step hl' hb he)) with h | h
    · exact absurd h hne
    · exact h
  uses := fun hm hb ht _ _ hv hvv hphi _ ha =>
    ⟨ht, fun l hl => (hu _ _ hm hb).1 l hl _ hv _ hvv hphi _ ha⟩
  phiUse := fun hm hb _ _ _ hv hvv hphi _ _ _ ha he hpt =>
    ⟨hpt, fun l hl => (hu _ _ hm hb).2.2 _ hv _ hvv hphi _ _ _ l ha he hl⟩
  ctrlUse := fun hm hb ht _ hx => ⟨ht, fun l hl => (hu _ _ hm hb).2.1 l hl _ hx⟩

end GoFV.Proof.Dom
