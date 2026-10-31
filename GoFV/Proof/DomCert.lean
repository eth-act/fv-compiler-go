import GoFV.Proof.CheckFacts

/-!
# What the dominator certificate gives

`GoFV.SSA.DomCert.check` (the last step of `check`) validates the dominator tree of `f`. Here:

* the tree facts: `Anc c a b` (`a` is `b` or a tree ancestor of `b`) is reflexive, transitive,
  antisymmetric and linear below a block (`anc_linear`); a strict ancestor of `b` is an ancestor
  of `b`'s immediate dominator (`Anc.up`);
* the edge, rootedness and use facts (`edge`, `rooted`, `uses`, `phiUse`, `ctrlUse`);
* the semantic dominance fact (`Reach.dom`, `use_dominated`): every ancestor of `b` — in
  particular the block of every value `b` uses — lies on every path from the entry to `b`.
-/

namespace GoFV.Proof.Dom

open GoFV.SSA GoFV.SSA.DomCert

theorem ensure_bind {b : Bool} {m : String} {k : Unit → Except String Unit}
    (h : (ensure b m >>= k) = .ok ()) : b = true ∧ k () = .ok () := by
  unfold ensure at h
  cases b
  · exact nomatch h
  · exact ⟨rfl, h⟩

theorem ensure_ok {b : Bool} {m : String} (h : ensure b m = .ok ()) : b = true := by
  unfold ensure at h
  cases b
  · exact nomatch h
  · rfl

/-- The four conditions of a passing certificate check. -/
structure CertOK (f : Func) : Prop where
  parents : parentsOK (make f) f.entry = true
  edges : edgesOK (make f) f = true
  rooted : rootedOK (make f) f = true
  uses : usesOK (make f) f = true

theorem certOK_of_check {f : Func} (h : DomCert.check f = .ok ()) : CertOK f := by
  unfold DomCert.check at h
  obtain ⟨h1, h⟩ := ensure_bind h
  obtain ⟨h2, h⟩ := ensure_bind h
  obtain ⟨h3, h⟩ := ensure_bind h
  exact ⟨h1, h2, h3, ensure_ok h⟩

/-! ## The tree -/

variable {c : Cert} {entry : ID}

/-- `a` is `b` or a tree ancestor of `b`. -/
def Anc (c : Cert) (a b : ID) : Prop := ∃ n k, c.depthOf b = some n ∧ k ≤ n ∧ c.walk k b = a

theorem lt_of_depthOf {b n : ID} (h : c.depthOf b = some n) : b < c.depth.size := by
  unfold Cert.depthOf at h
  rcases Nat.lt_or_ge b c.depth.size with hb | hb
  · exact hb
  · rw [Array.getElem?_eq_none hb] at h; cases h

theorem parent_spec (hp : parentsOK c entry = true) {b : ID} {n : Nat}
    (hb : c.depthOf b = some n) :
    (n = 0 → b = entry) ∧ (∀ k, n = k + 1 → c.idom[b]?.join = some (c.up b) ∧
      c.depthOf (c.up b) = some k) := by
  unfold parentsOK at hp
  rw [Bool.and_eq_true, List.all_eq_true] at hp
  have h := hp.2 b (List.mem_range.2 (lt_of_depthOf hb))
  rw [hb] at h
  refine ⟨fun h0 => ?_, fun k hk => ?_⟩
  · subst h0; simpa using h
  · subst hk
    simp only at h
    split at h
    · rename_i d hd
      unfold Cert.up; rw [hd]
      exact ⟨rfl, by simpa using h⟩
    · cases h

theorem entry_depth (hp : parentsOK c entry = true) : c.depthOf entry = some 0 := by
  unfold parentsOK at hp
  rw [Bool.and_eq_true] at hp
  simpa using hp.1

theorem walk_succ (k : Nat) (b : ID) : c.walk (k + 1) b = c.walk k (c.up b) := rfl

theorem walk_add (k : Nat) : ∀ j b, c.walk (k + j) b = c.walk k (c.walk j b) := by
  intro j
  induction j with
  | zero => intro b; rfl
  | succ j ih => intro b; rw [← Nat.add_assoc, walk_succ, ih, walk_succ]

theorem walk_depth (hp : parentsOK c entry = true) (k : Nat) :
    ∀ b n, c.depthOf b = some n → k ≤ n → c.depthOf (c.walk k b) = some (n - k) := by
  induction k with
  | zero => intro b n hb _; exact hb
  | succ k ih =>
    intro b n hb hk
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hu := ((parent_spec hp hb).2 m rfl).2
    rw [walk_succ, ih (c.up b) m hu (by omega)]
    congr 1; omega

theorem walk_root (hp : parentsOK c entry = true) {b : ID} {n : Nat}
    (hb : c.depthOf b = some n) : c.walk n b = entry := by
  have := walk_depth hp n b n hb (Nat.le_refl _)
  rw [Nat.sub_self] at this
  exact (parent_spec hp this).1 rfl

theorem anc_iff (hp : parentsOK c entry = true) {a b : ID} : c.anc a b = true ↔ Anc c a b := by
  unfold Cert.anc
  constructor
  · intro h
    split at h
    · rename_i da db _ hb
      rw [Bool.and_eq_true, decide_eq_true_iff, beq_iff_eq] at h
      exact ⟨db, db - da, hb, Nat.sub_le _ _, h.2⟩
    · cases h
  · rintro ⟨n, k, hb, hk, rfl⟩
    rw [walk_depth hp k b n hb hk, hb]
    simp only [Bool.and_eq_true, decide_eq_true_iff, beq_iff_eq]
    refine ⟨Nat.sub_le _ _, ?_⟩
    rw [show n - (n - k) = k by omega]

theorem Anc.right {a b : ID} (h : Anc c a b) : (c.depthOf b).isSome := by
  obtain ⟨n, _, hb, _⟩ := h; simp [hb]

theorem Anc.depth (hp : parentsOK c entry = true) {a b : ID} (h : Anc c a b) :
    ∃ na nb, c.depthOf a = some na ∧ c.depthOf b = some nb ∧ na ≤ nb ∧ (na = nb → a = b) := by
  obtain ⟨n, k, hb, hk, rfl⟩ := h
  refine ⟨n - k, n, walk_depth hp k b n hb hk, hb, Nat.sub_le _ _, fun he => ?_⟩
  have : k = 0 := by omega
  subst this; rfl

theorem Anc.left (hp : parentsOK c entry = true) {a b : ID} (h : Anc c a b) :
    (c.depthOf a).isSome := by
  obtain ⟨na, _, ha, _⟩ := h.depth hp; simp [ha]

theorem anc_refl {b : ID} (h : (c.depthOf b).isSome) : Anc c b b := by
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 h
  exact ⟨n, 0, hn, Nat.zero_le _, rfl⟩

theorem Anc.trans (hp : parentsOK c entry = true) {a b d : ID} (h1 : Anc c a b)
    (h2 : Anc c b d) : Anc c a d := by
  obtain ⟨n2, k2, hd, hk2, rfl⟩ := h2
  obtain ⟨n1, k1, hb, hk1, rfl⟩ := h1
  rw [walk_depth hp k2 d n2 hd hk2] at hb
  cases hb
  exact ⟨n2, k1 + k2, hd, by omega, walk_add k1 k2 d⟩

theorem Anc.antisymm (hp : parentsOK c entry = true) {a b : ID} (h1 : Anc c a b)
    (h2 : Anc c b a) : a = b := by
  obtain ⟨na, nb, ha, hb, hle, heq⟩ := h1.depth hp
  obtain ⟨nb', na', hb', ha', hle', _⟩ := h2.depth hp
  rw [ha] at ha'; rw [hb] at hb'; cases ha'; cases hb'
  exact heq (Nat.le_antisymm hle hle')

/-- A strict ancestor of `b` is an ancestor of `b`'s immediate dominator. -/
theorem Anc.up (hp : parentsOK c entry = true) {a b : ID} (h : Anc c a b) (hne : a ≠ b) :
    Anc c a (c.up b) := by
  obtain ⟨n, k, hb, hk, rfl⟩ := h
  cases k with
  | zero => exact absurd rfl hne
  | succ k =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact ⟨m, k, ((parent_spec hp hb).2 m rfl).2, by omega, rfl⟩

/-- The immediate dominator of a non-root tree block is a strict ancestor. -/
theorem anc_up_self (hp : parentsOK c entry = true) {b : ID} {n : Nat}
    (hb : c.depthOf b = some (n + 1)) : Anc c (c.up b) b ∧ c.up b ≠ b := by
  refine ⟨⟨n + 1, 1, hb, by omega, rfl⟩, fun he => ?_⟩
  have := ((parent_spec hp hb).2 n rfl).2
  rw [he, hb] at this
  cases this

theorem anc_linear (hp : parentsOK c entry = true) {a b x : ID} (h1 : Anc c a x)
    (h2 : Anc c b x) : Anc c a b ∨ Anc c b a := by
  obtain ⟨n, ka, hx, hka, rfl⟩ := h1
  obtain ⟨n', kb, hx', hkb, rfl⟩ := h2
  rw [hx] at hx'; cases hx'
  rcases Nat.le_total kb ka with h | h
  · refine .inl ⟨n - kb, ka - kb, walk_depth hp kb x n hx hkb, by omega, ?_⟩
    rw [← walk_add, Nat.sub_add_cancel h]
  · refine .inr ⟨n - ka, kb - ka, walk_depth hp ka x n hx hka, by omega, ?_⟩
    rw [← walk_add, Nat.sub_add_cancel h]

theorem anc_entry (hp : parentsOK c entry = true) {b : ID} (h : (c.depthOf b).isSome) :
    Anc c entry b := by
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 h
  exact ⟨n, n, hn, Nat.le_refl _, walk_root hp hn⟩

theorem anc_of_entry (hp : parentsOK c entry = true) {a : ID} (h : Anc c a entry) :
    a = entry := by
  obtain ⟨n, k, he, hk, rfl⟩ := h
  rw [entry_depth hp] at he; cases he
  cases Nat.le_zero.1 hk; rfl

/-- Ancestors of a block are strictly shallower unless equal. -/
theorem Anc.ne_of_up (hp : parentsOK c entry = true) {a b : ID} {n : Nat}
    (hb : c.depthOf b = some (n + 1)) (h : Anc c a (c.up b)) : a ≠ b := by
  rintro rfl
  have h' := (anc_up_self hp hb)
  exact h'.2 (Anc.antisymm hp h'.1 h)

/-! ## Facts about `f` -/

/-- An edge `p → e.b` (`e` among `p`'s successors). -/
theorem edge {f : Func} (hc : CertOK f) {p : ID} {blk : Block} (hp : p ∈ f.blocks)
    (hb : f.block? p = some blk) (ht : ((make f).depthOf p).isSome) {e : Edge}
    (he : e ∈ blk.succs) :
    e.b ≠ f.entry ∧ ((make f).depthOf e.b).isSome ∧ Anc (make f) ((make f).up e.b) p := by
  have h := hc.edges
  unfold edgesOK at h
  rw [Array.all_eq_true'] at h
  have h := h p hp
  simp only [Cert.inTree, ht, Bool.not_true, Bool.false_or, hb, Array.all_eq_true',
    Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h e he
  exact ⟨h1, h2, (anc_iff hc.parents).1 h3⟩

/-- A non-entry tree block has a tree predecessor it is not an ancestor of. -/
theorem rooted {f : Func} (hc : CertOK f) {b : ID} {blk : Block} (hm : b ∈ f.blocks)
    (hb : f.block? b = some blk) (ht : ((make f).depthOf b).isSome) (hne : b ≠ f.entry) :
    ∃ e ∈ blk.preds, ((make f).depthOf e.b).isSome ∧ ¬ Anc (make f) b e.b := by
  have h := hc.rooted
  unfold rootedOK at h
  rw [Array.all_eq_true'] at h
  have h := h b hm
  rw [Bool.or_eq_true, Bool.or_eq_true] at h
  simp only [Cert.inTree, ht, Bool.not_true, beq_iff_eq, hne] at h
  rcases h with (h | h) | h
  · cases h
  · cases h
  rw [hb, Array.any_eq_true'] at h
  obtain ⟨e, he, h⟩ := h
  rw [Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨e, he, h1, fun ha => ?_⟩
  rw [← anc_iff hc.parents] at ha
  rw [ha] at h2; cases h2

theorem usesBlock {f : Func} (hc : CertOK f) {b : ID} {blk : Block} (hm : b ∈ f.blocks)
    (hb : f.block? b = some blk) (ht : ((make f).depthOf b).isSome) :
    (∀ vid ∈ blk.values, ∃ v, f.value? vid = some v ∧
      (v.op = .Phi → ∀ p ∈ v.args.zip blk.preds,
        ((make f).depthOf p.2.b).isSome → Anc (make f) (blockOf f p.1) p.2.b) ∧
      (v.op ≠ .Phi → ∀ a ∈ v.args, Anc (make f) (blockOf f a) b)) ∧
    (∀ x ∈ blk.controls, Anc (make f) (blockOf f x) b) := by
  have h := hc.uses
  unfold usesOK at h
  rw [Array.all_eq_true'] at h
  have h := h b hm
  simp only [Cert.inTree, ht, Bool.not_true, Bool.false_or, hb, Bool.and_eq_true,
    Array.all_eq_true'] at h
  refine ⟨fun vid hv => ?_, fun x hx => (anc_iff hc.parents).1 (h.2 x hx)⟩
  have h1 := h.1 vid hv
  split at h1
  · cases h1
  · rename_i v hv'
    refine ⟨v, hv', fun hphi p hp hpt => ?_, fun hphi a ha => ?_⟩
    · have hc' : (v.op == .Phi) = true := by simpa using hphi
      simp only [hc', ite_true, Array.all_eq_true'] at h1
      have := h1 p hp
      simp only [hpt, Bool.not_true, Bool.false_or] at this
      exact (anc_iff hc.parents).1 this
    · have hc' : (v.op == .Phi) = false := by simpa using hphi
      simp only [hc', Bool.false_eq_true, ite_false, Array.all_eq_true'] at h1
      exact (anc_iff hc.parents).1 (h1 a ha)

/-- A non-`Phi` use in a tree block is defined in an ancestor. -/
theorem uses {f : Func} (hc : CertOK f) {b : ID} {blk : Block} (hm : b ∈ f.blocks)
    (hb : f.block? b = some blk) (ht : ((make f).depthOf b).isSome) {vid : ID} {v : Value}
    (hv : vid ∈ blk.values) (hvv : f.value? vid = some v) (hphi : v.op ≠ .Phi) {a : ID}
    (ha : a ∈ v.args) : Anc (make f) (blockOf f a) b := by
  obtain ⟨v', hv', -, h⟩ := (usesBlock hc hm hb ht).1 vid hv
  rw [hvv] at hv'; cases hv'
  exact h hphi a ha

/-- Argument `i` of a `Phi` of a tree block is defined in an ancestor of predecessor `i`, if
that is a tree block. -/
theorem phiUse {f : Func} (hc : CertOK f) {b : ID} {blk : Block} (hm : b ∈ f.blocks)
    (hb : f.block? b = some blk) (ht : ((make f).depthOf b).isSome) {vid : ID} {v : Value}
    (hv : vid ∈ blk.values) (hvv : f.value? vid = some v) (hphi : v.op = .Phi) {i : Nat}
    {a : ID} {e : Edge} (ha : v.args[i]? = some a) (he : blk.preds[i]? = some e)
    (hpt : ((make f).depthOf e.b).isSome) : Anc (make f) (blockOf f a) e.b := by
  obtain ⟨v', hv', h, -⟩ := (usesBlock hc hm hb ht).1 vid hv
  rw [hvv] at hv'; cases hv'
  refine h hphi (a, e) ?_ hpt
  obtain ⟨hi1, rfl⟩ := Array.getElem?_eq_some_iff.1 ha
  obtain ⟨hi2, rfl⟩ := Array.getElem?_eq_some_iff.1 he
  exact Array.mem_iff_getElem.2 ⟨i, by simp [Nat.lt_min, hi1, hi2], by simp⟩

/-- A control of a tree block is defined in an ancestor. -/
theorem ctrlUse {f : Func} (hc : CertOK f) {b : ID} {blk : Block} (hm : b ∈ f.blocks)
    (hb : f.block? b = some blk) (ht : ((make f).depthOf b).isSome) {x : ID}
    (hx : x ∈ blk.controls) : Anc (make f) (blockOf f x) b :=
  (usesBlock hc hm hb ht).2 x hx

/-! ## Semantic dominance -/

/-- `Reach f b l`: `l` is a path from the entry to `b`, most recent block first. -/
inductive Reach (f : Func) : ID → List ID → Prop where
  | entry : Reach f f.entry [f.entry]
  | step {p : ID} {l : List ID} {blk : Block} {e : Edge} :
      Reach f p l → f.block? p = some blk → e ∈ blk.succs → Reach f e.b (e.b :: l)

/-- Every block on a path from the entry is a listed tree block, and each of its ancestors
lies on the path. -/
theorem Reach.dom {ce : CheckEnv} {f : Func} (hwf : WF ce f) (hc : CertOK f) {b : ID}
    {l : List ID} (h : Reach f b l) :
    b ∈ f.blocks ∧ ((make f).depthOf b).isSome ∧ ∀ a, Anc (make f) a b → a ∈ l := by
  induction h with
  | entry =>
    refine ⟨hwf.entry, by simp [entry_depth hc.parents], fun a ha => ?_⟩
    rw [anc_of_entry hc.parents ha]; exact List.mem_singleton_self _
  | @step p l blk e _ hb he ih =>
    obtain ⟨hm, ht, hl⟩ := ih
    obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 he
    obtain ⟨-, h2, h3⟩ := edge hc hm hb ht he
    refine ⟨(hwf.succLink p blk ⟨hm, hb⟩ j e hj).1, h2, fun a ha => ?_⟩
    by_cases hae : a = e.b
    · subst hae; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (hl a (Anc.trans hc.parents (ha.up hc.parents hae) h3))

/-- **Use dominance.** On every path from the entry to a block `b`, the block of every value
that a non-`Phi` value or a control of `b` uses occurs; for argument `i` of a `Phi`, it occurs
on every path to predecessor `i`. -/
theorem use_dominated {ce : CheckEnv} {f : Func} (h : check ce f = .ok ()) {b : ID}
    {blk : Block} (hbm : b ∈ f.blocks) (hb : f.block? b = some blk) :
    (∀ l, Reach f b l → ∀ vid ∈ blk.values, ∀ v, f.value? vid = some v → v.op ≠ .Phi →
      ∀ a ∈ v.args, blockOf f a ∈ l) ∧
    (∀ l, Reach f b l → ∀ x ∈ blk.controls, blockOf f x ∈ l) ∧
    (∀ vid ∈ blk.values, ∀ v, f.value? vid = some v → v.op = .Phi →
      ∀ (i : Nat) (a : ID) (e : Edge) (l : List ID), v.args[i]? = some a →
        blk.preds[i]? = some e → Reach f e.b l → blockOf f a ∈ l) := by
  have hwf := check_wf h
  have hc := certOK_of_check (check_domCert h)
  refine ⟨fun l hr vid hv v hvv hphi a ha => ?_, fun l hr x hx => ?_,
    fun vid hv v hvv hphi i a e l ha he hr => ?_⟩
  · obtain ⟨hm, ht, hl⟩ := hr.dom hwf hc
    exact hl _ (uses hc hm hb ht hv hvv hphi ha)
  · obtain ⟨hm, ht, hl⟩ := hr.dom hwf hc
    exact hl _ (ctrlUse hc hm hb ht hx)
  · obtain ⟨-, p, hp, hps⟩ := hwf.predLink b blk ⟨hbm, hb⟩ i e he
    have hrb : Reach f b (b :: l) := Reach.step (e := ⟨b, i⟩) hr hp (Array.mem_of_getElem? hps)
    obtain ⟨hm, ht, -⟩ := hrb.dom hwf hc
    obtain ⟨hpm, hpt, hl⟩ := hr.dom hwf hc
    exact hl _ (phiUse hc hm hb ht hv hvv hphi ha he hpt)

end GoFV.Proof.Dom
