import GoFV.Proof.Pass.FuseRedirectRel
import GoFV.Proof.Pass.FuseCmpPres
import GoFV.Proof.DomRel

variable [GoFV.SSA.Sem.Addrs]

/-!
# A checked redirect keeps well-formedness and use dominance

`Base.wf_pres`: the result of a checked redirect of a well-formed function is well formed;
`Base.useDom_pres`: its uses are dominated on paths if the input's are. Neither needs a `check`
of the result: every block table entry is `expect`ed (`gblock`: untouched blocks have no edge
the redirect renumbers, `succs_fixed`), the values keep what is read, and a `child` `Phi`'s new
argument is its argument along `b → child`. A path of `g` is a path of `f` with `b` inserted
after each step `p → child` (`reach_f`), and the only value of `b` (its control, if any) is read
by nothing but `b`'s terminator.
-/

namespace GoFV.Proof.FuseRedirect

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.Fuse GoFV.Opt.Fuse.Redir GoFV.Proof
  Dom

/-- The shape of a redirect site in `f`, by name. -/
structure Shape (f : Func) (st : Site) (B P C : Block) : Prop where
  hB : f.block? st.b = some B
  hP : f.block? st.p = some P
  hC : f.block? st.child = some C
  bIn : st.b ∈ f.blocks
  pb : st.p ≠ st.b
  cb : st.child ≠ st.b
  centry : st.child ≠ f.entry
  out2 : st.out < 2
  kn : st.k ≤ st.n
  bkind : B.kind = .If
  bctl : B.controls = #[st.ctl]
  bsz : B.succs.size = 2
  bout : B.succs[st.out]? = some ⟨st.child, st.ai⟩
  bpsz : B.preds.size = st.n + 1
  bk : B.preds[st.k]? = some ⟨st.p, st.pi⟩
  bq : B.preds[st.n]?.map (·.b) = some st.q
  pkind : P.kind = .If
  pctl : P.controls = #[st.cp]
  cpsz : C.preds.size = st.cn
  bvals : B.values = #[] ∨ (B.values = #[st.ctl] ∧ st.ctlOK f = true)

variable {tabs : Tables} {f g : Func} {st : Site}

theorem RRel.sh (h : RRel tabs f g st) : ∃ B P C, Shape f st B P C := by
  obtain ⟨B, P, C, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20⟩ := h.shape
  exact ⟨B, P, C, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20⟩⟩

/-! ## The edge map and the expected blocks -/

theorem r_bk : st.r ⟨st.b, st.k⟩ = ⟨st.child, st.cn⟩ := by simp [Site.r]

theorem r_bn (h : st.n ≠ st.k) : st.r ⟨st.b, st.n⟩ = ⟨st.b, st.k⟩ := by
  simp [Site.r, h]

theorem r_self {e : Edge} (h1 : ¬ (e.b = st.b ∧ e.i = st.k)) (h2 : ¬ (e.b = st.b ∧ e.i = st.n)) :
    st.r e = e := by
  unfold Site.r
  rw [if_neg (by simpa using h1), if_neg (by simpa using h2)]

theorem r_ne {e : Edge} (h : e.b ≠ st.b) : st.r e = e :=
  r_self (fun h' => h h'.1) (fun h' => h h'.1)

/-- The edge map: `p → b` goes to `child`; otherwise the target block is kept. -/
theorem r_cases (e : Edge) :
    (e = ⟨st.b, st.k⟩ ∧ st.r e = ⟨st.child, st.cn⟩) ∨
      (e ≠ ⟨st.b, st.k⟩ ∧ (st.r e).b = e.b ∧
        (e.b = st.b → e.i = st.n → st.r e = ⟨st.b, st.k⟩) ∧
        (¬ (e.b = st.b ∧ e.i = st.n) → st.r e = e)) := by
  obtain ⟨eb, ei⟩ := e
  by_cases h1 : eb = st.b ∧ ei = st.k
  · obtain ⟨rfl, rfl⟩ := h1
    exact .inl ⟨rfl, r_bk⟩
  · refine .inr ⟨fun he => h1 ⟨(Edge.mk.inj he).1, (Edge.mk.inj he).2⟩, ?_, ?_, ?_⟩
    · unfold Site.r
      rw [if_neg (by simpa using h1)]
      split <;> simp_all
    · rintro rfl rfl
      unfold Site.r
      rw [if_neg (by simpa using h1)]
      simp
    · intro h2
      exact r_self h1 h2

theorem expect_id {x : ID} {X : Block} : (st.expect x X).id = X.id := by
  unfold Site.expect; split <;> split <;> rfl

theorem expect_values {x : ID} {X : Block} : (st.expect x X).values = X.values := by
  unfold Site.expect; split <;> split <;> rfl

theorem expect_kind {x : ID} {X : Block} : (st.expect x X).kind = X.kind := by
  unfold Site.expect; split <;> split <;> rfl

theorem expect_controls {x : ID} {X : Block} : (st.expect x X).controls = X.controls := by
  unfold Site.expect; split <;> split <;> rfl

theorem expect_succs {x : ID} {X : Block} : (st.expect x X).succs = X.succs.map st.r := by
  unfold Site.expect; split <;> split <;> rfl

theorem expect_preds (hcb : st.child ≠ st.b) {x : ID} {X : Block} :
    (st.expect x X).preds =
      if x = st.b then Cmp.swapRemove X.preds st.k
      else if x = st.child then X.preds.push ⟨st.p, st.pi⟩ else X.preds := by
  unfold Site.expect
  by_cases hb : x = st.b
  · subst hb
    simp [hcb.symm]
  · by_cases hc : x = st.child
    · subst hc; simp [hb]
    · simp [hb, hc]

/-! ## The setting -/

/-- A checked redirect of a well-formed function. -/
structure Base (ce : CheckEnv) (tabs : Tables) (f g : Func) (st : Site) : Prop where
  wf : WF ce f
  rel : RRel tabs f g st

namespace Base

variable {ce : CheckEnv} (S : Base ce tabs f g st)
include S

/-- An edge of `f` into `b` comes from the block at `b`'s predecessor entry. -/
theorem into_b {B : Block} (hB : f.block? st.b = some B) {y : ID} (hy : y ∈ f.blocks) {Y : Block}
    (hY : f.block? y = some Y) {j i : Nat} (hj : Y.succs[j]? = some ⟨st.b, i⟩) :
    B.preds[i]? = some ⟨y, j⟩ := by
  obtain ⟨-, C, hC, hci⟩ := S.wf.succLink y Y ⟨hy, hY⟩ j _ hj
  rw [hB] at hC; cases hC; exact hci

/-- `p`'s edge into `b`. -/
theorem p_succ {B P C : Block} (H : Shape f st B P C) : P.succs[st.pi]? = some ⟨st.b, st.k⟩ := by
  obtain ⟨-, P', hP', hs⟩ := S.wf.predLink st.b B ⟨H.bIn, H.hB⟩ st.k _ H.bk
  rw [H.hP] at hP'; cases hP'; exact hs

theorem p_in {B P C : Block} (H : Shape f st B P C) : st.p ∈ f.blocks :=
  (S.wf.predLink st.b B ⟨H.bIn, H.hB⟩ st.k _ H.bk).1

theorem child_in {B P C : Block} (H : Shape f st B P C) : st.child ∈ f.blocks :=
  (S.wf.succLink st.b B ⟨H.bIn, H.hB⟩ st.out _ H.bout).1

/-- `b`'s last predecessor edge, from `q`. -/
theorem q_succ {B P C : Block} (H : Shape f st B P C) :
    ∃ qi Q, B.preds[st.n]? = some ⟨st.q, qi⟩ ∧ st.q ∈ f.blocks ∧ f.block? st.q = some Q ∧
      Q.succs[qi]? = some ⟨st.b, st.n⟩ := by
  have hq := H.bq
  cases hn : B.preds[st.n]? with
  | none => rw [hn] at hq; cases hq
  | some e =>
    rw [hn] at hq
    simp only [Option.map_some, Option.some.injEq] at hq
    obtain ⟨hm, Q, hQ, hs⟩ := S.wf.predLink st.b B ⟨H.bIn, H.hB⟩ st.n e hn
    obtain ⟨eb, qi⟩ := e
    simp only at hq; subst hq
    exact ⟨qi, Q, rfl, hm, hQ, hs⟩

/-- An untouched listed block's successors avoid the renumbered edges. -/
theorem succs_fixed {B P C : Block} (H : Shape f st B P C) {x : ID} (hx : x ∈ f.blocks)
    {X : Block} (hX : f.block? x = some X) (ht : st.touched x = false) :
    X.succs.map st.r = X.succs := by
  have hxp : x ≠ st.p := fun h => by simp [Site.touched, h] at ht
  have hxq : x ≠ st.q := fun h => by simp [Site.touched, h] at ht
  apply Array.ext_getElem?
  intro j
  rw [Array.getElem?_map]
  cases hj : X.succs[j]? with
  | none => rfl
  | some e =>
    simp only [Option.map_some, Option.some.injEq]
    by_cases heb : e.b = st.b
    · obtain ⟨eb, ei⟩ := e
      simp only at heb; subst heb
      have hpr := S.into_b H.hB hx hX hj
      refine r_self (fun h1 => ?_) (fun h2 => ?_)
      · simp only at h1; rw [h1.2, H.bk] at hpr
        exact hxp (Edge.mk.inj (Option.some.inj hpr)).1.symm
      · simp only at h2
        obtain ⟨qi, Q, hqn, -⟩ := S.q_succ H
        rw [h2.2, hqn] at hpr
        exact hxq (Edge.mk.inj (Option.some.inj hpr)).1.symm
    · exact r_ne heb

/-- A listed block's entry in `g` is `expect`ed. -/
theorem gblock {B P C : Block} (H : Shape f st B P C) {x : ID} (hx : x ∈ f.blocks) {X : Block}
    (hX : f.block? x = some X) : g.block? x = some (st.expect x X) := by
  cases ht : st.touched x with
  | true =>
    have hm : x ∈ [st.b, st.p, st.child, st.q] := by
      unfold Site.touched at ht
      simp only [Bool.or_eq_true, beq_iff_eq] at ht
      rcases ht with ((h | h) | h) | h <;> simp [h]
    obtain ⟨X', hX', h⟩ := S.rel.gblock hm
    rw [hX] at hX'; cases hX'; exact h
  | false =>
    rw [S.rel.block_same ht, hX]
    have hb : x ≠ st.b := fun h => by simp [Site.touched, h] at ht
    have hc : x ≠ st.child := fun h => by simp [Site.touched, h] at ht
    congr 1
    unfold Site.expect
    simp only [beq_iff_eq, hb, hc, ite_false, S.succs_fixed H hx hX ht]

theorem gblock_inv {B P C : Block} (H : Shape f st B P C) {x : ID} (hx : x ∈ f.blocks) {Y : Block}
    (h : g.block? x = some Y) : ∃ X, f.block? x = some X ∧ Y = st.expect x X := by
  obtain ⟨X, hX, -⟩ := S.wf.blockId x hx
  rw [S.gblock H hx hX] at h; cases h
  exact ⟨X, hX, rfl⟩

theorem blockOf_g (a : ID) : blockOf g a = blockOf f a := by
  obtain ⟨hn, hv⟩ := S.rel.value a
  unfold blockOf
  cases hf : f.value? a with
  | none => rw [hn hf]
  | some v =>
    obtain ⟨w, hw, -, -, -, -, -, hb, -⟩ := hv v hf
    rw [hw]; simp [hb]

theorem listed_g {B P C : Block} (H : Shape f st B P C) {a : ID} (h : Listed f a) : Listed g a := by
  obtain ⟨y, Y, ⟨hy, hY⟩, ha⟩ := h
  exact ⟨y, _, ⟨S.rel.blocks ▸ hy, S.gblock H hy hY⟩, by rw [expect_values]; exact ha⟩

/-- `b`'s values are not `Phi`s. -/
theorem b_noPhi {B P C : Block} (H : Shape f st B P C) {x : ID} (hx : x ∈ B.values) {v : Value}
    (hv : f.value? x = some v) : v.op ≠ .Phi := by
  rcases H.bvals with h | ⟨h, hok⟩
  · rw [h] at hx; simp at hx
  · rw [h] at hx
    simp only [List.mem_toArray, List.mem_singleton] at hx
    subst hx
    obtain ⟨v', hv', -, ht, -⟩ := ctlOK_spec hok
    rw [hv] at hv'; cases hv'
    intro hp; rw [hp] at ht; exact absurd ht (by decide)

/-- A listed value in `b` is `ctl`, and then nothing but `b`'s terminator reads it. -/
theorem b_val {B P C : Block} (H : Shape f st B P C) {x : ID} (hx : x ∈ B.values) :
    x = st.ctl ∧ B.values ≠ #[] := by
  rcases H.bvals with h | ⟨h, -⟩
  · rw [h] at hx; simp at hx
  · rw [h] at hx
    simp only [List.mem_toArray, List.mem_singleton] at hx
    exact ⟨hx, by rw [h]; simp⟩

/-- A listed argument is not a value of `b`. -/
theorem arg_not_b {B P C : Block} (H : Shape f st B P C) {y : ID} (hy : y ∈ f.blocks) {Y : Block}
    (hY : f.block? y = some Y) {x : ID} (hx : x ∈ Y.values) {v : Value} (hv : f.value? x = some v)
    {a : ID} (ha : a ∈ v.args) : blockOf f a ≠ st.b := by
  intro hab
  obtain ⟨u, U, hP, hub, hU, haU, -⟩ :=
    blockOf_listed S.wf (S.wf.argListed y Y x v ⟨⟨hy, hY⟩, hx, hv⟩ a ha)
  rw [hab, H.hB] at hU; cases hU
  obtain ⟨rfl, hne⟩ := S.b_val H haU
  exact (S.rel.unread H.hB hne hy hY).1 x hx v hv ha

/-- A control of a block other than `b` is not a value of `b`. -/
theorem ctrl_not_b {B P C : Block} (H : Shape f st B P C) {y : ID} (hy : y ∈ f.blocks) {Y : Block}
    (hY : f.block? y = some Y) (hyb : y ≠ st.b) {c : ID} (hc : c ∈ Y.controls) :
    blockOf f c ≠ st.b := by
  intro hcb
  obtain ⟨u, U, hP, hub, hU, hcU, -⟩ := blockOf_listed S.wf (S.wf.ctrlListed y Y ⟨hy, hY⟩ c hc)
  rw [hcb, H.hB] at hU; cases hU
  obtain ⟨rfl, hne⟩ := S.b_val H hcU
  exact (S.rel.unread H.hB hne hy hY).2 hyb hc

/-- The value of a listed value of `f` in `g`. -/
theorem gval {y : ID} {Y : Block} (hy : BlockIn f y Y) {vid : ID} (hv : vid ∈ Y.values) :
    ∃ v w, f.value? vid = some v ∧ g.value? vid = some w ∧ v.id = vid ∧ v.block = y ∧
      w.id = v.id ∧ w.type = v.type ∧ w.aux = v.aux ∧ w.auxInt = v.auxInt ∧ w.op = v.op ∧
      w.block = v.block ∧
      (v.op = .Phi → y = st.child → st.ai < v.args.size ∧ w.args = v.args.push v.args[st.ai]!) ∧
      (¬ (v.op = .Phi ∧ y = st.child) → w.args = v.args) := by
  obtain ⟨v, hfv, hvid, hvb⟩ := S.wf.valueId y Y hy vid hv
  obtain ⟨-, hval⟩ := S.rel.value vid
  obtain ⟨w, hw, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hval v hfv
  exact ⟨v, w, hfv, hw, hvid, hvb, h1, h2, h3, h4, h5, h6, fun hp hs => h7 hp (hvb.trans hs),
    fun hn => h8 fun h => hn ⟨h.1, hvb.symm.trans h.2⟩⟩

/-- **Well-formedness is kept.** -/
theorem wf_pres {B P C : Block} (H : Shape f st B P C) : WF ce g := by
  have hwf := S.wf
  have hbl := S.rel.blocks
  have hcb := H.cb
  have hpsucc := S.p_succ H
  have hpm := S.p_in H
  have hcm := S.child_in H
  obtain ⟨qi, Q, hqn, hqm, hQ, hqs⟩ := S.q_succ H
  have hblk : ∀ bid b', BlockIn g bid b' → bid ∈ f.blocks ∧ ∃ X, f.block? bid = some X ∧
      b' = st.expect bid X := fun bid b' ⟨hm, hb'⟩ => by
    rw [hbl] at hm
    obtain ⟨X, hX, rfl⟩ := S.gblock_inv H hm hb'
    exact ⟨hm, X, hX, rfl⟩
  have hvin : ∀ bid b' vid v, ValueIn g bid b' vid v →
      ∃ X, BlockIn f bid X ∧ vid ∈ X.values ∧ b' = st.expect bid X := by
    rintro bid b' vid v ⟨hb, hvm, -⟩
    obtain ⟨hm, X, hX, rfl⟩ := hblk bid b' hb
    exact ⟨X, ⟨hm, hX⟩, by rwa [expect_values] at hvm, rfl⟩
  -- the edge of `g` along successor `j` of a listed block
  have hsucc : ∀ x X j e, f.block? x = some X → (st.expect x X).succs[j]? = some e →
      ∃ e0, X.succs[j]? = some e0 ∧ e = st.r e0 := fun x X j e _ he => by
    rw [expect_succs, Array.getElem?_map] at he
    cases h0 : X.succs[j]? with
    | none => rw [h0] at he; cases he
    | some e0 => rw [h0] at he; exact ⟨e0, h0, (Option.some.inj he).symm⟩
  have hgsucc : ∀ x X j e0, x ∈ f.blocks → f.block? x = some X → X.succs[j]? = some e0 →
      ∃ X', g.block? x = some X' ∧ X'.succs[j]? = some (st.r e0) := fun x X j e0 hx hX h0 =>
    ⟨_, S.gblock H hx hX, by rw [expect_succs, Array.getElem?_map, h0]; rfl⟩
  exact {
    blockId := fun bid hm => by
      rw [hbl] at hm
      obtain ⟨X, hX, hid⟩ := hwf.blockId bid hm
      exact ⟨_, S.gblock H hm hX, by rw [expect_id, hid]⟩
    blocksNodup := by rw [hbl]; exact hwf.blocksNodup
    valueId := fun bid b' hb vid hvm => by
      obtain ⟨hm, X, hX, rfl⟩ := hblk bid b' hb
      rw [expect_values] at hvm
      obtain ⟨v, w', -, hw', hvid, hvb, h1, -, -, -, -, h6, -⟩ := S.gval ⟨hm, hX⟩ hvm
      exact ⟨w', hw', h1.trans hvid, h6.trans hvb⟩
    valuesNodup := fun bid b' hb => by
      obtain ⟨hm, X, hX, rfl⟩ := hblk bid b' hb
      rw [expect_values]; exact hwf.valuesNodup bid X ⟨hm, hX⟩
    valueOnce := fun bid1 b1 bid2 b2 hb1 hb2 vid h1 h2 => by
      obtain ⟨hm1, X1, hX1, rfl⟩ := hblk bid1 b1 hb1
      obtain ⟨hm2, X2, hX2, rfl⟩ := hblk bid2 b2 hb2
      rw [expect_values] at h1 h2
      exact hwf.valueOnce bid1 X1 bid2 X2 ⟨hm1, hX1⟩ ⟨hm2, hX2⟩ vid h1 h2
    predLink := fun bid b' hb i e he => by
      obtain ⟨hm, X, hX, rfl⟩ := hblk bid b' hb
      rw [expect_preds hcb] at he
      rw [hbl]
      -- an edge of `f` into `bid` at `i0` that `r` maps to `⟨bid, i⟩`
      have hgen : ∀ i0, X.preds[i0]? = some e → st.r ⟨bid, i0⟩ = ⟨bid, i⟩ →
          e.b ∈ f.blocks ∧ ∃ p', g.block? e.b = some p' ∧ p'.succs[e.i]? = some ⟨bid, i⟩ := by
        intro i0 hi0 hr
        obtain ⟨hem, E, hE, hEs⟩ := hwf.predLink bid X ⟨hm, hX⟩ i0 e hi0
        obtain ⟨X', hX', hs⟩ := hgsucc e.b E e.i _ hem hE hEs
        exact ⟨hem, X', hX', by rw [hs, hr]⟩
      by_cases hbb : bid = st.b
      · subst hbb
        rw [if_pos rfl] at he
        rw [H.hB] at hX; cases hX
        obtain ⟨hin, h1, h2⟩ := FuseCmp.swapRemove_get_inv H.bpsz H.kn he
        by_cases hik : i = st.k
        · subst hik
          refine hgen st.n (h1 rfl) ?_
          exact r_bn (by omega)
        · refine hgen i (h2 hik) (r_self (fun h => hik h.2) (fun h => by simp only at h; omega))
      · rw [if_neg hbb] at he
        by_cases hcc : bid = st.child
        · subst hcc
          rw [if_pos rfl] at he
          rw [H.hC] at hX; cases hX
          rcases Nat.lt_or_ge i C.preds.size with hlt | hge
          · rw [Array.getElem?_push_lt hlt, ← Array.getElem?_eq_getElem hlt] at he
            exact hgen i he (r_ne hbb)
          · have hi : i = C.preds.size := by
              have := (Array.getElem?_eq_some_iff.1 he).1
              simp at this; omega
            rw [hi, Array.getElem?_push_size] at he
            cases he
            refine ⟨hpm, _, S.gblock H hpm H.hP, ?_⟩
            rw [expect_succs, Array.getElem?_map, hpsucc]
            simp [r_bk, hi, H.cpsz]
        · rw [if_neg hcc] at he
          exact hgen i he (r_ne hbb)
    succLink := fun bid b' hb j e he => by
      obtain ⟨hm, X, hX, rfl⟩ := hblk bid b' hb
      rw [hbl]
      obtain ⟨e0, he0, rfl⟩ := hsucc bid X j e hX he
      obtain ⟨hem, E, hE, hEi⟩ := hwf.succLink bid X ⟨hm, hX⟩ j e0 he0
      rcases r_cases (st := st) e0 with ⟨rfl, hr⟩ | ⟨hne, hrb, hrn, hrs⟩
      · -- `p → b` becomes `p → child` at `cn`
        rw [H.hB] at hE; cases hE
        rw [H.bk] at hEi; cases hEi
        rw [hr]
        refine ⟨hcm, _, S.gblock H hcm H.hC, ?_⟩
        rw [expect_preds hcb, if_neg hcb, if_pos rfl, ← H.cpsz, Array.getElem?_push_size]
      · rw [hrb]
        refine ⟨hem, _, S.gblock H hem hE, ?_⟩
        rw [expect_preds hcb]
        by_cases heb : e0.b = st.b
        · rw [if_pos heb]
          rw [heb, H.hB] at hE; cases hE
          by_cases hen : e0.i = st.n
          · have hnk : st.n ≠ st.k := fun h => hne (by
              obtain ⟨eb, ei⟩ := e0; simp only at heb hen; subst heb hen; rw [h])
            rw [hrn heb hen]
            have := FuseCmp.swapRemove_get H.bpsz H.kn (k := st.n) hnk
            simp only [ite_true] at this
            rw [this, ← hen, hEi]
          · rw [hrs fun h => hen h.2]
            have hik : e0.i ≠ st.k := fun h => hne (by
              obtain ⟨eb, ei⟩ := e0; simp only at heb h; subst heb h; rfl)
            have := FuseCmp.swapRemove_get H.bpsz H.kn (k := e0.i) hik
            simp only [hen, ite_false] at this
            rw [this, hEi]
        · rw [if_neg heb, r_ne heb]
          by_cases hec : e0.b = st.child
          · rw [if_pos hec]
            rw [hec, H.hC] at hE; cases hE
            have hlt := (Array.getElem?_eq_some_iff.1 hEi).1
            rw [Array.getElem?_push_lt hlt, ← Array.getElem?_eq_getElem hlt]; exact hEi
          · rw [if_neg hec]; exact hEi
    arity := fun bid b' vid v hv hlen => by
      obtain ⟨X, hX, hvx, rfl⟩ := hvin bid b' vid v hv
      obtain ⟨fv, w', hfv, hw', -, -, -, -, -, -, hop, -, -, hargs⟩ := S.gval hX hvx
      have hgv := hv.2.2
      rw [hw'] at hgv; cases hgv
      have hnp : ¬ (fv.op = .Phi ∧ bid = st.child) := fun h => by
        rw [hop, h.1] at hlen; exact hlen rfl
      rw [hargs hnp, hop]
      exact hwf.arity bid X vid fv ⟨hX, hvx, hfv⟩ (hop ▸ hlen)
    phiArity := fun bid b' vid v hv hph => by
      obtain ⟨X, hX, hvx, rfl⟩ := hvin bid b' vid v hv
      obtain ⟨fv, w', hfv, hw', -, -, -, -, -, -, hop, -, hsw, hargs⟩ := S.gval hX hvx
      have hgv := hv.2.2
      rw [hw'] at hgv; cases hgv
      have hfph : fv.op = .Phi := hop ▸ hph
      have har := hwf.phiArity bid X vid fv ⟨hX, hvx, hfv⟩ hfph
      have hbb : bid ≠ st.b := fun h => by
        subst h; have := hX.2; rw [H.hB] at this; cases this
        exact S.b_noPhi H hvx hfv hfph
      rw [expect_preds hcb, if_neg hbb]
      by_cases hcc : bid = st.child
      · rw [if_pos hcc, (hsw hfph hcc).2, Array.size_push, Array.size_push, har]
      · rw [if_neg hcc, hargs fun h => hcc h.2, har]
    boolAux := fun bid b' vid v hv haux => by
      obtain ⟨X, hX, hvx, rfl⟩ := hvin bid b' vid v hv
      obtain ⟨fv, w', hfv, hw', -, -, -, -, -, hai, hop, -, -, -⟩ := S.gval hX hvx
      have hgv := hv.2.2
      rw [hw'] at hgv; cases hgv
      rw [hai]
      exact hwf.boolAux bid X vid fv ⟨hX, hvx, hfv⟩ (hop ▸ haux)
    argListed := fun bid b' vid v hv a ha => by
      obtain ⟨X, hX, hvx, rfl⟩ := hvin bid b' vid v hv
      obtain ⟨fv, w', hfv, hw', -, -, -, -, -, -, -, -, hsw, hargs⟩ := S.gval hX hvx
      have hgv := hv.2.2
      rw [hw'] at hgv; cases hgv
      have ha' : a ∈ fv.args := by
        by_cases hc : fv.op = .Phi ∧ bid = st.child
        · obtain ⟨hlt, heq⟩ := hsw hc.1 hc.2
          rw [heq] at ha
          rcases Array.mem_push.1 ha with h | h
          · exact h
          · rw [h, getElem!_pos fv.args st.ai hlt]; exact Array.getElem_mem hlt
        · rwa [hargs hc] at ha
      exact S.listed_g H (hwf.argListed bid X vid fv ⟨hX, hvx, hfv⟩ a ha')
    ctrlListed := fun bid b' hb c hc => by
      obtain ⟨hm, X, hX, rfl⟩ := hblk bid b' hb
      rw [expect_controls] at hc
      exact S.listed_g H (hwf.ctrlListed bid X ⟨hm, hX⟩ c hc)
    entry := by rw [hbl, S.rel.entry]; exact hwf.entry
    entryPreds := fun b' hb' => by
      rw [S.rel.entry] at hb'
      obtain ⟨X, hX, rfl⟩ := S.gblock_inv H hwf.entry hb'
      have he0 := hwf.entryPreds X hX
      have hbe : f.entry ≠ st.b := fun h => by
        rw [h, H.hB] at hX; cases hX; have := H.bpsz; omega
      rw [expect_preds hcb, if_neg hbe, if_neg (Ne.symm H.centry), he0] }

/-- **A path of `g` is a path of `f`** with `b` inserted after each step `p → child`. -/
theorem reach_f {B P C : Block} (H : Shape f st B P C) {x : ID} {l : List ID}
    (hr : Reach g x l) : ∃ l', Reach f x l' ∧ ∀ z ∈ l', z ∈ l ∨ z = st.b := by
  induction hr with
  | entry => exact ⟨[f.entry], by rw [S.rel.entry]; exact .entry, fun z hz => .inl (by
      rw [S.rel.entry]; exact hz)⟩
  | @step y l blk e hr hb he ih =>
    obtain ⟨l', hl', hsub⟩ := ih
    have hym : y ∈ f.blocks := hl'.mem S.wf
    obtain ⟨X, hX, rfl⟩ := S.gblock_inv H hym hb
    rw [expect_succs, Array.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    have hsub' : ∀ z ∈ l', z ∈ (st.r e0).b :: l ∨ z = st.b := fun z hz =>
      (hsub z hz).imp_left (List.mem_cons_of_mem _)
    rcases r_cases (st := st) e0 with ⟨rfl, hr0⟩ | ⟨-, hrb, -⟩
    · rw [hr0]
      have h1 : Reach f st.b (st.b :: l') := .step hl' hX he0
      have h2 : Reach f st.child (st.child :: st.b :: l') :=
        .step h1 H.hB (Array.mem_of_getElem? H.bout)
      refine ⟨_, h2, fun z hz => ?_⟩
      rcases List.mem_cons.1 hz with rfl | hz
      · exact .inl List.mem_cons_self
      · rcases List.mem_cons.1 hz with rfl | hz
        · exact .inr rfl
        · rw [hr0] at hsub'; exact hsub' z hz
    · rw [hrb]
      refine ⟨_, .step hl' hX he0, fun z hz => ?_⟩
      rcases List.mem_cons.1 hz with rfl | hz
      · exact .inl List.mem_cons_self
      · rw [hrb] at hsub'; exact hsub' z hz

/-- **Use dominance is kept.** -/
theorem useDom_pres {B P C : Block} (H : Shape f st B P C) (hu : UseDom f) : UseDom g := by
  have hwf := S.wf
  have hcb := H.cb
  intro bid blk hbm hbb
  rw [S.rel.blocks] at hbm
  obtain ⟨X, hX, rfl⟩ := S.gblock_inv H hbm hbb
  obtain ⟨hu1, hu2, hu3⟩ := hu bid X hbm hX
  refine ⟨fun l hl vid hvid v hv hnp a ha => ?_, fun l hl x hx => ?_,
    fun vid hvid v hv hph i a e l ha he hr => ?_⟩
  · obtain ⟨l', hlf, hsub⟩ := S.reach_f H hl
    rw [expect_values] at hvid
    obtain ⟨fv, w', hfv, hw', -, -, -, -, -, -, hop, -, -, hargs⟩ := S.gval ⟨hbm, hX⟩ hvid
    rw [hw'] at hv; cases hv
    have hfnp : fv.op ≠ .Phi := hop ▸ hnp
    rw [hargs fun h => hfnp h.1] at ha
    rw [S.blockOf_g]
    rcases hsub _ (hu1 l' hlf vid hvid fv hfv hfnp a ha) with h | h
    · exact h
    · exact absurd h (S.arg_not_b H hbm hX hvid hfv ha)
  · rw [expect_controls] at hx
    obtain ⟨l', hlf, hsub⟩ := S.reach_f H hl
    rw [S.blockOf_g]
    rcases hsub _ (hu2 l' hlf x hx) with h | h
    · exact h
    · by_cases hyb : bid = st.b
      · rw [h, ← hyb]; exact hl.mem_self
      · exact absurd h (S.ctrl_not_b H hbm hX hyb hx)
  · rw [expect_values] at hvid
    obtain ⟨fv, w', hfv, hw', -, -, -, -, -, -, hop, -, hsw, hargs⟩ := S.gval ⟨hbm, hX⟩ hvid
    rw [hw'] at hv; cases hv
    have hfph : fv.op = .Phi := hop ▸ hph
    have hbb : bid ≠ st.b := fun h => by
      subst h
      have hXB := H.hB
      rw [hX] at hXB; cases hXB
      exact S.b_noPhi H hvid hfv hfph
    rw [expect_preds hcb, if_neg hbb] at he
    obtain ⟨l', hlf, hsub⟩ := S.reach_f H hr
    rw [S.blockOf_g]
    -- the argument read along a predecessor edge of `f`
    have hfin : ∀ (i0 : Nat) (a0 : ID) (l0 : List ID), fv.args[i0]? = some a0 → a0 = a →
        (∃ e0 : Edge, X.preds[i0]? = some e0 ∧ Reach f e0.b l0) →
        (∀ z ∈ l0, z ∈ l ∨ z = st.b) → blockOf f a ∈ l := by
      rintro i0 a0 l0 ha0 rfl ⟨e0, he0, hr0⟩ hs0
      rcases hs0 _ (hu3 vid hvid fv hfv hfph i0 a0 e0 l0 ha0 he0 hr0) with h | h
      · exact h
      · exact absurd h (S.arg_not_b H hbm hX hvid hfv (Array.mem_of_getElem? ha0))
    by_cases hcc : bid = st.child
    · rw [if_pos hcc] at he
      subst hcc
      rw [H.hC] at hX; cases hX
      obtain ⟨hlt, heq⟩ := hsw hfph rfl
      rw [heq] at ha
      have har : fv.args.size = C.preds.size := hwf.phiArity _ C vid fv ⟨⟨hbm, H.hC⟩, hvid, hfv⟩ hfph
      rcases Nat.lt_or_ge i C.preds.size with hlt' | hge
      · have hlt2 : i < fv.args.size := by omega
        rw [Array.getElem?_push_lt hlt2, ← Array.getElem?_eq_getElem hlt2] at ha
        rw [Array.getElem?_push_lt hlt', ← Array.getElem?_eq_getElem hlt'] at he
        exact hfin i a l' ha rfl ⟨e, he, hlf⟩ hsub
      · have hi : i = C.preds.size := by
          have := (Array.getElem?_eq_some_iff.1 he).1
          simp at this; omega
        rw [hi, Array.getElem?_push_size] at he
        cases he
        rw [hi, ← har, Array.getElem?_push_size] at ha
        cases ha
        -- along `b → child` in `f`, from `p`
        obtain ⟨-, C', hC', hcp⟩ := hwf.succLink st.b B ⟨H.bIn, H.hB⟩ st.out _ H.bout
        rw [H.hC] at hC'; cases hC'
        have hai : fv.args[st.ai]? = some fv.args[st.ai]! := by
          rw [getElem!_pos fv.args st.ai hlt]; exact Array.getElem?_eq_getElem hlt
        have hpb : Reach f st.b (st.b :: l') :=
          .step hlf H.hP (Array.mem_of_getElem? (S.p_succ H))
        refine hfin st.ai _ (st.b :: l') hai rfl ⟨_, hcp, hpb⟩ fun z hz => ?_
        rcases List.mem_cons.1 hz with rfl | hz
        · exact .inr rfl
        · exact hsub z hz
    · rw [if_neg hcc] at he
      rw [hargs fun h => hcc h.2] at ha
      exact hfin i a l' ha rfl ⟨e, he, hlf⟩ hsub

end Base

end GoFV.Proof.FuseRedirect
