import GoFV.Proof.Pass.FuseCmpTarget

/-!
# fuseComparisons keeps well-formedness and use dominance

`Base.wf_pres`: the result of a checked comparison fusion of a well-formed function is well
formed; `Base.useDom_pres`: its uses are dominated on paths if the input's are. Neither needs a
`check` of the result: the block table entries are `Site.expect`ed (the touched blocks) or
unchanged, the values keep what is read, `nv` is a fresh value of `b` reading `p`'s and `b`'s
controls. Every edge of `g` is an edge of `f` (`reach_f`), so a path of `g` is one of `f`, and
`nv`'s arguments lie on every path to `b` (through `p`, its only predecessor).
-/

namespace GoFV.Proof.FuseCmp

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.Fuse GoFV.Opt.Fuse.Cmp GoFV.Proof
  Dom

variable {f g : Func} {st : Site}

theorem expect_id {x : ID} {X : Block} : (st.expect x X).id = X.id := by
  unfold Site.expect; repeat' split
  all_goals rfl

theorem expect_values {x : ID} {X : Block} :
    (st.expect x X).values = if x = st.b then X.values.push st.nv else X.values := by
  unfold Site.expect
  by_cases hb : x = st.b
  · simp [hb]
  · simp only [beq_iff_eq, hb, ite_false]; repeat' split
    all_goals rfl

theorem expect_controls {x : ID} {X : Block} :
    (st.expect x X).controls =
      if x = st.b then #[st.nv] else if x = st.p then #[] else X.controls := by
  unfold Site.expect
  by_cases hb : x = st.b
  · simp [hb]
  · by_cases hp : x = st.p
    · subst hp; simp [hb]
    · simp only [beq_iff_eq, hb, hp, ite_false]; repeat' split
      all_goals rfl

theorem expect_succs {x : ID} {X : Block} (hp : x ≠ st.p) :
    (st.expect x X).succs = X.succs.map st.remapE := by
  unfold Site.expect
  by_cases hb : x = st.b
  · simp [hb]
  · simp only [beq_iff_eq, hb, hp, ite_false]; repeat' split
    all_goals rfl

theorem expect_succs_p {X : Block} (h : st.p ≠ st.b) : (st.expect st.p X).succs = #[⟨st.b, 0⟩] := by
  unfold Site.expect; simp [h]

theorem expect_preds {x : ID} {X : Block} (hsp : st.s ≠ st.p) :
    (st.expect x X).preds =
      if x = st.b then #[⟨st.p, 0⟩] else if x = st.s then swapRemove X.preds st.jp else X.preds := by
  unfold Site.expect
  by_cases hb : x = st.b
  · simp [hb]
  · by_cases hp : x = st.p
    · subst hp; simp [hb, Ne.symm hsp]
    · by_cases hs : x = st.s
      · subst hs; simp [hb, hp]
      · simp [hb, hp, hs]

theorem swapRemove_mem {α : Type} [Inhabited α] {a : Array α} {j : Nat} {x : α} (hj : j < a.size)
    (h : x ∈ swapRemove a j) : x ∈ a := by
  obtain ⟨k, hk⟩ := Array.mem_iff_getElem?.1 h
  have hsz : a.size = (a.size - 1) + 1 := by omega
  obtain ⟨-, h1, h2⟩ := swapRemove_get_inv hsz (by omega) hk
  by_cases hkj : k = j
  · exact Array.mem_of_getElem? (h1 hkj)
  · exact Array.mem_of_getElem? (h2 hkj)

theorem newOp_argLen (i : Nat) : (newOp i).argLen = 2 := by
  unfold newOp; split <;> rfl

theorem newOp_ne_phi (i : Nat) : newOp i ≠ .Phi := by
  unfold newOp; split <;> decide

theorem newOp_auxType (i : Nat) : (newOp i).auxType ≠ .Bool := by
  unfold newOp; split <;> decide

theorem phi_argLen : Op.Phi.argLen = -1 := rfl

namespace Base

variable (S : Base f g st)
include S

theorem ne3 : st.p ≠ st.b ∧ st.s ≠ st.b ∧ st.s ≠ st.p := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h1, h2, h3, -⟩ := S.rel.shape
  exact ⟨h1, h2, h3⟩

/-- An untouched listed block's successors avoid the moved edge. -/
theorem succs_fixed {x : ID} (hx : x ∈ f.blocks) {X : Block} (hX : f.block? x = some X)
    (ht : st.touched x = false) : X.succs.map st.remapE = X.succs := by
  obtain ⟨ce, hwf⟩ := S.wf
  apply Array.ext_getElem?
  intro j
  rw [Array.getElem?_map]
  cases hj : X.succs[j]? with
  | none => rfl
  | some e =>
    simp only [Option.map_some, Option.some.injEq]
    refine remapE_self fun hsn => ?_
    obtain ⟨-, C, hC, hci⟩ := hwf.succLink x X ⟨hx, hX⟩ j e hj
    obtain ⟨-, -, Sb, -, -, -, hS, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hSq, -⟩ :=
      S.rel.shape
    rw [hsn.1, hS] at hC; cases hC
    rw [← hsn.2, hci] at hSq
    simp only [Option.map_some, Option.some.injEq] at hSq
    unfold Site.touched at ht
    simp [hSq] at ht

/-- A listed block's entry in `g` is `expect`ed. -/
theorem gblock {x : ID} (hx : x ∈ f.blocks) {X : Block} (hX : f.block? x = some X) :
    g.block? x = some (st.expect x X) := by
  cases ht : st.touched x with
  | true =>
    have hm : x ∈ [st.p, st.b, st.s, st.q] := by
      unfold Site.touched at ht
      simp only [Bool.or_eq_true, beq_iff_eq] at ht
      rcases ht with ((h | h) | h) | h <;> simp [h]
    obtain ⟨X', hX', h⟩ := S.rel.gblock hm
    rw [hX] at hX'; cases hX'; exact h
  | false =>
    rw [S.rel.block_same ht, hX]
    have hb : x ≠ st.b := fun h => by simp [Site.touched, h] at ht
    have hp : x ≠ st.p := fun h => by simp [Site.touched, h] at ht
    have hs : x ≠ st.s := fun h => by simp [Site.touched, h] at ht
    congr 1
    unfold Site.expect
    simp only [beq_iff_eq, hb, hp, hs, ite_false, S.succs_fixed hx hX ht]

theorem gblock_inv {ce : CheckEnv} (hwf : WF ce f) {x : ID} (hx : x ∈ f.blocks) {Y : Block}
    (h : g.block? x = some Y) : ∃ X, f.block? x = some X ∧ Y = st.expect x X := by
  obtain ⟨X, hX, -⟩ := hwf.blockId x hx
  rw [S.gblock hx hX] at h; cases h
  exact ⟨X, hX, rfl⟩

/-- A value other than `nv` keeps its block. -/
theorem blockOf_g {a : ID} (ha : a ≠ st.nv) : blockOf g a = blockOf f a := by
  obtain ⟨hn, hv⟩ := S.rel.value ha
  unfold blockOf
  cases hf : f.value? a with
  | none => rw [hn hf]
  | some v =>
    obtain ⟨w, hw, -, -, -, -, -, hb, -⟩ := hv v hf
    rw [hw]; simp [hb]

theorem blockOf_nv : blockOf g st.nv = st.b := by
  obtain ⟨-, -, -, w, hw, -, -, -, hb, -⟩ := S.rel.newv
  unfold blockOf; rw [hw]; simp [hb]

theorem listed_g {a : ID} (h : Listed f a) : Listed g a := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨y, Y, ⟨hy, hY⟩, ha⟩ := h
  refine ⟨y, _, ⟨S.rel.blocks ▸ hy, S.gblock hy hY⟩, ?_⟩
  rw [expect_values]
  split
  · exact Array.mem_push_of_mem _ ha
  · exact ha

theorem nv_listed : Listed g st.nv := by
  obtain ⟨B, -, hB, -, -, -, -⟩ := S.bblock
  refine ⟨st.b, _, ⟨S.rel.blocks ▸ S.inB, S.gblock S.inB hB⟩, ?_⟩
  rw [expect_values, if_pos rfl]
  exact Array.mem_push_self

/-- A value listed in an `expect`ed block. -/
theorem values_mem {x : ID} {X : Block} {vid : ID} (h : vid ∈ (st.expect x X).values) :
    vid ∈ X.values ∨ (x = st.b ∧ vid = st.nv) := by
  rw [expect_values] at h
  split at h
  · rename_i hb
    rcases Array.mem_push.1 h with h | h
    · exact .inl h
    · exact .inr ⟨hb, h⟩
  · exact .inl h

/-- The edge of `f` an edge of a listed block of `g` comes from. -/
theorem gsucc {x : ID} (hx : x ∈ f.blocks) {X : Block} (hX : f.block? x = some X) {e : Edge}
    (he : e ∈ (st.expect x X).succs) : ∃ e0 ∈ X.succs, e0.b = e.b := by
  by_cases hp : x = st.p
  · subst hp
    obtain ⟨B, P, -, hP, -, -, hps⟩ := S.bblock
    rw [hX] at hP; cases hP
    rw [expect_succs_p S.ne3.1] at he
    simp only [List.mem_toArray, List.mem_singleton] at he
    subst he
    exact ⟨_, Array.mem_of_getElem? hps, rfl⟩
  · rw [expect_succs hp, Array.mem_map] at he
    obtain ⟨e0, he0, rfl⟩ := he
    exact ⟨e0, he0, remapE_b.symm⟩

/-- **A path of `g` is a path of `f`.** -/
theorem reach_f {ce : CheckEnv} (hwf : WF ce f) {x : ID} {l : List ID} (hr : Reach g x l) :
    Reach f x l := by
  induction hr with
  | entry => rw [S.rel.entry]; exact .entry
  | @step p l blk e hr hb he ih =>
    have hpm : p ∈ f.blocks := ih.mem hwf
    obtain ⟨X, hX, rfl⟩ := S.gblock_inv hwf hpm hb
    obtain ⟨e0, he0, hb0⟩ := S.gsucc hpm hX he
    rw [← hb0]
    exact .step ih hX he0

/-- The value of a listed value of `f` in `g`. -/
theorem gval {ce : CheckEnv} (hwf : WF ce f) {y : ID} {Y : Block} (hy : BlockIn f y Y) {vid : ID}
    (hv : vid ∈ Y.values) :
    ∃ v w, f.value? vid = some v ∧ g.value? vid = some w ∧ v.id = vid ∧ v.block = y ∧
      w.id = v.id ∧ w.type = v.type ∧ w.aux = v.aux ∧ w.auxInt = v.auxInt ∧ w.op = v.op ∧
      w.block = v.block ∧
      (v.op = .Phi → y = st.s → w.args = swapRemove v.args st.jp ∧ v.args[st.jp]? = v.args[st.jb]?) ∧
      (¬ (v.op = .Phi ∧ y = st.s) → w.args = v.args) := by
  obtain ⟨v, hfv, hvid, hvb⟩ := hwf.valueId y Y hy vid hv
  obtain ⟨-, hval⟩ := S.rel.value (S.mem_ne hy.1 hy.2 hv)
  obtain ⟨w, hw, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hval v hfv
  exact ⟨v, w, hfv, hw, hvid, hvb, h1, h2, h3, h4, h5, h6, fun hp hs => h7 hp (hvb.trans hs),
    fun hn => h8 fun h => hn ⟨h.1, hvb.symm.trans h.2⟩⟩

/-- The edges out of `p` in `f`: to `s` on side `i`, to `b` on side `kp`. -/
theorem p_succ {ce : CheckEnv} (hwf : WF ce f) {P : Block} (hP : f.block? st.p = some P) {j : Nat}
    {e : Edge} (he : P.succs[j]? = some e) :
    (j = st.i ∧ e = ⟨st.s, st.jp⟩) ∨ (j = st.kp ∧ e = ⟨st.b, 0⟩) := by
  obtain ⟨-, P1, -, -, -, hP1, -, -, -, hkp, hi, -, -, -, -, -, -, -, -, -, hPsz, hPs, -⟩ :=
    S.rel.shape
  rw [hP] at hP1; cases hP1
  obtain ⟨-, P2, -, hP2, -, -, hpk⟩ := S.bblock
  rw [hP] at hP2; cases hP2
  have hj : j < 2 := by rw [← hPsz]; exact (Array.getElem?_eq_some_iff.1 he).1
  have : j = st.i ∨ j = st.kp := by omega
  rcases this with rfl | rfl
  · rw [hPs] at he; cases he; exact .inl ⟨rfl, rfl⟩
  · rw [hpk] at he; cases he; exact .inr ⟨rfl, rfl⟩

/-- `p`'s only edge into `s` is at `jp`. -/
theorem s_pred_p {ce : CheckEnv} (hwf : WF ce f) {Sb : Block} (hS : f.block? st.s = some Sb)
    {k j : Nat} (h : Sb.preds[k]? = some ⟨st.p, j⟩) : k = st.jp := by
  obtain ⟨-, P, -, hP, -, -, -⟩ := S.bblock
  obtain ⟨-, -, hsm, -⟩ := S.s_preds
  obtain ⟨-, P', hP', hPs⟩ := hwf.predLink st.s Sb ⟨hsm, hS⟩ k _ h
  rw [hP] at hP'; cases hP'
  rcases S.p_succ hwf hP hPs with ⟨-, he⟩ | ⟨-, he⟩
  · exact (Edge.mk.inj he).2
  · exact absurd (Edge.mk.inj he).1 S.ne3.2.1

/-- **Well-formedness is kept.** -/
theorem wf_pres {ce : CheckEnv} (hwf : WF ce f) : WF ce g := by
  have hbl := S.rel.blocks
  obtain ⟨hpb, hsb, hsp⟩ := S.ne3
  obtain ⟨-, -, -, w, hw, hwid, hwop, hwargs, hwb, ⟨pv, hpv, -⟩, ⟨bv, hbv, -⟩⟩ := S.rel.newv
  obtain ⟨B, P, hB, hP, hpm, hbpr, hpk⟩ := S.bblock
  obtain ⟨Sb, hS, hsm, hjp, hjb, hSn, hjpn, hjbn, hjne⟩ := S.s_preds
  have hBnp : ∀ x ∈ B.values, ∀ v, f.value? x = some v → v.op ≠ .Phi := fun x hx v hv => by
    obtain ⟨v', -, hv', -, -, -, -, hnp, -⟩ := S.bval hB hx
    rw [hv] at hv'; cases hv'; exact hnp
  -- a block of `g`
  have hblk : ∀ bid b', BlockIn g bid b' → bid ∈ f.blocks ∧ ∃ X, f.block? bid = some X ∧
      b' = st.expect bid X := fun bid b' ⟨hm, hb'⟩ => by
    rw [hbl] at hm
    obtain ⟨X, hX, rfl⟩ := S.gblock_inv hwf hm hb'
    exact ⟨hm, X, hX, rfl⟩
  -- a value of a block of `g`
  have hvin : ∀ bid b' vid v, ValueIn g bid b' vid v →
      (vid = st.nv ∧ bid = st.b ∧ v = w) ∨
      (∃ X, BlockIn f bid X ∧ vid ∈ X.values ∧ b' = st.expect bid X) := by
    rintro bid b' vid v ⟨hb, hvm, hgv⟩
    obtain ⟨hm, X, hX, rfl⟩ := hblk bid b' hb
    rcases S.values_mem hvm with h | ⟨h1, h2⟩
    · exact .inr ⟨X, ⟨hm, hX⟩, h, rfl⟩
    · subst h2; rw [hw] at hgv; cases hgv; exact .inl ⟨rfl, h1, rfl⟩
  exact {
    blockId := fun bid hm => by
      rw [hbl] at hm
      obtain ⟨X, hX, hid⟩ := hwf.blockId bid hm
      exact ⟨_, S.gblock hm hX, by rw [expect_id, hid]⟩
    blocksNodup := by rw [hbl]; exact hwf.blocksNodup
    valueId := fun bid b' hb vid hvm => by
      obtain ⟨hm, X, hX, rfl⟩ := hblk bid b' hb
      rcases S.values_mem hvm with h | ⟨h1, h2⟩
      · obtain ⟨v, w', -, hw', hvid, hvb, h1, -, -, -, -, h6, -⟩ := S.gval hwf ⟨hm, hX⟩ h
        exact ⟨w', hw', h1.trans hvid, h6.trans hvb⟩
      · subst h2; exact ⟨w, hw, hwid, hwb.trans h1.symm⟩
    valuesNodup := fun bid b' hb => by
      obtain ⟨hm, X, hX, rfl⟩ := hblk bid b' hb
      rw [expect_values]
      split
      · rw [Array.toList_push, List.nodup_append]
        refine ⟨hwf.valuesNodup bid X ⟨hm, hX⟩, List.pairwise_singleton _ _, ?_⟩
        intro a ha b hb' hab
        rw [List.mem_singleton] at hb'
        subst hb'; subst hab
        exact S.mem_ne hm hX (Array.mem_toList_iff.1 ha) rfl
      · exact hwf.valuesNodup bid X ⟨hm, hX⟩
    valueOnce := fun bid1 b1 bid2 b2 hb1 hb2 vid h1 h2 => by
      obtain ⟨hm1, X1, hX1, rfl⟩ := hblk bid1 b1 hb1
      obtain ⟨hm2, X2, hX2, rfl⟩ := hblk bid2 b2 hb2
      rcases S.values_mem h1 with h1 | ⟨e1, n1⟩ <;> rcases S.values_mem h2 with h2 | ⟨e2, n2⟩
      · exact hwf.valueOnce bid1 X1 bid2 X2 ⟨hm1, hX1⟩ ⟨hm2, hX2⟩ vid h1 h2
      · exact absurd n2 (S.mem_ne hm1 hX1 h1)
      · exact absurd n1 (S.mem_ne hm2 hX2 h2)
      · rw [e1, e2]
    predLink := fun bid b' hb i e he => by
      obtain ⟨hm, X, hX, rfl⟩ := hblk bid b' hb
      rw [expect_preds hsp] at he
      rw [hbl]
      -- the source block of an edge of `f` into `bid` at index `k`, which `g` keeps but `p`'s
      have hgen : ∀ k, X.preds[k]? = some ⟨e.b, e.i⟩ → (e.b ≠ st.p) →
          (st.remapE ⟨bid, k⟩) = ⟨bid, i⟩ →
          e.b ∈ f.blocks ∧ ∃ p', g.block? e.b = some p' ∧ p'.succs[e.i]? = some ⟨bid, i⟩ := by
        intro k hk hne hr
        obtain ⟨hem, E, hE, hEs⟩ := hwf.predLink bid X ⟨hm, hX⟩ k ⟨e.b, e.i⟩ hk
        refine ⟨hem, _, S.gblock hem hE, ?_⟩
        rw [expect_succs hne, Array.getElem?_map, hEs]
        simp only [Option.map_some, hr]
      by_cases hbb : bid = st.b
      · subst hbb
        rw [if_pos rfl] at he
        have hi0 : i = 0 := by
          rcases Nat.lt_or_ge i 1 with h' | h'
          · omega
          · rw [Array.getElem?_eq_none (by simpa using h')] at he; cases he
        subst hi0
        simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at he
        subst he
        refine ⟨hpm, _, S.gblock hpm hP, ?_⟩
        rw [expect_succs_p hpb]; rfl
      · rw [if_neg hbb] at he
        by_cases hss : bid = st.s
        · rw [if_pos hss] at he
          have hXS : X = Sb := by rw [hss, hS] at hX; exact (Option.some.inj hX).symm
          rw [hXS] at he
          obtain ⟨hin, hk1, hk2⟩ := swapRemove_get_inv hSn hjpn he
          by_cases hij : i = st.jp
          · have hk := hk1 hij
            have hne : e.b ≠ st.p := fun h => by
              have : st.n = st.jp := S.s_pred_p hwf hS (j := e.i) (by rw [hk, ← h])
              omega
            refine hgen st.n (by rw [hXS]; exact hk) hne ?_
            rw [hss, Site.remapE]; simp [hij]
          · have hk := hk2 hij
            have hne : e.b ≠ st.p := fun h =>
              hij (S.s_pred_p hwf hS (j := e.i) (by rw [hk, ← h]))
            refine hgen i (by rw [hXS]; exact hk) hne ?_
            rw [hss, Site.remapE]; simp [show i ≠ st.n by omega]
        · rw [if_neg hss] at he
          have hne : e.b ≠ st.p := fun h => by
            obtain ⟨-, E, hE, hEs⟩ := hwf.predLink bid X ⟨hm, hX⟩ i e he
            rw [h, hP] at hE; cases hE
            rcases S.p_succ hwf hP hEs with ⟨-, h1⟩ | ⟨-, h1⟩
            · exact hss (Edge.mk.inj h1).1
            · exact hbb (Edge.mk.inj h1).1
          refine hgen i (by cases e; exact he) hne ?_
          rw [Site.remapE]; simp [hss]
    succLink := fun bid b' hb j e he => by
      obtain ⟨hm, X, hX, rfl⟩ := hblk bid b' hb
      rw [hbl]
      by_cases hbp : bid = st.p
      · subst hbp
        rw [hP] at hX; cases hX
        rw [expect_succs_p hpb] at he
        have hj0 : j = 0 := by
          rcases Nat.lt_or_ge j 1 with h' | h'
          · omega
          · rw [Array.getElem?_eq_none (by simpa using h')] at he; cases he
        subst hj0
        simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq] at he
        subst he
        refine ⟨S.inB, _, S.gblock S.inB hB, ?_⟩
        rw [expect_preds hsp, if_pos rfl]; rfl
      · rw [expect_succs hbp, Array.getElem?_map] at he
        cases he0 : X.succs[j]? with
        | none => rw [he0] at he; cases he
        | some e0 =>
          rw [he0] at he
          simp only [Option.map_some, Option.some.injEq] at he
          subst he
          obtain ⟨hem, C, hC, hci⟩ := hwf.succLink bid X ⟨hm, hX⟩ j e0 he0
          refine ⟨by rw [remapE_b]; exact hem, _, by rw [remapE_b]; exact S.gblock hem hC, ?_⟩
          rw [expect_preds hsp]
          by_cases heb : e0.b = st.b
          · exfalso
            rw [heb, hB] at hC; cases hC
            rw [hbpr] at hci
            have h0 : e0.i = 0 := by
              rcases Nat.lt_or_ge e0.i 1 with h' | h'
              · omega
              · rw [Array.getElem?_eq_none (by simpa using h')] at hci; cases hci
            rw [h0] at hci
            simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq,
              Edge.mk.injEq] at hci
            exact hbp hci.1.symm
          · rw [if_neg heb]
            by_cases hes : e0.b = st.s
            · rw [if_pos hes]
              have hCS : C = Sb := by rw [hes, hS] at hC; exact (Option.some.inj hC).symm
              subst hCS
              have hnp : ∀ k, C.preds[k]? = some ⟨bid, j⟩ → k ≠ st.jp := fun k hk hkj => by
                rw [hkj, hjp] at hk
                exact hbp (Edge.mk.inj (Option.some.inj hk)).1.symm
              by_cases hen : e0.i = st.n
              · have hr : st.remapE e0 = ⟨e0.b, st.jp⟩ := by
                  unfold Site.remapE; simp [hes, hen]
                rw [hr]
                have := swapRemove_get hSn hjpn (k := st.n) (fun h => hnp _ (hen ▸ hci) h)
                simp only [ite_true] at this
                rw [this, ← hen, hci]
              · rw [remapE_self fun h => hen h.2]
                have := swapRemove_get hSn hjpn (k := e0.i) (hnp _ hci)
                simp only [hen, ite_false] at this
                rw [this, hci]
            · rw [if_neg hes, remapE_self fun h => hes h.1]
              exact hci
    arity := fun bid b' vid v hv hlen => by
      rcases hvin bid b' vid v hv with ⟨-, -, rfl⟩ | ⟨X, hX, hvx, rfl⟩
      · rw [hwargs, hwop, newOp_argLen]; rfl
      · obtain ⟨fv, w', hfv, hw', -, -, -, -, -, -, hop, -, -, hargs⟩ := S.gval hwf hX hvx
        have hgv := hv.2.2
        rw [hw'] at hgv; cases hgv
        have hnp : ¬ (fv.op = .Phi ∧ bid = st.s) := fun h => by
          rw [hop, h.1] at hlen; exact hlen rfl
        rw [hargs hnp, hop]
        exact hwf.arity bid X vid fv ⟨hX, hvx, hfv⟩ (hop ▸ hlen)
    phiArity := fun bid b' vid v hv hph => by
      rcases hvin bid b' vid v hv with ⟨-, -, rfl⟩ | ⟨X, hX, hvx, rfl⟩
      · exact absurd (hwop ▸ hph) (newOp_ne_phi _)
      · obtain ⟨fv, w', hfv, hw', -, -, -, -, -, -, hop, -, hsw, hargs⟩ := S.gval hwf hX hvx
        have hgv := hv.2.2
        rw [hw'] at hgv; cases hgv
        have hfph : fv.op = .Phi := hop ▸ hph
        have har := hwf.phiArity bid X vid fv ⟨hX, hvx, hfv⟩ hfph
        have hbb : bid ≠ st.b := fun h => by
          subst h; have := hX.2; rw [hB] at this; cases this; exact hBnp vid hvx fv hfv hfph
        rw [expect_preds hsp, if_neg hbb]
        by_cases hss : bid = st.s
        · rw [if_pos hss, (hsw hfph hss).1, swapRemove_size, swapRemove_size, har]
        · rw [if_neg hss, hargs fun h => hss h.2, har]
    boolAux := fun bid b' vid v hv haux => by
      rcases hvin bid b' vid v hv with ⟨-, -, rfl⟩ | ⟨X, hX, hvx, rfl⟩
      · exact absurd (hwop ▸ haux) (newOp_auxType _)
      · obtain ⟨fv, w', hfv, hw', -, -, -, -, -, hai, hop, -, -, -⟩ := S.gval hwf hX hvx
        have hgv := hv.2.2
        rw [hw'] at hgv; cases hgv
        rw [hai]
        exact hwf.boolAux bid X vid fv ⟨hX, hvx, hfv⟩ (hop ▸ haux)
    argListed := fun bid b' vid v hv a ha => by
      rcases hvin bid b' vid v hv with ⟨-, -, rfl⟩ | ⟨X, hX, hvx, rfl⟩
      · obtain ⟨B1, P1, -, -, hB1, hP1, -, -, -, -, -, -, -, -, -, -, -, hBc, hPc, -⟩ := S.rel.shape
        rw [hB] at hB1; cases hB1
        rw [hP] at hP1; cases hP1
        rw [hwargs] at ha
        simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl
        · exact S.listed_g (hwf.ctrlListed st.p P ⟨hpm, hP⟩ _ (by rw [hPc]; simp))
        · exact S.listed_g (hwf.ctrlListed st.b B ⟨S.inB, hB⟩ _ (by rw [hBc]; simp))
      · obtain ⟨fv, w', hfv, hw', -, -, -, -, -, -, -, -, hsw, hargs⟩ := S.gval hwf hX hvx
        have hgv := hv.2.2
        rw [hw'] at hgv; cases hgv
        have ha' : a ∈ fv.args := by
          by_cases hc : fv.op = .Phi ∧ bid = st.s
          · rw [(hsw hc.1 hc.2).1] at ha
            have har := hwf.phiArity bid X vid fv ⟨hX, hvx, hfv⟩ hc.1
            have hXS : X = Sb := by
              have := hX.2; rw [hc.2, hS] at this; exact (Option.some.inj this).symm
            exact swapRemove_mem (by rw [har, hXS, hSn]; omega) ha
          · rwa [hargs hc] at ha
        exact S.listed_g (hwf.argListed bid X vid fv ⟨hX, hvx, hfv⟩ a ha')
    ctrlListed := fun bid b' hb c hc => by
      obtain ⟨hm, X, hX, rfl⟩ := hblk bid b' hb
      rw [expect_controls] at hc
      split at hc
      · simp only [List.mem_toArray, List.mem_singleton] at hc
        subst hc; exact S.nv_listed
      · split at hc
        · simp at hc
        · exact S.listed_g (hwf.ctrlListed bid X ⟨hm, hX⟩ c hc)
    entry := by rw [hbl, S.rel.entry]; exact hwf.entry
    entryPreds := fun b' hb' => by
      rw [S.rel.entry] at hb'
      obtain ⟨X, hX, rfl⟩ := S.gblock_inv hwf hwf.entry hb'
      have he0 := hwf.entryPreds X hX
      have hse : f.entry ≠ st.s := fun h => by
        rw [h, hS] at hX; cases hX; omega
      rw [expect_preds hsp, if_neg (Ne.symm S.b_ne_entry), if_neg hse, he0] }

/-- **Use dominance is kept.** -/
theorem useDom_pres (hu : UseDom f) : UseDom g := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨hpb, hsb, hsp⟩ := S.ne3
  obtain ⟨-, -, -, w, hw, -, hwop, hwargs, -, -⟩ := S.rel.newv
  obtain ⟨B, P, hB, hP, hpm, hbpr, hpk⟩ := S.bblock
  obtain ⟨Sb, hS, hsm, hjp, hjb, hSn, hjpn, hjbn, hjne⟩ := S.s_preds
  obtain ⟨B1, P1, -, -, hB1, hP1, -, -, -, -, -, -, -, -, -, -, -, hBc, hPc, -⟩ := S.rel.shape
  rw [hB] at hB1; cases hB1
  rw [hP] at hP1; cases hP1
  have hBnp : ∀ x ∈ B.values, ∀ v, f.value? x = some v → v.op ≠ .Phi := fun x hx v hv => by
    obtain ⟨v', -, hv', -, -, -, -, hnp, -⟩ := S.bval hB hx
    rw [hv] at hv'; cases hv'; exact hnp
  have hbo : ∀ a, Listed f a → blockOf g a = blockOf f a := fun a ha => S.blockOf_g (S.listed_ne ha)
  intro bid blk hbm hbb
  rw [S.rel.blocks] at hbm
  obtain ⟨X, hX, rfl⟩ := S.gblock_inv hwf hbm hbb
  obtain ⟨hu1, hu2, hu3⟩ := hu bid X hbm hX
  refine ⟨fun l hl vid hvid v hv hnp a ha => ?_, fun l hl x hx => ?_,
    fun vid hvid v hv hph i a e l ha he hr => ?_⟩
  · have hlf := S.reach_f hwf hl
    rcases S.values_mem hvid with hvx | ⟨rfl, rfl⟩
    · obtain ⟨fv, w', hfv, hw', -, -, -, -, -, -, hop, -, -, hargs⟩ := S.gval hwf ⟨hbm, hX⟩ hvx
      rw [hw'] at hv; cases hv
      have hfnp : fv.op ≠ .Phi := hop ▸ hnp
      rw [hargs fun h => hfnp h.1] at ha
      rw [hbo a (hwf.argListed bid X vid fv ⟨⟨hbm, hX⟩, hvx, hfv⟩ a ha)]
      exact hu1 l hlf vid hvx fv hfv hfnp a ha
    · rw [hw] at hv; cases hv
      rw [hwargs] at ha
      simp only [List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at ha
      have hXB : X = B := by rw [hX] at hB; exact Option.some.inj hB
      subst hXB
      rcases ha with rfl | rfl
      · have hc : st.pc ∈ P.controls := by rw [hPc]; simp
        rw [hbo _ (hwf.ctrlListed st.p P ⟨hpm, hP⟩ _ hc)]
        obtain ⟨l', rfl, hr'⟩ := S.reach_b hlf rfl
        exact List.mem_cons_of_mem _ ((hu st.p P hpm hP).2.1 l' hr' _ hc)
      · have hc : st.bc ∈ X.controls := by rw [hBc]; simp
        rw [hbo _ (hwf.ctrlListed _ X ⟨hbm, hX⟩ _ hc)]
        exact hu2 l hlf _ hc
  · rw [expect_controls] at hx
    split at hx
    · rename_i hbb'
      simp only [List.mem_toArray, List.mem_singleton] at hx
      subst hx; subst hbb'
      rw [S.blockOf_nv]; exact hl.mem_self
    · split at hx
      · simp at hx
      · rw [hbo x (hwf.ctrlListed bid X ⟨hbm, hX⟩ x hx)]
        exact hu2 l (S.reach_f hwf hl) x hx
  · have hlf := S.reach_f hwf hr
    rcases S.values_mem hvid with hvx | ⟨-, rfl⟩
    · obtain ⟨fv, w', hfv, hw', -, -, -, -, -, -, hop, -, hsw, hargs⟩ := S.gval hwf ⟨hbm, hX⟩ hvx
      rw [hw'] at hv; cases hv
      have hfph : fv.op = .Phi := hop ▸ hph
      have hbb : bid ≠ st.b := fun h => by
        subst h; rw [hX] at hB; cases hB; exact hBnp vid hvx fv hfv hfph
      rw [expect_preds hsp, if_neg hbb] at he
      have hl : ∀ a, a ∈ fv.args → blockOf g a = blockOf f a := fun a ha =>
        hbo a (hwf.argListed bid X vid fv ⟨⟨hbm, hX⟩, hvx, hfv⟩ a ha)
      by_cases hss : bid = st.s
      · rw [if_pos hss] at he
        rw [(hsw hfph hss).1] at ha
        have hXS : X = Sb := by rw [hss, hS] at hX; exact (Option.some.inj hX).symm
        subst hXS
        have har : fv.args.size = st.n + 1 := by
          rw [hwf.phiArity bid X vid fv ⟨⟨hbm, hX⟩, hvx, hfv⟩ hfph, hSn]
        obtain ⟨-, ha1, ha2⟩ := swapRemove_get_inv har hjpn ha
        obtain ⟨-, he1, he2⟩ := swapRemove_get_inv hSn hjpn he
        by_cases hij : i = st.jp
        · have ha' := ha1 hij
          rw [hl a (Array.mem_of_getElem? ha')]
          exact hu3 vid hvx fv hfv hfph st.n a e l ha' (he1 hij) hlf
        · have ha' := ha2 hij
          rw [hl a (Array.mem_of_getElem? ha')]
          exact hu3 vid hvx fv hfv hfph i a e l ha' (he2 hij) hlf
      · rw [if_neg hss] at he
        rw [hargs fun h => hss h.2] at ha
        rw [hl a (Array.mem_of_getElem? ha)]
        exact hu3 vid hvx fv hfv hfph i a e l ha he hlf
    · rw [hw] at hv; cases hv
      exact absurd (hwop ▸ hph) (newOp_ne_phi _)

end Base

end GoFV.Proof.FuseCmp
