import GoFV.Proof.Pass.FuseCmpRel
import GoFV.Proof.AgreeIdx
import GoFV.Proof.Enter
import GoFV.Proof.Mixed
import GoFV.Proof.SimIH
import GoFV.Proof.Speculate
import GoFV.Proof.Merge

variable [GoFV.SSA.Sem.Addrs]

/-!
# fuseComparisons: the setting of one checked rewrite

`Setup f g st`: `f` and `g` are well formed, `f`'s uses are dominated on paths (`UseDom`, so
path dominance `SDom f` is a dominance relation: `dom`), and `g` is `f` with one comparison
fusion at `st` (`CRel`).

The target speculates `b`'s values on the path `p → s`, so its registers may differ from the
source's on `b`'s values (`BVal`) and the new value `nv`. `Xq f st q` is the set they may differ
on at a block entered from `q`: `nv`, and `b`'s values unless `b` dominates `q` (then the
target's last execution of `b` was the source's). `IdxOK`: the target enters a block along the
remapped edge index (`p → s` removed: `s`'s last predecessor took `p`'s index), or along `b`'s
edge into `s` where the source came from `p`.

`enter_rel`: a block other than `b`, entered in frames agreeing outside `Xq` of its predecessor,
is entered alike in `g`; afterwards the frames agree outside `Xq` of the block itself.
-/

namespace GoFV.Proof.FuseCmp

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.Fuse GoFV.Opt.Fuse.Cmp GoFV.Proof Dom

/-- `f` is well formed and `g` is `f` with one comparison fusion at `st`. -/
structure Base (f g : Func) (st : Site) : Prop where
  wf : ∃ ce, WF ce f
  rel : CRel f g st

/-- See the module doc. -/
structure Setup (f g : Func) (st : Site) : Prop extends Base f g st where
  wg : ∃ ce, WF ce g
  cf : UseDom f

/-- `a` is a value of `b`. -/
def BVal (f : Func) (st : Site) (a : ID) : Prop := a ∈ (valsOf f st.b).toList

/-- The values the registers may differ on at a block entered from `q` (see the module doc). -/
def Xq (f : Func) (st : Site) (q : Option ID) (a : ID) : Prop :=
  a = st.nv ∨ (BVal f st a ∧ ∀ q', q = some q' → ¬ SDom f st.b q')

/-- The predecessor of `y` along index `i`. -/
def predOf (f : Func) (y : ID) (i : Nat) : Option ID :=
  ((f.block? y).bind (·.preds[i]?)).map (·.b)

/-- The target's edge index (see the module doc). -/
def IdxOK (st : Site) (y : ID) (iS iT : Nat) : Prop :=
  (y = st.s ∧ iS = st.jp ∧ iT = (st.remapE ⟨st.s, st.jb⟩).i) ∨
    ((y = st.s → iS ≠ st.jp) ∧ iT = (st.remapE ⟨y, iS⟩).i)

/-- The source's predecessor: a listed reachable block, or none at the entry. -/
def PredT (f : Func) (y : ID) (i : Nat) : Prop :=
  (∃ q, predOf f y i = some q ∧ q ∈ f.blocks ∧ Reachable f q) ∨
    (predOf f y i = none ∧ y = f.entry)

theorem remapE_b {st : Site} {e : Edge} : (st.remapE e).b = e.b := by
  unfold Site.remapE; split <;> rfl

theorem remapE_i {st : Site} {y : ID} {i : Nat} :
    (st.remapE ⟨y, i⟩).i = if y = st.s ∧ i = st.n then st.jp else i := by
  unfold Site.remapE
  by_cases h : y = st.s ∧ i = st.n
  · simp [h]
  · simp only [h, ite_false]
    split
    · rename_i h'; simp only [Bool.and_eq_true, beq_iff_eq] at h'; exact absurd h' h
    · rfl

theorem remapE_self {st : Site} {e : Edge} (h : ¬ (e.b = st.s ∧ e.i = st.n)) :
    st.remapE e = e := by
  unfold Site.remapE
  split
  · rename_i h'; simp only [Bool.and_eq_true, beq_iff_eq] at h'; exact absurd h' h
  · rfl

theorem predOf_eq {f : Func} {y : ID} {Y : Block} (hY : f.block? y = some Y) {i : Nat} :
    predOf f y i = (Y.preds[i]?).map (·.b) := by
  unfold predOf; rw [hY]; rfl

variable {f g : Func} {st : Site}

namespace Base

variable (S : Base f g st)
include S

theorem inB : st.b ∈ f.blocks := by
  obtain ⟨-, -, -, -, -, -, -, -, h, -⟩ := S.rel.shape; exact h

/-- `b`'s block, its only predecessor `p` and `p`'s edge to it. -/
theorem bblock : ∃ B P, f.block? st.b = some B ∧ f.block? st.p = some P ∧ st.p ∈ f.blocks ∧
    B.preds = #[⟨st.p, st.kp⟩] ∧ P.succs[st.kp]? = some ⟨st.b, 0⟩ := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨B, P, -, -, hB, hP, -, -, hbm, -, -, -, -, -, -, -, hpr, -⟩ := S.rel.shape
  obtain ⟨hpm, P', hP', hs⟩ := hwf.predLink st.b B ⟨hbm, hB⟩ 0 ⟨st.p, st.kp⟩ (by rw [hpr]; rfl)
  rw [hP] at hP'; cases hP'
  exact ⟨B, P, hB, hP, hpm, hpr, hs⟩

theorem inP : st.p ∈ f.blocks := by
  obtain ⟨-, -, -, -, h, -⟩ := S.bblock; exact h

theorem gsize : g.valueTab.size = f.valueTab.size := S.rel.newv.1

theorem params_eq {tabs : Tables} : (Ctx.make tabs g).params = (Ctx.make tabs f).params := by
  simp only [Ctx.make, abiParams, S.rel.ownAux]

/-- A listed value is not `nv`. -/
theorem listed_ne {a : ID} (h : Listed f a) : a ≠ st.nv := fun he => by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨bid, blk, hb, ha⟩ := h
  obtain ⟨v, hv, -, -⟩ := hwf.valueId bid blk hb a ha
  rw [he, S.rel.newv.2.2.1] at hv
  cases hv

theorem mem_ne {y : ID} (hy : y ∈ f.blocks) {Y : Block} (hY : f.block? y = some Y) {a : ID}
    (ha : a ∈ Y.values) : a ≠ st.nv := S.listed_ne ⟨y, Y, ⟨hy, hY⟩, ha⟩

/-- The value types, but `nv`'s, are unchanged. -/
theorem tys_eq {tabs : Tables} {x : ID} (hx : x ≠ st.nv) :
    (Ctx.make tabs g).tys[x]? = (Ctx.make tabs f).tys[x]? := by
  obtain ⟨hn, hv⟩ := S.rel.value hx
  cases hf : f.value? x with
  | some v =>
    obtain ⟨w, hw, -, hty, -⟩ := hv v hf
    rw [tys_of_value hf, tys_of_value hw, hty]
  | none =>
    have hg := hn hf
    unfold Func.value? at hf hg
    simp only [Ctx.make, Array.getElem?_map]
    have hsz := S.gsize
    rcases Nat.lt_or_ge x f.valueTab.size with hlt | hge
    · rw [Array.getElem?_eq_getElem hlt] at hf ⊢
      rw [Array.getElem?_eq_getElem (hsz ▸ hlt)] at hg ⊢
      simp only [Option.join_some] at hf hg
      simp only [Option.map_some, hf, hg]
    · rw [Array.getElem?_eq_none hge, Array.getElem?_eq_none (by omega)]

/-- A value of block `y ≠ b` is no value of `b`. -/
theorem not_bval {y : ID} (hy : y ∈ f.blocks) (hyb : y ≠ st.b) {Y : Block}
    (hY : f.block? y = some Y) {a : ID} (ha : a ∈ Y.values) : ¬ BVal f st a := fun hb => by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨B, hB, haB⟩ := FusePlain.valsOf_mem.1 hb
  exact hyb (hwf.valueOnce y Y st.b B ⟨hy, hY⟩ ⟨S.inB, hB⟩ a ha haB)

/-- A value of `b` lives in block `b`. -/
theorem blockOf_bval {a : ID} (h : BVal f st a) : blockOf f a = st.b := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨B, hB, haB⟩ := FusePlain.valsOf_mem.1 h
  obtain ⟨v, hv, -, hvb⟩ := hwf.valueId st.b B ⟨S.inB, hB⟩ a haB
  unfold blockOf; rw [hv]; exact hvb

/-- `b` is not the entry block. -/
theorem b_ne_entry : st.b ≠ f.entry := fun he => by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨B, -, hB, -, -, hpr, -⟩ := S.bblock
  rw [he] at hB
  have := hwf.entryPreds B hB
  rw [hpr] at this; cases this

/-- Every path to `b` comes from `p`. -/
theorem reach_b {y : ID} {l : List ID} (h : Reach f y l) (hy : y = st.b) :
    ∃ l', l = st.b :: l' ∧ Reach f st.p l' := by
  obtain ⟨ce, hwf⟩ := S.wf
  cases h with
  | entry => exact absurd hy.symm S.b_ne_entry
  | @step q l' blk e hr hq he =>
    obtain ⟨B, -, hB, -, -, hpr, -⟩ := S.bblock
    obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 he
    obtain ⟨-, C, hC, hci⟩ := hwf.succLink q blk ⟨hr.mem hwf, hq⟩ j e hj
    rw [hy, hB] at hC; cases hC
    rw [hpr] at hci
    have h0 : e.i = 0 := by
      rcases Nat.lt_or_ge e.i 1 with h' | h'
      · omega
      · rw [Array.getElem?_eq_none (by simpa using h')] at hci; cases hci
    rw [h0] at hci
    simp only [List.getElem?_toArray, List.getElem?_cons_zero, Option.some.injEq,
      Edge.mk.injEq] at hci
    rw [← hci.1] at hr
    exact ⟨l', by rw [hy], hr⟩

/-- The predecessors of `s` along `p`'s and `b`'s edges. -/
theorem s_preds : ∃ Sb, f.block? st.s = some Sb ∧ st.s ∈ f.blocks ∧
    Sb.preds[st.jp]? = some ⟨st.p, st.i⟩ ∧ Sb.preds[st.jb]? = some ⟨st.b, st.i⟩ ∧
    Sb.preds.size = st.n + 1 ∧ st.jp ≤ st.n ∧ st.jb ≤ st.n ∧ st.jb ≠ st.jp := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨B, P, Sb, -, hB, hP, hS, -, hbm, -, -, hpb, -, -, -, -, -, -, -, -, -, hPs, hBs, hSn,
    -⟩ := S.rel.shape
  obtain ⟨hsm, Sb', hS', hjp⟩ := hwf.succLink st.p P ⟨S.inP, hP⟩ st.i _ hPs
  rw [hS] at hS'; cases hS'
  obtain ⟨-, Sb', hS', hjb⟩ := hwf.succLink st.b B ⟨hbm, hB⟩ st.i _ hBs
  rw [hS] at hS'; cases hS'
  have hjp' : Sb.preds[st.jp]? = some ⟨st.p, st.i⟩ := hjp
  have hjb' : Sb.preds[st.jb]? = some ⟨st.b, st.i⟩ := hjb
  have hlt1 := (Array.getElem?_eq_some_iff.1 hjp').1
  have hlt2 := (Array.getElem?_eq_some_iff.1 hjb').1
  refine ⟨Sb, hS, hsm, hjp', hjb', hSn, by omega, by omega, fun he => ?_⟩
  rw [he, hjp'] at hjb'
  exact hpb (Edge.mk.inj (Option.some.inj hjb')).1

/-- A listed block other than `p` and `b` is unchanged but for `remapE` on its successors (and
the swap-removed predecessor of `s`). -/
theorem block_out {x : ID} (hx : x ∈ f.blocks) (hp : x ≠ st.p) (hb : x ≠ st.b) :
    ∃ fb gb, f.block? x = some fb ∧ g.block? x = some gb ∧ gb.id = fb.id ∧
      gb.values = fb.values ∧ gb.kind = fb.kind ∧ gb.controls = fb.controls ∧
      gb.succs = fb.succs.map st.remapE := by
  obtain ⟨ce, hwf⟩ := S.wf
  cases ht : st.touched x with
  | true =>
    have hm : x ∈ [st.p, st.b, st.s, st.q] := by
      unfold Site.touched at ht
      simp only [Bool.or_eq_true, beq_iff_eq] at ht
      rcases ht with ((h | h) | h) | h <;> simp [h]
    obtain ⟨X, hX, hX'⟩ := S.rel.gblock hm
    refine ⟨X, _, hX, hX', ?_⟩
    unfold Site.expect
    simp only [show (x == st.b) = false by simpa using hb, show (x == st.p) = false by simpa using hp,
      Bool.false_eq_true, ite_false]
    split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | false =>
    obtain ⟨X, hX, -⟩ := hwf.blockId x hx
    refine ⟨X, X, hX, by rw [S.rel.block_same ht, hX], rfl, rfl, rfl, rfl, ?_⟩
    apply Array.ext_getElem?
    intro j
    rw [Array.getElem?_map]
    cases hj : X.succs[j]? with
    | none => rfl
    | some e =>
      simp only [Option.map_some, Option.some.injEq]
      refine (remapE_self fun hsn => ?_).symm
      obtain ⟨-, C, hC, hci⟩ := hwf.succLink x X ⟨hx, hX⟩ j e hj
      obtain ⟨-, -, Sb, -, -, -, hS, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hSq, -⟩ :=
        S.rel.shape
      rw [hsn.1, hS] at hC; cases hC
      rw [← hsn.2, hci] at hSq
      simp only [Option.map_some, Option.some.injEq] at hSq
      unfold Site.touched at ht
      simp [hSq] at ht

/-- **The `Phi` arguments along the target's edge** are the source's. -/
theorem phi_idx {y : ID} (hy : y ∈ f.blocks) {Y : Block} (hY : f.block? y = some Y)
    {iS iT : Nat} (hidx : IdxOK st y iS iT) {x : ID} (hx : x ∈ Y.values) {v : Value}
    (hv : f.value? x = some v) (hph : v.op = .Phi) :
    ∃ w, g.value? x = some w ∧ w.op = v.op ∧ w.args[iT]? = v.args[iS]? := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨-, hval⟩ := S.rel.value (S.mem_ne hy hY hx)
  obtain ⟨w, hw, -, -, -, -, hop, -, hsw, hsame⟩ := hval v hv
  refine ⟨w, hw, hop, ?_⟩
  obtain ⟨Sb, hS, hsm, -, -, hSn, hjp, -, hjb⟩ := S.s_preds
  obtain ⟨v', hv', -, hvb⟩ := hwf.valueId y Y ⟨hy, hY⟩ x hx
  rw [hv] at hv'; cases hv'
  by_cases hys : y = st.s
  · rw [hys] at hY
    rw [hS] at hY; cases hY
    obtain ⟨hargs, hagree⟩ := hsw hph (hvb.trans hys)
    have hsz : v.args.size = st.n + 1 := by
      rw [hwf.phiArity st.s Y x v ⟨⟨hsm, hS⟩, hx, hv⟩ hph, hSn]
    rw [hargs]
    rcases hidx with ⟨-, hiS, hiT⟩ | ⟨hne, hiT⟩
    · rw [hiT, remapE_i, hiS, hagree]
      have := swapRemove_get hsz hjp hjb
      simpa using this
    · rw [hiT, remapE_i]
      have := swapRemove_get hsz hjp (hne hys)
      simpa [hys] using this
  · rw [hsame fun hh => hys (hvb.symm.trans hh.2)]
    rcases hidx with ⟨h, -, -⟩ | ⟨-, hiT⟩
    · exact absurd h hys
    · rw [hiT, remapE_i]; simp [hys]

end Base

namespace Setup

variable (S : Setup f g st)
include S

theorem dom : DomRel f (Reachable f) (SDom f) := S.cf.domRel

/-- `b` does not dominate `p` (`p` dominates `b`, its only predecessor). -/
theorem not_sdom_bp : ¬ SDom f st.b st.p := fun h => by
  obtain ⟨-, P, -, hP, hpm, -, hps⟩ := S.bblock
  obtain ⟨l, hl⟩ := h.1
  have hpb : SDom f st.p st.b := ⟨⟨_, .step hl hP (Array.mem_of_getElem? hps)⟩, fun l' hl' => by
    obtain ⟨l'', rfl, hr⟩ := S.reach_b hl' rfl
    exact List.mem_cons_of_mem _ hr.mem_self⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hpb', -⟩ := S.rel.shape
  exact hpb' (S.dom.antisymm hpb h)

/-- If `b` dominates a block other than itself, it dominates its predecessor. -/
theorem sdom_pred {y : ID} (hy : y ∈ f.blocks) {i : Nat} (hp : PredT f y i) (hyb : y ≠ st.b)
    (ha : SDom f st.b y) : ∃ q, predOf f y i = some q ∧ SDom f st.b q := by
  obtain ⟨ce, hwf⟩ := S.wf
  rcases hp with ⟨q, hq, hqm, hqt⟩ | ⟨-, hye⟩
  · refine ⟨q, hq, ?_⟩
    unfold predOf at hq
    cases hY : f.block? y with
    | none => rw [hY] at hq; cases hq
    | some Y =>
      rw [hY] at hq
      simp only [Option.bind_some, Option.map_eq_some_iff] at hq
      obtain ⟨e, he, rfl⟩ := hq
      obtain ⟨-, Q, hQ, hQs⟩ := hwf.predLink y Y ⟨hy, hY⟩ i e he
      exact (S.dom.edge hqm hQ hqt (Array.mem_of_getElem? hQs)).2 st.b ha (Ne.symm hyb)
  · subst hye
    exact absurd (S.dom.entry_anc ha) S.b_ne_entry

/-- **Entering a block other than `b`** (see the module doc). -/
theorem enter_rel {env : Env} {tabs : Tables} {y : ID} (hy : y ∈ f.blocks) (hyb : y ≠ st.b)
    {iS iT : Nat} (hidx : IdxOK st y iS iT) (hpt : PredT f y iS) {Y Y' : Block}
    (hY : f.block? y = some Y) (hY' : g.block? y = some Y') (hid : Y'.id = Y.id)
    (hvals : Y'.values = Y.values) (ht : Reachable f y) {frS frT : Frame}
    (hfr : frT = { frS with regs := frT.regs }) (hsz : frT.regs.size = frS.regs.size)
    (hag : ∀ a, ¬ Xq f st (predOf f y iS) a → frT.regs[a]? = frS.regs[a]?) :
    (∀ G, enterBlock env (Ctx.make tabs f) frS Y iS = .ok G →
      ∃ GT, enterBlock env (Ctx.make tabs g) frT Y' iT = .ok GT ∧
        GT = { G with regs := GT.regs } ∧ GT.regs.size = G.regs.size ∧
        ∀ a, ¬ Xq f st (some y) a → GT.regs[a]? = G.regs[a]?) ∧
    (∀ e m, enterBlock env (Ctx.make tabs f) frS Y iS = .panic e m →
      enterBlock env (Ctx.make tabs g) frT Y' iT = .panic e m) := by
  obtain ⟨ce, hwf⟩ := S.wf
  have hD := S.dom
  obtain ⟨b', hb', hbid⟩ := hwf.blockId y hy
  rw [hY] at hb'; cases hb'
  -- a read of a value of `b` in `y` (or along its incoming edge) is no difference
  have hread : ∀ a, Listed f a → (BVal f st a → SDom f st.b y) →
      ¬ Xq f st (predOf f y iS) a := by
    intro a hl hba hx
    rcases hx with hx | ⟨hbv, hnq⟩
    · exact S.listed_ne hl hx
    · obtain ⟨q, hq, hqa⟩ := S.sdom_pred hy hpt hyb (hba hbv)
      exact hnq q hq hqa
  have hca : ∀ l : List ID, (∀ x ∈ l, x ∈ Y.values ∧ ∀ v, f.value? x = some v → v.op ≠ .Phi) →
      CtxAgree (Ctx.make tabs f) (Ctx.make tabs g) l := fun l hl =>
    ⟨fun x hx => by
      obtain ⟨hxY, hnp⟩ := hl x hx
      obtain ⟨hn, hval⟩ := S.rel.value (S.mem_ne hy hY hxY)
      change SemEq (f.value? x) (g.value? x)
      cases hf : f.value? x with
      | none => rw [hn hf]; trivial
      | some v =>
        obtain ⟨w, hw, hid', -, haux, hai, hop, -, -, hsame⟩ := hval v hf
        rw [hw]
        exact ⟨hid', hop, haux, hai, hsame fun h => hnp v hf h.1⟩,
     fun x hx v hv => by
      obtain ⟨hxY, -⟩ := hl x hx
      obtain ⟨vv, hvv, hvid⟩ := valuesOwn hwf hy hY x hxY
      change f.value? x = some v at hv
      rw [hv] at hvv; cases hvv
      rw [hvid]; exact S.tys_eq (S.mem_ne hy hY hxY),
     rfl, S.params_eq, rfl⟩
  have hE := enterBlock_rel (env := env) (ctxS := Ctx.make tabs f) (ctxT := Ctx.make tabs g)
    (frS := frS) (frT := frT) (bS := Y) (bT := Y') (iS := iS) (iT := iT)
    (X := Xq f st (predOf f y iS)) hid hvals
    (fun ps hps => filterMapM_phi_rel (fun z hz v hv => by
        have hzY := Array.mem_toList_iff.1 hz
        by_cases hph : v.op = .Phi
        · obtain ⟨w, hw, hop, hargs⟩ := S.phi_idx hy hY hidx hzY hv hph
          refine ⟨w, hw, hop, fun _ => ⟨hargs, fun a ha => hag a ?_⟩⟩
          have hsz' := hwf.phiArity y Y z v ⟨⟨hy, hY⟩, hzY, hv⟩ hph
          obtain ⟨e, he⟩ : ∃ e, Y.preds[iS]? = some e := by
            have := (Array.getElem?_eq_some_iff.1 ha).1
            exact ⟨_, Array.getElem?_eq_getElem (by omega)⟩
          refine fun hx => ?_
          rcases hx with hx | ⟨hbv, hnq⟩
          · exact S.listed_ne (hwf.argListed y Y z v ⟨⟨hy, hY⟩, hzY, hv⟩ a
              (Array.mem_of_getElem? ha)) hx
          · have hq : predOf f y iS = some e.b := by rw [predOf_eq hY, he]; rfl
            rcases hpt with ⟨q, hq', hqm, hqt⟩ | ⟨hq', -⟩
            · rw [hq] at hq'; cases hq'
              have := hD.phiUse hy hY ht hzY hv hph ha he hqt
              rw [S.blockOf_bval hbv] at this
              exact hnq _ hq this
            · rw [hq] at hq'; cases hq'
        · obtain ⟨-, hval⟩ := S.rel.value (S.mem_ne hy hY hzY)
          obtain ⟨w, hw, -, -, -, -, hop, -, -, -⟩ := hval v hv
          exact ⟨w, hw, hop, fun h => absurd h hph⟩)
      (fun z hz => S.tys_eq (S.mem_ne hy hY (Array.mem_toList_iff.1 hz))) hps)
    (by
      change ((Ctx.make tabs g).sched[Y.id]?).join = ((Ctx.make tabs f).sched[Y.id]?).join
      rw [hbid, sched_of_block hY', sched_of_block hY]
      unfold schedule
      rw [schedNodes_phiEq hvals fun x hx => by
        obtain ⟨hn, hval⟩ := S.rel.value (S.mem_ne hy hY hx)
        refine ⟨hn, fun v hv => ?_⟩
        obtain ⟨w, hw, hid', -, -, -, hop, -, -, hsame⟩ := hval v hv
        exact ⟨w, hw, hid', hop, fun hnp => hsame fun h => hnp h.1⟩])
    (fun o ho => by
      rw [hbid, sched_of_block hY] at ho
      obtain ⟨-, -, omem⟩ := schedule_topo (valuesOwn hwf hy hY) (hwf.valuesNodup y Y ⟨hy, hY⟩) ho
      refine ⟨hca _ fun x hx => ?_, fun x hx => ⟨?_, fun v hv a ha => ?_⟩⟩
      · obtain ⟨hxY, v, hv, hnp⟩ := (omem x).1 hx
        exact ⟨hxY, fun v' hv' => by rw [hv] at hv'; cases hv'; exact hnp⟩
      · obtain ⟨hxY, -⟩ := (omem x).1 hx
        refine hread x ⟨y, Y, ⟨hy, hY⟩, hxY⟩ fun hbv => absurd hbv (S.not_bval hy hyb hY hxY)
      · obtain ⟨hxY, v', hv', hnp⟩ := (omem x).1 hx
        change f.value? x = some v at hv
        rw [hv] at hv'; cases hv'
        refine hread a (hwf.argListed y Y x v ⟨⟨hy, hY⟩, hxY, hv⟩ a ha) fun hbv => ?_
        have := hD.uses hy hY ht hxY hv hnp ha
        rwa [S.blockOf_bval hbv] at this)
    hfr hsz hag
  refine ⟨fun G hG => ?_, hE.2⟩
  obtain ⟨GT, h1, h2, h3, h4⟩ := hE.1 G hG
  refine ⟨GT, h1, h2, h3, fun a ha => h4 a fun hx => ha ?_⟩
  rcases hx with hx | ⟨hbv, hnq⟩
  · exact .inl hx
  · refine .inr ⟨hbv, fun q hq hqa => ?_⟩
    cases hq
    obtain ⟨q', hq', hqa'⟩ := S.sdom_pred hy hpt hyb hqa
    exact hnq q' hq' hqa'

end Setup

end GoFV.Proof.FuseCmp
