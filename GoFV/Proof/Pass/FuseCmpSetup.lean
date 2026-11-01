import GoFV.Proof.Pass.FuseCmpRel
import GoFV.Proof.AgreeIdx
import GoFV.Proof.Enter
import GoFV.Proof.Mixed
import GoFV.Proof.SimIH
import GoFV.Proof.Speculate
import GoFV.Proof.Merge

/-!
# fuseComparisons: the setting of one checked rewrite

`Setup f g st`: `f` and `g` are well formed, `f`'s dominator certificate holds, and `g` is `f`
with one comparison fusion at `st` (`CRel`).

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

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.Fuse GoFV.Opt.Fuse.Cmp
  GoFV.Proof Dom

/-- See the module doc. -/
structure Setup (f g : Func) (st : Site) : Prop where
  wf : ∃ ce, WF ce f
  wg : ∃ ce, WF ce g
  cf : CertOK f
  rel : CRel f g st

/-- `a` is a value of `b`. -/
def BVal (f : Func) (st : Site) (a : ID) : Prop := a ∈ (valsOf f st.b).toList

/-- The values the registers may differ on at a block entered from `q` (see the module doc). -/
def Xq (f : Func) (st : Site) (q : Option ID) (a : ID) : Prop :=
  a = st.nv ∨ (BVal f st a ∧ ∀ q', q = some q' → ¬ Anc (make f) st.b q')

/-- The predecessor of `y` along index `i`. -/
def predOf (f : Func) (y : ID) (i : Nat) : Option ID :=
  ((f.block? y).bind (·.preds[i]?)).map (·.b)

/-- The target's edge index (see the module doc). -/
def IdxOK (st : Site) (y : ID) (iS iT : Nat) : Prop :=
  (y = st.s ∧ iS = st.jp ∧ iT = (st.remapE ⟨st.s, st.jb⟩).i) ∨
    ((y = st.s → iS ≠ st.jp) ∧ iT = (st.remapE ⟨y, iS⟩).i)

/-- The source's predecessor: a listed tree block, or none at the entry. -/
def PredT (f : Func) (y : ID) (i : Nat) : Prop :=
  (∃ q, predOf f y i = some q ∧ q ∈ f.blocks ∧ ((make f).depthOf q).isSome) ∨
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

theorem predOf_eq {f : Func} {y : ID} {Y : Block} (hY : f.block? y = some Y) {i : Nat} :
    predOf f y i = (Y.preds[i]?).map (·.b) := by
  unfold predOf; rw [hY]; rfl

variable {f g : Func} {st : Site}

namespace Setup

variable (S : Setup f g st)
include S

theorem inB : st.b ∈ f.blocks := S.rel.place.1
theorem inP : st.p ∈ f.blocks := S.rel.place.2.1

theorem not_anc_bp : ¬ Anc (make f) st.b st.p := fun h => by
  have := S.rel.place.2.2
  rw [(anc_iff S.cf.parents).2 h] at this
  cases this

theorem gsize : g.valueTab.size = f.valueTab.size := S.rel.newv.1

theorem params_eq {tabs : Tables} : (Ctx.make tabs g).params = (Ctx.make tabs f).params := by
  simp only [Ctx.make, abiParams, S.rel.parts.2.2.2.2.2.2.2.1]

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
  obtain ⟨B, -, -, -, -, hB, -, -, -, -, -, -, -, -, -, -, -, hpr, -⟩ := S.rel.shape
  rw [he] at hB
  have := hwf.entryPreds B hB
  rw [hpr] at this; cases this

/-- If `b` dominates a block other than itself, it dominates its predecessor. -/
theorem anc_pred {y : ID} (hy : y ∈ f.blocks) {i : Nat} (hp : PredT f y i) (hyb : y ≠ st.b)
    (ha : Anc (make f) st.b y) : ∃ q, predOf f y i = some q ∧ Anc (make f) st.b q := by
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
      obtain ⟨-, -, hup⟩ := edge S.cf hqm hQ hqt (Array.mem_of_getElem? hQs)
      exact Anc.trans S.cf.parents (ha.up S.cf.parents (Ne.symm hyb)) hup
  · subst hye
    exact absurd (anc_of_entry S.cf.parents ha) S.b_ne_entry

/-- The predecessors of `s` along `p`'s and `b`'s edges. -/
theorem s_preds : ∃ Sb, f.block? st.s = some Sb ∧ st.s ∈ f.blocks ∧
    Sb.preds[st.jp]? = some ⟨st.p, st.i⟩ ∧ Sb.preds[st.jb]? = some ⟨st.b, st.i⟩ ∧
    Sb.preds.size = st.n + 1 ∧ st.jp ≤ st.n ∧ st.jb ≤ st.n ∧ st.jb ≠ st.jp := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨B, P, Sb, -, -, hB, hP, hS, -, -, -, -, hpb, -, -, -, -, -, -, -, -, -, hPs, hBs, hSn,
    -⟩ := S.rel.shape
  obtain ⟨hsm, Sb', hS', hjp⟩ := hwf.succLink st.p P ⟨S.inP, hP⟩ st.i _ hPs
  rw [hS] at hS'; cases hS'
  obtain ⟨-, Sb', hS', hjb⟩ := hwf.succLink st.b B ⟨S.inB, hB⟩ st.i _ hBs
  rw [hS] at hS'; cases hS'
  have hjp' : Sb.preds[st.jp]? = some ⟨st.p, st.i⟩ := hjp
  have hjb' : Sb.preds[st.jb]? = some ⟨st.b, st.i⟩ := hjb
  have hlt1 := (Array.getElem?_eq_some_iff.1 hjp').1
  have hlt2 := (Array.getElem?_eq_some_iff.1 hjb').1
  refine ⟨Sb, hS, hsm, hjp', hjb', hSn, by omega, by omega, fun he => ?_⟩
  rw [he, hjp'] at hjb'
  exact hpb (Edge.mk.inj (Option.some.inj hjb')).1

/-- **The `Phi` arguments along the target's edge** are the source's. -/
theorem phi_idx {y : ID} (hy : y ∈ f.blocks) {Y : Block} (hY : f.block? y = some Y)
    {iS iT : Nat} (hidx : IdxOK st y iS iT) {x : ID} (hx : x ∈ Y.values) {v : Value}
    (hv : f.value? x = some v) (hph : v.op = .Phi) :
    ∃ w, g.value? x = some w ∧ w.op = v.op ∧ w.args[iT]? = v.args[iS]? := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨-, hval⟩ := S.rel.value (S.mem_ne hy hY hx)
  obtain ⟨w, hw, -, -, -, -, hop, hsw, hsame⟩ := hval v hv
  refine ⟨w, hw, hop, ?_⟩
  obtain ⟨Sb, hS, hsm, -, -, hSn, hjp, -, hjb⟩ := S.s_preds
  by_cases hys : y = st.s
  · rw [hys] at hY
    rw [hS] at hY; cases hY
    have hxs : x ∈ (valsOf f st.s).toList := FusePlain.valsOf_mem.2 ⟨Y, hS, hx⟩
    obtain ⟨hargs, hagree⟩ := hsw hph hxs
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
  · have hxs : ¬ (v.op = .Phi ∧ x ∈ (valsOf f st.s).toList) := fun hh => by
      have h := hh.2
      obtain ⟨Y', hY', hxY'⟩ := FusePlain.valsOf_mem.1 h
      exact hys (hwf.valueOnce y Y st.s Y' ⟨hy, hY⟩ ⟨hsm, hY'⟩ x hx hxY')
    rw [hsame hxs]
    rcases hidx with ⟨h, -, -⟩ | ⟨-, hiT⟩
    · exact absurd h hys
    · rw [hiT, remapE_i]; simp [hys]

/-- **Entering a block other than `b`** (see the module doc). -/
theorem enter_rel {env : Env} {tabs : Tables} {y : ID} (hy : y ∈ f.blocks) (hyb : y ≠ st.b)
    {iS iT : Nat} (hidx : IdxOK st y iS iT) (hpt : PredT f y iS) {Y Y' : Block}
    (hY : f.block? y = some Y) (hY' : g.block? y = some Y') (hid : Y'.id = Y.id)
    (hvals : Y'.values = Y.values) (ht : ((make f).depthOf y).isSome) {frS frT : Frame}
    (hfr : frT = { frS with regs := frT.regs }) (hsz : frT.regs.size = frS.regs.size)
    (hag : ∀ a, ¬ Xq f st (predOf f y iS) a → frT.regs[a]? = frS.regs[a]?) :
    (∀ G, enterBlock env (Ctx.make tabs f) frS Y iS = .ok G →
      ∃ GT, enterBlock env (Ctx.make tabs g) frT Y' iT = .ok GT ∧
        GT = { G with regs := GT.regs } ∧ GT.regs.size = G.regs.size ∧
        ∀ a, ¬ Xq f st (some y) a → GT.regs[a]? = G.regs[a]?) ∧
    (∀ e m, enterBlock env (Ctx.make tabs f) frS Y iS = .panic e m →
      enterBlock env (Ctx.make tabs g) frT Y' iT = .panic e m) := by
  obtain ⟨ce, hwf⟩ := S.wf
  have hc := S.cf
  obtain ⟨b', hb', hbid⟩ := hwf.blockId y hy
  rw [hY] at hb'; cases hb'
  -- a read of a value of `b` in `y` (or along its incoming edge) is no difference
  have hread : ∀ a, Listed f a → (BVal f st a → Anc (make f) st.b y) →
      ¬ Xq f st (predOf f y iS) a := by
    intro a hl hba hx
    rcases hx with hx | ⟨hbv, hnq⟩
    · exact S.listed_ne hl hx
    · obtain ⟨q, hq, hqa⟩ := S.anc_pred hy hpt hyb (hba hbv)
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
        obtain ⟨w, hw, hid', -, haux, hai, hop, -, hsame⟩ := hval v hf
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
              have := phiUse hc hy hY ht hzY hv hph ha he hqt
              rw [S.blockOf_bval hbv] at this
              exact hnq _ hq this
            · rw [hq] at hq'; cases hq'
        · obtain ⟨-, hval⟩ := S.rel.value (S.mem_ne hy hY hzY)
          obtain ⟨w, hw, -, -, -, -, hop, -, -⟩ := hval v hv
          exact ⟨w, hw, hop, fun h => absurd h hph⟩)
      (fun z hz => S.tys_eq (S.mem_ne hy hY (Array.mem_toList_iff.1 hz))) hps)
    (by
      change ((Ctx.make tabs g).sched[Y.id]?).join = ((Ctx.make tabs f).sched[Y.id]?).join
      rw [hbid, sched_of_block hY', sched_of_block hY]
      unfold schedule
      rw [schedNodes_phiEq hvals fun x hx => by
        obtain ⟨hn, hval⟩ := S.rel.value (S.mem_ne hy hY hx)
        refine ⟨hn, fun v hv => ?_⟩
        obtain ⟨w, hw, hid', -, -, -, hop, -, hsame⟩ := hval v hv
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
        have := uses hc hy hY ht hxY hv hnp ha
        rwa [S.blockOf_bval hbv] at this)
    hfr hsz hag
  refine ⟨fun G hG => ?_, hE.2⟩
  obtain ⟨GT, h1, h2, h3, h4⟩ := hE.1 G hG
  refine ⟨GT, h1, h2, h3, fun a ha => h4 a fun hx => ha ?_⟩
  rcases hx with hx | ⟨hbv, hnq⟩
  · exact .inl hx
  · refine .inr ⟨hbv, fun q hq hqa => ?_⟩
    cases hq
    obtain ⟨q', hq', hqa'⟩ := S.anc_pred hy hpt hyb hqa
    exact hnq q' hq' hqa'

end Setup

end GoFV.Proof.FuseCmp
