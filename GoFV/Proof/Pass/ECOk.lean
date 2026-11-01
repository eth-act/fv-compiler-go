import GoFV.Proof.Pass.ECEnter
import GoFV.Proof.AtomSimBlock

/-!
# A block entry the source completes (issue #28)

`tgt_phis`: the target's `Phi`s (those of the source) read refined arguments. `enter_ok`: the
target's block entry completes too (`tgt_loop` against the source's final frame), and its
registers refine the conversions of the source's; afterwards the entry block has run
(`EntryOK`) and the source's registers are `RegsOK` (`regsOK_block`).
-/

namespace GoFV.Proof.EC

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Proof.AtomSim GoFV.Proof.Order

section
variable {tabs : Tables} {f g : Func} {cv : Cv} {isNew : ID → Bool} {front : ID → List ID}
  {RR : List Val → Mem → List Val → Mem → Prop} {ce ce' : CheckEnv}

/-- **The target's `Phi`s**, each refining the source's. -/
theorem tgt_phis (H : Hyp tabs f g cv isNew front RR ce ce') {env : Env} {frS frT : Frame}
    {b : ID} {i : Nat} (hA : SimAt env tabs f g cv isNew frS frT b i) {fb gb : Block}
    (hbm : b ∈ f.blocks) (hfb : f.block? b = some fb) (hgb : g.block? b = some gb)
    (B : CvBlock tabs f g cv isNew front RR fb gb) {ps : List (ID × Val)}
    (hps : fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) frS i) = .ok ps) :
    ∃ psT, gb.values.toList.filterMapM (phiStep (Ctx.make tabs g) frT i) = .ok psT ∧
      ∀ z ∈ gb.values, ∀ w, g.value? z = some w → w.op = .Phi →
        ∃ y y', (setPhis ps frS.regs)[z]? = some (some y) ∧
          (setPhis psT frT.regs)[z]? = some (some y') ∧ Sem.Refines y y' := by
  have hbm' : b ∈ g.blocks := H.blocks_eq ▸ hbm
  obtain ⟨-, -, -, hphS⟩ := phis_spec (H.wf.valuesNodup b fb ⟨hbm, hfb⟩) hps
  -- each `Phi` of `g`: its argument and the refinement
  have key : ∀ z ∈ gb.values, ∀ w, g.value? z = some w → w.op = .Phi →
      ∃ a y y', w.args[i]? = some a ∧ frT.regs[a]? = some (some y') ∧
        (setPhis ps frS.regs)[z]? = some (some (y.retype (tabs.ty w.type))) ∧ Sem.Refines y y' := by
    intro z hz w hw hph
    obtain ⟨hzf, u, hfu, hsw⟩ := B.phiT z hz w hw hph
    have huph : u.op = .Phi := hsw.1.symm.trans hph
    obtain ⟨-, -, hcva⟩ := B.phiS z hzf u hfu huph
    obtain ⟨a, y, ha, hy, hset⟩ := hphS z hzf u hfu huph (by rw [hA.szS]; exact lt_of_value? hfu)
    obtain ⟨y', hy', hyy⟩ := hA.rel a y hy
    rw [hcva a (Array.mem_of_getElem? ha) y] at hyy
    refine ⟨a, y, y', by rw [hsw.2.1]; exact ha, hy', ?_, hyy⟩
    rw [hset, tys_of_value hfu, hsw.2.2]; rfl
  obtain ⟨psT, hpsT⟩ := filterMapM_phi_ok (ctx := Ctx.make tabs g) (fr := frT) (i := i)
    (l := gb.values.toList) fun z hz => by
      have hz' := Array.mem_toList_iff.1 hz
      obtain ⟨w, hw, -, -⟩ := H.wg.valueId b gb ⟨hbm', hgb⟩ z hz'
      by_cases hph : w.op = .Phi
      · obtain ⟨a, -, y', ha, hy', -, -⟩ := key z hz' w hw hph
        exact ⟨_, phiStep_phi hw hph ha hy'⟩
      · exact ⟨_, phiStep_nonphi hw hph⟩
  refine ⟨psT, hpsT, fun z hz w hw hph => ?_⟩
  obtain ⟨a, y, y', ha, hy', hS, hyy⟩ := key z hz w hw hph
  obtain ⟨-, -, -, hphT⟩ := phis_spec (H.wg.valuesNodup b gb ⟨hbm', hgb⟩) hpsT
  obtain ⟨a', y'', ha', hy'', hset⟩ := hphT z hz w hw hph (by rw [hA.szT]; exact lt_of_value? hw)
  rw [ha] at ha'; cases ha'
  rw [hy'] at hy''; cases hy''
  refine ⟨_, _, hS, hset, ?_⟩
  rw [tys_of_value hw]
  exact retype_mono _ hyy

/-- `EntryOK` survives a block entry that does not set entry values. -/
theorem EntryOK.keep (H : Hyp tabs f g cv isNew front RR ce ce') {env : Env} {T T' : Frame}
    (h : EntryOK env tabs g isNew T) (hT' : T' = { T with regs := T'.regs })
    (hk : ∀ z, EntryVal g z → T'.regs[z]? = T.regs[z]?) : EntryOK env tabs g isNew T' := by
  obtain ⟨hreg, hN⟩ := h
  refine ⟨fun z hz => by rw [Reg, hk z hz]; exact hreg z hz, fun z hz => ?_⟩
  obtain ⟨hn, w, y, hw, hcl, hy, hev⟩ := hN z hz
  refine ⟨hn, w, y, hw, hcl, by rw [hk z hz.1]; exact hy, ?_⟩
  rw [← hev]
  exact evalValue_congr (fr := T') (g := T) (by rw [hT']) fun a ha =>
    hk a (H.entry_args hz.1 hw a ha)

/-- Frames with the same activation inputs differ in their registers only. -/
theorem frame_regs {a b : Frame} (h1 : a.args = b.args) (h2 : a.mem0 = b.mem0)
    (h3 : a.images = b.images) (h4 : a.closure = b.closure) : a = { b with regs := a.regs } := by
  cases a; cases b; simp_all

/-- A value listed in `f` is not new. -/
theorem Hyp.notNew (H : Hyp tabs f g cv isNew front RR ce ce') {x : ID} (h : Listed f x) :
    isNew x = false := by
  obtain ⟨c, fc, ⟨hcm, hfc⟩, hx⟩ := h
  obtain ⟨gc, -, B⟩ := H.block hcm hfc
  exact (B.common x hx).2

/-- An entry value is not listed in another block. -/
theorem Hyp.entry_not_mem (H : Hyp tabs f g cv isNew front RR ce ce') {z b : ID} {gb : Block}
    (hz : EntryVal g z) (hbm : b ∈ g.blocks) (hgb : g.block? b = some gb) (hb : b ≠ f.entry) :
    z ∉ gb.values := fun hm => by
  obtain ⟨eb, heb, hze⟩ := hz
  have := H.wg.valueOnce _ _ _ _ ⟨H.wg.entry, heb⟩ ⟨hbm, hgb⟩ z hze hm
  exact hb (by rw [← this, H.entry_eq])

/-- The source's frame after its `Phi`s and a part `L` of its schedule is `RegsOK`. -/
theorem regsOK_block (H : Hyp tabs f g cv isNew front RR ce ce') {env : Env} {frS : Frame}
    {b : ID} {i : Nat} {fb : Block} (hbm : b ∈ f.blocks) (hfb : f.block? b = some fb)
    {ps : List (ID × Val)}
    (hps : fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) frS i) = .ok ps)
    (hok : RegsOK (Ctx.make tabs f) frS) {L : List ID} (hL : ∀ x ∈ L, x ∈ fb.values) {G : Frame}
    (hev : evalAll env (Ctx.make tabs f) { frS with regs := setPhis ps frS.regs } L = .ok G) :
    RegsOK (Ctx.make tabs f) G :=
  regsOK_evalAll (fun x hx v hv => by
      obtain ⟨u, hu, hid, -⟩ := H.wf.valueId b fb ⟨hbm, hfb⟩ x (hL x hx)
      have hv' : f.value? x = some v := hv
      rw [hu] at hv'; cases hv'; exact hid)
    (regsOK_phis hps hok) hev

/-- **The target's block against a source reference frame `G`** (the source's frame after its
`Phi`s, `PS`, with the source's schedule `oS` evaluated in part or in full): the hypotheses of
`tgt_loop`/`tgt_next` for the target's frame after its `Phi`s, the new entry values (once the
entry has run) as the initial new-value set. -/
theorem tgtHyp_of (H : Hyp tabs f g cv isNew front RR ce ce') {env : Env} {frS frT : Frame}
    {b : ID} {i : Nat} (hA : SimAt env tabs f g cv isNew frS frT b i) (hbm : b ∈ f.blocks)
    {fb gb : Block} (hfb : f.block? b = some fb) (hgb : g.block? b = some gb)
    (B : CvBlock tabs f g cv isNew front RR fb gb) {ps : List (ID × Val)}
    (hps : fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) frS i) = .ok ps)
    {oS og : Array ID} (hsf : schedule f fb = some oS) (hsg : schedule g gb = some og)
    {psT : List (ID × Val)}
    (hpsT : gb.values.toList.filterMapM (phiStep (Ctx.make tabs g) frT i) = .ok psT)
    (hphiT : ∀ z ∈ gb.values, ∀ w, g.value? z = some w → w.op = .Phi →
      ∃ y y', (setPhis ps frS.regs)[z]? = some (some y) ∧
        (setPhis psT frT.regs)[z]? = some (some y') ∧ Sem.Refines y y')
    {G : Frame} (hG : G = { frS with regs := G.regs })
    (hGk : ∀ a, a ∉ oS.toList → G.regs[a]? = (setPhis ps frS.regs)[a]?)
    (hGok : RegsOK (Ctx.make tabs f) G) :
    TgtHyp env tabs f g cv isNew front RR fb gb og G { frT with regs := setPhis psT frT.regs }
      (fun z => EntryVal g z ∧ isNew z = true ∧ b ≠ f.entry) := by
  have hbm' : b ∈ g.blocks := H.blocks_eq ▸ hbm
  have hndF := H.wf.valuesNodup b fb ⟨hbm, hfb⟩
  have hndG := H.wg.valuesNodup b gb ⟨hbm', hgb⟩
  obtain ⟨-, -, ofm⟩ := schedule_topo (valuesOwn H.wf hbm hfb) hndF hsf
  obtain ⟨ogn, ogt, ogm⟩ := schedule_topo (valuesOwn H.wg hbm' hgb) hndG hsg
  obtain ⟨-, -, pS3, -⟩ := phis_spec hndF hps
  obtain ⟨pT1, -, pT3, pT4⟩ := phis_spec hndG hpsT
  have hogb : ∀ x ∈ og.toList, x ∈ gb.values := fun x hx => ((ogm x).1 hx).1
  have hphi_of : ∀ a ∈ gb.values, a ∉ og.toList → ∃ w, g.value? a = some w ∧ w.op = .Phi :=
    fun a ha hm => by
      obtain ⟨w, hw, -, -⟩ := H.wg.valueId b gb ⟨hbm', hgb⟩ a ha
      exact ⟨w, hw, Classical.byContradiction fun hph => hm ((ogm a).2 ⟨ha, w, hw, hph⟩)⟩
  have hE0gb : ∀ z, (EntryVal g z ∧ isNew z = true ∧ b ≠ f.entry) → z ∉ gb.values :=
    fun z hz => H.entry_not_mem hz.1 hbm' hgb hz.2.2
  have hnotNewPhi : ∀ a ∈ gb.values, a ∉ og.toList → isNew a = true → False :=
    fun a ha hm han => by
      obtain ⟨w, hw, hph⟩ := hphi_of a ha hm
      exact (B.newOK a ha han w hw).1 hph
  refine ⟨B, hsg, ogn, ogt, ogm, fun x hx w hw => ?_, ?_, by simp [pT1, hA.szT], hA.img,
    ?_, fun z hz hm => hE0gb z hz (hogb z hm), fun z hz w hw a ha hm =>
      H.entry_not_mem (H.entry_args hz.1 hw a ha) hbm' hgb hz.2.2 (hogb a hm), ?_, ?_, ?_, hGok⟩
  · obtain ⟨w', hw', hid, -⟩ := H.wg.valueId b gb ⟨hbm', hgb⟩ x hx
    rw [hw] at hw'; cases hw'; exact hid
  · rw [hG]; conv => lhs; rw [hA.frame]
  · intro z ⟨hz, hn, hb⟩
    obtain ⟨-, hN⟩ := EntryOK.keep H (hA.entry.resolve_left hb)
      (T' := { frT with regs := setPhis psT frT.regs }) rfl
      (fun z hz => pT3 z (.inl (H.entry_not_mem hz hbm' hgb hb)))
    obtain ⟨-, w, y, hw, hcl, hy, hev⟩ := hN z ⟨hz, hn⟩
    exact ⟨hn, w, y, hw, fun a ha han => ⟨(hcl a ha han).1, han, hb⟩, hy, hev⟩
  · intro x hx w hw a ha han hm
    rcases B.newArgs x (hogb x hx) w hw a ha han with h | h
    · exact (hnotNewPhi a h hm han).elim
    · refine ⟨h, han, fun hb => ?_⟩
      obtain ⟨eb, heb, hae⟩ := h
      rw [H.entry_eq, ← hb, hgb] at heb; cases heb
      exact hnotNewPhi a hae hm han
  · intro x hx w hw a ha hm
    obtain ⟨-, w', hw', hph⟩ := (ogm x).1 hx
    rw [hw] at hw'; cases hw'
    by_cases hag : a ∈ gb.values
    · obtain ⟨wa, hwa, hpha⟩ := hphi_of a hag hm
      obtain ⟨-, y, -, -, hset⟩ := pT4 a hag wa hwa hpha (by rw [hA.szT]; exact lt_of_value? hwa)
      exact ⟨_, hset⟩
    · obtain ⟨y, hy⟩ := out_arg_reg H hA hfb hgb B (hogb x hx) hw hph ha hag
      exact ⟨y, by show (setPhis psT frT.regs)[a]? = _; rw [pT3 a (.inl hag)]; exact hy⟩
  · intro a hm han y hy
    by_cases hag : a ∈ gb.values
    · obtain ⟨w, hw, hph⟩ := hphi_of a hag hm
      obtain ⟨haf, u, hfu, hsw⟩ := B.phiT a hag w hw hph
      have huph : u.op = .Phi := hsw.1.symm.trans hph
      obtain ⟨-, hcv, -⟩ := B.phiS a haf u hfu huph
      have hao : a ∉ oS.toList := fun h => by
        obtain ⟨-, u', hu', hne⟩ := (ofm a).1 h
        rw [hfu] at hu'; cases hu'; exact hne huph
      obtain ⟨y0, y0', hy0, hy0', hyy⟩ := hphiT a hag w hw hph
      rw [hGk a hao, hy0] at hy; cases hy
      exact ⟨y0', hy0', by rw [hcv]; exact hyy⟩
    · have haf : a ∉ fb.values := fun h => hag (B.common a h).1
      have hao : a ∉ oS.toList := fun h => haf ((ofm a).1 h).1
      rw [hGk a hao, pS3 a (.inl haf)] at hy
      obtain ⟨y', hy', hyy⟩ := hA.rel a y hy
      exact ⟨y', by show (setPhis psT frT.regs)[a]? = _; rw [pT3 a (.inl hag)]; exact hy', hyy⟩

/-- The parts of a block entry the source does not get stuck in: its `Phi`s and schedule, the
target's block, schedule and `Phi`s. -/
theorem block_parts (H : Hyp tabs f g cv isNew front RR ce ce') {env : Env} {frS frT : Frame}
    {b : ID} {i : Nat} (hA : SimAt env tabs f g cv isNew frS frT b i) {fb : Block}
    (hfb : f.block? b = some fb) {r : Res Frame}
    (hen : enterBlock env (Ctx.make tabs f) frS fb i = r) (hr : ∀ msg, r ≠ .stuck msg) :
    ∃ gb ps oS og psT, g.block? b = some gb ∧ CvBlock tabs f g cv isNew front RR fb gb ∧
      b ∈ f.blocks ∧ ((make f).depthOf b).isSome ∧
      fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) frS i) = .ok ps ∧
      schedule f fb = some oS ∧ schedule g gb = some og ∧
      evalAll env (Ctx.make tabs f) { frS with regs := setPhis ps frS.regs } oS.toList = r ∧
      gb.values.toList.filterMapM (phiStep (Ctx.make tabs g) frT i) = .ok psT ∧
      (∀ z ∈ gb.values, ∀ w, g.value? z = some w → w.op = .Phi →
        ∃ y y', (setPhis ps frS.regs)[z]? = some (some y) ∧
          (setPhis psT frT.regs)[z]? = some (some y') ∧ Sem.Refines y y') ∧
      enterBlock env (Ctx.make tabs g) frT gb i =
        evalAll env (Ctx.make tabs g) { frT with regs := setPhis psT frT.regs } og.toList := by
  have hbt := CSE.pre_tree H.wf H.cf hA.pre
  have hbm' : b ∈ g.blocks := H.blocks_eq ▸ hbt.1
  obtain ⟨gb, hgb, B⟩ := H.block hbt.1 hfb
  obtain ⟨fb', hfb', hfid⟩ := H.wf.blockId b hbt.1
  rw [hfb] at hfb'; cases hfb'
  obtain ⟨gb', hgb', hgid⟩ := H.wg.blockId b hbm'
  rw [hgb] at hgb'; cases hgb'
  obtain ⟨ps, oS, hps, hoS, hev⟩ := CSE.enterBlock_split hen hr
  rw [hfid, sched_of_block hfb] at hoS
  obtain ⟨oF, og, hsf, hsg, -⟩ := B.sched
  rw [hsf] at hoS; cases hoS
  obtain ⟨psT, hpsT, hphiT⟩ := tgt_phis H hA hbt.1 hfb hgb B hps
  exact ⟨gb, ps, oS, og, psT, hgb, B, hbt.1, hbt.2, hps, hsf, hsg, hev, hpsT, hphiT,
    CSE.enterBlock_of_parts hpsT (by rw [hgid, sched_of_block hgb, hsg])⟩

/-- **A block the source enters successfully is entered by the target.** -/
theorem enter_ok (H : Hyp tabs f g cv isNew front RR ce ce') {env : Env} (hE : env.Mono)
    {frS frT : Frame} {b : ID} {i : Nat} (hA : SimAt env tabs f g cv isNew frS frT b i)
    {fb : Block} (hfb : f.block? b = some fb) {GS : Frame}
    (hen : enterBlock env (Ctx.make tabs f) frS fb i = .ok GS) :
    ∃ gb GT, g.block? b = some gb ∧ CvBlock tabs f g cv isNew front RR fb gb ∧
      enterBlock env (Ctx.make tabs g) frT gb i = .ok GT ∧
      GT = { GS with regs := GT.regs } ∧ GT.regs.size = g.valueTab.size ∧
      GS.regs.size = f.valueTab.size ∧
      (∀ x y, GS.regs[x]? = some (some y) →
        ∃ y', GT.regs[x]? = some (some y') ∧ Sem.Refines (cv x y) y') ∧
      (∀ x y, GS.regs[x]? = some (some y) → Listed f x) ∧
      EntryOK env tabs g isNew GT ∧ RegsOK (Ctx.make tabs f) GS := by
  obtain ⟨gb, ps, oS, og, psT, hgb, B, hbm, -, hps, hsf, hsg, hev, hpsT, hphiT, hentT⟩ :=
    block_parts H hA hfb hen (fun _ h => nomatch h)
  have hbm' : b ∈ g.blocks := H.blocks_eq ▸ hbm
  have hndF := H.wf.valuesNodup b fb ⟨hbm, hfb⟩
  have hndG := H.wg.valuesNodup b gb ⟨hbm', hgb⟩
  obtain ⟨ofn, oft, ofm⟩ := schedule_topo (valuesOwn H.wf hbm hfb) hndF hsf
  obtain ⟨-, -, ogm⟩ := schedule_topo (valuesOwn H.wg hbm' hgb) hndG hsg
  obtain ⟨pS1, -, pS3, -⟩ := phis_spec hndF hps
  obtain ⟨pT1, -, pT3, pT4⟩ := phis_spec hndG hpsT
  obtain ⟨e1, e2, e3, e4⟩ := evalAll_spec ofn oft (by rw [pS1, hA.szS]; rfl) hev
  have hGSok : RegsOK (Ctx.make tabs f) GS :=
    regsOK_block H hbm hfb hps hA.ok (fun x hx => ((ofm x).1 hx).1) hev
  have TH := tgtHyp_of H hA hbm hfb hgb B hps hsf hsg hpsT hphiT (G := GS)
    (by rw [e1]) e3 hGSok
  have hogb : ∀ x ∈ og.toList, x ∈ gb.values := fun x hx => ((ogm x).1 hx).1
  have hphi_of : ∀ a ∈ gb.values, a ∉ og.toList → ∃ w, g.value? a = some w ∧ w.op = .Phi :=
    fun a ha hm => by
      obtain ⟨w, hw, -, -⟩ := H.wg.valueId b gb ⟨hbm', hgb⟩ a ha
      exact ⟨w, hw, Classical.byContradiction fun hph => hm ((ogm a).2 ⟨ha, w, hw, hph⟩)⟩
  have hnotNewPhi : ∀ a ∈ gb.values, a ∉ og.toList → isNew a = true → False :=
    fun a ha hm han => by
      obtain ⟨w, hw, hph⟩ := hphi_of a ha hm
      exact (B.newOK a ha han w hw).1 hph
  have hlisted : ∀ x y, GS.regs[x]? = some (some y) → Listed f x := by
    intro x y hy
    by_cases hxo : x ∈ oS.toList
    · exact ⟨b, fb, ⟨hbm, hfb⟩, ((ofm x).1 hxo).1⟩
    · rw [e3 x hxo] at hy
      by_cases hxf : x ∈ fb.values
      · exact ⟨b, fb, ⟨hbm, hfb⟩, hxf⟩
      · rw [pS3 x (.inl hxf)] at hy; exact hA.listed x y hy
  obtain ⟨T, hT, hTf, hTs, hTk, hTr, hTN, hTreg, -⟩ := tgt_loop hE TH (L := og.toList) (M := [])
    (by simp) (fun x hx hn => by
      obtain ⟨hxg, w, hw, hph⟩ := (ogm x).1 hx
      have hxf : x ∈ fb.values := Classical.byContradiction fun h => by
        rw [B.fresh x hxg h] at hn; cases hn
      obtain ⟨u, hu, -, -⟩ := H.wf.valueId b fb ⟨hbm, hfb⟩ x hxf
      have huphi : u.op ≠ .Phi := fun hp => by
        obtain ⟨⟨w', hgu, hsw⟩, -⟩ := B.phiS x hxf u hu hp
        rw [hw] at hgu; cases hgu; exact hph (hsw.1.trans hp)
      exact e4 x ((ofm x).2 ⟨hxf, u, hu, huphi⟩))
  have hGT : T = { GS with regs := T.regs } := by rw [TH.hT0] at hTf; exact hTf
  refine ⟨gb, T, hgb, B, by rw [hentT, hT], hGT, by rw [hTs]; simp [pT1, hA.szT],
    by rw [e2, pS1, hA.szS],
    fun x y hy => ?_, hlisted, ?_, hGSok⟩
  · have hn := H.notNew (hlisted x y hy)
    by_cases hxo : x ∈ og.toList
    · exact hTr x hxo hn y hy
    · rw [hTk x hxo]; exact TH.hrel0 x hxo hn y hy
  · by_cases hb : b = f.entry
    · have hge : g.entry = b := by rw [H.entry_eq, hb]
      have hent : ∀ z, EntryVal g z ↔ z ∈ gb.values := fun z => by
        constructor
        · rintro ⟨eb, heb, hz⟩; rw [hge, hgb] at heb; cases heb; exact hz
        · intro hz; exact ⟨gb, by rw [hge]; exact hgb, hz⟩
      refine ⟨fun z hz => ?_, ?_⟩
      · have hzg := (hent z).1 hz
        by_cases hzo : z ∈ og.toList
        · exact hTreg z hzo
        · obtain ⟨wz, hwz, hph⟩ := hphi_of z hzg hzo
          obtain ⟨-, y, -, -, hset⟩ := pT4 z hzg wz hwz hph (by rw [hA.szT]; exact lt_of_value? hwz)
          exact ⟨_, by rw [hTk z hzo]; exact hset⟩
      · refine hTN.mono (fun z hz => ?_) fun z hz w hw a ha han =>
          ⟨H.entry_args hz.1 hw a ha, han⟩
        exact .inl ⟨Classical.byContradiction fun hzo => hnotNewPhi z ((hent z).1 hz.1) hzo hz.2,
          hz.2⟩
    · exact EntryOK.keep H (EntryOK.keep H (hA.entry.resolve_left hb)
        (T' := { frT with regs := setPhis psT frT.regs }) rfl
        (fun z hz => pT3 z (.inl (H.entry_not_mem hz hbm' hgb hb)))) hTf
        (fun z hz => hTk z fun hm => H.entry_not_mem hz hbm' hgb hb (hogb z hm))

end

end GoFV.Proof.EC
