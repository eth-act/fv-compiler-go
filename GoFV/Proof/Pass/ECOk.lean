import GoFV.Proof.Pass.ECEnter
import GoFV.Proof.AtomSimBlock

/-!
# A block entry the source completes (issue #28)

`tgt_phis`: the target's `Phi`s (those of the source) read refined arguments. `tgtHyp_of`: the
hypotheses of the target's schedule loop, with the new values placed in strict dominators
(lemma (D) on the target, `SimAt.dinvT`) holding their evaluations. `enter_ok`: the target's
block entry completes too (`tgt_loop` against the source's final frame), and its registers
refine the conversions of the source's; the source's registers are `RegsOK` (`regsOK_block`).
-/

namespace GoFV.Proof.EC

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Proof.AtomSim GoFV.Proof.Order

section
variable {tabs : Tables} {f g : Func} {cv : Cv} {isNew : ID → Bool} {front : ID → List ID}
  {RR : List Val → Mem → List Val → Mem → Prop} {ce ce' : CheckEnv}

/-- **The target's `Phi`s**, each refining the source's. -/
theorem tgt_phis (H : Hyp tabs f g cv isNew front RR ce ce') {env : Env} {frS frT : Frame}
    {b : ID} {i : Nat} (hA : SimAt env tabs f g cv frS frT b i) {fb gb : Block}
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

/-- Lemma (D) for the strict dominators of block `b` survives any change of the registers of
`b`'s values (their arguments are placed in dominators of their blocks). -/
theorem ec_dinv_keep {ce : CheckEnv} {f : Func} {env : Env} (hwf : WF ce f) (hc : CertOK f)
    {b : ID} {blk : Block} (hb : b ∈ f.blocks) (hbb : f.block? b = some blk) {fr fr' : Frame}
    (hup : DInv env (Ctx.make tabs f) (fun a => Anc (make f) a b ∧ a ≠ b) fr)
    (hfr' : fr' = { fr with regs := fr'.regs })
    (hout : ∀ z, z ∉ blk.values → fr'.regs[z]? = fr.regs[z]?) :
    DInv env (Ctx.make tabs f) (fun a => Anc (make f) a b ∧ a ≠ b) fr' := by
  intro x v hx ⟨hanc, hxb⟩
  change Placed f x v at hx
  obtain ⟨hv, hvb, blk', hblk', hxv⟩ := hx
  obtain ⟨y, hy, hevy⟩ := hup x v ⟨hv, hvb, blk', hblk', hxv⟩ ⟨hanc, hxb⟩
  have hxn : x ∉ blk.values := fun hm => by
    obtain ⟨v', hv', -, hvb'⟩ := hwf.valueId b blk ⟨hb, hbb⟩ x hm
    rw [hv] at hv'; cases hv'; exact hxb hvb'
  refine ⟨y, by rw [hout x hxn, hy], fun hne => ?_⟩
  have hna : ∀ a ∈ v.args, a ∉ blk.values := fun a ha hm => by
    have hua := hc.domRel.uses hvb hblk' (hc.domRel.left hanc) hxv hv hne ha
    obtain ⟨va, hva, -, hvab⟩ := hwf.valueId b blk ⟨hb, hbb⟩ a hm
    have hba : blockOf f a = b := by unfold blockOf; rw [hva]; exact hvab
    rw [hba] at hua
    exact hxb (hc.domRel.antisymm hanc hua)
  rw [← hevy hne]
  exact (evalValue_congr hfr' fun a ha => (hout a (hna a ha)).symm).symm

/-- A new value of `g` is not a `Phi`. -/
theorem Hyp.new_nonPhi (H : Hyp tabs f g cv isNew front RR ce ce') {a : ID} {va : Value}
    (hP : Placed g a va) (han : isNew a = true) : va.op ≠ .Phi := by
  obtain ⟨hva, hvb, gc, hgc, hac⟩ := hP
  have hvb' : va.block ∈ f.blocks := H.blocks_eq ▸ hvb
  obtain ⟨fc, hfc, -⟩ := H.wf.blockId _ hvb'
  obtain ⟨gc', hgc', B⟩ := H.block hvb' hfc
  rw [hgc] at hgc'; cases hgc'
  exact (B.newOK a hac han va hva).1

/-- A non-`Phi` value placed in an ancestor of a strict dominator `c` of `gb` is placed in a
strict dominator of `gb`. -/
theorem Hyp.sdom_of_anc (H : Hyp tabs f g cv isNew front RR ce ce') {gb : Block} {a c : ID}
    {va : Value} (hP : Placed g a va) (hph : va.op ≠ .Phi) (h1 : Anc (make g) va.block c)
    (h2 : Anc (make g) c gb.id) (hc : c ≠ gb.id) : SDomPlaced g gb a :=
  ⟨va, hP, hph, Anc.trans H.cg.parents h1 h2,
    fun he => hc (H.cg.domRel.antisymm h2 (he ▸ h1))⟩

/-- A new value of the entry block is placed in a strict dominator of any other tree block. -/
theorem Hyp.sdom_of_entryVal (H : Hyp tabs f g cv isNew front RR ce ce') {gb : Block}
    (hgt : ((make g).depthOf gb.id).isSome) (hne : g.entry ≠ gb.id) {a : ID} (hE : EntryVal g a)
    (han : isNew a = true) : SDomPlaced g gb a := by
  obtain ⟨eb, heb, hae⟩ := hE
  obtain ⟨va, hP, hvb, -⟩ := placed_of_mem H.wg H.wg.entry heb hae
  refine ⟨va, hP, H.new_nonPhi hP han, ?_, ?_⟩
  · rw [hvb]; exact anc_entry H.cg.parents hgt
  · rw [hvb]; exact hne

/-- The new arguments of a new value placed in a strict dominator of `gb` are placed in strict
dominators of `gb` (`CvBlock.newArgs` of its block). -/
theorem Hyp.newArg_sdom (H : Hyp tabs f g cv isNew front RR ce ce') {gb : Block} {z : ID}
    (hz : SDomPlaced g gb z) {w : Value} (hw : g.value? z = some w) {a : ID} (ha : a ∈ w.args)
    (han : isNew a = true) : SDomPlaced g gb a := by
  obtain ⟨v, hP, -, hanc, hne⟩ := hz
  have ha' : a ∈ v.args := by rw [hP.1] at hw; cases hw; exact ha
  obtain ⟨hv, hvb, gc, hgc, hzc⟩ := hP
  have hvb' : v.block ∈ f.blocks := H.blocks_eq ▸ hvb
  obtain ⟨fc, hfc, -⟩ := H.wf.blockId _ hvb'
  obtain ⟨gc', hgc', B⟩ := H.block hvb' hfc
  rw [hgc] at hgc'; cases hgc'
  obtain ⟨gc'', hgc'', hgid⟩ := H.wg.blockId _ hvb
  rw [hgc] at hgc''; cases hgc''
  rcases B.newArgs z hzc v hv a ha' han with h | h | h
  · obtain ⟨va, hPa, hvab, -⟩ := placed_of_mem H.wg hvb hgc h
    exact H.sdom_of_anc hPa (H.new_nonPhi hPa han)
      (by rw [hvab]; exact anc_refl (H.cg.domRel.left hanc)) hanc hne
  · refine H.sdom_of_entryVal (H.cg.domRel.right hanc) (fun he => hne ?_) h han
    rw [← he] at hanc ⊢
    exact anc_of_entry H.cg.parents hanc
  · obtain ⟨va, hPa, hpha, h1, h2⟩ := h
    rw [hgid] at h1
    exact H.sdom_of_anc hPa hpha h1 hanc hne

/-- **The target's block against a source reference frame `G`** (the source's frame after its
`Phi`s, `PS`, with the source's schedule `oS` evaluated in part or in full): the hypotheses of
`tgt_loop`/`tgt_next` for the target's frame after its `Phi`s, the new values placed in strict
dominators (lemma (D) on the target) as the initial new-value set. -/
theorem tgtHyp_of (H : Hyp tabs f g cv isNew front RR ce ce') {env : Env} {frS frT : Frame}
    {b : ID} {i : Nat} (hA : SimAt env tabs f g cv frS frT b i) (hbm : b ∈ f.blocks)
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
    (hGok : RegsOK (Ctx.make tabs f) G)
    (hGq : ∀ (a : ID) (m : Mem), G.regs[a]? = some (some (Val.mem m)) → EcQ tabs f m) :
    TgtHyp env tabs f g cv isNew front RR fb gb og G { frT with regs := setPhis psT frT.regs }
      (fun z => isNew z = true ∧ SDomPlaced g gb z) := by
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
  have hnotNewPhi : ∀ a ∈ gb.values, a ∉ og.toList → isNew a = true → False :=
    fun a ha hm han => by
      obtain ⟨w, hw, hph⟩ := hphi_of a ha hm
      exact (B.newOK a ha han w hw).1 hph
  have hbt := CSE.pre_tree H.wf H.cf hA.pre
  obtain ⟨fb', hfb', hfid⟩ := H.wf.blockId b hbm
  rw [hfb] at hfb'; cases hfb'
  obtain ⟨gb', hgb', hgid⟩ := H.wg.blockId b hbm'
  rw [hgb] at hgb'; cases hgb'
  have hgt : ((make g).depthOf gb.id).isSome := by rw [hgid, H.make_eq]; exact hbt.2
  have hDT : ∀ T : Frame, T = { { frT with regs := setPhis psT frT.regs } with regs := T.regs } →
      (∀ z, z ∉ gb.values → T.regs[z]? = (setPhis psT frT.regs)[z]?) →
      DInv env (Ctx.make tabs g) (fun a => Anc (make g) a gb.id ∧ a ≠ gb.id) T := by
    intro T hT hk
    rw [hgid]
    exact ec_dinv_keep H.wg H.cg hbm' hgb hA.dinvT hT fun z hz => by
      rw [hk z hz]; exact pT3 z (.inl hz)
  refine ⟨B, hsg, ogn, ogt, ogm, fun x hx w hw => ?_, ?_, by simp [pT1, hA.szT], hA.img,
    ?_, ?_, ?_, ?_, ?_, ?_, hGok,
    by rw [hfid]; exact hbt.2, ?_, ?_, ?_, hDT, ?_, hGq⟩
  · obtain ⟨w', hw', hid, -⟩ := H.wg.valueId b gb ⟨hbm', hgb⟩ x hx
    rw [hw] at hw'; cases hw'; exact hid
  · rw [hG]; conv => lhs; rw [hA.frame]
  · intro z ⟨hn, hz⟩
    obtain ⟨v, hP, hph, hanc, hne⟩ := id hz
    obtain ⟨y, hy, hev⟩ := hDT { frT with regs := setPhis psT frT.regs } rfl (fun _ _ => rfl)
      z v hP ⟨hanc, hne⟩
    exact ⟨hn, v, y, hP.1, fun a ha han => ⟨han, H.newArg_sdom hz hP.1 ha han⟩, hy, hev hph⟩
  · intro z hz hm
    obtain ⟨v, hP, -, -, hne⟩ := hz.2
    obtain ⟨v', hv', -, hvb'⟩ := H.wg.valueId b gb ⟨hbm', hgb⟩ z (hogb z hm)
    rw [hP.1] at hv'; cases hv'
    exact hne (hvb'.trans hgid.symm)
  · intro z hz w hw a ha hm
    obtain ⟨v, ⟨hv, hvb, gc, hgc, hzc⟩, hph, hanc, hne⟩ := hz.2
    have ha' : a ∈ v.args := by rw [hv] at hw; cases hw; exact ha
    obtain ⟨va, hva, -, hvab⟩ := H.wg.valueId b gb ⟨hbm', hgb⟩ a (hogb a hm)
    have hua := H.cg.domRel.uses hvb hgc (H.cg.domRel.left hanc) hzc hv hph ha'
    have hba : blockOf g a = gb.id := by unfold blockOf; rw [hva]; exact hvab.trans hgid.symm
    rw [hba] at hua
    exact hne (H.cg.domRel.antisymm hanc hua)
  · intro x hx w hw a ha han hm
    rcases B.newArgs x (hogb x hx) w hw a ha han with h | h | h
    · exact (hnotNewPhi a h hm han).elim
    · refine ⟨han, H.sdom_of_entryVal hgt (fun he => ?_) h han⟩
      obtain ⟨eb, heb, hae⟩ := h
      rw [he, hgid, hgb] at heb; cases heb
      exact hnotNewPhi a hae hm han
    · exact ⟨han, h⟩
  · intro x hx w hw a ha hm
    obtain ⟨-, w', hw', hph⟩ := (ogm x).1 hx
    rw [hw] at hw'; cases hw'
    by_cases hag : a ∈ gb.values
    · obtain ⟨wa, hwa, hpha⟩ := hphi_of a hag hm
      obtain ⟨-, y, -, -, hset⟩ := pT4 a hag wa hwa hpha (by rw [hA.szT]; exact lt_of_value? hwa)
      exact ⟨_, hset⟩
    · obtain ⟨y, hy⟩ := out_arg_reg H hA hgb (hogb x hx) hw hph ha hag
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
  · rw [hfid]
    exact ec_dinv_keep H.wf H.cf hbm hfb (CSE.pre_strict H.cf hA.pre).1 hG fun z hz => by
      rw [hGk z fun h => hz ((ofm z).1 h).1, pS3 z (.inl hz)]
  · intro z u ⟨hu, hub, blk, hblk, hz⟩
    obtain ⟨v, hv, hvid, -⟩ := H.wf.valueId u.block blk ⟨hub, hblk⟩ z hz
    rw [hu] at hv; cases hv; exact hvid
  · intro z hz u hu
    obtain ⟨v, hP, -, -⟩ := placed_of_mem H.wf hbm hfb hz
    rw [hP.1] at hu; cases hu; exact hP
  · intro z w ⟨hw, hwb, blk, hblk, hz⟩
    obtain ⟨v, hv, hvid, -⟩ := H.wg.valueId w.block blk ⟨hwb, hblk⟩ z hz
    rw [hw] at hv; cases hv; exact hvid

/-- The parts of a block entry the source does not get stuck in: its `Phi`s and schedule, the
target's block, schedule and `Phi`s. -/
theorem block_parts (H : Hyp tabs f g cv isNew front RR ce ce') {env : Env} {frS frT : Frame}
    {b : ID} {i : Nat} (hA : SimAt env tabs f g cv frS frT b i) {fb : Block}
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

/-- **A block the source enters successfully is entered by the target**, given that a `Ret`
terminator of the block reads results and a memory of the source's control (`hret`: else the
source is stuck at the terminator). -/
theorem enter_ok (H : Hyp tabs f g cv isNew front RR ce ce') {env : Env} (hE : env.Mono)
    (hK : env.FrameKeep) {frS frT : Frame} {b : ID} {i : Nat} (hA : SimAt env tabs f g cv frS frT b i)
    {fb : Block} (hfb : f.block? b = some fb) {GS : Frame}
    (hen : enterBlock env (Ctx.make tabs f) frS fb i = .ok GS)
    (hret : fb.kind = .Ret → ∀ c, fb.controls[0]? = some c → ∀ y, GS.regs[c]? = some (some y) →
      ∃ rs m, retOf y = some (rs, m)) :
    ∃ gb GT, g.block? b = some gb ∧ CvBlock tabs f g cv isNew front RR fb gb ∧
      enterBlock env (Ctx.make tabs g) frT gb i = .ok GT ∧
      GT = { GS with regs := GT.regs } ∧ GT.regs.size = g.valueTab.size ∧
      GS.regs.size = f.valueTab.size ∧
      (∀ x y, GS.regs[x]? = some (some y) →
        ∃ y', GT.regs[x]? = some (some y') ∧ Sem.Refines (cv x y) y') ∧
      (∀ x y, GS.regs[x]? = some (some y) → Listed f x) ∧ RegsOK (Ctx.make tabs f) GS ∧
      MemInv.SInv (EcQ tabs f) GS := by
  obtain ⟨gb, ps, oS, og, psT, hgb, B, hbm, -, hps, hsf, hsg, hev, hpsT, hphiT, hentT⟩ :=
    block_parts H hA hfb hen (fun _ h => nomatch h)
  have hbm' : b ∈ g.blocks := H.blocks_eq ▸ hbm
  have hndF := H.wf.valuesNodup b fb ⟨hbm, hfb⟩
  have hndG := H.wg.valuesNodup b gb ⟨hbm', hgb⟩
  obtain ⟨ofn, oft, ofm⟩ := schedule_topo (valuesOwn H.wf hbm hfb) hndF hsf
  obtain ⟨-, -, ogm⟩ := schedule_topo (valuesOwn H.wg hbm' hgb) hndG hsg
  obtain ⟨pS1, -, pS3, -⟩ := phis_spec hndF hps
  obtain ⟨pT1, -, -, -⟩ := phis_spec hndG hpsT
  obtain ⟨e1, e2, e3, e4⟩ := evalAll_spec ofn oft (by rw [pS1, hA.szS]; rfl) hev
  have hGSok : RegsOK (Ctx.make tabs f) GS :=
    regsOK_block H hbm hfb hps hA.ok (fun x hx => ((ofm x).1 hx).1) hev
  have hGSq := ecQ_enter hK H.wf hbm hfb hA.slots hen
  have TH := tgtHyp_of H hA hbm hfb hgb B hps hsf hsg hpsT hphiT (G := GS)
    (by rw [e1]) e3 hGSok (ecQ_memQ hGSq)
  have hlisted : ∀ x y, GS.regs[x]? = some (some y) → Listed f x := by
    intro x y hy
    by_cases hxo : x ∈ oS.toList
    · exact ⟨b, fb, ⟨hbm, hfb⟩, ((ofm x).1 hxo).1⟩
    · rw [e3 x hxo] at hy
      by_cases hxf : x ∈ fb.values
      · exact ⟨b, fb, ⟨hbm, hfb⟩, hxf⟩
      · rw [pS3 x (.inl hxf)] at hy; exact hA.listed x y hy
  have hsrc : ∀ x ∈ og.toList, isNew x = false → ∃ u y, f.value? x = some u ∧
      GS.regs[x]? = some (some y) ∧ evalValue env (Ctx.make tabs f) GS u = .ok y := fun x hx hn => by
    obtain ⟨hxg, w, hw, hph⟩ := (ogm x).1 hx
    have hxf : x ∈ fb.values := Classical.byContradiction fun h => by
      rw [B.fresh x hxg h] at hn; cases hn
    obtain ⟨u, hu, -, -⟩ := H.wf.valueId b fb ⟨hbm, hfb⟩ x hxf
    have huphi : u.op ≠ .Phi := fun hp => by
      obtain ⟨⟨w', hgu, hsw⟩, -⟩ := B.phiS x hxf u hu hp
      rw [hw] at hgu; cases hgu; exact hph (hsw.1.trans hp)
    exact e4 x ((ofm x).2 ⟨hxf, u, hu, huphi⟩)
  have hsrcF : ∀ x z, SrcArg f fb x z → ∃ u y, f.value? z = some u ∧
      GS.regs[z]? = some (some y) ∧ evalValue env (Ctx.make tabs f) GS u = .ok y := by
    intro x z hz
    obtain ⟨hzf, -, hzp⟩ := hz
    obtain ⟨uz, huz, -, -⟩ := H.wf.valueId b fb ⟨hbm, hfb⟩ z hzf
    exact e4 z ((ofm z).2 ⟨hzf, uz, huz, hzp uz huz⟩)
  obtain ⟨T, hT, hTf, hTs, hTk, hTr, -, -, -⟩ := tgt_loop hE TH (L := og.toList) (M := [])
    (U := fun _ => False) (by simp) (fun _ h => h.elim) (fun _ _ h => h.elim)
    (fun x hx hn _ _ => hsrc x hx hn) (fun x _ _ _ _ z hz => hsrcF x z hz)
    (fun c z hc _ _ _ A P Q hA _ => ⟨fun uc huc => by
      obtain ⟨u, y, hu, -, hev⟩ := hsrc c (by rw [hA]; simp) (B.common c hc).2
      rw [huc] at hu; cases hu
      exact .inl ⟨y, hev⟩, fun z hz => hsrcF c z hz⟩)
    fun z _ hra c hc0 => by
      obtain ⟨hk, c', hc0', hcf, hcph, -⟩ := hra
      rw [hc0] at hc0'; cases hc0'
      refine ⟨fun uc huc => ?_, hret hk c hc0⟩
      obtain ⟨u, y, hu, hy, hev⟩ := e4 c ((ofm c).2 ⟨hcf, uc, huc, hcph uc huc⟩)
      change f.value? c = some u at hu
      rw [huc] at hu; cases hu
      obtain ⟨u', hu', hid, -⟩ := H.wf.valueId b fb ⟨hbm, hfb⟩ c hcf
      rw [huc] at hu'; cases hu'
      exact ⟨hid, y, hy, hev⟩
  have hGT : T = { GS with regs := T.regs } := by rw [TH.hT0] at hTf; exact hTf
  refine ⟨gb, T, hgb, B, by rw [hentT, hT], hGT, by rw [hTs]; simp [pT1, hA.szT],
    by rw [e2, pS1, hA.szS],
    fun x y hy => ?_, hlisted, hGSok, hGSq⟩
  have hn := H.notNew (hlisted x y hy)
  by_cases hxo : x ∈ og.toList
  · exact hTr x hxo hn id y hy
  · rw [hTk x hxo]; exact TH.hrel0 x hxo hn y hy

end

end GoFV.Proof.EC
