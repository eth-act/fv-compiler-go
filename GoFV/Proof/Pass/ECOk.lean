import GoFV.Proof.Pass.ECEnter
import GoFV.Proof.AtomSimBlock

/-!
# A block entry the source completes (issue #28)

`tgt_phis`: the target's `Phi`s (those of the source) read refined arguments. `enter_ok`: the
target's block entry completes too (`tgt_loop` against the source's final frame), and its
registers refine the conversions of the source's; afterwards the entry block has run
(`EntryOK`).
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
    obtain ⟨hzf, hfw⟩ := B.phiT z hz w hw hph
    obtain ⟨-, -, hcva⟩ := B.phiS z hzf w hfw hph
    obtain ⟨a, y, ha, hy, hset⟩ := hphS z hzf w hfw hph (by rw [hA.szS]; exact lt_of_value? hfw)
    obtain ⟨y', hy', hyy⟩ := hA.rel a y hy
    rw [hcva a (Array.mem_of_getElem? ha) y] at hyy
    refine ⟨a, y, y', ha, hy', ?_, hyy⟩
    rw [hset, tys_of_value hfw]; rfl
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

/-- **A block the source enters successfully is entered by the target.** -/
theorem enter_ok (H : Hyp tabs f g cv isNew front RR ce ce') {env : Env} (hE : env.Mono)
    {frS frT : Frame} {b : ID} {i : Nat} (hA : SimAt env tabs f g cv isNew frS frT b i)
    {fb : Block} (hfb : f.block? b = some fb) {GS : Frame}
    (hen : enterBlock env (Ctx.make tabs f) frS fb i = .ok GS) :
    ∃ gb GT, g.block? b = some gb ∧ CvBlock tabs f g cv isNew front RR fb gb ∧
      enterBlock env (Ctx.make tabs g) frT gb i = .ok GT ∧
      GT = { GS with regs := GT.regs } ∧ GT.regs.size = g.valueTab.size ∧
      (∀ x y, GS.regs[x]? = some (some y) →
        ∃ y', GT.regs[x]? = some (some y') ∧ Sem.Refines (cv x y) y') ∧
      (∀ x y, GS.regs[x]? = some (some y) → Listed f x) ∧
      EntryOK env tabs g isNew GT := by
  have hbt := CSE.pre_tree H.wf H.cf hA.pre
  have hbm' : b ∈ g.blocks := H.blocks_eq ▸ hbt.1
  obtain ⟨gb, hgb, B⟩ := H.block hbt.1 hfb
  obtain ⟨fb', hfb', hfid⟩ := H.wf.blockId b hbt.1
  rw [hfb] at hfb'; cases hfb'
  obtain ⟨gb', hgb', hgid⟩ := H.wg.blockId b hbm'
  rw [hgb] at hgb'; cases hgb'
  obtain ⟨ps, oS, hps, hoS, hev⟩ := CSE.enterBlock_split hen (fun _ h => nomatch h)
  rw [hfid, sched_of_block hfb] at hoS
  obtain ⟨oF, og, hsf, hsg, -⟩ := B.sched
  rw [hsf] at hoS; cases hoS
  obtain ⟨psT, hpsT, hphiT⟩ := tgt_phis H hA hbt.1 hfb hgb B hps
  have hentT : enterBlock env (Ctx.make tabs g) frT gb i =
      evalAll env (Ctx.make tabs g) { frT with regs := setPhis psT frT.regs } og.toList :=
    CSE.enterBlock_of_parts hpsT (by rw [hgid, sched_of_block hgb, hsg])
  have hndF := H.wf.valuesNodup b fb ⟨hbt.1, hfb⟩
  have hndG := H.wg.valuesNodup b gb ⟨hbm', hgb⟩
  obtain ⟨ofn, oft, ofm⟩ := schedule_topo (valuesOwn H.wf hbt.1 hfb) hndF hsf
  obtain ⟨ogn, ogt, ogm⟩ := schedule_topo (valuesOwn H.wg hbm' hgb) hndG hsg
  obtain ⟨pS1, -, pS3, -⟩ := phis_spec hndF hps
  obtain ⟨pT1, -, pT3, pT4⟩ := phis_spec hndG hpsT
  obtain ⟨e1, e2, e3, e4⟩ := evalAll_spec ofn oft (by rw [pS1, hA.szS]; rfl) hev
  have hPT_G : ({ frT with regs := setPhis psT frT.regs } : Frame) =
      { GS with regs := setPhis psT frT.regs } := by
    rw [e1]; conv => lhs; rw [hA.frame]
  have hogb : ∀ x ∈ og.toList, x ∈ gb.values := fun x hx => ((ogm x).1 hx).1
  have hphi_of : ∀ a ∈ gb.values, a ∉ og.toList → ∃ w, g.value? a = some w ∧ w.op = .Phi :=
    fun a ha hm => by
      obtain ⟨w, hw, -, -⟩ := H.wg.valueId b gb ⟨hbm', hgb⟩ a ha
      exact ⟨w, hw, Classical.byContradiction fun hph => hm ((ogm a).2 ⟨ha, w, hw, hph⟩)⟩
  have hlisted : ∀ x y, GS.regs[x]? = some (some y) → Listed f x := by
    intro x y hy
    by_cases hxo : x ∈ oS.toList
    · exact ⟨b, fb, ⟨hbt.1, hfb⟩, ((ofm x).1 hxo).1⟩
    · rw [e3 x hxo] at hy
      by_cases hxf : x ∈ fb.values
      · exact ⟨b, fb, ⟨hbt.1, hfb⟩, hxf⟩
      · rw [pS3 x (.inl hxf)] at hy; exact hA.listed x y hy
  let E0 : ID → Prop := fun z => EntryVal g z ∧ isNew z = true ∧ b ≠ f.entry
  have hE0gb : ∀ z, E0 z → z ∉ gb.values := fun z hz =>
    H.entry_not_mem hz.1 hbm' hgb hz.2.2
  have hE0 : NewCons env (Ctx.make tabs g) isNew { frT with regs := setPhis psT frT.regs } E0 := by
    intro z ⟨hz, hn, hb⟩
    obtain ⟨-, hN⟩ := EntryOK.keep H (hA.entry.resolve_left hb)
      (T' := { frT with regs := setPhis psT frT.regs }) rfl
      (fun z hz => pT3 z (.inl (H.entry_not_mem hz hbm' hgb hb)))
    obtain ⟨-, w, y, hw, hcl, hy, hev⟩ := hN z ⟨hz, hn⟩
    exact ⟨hn, w, y, hw, fun a ha han => ⟨(hcl a ha han).1, han, hb⟩, hy, hev⟩
  have hnotNewPhi : ∀ a ∈ gb.values, a ∉ og.toList → isNew a = true → False :=
    fun a ha hm han => by
      obtain ⟨w, hw, hph⟩ := hphi_of a ha hm
      exact (B.newOK a ha han w hw).1 hph
  have hrel0 : ∀ a, a ∉ og.toList → isNew a = false → ∀ y, GS.regs[a]? = some (some y) →
      ∃ y', (setPhis psT frT.regs)[a]? = some (some y') ∧ Sem.Refines (cv a y) y' := by
    intro a hm han y hy
    by_cases hag : a ∈ gb.values
    · obtain ⟨w, hw, hph⟩ := hphi_of a hag hm
      obtain ⟨haf, hfw⟩ := B.phiT a hag w hw hph
      obtain ⟨-, hcv, -⟩ := B.phiS a haf w hfw hph
      have hao : a ∉ oS.toList := fun h => by
        obtain ⟨-, u, hu, hne⟩ := (ofm a).1 h
        rw [hfw] at hu; cases hu; exact hne hph
      obtain ⟨y0, y0', hy0, hy0', hyy⟩ := hphiT a hag w hw hph
      rw [e3 a hao, hy0] at hy; cases hy
      exact ⟨y0', hy0', by rw [hcv]; exact hyy⟩
    · have haf : a ∉ fb.values := fun h => hag (B.common a h).1
      have hao : a ∉ oS.toList := fun h => haf ((ofm a).1 h).1
      rw [e3 a hao, pS3 a (.inl haf)] at hy
      obtain ⟨y', hy', hyy⟩ := hA.rel a y hy
      exact ⟨y', by rw [pT3 a (.inl hag)]; exact hy', hyy⟩
  obtain ⟨T, hT, hTf, hTs, hTk, hTr, hTN, hTreg⟩ := tgt_loop B hE hsg ogn ogt ogm
    (fun x hx w hw => by
      obtain ⟨w', hw', hid, -⟩ := H.wg.valueId b gb ⟨hbm', hgb⟩ x hx
      rw [hw] at hw'; cases hw'; exact hid)
    (L := og.toList) (M := []) (by simp) hPT_G (by simp [pT1, hA.szT]) hA.img
    hE0 (fun z hz hm => hE0gb z hz (hogb z hm))
    (fun z hz w hw a ha hm =>
      H.entry_not_mem (H.entry_args hz.1 hw a ha) hbm' hgb hz.2.2 (hogb a hm))
    (fun x hx w hw a ha han hm => by
      rcases B.newArgs x (hogb x hx) w hw a ha han with h | h
      · exact (hnotNewPhi a h hm han).elim
      · refine ⟨h, han, fun hb => ?_⟩
        obtain ⟨eb, heb, hae⟩ := h
        rw [H.entry_eq, ← hb, hgb] at heb; cases heb
        exact hnotNewPhi a hae hm han)
    (fun x hx w hw a ha hm => by
      obtain ⟨-, w', hw', hph⟩ := (ogm x).1 hx
      rw [hw] at hw'; cases hw'
      by_cases hag : a ∈ gb.values
      · obtain ⟨wa, hwa, hpha⟩ := hphi_of a hag hm
        obtain ⟨-, y, -, -, hset⟩ := pT4 a hag wa hwa hpha (by rw [hA.szT]; exact lt_of_value? hwa)
        exact ⟨_, hset⟩
      · obtain ⟨y, hy⟩ := out_arg_reg H hA hfb hgb B (hogb x hx) hw hph ha hag
        exact ⟨y, by show (setPhis psT frT.regs)[a]? = _; rw [pT3 a (.inl hag)]; exact hy⟩)
    hrel0
    (fun x hx hn => by
      obtain ⟨hxg, w, hw, hph⟩ := (ogm x).1 hx
      have hxf : x ∈ fb.values := Classical.byContradiction fun h => by
        rw [B.fresh x hxg h] at hn; cases hn
      obtain ⟨u, hu, -, -⟩ := H.wf.valueId b fb ⟨hbt.1, hfb⟩ x hxf
      have huphi : u.op ≠ .Phi := fun hp => by
        obtain ⟨hgu, -⟩ := B.phiS x hxf u hu hp
        rw [hw] at hgu; cases hgu; exact hph hp
      exact e4 x ((ofm x).2 ⟨hxf, u, hu, huphi⟩))
  have hGT : T = { GS with regs := T.regs } := by rw [hPT_G] at hTf; exact hTf
  refine ⟨gb, T, hgb, B, by rw [hentT, hT], hGT, by rw [hTs]; simp [pT1, hA.szT],
    fun x y hy => ?_, hlisted, ?_⟩
  · have hn := H.notNew (hlisted x y hy)
    by_cases hxo : x ∈ og.toList
    · exact hTr x hxo hn y hy
    · rw [hTk x hxo]; exact hrel0 x hxo hn y hy
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
