import GoFV.Proof.Pass.BranchElimOk

/-!
# branchelim: panics in the merged block

`post_panic`: a panic of the source in `post` (after `dom` and the arm ran) is a panic of the
merged block. `dom_panic`: a panic in `dom` is one too. In both, the target's schedule lists
before the panicking node only values the source evaluated before it and speculation-safe
values (`Order.transfer_rank`: the checker's `npSeqOK`, via `npSeqSem`, makes the merged schedule list the
non-pure nodes of `dom` and then those of `post` in their source sequence); for `dom_panic` no
non-pure node of `post` comes first (`not_before_append`).
-/

namespace GoFV.Proof.BranchElim

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Opt GoFV.Opt.BranchElim GoFV.Proof Dom

variable {f g : Func} {s : Site}

/-- Splitting a filtered list that is the concatenation of two disjointly filtered lists. -/
theorem filter_split {a b : ID → Bool} {oT oD oP : List ID}
    (h : oT.filter (fun x => a x || b x) = oD.filter a ++ oP.filter b)
    (hab : ∀ x, a x = true → b x = false) :
    oT.filter a = oD.filter a ∧ oT.filter b = oP.filter b := by
  have hba : ∀ x, b x = true → a x = false := fun x hb =>
    Bool.eq_false_iff.2 fun ha => by rw [hab x ha] at hb; cases hb
  have n1 : (oP.filter b).filter a = [] := List.filter_eq_nil_iff.2 fun x hx => by
    rw [hba x (List.mem_filter.1 hx).2]; decide
  have n2 : (oD.filter a).filter b = [] := List.filter_eq_nil_iff.2 fun x hx => by
    rw [hab x (List.mem_filter.1 hx).2]; decide
  have i1 : (oD.filter a).filter a = oD.filter a := by
    rw [List.filter_filter]; exact List.filter_congr fun x _ => by cases a x <;> rfl
  have i2 : (oP.filter b).filter b = oP.filter b := by
    rw [List.filter_filter]; exact List.filter_congr fun x _ => by cases b x <;> rfl
  have e1 : oT.filter a = (oT.filter (fun x => a x || b x)).filter a := by
    rw [List.filter_filter]; exact List.filter_congr fun x _ => by cases a x <;> rfl
  have e2 : oT.filter b = (oT.filter (fun x => a x || b x)).filter b := by
    rw [List.filter_filter]
    exact List.filter_congr fun x _ => by cases b x <;> cases a x <;> rfl
  exact ⟨by rw [e1, h, List.filter_append, i1, n1, List.append_nil],
    by rw [e2, h, List.filter_append, i2, n2, List.nil_append]⟩

namespace Setup

variable (S : Setup f g s)
include S

/-- `dom`'s and `post`'s non-`Phi` values are distinct. -/
theorem np_disj {D P : Block} (hD : f.block? s.dom = some D) (hP : f.block? s.post = some P)
    (x : ID) (h : npOf f D x = true) : npOf f P x = false := by
  unfold npOf at h ⊢
  have hx : x ∈ D.values := Array.contains_iff_mem.1 (Bool.and_eq_true_iff.1 h).1
  have hnp := (S.dom_not hD hx).1
  have hc : P.values.contains x = false := Bool.eq_false_iff.2 fun hc => by
    rw [postVal_iff.2 ⟨P, hP, Array.contains_iff_mem.1 hc⟩] at hnp; cases hnp
  rw [hc]; rfl

/-- The merged block's schedule lists the non-pure nodes of `dom`, then those of `post`, in
their source sequence (`npSeqOK`, read through `npSeqSem`). -/
theorem npSeq {D P D' : Block} (hD : f.block? s.dom = some D) (hP : f.block? s.post = some P)
    (hD' : g.block? s.dom = some D') {oT : Array ID} (hoT : schedule g D' = some oT) :
    ∃ oD oP, schedule f D = some oD ∧ schedule f P = some oP ∧
      oT.toList.filter (fun x => npOf f D x || npOf f P x) =
        oD.toList.filter (npOf f D) ++ oP.toList.filter (npOf f P) := by
  obtain ⟨D1, P1, D1', hD1, hP1, hD1', -, -, -, -, -, -, -, -, -, hn⟩ := merged_spec S.rel S.wf S.wg
  rw [hD] at hD1; cases hD1
  rw [hP] at hP1; cases hP1
  rw [hD'] at hD1'; cases hD1'
  unfold npSeqSem at hn
  cases hoD : schedule f D with
  | none => rw [hoD] at hn; cases hn
  | some oD =>
    cases hoP : schedule f P with
    | none => rw [hoD, hoP] at hn; cases hn
    | some oP =>
      rw [hoD, hoP, hoT] at hn
      exact ⟨oD, oP, rfl, rfl, by simpa using hn⟩

/-- **A panic in `post`** (after `dom` and the arm) is a panic of the merged block. -/
theorem post_panic {tabs : Tables} {env : Env} {frS frT G1 G' : Frame} {i k : Nat}
    {arm arm' : Option ID} {j j' : Nat}
    (hfr : frT = { frS with regs := frT.regs }) (hsz : frT.regs.size = frS.regs.size)
    (hs : frS.regs.size = f.valueTab.size)
    (hag : ∀ a, s.armVal f a = false → frT.regs[a]? = frS.regs[a]?)
    (htd : Reachable f s.dom)
    (hdi : DInv env (Ctx.make tabs f) (fun a => SDom f a s.dom ∧ a ≠ s.dom) frS)
    {D P : Block} (hD : f.block? s.dom = some D) (hP : f.block? s.post = some P)
    (h1 : enterBlock env (Ctx.make tabs f) frS D i = .ok G1)
    (htk : Taken s k arm j arm' j')
    (hc : G1.regs[s.c]? = some (some (.bool (k == 0))))
    (hpath : (arm = none ∧ G' = G1) ∨
      (∃ a A, arm = some a ∧ f.block? a = some A ∧ enterBlock env (Ctx.make tabs f) G1 A 0 = .ok G'))
    {e : Panic} {m : Mem} (h3 : enterBlock env (Ctx.make tabs f) G' P j = .panic e m) :
    ∃ D', g.block? s.dom = some D' ∧ enterBlock env (Ctx.make tabs g) frT D' i = .panic e m := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  obtain ⟨e1f, e1s, -, -, -⟩ := enter_ok_facts hwf S.domIn hD hs h1
  obtain ⟨eaf, eas, -, -⟩ := S.arm_facts htk (by rw [e1s, hs]) hpath
  obtain ⟨psP, oP, pre, r, post, Gp, hpsP, hoP, hsplit, hpre, hrp, hGf, hGs, hGo, hGv, hGp, hrP, rv,
    hrv, hrnp, hrop⟩ := enter_panic_facts hwf S.postIn hP (by rw [eas, e1s, hs]) h3
  obtain ⟨D', psT, oT, hD', hid', hpsT, hoT, ondT, otopoT, omemT, hPnode, hg0, hsz0, hGs', hT0, hSd,
      hmix, hAnode, hFarm⟩ := S.merged_core hfr hsz hs hag htd hdi hD hP h1 htk hc hpath
    (G3 := Gp) (by rw [hGf, eaf, e1f]) (by rw [hGs, eas, e1s, hs]) hGo hGp (· ∈ pre)
    (fun x _ v hv _ hx => by
      obtain ⟨v', y, hv', hy, hev⟩ := hGv x hx
      rw [hv] at hv'; cases hv'
      exact ⟨y, hy, hev⟩)
  have hdg := S.domInG
  have hownP := valuesOwn hwf S.postIn hP
  have hndP := hwf.valuesNodup s.post P ⟨S.postIn, hP⟩
  have hownD' := valuesOwn hwg hdg hD'
  have hndD' := hwg.valuesNodup s.dom D' ⟨hdg, hD'⟩
  -- the panicking root in the target's schedule
  have hrT : r ∈ oT.toList := hPnode r hrP
  obtain ⟨pre', post', hsplitT⟩ := List.append_of_mem hrT
  have hspecS := schedule_spec hoP
  have hspecT := schedule_spec hoT
  have hk : oP.toList[pre.length]? = some r := by rw [hsplit]; simp
  have hk' : oT.toList[pre'.length]? = some r := by rw [hsplitT]; simp
  have hnodeP : ∀ x, NodeIn (schedNodes f P).toList x ↔
      x ∈ P.values ∧ ∃ v, f.value? x = some v ∧ v.op ≠ .Phi := fun x => nodeIn_schedNodes hownP
  have hnodeT : ∀ x, NodeIn (schedNodes g D').toList x ↔
      x ∈ D'.values ∧ ∃ v, g.value? x = some v ∧ v.op ≠ .Phi := fun x => nodeIn_schedNodes hownD'
  -- a non-`Phi` of `post` is a node of the merged block with the same arguments
  have hPsem : ∀ x, x ∈ P.values → ∀ fv, f.value? x = some fv → fv.op ≠ .Phi →
      ∃ gv, g.value? x = some gv ∧ gv.op = fv.op ∧ gv.args = fv.args := by
    intro x hx fv hfv hnp
    have hc' : ∀ fv', f.value? x = some fv' → s.postVal f x = true → fv'.op ≠ .Phi :=
      fun fv' h _ => by rw [hfv] at h; cases h; exact hnp
    obtain ⟨hsem, hv⟩ := semEq_of S.rel hc'
    rw [hfv] at hsem
    obtain ⟨gv, hgv, -, hop⟩ := hv fv hfv
    rw [hgv] at hsem
    exact ⟨gv, hgv, hop, hsem.2.2.2.2⟩
  have hsubN : ∀ x, NodeIn (schedNodes f P).toList x → NodeIn (schedNodes g D').toList x := by
    intro x hx
    obtain ⟨hxP, fv, hfv, hnp⟩ := (hnodeP x).1 hx
    obtain ⟨gv, hgv, hop, -⟩ := hPsem x hxP fv hfv hnp
    exact (hnodeT x).2 ⟨((omemT x).1 (hPnode x hxP)).1, gv, hgv, by rw [hop]; exact hnp⟩
  have hargsN : ∀ x, NodeIn (schedNodes f P).toList x →
      argsOf (schedNodes g D').toList x = argsOf (schedNodes f P).toList x := by
    intro x hx
    obtain ⟨hxP, fv, hfv, hnp⟩ := (hnodeP x).1 hx
    obtain ⟨gv, hgv, hop, hargs⟩ := hPsem x hxP fv hfv hnp
    rw [argsOf_schedNodes hownP hndP hxP hfv hnp,
      argsOf_schedNodes hownD' hndD' ((omemT x).1 (hPnode x hxP)).1 hgv (by rw [hop]; exact hnp),
      hargs]
  obtain ⟨oD, oP', -, hoP', hseqA⟩ := S.npSeq hD hP hD' hoT
  rw [hoP] at hoP'; cases hoP'
  have hseq := (filter_split hseqA (S.np_disj hD hP)).2
  rw [← npIn_schedNodes hownP hndP] at hseq
  have hrnpP : npIn (schedNodes f P).toList r = true := by
    rw [npIn_schedNodes hownP hndP]
    simp [npOf, hrP, hrv, hrnp, prio_panicking hrop]
  have htr := Order.transfer_rank hspecS.topo hspecS.pureFirst hspecT.topo (fun _ => npIn_iff)
    hseq.symm hk hk' hrnpP (fun a y ha hy hay hy' =>
      .direct (hsubN a ha) (.arg (hsubN a ha) hy' (by rw [hargsN y hy]; exact hay)))
  -- a value of `post` the target lists before `r` the source evaluated before `r`
  have hQ : ∀ x ∈ pre', ∀ fv, f.value? x = some fv → x ∈ P.values → fv.op ≠ .Phi → x ∈ pre := by
    intro x hx fv hfv hxP hnp
    obtain ⟨jx, hjx⟩ := List.getElem?_of_mem hx
    have hjl : jx < pre'.length := (List.getElem?_eq_some_iff.1 hjx).1
    obtain ⟨i', hi', hix⟩ := htr jx x hjl (by rw [hsplitT, List.getElem?_append_left hjl]; exact hjx)
      ((hnodeP x).2 ⟨hxP, fv, hfv, hnp⟩)
    rw [hsplit, List.getElem?_append_left hi'] at hix
    exact List.mem_of_getElem? hix
  have hpreT : ∀ x ∈ pre', x ∈ oT.toList := fun x hx => by rw [hsplitT]; simp [hx]
  have htopo' : TopoRem (argsF (Ctx.make tabs g).f) (pre' ++ r :: post') := hsplitT ▸ otopoT
  have hnoarmS : ∀ a, a ∉ oT.toList → s.armVal f a = false := fun a ha =>
    Bool.eq_false_iff.2 fun h => ha (hAnode a h)
  -- `r`'s arguments are no arm values
  obtain ⟨gr, hgr, hgrop, hgrargs⟩ := hPsem r hrP rv hrv hrnp
  have hrNA : ∀ a ∈ rv.args, s.armVal f a = false := by
    intro a ha
    obtain ⟨k', hk'⟩ := Array.mem_iff_getElem?.1 ha
    have hu := (uses_spec S.rel S.postIn hP).1 r hrP rv hrv k' a hk'
    unfold Site.useOK at hu
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hu
    have hpa : ∀ a', (s.arm0 = some a' ∨ s.arm1 = some a') → a' ≠ s.post := fun a' ha' h => by
      obtain ⟨D2, e0, e1, hD2, -, -, hs2, -, h0, h1⟩ := S.diamond
      rcases ha' with ha' | ha'
      · rcases S.side_facts hD2 (by rw [hs2]; rfl) h0 with ⟨h', -⟩ | ⟨b, A, hb, -, -, -, -, -, -, hbp, -⟩
        · rw [h'] at ha'; cases ha'
        · rw [ha'] at hb; cases hb; exact hbp h
      · rcases S.side_facts hD2 (by rw [hs2]; rfl) h1 with ⟨h', -⟩ | ⟨b, A, hb, -, -, -, -, -, -, hbp, -⟩
        · rw [h'] at ha'; cases ha'
        · rw [ha'] at hb; cases hb; exact hbp h
    obtain ⟨h0, h1⟩ := hu
    have e0 : Site.inArm f s.arm0 a = false := by
      rcases h0 with (h0 | h0) | h0
      · exact h0
      · exact absurd rfl (hpa s.post (.inl h0))
      · exact absurd h0.1.2 hrnp
    have e1 : Site.inArm f s.arm1 a = false := by
      rcases h1 with (h1 | h1) | h1
      · exact h1
      · exact absurd rfl (hpa s.post (.inr h1))
      · exact absurd h1.1.2 hrnp
    unfold Site.armVal; rw [e0, e1]; rfl
  have hctxT : (Ctx.make tabs g).params = (Ctx.make tabs f).params := params_eq S.rel.parts.2.2.2.1
  obtain ⟨gr', hgr', hgrid, -⟩ := hwg.valueId s.dom D' ⟨hdg, hD'⟩ r ((omemT r).1 hrT).1
  rw [hgr] at hgr'; cases hgr'
  have hpanT := evalAll_mix_panic (F := fun z => Site.inArm f arm' z = true) (post := post')
    (S := fun a => a ∉ oT.toList ∧ ∃ x ∈ oT.toList, a ∈ argsF (Ctx.make tabs g).f x)
    hGs' (mixOK_of_single fun x hx => hmix x (hpreT x hx) fun fv hfv hxP hnp => hQ x hx fv hfv hxP hnp)
    (Dead.refOK_of_topo (topoRem_prefix htopo') fun x hx a ha hna => ⟨fun haT =>
        hna (topoRem_arg_prefix htopo' x hx a ha (hsplitT ▸ haT)), x, hpreT x hx, ha⟩)
    (fun a ha _ => hT0 a ha.1 (hnoarmS a ha.1)) (fun a ha => hSd a ha.1 ha.2) hg0 hsz0
    (fun a ha => by
      by_cases haT : a ∈ oT.toList
      · rw [hsplitT] at haT
        rcases List.mem_append.1 haT with h | h
        · exact .inr h
        · exact absurd h (CopyElim.topoRem_at htopo' a ha)
      · exact .inl ⟨haT, r, hrT, ha⟩)
    (fun g' hg' hag' _ => by
      have hsrc : stepV env (Ctx.make tabs f) Gp r = .panic e m := hrp
      rw [stepV_eq hrv] at hsrc
      rw [stepV_eq hgr]
      obtain ⟨hsem, hv⟩ := semEq_of S.rel (fun fv' h _ => by rw [hrv] at h; cases h; exact hrnp)
      rw [hrv, hgr] at hsem
      obtain ⟨gv, hgv, hty, -⟩ := hv rv hrv
      rw [hgr] at hgv; cases hgv
      have hrid : rv.id = r := hsem.1 ▸ hgrid
      rw [evalValue_ctx_congr (ctxS := Ctx.make tabs f) (ctxT := Ctx.make tabs g) hsem hg'
        (fun a ha => hag' a (by
            rw [show (Ctx.make tabs g).f = g from rfl, argsF_of hgr, hgrargs]
            exact Array.mem_toList_iff.2 ha)
          (fun h => by have := hFarm a h; rw [hrNA a ha] at this; cases this))
        (by rw [hrid, tys_of_value hrv, tys_of_value hgr, hty]) rfl hctxT rfl]
      exact hsrc)
  refine ⟨D', hD', ?_⟩
  rw [enterBlock_eq, hpsT]
  change (Res.ofOption _ ((Ctx.make tabs g).sched[D'.id]?).join).bind _ = _
  rw [hid', sched_of_block hD', hoT]
  change evalAll env (Ctx.make tabs g) _ oT.toList = _
  rw [hsplitT]
  exact hpanT

/-- Every value of `post` and every arm value is a node of the merged block's schedule. -/
theorem region_nodes {D' : Block} (hD' : g.block? s.dom = some D') {oT : Array ID}
    (hoT : schedule g D' = some oT) {P : Block} (hP : f.block? s.post = some P) :
    (∀ x ∈ P.values, x ∈ oT.toList) ∧ (∀ x, s.armVal f x = true → x ∈ oT.toList) := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  obtain ⟨D1, P1, D1', hD1, hP1, hD1', -, -, -, -, -, -, hPin, harmin, -⟩ := merged_spec S.rel S.wf S.wg
  rw [hP] at hP1; cases hP1
  rw [hD'] at hD1'; cases hD1'
  have hdg := S.domInG
  obtain ⟨-, -, omemT⟩ := schedule_topo (valuesOwn hwg hdg hD')
    (hwg.valuesNodup s.dom D' ⟨hdg, hD'⟩) hoT
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨fv, hfv, -⟩ := hwf.valueId s.post P ⟨S.postIn, hP⟩ z hz
    have hzp : s.postVal f z = true := postVal_iff.2 ⟨P, hP, hz⟩
    refine (omemT z).2 ⟨hPin z hz, ?_⟩
    by_cases hph : fv.op = .Phi
    · obtain ⟨gv, hgv, -, -, -, -, hop, -⟩ := condSel_of S.rel hfv hzp hph
      exact ⟨gv, hgv, by rw [hop]; simp⟩
    · obtain ⟨gv, hgv, -, hop⟩ := (semEq_of S.rel fun fv' h _ => by
        rw [hfv] at h; cases h; exact hph).2 fv hfv
      exact ⟨gv, hgv, by rw [hop]; exact hph⟩
  · obtain ⟨fv, hfv, hsafe, -⟩ := armVal_spec S.rel hz
    have hnp : s.postVal f z = false := Bool.eq_false_iff.2 fun hp' => by
      obtain ⟨P2, hP2, hzP⟩ := postVal_iff.1 hp'
      have := S.post_not_arm hP2 hzP; rw [hz] at this; cases this
    obtain ⟨gv, hgv, -, hop⟩ := (semEq_of S.rel fun _ _ h => by rw [hnp] at h; cases h).2 fv hfv
    refine (omemT z).2 ⟨harmin z hz, gv, hgv, ?_⟩
    rw [hop]; intro h; rw [h] at hsafe; simp [specSafeOp] at hsafe

/-- **A panic in `dom`** is a panic of the merged block. -/
theorem dom_panic {tabs : Tables} {env : Env} {frS frT : Frame} {i : Nat}
    (hfr : frT = { frS with regs := frT.regs }) (hsz : frT.regs.size = frS.regs.size)
    (hs : frS.regs.size = f.valueTab.size)
    (hag : ∀ a, s.armVal f a = false → frT.regs[a]? = frS.regs[a]?)
    (htd : Reachable f s.dom)
    (hdi : DInv env (Ctx.make tabs f) (fun a => SDom f a s.dom ∧ a ≠ s.dom) frS)
    {D : Block} (hD : f.block? s.dom = some D)
    {e : Panic} {m : Mem} (h1 : enterBlock env (Ctx.make tabs f) frS D i = .panic e m) :
    ∃ D', g.block? s.dom = some D' ∧ enterBlock env (Ctx.make tabs g) frT D' i = .panic e m := by
  obtain ⟨ce, hwf⟩ := S.wf
  obtain ⟨ce', hwg⟩ := S.wg
  obtain ⟨psS, oS, pre, r, post, Gp, hpsS, hoS, hsplit, hpre, hrp, hGf, hGs, hGo, hGv, hGp, hrD, rv,
    hrv, hrnp, hrop⟩ := enter_panic_facts hwf S.domIn hD hs h1
  obtain ⟨D', psT, oT, hD', hpsT, hoT, hszT, hagT⟩ := S.targetPre hs hsz hag hD hpsS
  obtain ⟨D1, P, D1', hD1, hP, hD1', hid', -, -, -, hreg, hDin, -, -, -⟩ := merged_spec S.rel S.wf S.wg
  rw [hD] at hD1; cases hD1
  rw [hD'] at hD1'; cases hD1'
  obtain ⟨hPnode, hAnode⟩ := S.region_nodes hD' hoT hP
  have hdg := S.domInG
  have hownD := valuesOwn hwf S.domIn hD
  have hndD := hwf.valuesNodup s.dom D ⟨S.domIn, hD⟩
  have hownD' := valuesOwn hwg hdg hD'
  have hndD' := hwg.valuesNodup s.dom D' ⟨hdg, hD'⟩
  obtain ⟨ondT, otopoT, omemT⟩ := schedule_topo hownD' hndD' hoT
  obtain ⟨-, -, hkeepS, hphiS⟩ := phis_spec hndD hpsS
  have hctxT : (Ctx.make tabs g).params = (Ctx.make tabs f).params := params_eq S.rel.parts.2.2.2.1
  have hgsz : g.valueTab.size = f.valueTab.size := S.rel.parts.2.2.2.2.1
  -- the free values: the arms' and `post`'s
  let F : ID → Prop := fun x => s.armVal f x = true ∨ s.postVal f x = true
  have hnotF : ∀ a, a ∉ oT.toList → ¬ F a := by
    rintro a ha (h | h)
    · exact ha (hAnode a h)
    · obtain ⟨P2, hP2, haP⟩ := postVal_iff.1 h
      rw [hP] at hP2; cases hP2
      exact ha (hPnode a haP)
  have hnoarmS : ∀ a, a ∉ oT.toList → s.armVal f a = false := fun a ha =>
    Bool.eq_false_iff.2 fun h => ha (hAnode a h)
  -- the target after its `Phi`s agrees with `Gp` outside its schedule
  have hT0 : ∀ a, a ∉ oT.toList → (setPhis psT frT.regs)[a]? = Gp.regs[a]? := by
    intro a ha
    rw [hagT a ha (hnoarmS a ha)]
    by_cases haD : a ∈ D.values
    · obtain ⟨gv, hgv, -, -⟩ := hwg.valueId s.dom D' ⟨hdg, hD'⟩ a (hDin a haD)
      have hgph : gv.op = .Phi := Classical.byContradiction fun hne =>
        ha ((omemT a).2 ⟨hDin a haD, gv, hgv, hne⟩)
      obtain ⟨-, fv, hfv, hfph, -, -⟩ := S.merged_values hD hD' (hDin a haD) hgv hgph
      have hlt : a < frS.regs.size := by rw [hs]; exact lt_of_value? hfv
      obtain ⟨b1, y1, hb1, hy1, hS1⟩ := hphiS a haD fv hfv hfph hlt
      obtain ⟨b2, y2, hb2, hy2, hS2⟩ := hGp a haD fv hfv hfph
      rw [hb1] at hb2; cases hb2
      rw [hy1] at hy2; cases hy2
      rw [hS1, hS2]
    · rw [hkeepS a (.inl haD), hGo a haD]
  -- the panicking root and the transfer of its prefix
  have hrnode : r ∈ oT.toList := by
    obtain ⟨gv, hgv, hop⟩ : ∃ gv, g.value? r = some gv ∧ gv.op = rv.op := by
      obtain ⟨gv, hgv, -, hop⟩ := (semEq_of S.rel fun _ _ h => by
        rw [(S.dom_not hD hrD).1] at h; cases h).2 rv hrv
      exact ⟨gv, hgv, hop⟩
    exact (omemT r).2 ⟨hDin r hrD, gv, hgv, by rw [hop]; exact hrnp⟩
  obtain ⟨pre', post', hsplitT⟩ := List.append_of_mem hrnode
  have hspecS := schedule_spec hoS
  have hspecT := schedule_spec hoT
  have hk : oS.toList[pre.length]? = some r := by rw [hsplit]; simp
  have hk' : oT.toList[pre'.length]? = some r := by rw [hsplitT]; simp
  -- a non-`Phi` of `dom` keeps its op and arguments
  have hDsem : ∀ x ∈ D.values, ∀ fv, f.value? x = some fv →
      ∃ gv, g.value? x = some gv ∧ SemEq (some fv) (some gv) ∧ gv.type = fv.type := by
    intro x hx fv hfv
    obtain ⟨hsem, hv⟩ := semEq_of S.rel fun _ _ h => by rw [(S.dom_not hD hx).1] at h; cases h
    obtain ⟨gv, hgv, hty, -⟩ := hv fv hfv
    rw [hfv, hgv] at hsem
    exact ⟨gv, hgv, hsem, hty⟩
  have hnodeD : ∀ x, NodeIn (schedNodes f D).toList x ↔
      x ∈ D.values ∧ ∃ v, f.value? x = some v ∧ v.op ≠ .Phi := fun x => nodeIn_schedNodes hownD
  have hnodeT : ∀ x, NodeIn (schedNodes g D').toList x ↔
      x ∈ D'.values ∧ ∃ v, g.value? x = some v ∧ v.op ≠ .Phi := fun x => nodeIn_schedNodes hownD'
  have hsubN : ∀ x, NodeIn (schedNodes f D).toList x → NodeIn (schedNodes g D').toList x := by
    intro x hx
    obtain ⟨hxD, fv, hfv, hnp⟩ := (hnodeD x).1 hx
    obtain ⟨gv, hgv, hsem, -⟩ := hDsem x hxD fv hfv
    exact (hnodeT x).2 ⟨hDin x hxD, gv, hgv, by rw [hsem.2.1]; exact hnp⟩
  have hargsN : ∀ x, NodeIn (schedNodes f D).toList x →
      argsOf (schedNodes g D').toList x = argsOf (schedNodes f D).toList x := by
    intro x hx
    obtain ⟨hxD, fv, hfv, hnp⟩ := (hnodeD x).1 hx
    obtain ⟨gv, hgv, hsem, -⟩ := hDsem x hxD fv hfv
    rw [argsOf_schedNodes hownD hndD hxD hfv hnp,
      argsOf_schedNodes hownD' hndD' (hDin x hxD) hgv (by rw [hsem.2.1]; exact hnp), hsem.2.2.2.2]
  obtain ⟨oD', oP, hoD', -, hseqA⟩ := S.npSeq hD hP hD' hoT
  rw [hoS] at hoD'; cases hoD'
  have hseq := (filter_split hseqA (S.np_disj hD hP)).1
  rw [← npIn_schedNodes hownD hndD] at hseq
  have hrnpD' : npOf f D r = true := by
    simp [npOf, hrD, hrv, hrnp, prio_panicking hrop]
  have hrnpD : npIn (schedNodes f D).toList r = true := by
    rw [npIn_schedNodes hownD hndD]; exact hrnpD'
  have htr := Order.transfer_rank hspecS.topo hspecS.pureFirst hspecT.topo (fun _ => npIn_iff)
    hseq.symm hk hk' hrnpD (fun a y ha hy hay hy' =>
      .direct (hsubN a ha) (.arg (hsubN a ha) hy' (by rw [hargsN y hy]; exact hay)))
  -- arguments of `dom`'s non-`Phi`s are neither arm nor `post` values
  have hDargs : ∀ x ∈ D.values, ∀ fv, f.value? x = some fv → fv.op ≠ .Phi → ∀ a ∈ fv.args, ¬ F a := by
    intro x hx fv hfv hnp a ha
    have hpa := (dom_spec S.rel hD).1 x hx fv hfv hnp a ha
    obtain ⟨k', hk'⟩ := Array.mem_iff_getElem?.1 ha
    have hu := (uses_spec S.rel S.domIn hD).1 x hx fv hfv k' a hk'
    unfold Site.useOK at hu
    simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at hu
    obtain ⟨-, -, -, -, -, -, -, hpd, -⟩ := S.diamond
    have hda : ∀ a', (s.arm0 = some a' ∨ s.arm1 = some a') → s.dom ≠ a' := fun a' ha' h => by
      obtain ⟨D2, e0, e1, hD2, -, -, hs2, -, h0, h1⟩ := S.diamond
      rcases ha' with ha' | ha'
      · rcases S.side_facts hD2 (by rw [hs2]; rfl) h0 with ⟨h', -⟩ | ⟨b, A, hb, -, -, -, -, -, -, -, hbd⟩
        · rw [h'] at ha'; cases ha'
        · rw [ha'] at hb; cases hb; exact hbd h.symm
      · rcases S.side_facts hD2 (by rw [hs2]; rfl) h1 with ⟨h', -⟩ | ⟨b, A, hb, -, -, -, -, -, -, -, hbd⟩
        · rw [h'] at ha'; cases ha'
        · rw [ha'] at hb; cases hb; exact hbd h.symm
    obtain ⟨h0, h1⟩ := hu
    have e0 : Site.inArm f s.arm0 a = false := by
      rcases h0 with (h0 | h0) | h0
      · exact h0
      · exact absurd rfl (hda s.dom (.inl h0))
      · exact absurd h0.1.1 (Ne.symm hpd)
    have e1 : Site.inArm f s.arm1 a = false := by
      rcases h1 with (h1 | h1) | h1
      · exact h1
      · exact absurd rfl (hda s.dom (.inr h1))
      · exact absurd h1.1.1 (Ne.symm hpd)
    rintro (h | h)
    · unfold Site.armVal at h; rw [e0, e1] at h; cases h
    · rw [hpa] at h; cases h
  -- a value of `dom` the target lists before `r` the source evaluated before `r`
  have hpreT : ∀ x ∈ pre', x ∈ oT.toList := fun x hx => by rw [hsplitT]; simp [hx]
  have hQ : ∀ x ∈ pre', ∀ fv, f.value? x = some fv → x ∈ D.values → fv.op ≠ .Phi → x ∈ pre := by
    intro x hx fv hfv hxD hnp
    obtain ⟨jx, hjx⟩ := List.getElem?_of_mem hx
    have hjl : jx < pre'.length := (List.getElem?_eq_some_iff.1 hjx).1
    obtain ⟨i', hi', hix⟩ := htr jx x hjl (by rw [hsplitT, List.getElem?_append_left hjl]; exact hjx)
      ((hnodeD x).2 ⟨hxD, fv, hfv, hnp⟩)
    rw [hsplit, List.getElem?_append_left hi'] at hix
    exact List.mem_of_getElem? hix
  have hval : ∀ x gv, g.value? x = some gv → ∃ fv, f.value? x = some fv := fun x gv hgv => by
    have hsem := value_spec S.rel x
    unfold Site.valueOK at hsem
    cases h : f.value? x with
    | some fv => exact ⟨fv, rfl⟩
    | none => rw [h, hgv] at hsem; cases hsem
  have hargsT : ∀ x gv, g.value? x = some gv → ∀ a ∈ gv.args, a ∈ argsF (Ctx.make tabs g).f x :=
    fun x gv hgv a ha => by
      rw [show (Ctx.make tabs g).f = g from rfl, argsF_of hgv]; exact Array.mem_toList_iff.2 ha
  -- no root of `post` comes before `r` in the target
  have hnotroot : ∀ x ∈ pre', ∀ fv, f.value? x = some fv → s.postVal f x = true → fv.op ≠ .Phi →
      isRoot fv.op = false := by
    intro x hx fv hfv hxp hph
    cases hiso : isRoot fv.op with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨P2, hP2, hxP⟩ := postVal_iff.1 hxp
      rw [hP] at hP2; cases hP2
      have hxnp : npOf f P x = true := by
        simp [npOf, hxP, hfv, hph, prio_root hiso]
      have hxD : npOf f D x = false := Bool.eq_false_iff.2 fun h => by
        rw [S.np_disj hD hP x h] at hxnp; cases hxnp
      obtain ⟨jx, hjx⟩ := List.getElem?_of_mem hx
      have hjl : jx < pre'.length := (List.getElem?_eq_some_iff.1 hjx).1
      have hb : Order.Before oT.toList x r :=
        ⟨jx, pre'.length, hjl, by rw [hsplitT, List.getElem?_append_left hjl]; exact hjx, hk'⟩
      rw [← Order.before_filter (fun x => npOf f D x || npOf f P x) (by simp [hxnp])
        (by simp [hrnpD']), hseqA] at hb
      exact not_before_append (hseqA ▸ ondT.filter _)
        (List.mem_filter.2 ⟨List.mem_of_getElem? hk, hrnpD'⟩)
        (fun h => by rw [(List.mem_filter.1 h).2] at hxD; cases hxD) hb
  -- `MixOK` on the target's prefix
  have hmix : MixOK env (Ctx.make tabs g) Gp F pre' := by
    intro x hx
    have hxT := hpreT x hx
    obtain ⟨hxD', gv, hgv, hgnp⟩ := (omemT x).1 hxT
    obtain ⟨fv, hfv⟩ := hval x gv hgv
    obtain ⟨gv'', hgv'', hgid, -⟩ := hwg.valueId s.dom D' ⟨hdg, hD'⟩ x hxD'
    rw [hgv] at hgv''; cases hgv''
    refine ⟨fun hnFx => ?_, fun hFx g' hg' hdef => ?_⟩
    · -- a value of `dom`
      have hr := hreg x hxD'
      unfold Site.regionVal at hr
      have hxD : x ∈ D.values := by
        rcases Bool.or_eq_true_iff.1 hr with hr | hr
        · rcases Bool.or_eq_true_iff.1 hr with hr | hr
          · obtain ⟨D2, hD2, h2⟩ := domVal_iff.1 hr; rw [hD] at hD2; cases hD2; exact h2
          · exact absurd (.inl hr) hnFx
        · exact absurd (.inr hr) hnFx
      obtain ⟨gv', hgv', hsem, hty⟩ := hDsem x hxD fv hfv
      rw [hgv] at hgv'; cases hgv'
      have hnp : fv.op ≠ .Phi := fun h => hgnp (hsem.2.1 ▸ h)
      obtain ⟨v, y, hv, hy, hev⟩ := hGv x (hQ x hx fv hfv hxD hnp)
      change f.value? x = some v at hv
      rw [hfv] at hv; cases hv
      refine ⟨y, hy, fun g' hg' hag' _ => ?_⟩
      have hfid : fv.id = x := hsem.1 ▸ hgid
      rw [stepV_eq hgv]
      rw [evalValue_ctx_congr (ctxS := Ctx.make tabs f) (ctxT := Ctx.make tabs g) hsem hg'
        (fun a ha => hag' a (hargsT x gv hgv a (hsem.2.2.2.2 ▸ ha)) (hDargs x hxD fv hfv hnp a ha))
        (by rw [hfid, tys_of_value hfv, tys_of_value hgv, hty]) rfl hctxT rfl]
      exact hev
    · -- an arm or `post` value: speculation-safe
      rw [stepV_eq hgv]
      refine evalValue_specSafe ?_ fun a ha => hdef a (hargsT x gv hgv a ha)
      rcases hFx with hxa | hxp
      · obtain ⟨v, hv, hsafe, -⟩ := armVal_spec S.rel hxa
        rw [hfv] at hv; cases hv
        have hnp : s.postVal f x = false := Bool.eq_false_iff.2 fun hp' => by
          obtain ⟨P2, hP2, hzP⟩ := postVal_iff.1 hp'
          have := S.post_not_arm hP2 hzP; rw [hxa] at this; cases this
        obtain ⟨-, hv'⟩ := semEq_of S.rel fun _ _ h => by rw [hnp] at h; cases h
        obtain ⟨gv', hgv', -, hop⟩ := hv' fv hfv
        rw [hgv] at hgv'; cases hgv'
        rw [hop]; exact hsafe
      · obtain ⟨P2, hP2, hxP⟩ := postVal_iff.1 hxp
        rw [hP] at hP2; cases hP2
        by_cases hph : fv.op = .Phi
        · obtain ⟨gv', hgv', -, -, -, -, hop, -⟩ := condSel_of S.rel hfv hxp hph
          rw [hgv] at hgv'; cases hgv'
          rw [hop]; decide
        · obtain ⟨-, hv'⟩ := semEq_of S.rel fun fv' h _ => by rw [hfv] at h; cases h; exact hph
          obtain ⟨gv', hgv', -, hop⟩ := hv' fv hfv
          rw [hgv] at hgv'; cases hgv'
          obtain ⟨hna, hnar⟩ := (post_spec S.rel hP x hxP fv hfv).2 hph
          have hroot := hnotroot x hx fv hfv hxp hph
          rw [hop]
          simp [specSafeOp, hroot, hph, hna, hnar]
  have htopo' : TopoRem (argsF (Ctx.make tabs g).f) (pre' ++ r :: post') := hsplitT ▸ otopoT
  have hSd : ∀ a, a ∉ oT.toList → (∃ x ∈ oT.toList, a ∈ argsF (Ctx.make tabs g).f x) →
      ∃ z, (setPhis psT frT.regs)[a]? = some (some z) := by
    rintro a hna ⟨x, hx, hax⟩
    rw [hT0 a hna]
    by_cases haD : a ∈ D.values
    · obtain ⟨gv, hgv, -, -⟩ := hwg.valueId s.dom D' ⟨hdg, hD'⟩ a (hDin a haD)
      have hgph : gv.op = .Phi := Classical.byContradiction fun hne =>
        hna ((omemT a).2 ⟨hDin a haD, gv, hgv, hne⟩)
      obtain ⟨-, fv, hfv, hfph, -, -⟩ := S.merged_values hD hD' (hDin a haD) hgv hgph
      obtain ⟨-, y, -, -, hy⟩ := hGp a haD fv hfv hfph
      exact ⟨_, hy⟩
    · rw [hGo a haD]
      obtain ⟨hxD', gv, hgv, hgnp⟩ := (omemT x).1 hx
      have hout : s.regionVal f a = false := by
        have hd : (valsOf f s.dom).contains a = false := Bool.eq_false_iff.2 fun h => haD (by
          obtain ⟨D2, hD2, h2⟩ := domVal_iff.1 h; rw [hD] at hD2; cases hD2; exact h2)
        have hpv : s.postVal f a = false := Bool.eq_false_iff.2 fun h => hnotF a hna (.inr h)
        unfold Site.regionVal
        rw [hnoarmS a hna, hd, hpv]; rfl
      exact S.region_arg_def htd hdi (hreg x hxD') hgv hgnp
        (by rw [show (Ctx.make tabs g).f = g from rfl, argsF_of hgv] at hax
            exact Array.mem_toList_iff.1 hax) hout
  obtain ⟨grv, hgrv, hgrsem, hgrty⟩ := hDsem r hrD rv hrv
  obtain ⟨grv', hgrv', hgrid, -⟩ := hwg.valueId s.dom D' ⟨hdg, hD'⟩ r (hDin r hrD)
  rw [hgrv] at hgrv'; cases hgrv'
  have hpanT := evalAll_mix_panic (F := F) (post := post')
    (S := fun a => a ∉ oT.toList ∧ ∃ x ∈ oT.toList, a ∈ argsF (Ctx.make tabs g).f x)
    (by rw [hGs, hs, ← hgsz]; rfl) hmix
    (Dead.refOK_of_topo (topoRem_prefix htopo') fun x hx a ha hna => ⟨fun haT =>
        hna (topoRem_arg_prefix htopo' x hx a ha (hsplitT ▸ haT)), x, hpreT x hx, ha⟩)
    (fun a ha _ => hT0 a ha.1) (fun a ha => hSd a ha.1 ha.2) (with_regs_same hfr hGf _)
    (by show (setPhis psT frT.regs).size = Gp.regs.size; rw [setPhis_size, hsz, hGs])
    (fun a ha => by
      by_cases haT : a ∈ oT.toList
      · rw [hsplitT] at haT
        rcases List.mem_append.1 haT with h | h
        · exact .inr h
        · exact absurd h (CopyElim.topoRem_at htopo' a ha)
      · exact .inl ⟨haT, r, hrnode, ha⟩)
    (fun g' hg' hag' _ => by
      have hsrc : stepV env (Ctx.make tabs f) Gp r = .panic e m := hrp
      rw [stepV_eq hrv] at hsrc
      rw [stepV_eq hgrv]
      have hrid : rv.id = r := hgrsem.1 ▸ hgrid
      rw [evalValue_ctx_congr (ctxS := Ctx.make tabs f) (ctxT := Ctx.make tabs g) hgrsem hg'
        (fun a ha => hag' a (hargsT r grv hgrv a (hgrsem.2.2.2.2 ▸ ha))
          (hDargs r hrD rv hrv hrnp a ha))
        (by rw [hrid, tys_of_value hrv, tys_of_value hgrv, hgrty]) rfl hctxT rfl]
      exact hsrc)
  refine ⟨D', hD', ?_⟩
  rw [enterBlock_eq, hpsT]
  change (Res.ofOption _ ((Ctx.make tabs g).sched[D'.id]?).join).bind _ = _
  rw [hid', sched_of_block hD', hoT]
  change evalAll env (Ctx.make tabs g) _ oT.toList = _
  rw [hsplitT]
  exact hpanT

end Setup

end GoFV.Proof.BranchElim
