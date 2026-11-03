import GoFV.Proof.Pass.MoveLPhase
import GoFV.Proof.AvailL
import GoFV.Proof.DomRel

/-!
# Related block entries for `refinesL_of_move`

`St`: the simulation relation at a block entry (same block, same edge) — frames equal but for
the registers, lemma (D) on both sides, and agreement of related registers on available values
(`Agree`) of some dominance-closed sets covering the block's strict dominators and the arguments
its `Phi`s read along the edge. `enter_phis`: after the `Phi`s, the strict dominators' values and
the block's `Phi`s (`X0`) are available on both sides and agree; `ready_block`: a block's schedule
is a dependency order after them.
-/

namespace GoFV.Proof.MoveL

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Proof Dom

variable {ok : Array Bool} {f g : Func} {tabs : Tables} {md : LMode} {env : Env}

/-- What `refinesL_of_move` assumes: both functions well formed with dominator certificates, and
the validator with certificate `ok` accepts. -/
structure Setup (ok : Array Bool) (f g : Func) : Prop where
  wf : ∃ ce, WF ce f
  wg : ∃ ce, WF ce g
  cf : CertOK f
  cg : CertOK g
  mv : moveWith ok f g = true

/-- Value `a` is placed in a block of `A`. -/
def PlacedIn (h : Func) (A : ID → Prop) (a : ID) : Prop := ∃ v, Placed h a v ∧ A v.block

/-- The values available at the entry of block `b` (table entry `hb`) of `h` after its `Phi`s:
those placed in strict dominators of `b`, and `b`'s `Phi`s. -/
def X0 (h : Func) (hb : Block) (b : ID) (a : ID) : Prop :=
  (∃ v, Placed h a v ∧ Anc (make h) v.block b ∧ v.block ≠ b) ∨
    (a ∈ hb.values ∧ ∃ v, h.value? a = some v ∧ v.op = .Phi)

/-- **The simulation relation** at the entry of block `b` along edge `i`. -/
def St (ok : Array Bool) (f g : Func) (tabs : Tables) (md : LMode) (env : Env) (frS frT : Frame)
    (b : ID) (i : Nat) : Prop :=
  b ∈ f.blocks ∧ ((make f).depthOf b).isSome ∧ ((make g).depthOf b).isSome ∧
  frT = { frS with regs := frT.regs } ∧ frS.regs.size = f.valueTab.size ∧
  frT.regs.size = g.valueTab.size ∧
  DInvL md env (Ctx.makeL tabs f) (fun a => Anc (make f) a b ∧ a ≠ b) frS ∧
  DInvL md env (Ctx.makeL tabs g) (fun a => Anc (make g) a b ∧ a ≠ b) frT ∧
  ∃ AS AT : ID → Prop, (∀ a, Anc (make f) a b ∧ a ≠ b → AS a) ∧
    (∀ a, Anc (make g) a b ∧ a ≠ b → AT a) ∧
    Agree ok f g (PlacedIn g AT) (PlacedIn f AS) frT frS ∧
    (∀ blk x v a, f.block? b = some blk → x ∈ blk.values → f.value? x = some v → v.op = .Phi →
      v.args[i]? = some a → PlacedIn f AS a) ∧
    (∀ blk x v a, g.block? b = some blk → x ∈ blk.values → g.value? x = some v → v.op = .Phi →
      v.args[i]? = some a → PlacedIn g AT a)

/-! ## The validator -/

theorem moveWith_spec (h : moveWith ok f g = true) :
    g.entry = f.entry ∧ g.blocks = f.blocks ∧ g.ownAux = f.ownAux ∧ g.lowered = f.lowered ∧
      certValid ok f g = true ∧ ∀ b ∈ f.blocks, blockOK ok f g b = true := by
  unfold moveWith at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem blockOK_spec {b : ID} (h : blockOK ok f g b = true) :
    ∃ fb gb oT oS, f.block? b = some fb ∧ g.block? b = some gb ∧ gb.kind = fb.kind ∧
      gb.auxInt = fb.auxInt ∧ gb.succs = fb.succs ∧ gb.preds = fb.preds ∧
      gb.controls = fb.controls ∧ (∀ c ∈ gb.controls, okAt ok c = true) ∧
      (∀ x ∈ gb.values, valueOK ok g fb x = true) ∧ schedule g gb = some oT ∧
      schedule f fb = some oS ∧ orderOK ok f g oT.toList oS.toList = true := by
  unfold blockOK at h
  cases hf : f.block? b with
  | none => rw [hf] at h; cases h
  | some fb =>
  cases hg : g.block? b with
  | none => rw [hf, hg] at h; cases h
  | some gb =>
  rw [hf, hg] at h
  simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hk, hai⟩, hsu⟩, hpr⟩, hct⟩, hcok⟩, hvals⟩, hord⟩ := h
  cases hoT : schedule g gb with
  | none => rw [hoT] at hord; cases hord
  | some oT =>
  cases hoS : schedule f fb with
  | none => rw [hoT, hoS] at hord; cases hord
  | some oS =>
  rw [hoT, hoS] at hord
  exact ⟨fb, gb, oT, oS, rfl, rfl, hk, hai, hsu, hpr, hct, hcok, hvals, hoT, hoS, hord⟩

theorem valueOK_spec {fb : Block} {x : ID} (h : valueOK ok g fb x = true) :
    ∃ gv, g.value? x = some gv ∧ (gv.op = .Phi → okAt ok x = true ∧ x ∈ fb.values) ∧
      (gv.op ≠ .Phi → totalOp gv.op = true ∨ (okAt ok x = true ∧ x ∈ fb.values)) := by
  unfold valueOK at h
  cases hg : g.value? x with
  | none => rw [hg] at h; cases h
  | some gv =>
  rw [hg] at h
  dsimp only at h
  refine ⟨gv, rfl, fun hp => ?_, fun hp => ?_⟩
  · rw [ite_eq_left (by rw [hp]; decide)] at h
    simp only [Bool.and_eq_true, Array.contains_iff_mem] at h
    exact h
  · rw [ite_eq_right (by simpa using hp)] at h
    simp only [Bool.or_eq_true, Bool.and_eq_true, Array.contains_iff_mem] at h
    exact h

theorem before_eq {r : ID} : ∀ {pre post : List ID}, r ∉ pre → before (pre ++ r :: post) r = pre
  | [], post, _ => by simp [before]
  | y :: pre, post, h => by
    have hy : y ≠ r := fun e => h (e ▸ List.mem_cons_self)
    have ih := before_eq (pre := pre) (post := post) (fun hm => h (List.mem_cons_of_mem _ hm))
    unfold before at ih ⊢
    simp [List.takeWhile_cons, hy, ih]

theorem orderOK_spec {oT oS : List ID} (h : orderOK ok f g oT oS = true) {r : ID} (hr : r ∈ oS)
    (hp : mayPanic f r = true) :
    okAt ok r = true ∧ r ∈ oT ∧ ∀ x ∈ before oT r, nonTotal g x = true → x ∈ before oS r := by
  unfold orderOK at h
  have := List.all_eq_true.1 h r hr
  simp only [hp, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.contains_iff_mem,
    List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at this
  obtain ⟨⟨h1, h2⟩, h3⟩ := this
  refine ⟨h1, h2, fun x hx hn => ?_⟩
  rcases h3 x hx with h | h
  · rw [hn] at h; cases h
  · exact h

/-! ## Dominance facts -/

theorem placed_of_listed {ce : CheckEnv} {h : Func} (hwf : WF ce h) {a : ID}
    (ha : Listed h a) : ∃ v, Placed h a v ∧ blockOf h a = v.block := by
  obtain ⟨bid, b, ⟨hbm, hbb⟩, hab⟩ := ha
  obtain ⟨v, hp, -, -⟩ := placed_of_mem hwf hbm hbb hab
  exact ⟨v, hp, blockOf_placed hp⟩

theorem placed_val {h : Func} {x : ID} {v w : Value} (hp : Placed h x v) (hw : h.value? x = some w) :
    w = v := by
  rw [hp.1] at hw; cases hw; rfl

/-- The table entry of a placed value has its ID. -/
theorem placed_id {ce : CheckEnv} {h : Func} (hwf : WF ce h) {x : ID} {v : Value}
    (hP : Placed h x v) : v.id = x := by
  obtain ⟨hv, hbm, blk, hblk, hxv⟩ := hP
  obtain ⟨w, hw, hwid, -⟩ := hwf.valueId _ blk ⟨hbm, hblk⟩ x hxv
  rw [hv] at hw; cases hw; exact hwid

/-- A value placed outside block `b` is not listed in `b`. -/
theorem not_mem_of_placed {ce : CheckEnv} {h : Func} (hwf : WF ce h) {x : ID} {v : Value}
    (hp : Placed h x v) {b : ID} {hb : Block} (hbm : b ∈ h.blocks) (hbb : h.block? b = some hb)
    (hne : v.block ≠ b) : x ∉ hb.values := fun hx => by
  obtain ⟨-, hvb, blk, hblk, hxv⟩ := hp
  exact hne (hwf.valueOnce _ _ _ _ ⟨hvb, hblk⟩ ⟨hbm, hbb⟩ x hxv hx)

/-- A value listed in block `b` is placed there. -/
theorem placed_in {ce : CheckEnv} {h : Func} (hwf : WF ce h) {b : ID} {hb : Block}
    (hbm : b ∈ h.blocks) (hbb : h.block? b = some hb) {x : ID} (hx : x ∈ hb.values) :
    ∃ v, h.value? x = some v ∧ v.id = x ∧ v.block = b ∧ Placed h x v := by
  obtain ⟨v, hv, hid, hvb⟩ := hwf.valueId b hb ⟨hbm, hbb⟩ x hx
  exact ⟨v, hv, hid, hvb, hv, hvb ▸ hbm, hb, hvb ▸ hbb, hx⟩

/-- The arguments of a non-`Phi` placed in a strict dominator of `b` are placed in strict
dominators of `b`. -/
theorem strict_args {ce : CheckEnv} {h : Func} (hwf : WF ce h) (hc : CertOK h) {b : ID} {x : ID}
    {v : Value} (hp : Placed h x v) (ha : Anc (make h) v.block b) (hne : v.block ≠ b)
    (hph : v.op ≠ .Phi) {a : ID} (hm : a ∈ v.args) :
    ∃ va, Placed h a va ∧ Anc (make h) va.block b ∧ va.block ≠ b := by
  have hD := hc.domRel
  obtain ⟨hv, hvb, blk, hblk, hxv⟩ := hp
  obtain ⟨va, hpa, hba⟩ := placed_of_listed hwf
    (hwf.argListed _ blk x v ⟨⟨hvb, hblk⟩, hxv, hv⟩ a hm)
  have hu := hD.uses hvb hblk (hD.left ha) hxv hv hph hm
  rw [hba] at hu
  exact ⟨va, hpa, hD.trans hu ha, fun he => hne (hD.antisymm ha (he ▸ hu))⟩

/-- The arguments of a non-`Phi` listed in block `b` are placed in strict dominators of `b`,
or listed in `b`. -/
theorem block_args {ce : CheckEnv} {h : Func} (hwf : WF ce h) (hc : CertOK h) {b : ID}
    {hb : Block} (hbm : b ∈ h.blocks) (hbb : h.block? b = some hb)
    (ht : ((make h).depthOf b).isSome) {x : ID} {v : Value} (hx : x ∈ hb.values)
    (hv : h.value? x = some v) (hph : v.op ≠ .Phi) {a : ID} (hm : a ∈ v.args) :
    (∃ va, Placed h a va ∧ Anc (make h) va.block b ∧ va.block ≠ b) ∨ a ∈ hb.values := by
  have hD := hc.domRel
  obtain ⟨va, hpa, hba⟩ := placed_of_listed hwf (hwf.argListed _ hb x v ⟨⟨hbm, hbb⟩, hx, hv⟩ a hm)
  have hu := hD.uses hbm hbb ht hx hv hph hm
  rw [hba] at hu
  by_cases he : va.block = b
  · obtain ⟨-, -, blk, hblk, hab⟩ := hpa
    rw [he, hbb] at hblk; cases hblk
    exact .inr hab
  · exact .inl ⟨va, hpa, hu, he⟩

/-- **A block's schedule is a dependency order** after its strict dominators' values and `Phi`s. -/
theorem ready_block {ce : CheckEnv} {h : Func} (hwf : WF ce h) (hc : CertOK h) {b : ID}
    {hb : Block} (hbm : b ∈ h.blocks) (hbb : h.block? b = some hb)
    (ht : ((make h).depthOf b).isSome) {o : Array ID} (ho : schedule h hb = some o) :
    Ready (argsF h) (fun y => ∃ v, h.value? y = some v ∧ v.id = y ∧ v.op ≠ .Phi) (X0 h hb b)
      o.toList ∧ ∀ y, y ∈ o.toList ↔ y ∈ hb.values ∧ ∃ v, h.value? y = some v ∧ v.op ≠ .Phi := by
  have hnd := hwf.valuesNodup b hb ⟨hbm, hbb⟩
  obtain ⟨ond, otopo, omem⟩ := schedule_topo (valuesOwn hwf hbm hbb) hnd ho
  refine ⟨ready_of ond otopo (fun y hy a ha => ?_) (fun y hy hx => ?_) (fun y hy => ?_), omem⟩
  · obtain ⟨hyb, v, hv, hph⟩ := (omem y).1 hy
    rw [argsF_of hv] at ha
    rcases block_args hwf hc hbm hbb ht hyb hv hph (Array.mem_toList_iff.1 ha) with h' | h'
    · exact .inl (.inl h')
    · obtain ⟨va, hva, -, -, -⟩ := placed_in hwf hbm hbb h'
      by_cases hp : va.op = .Phi
      · exact .inl (.inr ⟨h', va, hva, hp⟩)
      · exact .inr ((omem a).2 ⟨h', va, hva, hp⟩)
  · obtain ⟨hyb, v, hv, hph⟩ := (omem y).1 hy
    rcases hx with ⟨w, hpw, -, hne⟩ | ⟨-, w, hw, hp⟩
    · obtain ⟨v', hv', -, hvb, -⟩ := placed_in hwf hbm hbb hyb
      rw [placed_val hpw hv'] at hvb
      exact hne hvb
    · rw [hv] at hw; cases hw; exact hph hp
  · obtain ⟨hyb, -⟩ := (omem y).1 hy
    obtain ⟨v, hv, hid, -, -⟩ := placed_in hwf hbm hbb hyb
    obtain ⟨-, v', hv', hph⟩ := (omem y).1 hy
    rw [hv] at hv'; cases hv'
    exact ⟨v, hv, hid, hph⟩

theorem Ready.mono_mem {D : ID → List ID} {P P' : ID → Prop} :
    ∀ {l : List ID} {X : ID → Prop}, (∀ y ∈ l, P y → P' y) → Ready D P X l → Ready D P' X l
  | [], _, _, _ => trivial
  | y :: l, _, hPP, ⟨hp, hn, ha, hr⟩ =>
    ⟨hPP y List.mem_cons_self hp, hn, ha,
      Ready.mono_mem (fun z hz => hPP z (List.mem_cons_of_mem _ hz)) hr⟩

theorem Agree.mono {XT XS XT' XS' : ID → Prop} {frT frS : Frame}
    (h : Agree ok f g XT XS frT frS) (hT : ∀ x, XT' x → XT x) (hS : ∀ y, XS' y → XS y) :
    Agree ok f g XT' XS' frT frS :=
  fun x y hx hy hr => h x y (hT x hx) (hS y hy) hr

/-! ## After the `Phi`s -/

/-- After the `Phi`s of block `b`, the strict dominators' values and the `Phi`s are available. -/
theorem av_X0 {ce : CheckEnv} {h : Func} (hwf : WF ce h) (hc : CertOK h) {b : ID} {hb : Block}
    (hbm : b ∈ h.blocks) (hbb : h.block? b = some hb) {fr : Frame} {i : Nat}
    {ps : List (ID × Val)} (hs : fr.regs.size = h.valueTab.size)
    (hd : DInvL md env (Ctx.makeL tabs h) (fun a => Anc (make h) a b ∧ a ≠ b) fr)
    (hps : hb.values.toList.filterMapM (phiStepL md (Ctx.makeL tabs h) fr i) = .ok ps) :
    Av md env (Ctx.makeL tabs h) (X0 h hb b) { fr with regs := setPhis ps fr.regs } ∧
      Closed h (X0 h hb b) := by
  have hcf : (Ctx.makeL tabs h).f = h := makeL_f tabs h
  obtain ⟨-, -, hun, hphi⟩ := phisL_spec (hwf.valuesNodup b hb ⟨hbm, hbb⟩) hps
  rw [hcf] at hun hphi
  refine ⟨fun a ha => ?_, fun x v hx hv hp a hm => ?_⟩
  · rcases ha with ⟨v, hpv, hanc, hne⟩ | ⟨hab, v, hv, hph⟩
    · obtain ⟨y, hy, hre⟩ := hd a v (by rw [hcf]; exact hpv) ⟨hanc, hne⟩
      refine ⟨v, y, by rw [hcf]; exact hpv.1, placed_id hwf hpv,
        by rw [hun a (.inl (not_mem_of_placed hwf hpv hbm hbb hne))]; exact hy, fun hp => ?_⟩
      have hargs : ∀ c ∈ v.args, fr.regs[c]? = (setPhis ps fr.regs)[c]? := fun c hc' => by
        obtain ⟨vc, hpc, -, hnec⟩ := strict_args hwf hc hpv hanc hne hp hc'
        exact (hun c (.inl (not_mem_of_placed hwf hpc hbm hbb hnec))).symm
      exact (evalValueL_congr rfl hargs).symm.trans (hre hp)
    · obtain ⟨v', hv', hid, -, -⟩ := placed_in hwf hbm hbb hab
      rw [hv] at hv'; cases hv'
      obtain ⟨-, y, -, -, hy⟩ := hphi a hab v hv hph (hs ▸ lt_of_value? hv)
      exact ⟨v, _, by rw [hcf]; exact hv, hid, hy, fun hne => absurd hph hne⟩
  · rcases hx with ⟨w, hpw, hanc, hne⟩ | ⟨-, w, hw, hph⟩
    · have e := placed_val hpw hv
      subst e
      exact .inl (strict_args hwf hc hpw hanc hne hp hm)
    · rw [hv] at hw; cases hw; exact absurd hph hp

/-- **Related block entries, after the `Phi`s**: the target's `Phi`s read registers, and the
strict dominators' values and the `Phi`s of both sides agree. -/
theorem enter_phis {ce ce' : CheckEnv} (hwf : WF ce f) (hwg : WF ce' g) (hcf : CertOK f)
    (hcg : CertOK g) (H : Hyp ok f g md) {frS frT : Frame} {b : ID} {i : Nat}
    (hR : St ok f g tabs md env frS frT b i) {fb gb : Block} (hfb : f.block? b = some fb)
    (hgb : g.block? b = some gb) (hbg : b ∈ g.blocks)
    (hvals : ∀ x ∈ gb.values, valueOK ok g fb x = true) {ps : List (ID × Val)}
    (hps : fb.values.toList.filterMapM (phiStepL md (Ctx.makeL tabs f) frS i) = .ok ps) :
    ∃ psT, gb.values.toList.filterMapM (phiStepL md (Ctx.makeL tabs g) frT i) = .ok psT ∧
      Av md env (Ctx.makeL tabs f) (X0 f fb b) { frS with regs := setPhis ps frS.regs } ∧
      Closed f (X0 f fb b) ∧
      Av md env (Ctx.makeL tabs g) (X0 g gb b) { frT with regs := setPhis psT frT.regs } ∧
      Closed g (X0 g gb b) ∧
      Agree ok f g (X0 g gb b) (X0 f fb b) { frT with regs := setPhis psT frT.regs }
        { frS with regs := setPhis ps frS.regs } := by
  obtain ⟨hb, htf, htg, hfr, hsS, hsT, hdS, hdT, AS, AT, hAS, hAT, hag, hphS, hphT⟩ := hR
  have hcF : (Ctx.makeL tabs f).f = f := makeL_f tabs f
  have hcG : (Ctx.makeL tabs g).f = g := makeL_f tabs g
  -- the source's `Phi`s read registers
  obtain ⟨-, hsome, hall⟩ := filterMapM_phiL hps
  have hSphi : ∀ x ∈ fb.values, ∀ fv, f.value? x = some fv → fv.op = .Phi →
      ∃ a w, fv.args[i]? = some a ∧ frS.regs[a]? = some (some w) := by
    intro x hx fv hfv hp
    rcases hall x (Array.mem_toList_iff.2 hx) with ⟨q, hq, rfl⟩ | hn
    · obtain ⟨-, v, a, y, hv, -, ha, hy, -⟩ := phiStepL_some (hsome q hq)
      rw [hcF, hfv] at hv; cases hv
      exact ⟨a, y, ha, hy⟩
    · obtain ⟨v, hv, hne⟩ := phiStepL_none hn
      rw [hcF, hfv] at hv; cases hv; exact absurd hp hne
  -- a target `Phi` and its source: their arguments along `i` agree
  have hpair : ∀ x ∈ gb.values, ∀ gv, g.value? x = some gv → gv.op = .Phi →
      ∃ fv a a' w, f.value? x = some fv ∧ fv.op = .Phi ∧ x ∈ fb.values ∧ gv.type = fv.type ∧
        fv.args[i]? = some a ∧ gv.args[i]? = some a' ∧ frS.regs[a]? = some (some w) ∧
        frT.regs[a']? = some (some w) := by
    intro x hx gv hgv hp
    obtain ⟨gv', hgv', hphi, -⟩ := valueOK_spec (hvals x hx)
    rw [hgv] at hgv'; cases hgv'
    obtain ⟨hok, hxf⟩ := hphi hp
    obtain ⟨gv', fv, hgv', hfv, hop, hty, hsz, hrel, -, -⟩ := okLocal_spec (okLocal_of H.cert hok)
    rw [hgv] at hgv'; cases hgv'
    have hfp : fv.op = .Phi := hop ▸ hp
    obtain ⟨a, w, ha, hw⟩ := hSphi x hxf fv hfv hfp
    have hif : i < fv.args.size := (Array.getElem?_eq_some_iff.1 ha).1
    have hig : i < gv.args.size := hsz ▸ hif
    have ha' : gv.args[i]? = some gv.args[i] := by simp [hig]
    have hae : fv.args[i] = a := (Array.getElem?_eq_some_iff.1 ha).2
    have hr := hrel i hig hif
    rw [hae] at hr
    have hx' := hag _ _ (hphT gb x gv _ hgb hx hgv hp ha') (hphS fb x fv a hfb hxf hfv hfp ha) hr
    exact ⟨fv, a, gv.args[i], w, hfv, hfp, hxf, hty, ha, ha', hw, hx'.trans hw⟩
  -- the target's `Phi`s
  obtain ⟨psT, hpsT⟩ := filterMapM_phiL_ok (md := md) (ctx := Ctx.makeL tabs g) (fr := frT)
    (i := i) (l := gb.values.toList) fun z hz => by
      have hz' := Array.mem_toList_iff.1 hz
      obtain ⟨gv, hgv, -, -, -⟩ := placed_in hwg hbg hgb hz'
      by_cases hp : gv.op = .Phi
      · obtain ⟨-, -, a', w, -, -, -, -, -, ha', -, hw⟩ := hpair z hz' gv hgv hp
        refine ⟨some (z, md.retype ((Ctx.makeL tabs g).tys[z]?.getD .other) w), ?_⟩
        unfold phiStepL
        rw [hcG, hgv]
        simp [hp, ha', hw]
      · refine ⟨none, ?_⟩
        unfold phiStepL
        rw [hcG, hgv]
        simp [hp]
  obtain ⟨hAvS, hclS⟩ := av_X0 hwf hcf hb hfb hsS hdS hps
  obtain ⟨hAvT, hclT⟩ := av_X0 hwg hcg hbg hgb hsT hdT hpsT
  refine ⟨psT, hpsT, hAvS, hclS, hAvT, hclT, ?_⟩
  obtain ⟨-, -, hunS, hphiS⟩ := phisL_spec (hwf.valuesNodup b fb ⟨hb, hfb⟩) hps
  obtain ⟨-, -, hunT, hphiT⟩ := phisL_spec (hwg.valuesNodup b gb ⟨hbg, hgb⟩) hpsT
  rw [hcF] at hunS hphiS
  rw [hcG] at hunT hphiT
  intro x y hx hy hrel
  rcases hx with ⟨gv, hpg, hancg, hneg⟩ | ⟨hxb, gv, hgv, hgph⟩
  · rcases hy with ⟨fv, hpf, hancf, hnef⟩ | ⟨hyb, fv, hfv, hfph⟩
    · show (setPhis psT frT.regs)[x]? = (setPhis ps frS.regs)[y]?
      rw [hunT x (.inl (not_mem_of_placed hwg hpg hbg hgb hneg)),
        hunS y (.inl (not_mem_of_placed hwf hpf hb hfb hnef))]
      exact hag x y ⟨gv, hpg, hAT _ ⟨hancg, hneg⟩⟩ ⟨fv, hpf, hAS _ ⟨hancf, hnef⟩⟩ hrel
    · obtain ⟨rfl, hok⟩ := rel_phi_right hrel hfv hfph
      obtain ⟨gv', fv', hgv', hfv', hop, -, -, -, hblk, -⟩ := okLocal_spec (okLocal_of H.cert hok)
      rw [hpg.1] at hgv'; cases hgv'
      rw [hfv] at hfv'; cases hfv'
      obtain ⟨fv', hfv', -, hfb', -⟩ := placed_in hwf hb hfb hyb
      rw [hfv] at hfv'; cases hfv'
      exact absurd ((hblk (hop.trans hfph)).trans hfb') hneg
  · obtain ⟨rfl, -⟩ := rel_phi_left hrel hgv hgph
    obtain ⟨fv, a, a', w, hfv, hfph, hxf, hty, ha, ha', hw, hw'⟩ := hpair x hxb gv hgv hgph
    obtain ⟨c', w1, hc', hw1, hT⟩ := hphiT x hxb gv hgv hgph (by rw [hsT]; exact lt_of_value? hgv)
    obtain ⟨c, w2, hc, hw2, hS⟩ := hphiS x hxf fv hfv hfph (by rw [hsS]; exact lt_of_value? hfv)
    rw [ha'] at hc'; cases hc'
    rw [ha] at hc; cases hc
    rw [hw'] at hw1; cases hw1
    rw [hw] at hw2; cases hw2
    show (setPhis psT frT.regs)[x]? = (setPhis ps frS.regs)[x]?
    rw [hT, hS, tys_eq (tabs := tabs) H hgv hfv hty]

end GoFV.Proof.MoveL
