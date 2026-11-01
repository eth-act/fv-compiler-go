import GoFV.Proof.Pass.CSEBlockSpec

/-!
# cse: a block's `Phi`s

A block is entered from the entry or along edge `i` of a tree block `p` after which the frame
holds lemma (D) and `RepInv` for `p`'s ancestors (`Pre`). Then:

* `phis_target`: the target collects the source's `Phi`s (a target `Phi` reads the
  representative of the source's argument, `phiUse` places that argument in an ancestor of `p`,
  where `RepInv` makes the registers equal);
* `phis_repInv`: after setting them, a `Phi` replaced by another `Phi` of the block holds its
  representative's register (the two read arguments with one representative);
* `phis_strict`: lemma (D) and `RepInv` for the strict ancestors of the block still hold (the
  `Phi`s change no register of a strict ancestor's values).
-/

namespace GoFV.Proof.CSE

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Proof.CopyElim Dom

variable {tabs : Tables} {f g : Func} {rw : Array (Option ID)}

/-- How block `bid` is entered along edge `i` with frame `fr`: it is the entry, or a successor
of a tree block `p` after which `fr` holds lemma (D) and `RepInv` for `p`'s ancestors. -/
def Pre (env : Env) (tabs : Tables) (f : Func) (rw : Array (Option ID)) (fr : Frame) (bid : ID)
    (i : Nat) : Prop :=
  bid = f.entry ∨ ∃ p blkp, p ∈ f.blocks ∧ f.block? p = some blkp ∧
    ((make f).depthOf p).isSome ∧ (⟨bid, i⟩ : Edge) ∈ blkp.succs ∧
    DInv env (Ctx.make tabs f) (fun a => Anc (make f) a p) fr ∧
    RepInv f rw fr (fun a => Anc (make f) a p)

theorem pre_tree {ce : CheckEnv} (hwf : WF ce f) (hc : CertOK f) {env : Env} {fr : Frame}
    {bid : ID} {i : Nat} (h : Pre env tabs f rw fr bid i) : Tree f bid := by
  rcases h with rfl | ⟨p, blkp, hp, hpb, hpt, he, -⟩
  · exact ⟨hwf.entry, by simp [entry_depth hc.parents]⟩
  · obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 he
    exact ⟨(hwf.succLink p blkp ⟨hp, hpb⟩ j _ hj).1, (edge hc hp hpb hpt he).2.1⟩

/-- Lemma (D) and `RepInv` for the strict ancestors of the block entered. -/
theorem pre_strict (hc : CertOK f) {env : Env} {fr : Frame}
    {bid : ID} {i : Nat} (h : Pre env tabs f rw fr bid i) :
    DInv env (Ctx.make tabs f) (fun a => Anc (make f) a bid ∧ a ≠ bid) fr ∧
      RepInv f rw fr (fun a => Anc (make f) a bid ∧ a ≠ bid) := by
  rcases h with rfl | ⟨p, blkp, hp, hpb, hpt, he, hd, hr⟩
  · exact ⟨dinv_entry hc fr, fun _ _ _ ⟨ha, hne⟩ => absurd (anc_of_entry hc.parents ha) hne⟩
  · have hup : ∀ a, (Anc (make f) a bid ∧ a ≠ bid) → Anc (make f) a p := fun _ ⟨ha, hne⟩ =>
      Anc.trans hc.parents (ha.up hc.parents hne) (edge hc hp hpb hpt he).2.2
    exact ⟨hd.mono hup, fun x v hx hb => hr x v hx (hup _ hb)⟩

theorem argsRel_phi {fa ga : Array ID} (h : ArgsRel rw .Phi fa ga) :
    ga = fa.map (Opt.CSE.rep rw) := by
  rcases h with h | ⟨hc, -⟩
  · exact h
  · exact absurd hc (by decide)

/-- An argument of a listed value is placed. -/
theorem placed_arg {ce : CheckEnv} (hwf : WF ce f) {b : ID} {blk : Block} (hb : BlockIn f b blk)
    {x : ID} {v : Value} (hx : x ∈ blk.values) (hv : f.value? x = some v) {a : ID}
    (ha : a ∈ v.args) : ∃ va, Placed f a va ∧ blockOf f a = va.block := by
  obtain ⟨b', blk', hb', hab⟩ := hwf.argListed b blk x v ⟨hb, hx, hv⟩ a ha
  obtain ⟨va, hpl, -, -⟩ := placed_of_mem hwf hb'.1 hb'.2 hab
  exact ⟨va, hpl, blockOf_placed hpl⟩

/-- The argument a `Phi` reads holds its representative's register. -/
theorem phiArg_rep {ce : CheckEnv} (hwf : WF ce f) (hc : CertOK f) {env : Env} {fr : Frame}
    {bid : ID} {i : Nat} (hpre : Pre env tabs f rw fr bid i) (hbt : Tree f bid) {fb : Block}
    (hfb : f.block? bid = some fb) {z : ID} (hz : z ∈ fb.values) {fv : Value}
    (hfv : f.value? z = some fv) (hph : fv.op = .Phi) {a : ID} (ha : fv.args[i]? = some a) :
    fr.regs[Opt.CSE.rep rw a]? = fr.regs[a]? := by
  rcases hpre with hbe | ⟨p, blkp, hp, hpb, hpt, he, -, hrep⟩
  · have hsz := hwf.phiArity bid fb z fv ⟨⟨hbt.1, hfb⟩, hz, hfv⟩ hph
    have hilt := (Array.getElem?_eq_some_iff.1 ha).1
    subst hbe
    have := hwf.entryPreds fb hfb
    omega
  · obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 he
    obtain ⟨-, c, hcb, hcp⟩ := hwf.succLink p blkp ⟨hp, hpb⟩ j _ hj
    rw [hfb] at hcb; cases hcb
    have hanc := phiUse hc hbt.1 hfb hbt.2 hz hfv hph ha hcp hpt
    obtain ⟨va, hpl, hba⟩ := placed_arg hwf ⟨hbt.1, hfb⟩ hz hfv (Array.mem_of_getElem? ha)
    rw [hba] at hanc
    exact hrep a va hpl hanc

/-- One `Phi` step of the target gives the source's. -/
theorem phiStep_target {ce : CheckEnv} (hwf : WF ce f) (hc : CertOK f) (hrel : CRel tabs f g rw)
    {env : Env} {fr : Frame} {bid : ID} {i : Nat} (hpre : Pre env tabs f rw fr bid i)
    (hbt : Tree f bid) {fb : Block} (hfb : f.block? bid = some fb) {z : ID} (hz : z ∈ fb.values)
    {o : Option (ID × Val)} (h : phiStep (Ctx.make tabs f) fr i z = .ok o) :
    phiStep (Ctx.make tabs g) fr i z = .ok o := by
  obtain ⟨fv, hfv, -, -⟩ := hwf.valueId bid fb ⟨hbt.1, hfb⟩ z hz
  obtain ⟨gv, hgv, -, hop, -, -, hty, -, hargs⟩ := hrel.value z fv hfv
  cases o with
  | none =>
    obtain ⟨v, hv, hne⟩ := phiStep_none h
    change f.value? z = some v at hv
    rw [hfv] at hv; cases hv
    unfold phiStep
    simp only [show (Ctx.make tabs g).f = g from rfl, hgv,
      show (gv.op == .Phi) = false by simpa [hop] using hne]
    rfl
  | some q =>
    obtain ⟨hq1, v, a, y, hv, hph, ha, hy, hq2⟩ := phiStep_some h
    change f.value? z = some v at hv
    rw [hfv] at hv; cases hv
    rw [hph] at hargs
    have hga : gv.args[i]? = some (Opt.CSE.rep rw a) := by
      rw [argsRel_phi hargs, Array.getElem?_map, ha]; rfl
    have hra := phiArg_rep hwf hc hpre hbt hfb hz hfv hph ha
    have htys : (Ctx.make tabs g).tys[z]? = (Ctx.make tabs f).tys[z]? := by
      rw [tys_of_value hfv, tys_of_value hgv, hty]
    obtain ⟨z', x⟩ := q
    simp only at hq1 hq2
    subst hq1 hq2
    unfold phiStep
    simp only [show (Ctx.make tabs g).f = g from rfl, hgv,
      show (gv.op == .Phi) = true by simp [hop, hph], ite_true, hga, hra, hy, Option.join,
      htys]
    rfl

theorem filterMapM_transfer {F G : ID → Res (Option (ID × Val))} :
    ∀ {l : List ID} {ps : List (ID × Val)}, (∀ z ∈ l, ∀ o, F z = .ok o → G z = .ok o) →
      l.filterMapM F = .ok ps → l.filterMapM G = .ok ps
  | [], _, _, h => h
  | z :: l, ps, hz, h => by
    rw [List.filterMapM_cons] at h ⊢
    have hl := fun y hy => hz y (List.mem_cons_of_mem _ hy)
    cases hF : F z with
    | panic e m => rw [hF] at h; cases h
    | stuck msg => rw [hF] at h; cases h
    | ok o =>
      rw [hF] at h
      rw [hz z List.mem_cons_self o hF]
      cases o with
      | none => exact filterMapM_transfer hl h
      | some p =>
        change (List.filterMapM F l).bind (fun r => .ok (p :: r)) = .ok ps at h
        change (List.filterMapM G l).bind (fun r => .ok (p :: r)) = .ok ps
        cases hF' : List.filterMapM F l with
        | ok r => rw [hF'] at h; rw [filterMapM_transfer hl hF']; exact h
        | panic e m => rw [hF'] at h; cases h
        | stuck msg => rw [hF'] at h; cases h

/-- **The target collects the source's `Phi`s.** -/
theorem phis_target {ce : CheckEnv} (hwf : WF ce f) (hc : CertOK f) (hrel : CRel tabs f g rw)
    {env : Env} {fr : Frame} {bid : ID} {i : Nat} (hpre : Pre env tabs f rw fr bid i)
    {fb gb : Block} (hfb : f.block? bid = some fb) (hgb : g.block? bid = some gb)
    {ps : List (ID × Val)}
    (hps : fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) fr i) = .ok ps) :
    gb.values.toList.filterMapM (phiStep (Ctx.make tabs g) fr i) = .ok ps := by
  have hbt := pre_tree hwf hc hpre
  obtain ⟨gb', hgb', -, hv, -⟩ := hrel.block bid hbt.1 fb hfb
  rw [hgb] at hgb'; cases hgb'
  rw [hv]
  exact filterMapM_transfer (fun z hz o h =>
    phiStep_target hwf hc hrel hpre hbt hfb (Array.mem_toList_iff.1 hz) h) hps

/-- **After the `Phi`s, a replaced `Phi` holds its representative's register.** -/
theorem phis_repInv {ce : CheckEnv} (hwf : WF ce f) (hc : CertOK f) (hrel : CRel tabs f g rw)
    {env : Env} {fr : Frame} {bid : ID} {i : Nat} (hpre : Pre env tabs f rw fr bid i)
    {fb : Block} (hfb : f.block? bid = some fb) (hs : fr.regs.size = f.valueTab.size)
    {ps : List (ID × Val)}
    (hps : fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) fr i) = .ok ps) :
    ∀ z v, Placed f z v → v.block = bid → v.op = .Phi →
      (setPhis ps fr.regs)[Opt.CSE.rep rw z]? = (setPhis ps fr.regs)[z]? := by
  have hbt := pre_tree hwf hc hpre
  obtain ⟨-, -, -, hphiS⟩ := phis_spec (hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩) hps
  intro z v hz hvb hph
  cases hr : rw.getD z none with
  | none => simp [Opt.CSE.rep, hr]
  | some r =>
    have hrep : Opt.CSE.rep rw z = r := by simp [Opt.CSE.rep, hr]
    rw [hrep]
    obtain ⟨-, fx, frv, gx, gr, hfx, hfr, hgx, hgr, ⟨hop, -, -, htys, hargs⟩, -, hblk, -, blk,
      hblkr, hrb⟩ := hrel.subst z r hr
    obtain ⟨hzv, -, blk', hblk', hzb⟩ := hz
    rw [hzv] at hfx; cases hfx
    rw [hvb, hfb] at hblk'; cases hblk'
    have hrph : frv.op = .Phi := by rw [hop, hph]
    rw [hblk hph, hvb, hfb] at hblkr; cases hblkr
    have hga : gx.args = gr.args := by
      rcases hargs with h | ⟨-, -, (⟨h, -⟩ | h | ⟨h, -⟩)⟩
      · exact h
      all_goals rw [hph] at h; cases h
    obtain ⟨gx', hgx', -, -, -, -, -, -, hax⟩ := hrel.value z v hzv
    rw [hgx] at hgx'; cases hgx'
    obtain ⟨gr', hgr', -, -, -, -, -, -, har⟩ := hrel.value r frv hfr
    rw [hgr] at hgr'; cases hgr'
    rw [hph] at hax
    rw [hrph] at har
    obtain ⟨a, y, ha, hy, hz'⟩ := hphiS z hzb v hzv hph (by rw [hs]; exact lt_of_value? hzv)
    obtain ⟨a', y', ha', hy', hr'⟩ := hphiS r hrb frv hfr hrph (by rw [hs]; exact lt_of_value? hfr)
    have hreps : Opt.CSE.rep rw a = Opt.CSE.rep rw a' := by
      have e1 : gx.args[i]? = some (Opt.CSE.rep rw a) := by
        rw [argsRel_phi hax, Array.getElem?_map, ha]; rfl
      have e2 : gx.args[i]? = some (Opt.CSE.rep rw a') := by
        rw [hga, argsRel_phi har, Array.getElem?_map, ha']; rfl
      rw [e1] at e2; exact Option.some.inj e2
    have hyy : y' = y := by
      have := (phiArg_rep hwf hc hpre hbt hfb hrb hfr hrph ha').symm.trans
        ((congrArg (fr.regs[·]?) hreps).symm.trans (phiArg_rep hwf hc hpre hbt hfb hzb hzv hph ha))
      rw [hy', hy] at this
      exact Option.some.inj (Option.some.inj this)
    subst hyy
    rw [hr', hz', tys_of_value hfr, tys_of_value hzv, htys]

/-- **The `Phi`s keep lemma (D) and `RepInv` for the strict ancestors.** -/
theorem phis_strict {ce : CheckEnv} (hwf : WF ce f) (hc : CertOK f) (hrel : CRel tabs f g rw)
    {env : Env} {fr : Frame} {bid : ID} {i : Nat} (hpre : Pre env tabs f rw fr bid i)
    {fb : Block} (hfb : f.block? bid = some fb) {ps : List (ID × Val)}
    (hps : fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) fr i) = .ok ps) :
    DInv env (Ctx.make tabs f) (fun a => Anc (make f) a bid ∧ a ≠ bid)
        { fr with regs := setPhis ps fr.regs } ∧
      RepInv f rw { fr with regs := setPhis ps fr.regs }
        (fun a => Anc (make f) a bid ∧ a ≠ bid) := by
  have hp := hc.parents
  have hbt := pre_tree hwf hc hpre
  obtain ⟨hd, hr⟩ := pre_strict hc hpre
  obtain ⟨-, -, hkeep, -⟩ := phis_spec (hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩) hps
  have hout : ∀ z, z ∉ fb.values → (setPhis ps fr.regs)[z]? = fr.regs[z]? :=
    fun z hz => hkeep z (.inl hz)
  -- a value of the block is placed in the block
  have hin : ∀ z v, f.value? z = some v → z ∈ fb.values → v.block = bid := fun z v hv hz => by
    obtain ⟨v', hv', -, hvb⟩ := hwf.valueId bid fb ⟨hbt.1, hfb⟩ z hz
    rw [hv] at hv'; cases hv'; exact hvb
  have hnot : ∀ z v, f.value? z = some v → (Anc (make f) v.block bid ∧ v.block ≠ bid) →
      z ∉ fb.values := fun z v hv hb hz => hb.2 (hin z v hv hz)
  refine ⟨fun x v hx hb => ?_, fun x v hx hb => ?_⟩
  · obtain ⟨y, hy, hev⟩ := hd x v hx hb
    refine ⟨y, by rw [show ({ fr with regs := setPhis ps fr.regs } : Frame).regs = _ from rfl,
      hout x (hnot x v hx.1 hb), hy], fun hne => ?_⟩
    rw [← hev hne]
    refine (evalValue_congr rfl fun a ha => ?_).symm
    obtain ⟨hv, hvb, blk, hblk, hxv⟩ := hx
    have hua := uses hc hvb hblk (Anc.left hp hb.1) hxv hv hne ha
    refine (hout a fun ham => ?_).symm
    obtain ⟨va, hva, -, hvab⟩ := hwf.valueId bid fb ⟨hbt.1, hfb⟩ a ham
    have hba : blockOf f a = bid := by unfold blockOf; rw [hva]; exact hvab
    rw [hba] at hua
    exact hb.2 (Anc.antisymm hp hb.1 hua)
  · change (setPhis ps fr.regs)[Opt.CSE.rep rw x]? = (setPhis ps fr.regs)[x]?
    rw [hout x (hnot x v hx.1 hb), ← hr x v hx hb]
    apply hout
    cases hrw : rw.getD x none with
    | none => simpa [Opt.CSE.rep, hrw] using hnot x v hx.1 hb
    | some r =>
      have hrep : Opt.CSE.rep rw x = r := by simp [Opt.CSE.rep, hrw]
      rw [hrep]
      obtain ⟨-, fx, frv, -, -, hfx, hfr, -, -, -, -, -, hanc, -⟩ := hrel.subst x r hrw
      rw [hx.1] at hfx; cases hfx
      intro hrm
      have hrb := hin r frv hfr hrm
      have ha := (anc_iff hp).1 hanc
      rw [hrb] at ha
      exact hb.2 (Anc.antisymm hp hb.1 ha)

end GoFV.Proof.CSE
