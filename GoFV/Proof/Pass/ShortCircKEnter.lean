import GoFV.Proof.Pass.ShortCircKBlock

/-!
# Checked `shortcircuitBlock`: a checked block's entry

`kenter`/`kenter_panic`: entering a checked block (`B ∈ K`) along related edges in frames related
by the edge's facts, the target ends in a frame related to the source's by the block's end facts
(its registers outside `Delta` equal, each end fact holding), with controls holding the source's
controls' values; a panicking source entry panics alike in the target.
-/

namespace GoFV.Proof.ShortCirc

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.ShortCircuit GoFV.Proof Dom

theorem idx_lt_mem {l : List ID} (hnd : l.Nodup) {pre post : List ID} {r x : ID}
    (hl : l = pre ++ r :: post) (hx : x ∈ l) (hlt : l.idxOf x < l.idxOf r) : x ∈ pre := by
  have hr : l.idxOf r = pre.length := by
    have hlen : pre.length < l.length := by rw [hl]; simp
    have := List.Nodup.idxOf_getElem hnd pre.length hlen
    rw [show l[pre.length] = r by subst hl; simp] at this
    exact this
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  rw [List.Nodup.idxOf_getElem hnd i hi, hr] at hlt
  have : l[i] = pre[i] := by subst hl; simp [List.getElem_append_left hlt]
  rw [this]; exact List.getElem_mem hlt

section KEnter

variable {ce : CheckEnv} {tabs : Tables} {f g : Func} {s : Site} (S : Setup ce tabs f g s)
  {B : ID} {fB gB : Block} (hBm : B ∈ f.blocks) (hfB : f.block? B = some fB)
  (hgB : g.block? B = some gB) (hBK : B ∈ (infoOf tabs f g s).K)
  (hns : ¬ (gB.preds = #[] ∧ B = s.b)) {iT : Nat} (hiT : iT < max 1 gB.preds.size)
  {frS frT : Frame}
  (hrel : FactsRel (infoOf tabs f g s) f
    ((infoOf tabs f g s).edgeIn f (Info.factTab (infoOf tabs f g s) f g) B gB iT).2 frS frT)
  (hsrc : B ∈ (infoOf tabs f g s).region → SrcB (infoOf tabs f g s) frS)
  (hsS : frS.regs.size = f.valueTab.size) (hsz : frT.regs.size = frS.regs.size)
  (htyS : Typed (Ctx.make tabs f) frS) (hfrS : frT = { frS with regs := frT.regs })
include S hBm hfB hgB hBK hns hiT hrel hsrc hsS hsz htyS hfrS

set_option hygiene false in
local notation "𝓘" => infoOf tabs f g s
set_option hygiene false in
local notation "𝓣" => Info.factTab (infoOf tabs f g s) f g

/-- The checker's parts for block `B` (the case that is checked). -/
theorem kparts : fB.id = B ∧ gB.id = B ∧ gB.kind = fB.kind ∧ gB.controls.size = fB.controls.size ∧
    (B ∈ (𝓘).region ∨ B = s.b ∨ (((𝓘).factsOf 𝓣 B).1 = (𝓘).dflt ∧ ((𝓘).factsOf 𝓣 B).2 = (𝓘).dflt)) ∧
    (𝓘).newOK f fB gB = true ∧
    (𝓘).nodesOK f g fB gB ((𝓘).factsOf 𝓣 B).1 ((𝓘).factsOf 𝓣 B).2
      ((𝓘).region.contains B || B == s.b) = true ∧
    Info.schedOK f g fB gB = true ∧
    (𝓘).outOK f g fB gB ((𝓘).factsOf 𝓣 B).1 ((𝓘).factsOf 𝓣 B).2 = true ∧
    (𝓘).succOK fB gB B = true ∧
    (∀ (k : Nat) (c' c : ID), gB.controls[k]? = some c' → fB.controls[k]? = some c →
      (𝓘).argRel f g fB gB ((𝓘).factsOf 𝓣 B).1 ((𝓘).factsOf 𝓣 B).2 c' c = true) ∧
    ((𝓘).redir B iT = true ∨ fB.preds[((𝓘).edgeIn f 𝓣 B gB iT).1]? = gB.preds[iT]?) ∧
    (𝓘).phisOK f g fB gB ((𝓘).factsOf 𝓣 B).1 iT ((𝓘).edgeIn f 𝓣 B gB iT).1
      ((𝓘).edgeIn f 𝓣 B gB iT).2 ((𝓘).region.contains B) = true := by
  have hBg : B ∈ g.blocks := by rw [S.gblocks]; exact hBm
  obtain ⟨h1, h2, h3⟩ := blockOK_spec hBg hfB hgB (S.blockOK hBK)
  rcases h3 with h3 | ⟨h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  · exact absurd h3 hns
  · obtain ⟨h14, h15⟩ := h13 iT hiT
    exact ⟨h1, h2, h4, h5, h6, h7, h8, h9, h10, h11, h12, h14, h15⟩

theorem hbv_of : B = s.b → ∀ v ∈ (𝓘).vs, v ∈ fB.values := by
  intro hb v hv
  obtain ⟨Bb, hBb, -, -, hvals, -⟩ := S.pre
  subst hb
  rw [hfB] at hBb; cases hBb
  rw [hvals]; exact (S.vs_mem hv).1

/-- **Entering a checked block**: the target's entry succeeds where the source's does. -/
theorem kenter {env : Env} {G : Frame}
    (h : enterBlock env (Ctx.make tabs f) frS fB ((𝓘).edgeIn f 𝓣 B gB iT).1 = .ok G) :
    ∃ GT, enterBlock env (Ctx.make tabs g) frT gB iT = .ok GT ∧ GT = { G with regs := GT.regs } ∧
      GT.regs.size = G.regs.size ∧ G.regs.size = f.valueTab.size ∧
      FactsRel (𝓘) f ((𝓘).outOf 𝓣 B) G GT ∧
      (B ∈ (𝓘).region ∨ B = s.b → SrcB (𝓘) G) ∧
      Typed (Ctx.make tabs f) G ∧
      ∀ (k : Nat) (c' c : ID), gB.controls[k]? = some c' → fB.controls[k]? = some c →
        ∀ y, G.regs[c]? = some (some y) → GT.regs[c']? = some (some y) := by
  obtain ⟨hfid, hgid, -, -, -, hnew, hnodes, hsch, houtok, -, hctl, -, hph⟩ :=
    kparts S hBm hfB hgB hBK hns hiT hrel hsrc hsS hsz htyS hfrS
  have hBg : B ∈ g.blocks := by rw [S.gblocks]; exact hBm
  have hbv := hbv_of S hBm hfB hgB hBK hns hiT hrel hsrc hsS hsz htyS hfrS
  have hndf := S.wf.valuesNodup B fB ⟨hBm, hfB⟩
  have hndg := S.wfg.valuesNodup B gB ⟨hBg, hgB⟩
  have hsrc' : (𝓘).region.contains B = true → SrcB (𝓘) frS := fun h => hsrc (contains_iff.1 h)
  -- the source
  obtain ⟨PS, o, ho, hev, hPf, hPs, -, hPk, hPp⟩ := enterBlock_spec hndf h
  have hPS : PhiData tabs f fB _ frS PS := ⟨hPf, hPs, hPk, hPp⟩
  rw [hfid, sched_of_block hfB] at ho
  obtain ⟨ond, otopo, omem⟩ := schedule_topo (valuesOwn S.wf hBm hfB) hndf ho
  obtain ⟨e1, e2, e3, e4⟩ := evalAll_spec ond otopo (by rw [hPs, hsS]; rfl) hev
  -- the target's `Phi`s
  obtain ⟨ps, hps⟩ := phisT_ok S hBm hfB hgB hph hrel hsrc' hPS hsS hsz
  have hPT := phiData_of (tabs := tabs) hndg hps
  -- the target's schedule
  obtain ⟨oS', oT, hoS', hoT, -⟩ := SCI.schedOK_spec hsch
  rw [ho] at hoS'; cases hoS'
  obtain ⟨tnd, ttopo, tmem⟩ := schedule_topo (valuesOwn S.wfg hBg hgB) hndg hoT
  have hOT : ∀ x, x ∈ oT.toList ↔ x ∈ Info.nodesOf g gB := fun x =>
    (tmem x).trans (mem_nodesOf_iff S.wfg hBg hgB).symm
  have hOS : ∀ x, x ∈ o.toList ↔ x ∈ Info.nodesOf f fB := fun x =>
    (omem x).trans (mem_nodesOf_iff S.wf hBm hfB).symm
  have hinRb : ((𝓘).region.contains B || B == s.b) = true →
      (𝓘).region.contains B = true ∨ B = s.b := by
    intro h; simpa using h
  have hPTs : ({ frT with regs := setPhis ps frT.regs } : Frame).regs.size = g.valueTab.size := by
    rw [hPT.size, hsz, hsS, S.gvsize]
  -- evaluate the target's non-`Phi`s against `G`
  have hloc := fun x (hx : x ∈ oT.toList) =>
    node_loc S hBm hfB hgB hph hrel hsrc' hPS hsS hsz hPT htyS hnodes hnew hinRb hbv hfrS e1 e2
      (Done := (· ∈ o.toList)) (fun x hx => (hOS x).1 hx)
      (fun x hx => by obtain ⟨v, y, hv, hy, hev⟩ := e4 x hx; exact ⟨v, y, hv, hy, hev⟩)
      (fun z hz => e3 z hz) (env := env) ((hOT x).1 hx)
      (fun hxf hxp => (hOS x).2 (mem_nodesOf.2 ⟨hxf, hxp⟩))
  obtain ⟨GT, hGT, k1, k2, k3, k4⟩ := evalAll_map (ctx := Ctx.make tabs g)
    (O := (· ∈ Info.nodesOf g gB)) hPTs (D := fun _ => False) tnd ttopo
    (fun x hx => ⟨id, (hOT x).1 hx, hloc x hx⟩)
    (fun x _ a _ hOa => .inr ((hOT a).2 hOa)) (fun _ h => h.elim)
    ⟨rfl, rfl, fun _ h => h.elim, fun _ _ => rfl⟩
  have henter : enterBlock env (Ctx.make tabs g) frT gB iT = .ok GT := by
    rw [enterBlock_eq, hps]
    show (Res.ofOption _ ((Ctx.make tabs g).sched[gB.id]?).join).bind _ = _
    rw [hgid, sched_of_block hgB, hoT]
    exact hGT
  -- `G`'s registers
  have hGP : ∀ z, z ∉ Info.nodesOf f fB → G.regs[z]? = PS.regs[z]? := fun z hz =>
    e3 z (fun h => hz ((hOS z).1 h))
  have hGTin : ∀ x ∈ Info.nodesOf g gB, ∃ z, GT.regs[x]? = some (some z) ∧
      ∀ y, expOf (𝓘) f g fB ((𝓘).factsOf 𝓣 B).2 G x = some y → z = y :=
    fun x hx => k3 x (.inr ((hOT x).2 hx))
  have hGTout : ∀ x, x ∉ Info.nodesOf g gB → GT.regs[x]? = (setPhis ps frT.regs)[x]? :=
    fun x hx => k4 x (fun h => h.elim id (fun hm => hx ((hOT x).1 hm)))
  have postR := fun {w a : ID} (hp : (𝓘).pinRel f g fB gB ((𝓘).factsOf 𝓣 B).1 w a = true)
      (hl : Listed f a) (hn : a ∉ Info.nodesOf f fB) =>
    post_rel S hBm hfB hgB hph hrel hsrc' hPS hsS hsz hPT htyS hp hl hn hnew
  have postP := fun {v w : ID} (hl : (𝓘).look ((𝓘).factsOf 𝓣 B).1 v = some w) =>
    post_pin S hBm hfB hgB hph hrel hsrc' hPS hsS hsz hPT htyS hl
  have pvD := fun {v : ID} (hv : v ∈ (𝓘).vs) (hin : (𝓘).region.contains B = true ∨ B = s.b) =>
    pv_def S hBm hfB hgB hph hrel hsrc' hPS hsS hsz hPT htyS hbv hv hin
  have hvnd : ∀ v ∈ (𝓘).vs, v ∉ Info.nodesOf f fB := fun v hv h => by
    have := (mem_nodesOf.1 h).2; rw [(S.vs_mem hv).2.2] at this; cases this
  refine ⟨GT, henter, ?_, ?_, by rw [e2, hPs, hsS], ⟨fun x hx => ?_, fun v w hvw => ?_⟩,
    fun hin v hv => ?_, typed_enter S.wf hBm hfB hsS htyS h, fun k c' c hc' hc y hy => ?_⟩
  · exact ((SameAct.of k1).trans ((SameAct.of hPT.frame).trans ((SameAct.of hfrS).trans
      ((SameAct.of e1).trans (SameAct.of hPf)).symm))).eq
  · rw [k2, hPT.size, hsz, e2, hPs]
  · -- registers outside `Delta`
    have hxb : x ∉ (𝓘).bvals := fun h => hx (.inl h)
    have hxl : Listed f x := Classical.byContradiction fun h => hx (.inr h)
    by_cases hxs : x ∈ Info.nodesOf f fB
    · obtain ⟨hxg, hh⟩ := (SCI.nodesOK_spec _ hnodes).1 x hxs
      obtain ⟨-, y, -, hy, -⟩ := e4 x ((hOS x).2 hxs)
      obtain ⟨z, hz, hze⟩ := hGTin x hxg
      rw [hz, hy, hze y (by simp only [expOf, hh, Option.bind_some, hy, Option.join_some])]
    · have hxg : x ∉ Info.nodesOf g gB := fun h => by
        obtain ⟨hxv, hxp⟩ := mem_nodesOf.1 h
        rcases SCI.newOK_spec _ hnew x hxv with hxf | hxb' | hlx
        · have hpf : isPhiIn f x = true := by
            cases hp : isPhiIn f x
            · exact absurd (mem_nodesOf.2 ⟨hxf, hp⟩) hxs
            · rfl
          obtain ⟨-, hY, -⟩ := SCI.phisOK_spec _ hph
          rcases (hY x hxf hpf).1 hxv with hpg | ⟨hb, -⟩
          · rw [hxp] at hpg; cases hpg
          · exact hxb hb
        · exact hxb hxb'
        · rw [listedIn_of S.wf hxl] at hlx; cases hlx
      rw [hGTout x hxg, hGP x hxs]
      exact postR (w := x) (a := x) ((SCI.pinRel_iff _).2 (.inl ⟨rfl, (SCI.idPost_iff _).2 (.inl hxb)⟩))
        hxl hxs
  · -- the end facts
    have hvm := SCI.look_mem _ hvw
    obtain ⟨ho1, ho2⟩ := SCI.outOK_spec _ houtok v hvm w hvw
    by_cases hwn : w ∈ Info.nodesOf g gB
    · have hh := ho1 hwn
      obtain ⟨yv, hyv⟩ : ∃ yv, PS.regs[v]? = some (some yv) := by
        rcases SCI.home_eq_some _ hh with ⟨-, hp, rfl⟩ | ⟨hns', hinv, ⟨hwf, rfl⟩ | ⟨hwf, -, -⟩⟩
        · rw [(S.vs_mem hvm).2.2] at hp; cases hp
        · obtain ⟨-, -, y, -, -, -, -, h⟩ := src_phi S hBm hfB hgB hph hrel hsrc' hPS hsS hsz hwf
            (S.vs_mem hvm).2.2
          exact ⟨_, h⟩
        · have hspec := SCI.nodeOK_spec _ ((SCI.nodesOK_spec _ hnodes).2 w hwn)
          obtain ⟨-, -, hinb, -⟩ := SCI.carrierOK_spec _ (hspec.2.2.2 hns' hinv hwf)
          exact pvD hvm (hinRb hinb)
      obtain ⟨z, hz, hze⟩ := hGTin w hwn
      rw [hz, hGP v (hvnd v hvm), hyv,
        hze yv (by simp only [expOf, hh, Option.bind_some, hGP v (hvnd v hvm), hyv, Option.join_some])]
    · rw [hGTout w hwn, postP (ho2 hwn), hGP v (hvnd v hvm)]
  · -- `b`'s other phis are defined
    obtain ⟨y, hy⟩ := pvD hv (by
      rcases hin with h | h
      · exact .inl (contains_iff.2 h)
      · exact .inr h)
    exact ⟨y, by rw [hGP v (hvnd v hv), hy]⟩
  · -- the controls
    rcases (SCI.argRel_iff _).1 (hctl k c' c hc' hc) with ⟨hcn, hh⟩ | ⟨hcn, hcs, hp⟩
    · obtain ⟨z, hz, hze⟩ := hGTin c' hcn
      rw [hz, hze y (by simp only [expOf, hh, Option.bind_some, hy, Option.join_some])]
    · have hcl : Listed f c := S.wf.ctrlListed B fB ⟨hBm, hfB⟩ c (Array.mem_of_getElem? hc)
      rw [hGTout c' hcn, postR hp hcl hcs, ← hGP c hcs, hy]

/-- **Entering a checked block that panics in the source** panics alike in the target. -/
theorem kenter_panic {env : Env} {e : Panic} {m : Mem}
    (h : enterBlock env (Ctx.make tabs f) frS fB ((𝓘).edgeIn f 𝓣 B gB iT).1 = .panic e m) :
    enterBlock env (Ctx.make tabs g) frT gB iT = .panic e m := by
  obtain ⟨hfid, hgid, -, -, -, hnew, hnodes, hsch, -, -, -, -, hph⟩ :=
    kparts S hBm hfB hgB hBK hns hiT hrel hsrc hsS hsz htyS hfrS
  have hBg : B ∈ g.blocks := by rw [S.gblocks]; exact hBm
  have hbv := hbv_of S hBm hfB hgB hBK hns hiT hrel hsrc hsS hsz htyS hfrS
  have hndf := S.wf.valuesNodup B fB ⟨hBm, hfB⟩
  have hndg := S.wfg.valuesNodup B gB ⟨hBg, hgB⟩
  have hsrc' : (𝓘).region.contains B = true → SrcB (𝓘) frS := fun h => hsrc (contains_iff.1 h)
  -- the source
  rw [enterBlock_eq] at h
  cases hpsS : fB.values.toList.filterMapM (phiStep (Ctx.make tabs f) frS
      ((𝓘).edgeIn f 𝓣 B gB iT).1) with
  | panic e' m' => exact absurd hpsS filterMapM_phi_not_panic
  | stuck msg => rw [hpsS] at h; cases h
  | ok psS =>
  rw [hpsS] at h
  change (Res.ofOption _ ((Ctx.make tabs f).sched[fB.id]?).join).bind _ = _ at h
  rw [hfid, sched_of_block hfB] at h
  cases ho : schedule f fB with
  | none => rw [ho] at h; cases h
  | some o =>
  rw [ho] at h
  change evalAll env (Ctx.make tabs f) _ o.toList = .panic e m at h
  have hPS := phiData_of (tabs := tabs) hndf hpsS
  obtain ⟨ond, otopo, omem⟩ := schedule_topo (valuesOwn S.wf hBm hfB) hndf ho
  have hOS : ∀ x, x ∈ o.toList ↔ x ∈ Info.nodesOf f fB := fun x =>
    (omem x).trans (mem_nodesOf_iff S.wf hBm hfB).symm
  obtain ⟨pre, r, post, Gp, hsplit, hpre, hr⟩ := evalAll_panic_split h
  have hndp : pre.Nodup := by rw [hsplit] at ond; exact (List.nodup_append.1 ond).1
  have htp : TopoRem (argsF f) pre := by rw [hsplit] at otopo; exact topoRem_prefix otopo
  obtain ⟨e1, e2, e3, e4⟩ := evalAll_spec (ctx := Ctx.make tabs f) hndp htp
    (by rw [hPS.size, hsS]; rfl) hpre
  have hrm : r ∈ o.toList := by rw [hsplit]; simp
  have hrs := (hOS r).1 hrm
  obtain ⟨fr, hfr⟩ : ∃ fr, f.value? r = some fr := by
    obtain ⟨hrv, v, hv, -⟩ := (mem_nodesOf_iff S.wf hBm hfB).1 hrs; exact ⟨v, hv⟩
  have hrev : evalValue env (Ctx.make tabs f) Gp fr = .panic e m := by
    unfold stepV at hr; rw [show (Ctx.make tabs f).f = f from rfl, hfr] at hr; exact hr
  -- the target's `Phi`s and schedule
  obtain ⟨ps, hps⟩ := phisT_ok S hBm hfB hgB hph hrel hsrc' hPS hsS hsz
  have hPT := phiData_of (tabs := tabs) hndg hps
  obtain ⟨oS', oT, hoS', hoT, hord⟩ := SCI.schedOK_spec hsch
  rw [ho] at hoS'; cases hoS'
  obtain ⟨tnd, ttopo, tmem⟩ := schedule_topo (valuesOwn S.wfg hBg hgB) hndg hoT
  have hOT : ∀ x, x ∈ oT.toList ↔ x ∈ Info.nodesOf g gB := fun x =>
    (tmem x).trans (mem_nodesOf_iff S.wfg hBg hgB).symm
  have hinRb : ((𝓘).region.contains B || B == s.b) = true →
      (𝓘).region.contains B = true ∨ B = s.b := by
    intro h; simpa using h
  have hPTs : ({ frT with regs := setPhis ps frT.regs } : Frame).regs.size = g.valueTab.size := by
    rw [hPT.size, hsz, hsS, S.gvsize]
  have hrT : r ∈ oT.toList := (hOT r).2 ((SCI.nodesOK_spec _ hnodes).1 r hrs).1
  obtain ⟨preT, postT, hTsplit⟩ := List.append_of_mem hrT
  -- a source value the target lists before `r` the source lists before `r`
  have hprio : prio (f.getV r).op ≠ 0 := by
    rw [getV_of hfr]; exact prio_panicking (evalValue_panic_op hrev)
  have hbefore : ∀ x ∈ preT, x ∈ Info.nodesOf f fB → x ∈ pre := by
    intro x hx hxs
    let p : ID → Bool := fun x => (Info.nodesOf f fB).contains x
    have hpr : p r = true := contains_iff.2 hrs
    have hL : oT.toList.filter p = preT.filter p ++ r :: postT.filter p := by
      rw [hTsplit, List.filter_append, List.filter_cons_of_pos hpr]
    have hxf : x ∈ preT.filter p := List.mem_filter.2 ⟨hx, contains_iff.2 hxs⟩
    obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hxf
    have hk : (oT.toList.filter p)[(preT.filter p).length]? = some r := by rw [hL]; simp
    have hjL : (oT.toList.filter p)[j]? = some x := by
      rw [hL, List.getElem?_append_left hj, List.getElem?_eq_getElem hj, hjx]
    have := hord _ r hk hprio j x hj hjL
    exact idx_lt_mem ond hsplit ((hOS x).2 hxs) this
  have hloc := fun x (hx : x ∈ preT) =>
    node_loc S hBm hfB hgB hph hrel hsrc' hPS hsS hsz hPT htyS hnodes hnew hinRb hbv hfrS e1 e2
      (Done := (· ∈ pre)) (fun x hx => (hOS x).1 (by rw [hsplit]; exact List.mem_append_left _ hx))
      (fun x hx => by obtain ⟨v, y, hv, hy, hev⟩ := e4 x hx; exact ⟨v, y, hv, hy, hev⟩)
      (fun z hz => e3 z hz) (env := env)
      ((hOT x).1 (by rw [hTsplit]; exact List.mem_append_left _ hx))
      (fun hxf hxp => hbefore x hx (mem_nodesOf.2 ⟨hxf, hxp⟩))
  have hrsn : r ∈ fB.values ∧ isPhiIn f r = false := mem_nodesOf.1 hrs
  have hpanic := evalAll_map_panic (ctx := Ctx.make tabs g) (O := (· ∈ Info.nodesOf g gB))
    (exp := expOf (𝓘) f g fB ((𝓘).factsOf 𝓣 B).2 Gp) hPTs (pre := preT) (post := postT) (r := r)
    (by rw [← hTsplit]; exact tnd) (by rw [← hTsplit]; exact ttopo)
    (fun x hx => ⟨(hOT x).1 (by rw [hTsplit]; exact List.mem_append_left _ hx), hloc x hx⟩)
    (fun a ha => by rw [← hTsplit]; exact (hOT a).2 ha)
    (fun gr hgr hout hin => by
      rw [src_node_step S hBm hfB hgB hph hrel hsrc' hPS hsS hsz hPT htyS hnodes hnew hinRb hbv hfrS
        e1 e2 (Done := (· ∈ pre)) (fun x hx => (hOS x).1 (by rw [hsplit]; exact List.mem_append_left _ hx))
        (fun x hx => by obtain ⟨v, y, hv, hy, hev⟩ := e4 x hx; exact ⟨v, y, hv, hy, hev⟩)
        (fun z hz => e3 z hz) hrsn hfr (by rw [hrev]; nofun) hgr hout hin, hrev])
  rw [enterBlock_eq, hps]
  show (Res.ofOption _ ((Ctx.make tabs g).sched[gB.id]?).join).bind _ = _
  rw [hgid, sched_of_block hgB, hoT]
  show evalAll env (Ctx.make tabs g) _ oT.toList = _
  rw [hTsplit]
  exact hpanic

end KEnter

end GoFV.Proof.ShortCirc
