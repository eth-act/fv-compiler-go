import GoFV.Proof.Pass.ShortCircB
import GoFV.Proof.SimIH
import GoFV.Proof.Pass.ShortCircUseDom

variable [GoFV.SSA.Sem.Addrs]

/-!
# Checked `shortcircuitBlock` refines

`refines_of_step`: macro-step simulation (`runLoop_simIH`) with the relation `R`: the same block,
the source's edge index and the edge's facts given by `edgeIn` (`FactsRel`), the default facts
on edges into blocks outside `K`, `b`'s other phis defined in the plan's blocks (`SrcB`), and the
source invariants `Typed`, `ArglessInv`. A block outside `K` steps alike (`ostep`), a checked block
by `kenter`; at `p`, when the source takes the edge to `b`, it continues through `b` to `t`
(`bstep`) while the target takes the redirected edge to `t`. The result keeps `WFDom`
(`wfg`, `useDom_g`: `ShortCircPres`, `ShortCircUseDom`).
-/

namespace GoFV.Proof.ShortCirc

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.ShortCircuit GoFV.Proof Dom

/-- A terminator whose control 0 holds the source's value continues alike. -/
theorem stepTerm_ctl {G GT : Frame} {B BT : Block} (hk : BT.kind = B.kind)
    (hctl : ∀ v, Sem.control G B 0 = .ok v → Sem.control GT BT 0 = .ok v)
    {n : Next} (h : stepTerm G B = .ok n) :
    (∃ k e, n = .goto e ∧ B.succs[k]? = some e ∧ stepTerm GT BT = succ BT k) ∨
    (∃ rs m, n = .ret rs m ∧ stepTerm GT BT = .ok (.ret rs m)) := by
  have hgo : ∀ k, succ B k = .ok n → stepTerm GT BT = succ BT k →
      (∃ k e, n = .goto e ∧ B.succs[k]? = some e ∧ stepTerm GT BT = succ BT k) ∨
      (∃ rs m, n = .ret rs m ∧ stepTerm GT BT = .ok (.ret rs m)) := by
    intro k hs ht
    obtain ⟨e, he, rfl⟩ := Dead.succ_ok hs
    exact .inl ⟨k, e, rfl, he, ht⟩
  revert hgo
  cases hb : B.kind <;> intro hgo <;> have hb' := hk.trans hb <;> unfold stepTerm at h <;>
    simp only [hb] at h
  all_goals first
    | (cases h; done)
    | exact hgo 0 h (by unfold stepTerm; rw [hb'])
    | (cases hc0 : Sem.control G B 0 with
        | ok v =>
          rw [hc0] at h
          simp only [bind, Res.bind] at h
          have hT := hctl v hc0
          split at h
          all_goals first
            | (cases h; done)
            | exact hgo _ h (by unfold stepTerm; rw [hb', hT]; rfl)
            | (split at h
               · split at h
                 · cases h
                 · cases h
                   refine .inr ⟨_, _, rfl, ?_⟩
                   unfold stepTerm; rw [hb', hT]; simp only [bind, Res.bind]; simp_all
               · cases h)
        | panic e m => rw [hc0] at h; cases h
        | stuck msg => rw [hc0] at h; cases h)

namespace SCI

variable (I : Info) {f g : Func} {T : FactTab}

theorem edge_norm {B : ID} {gB : Block} {iT : Nat} (hr : I.redir B iT = false) {P : ID} {k : Nat}
    (hp : gB.preds[iT]? = some ⟨P, k⟩) : I.edgeIn f T B gB iT = (I.srcIdx B iT, I.outOf T P) := by
  unfold Info.edgeIn; rw [hr, hp]; rfl

theorem edge_redir {B : ID} {gB : Block} {iT : Nat} (hr : I.redir B iT = true) :
    I.edgeIn f T B gB iT = (I.s.te.i, I.einX f T) := by
  unfold Info.edgeIn; rw [hr]; rfl

theorem factsOf_out {B : ID} (hB : B ∉ I.K) : I.factsOf T B = (I.dflt, I.dflt) := by
  unfold Info.factsOf
  rw [show I.K.contains B = false by simpa [contains_iff] using hB]; rfl

end SCI

namespace Setup

variable {ce : CheckEnv} {tabs : Tables} {f g : Func} {s : Site} (S : Setup ce tabs f g s)
include S

set_option hygiene false in
local notation "𝓘" => infoOf tabs f g s
set_option hygiene false in
local notation "𝓣" => Info.factTab (infoOf tabs f g s) f g

/-- The simulation relation (see the module doc). -/
def Rel (tabs : Tables) (f g : Func) (s : Site) (env : Env) (frS : Frame) (bS iS : Nat) (frT : Frame) (bT iT : Nat) : Prop :=
  bT = bS ∧ bS ∈ f.blocks ∧ ∃ gB, g.block? bS = some gB ∧ iT < max 1 gB.preds.size ∧
    ¬ (gB.preds = #[] ∧ bS = s.b) ∧ iS = ((𝓘).edgeIn f 𝓣 bS gB iT).1 ∧
    FactsRel (𝓘) f ((𝓘).edgeIn f 𝓣 bS gB iT).2 frS frT ∧
    (bS ∉ (𝓘).K → ∀ v, (𝓘).look (𝓘).dflt v = some v →
      (𝓘).look ((𝓘).edgeIn f 𝓣 bS gB iT).2 v = some v) ∧
    (bS ∈ (𝓘).region → SrcB (𝓘) frS) ∧ frS.regs.size = f.valueTab.size ∧
    frT.regs.size = frS.regs.size ∧ Typed (Ctx.make tabs f) frS ∧
    ZCSE.ArglessInv env (Ctx.make tabs f) frS ∧ frT = { frS with regs := frT.regs }

theorem tyOf_same {x y : ID} {vx vy : Value} (hx : f.value? x = some vx) (hy : f.value? y = some vy)
    (ht : (𝓘).tyEq vx.type vy.type = true) : tyOf tabs f x = tyOf tabs f y := by
  rw [tyOf_shape (I := 𝓘) (tabs := tabs) rfl hx, tyOf_shape (I := 𝓘) (tabs := tabs) rfl hy,
    tyEq_shape ht]

theorem blockOf_f {B : ID} (hBm : B ∈ f.blocks) : ∃ fB, f.block? B = some fB := by
  obtain ⟨b, hb, -⟩ := S.wf.blockId B hBm; exact ⟨b, hb⟩

/-- **The relation after a normal edge** `B → e.b` (target edge `e'`). -/
theorem R_next {env : Env} {B : ID} {gB : Block} (hBm : B ∈ f.blocks) (hgB : g.block? B = some gB)
    {k : Nat} {e e' : Edge} (he' : gB.succs[k]? = some e') (hb : e'.b = e.b)
    (hi : e.i = (𝓘).srcIdx e.b e'.i) (hr : (𝓘).redir e'.b e'.i = false) {G GT : Frame}
    (hrel : FactsRel (𝓘) f ((𝓘).outOf 𝓣 B) G GT)
    (hdf : e.b ∉ (𝓘).K → ∀ v, (𝓘).look (𝓘).dflt v = some v →
      (𝓘).look ((𝓘).outOf 𝓣 B) v = some v)
    (hsrc : e.b ∈ (𝓘).region → SrcB (𝓘) G) (hs : G.regs.size = f.valueTab.size)
    (hsz : GT.regs.size = G.regs.size) (hty : Typed (Ctx.make tabs f) G)
    (hA : ZCSE.ArglessInv env (Ctx.make tabs f) G) (hfr : GT = { G with regs := GT.regs }) :
    Rel tabs f g s env G e.b e.i GT e'.b e'.i := by
  have hBg : B ∈ g.blocks := by rw [S.gblocks]; exact hBm
  obtain ⟨hm, gC, hgC, hpr⟩ := S.wfg.succLink B gB ⟨hBg, hgB⟩ k e' he'
  have hlt : e'.i < gC.preds.size := (Array.getElem?_eq_some_iff.1 hpr).1
  have hed := SCI.edge_norm (𝓘) (T := 𝓣) (f := f) hr hpr
  rw [hb] at hgC hed hm
  refine ⟨hb, by rw [← S.gblocks]; exact hm, gC, hgC, by omega, fun h => by
    rw [h.1] at hlt; simp at hlt, ?_, ?_, ?_, hsrc, hs, hsz, hty, hA, hfr⟩
  · rw [hed]; simpa [hb] using hi
  -- `dsimp only` reduces the `(…, …).snd` that `rw` leaves; without it `exact` unfolded
  -- `outOf`/`factsOf` in the unifier for ~3.5 s each (#1)
  · rw [hed]; dsimp only; exact hrel
  · rw [hed]; dsimp only; exact hdf

omit S in
theorem ctl_rel {fB gB : Block} {G GT : Frame} (hcsz : gB.controls.size = fB.controls.size)
    (hctl : ∀ (k : Nat) (c' c : ID), gB.controls[k]? = some c' → fB.controls[k]? = some c →
      ∀ y, G.regs[c]? = some (some y) → GT.regs[c']? = some (some y)) :
    ∀ v, Sem.control G fB 0 = .ok v → Sem.control GT gB 0 = .ok v := by
  intro v h
  unfold Sem.control at h ⊢
  cases hc : fB.controls[0]? with
  | none => rw [hc] at h; cases h
  | some c =>
    rw [hc] at h
    have hlt : 0 < gB.controls.size := by rw [hcsz]; exact (Array.getElem?_eq_some_iff.1 hc).1
    have hc' : gB.controls[0]? = some gB.controls[0] := by simp [hlt]
    rw [hc']
    simp only at h ⊢
    cases hr : G.regs[c]? with
    | none => rw [hr] at h; simp [Res.ofOption] at h
    | some o =>
      cases o with
      | none => rw [hr] at h; simp [Res.ofOption] at h
      | some y =>
        rw [hr] at h; simp only [Option.join_some, Res.ofOption] at h
        have hv := Res.ok.inj h; subst hv
        rw [hctl 0 _ c hc' hc _ hr]; rfl

/-- A normal edge into a plan block comes from a plan block or `b`. -/
theorem pred_in_region {B : ID} {gB : Block} (hBm : B ∈ f.blocks) (hgB : g.block? B = some gB)
    {k : Nat} {e' : Edge} (he' : gB.succs[k]? = some e') (hr : (𝓘).redir e'.b e'.i = false)
    (hreg : e'.b ∈ (𝓘).region) : B ∈ (𝓘).region ∨ B = s.b := by
  have hBg : B ∈ g.blocks := by rw [S.gblocks]; exact hBm
  obtain ⟨hm, gC, hgC, hpr⟩ := S.wfg.succLink B gB ⟨hBg, hgB⟩ k e' he'
  rcases (S.region_spec hreg).2.2.2 ⟨B, k⟩ (by rw [getB_of hgC]; exact Array.mem_of_getElem? hpr)
    with h | h | ⟨h1, h2⟩
  · exact .inl h
  · exact .inr h
  · exfalso
    obtain ⟨hp1, hp2⟩ := Edge.mk.inj h2
    obtain ⟨-, hrt⟩ := S.redir_spec
    rw [← h1, getB_of hgC] at hrt
    obtain ⟨-, P, hP, hPs⟩ := S.wfg.predLink e'.b gC ⟨hm, hgC⟩ _ _ hrt
    rw [← hp1, hgB] at hP; cases hP
    rw [← hp2, he'] at hPs
    have := (Option.some.inj hPs)
    rw [Edge.mk.injEq] at this
    have := (SCI.redir_iff _).2 ⟨h1, this.2⟩
    rw [hr] at this; cases this

/-- **The relation at `t` after the source went `p → b → t`.** -/
theorem R_redir {env : Env} {G GT G' : Frame} (hGTf : GT = { G with regs := GT.regs })
    (hGTs : GT.regs.size = G.regs.size) (hGs : G.regs.size = f.valueTab.size)
    (hfacts : FactsRel (𝓘) f ((𝓘).outOf 𝓣 s.p) G GT) (htyG : Typed (Ctx.make tabs f) G)
    (hkeep : ∀ z, z ∉ (𝓘).bvals → G'.regs[z]? = G.regs[z]?)
    (hvs : ∀ v ∈ (𝓘).vs, ∃ a y, (f.getV v).args[s.cidx]? = some a ∧ G.regs[a]? = some (some y) ∧
      G'.regs[v]? = some (some (y.retype (tyOf tabs f v))))
    (htyG' : Typed (Ctx.make tabs f) G') (hAG' : ZCSE.ArglessInv env (Ctx.make tabs f) G')
    (hG'f : G' = { G with regs := G'.regs }) (hG's : G'.regs.size = G.regs.size) :
    Rel tabs f g s env G' s.te.b s.te.i GT s.te.b (𝓘).tn := by
  obtain ⟨hsz, hrt⟩ := S.redir_spec
  obtain ⟨Bb, hBb, hbm, hbid, hvals, hkind, -, -, -, -, -, -, top, cv, chain, par, c, cc, htop, hcsz,
    hcv, hcvp, hctlm, hch, hcc, hcc', hccop, hccargs, hsucc, -⟩ := S.pre
  obtain ⟨j, hj⟩ : ∃ j, Bb.succs[j]? = some s.te := ⟨_, hsucc⟩
  obtain ⟨htm, -⟩ := S.wf.succLink s.b Bb ⟨hbm, hBb⟩ j s.te hj
  have htg : s.te.b ∈ g.blocks := by rw [S.gblocks]; exact htm
  obtain ⟨gt, hgt, -⟩ := S.wfg.blockId s.te.b htg
  rw [getB_of hgt] at hsz hrt
  have hred : (𝓘).redir s.te.b (𝓘).tn = true := (SCI.redir_iff _).2 ⟨rfl, rfl⟩
  have hed := SCI.edge_redir (𝓘) (f := f) (T := 𝓣) (gB := gt) hred
  refine ⟨rfl, htm, gt, hgt, by omega, fun h => by rw [h.1] at hsz; exact absurd hsz (by simp),
    by rw [hed]; rfl,
    ?_, fun h => absurd S.tK h, fun _ v hv => ?_, by rw [hG's, hGs], by rw [hGTs, hG's],
    htyG', hAG', ((SameAct.of hGTf).trans (SameAct.of hG'f).symm).eq⟩
  · rw [hed]
    refine ⟨fun x hx => ?_, fun v w hvw => ?_⟩
    · rw [hfacts.1 x hx, hkeep x fun h => hx (.inl h)]
    · have hvm := SCI.look_mem _ hvw
      have h := look_map_eq _ hvw
      obtain ⟨a, y, ha, hy, hv'⟩ := hvs v hvm
      simp only [infoOf_s] at h
      simp only [ha] at h
      split at h
      · rename_i htyq
        obtain ⟨fv, hfv, -⟩ := isPhiIn_iff.1 (S.vs_mem hvm).2.2
        have hvb : v ∈ Bb.values := by rw [hvals]; exact (S.vs_mem hvm).1
        have hla : Listed f a := argListed_of S.wf hbm hBb hvb hfv (by
          rw [getV_of hfv] at ha; exact args_get_mem ha)
        obtain ⟨fa, hfa⟩ := value_of_listed S.wf hla
        rw [getV_of hfa, getV_of hfv] at htyq
        rw [SCI.trans_rel _ hfacts h hla, hy, hv', ← S.tyOf_same hfa hfv htyq, typed_fix htyG hy]
      · contradiction
  · obtain ⟨a, y, h1, h2, h3⟩ := hvs v hv
    exact ⟨_, h3⟩

/-- **One step of the simulation.** -/
theorem sim_step {env : Env} (n : Nat)
    (ih : SimUpTo env (Ctx.make tabs f) (Ctx.make tabs g) (Rel tabs f g s env) n)
    {frS frT : Frame} {bS iS bT iT : Nat} (hR : Rel tabs f g s env frS bS iS frT bT iT)
    (hd : (runLoop env (Ctx.make tabs f) (n + 1) frS bS iS).Defined) :
    ∃ fuelT, LoopRefines Eq (runLoop env (Ctx.make tabs f) (n + 1) frS bS iS)
      (runLoop env (Ctx.make tabs g) fuelT frT bT iT) := by
  obtain ⟨rfl, hBm, gB, hgB, hiT, hns, hiS, hrel, hdf, hsrc, hsS, hsz, hty, hA, hfrS⟩ := hR
  subst hiS
  obtain ⟨fB, hfB⟩ := S.blockOf_f hBm
  have hBg : bT ∈ g.blocks := by rw [S.gblocks]; exact hBm
  by_cases hK : bT ∈ (𝓘).K
  · -- a checked block
    obtain ⟨hfid, hgid, hkind, hcsz, -, -, -, -, -, hsucc, -, -, -⟩ :=
      kparts S hBm hfB hgB hK hns hiT hrel hsrc hsS hsz hty hfrS
    cases hst : blockStep env (Ctx.make tabs f) frS bT ((𝓘).edgeIn f 𝓣 bT gB iT).1 with
    | stuck => exact absurd hd (runLoop_stuck hst)
    | panic e m =>
      obtain ⟨Y, hY, hpan⟩ := blockStep_panic hst
      change f.block? bT = some Y at hY
      rw [hfB] at hY; cases hY
      refine ⟨1, ?_⟩
      rw [runLoop_panic hst, runLoop_panic (blockStep_of_panic (ctx := Ctx.make tabs g) hgB
        (kenter_panic S hBm hfB hgB hK hns hiT hrel hsrc hsS hsz hty hfrS hpan))]
      exact .panicked_refl e m
    | ret rs m =>
      obtain ⟨Y, G, hY, hG, hterm⟩ := blockStep_ret hst
      change f.block? bT = some Y at hY
      rw [hfB] at hY; cases hY
      obtain ⟨GT, hGT, -, -, -, -, -, -, hctl⟩ :=
        kenter S hBm hfB hgB hK hns hiT hrel hsrc hsS hsz hty hfrS hG
      rcases stepTerm_ctl hkind (ctl_rel hcsz hctl) hterm with ⟨k, e, he, -⟩ | ⟨rs', m', he, hT⟩
      · cases he
      · cases he
        refine ⟨1, ?_⟩
        rw [runLoop_ret hst, runLoop_ret (ctx := Ctx.make tabs g)
          (by rw [blockStep_of (ctx := Ctx.make tabs g) hgB hGT, hT])]
        exact .returned (RefinesList.refl _) (Mem.Refines.refl _)
    | goto G e =>
      obtain ⟨Y, hY, hG, hterm⟩ := blockStep_goto hst
      change f.block? bT = some Y at hY
      rw [hfB] at hY; cases hY
      obtain ⟨GT, hGT, hGTf, hGTs, hGs, hfacts, hsrcG, htyG, hctl⟩ :=
        kenter S hBm hfB hgB hK hns hiT hrel hsrc hsS hsz hty hfrS hG
      have hAG := ZCSE.arglessInv_enter hA (S.wf.valuesNodup bT fB ⟨hBm, hfB⟩) hG
      rcases stepTerm_ctl hkind (ctl_rel hcsz hctl) hterm with ⟨k, e0, he, hek, hT⟩ | ⟨rs, m, he, -⟩
      · cases he
        obtain ⟨hssz, hsuc⟩ := SCI.succOK_spec _ hsucc
        have hk : k < gB.succs.size := by rw [hssz]; exact (Array.getElem?_eq_some_iff.1 hek).1
        have he' : gB.succs[k]? = some gB.succs[k] := by simp [hk]
        have hT' : blockStep env (Ctx.make tabs g) frT bT iT = .goto GT gB.succs[k] := by
          rw [blockStep_of (ctx := Ctx.make tabs g) hgB hGT, hT]; unfold succ; rw [he']; rfl
        rcases hsuc k _ e he' hek with ⟨hp, hpi, he1, he2⟩ | ⟨hb, hi, hr⟩
        · -- the redirected edge: the source goes through `b`
          subst he2
          rw [runLoop_goto hst] at hd ⊢
          dsimp only [infoOf_s] at hd ⊢
          cases n with
          | zero => exact absurd hd (runLoop_zero_not_defined)
          | succ m =>
          cases hb2 : blockStep env (Ctx.make tabs f) G s.b s.cidx with
          | stuck => exact absurd hd (runLoop_stuck hb2)
          | panic e m' => exact absurd hb2 ((S.bstep_not hGs).1 e m')
          | ret rs m' => exact absurd hb2 ((S.bstep_not hGs).2 rs m')
          | goto G' e2 =>
          obtain ⟨he2, hG'f, hG's, hkeep, hvs, htyG', hAG'⟩ := S.bstep hAG htyG hGs hb2
          subst he2
          rw [runLoop_goto hb2] at hd ⊢
          refine refines_goto hT' (ih m (by omega) _ _ _ _ _ _ ?_ hd)
          rw [he1]
          subst hp
          exact S.R_redir hGTf hGTs hGs hfacts htyG hkeep hvs htyG' hAG' hG'f hG's
        · rw [runLoop_goto hst] at hd ⊢
          refine refines_goto hT' (ih n (Nat.le_refl n) _ _ _ _ _ _ ?_ hd)
          refine S.R_next hBm hgB he' hb hi hr hfacts (fun heK v hv => ?_) (fun hreg => ?_) hGs
            hGTs htyG hAG hGTf
          · have hx := S.exitOK
            unfold Info.exitOK at hx
            have := Array.all_eq_true'.1 hx bT hK
            simp only [Array.all_eq_true', Bool.or_eq_true, contains_iff, beq_iff_eq] at this
            rcases this gB.succs[k] (by rw [getB_of hgB]; exact Array.getElem_mem hk) with h | h
            · rw [hb] at h; exact absurd h heK
            · rcases h v (SCI.look_mem _ hv) with h | h
              · rw [hv] at h; cases h
              · rw [h, hv]
          · apply hsrcG
            have := S.pred_in_region hBm hgB he' hr (by rw [hb]; exact hreg)
            rcases this with h | h
            · exact .inl h
            · exact .inr h
      · cases he
  · -- a block outside `K`
    have hgB' : g.block? bT = some fB := by rw [S.block_out hK, hfB]
    rw [hgB] at hgB'; cases hgB'
    have hnr : (𝓘).redir bT iT = false := by
      cases h : (𝓘).redir bT iT
      · rfl
      · exact absurd ((SCI.redir_iff _).1 h).1 (fun he => hK (he ▸ S.tK))
    have hiS : ((𝓘).edgeIn f 𝓣 bT gB iT).1 = iT := by
      unfold Info.edgeIn; rw [hnr]
      exact SCI.srcIdx_of _ (fun h => hK (h.1 ▸ S.bK))
    rw [hiS] at hd ⊢
    have hO := S.ostep (env := env) hBm hK hfB hrel (hdf hK) hfrS hsz (i := iT)
    cases hst : blockStep env (Ctx.make tabs f) frS bT iT with
    | stuck => exact absurd hd (runLoop_stuck hst)
    | panic e m =>
      obtain ⟨Y, hY, hpan⟩ := blockStep_panic hst
      change f.block? bT = some Y at hY
      rw [hfB] at hY; cases hY
      refine ⟨1, ?_⟩
      rw [runLoop_panic hst, runLoop_panic (blockStep_of_panic (ctx := Ctx.make tabs g) hgB
        (hO.2 e m hpan))]
      exact .panicked_refl e m
    | ret rs m =>
      obtain ⟨Y, G, hY, hG, hterm⟩ := blockStep_ret hst
      change f.block? bT = some Y at hY
      rw [hfB] at hY; cases hY
      obtain ⟨GT, hGT, -, -, -, hT⟩ := hO.1 G hG
      refine ⟨1, ?_⟩
      rw [runLoop_ret hst, runLoop_ret (ctx := Ctx.make tabs g)
        (by rw [blockStep_of (ctx := Ctx.make tabs g) hgB hGT, hT, hterm])]
      exact .returned (RefinesList.refl _) (Mem.Refines.refl _)
    | goto G e =>
      obtain ⟨Y, hY, hG, hterm⟩ := blockStep_goto hst
      change f.block? bT = some Y at hY
      rw [hfB] at hY; cases hY
      obtain ⟨GT, hGT, hGTf, hGTs, hfacts, hT⟩ := hO.1 G hG
      have hT' : blockStep env (Ctx.make tabs g) frT bT iT = .goto GT e := by
        rw [blockStep_of (ctx := Ctx.make tabs g) hgB hGT, hT, hterm]
      obtain ⟨k, hek⟩ := Array.mem_iff_getElem?.1 (stepTerm_goto_mem hterm)
      have hGs : G.regs.size = f.valueTab.size := by
        have hnd := S.wf.valuesNodup bT gB ⟨hBm, hfB⟩
        obtain ⟨PS, o, ho, hev, -, hPs, -, -, -⟩ := enterBlock_spec hnd hG
        have hfid : gB.id = bT := by
          obtain ⟨b', hb', hid⟩ := S.wf.blockId bT hBm; rw [hfB] at hb'; cases hb'; exact hid
        rw [hfid, sched_of_block hfB] at ho
        obtain ⟨ond, otopo, -⟩ := schedule_topo (valuesOwn S.wf hBm hfB) hnd ho
        obtain ⟨-, e2, -, -⟩ := evalAll_spec ond (by exact otopo) (by rw [hPs, hsS]; rfl) hev
        rw [e2, hPs, hsS]
      obtain ⟨hem, C, hC, hcp⟩ := S.wf.succLink bT gB ⟨hBm, hfB⟩ k e hek
      have hBg : bT ∈ g.blocks := by rw [S.gblocks]; exact hBm
      obtain ⟨-, C', hC', hcp'⟩ := S.wfg.succLink bT gB ⟨hBg, hgB⟩ k e hek
      have hr : (𝓘).redir e.b e.i = false := by
        cases h : (𝓘).redir e.b e.i
        · rfl
        · obtain ⟨h1, h2⟩ := (SCI.redir_iff _).1 h
          have h1' : e.b = s.te.b := h1
          obtain ⟨-, hrt⟩ := S.redir_spec
          rw [← h1', getB_of hC', ← h2, hcp'] at hrt
          exact absurd ((Edge.mk.inj (Option.some.inj hrt)).1 ▸ S.pK) hK
      have hi : e.i = (𝓘).srcIdx e.b e.i := by
        refine (SCI.srcIdx_of _ fun h => ?_).symm
        obtain ⟨Bb, hBb, -, -, -, -, -, -, hpr, -⟩ := S.pre
        have h1' : e.b = s.b := h.1
        have h2' : e.i = s.cidx := h.2
        rw [h1', hBb] at hC; cases hC
        rw [h2', hpr] at hcp
        exact hK ((Edge.mk.inj (Option.some.inj hcp)).1 ▸ S.pK)
      rw [runLoop_goto hst] at hd ⊢
      refine refines_goto hT' (ih n (Nat.le_refl n) _ _ _ _ _ _ ?_ hd)
      have hout : (𝓘).outOf 𝓣 bT = (𝓘).dflt := by
        unfold Info.outOf; rw [SCI.factsOf_out _ hK]
      refine S.R_next hBm hgB hek rfl hi hr (by rw [hout]; exact hfacts)
        (fun _ v hv => by rw [hout]; exact hv) (fun hreg => ?_) hGs hGTs
        (typed_enter S.wf hBm hfB hsS hty hG)
        (ZCSE.arglessInv_enter hA (S.wf.valuesNodup bT gB ⟨hBm, hfB⟩) hG) hGTf
      exfalso
      rcases S.pred_in_region hBm hgB hek hr hreg with h | h
      · exact hK (S.region_spec h).2.2.1
      · exact hK (h ▸ S.bK)

/-- **One checked `shortcircuitBlock` rewrite refines.** -/
theorem refines_of_step : Refines tabs g tabs f := by
  have hgsz := S.gvsize
  have hown : g.ownAux = f.ownAux := S.gownAux
  intro env args mem fuel hd
  unfold GoFV.SSA.run runCtx at hd ⊢
  rw [params_eq' (tabs := tabs) hown]
  split
  · rename_i hn; simp only [hn] at hd; exact hd.elim
  · rename_i hn
    simp only [hn] at hd
    have hentry : entryFrame env (Ctx.make tabs g) args mem =
        entryFrame env (Ctx.make tabs f) args mem := by
      unfold entryFrame frameMem frameAllocs
      rw [show (Ctx.make tabs g).f.valueTab.size = (Ctx.make tabs f).f.valueTab.size from hgsz]
      simp only [Ctx.make, abiParams, hown]
    have houts : (Ctx.make tabs g).outs = (Ctx.make tabs f).outs := by
      simp only [Ctx.make, abiParams, hown]
    rw [hentry, houts, show (Ctx.make tabs g).act = (Ctx.make tabs f).act from rfl]
    have hent : (Ctx.make tabs g).f.entry = f.entry := S.gentry
    rw [hent]
    have hwf := S.wf
    obtain ⟨E, hE, -⟩ := hwf.blockId f.entry hwf.entry
    have hE0 := hwf.entryPreds E hE
    have hentg : f.entry ∈ g.blocks := by rw [S.gblocks]; exact hwf.entry
    obtain ⟨gE, hgE, -⟩ := S.wfg.blockId f.entry hentg
    have hgE0 : gE.preds.size = 0 := S.wfg.entryPreds gE (by rw [S.gentry]; exact hgE)
    obtain ⟨Bb, hBb, -, -, -, -, -, -, hpr, -⟩ := S.pre
    have hnb : f.entry ≠ s.b := fun h => by
      rw [h, hBb] at hE; cases hE
      have := (Array.getElem?_eq_some_iff.1 hpr).1; omega
    have hnt : f.entry ≠ s.te.b := fun h => by
      obtain ⟨hsz, -⟩ := S.redir_spec
      rw [← h, getB_of hgE] at hsz; omega
    have hnr : (𝓘).redir f.entry 0 = false := by
      cases h : (𝓘).redir f.entry 0
      · rfl
      · exact absurd ((SCI.redir_iff _).1 h).1 hnt
    have hed : (𝓘).edgeIn f 𝓣 f.entry gE 0 = (0, (𝓘).dflt) := by
      have : gE.preds[0]? = none := Array.getElem?_eq_none (by omega)
      unfold Info.edgeIn
      have hsi : (𝓘).srcIdx f.entry 0 = 0 :=
        SCI.srcIdx_of (𝓘) (fun (h : f.entry = (𝓘).s.b ∧ 0 = (𝓘).s.cidx) => hnb h.1)
      simp only [hnr, Bool.false_eq_true, ↓reduceIte, this, hsi]
    let fr := entryFrame env (Ctx.make tabs f) args mem
    have hregs : fr.regs = Array.replicate f.valueTab.size none := rfl
    have hR0 : Rel tabs f g s env fr f.entry 0 fr f.entry 0 := by
      refine ⟨rfl, hwf.entry, gE, hgE, by omega, fun h => hnb h.2, by rw [hed], ?_, ?_, ?_,
        by rw [hregs]; simp, rfl, typed_replicate _ _ _ hregs, ZCSE.arglessInv_init _ _ _ _ hregs,
        rfl⟩
      · rw [hed]
        exact ⟨fun _ _ => rfl, fun v w h => by rw [look_dflt h]⟩
      · intro _ v hv; rw [hed]; exact hv
      · intro hr; exact absurd S.gentry.symm ((S.region_spec hr).2.1)
    obtain ⟨fuelT, h⟩ := runLoop_simIH (Rel tabs f g s env) (fun n ih _ _ _ _ _ _ hR hd' =>
      S.sim_step n ih hR hd') fuel _ _ _ _ _ _ hR0 (finish_defined hd)
    exact ⟨fuelT, finish_refines hd h⟩

end Setup

/-- **Checked `shortcircuitBlock` refines its input and keeps `WFDom`.** -/
theorem shortcircuitBlockChecked_refines {tabs : Tables} {ce : CheckEnv} {f g : Func} {b : ID}
    {ch : Bool} (h : shortcircuitBlockChecked tabs f b = (g, ch)) (hf : WFDom ce f) :
    Refines tabs g tabs f ∧ WFDom ce g := by
  unfold shortcircuitBlockChecked at h
  dsimp only at h
  split at h
  · cases h; exact ⟨Refines.refl _ _, hf⟩
  · rename_i s _
    split at h
    · rename_i hok
      cases h
      have S : Setup ce tabs f (applySite f s) s := ⟨hf.wf, hf.dom, hok⟩
      exact ⟨S.refines_of_step, S.wfg, S.useDom_g⟩
    · cases h; exact ⟨Refines.refl _ _, hf⟩

end GoFV.Proof.ShortCirc
