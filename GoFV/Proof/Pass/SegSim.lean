import GoFV.Proof.Pass.SegEval
import GoFV.Proof.Pass.SegChain
import GoFV.Proof.Pass.SegCallSeg
import GoFV.Proof.Pass.StructStoreSim
import GoFV.Proof.Pass.SegRo
import GoFV.Proof.Pass.SegMove

variable [GoFV.SSA.Sem.Addrs]

/-!
# Segment rewrites refine their input (issue #151)

`seg_refines`: if `g` is `f` with segments rewritten (`RewriteCheck.segRel`: `Zero`s under the
`Store`s that tile them dropped, `generic.rules:1833`/`:1844`/`:1857`; `memclrNoHeapPointers`/
`memmove` calls turned into `Zero`/`Move`, `:1638`/`:1730`), both checked, `g` refines `f` under
monotone contracts whose memory runtime contracts are the runtime's (`Env.MemOps`). Each segment
is sound (`SegSound`: `chainSeg_sound`, `callSeg_sound`). Lock-step simulation (`runLoop_simE`)
along the same edges with `SimAt` at block entries, as `StructStore.ss_refines`: the target's
registers refine the source's on the values the target keeps (`RR`); one block step: the `Phi`s
(the dropped and fresh values are none), the block's schedule (`Blk.okCase`, `Blk.panicCase`) and
the terminators (`stepTerm_mono2`; no control is dropped).
-/

namespace GoFV.Proof.Seg

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Proof.CopyElim GoFV.Opt GoFV.Opt.RewriteCheck
open GoFV.Proof.StructStore (ssSame_spec)

variable {env : Env} {tabs : Tables} {f g : Func}

/-- Every segment of `segRel` is sound under monotone contracts with the runtime's memory
contracts. -/
theorem segs_sound (R : SRel tabs f g) (hM : env.MemOps) {ro : List (String × Alloc)}
    (hro : roSegsOK tabs ro f g = true) {x : ID} {D N : List ID}
    (hs : segOK tabs f g x = some (D, N)) (hgid : ∀ n ∈ segL x N, ∀ v, g.value? n = some v → v.id = n) :
    SegSound (RoQ tabs ro f) env tabs f g x D N := by
  obtain ⟨d⟩ := segOK_spec hs
  rcases d.hkind with h | h | h | h
  · exact chainSeg_sound d.hfv d.hgv h hgid _ env
  · exact callSeg_sound d.hfv d.hgv d.hgid d.hgty h hM
  · obtain ⟨-, -, hop, -, -, -, -, hgop, -⟩ := roSeg_spec h
    obtain ⟨hm, hsrc⟩ := roSegsOK_spec hro hs d.hfv hop d.hgv hgop
    exact roSeg_sound d.hfv d.hgv d.hgid d.hgty h hsrc hm env
  · exact moveSeg_sound d.hfv d.hgv h hgid d.hgty _ env

/-- The simulation relation at the entry of block `bid` along edge `i`. -/
structure SimAt (Q : Mem → Prop) (env : Env) (tabs : Tables) (f g : Func) (frS frT : Frame)
    (bid : ID) (i : Nat) : Prop where
  size : frS.regs.size = f.valueTab.size
  sizeT : frT.regs.size = g.valueTab.size
  frame : frT = { frS with regs := frT.regs }
  rr : RR f g frS.regs frT.regs
  typed : Proof.Typed (Ctx.make tabs f) frS
  pre : CSE.Pre env tabs f #[] frS bid i
  /-- The source's memory invariant. -/
  inv : MemInv.SInv Q frS

theorem RR.set {r r' : Array (Option Val)} (h : RR f g r r') (hs : r.size ≤ r'.size) (z : ID)
    {x y : Val} (hxy : Sem.Refines x y) : RR f g (r.set! z (some x)) (r'.set! z (some y)) := by
  intro a v w hv hg ha
  simp only [Array.set!_eq_setIfInBounds] at ha ⊢
  by_cases hza : z = a
  · subst hza
    by_cases hlt : z < r.size
    · rw [Array.getElem?_setIfInBounds_self_of_lt hlt] at ha
      cases ha
      exact ⟨y, Array.getElem?_setIfInBounds_self_of_lt (Nat.lt_of_lt_of_le hlt hs), hxy⟩
    · rw [Array.setIfInBounds, dite_eq_right_of_eq_false (eq_false hlt),
        Array.getElem?_eq_none (Nat.le_of_not_lt hlt)] at ha
      cases ha
  · rw [Array.getElem?_setIfInBounds_ne hza] at ha ⊢
    exact h a v w hv hg ha

theorem setPhis_rr : ∀ {ps ps' : List (ID × Val)} {r r' : Array (Option Val)},
    PhisRefine ps ps' → RR f g r r' → r.size ≤ r'.size → RR f g (setPhis ps r) (setPhis ps' r')
  | _, _, _, _, .nil, h, _ => h
  | _, _, r, r', .cons (x := x) (y := y) (ps := ps) (ps' := ps') z hxy t, h, hs => by
    show RR f g (setPhis ps (r.set! z (some x))) (setPhis ps' (r'.set! z (some y)))
    exact setPhis_rr t (h.set hs z hxy) (by simp [hs])

/-- The `Phi` collection of the source's values, the target's: the kept ones, then fresh values;
the dropped ones are none. -/
theorem phis_rel {F G : ID → Res (Option (ID × Val))} {p : ID → Bool} :
    ∀ {l E : List ID}, (∀ z ∈ l, p z = true → Res.Rel PhiRefines (F z) (G z)) →
      (∀ z ∈ l, p z = false → F z = .ok none) → (∀ z ∈ E, G z = .ok none) →
      Res.Rel PhisRefine (l.filterMapM F) ((l.filter p ++ E).filterMapM G)
  | [], E, _, _, hE => by
    rw [List.filterMapM_nil, List.filter_nil, List.nil_append,
      StructStore.filterMapM_none hE]; exact .ok .nil
  | z :: l, E, h, hd, hE => by
    have ih := phis_rel (l := l) (fun y hy => h y (List.mem_cons_of_mem _ hy))
      (fun y hy => hd y (List.mem_cons_of_mem _ hy)) hE
    cases hpz : p z with
    | false =>
      rw [List.filterMapM_cons, hd z List.mem_cons_self hpz, List.filter_cons_of_neg (by simp [hpz])]
      exact ih
    | true =>
      rw [List.filter_cons_of_pos hpz, List.cons_append, List.filterMapM_cons, List.filterMapM_cons]
      have hz := h z List.mem_cons_self hpz
      revert hz
      generalize F z = o
      generalize G z = o'
      intro hz
      cases hz with
      | ok hp =>
        cases hp with
        | none => exact ih
        | some z hxy =>
          change Res.Rel PhisRefine ((List.filterMapM F l).bind fun r => .ok (_ :: r))
            ((List.filterMapM G (l.filter p ++ E)).bind fun r => .ok (_ :: r))
          exact Res.Rel.bind ih fun ps ps' hps => .ok (.cons z hxy hps)
      | panic e hm => exact .panic e hm
      | stuck msg r => exact .stuck _ _

section
variable {ce : CheckEnv} (hwf : WF ce f) (R : SRel tabs f g)
include hwf R

/-- One `Phi` step of a source value the target keeps, on refined registers. -/
theorem phiStep_rel {frS frT : Frame} (hr : RR f g frS.regs frT.regs) {bid : ID} {fb : Block}
    (hb : BlockIn f bid fb) {z : ID} (hz : z ∈ fb.values) (hnd : ∀ x, ¬ Drop tabs f g x z)
    (i : Nat) :
    Res.Rel PhiRefines (phiStep (Ctx.make tabs f) frS i z) (phiStep (Ctx.make tabs g) frT i z) := by
  obtain ⟨fv, hfv, -, -⟩ := hwf.valueId bid fb hb z hz
  obtain ⟨gv, hgv, hsv⟩ : ∃ gv, g.value? z = some gv ∧
      (ssSame fv gv = true ∨ ∃ D N, segOK tabs f g z = some (D, N)) := by
    rcases R.value z fv hfv with h | ⟨-, x', hd⟩
    · exact h
    · exact absurd hd (hnd x')
  unfold phiStep
  simp only [show (Ctx.make tabs f).f = f from rfl, show (Ctx.make tabs g).f = g from rfl,
    hfv, hgv]
  rcases hsv with hs | ⟨D, N, hs⟩
  · obtain ⟨-, hop, -, -, hty, -, hargs⟩ := ssSame_spec hs
    rw [hop, hargs, tys_of_value hgv, tys_of_value hfv, hty]
    by_cases hph : fv.op = .Phi
    · simp only [hph, beq_self_eq_true, ↓reduceIte]
      cases ha : fv.args[i]? with
      | none => exact .stuck _ _
      | some a =>
        simp only
        cases hx : (frS.regs[a]?).join with
        | none => exact .stuck _ _
        | some x =>
          obtain ⟨bid', b', hb', hab⟩ := hwf.argListed bid fb z fv ⟨hb, hz, hfv⟩ a
            (Array.mem_of_getElem? ha)
          obtain ⟨va, hva, -, -⟩ := hwf.valueId bid' b' hb' a hab
          have hag : (g.value? a).isSome = true := by
            rcases R.value a va hva with ⟨ga, hga, -⟩ | ⟨-, x', hd⟩
            · rw [hga]; rfl
            · rcases R.uses bid hb.1 fb hb.2 z hz fv hfv a (Array.mem_of_getElem? ha) x' hd with
                rfl | hd'
              · obtain ⟨D', N', hs', -⟩ := hd
                obtain ⟨d⟩ := segOK_spec hs'
                have h1 := d.hfv
                rw [hfv] at h1; cases h1
                exact absurd hph d.hfph
              · exact absurd hd' (hnd x')
          obtain ⟨y, hy, hxy⟩ := hr a va x hva hag (Option.join_eq_some_iff.1 hx)
          rw [hy]
          exact .ok (.some z (retype_mono _ hxy))
    · have : (fv.op == .Phi) = false := by simpa using hph
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      exact .ok .none
  · obtain ⟨d⟩ := segOK_spec hs
    rw [d.hfv] at hfv; cases hfv
    rw [d.hgv] at hgv; cases hgv
    have h1 : (d.gv.op == .Phi) = false := by
      simpa using root_ne_phi d.hroot d.hgv
    have h2 : (d.fv.op == .Phi) = false := by simpa using d.hfph
    simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
    exact .ok .none

/-- **The terminators** on refined controls. -/
theorem term_rel {G GT : Frame} (hr : RR f g G.regs GT.regs) {bid : ID} {fb gb : Block}
    (hb : BlockIn f bid fb) (hk : gb.kind = fb.kind) (hs : gb.succs = fb.succs) (hid : gb.id = fb.id)
    (hc : gb.controls = fb.controls) :
    Res.Rel Next.Refines (stepTerm G fb) (stepTerm GT gb) := by
  refine AtomSim.stepTerm_mono2 hk hs hid fun k => ?_
  unfold Sem.control
  rw [hc]
  cases hck : fb.controls[k]? with
  | none => exact .stuck _ _
  | some c =>
    dsimp only
    cases hx : (G.regs[c]?).join with
    | none => exact .stuck _ _
    | some x =>
      obtain ⟨bid', b', hb', hcb⟩ := hwf.ctrlListed bid fb hb c (Array.mem_of_getElem? hck)
      obtain ⟨vc, hvc, -, -⟩ := hwf.valueId bid' b' hb' c hcb
      have hcg : (g.value? c).isSome = true := by
        rcases R.value c vc hvc with ⟨gc, hgc, -⟩ | ⟨-, x', hd⟩
        · rw [hgc]; rfl
        · exact absurd hd (R.ctrls bid hb.1 fb hb.2 c (Array.mem_of_getElem? hck) x')
      obtain ⟨y, hy, hxy⟩ := hr c vc x hvc hcg (Option.join_eq_some_iff.1 hx)
      rw [hy]
      exact .ok hxy

end

/-- The simulation relation: the same block and edge, `SimAt`. -/
def SimR (Q : Mem → Prop) (env : Env) (tabs : Tables) (f g : Func) (frS : Frame) (bS : ID)
    (iS : Nat) (frT : Frame) (bT : ID) (iT : Nat) : Prop :=
  bT = bS ∧ iT = iS ∧ SimAt Q env tabs f g frS frT bS iS

/-- A block's schedule lists values of the block. -/
theorem sched_listed {ce : CheckEnv} (hwf : WF ce f) {b : ID} {B : Block} (hb : b ∈ f.blocks)
    (hB : f.block? b = some B) {o : Array ID} (ho : schedule f B = some o) :
    ∀ x ∈ o.toList, ∃ b' ∈ f.blocks, x ∈ WBCheck.vals f b' := by
  have hnd := hwf.valuesNodup b B ⟨hb, hB⟩
  have hown := valuesOwn hwf hb hB
  obtain ⟨-, -, omem⟩ := schedule_topo hown hnd ho
  intro x hx
  exact ⟨b, hb, by unfold WBCheck.vals; rw [hB]; exact ((omem x).1 hx).1⟩

/-- **One block step.** -/
theorem step {ce ce' : CheckEnv} (hwf : WF ce f) (hc : CertOK f) (hwg : WF ce' g)
    (R : SRel tabs f g) (hE : env.Mono) {Q : Mem → Prop}
    (hsound : ∀ x D N, segOK tabs f g x = some (D, N) → SegSound Q env tabs f g x D N)
    (hQ : ∀ fr fr' o, MemInv.SInv Q fr → (∀ x ∈ o, ∃ b ∈ f.blocks, x ∈ WBCheck.vals f b) →
      evalAll env (Ctx.make tabs f) fr o = .ok fr' → MemInv.SInv Q fr')
    {frS frT : Frame} {bid : ID} {i : Nat} (hA : SimAt Q env tabs f g frS frT bid i) :
    StepSimE Mem.Refines (SimR Q env tabs f g) (blockStep env (Ctx.make tabs f) frS bid i)
      (blockStep env (Ctx.make tabs g) frT bid i) := by
  have hbt := CSE.pre_tree hwf hc hA.pre
  unfold blockStep
  simp only [show (Ctx.make tabs f).f = f from rfl, show (Ctx.make tabs g).f = g from rfl]
  cases hfb : f.block? bid with
  | none => exact True.intro
  | some fb =>
  obtain ⟨gb, hgb, BS⟩ := R.block bid hbt.1 fb hfb
  obtain ⟨gb', hgb', hgid, hsucc, -⟩ := cfgView_block R.cfg hfb
  rw [hgb] at hgb'; cases hgb'
  obtain ⟨fb', hfb', hfid⟩ := hwf.blockId bid hbt.1
  rw [hfb] at hfb'; cases hfb'
  rw [hgb]
  simp only
  obtain ⟨E, hE', hEf⟩ := BS.values
  have hsz : f.valueTab.size ≤ g.valueTab.size := R.size
  have hkeep : ∀ z, (segOwner (segList (segArr tabs f g)) z).isNone = true ↔
      ∀ x, ¬ Drop tabs f g x z := fun z => by
    constructor
    · intro h x hd
      rw [(R.own z x).2 hd] at h; cases h
    · intro h
      cases ho : segOwner (segList (segArr tabs f g)) z with
      | none => rfl
      | some x => exact absurd ((R.own z x).1 ho) (h x)
  -- the parts of the source's block entry, and the target's
  have parts : ∀ r, enterBlock env (Ctx.make tabs f) frS fb i = r → (∀ msg, r ≠ .stuck msg) →
      ∃ ps ps' oS oT, fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) frS i) = .ok ps ∧
        PhisRefine ps ps' ∧ schedule f fb = some oS ∧ schedule g gb = some oT ∧
        oT.toList.filter (CSE.rootNode g) =
          segRoots g (segList (segArr tabs f g)) (oS.toList.filter (CSE.rootNode f)) ∧
        evalAll env (Ctx.make tabs f) { frS with regs := setPhis ps frS.regs } oS.toList = r ∧
        enterBlock env (Ctx.make tabs g) frT gb i =
          evalAll env (Ctx.make tabs g) { frT with regs := setPhis ps' frT.regs } oT.toList := by
    intro r hen hr
    obtain ⟨ps, oS, hps, hsched, hev⟩ := CSE.enterBlock_split hen hr
    rw [hfid, sched_of_block hfb] at hsched
    obtain ⟨oT, hoT, hfilt⟩ := BS.sched oS hsched
    have hrel := phis_rel (F := phiStep (Ctx.make tabs f) frS i)
      (G := phiStep (Ctx.make tabs g) frT i)
      (p := fun z => (segOwner (segList (segArr tabs f g)) z).isNone)
      (l := fb.values.toList) (E := E.toList)
      (fun z hz hp => phiStep_rel hwf R hA.rr ⟨hbt.1, hfb⟩ (Array.mem_toList_iff.1 hz)
        ((hkeep z).1 hp) i)
      (fun z hz hp => by
        have hd : ∃ x, Drop tabs f g x z := by
          cases ho : segOwner (segList (segArr tabs f g)) z with
          | none => rw [ho] at hp; cases hp
          | some x => exact ⟨x, (R.own z x).1 ho⟩
        obtain ⟨x, D, N, hs, hzD⟩ := hd
        obtain ⟨d⟩ := segOK_spec hs
        obtain ⟨v, hv, -, -⟩ := hwf.valueId bid fb ⟨hbt.1, hfb⟩ z (Array.mem_toList_iff.1 hz)
        have hnp : (v.op == .Phi) = false := by
          simpa using root_ne_phi (d.hD z hzD).2 hv
        unfold phiStep
        simp only [show (Ctx.make tabs f).f = f from rfl, hv, hnp, Bool.false_eq_true,
          ↓reduceIte])
      (fun z hz => by
        obtain ⟨hzf, ⟨x0, D0, N0, hs0, hzN⟩, v, hv, -⟩ := hEf z (Array.mem_toList_iff.1 hz)
        obtain ⟨d⟩ := segOK_spec hs0
        have hnp : (v.op == .Phi) = false := by
          simpa using d.ne_phi (by simp [segL, hzN]) hv
        unfold phiStep
        simp only [show (Ctx.make tabs g).f = g from rfl, hv, hnp, Bool.false_eq_true,
          ↓reduceIte])
    rw [hps, ← Array.toList_filter, ← Array.toList_append, ← hE'] at hrel
    generalize hT' : gb.values.toList.filterMapM (phiStep (Ctx.make tabs g) frT i) = rT at hrel
    cases hrel with
    | ok hpr =>
      refine ⟨ps, _, oS, oT, hps, hpr, hsched, hoT, hfilt, hev, CSE.enterBlock_of_parts hT' ?_⟩
      rw [hgid, hfid, sched_of_block hgb, hoT]
  -- the block's evaluation
  have blk : ∀ ps ps' oS oT,
      fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) frS i) = .ok ps →
      PhisRefine ps ps' → schedule f fb = some oS → schedule g gb = some oT →
      oT.toList.filter (CSE.rootNode g) =
        segRoots g (segList (segArr tabs f g)) (oS.toList.filter (CSE.rootNode f)) →
      Blk Q env tabs f g bid fb gb { frS with regs := setPhis ps frS.regs }
        { frT with regs := setPhis ps' frT.regs } oS oT := by
    intro ps ps' oS oT hps hpr hoS hoT hfilt
    have hnd := hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩
    obtain ⟨p1, p2, p3, p4⟩ := phis_spec hnd hps
    refine ⟨⟨⟨ce, hwf⟩, hc, hbt, hfb, by simp [setPhis_size, hA.size],
      DSE.phis_strict hwf hc hA.pre hfb hps, fun z hz v hv hph => ?_,
      typed_phis hA.typed p1 p3 p4 p2, hoS⟩, R, ⟨ce', hwg⟩, hgb, BS, hoT, hfilt, ?_,
      by simp [setPhis_size, hA.sizeT],
      setPhis_rr hpr hA.rr (by rw [hA.size, hA.sizeT]; exact hsz), hsound,
      fun L S hL hev => (hQ _ S L (MemInv.sinv_phis hA.inv hps) (fun x hx =>
        sched_listed hwf hbt.1 hfb hoS x (hL.subset hx)) hev).2⟩
    · obtain ⟨a, y, -, -, h⟩ := p4 z hz v hv hph (by rw [hA.size]; exact lt_of_value? hv)
      exact ⟨_, h⟩
    · conv => lhs; rw [hA.frame]
  cases hen : enterBlock env (Ctx.make tabs f) frS fb i with
  | stuck msg => exact True.intro
  | panic e m =>
    obtain ⟨ps, ps', oS, oT, hps, hpr, hoS, hoT, hfilt, hev, hT⟩ := parts _ hen nofun
    obtain ⟨m', h1, h2⟩ := (blk ps ps' oS oT hps hpr hoS hoT hfilt).panicCase hE hev
    rw [hT, h1]
    exact ⟨m', rfl, h2⟩
  | ok G =>
  obtain ⟨ps, ps', oS, oT, hps, hpr, hoS, hoT, hfilt, hev, hT⟩ := parts _ hen nofun
  obtain ⟨GT, hGT, hGTf, hGTs, hGTr⟩ := (blk ps ps' oS oT hps hpr hoS hoT hfilt).okCase hE hev
  have hinvG : MemInv.SInv Q G := hQ _ G _ (MemInv.sinv_phis hA.inv hps)
    (sched_listed hwf hbt.1 hfb hoS) hev
  rw [hT, hGT]
  simp only
  obtain ⟨hD, -, hGsz⟩ := dinv_enter hwf hc hbt.1 hfb hA.size (CSE.pre_strict hc hA.pre).1 hen
  have hty := typed_enter hwf hbt.1 hfb hA.size hA.typed hen
  have hst := term_rel hwf R hGTr ⟨hbt.1, hfb⟩ BS.kind (by rw [hsucc]) (by rw [hgid, hfid])
    BS.controls
  generalize hS : stepTerm G fb = sS at hst ⊢
  generalize stepTerm GT gb = sT at hst ⊢
  cases hst with
  | ok hn =>
    cases hn with
    | goto e =>
      refine ⟨GT, e, rfl, rfl, rfl, by rw [hGsz, hA.size], hGTs, hGTf, hGTr, hty,
        .inr ⟨bid, fb, hbt.1, hfb, hbt.2, ?_, hD, DSE.repInv_nil _ _⟩, hinvG⟩
      cases e; exact stepTerm_goto_mem hS
    | ret hl hm => exact ⟨_, _, rfl, hl, hm⟩
  | panic e hm => exact ⟨_, rfl, hm⟩
  | stuck msg r => exact True.intro

/-- **Segment rewrites refine** under monotone contracts whose memory runtime contracts are the
runtime's, and (for the read-only segments, `roSegsOK`) read-only symbols `ro` in the initial
memory that the contracts keep (`RoImage`). -/
theorem seg_refines {ce ce' : CheckEnv} (hf : check ce f = .ok ()) (hg : check ce' g = .ok ())
    (hrel : segRel tabs f g = true) {ro : List (String × Alloc)}
    (hro : roSegsOK tabs ro f g = true) :
    RefinesFrom (fun env _ mem => env.Mono ∧ env.MemOps ∧ RoImage ro env mem) tabs g tabs f := by
  have hwf := check_wf hf
  have hwg := check_wf hg
  have hc := certOK_of_check (check_domCert hf)
  have R := segRel_spec hrel
  intro env args mem ⟨hE, hM, hRo⟩ fuel hd
  have hsound : ∀ x D N, segOK tabs f g x = some (D, N) →
      SegSound (RoQ tabs ro f) env tabs f g x D N :=
    fun x D N hs => segs_sound R hM hro hs fun n hn v hv => by
      obtain ⟨d⟩ := segOK_spec hs
      simp only [segL, List.mem_append, List.mem_singleton] at hn
      rcases hn with hn | rfl
      · obtain ⟨-, ⟨b, hgb, hnb⟩, v', hv', -⟩ := d.hN n hn
        obtain ⟨v'', hv'', hid, -⟩ := hwg.valueId _ b ⟨by
          rw [cfgView_blocks R.cfg]; exact d.hbm, hgb⟩ n hnb
        rw [hv] at hv''; cases hv''; exact hid
      · rw [d.hgv] at hv; cases hv; exact d.hgid
  refine ⟨fuel, ?_⟩
  have hcx := AtomSim.ctx_eq (tabs := tabs) R.ownAux.symm
  have hpar : (Ctx.make tabs g).params = (Ctx.make tabs f).params := by rw [hcx]
  have houts : (Ctx.make tabs g).outs = (Ctx.make tabs f).outs := by rw [hcx]
  have hact : (Ctx.make tabs g).act = (Ctx.make tabs f).act := by rw [hcx]
  change (runCtx env (Ctx.make tabs f) args mem fuel).Defined at hd
  change OutcomeRefines 0 (runCtx env (Ctx.make tabs f) args mem fuel)
    (runCtx env (Ctx.make tabs g) args mem fuel)
  unfold runCtx at hd ⊢
  rw [hpar, houts, hact]
  split
  · next hn => simp only [hn] at hd; exact hd.elim
  · next hn =>
    simp only [hn] at hd
    have hT : entryFrame env (Ctx.make tabs g) args mem =
        { entryFrame env (Ctx.make tabs f) args mem with
          regs := Array.replicate g.valueTab.size none } :=
      AtomSim.entryFrame_eq R.ownAux.symm args mem
    have hA0 : SimAt (RoQ tabs ro f) env tabs f g (entryFrame env (Ctx.make tabs f) args mem)
        (entryFrame env (Ctx.make tabs g) args mem) f.entry 0 :=
      { size := by simp [entryFrame]; rfl
        sizeT := by rw [hT]; simp
        frame := by rw [hT]
        rr := fun a v x hv _ h => by
          simp [entryFrame, Array.getElem?_replicate] at h
        typed := typed_replicate _ _ _ rfl
        pre := .inl rfl
        inv := roQ_entry hRo args }
    rw [show (Ctx.make tabs g).f.entry = (Ctx.make tabs f).f.entry from cfgView_entry R.cfg]
    refine finish_refines_mono hE hd (runLoop_simE (SimR (RoQ tabs ro f) env tabs f g)
      (fun frS bS iS frT bT iT hR => ?_) fuel _ _ _ _ _ _ ⟨rfl, rfl, hA0⟩ (finish_defined hd))
    obtain ⟨rfl, rfl, hA⟩ := hR
    exact step hwf hc hwg R hE hsound
      (fun _ _ _ hs ho hev => roQ_evalAll hRo.1 hwf ho hs hev) hA

end GoFV.Proof.Seg
