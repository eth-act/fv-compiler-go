import GoFV.Proof.Pass.StructStoreEval
import GoFV.Proof.Pass.DSESim
import GoFV.Proof.AtomSim

/-!
# Struct-store splits refine their input (issue #151)

`ss_refines`: if `g` is `f` with struct stores split (`RewriteCheck.ssRel`), both checked, `g`
refines `f` under monotone contracts. Lock-step simulation (`runLoop_simE`) along the same edges
with `SimAt` at block entries: the source entered from the entry or along an edge of a tree block
after which lemma (D) holds (`CSE.Pre`), its registers typed, the target's registers refining the
source's on the source's values (`RR`). One block step (`step`): the `Phi`s of the target are the
source's on refined registers (`phis_rel`; the fresh values are none), the block's schedule
evaluates to refined registers or panics alike on a refined memory (`Blk.okCase`,
`Blk.panicCase`), and the terminators refine (`stepTerm_mono2` on refined controls).
-/

namespace GoFV.Proof.StructStore

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Proof.CopyElim GoFV.Opt GoFV.Opt.RewriteCheck

variable {env : Env} {tabs : Tables} {f g : Func}

/-- The simulation relation at the entry of block `bid` along edge `i`. -/
structure SimAt (env : Env) (tabs : Tables) (f g : Func) (frS frT : Frame) (bid : ID) (i : Nat) :
    Prop where
  size : frS.regs.size = f.valueTab.size
  sizeT : frT.regs.size = g.valueTab.size
  frame : frT = { frS with regs := frT.regs }
  rr : RR f frS.regs frT.regs
  typed : Proof.Typed (Ctx.make tabs f) frS
  pre : CSE.Pre env tabs f #[] frS bid i

theorem RR.set {r r' : Array (Option Val)} (h : RR f r r') (hs : r.size ≤ r'.size) (z : ID)
    {x y : Val} (hxy : Sem.Refines x y) : RR f (r.set! z (some x)) (r'.set! z (some y)) := by
  intro a v w hv ha
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
    exact h a v w hv ha

theorem setPhis_rr : ∀ {ps ps' : List (ID × Val)} {r r' : Array (Option Val)},
    PhisRefine ps ps' → RR f r r' → r.size ≤ r'.size → RR f (setPhis ps r) (setPhis ps' r')
  | _, _, _, _, .nil, h, _ => h
  | _, _, r, r', .cons (x := x) (y := y) (ps := ps) (ps' := ps') z hxy t, h, hs => by
    show RR f (setPhis ps (r.set! z (some x))) (setPhis ps' (r'.set! z (some y)))
    exact setPhis_rr t (h.set hs z hxy) (by simp [hs])

theorem filterMapM_none {G : ID → Res (Option (ID × Val))} :
    ∀ {l : List ID}, (∀ z ∈ l, G z = .ok none) → l.filterMapM G = .ok []
  | [], _ => rfl
  | z :: l, h => by
    rw [List.filterMapM_cons, h z List.mem_cons_self]
    exact filterMapM_none fun y hy => h y (List.mem_cons_of_mem _ hy)

/-- The `Phi` collection of the source's values, the target's with fresh values after them. -/
theorem phis_rel {F G : ID → Res (Option (ID × Val))} :
    ∀ {l E : List ID}, (∀ z ∈ l, Res.Rel PhiRefines (F z) (G z)) → (∀ z ∈ E, G z = .ok none) →
      Res.Rel PhisRefine (l.filterMapM F) ((l ++ E).filterMapM G)
  | [], E, _, hE => by
    rw [List.filterMapM_nil, List.nil_append, filterMapM_none hE]; exact .ok .nil
  | z :: l, E, h, hE => by
    rw [List.cons_append, List.filterMapM_cons, List.filterMapM_cons]
    have hz := h z List.mem_cons_self
    have ih := phis_rel (l := l) (fun y hy => h y (List.mem_cons_of_mem _ hy)) hE
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
          ((List.filterMapM G (l ++ E)).bind fun r => .ok (_ :: r))
        exact Res.Rel.bind ih fun ps ps' hps => .ok (.cons z hxy hps)
    | panic e hm => exact .panic e hm
    | stuck msg r => exact .stuck _ _

section
variable {ce : CheckEnv} (hwf : WF ce f) (R : SRel tabs f g)
include hwf R

/-- One `Phi` step of a source value, on refined registers. -/
theorem phiStep_rel {frS frT : Frame} (hr : RR f frS.regs frT.regs) {bid : ID} {fb : Block}
    (hb : BlockIn f bid fb) {z : ID} (hz : z ∈ fb.values) (i : Nat) :
    Res.Rel PhiRefines (phiStep (Ctx.make tabs f) frS i z) (phiStep (Ctx.make tabs g) frT i z) := by
  obtain ⟨fv, hfv, -, -⟩ := hwf.valueId bid fb hb z hz
  obtain ⟨gv, hgv, hsv⟩ := R.value z fv hfv
  unfold phiStep
  simp only [show (Ctx.make tabs f).f = f from rfl, show (Ctx.make tabs g).f = g from rfl,
    hfv, hgv]
  rcases hsv with hs | ⟨ps, hps⟩
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
          obtain ⟨y, hy, hxy⟩ := hr a va x hva (Option.join_eq_some_iff.1 hx)
          rw [hy]
          exact .ok (.some z (retype_mono _ hxy))
    · have : (fv.op == .Phi) = false := by simpa using hph
      simp only [this, Bool.false_eq_true, ↓reduceIte]
      exact .ok .none
  · obtain ⟨d⟩ := ssSplit_spec hps
    rw [d.hfv] at hfv; cases hfv
    rw [d.hgv] at hgv; cases hgv
    have h1 : (d.gv.op == .Phi) = false := by
      rcases d.hmode with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> rfl
    have h2 : (d.fv.op == .Phi) = false := by rw [d.hop]; rfl
    simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]
    exact .ok .none

omit R in
/-- **The terminators** on refined controls. -/
theorem term_rel {G GT : Frame} (hr : RR f G.regs GT.regs) {bid : ID} {fb gb : Block}
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
      obtain ⟨y, hy, hxy⟩ := hr c vc x hvc (Option.join_eq_some_iff.1 hx)
      rw [hy]
      exact .ok hxy

end

/-- The simulation relation: the same block and edge, `SimAt`. -/
def SimR (env : Env) (tabs : Tables) (f g : Func) (frS : Frame) (bS : ID) (iS : Nat) (frT : Frame)
    (bT : ID) (iT : Nat) : Prop :=
  bT = bS ∧ iT = iS ∧ SimAt env tabs f g frS frT bS iS

/-- **One block step.** -/
theorem step {ce ce' : CheckEnv} (hwf : WF ce f) (hc : CertOK f) (hwg : WF ce' g)
    (R : SRel tabs f g) (hE : env.Mono) {frS frT : Frame} {bid : ID} {i : Nat}
    (hA : SimAt env tabs f g frS frT bid i) :
    StepSimE (SimR env tabs f g) (blockStep env (Ctx.make tabs f) frS bid i)
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
  -- the parts of the source's block entry, and the target's
  have parts : ∀ r, enterBlock env (Ctx.make tabs f) frS fb i = r → (∀ msg, r ≠ .stuck msg) →
      ∃ ps ps' oS oT, fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) frS i) = .ok ps ∧
        PhisRefine ps ps' ∧ schedule f fb = some oS ∧ schedule g gb = some oT ∧
        oT.toList.filter (CSE.rootNode g) =
          ssRoots ((Array.range f.valueTab.size).map (ssSplit? tabs f g))
            (oS.toList.filter (CSE.rootNode f)) ∧
        evalAll env (Ctx.make tabs f) { frS with regs := setPhis ps frS.regs } oS.toList = r ∧
        enterBlock env (Ctx.make tabs g) frT gb i =
          evalAll env (Ctx.make tabs g) { frT with regs := setPhis ps' frT.regs } oT.toList := by
    intro r hen hr
    obtain ⟨ps, oS, hps, hsched, hev⟩ := CSE.enterBlock_split hen hr
    rw [hfid, sched_of_block hfb] at hsched
    obtain ⟨oT, hoT, hfilt⟩ := BS.sched oS hsched
    have hrel := phis_rel (F := phiStep (Ctx.make tabs f) frS i)
      (G := phiStep (Ctx.make tabs g) frT i) (l := fb.values.toList) (E := E.toList)
      (fun z hz => phiStep_rel hwf R hA.rr ⟨hbt.1, hfb⟩ (Array.mem_toList_iff.1 hz) i)
      (fun z hz => by
        obtain ⟨-, -, v, hv, -⟩ := hEf z (Array.mem_toList_iff.1 hz)
        obtain ⟨-, ⟨x0, ps0, hps0, q0, hq0, hzq⟩, -⟩ := hEf z (Array.mem_toList_iff.1 hz)
        obtain ⟨d⟩ := ssSplit_spec hps0
        obtain ⟨i0, hi0⟩ := List.getElem?_of_mem hq0
        obtain ⟨o, t, a, av, sv, ov, -, -, L⟩ := link_at d hi0
        have hzf : f.value? z = none := (hEf z (Array.mem_toList_iff.1 hz)).1
        have hnp : v.op ≠ .Phi := by
          rcases hzq with rfl | rfl
          · have P := L.hoff hzf
            rw [P.hp] at hv; cases hv; rw [P.hpop]; decide
          · rw [L.hs] at hv; cases hv; rw [L.hsop]; decide
        unfold phiStep
        simp only [show (Ctx.make tabs g).f = g from rfl, hv]
        have : (v.op == .Phi) = false := by simpa using hnp
        simp only [this, Bool.false_eq_true, ↓reduceIte])
    rw [hps, ← Array.toList_append, ← hE'] at hrel
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
        ssRoots ((Array.range f.valueTab.size).map (ssSplit? tabs f g))
          (oS.toList.filter (CSE.rootNode f)) →
      Blk env tabs f g bid fb gb { frS with regs := setPhis ps frS.regs }
        { frT with regs := setPhis ps' frT.regs } oS oT := by
    intro ps ps' oS oT hps hpr hoS hoT hfilt
    have hnd := hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩
    obtain ⟨p1, p2, p3, p4⟩ := phis_spec hnd hps
    refine ⟨⟨⟨ce, hwf⟩, hc, hbt, hfb, by simp [setPhis_size, hA.size],
      DSE.phis_strict hwf hc hA.pre hfb hps, fun z hz v hv hph => ?_,
      typed_phis hA.typed p1 p3 p4 p2, hoS⟩, R, ⟨ce', hwg⟩, hgb, BS, hoT, hfilt, ?_,
      by simp [setPhis_size, hA.sizeT], setPhis_rr hpr hA.rr (by rw [hA.size, hA.sizeT]; exact hsz)⟩
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
  rw [hT, hGT]
  simp only
  obtain ⟨hD, -, hGsz⟩ := dinv_enter hwf hc hbt.1 hfb hA.size (CSE.pre_strict hc hA.pre).1 hen
  have hty := typed_enter hwf hbt.1 hfb hA.size hA.typed hen
  have hst := term_rel hwf hGTr ⟨hbt.1, hfb⟩ BS.kind (by rw [hsucc]) (by rw [hgid, hfid])
    BS.controls
  generalize hS : stepTerm G fb = sS at hst ⊢
  generalize stepTerm GT gb = sT at hst ⊢
  cases hst with
  | ok hn =>
    cases hn with
    | goto e =>
      refine ⟨GT, e, rfl, rfl, rfl, by rw [hGsz, hA.size], hGTs, hGTf, hGTr, hty,
        .inr ⟨bid, fb, hbt.1, hfb, hbt.2, ?_, hD, DSE.repInv_nil _ _⟩⟩
      cases e; exact stepTerm_goto_mem hS
    | ret hl hm => exact ⟨_, _, rfl, hl, hm⟩
  | panic e hm => exact ⟨_, rfl, hm⟩
  | stuck msg r => exact True.intro

/-- **Struct-store splits refine.** -/
theorem ss_refines {ce ce' : CheckEnv} (hf : check ce f = .ok ()) (hg : check ce' g = .ok ())
    (hrel : ssRel tabs f g = true) : RefinesUnder Env.Mono tabs g tabs f := by
  have hwf := check_wf hf
  have hwg := check_wf hg
  have hc := certOK_of_check (check_domCert hf)
  have R := ssRel_spec hrel
  intro env hE args mem fuel hd
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
    have hA0 : SimAt env tabs f g (entryFrame env (Ctx.make tabs f) args mem)
        (entryFrame env (Ctx.make tabs g) args mem) f.entry 0 :=
      { size := by simp [entryFrame]; rfl
        sizeT := by rw [hT]; simp
        frame := by rw [hT]
        rr := fun a v x hv h => by
          simp [entryFrame, Array.getElem?_replicate] at h
        typed := typed_replicate _ _ _ rfl
        pre := .inl rfl }
    rw [show (Ctx.make tabs g).f.entry = (Ctx.make tabs f).f.entry from cfgView_entry R.cfg]
    refine finish_refines hd (runLoop_simE (SimR env tabs f g)
      (fun frS bS iS frT bT iT hR => ?_) fuel _ _ _ _ _ _ ⟨rfl, rfl, hA0⟩ (finish_defined hd))
    obtain ⟨rfl, rfl, hA⟩ := hR
    exact step hwf hc hwg R hE hA

end GoFV.Proof.StructStore
