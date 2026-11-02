import GoFV.Proof.Pass.DecPhiBlock
import GoFV.Proof.Pass.ZCSERank
import GoFV.Proof.AtomSimStep
import GoFV.Proof.AtomSimOK
import GoFV.Proof.CheckFacts

/-!
# Decompose's phi splitting refines its input (issue #17)

`enter_ok`/`enter_panic`: a block entry of the source is matched by the target's (its `Phi`s by
`tgt_phis`, its schedule by `tgt_loop` against the source's final frame; a panic at the same
non-pure node, both schedules listing the non-pure nodes in the same sequence,
`Order.transfer_rank`). `step`: then the terminators, on refined controls. `decPhis_refines`:
lock-step simulation (`runLoop_simE`) from the entry frames.
-/

namespace GoFV.Proof.DecPhi

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.ECCheck GoFV.Opt.DecPhiCheck GoFV.Proof.AtomSim
  GoFV.Proof.Order

section
variable {tabs : Tables} {f g : Func} {ce ce' : CheckEnv}

/-- A value listed in `f` is listed in `g`. -/
theorem Hyp.listed (H : Hyp tabs f g ce ce') {x : ID} (hx : Listed f x) : Listed g x := by
  obtain ⟨b, fb, ⟨hb, hfb⟩, hxf⟩ := hx
  obtain ⟨gb, hgb, -, -, hsub, -⟩ := H.block hb hfb
  exact ⟨b, gb, ⟨H.blocks_eq ▸ hb, hgb⟩, hsub x hxf⟩

theorem frame_with {S T G : Frame} (hT : T = { S with regs := T.regs })
    (hG : G = { S with regs := G.regs }) (X : Array (Option Val)) :
    ({ T with regs := X } : Frame) = { G with regs := X } := by
  rw [hT, hG]

/-- A value of `gb` that is not in its schedule is a `Phi` whose meaning's source value is a
`Phi` of `f`. -/
theorem phi_base (H : Hyp tabs f g ce ce') {b : ID} (hb : b ∈ f.blocks) {fb gb : Block}
    (hfb : f.block? b = some fb) (hgb : g.block? b = some gb) {z : ID} (hz : z ∈ gb.values)
    {w : Value} (hw : g.value? z = some w) (hph : w.op = .Phi) {s : ID} {π : Path}
    (hm : meanAt (mean tabs f g) z = some (s, π)) :
    ∃ u, f.value? s = some u ∧ u.op = .Phi := by
  obtain ⟨gb', hgb', -, -, -, hval, -⟩ := H.block hb hfb
  rw [hgb] at hgb'; cases hgb'
  obtain ⟨w', hw', hwx, hsrc, hnew⟩ := hval z hz
  rw [hw] at hw'; cases hw'
  cases hfz : f.value? z with
  | some u =>
    obtain ⟨hzf, hok⟩ := hsrc u hfz
    obtain ⟨u', hu', huid, -⟩ := H.wf.valueId b fb ⟨hb, hfb⟩ z hzf
    rw [hfz] at hu'; cases hu'
    obtain ⟨-, hmz, hcls⟩ := srcOK_spec hok
    rw [huid, hm] at hmz; cases hmz
    refine ⟨u, hfz, ?_⟩
    rcases hcls with hc | ⟨hp, -⟩
    · exact (sameOK_spec hc).1.symm.trans hph
    · exact hp
  | none =>
    obtain ⟨s', π', hm', -, -, -, hcls⟩ := newOK_spec (hnew hfz)
    rw [hwx, hm] at hm'; cases hm'
    rcases hcls with hc | hc | hc | hc
    · obtain ⟨k, -, -, hk, -⟩ := selOK_spec hc
      rw [selIdx_phi hph] at hk; cases hk
    · obtain ⟨-, u, hu, hup, -⟩ := phiOK_spec hc
      exact ⟨u, hu, hup⟩
    · have := (makeOK_spec hc).1; rw [hph] at this; cases this
    · have := (emptyOK_spec hc).1; rw [hph] at this; cases this

/-- **The target's block against the source's frame `G`** (after the source's `Phi`s `ps` and a
part of its schedule `o`). -/
theorem bh_of (H : Hyp tabs f g ce ce') {env : Env} {S T : Frame} {b : ID} {i : Nat}
    (hA : SimAt tabs f g S T b) {fb : Block} (hfb : f.block? b = some fb) {ps : List (ID × Val)}
    (hps : fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) S i) = .ok ps) {o : Array ID}
    (ho : schedule f fb = some o) {G : Frame} (hG : G = { S with regs := G.regs })
    (hGk : ∀ a, a ∉ o.toList → G.regs[a]? = (setPhis ps S.regs)[a]?)
    (hGt : Typed (Ctx.make tabs f) G) :
    ∃ gb og psT, g.block? b = some gb ∧ schedule g gb = some og ∧
      o.toList.filter (npOf f fb) = og.toList.filter (npOf f fb) ∧
      BH tabs f g ce ce' b fb gb og G { T with regs := setPhis psT T.regs } ∧
      enterBlock env (Ctx.make tabs g) T gb i =
        evalAll env (Ctx.make tabs g) { T with regs := setPhis psT T.regs } og.toList := by
  have hb := hA.mem
  have hbg : b ∈ g.blocks := H.blocks_eq ▸ hb
  obtain ⟨gb, hgb, -, -, -, hval, of, og, hsf, hsg, hseq⟩ := H.block hb hfb
  rw [ho] at hsf; cases hsf
  obtain ⟨psT, hpsT, hphT⟩ := tgt_phis H hA hfb hgb hps
  have hndF := H.wf.valuesNodup b fb ⟨hb, hfb⟩
  have hndG := H.wg.valuesNodup b gb ⟨hbg, hgb⟩
  obtain ⟨-, -, ofm⟩ := schedule_topo (valuesOwn H.wf hb hfb) hndF ho
  obtain ⟨-, -, ogm⟩ := schedule_topo (valuesOwn H.wg hbg hgb) hndG hsg
  obtain ⟨-, -, pS3, -⟩ := phis_spec hndF hps
  obtain ⟨pT1, -, pT3, -⟩ := phis_spec hndG hpsT
  obtain ⟨gb', hgbid, hgid⟩ := H.wg.blockId b hbg
  rw [hgb] at hgbid; cases hgbid
  -- a value of `gb` outside the schedule is a `Phi`
  have hphi_of : ∀ z ∈ gb.values, z ∉ og.toList → ∃ w, g.value? z = some w ∧ w.op = .Phi :=
    fun z hz hm => by
      obtain ⟨w, hw, -, -, -⟩ := hval z hz
      exact ⟨w, hw, Classical.byContradiction fun hph => hm ((ogm z).2 ⟨hz, w, hw, hph⟩)⟩
  -- a `Phi` of `f` is not in its schedule
  have hnotO : ∀ s u, f.value? s = some u → u.op = .Phi → s ∉ o.toList := fun s u hu hup hm => by
    obtain ⟨-, u', hu', hne⟩ := (ofm s).1 hm
    rw [hu] at hu'; cases hu'; exact hne hup
  refine ⟨gb, og, psT, hgb, hsg, hseq, ⟨H, hb, hfb, hgb, hsg, frame_with hA.frame hG _,
    by simp [pT1, hA.szT], ?_, ?_, hGt⟩, ?_⟩
  · intro z hl hzo s π hm y hy
    by_cases hzg : z ∈ gb.values
    · obtain ⟨w, hw, hph⟩ := hphi_of z hzg hzo
      obtain ⟨y', hy', hrel⟩ := hphT z hzg w hw hph
      obtain ⟨u, hu, hup⟩ := phi_base H hb hfb hgb hzg hw hph hm
      rw [hGk s (hnotO s u hu hup)] at hy
      exact ⟨y', hy', hrel s π hm y hy⟩
    · have hsf : s ∉ fb.values := fun hs => hzg (H.inBlock hb hfb hgb hl hm hs)
      have hso : s ∉ o.toList := fun h => hsf ((ofm s).1 h).1
      rw [hGk s hso, pS3 s (.inl hsf)] at hy
      obtain ⟨y', hy', hyy⟩ := hA.rel z hl s π hm y hy
      exact ⟨y', by show (setPhis psT T.regs)[z]? = _; rw [pT3 z (.inl hzg)]; exact hy', hyy⟩
  · intro z hz hzo
    obtain ⟨w, hw, hph⟩ := hphi_of z hz hzo
    obtain ⟨y', hy', -⟩ := hphT z hz w hw hph
    exact ⟨y', hy'⟩
  · exact CSE.enterBlock_of_parts hpsT (by rw [hgid, sched_of_block hgb, hsg])

/-- **A block the source enters successfully is entered by the target.** -/
theorem enter_ok (H : Hyp tabs f g ce ce') {env : Env} (hE : env.Mono) {S T : Frame} {b : ID}
    {i : Nat} (hA : SimAt tabs f g S T b) {fb : Block} (hfb : f.block? b = some fb) {GS : Frame}
    (hen : enterBlock env (Ctx.make tabs f) S fb i = .ok GS) :
    ∃ gb GT, g.block? b = some gb ∧ enterBlock env (Ctx.make tabs g) T gb i = .ok GT ∧
      GT = { GS with regs := GT.regs } ∧ GT.regs.size = g.valueTab.size ∧
      GS.regs.size = f.valueTab.size ∧ MRel (mean tabs f g) g GS GT ∧
      Typed (Ctx.make tabs f) GS := by
  have hb := hA.mem
  obtain ⟨ps, o, hps, ho, hev⟩ := CSE.enterBlock_split hen (fun _ h => nomatch h)
  obtain ⟨fb', hfb', hfid⟩ := H.wf.blockId b hb
  rw [hfb] at hfb'; cases hfb'
  rw [hfid, sched_of_block hfb] at ho
  have hndF := H.wf.valuesNodup b fb ⟨hb, hfb⟩
  obtain ⟨ofn, oft, ofm⟩ := schedule_topo (valuesOwn H.wf hb hfb) hndF ho
  obtain ⟨pS1, -, -, -⟩ := phis_spec hndF hps
  obtain ⟨e1, e2, e3, e4⟩ := evalAll_spec ofn oft (by rw [pS1, hA.szS]; rfl) hev
  have hGt := typed_enter H.wf hb hfb hA.szS hA.typed hen
  obtain ⟨gb, og, psT, hgb, hsg, -, B, hentT⟩ := bh_of H (env := env) hA hfb hps ho
    (G := GS) (by rw [e1]) e3 hGt
  obtain ⟨-, -, -, -, -, hval, -⟩ := H.block hb hfb
  obtain ⟨T', hT', hI⟩ := B.tgt_loop hE (L := og.toList) (M := []) (by simp)
    fun x hx u hu hup => by
      obtain ⟨-, -, ogm⟩ := B.og
      obtain ⟨gb', hgb', -, -, -, hval', -⟩ := H.block hb hfb
      rw [hgb] at hgb'; cases hgb'
      obtain ⟨_, -, -, hsrc, -⟩ := hval' x ((ogm x).1 hx).1
      have hxf := (hsrc u hu).1
      obtain ⟨u', y, hu', hy, hev'⟩ := e4 x ((ofm x).2 ⟨hxf, u, hu, hup⟩)
      change f.value? x = some u' at hu'
      rw [hu] at hu'; cases hu'
      exact ⟨y, hy, hev'⟩
  obtain ⟨hTf, hTs, hTk, -, hTm⟩ := hI
  refine ⟨gb, T', hgb, by rw [hentT, hT'], by rw [hTf, B.hT1], by rw [hTs, B.hsz],
    by rw [e2, pS1, hA.szS], fun z hl s π hm y hy => ?_, hGt⟩
  by_cases hzo : z ∈ og.toList
  · exact hTm z hzo s π hm y hy
  · rw [hTk z hzo]; exact B.hout z hl hzo s π hm y hy

/-- **A panicking block entry.** -/
theorem enter_panic (H : Hyp tabs f g ce ce') {env : Env} (hE : env.Mono) {S T : Frame}
    {b : ID} {i : Nat} (hA : SimAt tabs f g S T b) {fb : Block} (hfb : f.block? b = some fb)
    {e : Panic} {m : Mem} (hen : enterBlock env (Ctx.make tabs f) S fb i = .panic e m) :
    ∃ gb m', g.block? b = some gb ∧ enterBlock env (Ctx.make tabs g) T gb i = .panic e m' ∧
      Mem.Refines m m' := by
  have hb := hA.mem
  have hbg : b ∈ g.blocks := H.blocks_eq ▸ hb
  obtain ⟨ps, o, hps, ho, hev⟩ := CSE.enterBlock_split hen nofun
  obtain ⟨fb', hfb', hfid⟩ := H.wf.blockId b hb
  rw [hfb] at hfb'; cases hfb'
  rw [hfid, sched_of_block hfb] at ho
  have hndF := H.wf.valuesNodup b fb ⟨hb, hfb⟩
  have hownF := valuesOwn H.wf hb hfb
  obtain ⟨ofn, oft, ofm⟩ := schedule_topo hownF hndF ho
  obtain ⟨pS1, pS2, pS3, pS4⟩ := phis_spec hndF hps
  obtain ⟨pre, r, post, G, hof, hpre, hstep⟩ := evalAll_panic_split hev
  have hpren : pre.Nodup := (List.nodup_append.1 (hof ▸ ofn)).1
  have hpret : TopoRem (argsF f) pre := topoRem_prefix (hof ▸ oft)
  obtain ⟨g1, -, g3, g4⟩ := evalAll_spec hpren hpret (by rw [pS1, hA.szS]; rfl) hpre
  have hpreo : ∀ x ∈ pre, x ∈ o.toList := fun x hx => by
    rw [hof]; exact List.mem_append_left _ hx
  have hGt : Typed (Ctx.make tabs f) G :=
    typed_evalAll (typed_phis hA.typed pS1 pS3 pS4 pS2)
      (fun x hx v hv => by
        obtain ⟨u, hu, hid, -⟩ := H.wf.valueId b fb ⟨hb, hfb⟩ x ((ofm x).1 (hpreo x hx)).1
        have hv' : f.value? x = some v := hv
        rw [hu] at hv'; cases hv'; exact hid)
      g3 g4
  obtain ⟨gb, og, psT, hgb, hsg, hseq, B, hentT⟩ := bh_of H (env := env) hA hfb hps ho (G := G)
    (by rw [g1]) (fun a ha => g3 a fun hm => ha (hpreo a hm)) hGt
  have hndG := H.wg.valuesNodup b gb ⟨hbg, hgb⟩
  have hownG := valuesOwn H.wg hbg hgb
  obtain ⟨-, -, ogm⟩ := B.og
  obtain ⟨gb', hgb', -, -, -, hval, -⟩ := H.block hb hfb
  rw [hgb] at hgb'; cases hgb'
  -- the panicking node
  obtain ⟨ur, hur, hevr⟩ : ∃ ur, f.value? r = some ur ∧
      evalValue env (Ctx.make tabs f) G ur = .panic e m := by
    unfold stepV at hstep
    cases h : (Ctx.make tabs f).f.value? r with
    | none => rw [h] at hstep; cases hstep
    | some ur => rw [h] at hstep; exact ⟨ur, h, hstep⟩
  have hrp : prio ur.op ≠ 0 := prio_panicking (evalValue_panic_op hevr)
  have hrof : r ∈ o.toList := by rw [hof]; simp
  obtain ⟨hrfb, ur', hur', hrph⟩ := (ofm r).1 hrof
  rw [hur] at hur'; cases hur'
  have hnp : npIn (schedNodes f fb).toList r = true :=
    (ZCSE.npIn_sched hownF hndF).2 ⟨hrfb, ur, hur, hrph, hrp⟩
  have hseq' : o.toList.filter (npIn (schedNodes f fb).toList) =
      og.toList.filter (npIn (schedNodes f fb).toList) := by
    rw [npIn_schedNodes hownF hndF]; exact hseq
  have hrog : r ∈ og.toList := by
    have : r ∈ o.toList.filter (npIn (schedNodes f fb).toList) := List.mem_filter.2 ⟨hrof, hnp⟩
    rw [hseq'] at this; exact (List.mem_filter.1 this).1
  obtain ⟨preT, postT, hogT⟩ := List.append_of_mem hrog
  -- a source node is an unchanged node of `g` with the same arguments
  have hsame : ∀ y, NodeIn (schedNodes f fb).toList y →
      NodeIn (schedNodes g gb).toList y ∧
        argsOf (schedNodes g gb).toList y = argsOf (schedNodes f fb).toList y := by
    intro y hy
    obtain ⟨hyf, u, hu, hup⟩ := (nodeIn_schedNodes hownF).1 hy
    obtain ⟨gb2, hgb2, -, -, hsub, -⟩ := H.block hb hfb
    rw [hgb] at hgb2; cases hgb2
    obtain ⟨w, hw, hwy, hsrc, -⟩ := hval y (hsub y hyf)
    obtain ⟨-, hok⟩ := hsrc u hu
    obtain ⟨-, -, hcls⟩ := srcOK_spec hok
    have hs : sameOK u w = true := by
      rcases hcls with hc | ⟨hp, -⟩
      · exact hc
      · exact absurd hp hup
    obtain ⟨hop, -, -, -, hargs⟩ := sameOK_spec hs
    have hwp : w.op ≠ .Phi := by rw [hop]; exact hup
    refine ⟨(nodeIn_schedNodes hownG).2 ⟨hsub y hyf, w, hw, hwp⟩, ?_⟩
    rw [argsOf_schedNodes hownG hndG (hsub y hyf) hw hwp,
      argsOf_schedNodes hownF hndF hyf hu hup, hargs]
  -- the transfer: what the target evaluates before `r`, the source did
  have hspS := schedule_spec ho
  have hspT := schedule_spec hsg
  have htr := transfer_rank hspS.topo hspS.pureFirst hspT.topo (fun x => npIn_iff) hseq'
    (k := pre.length) (k' := preT.length) (by rw [hof]; simp) (by rw [hogT]; simp) hnp
    (fun a y ha hy hay hy' => by
      obtain ⟨hNa, -⟩ := hsame a ha
      obtain ⟨hNy, hargs⟩ := hsame y hy
      exact .direct hNa (.arg hNa hNy (by rw [hargs]; exact hay)))
  have hsrc : ∀ x ∈ preT, ∀ u, f.value? x = some u → u.op ≠ .Phi →
      ∃ y, G.regs[x]? = some (some y) ∧ evalValue env (Ctx.make tabs f) G u = .ok y := by
    intro x hx u hu hup
    have hxog : x ∈ og.toList := by rw [hogT]; exact List.mem_append_left _ hx
    obtain ⟨_, -, -, hsrc', -⟩ := hval x ((ogm x).1 hxog).1
    have hxf := (hsrc' u hu).1
    have hN : NodeIn (schedNodes f fb).toList x := (nodeIn_schedNodes hownF).2 ⟨hxf, u, hu, hup⟩
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hx
    have hjl : j < preT.length := (List.getElem?_eq_some_iff.1 hj).1
    obtain ⟨i', hi', hix⟩ := htr j x hjl (by rw [hogT, List.getElem?_append_left hjl]; exact hj) hN
    rw [hof, List.getElem?_append_left hi'] at hix
    obtain ⟨u', y, hu', hy, hev'⟩ := g4 x (List.mem_of_getElem? hix)
    change f.value? x = some u' at hu'
    rw [hu] at hu'; cases hu'
    exact ⟨y, hy, hev'⟩
  obtain ⟨T', hT', hI⟩ := B.tgt_loop hE (L := preT) (M := r :: postT) hogT hsrc
  have hob := B.tgt_src hE hogT hI hur hrph
  rw [hevr] at hob
  generalize hTr : stepV env (Ctx.make tabs g) T' r = rT at hob
  cases hob with
  | panic e hm =>
    rename_i m'
    refine ⟨gb, m', hgb, ?_, hm⟩
    rw [hentT, hogT, evalAll_append, hT']
    simp only
    rw [evalAll_cons, hTr]

/-- The simulation relation: the same block and edge, `SimAt`. -/
def SimR (tabs : Tables) (f g : Func) (S : Frame) (bS : ID) (iS : Nat) (T : Frame) (bT : ID)
    (iT : Nat) : Prop :=
  bT = bS ∧ iT = iS ∧ SimAt tabs f g S T bS

/-- **One block step.** -/
theorem step (H : Hyp tabs f g ce ce') {env : Env} (hE : env.Mono) {S T : Frame} {b : ID}
    {i : Nat} (hA : SimAt tabs f g S T b) :
    StepSimE Mem.Refines (SimR tabs f g) (blockStep env (Ctx.make tabs f) S b i)
      (blockStep env (Ctx.make tabs g) T b i) := by
  unfold blockStep
  simp only [show (Ctx.make tabs f).f = f from rfl, show (Ctx.make tabs g).f = g from rfl]
  cases hfb : f.block? b with
  | none => exact True.intro
  | some fb =>
  simp only
  cases hen : enterBlock env (Ctx.make tabs f) S fb i with
  | stuck msg => exact True.intro
  | panic e m =>
    obtain ⟨gb, m', hgb, hT, hm⟩ := enter_panic H hE hA hfb hen
    rw [hgb]; simp only; rw [hT]
    exact ⟨m', rfl, hm⟩
  | ok GS =>
  obtain ⟨gb, GT, hgb, hT, hGT, hszT, hszS, hrel, hGt⟩ := enter_ok H hE hA hfb hen
  rw [hgb]; simp only; rw [hT]; simp only
  obtain ⟨gb2, hgb2, hk, hc, -, -, -⟩ := H.block hA.mem hfb
  rw [hgb] at hgb2; cases hgb2
  obtain ⟨gb', hgb', hgid, hsucc, -⟩ := CopyElim.cfgView_block H.cfg hfb
  rw [hgb] at hgb'; cases hgb'
  have hmono : Res.Rel Next.Refines (stepTerm GS fb) (stepTerm GT gb) := by
    refine stepTerm_mono2 hk hsucc hgid fun k => ?_
    unfold Sem.control
    rw [hc]
    cases hck : fb.controls[k]? with
    | none => exact .stuck _ _
    | some c =>
      simp only [Res.ofOption]
      cases hy : GS.regs[c]? with
      | none => exact .stuck _ _
      | some o =>
        cases o with
        | none => exact .stuck _ _
        | some y =>
          have hcf : Listed f c :=
            H.wf.ctrlListed b fb ⟨hA.mem, hfb⟩ c (Array.mem_of_getElem? hck)
          obtain ⟨y', hy', hyy⟩ := hrel c (H.listed hcf) c [] (H.mean_src hcf) y hy
          rw [hy']
          exact .ok hyy
  revert hmono
  cases hst : stepTerm GS fb with
  | panic e m => exact absurd hst CopyElim.stepTerm_not_panic
  | stuck msg => intro _; exact True.intro
  | ok n =>
    intro hmono
    generalize stepTerm GT gb = rT at hmono
    cases hmono with
    | ok hn =>
      cases hn with
      | goto e =>
        have hem : e ∈ fb.succs := CopyElim.stepTerm_goto_mem hst
        obtain ⟨j, hj⟩ := List.getElem?_of_mem (Array.mem_toList_iff.2 hem)
        have hebm : e.b ∈ f.blocks :=
          (H.wf.succLink b fb ⟨hA.mem, hfb⟩ j e (by simpa using hj)).1
        exact ⟨GT, e, rfl, rfl, rfl, hGT, hszS, hszT, hebm, hrel, hGt⟩
      | ret hl hm => exact ⟨_, _, rfl, hl, hm⟩

/-- **Decompose's phi splitting refines its input**: a function `g` that `decPhiCheck` accepts
against `f` (both read in the tables `tabs`, both passing `check`) refines `f` under monotone
contracts. -/
theorem decPhis_refines (h : decPhiCheck tabs f g = true) (hf : check ce f = .ok ())
    (hg : check ce' g = .ok ()) : RefinesUnder Env.Mono tabs g tabs f := by
  obtain ⟨hcfg, hown, hblk⟩ := check_spec h
  have H : Hyp tabs f g ce ce' := ⟨hcfg, hown, hblk, check_wf hf, check_wf hg⟩
  intro env hE args mem fuel hd
  refine ⟨fuel, ?_⟩
  have hc := ctx_eq (tabs := tabs) hown.symm
  have hpar : (Ctx.make tabs g).params = (Ctx.make tabs f).params := by rw [hc]
  have houts : (Ctx.make tabs g).outs = (Ctx.make tabs f).outs := by rw [hc]
  have hact : (Ctx.make tabs g).act = (Ctx.make tabs f).act := by rw [hc]
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
          regs := Array.replicate g.valueTab.size none } := entryFrame_eq hown.symm args mem
    have hA : SimAt tabs f g (entryFrame env (Ctx.make tabs f) args mem)
        (entryFrame env (Ctx.make tabs g) args mem) f.entry :=
      { frame := by rw [hT]
        szS := by simp [entryFrame]; rfl
        szT := by rw [hT]; simp
        mem := H.wf.entry
        rel := fun z _ s π _ y hy => by
          simp [entryFrame, Array.getElem?_replicate] at hy
        typed := typed_replicate _ _ _ rfl }
    refine finish_refines_mono hE hd (runLoop_simE (SimR tabs f g) (fun frS bS iS frT bT iT hR => ?_) fuel
      _ _ _ _ _ _ ⟨H.entry_eq, rfl, hA⟩ (finish_defined hd))
    obtain ⟨rfl, rfl, R⟩ := hR
    exact step H hE R

end

end GoFV.Proof.DecPhi
