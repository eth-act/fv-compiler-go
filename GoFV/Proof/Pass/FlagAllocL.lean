import GoFV.Proof.Pass.FlagAllocLWalk
import GoFV.Proof.Pass.MoveL
import GoFV.Proof.RefineSched
import GoFV.Opt.FlagAlloc

variable [GoFV.SSA.Sem.Addrs]

/-!
# flagalloc refines its input under `runSched` (`flagalloc_refinesSched`, issue #385)

If `f` passes `check` and `flagAllocB` accepts `g` for `f` (`GoFV.Proof.Pass.FlagAllocLCheck`:
same CFG, `f`'s values in order up to removed pure ones, plus clones of available values with
related arguments; `g` need not pass `check`), every `runSched` of `f` is one of `g`
(`refinesSched_of_flagAlloc`). The proof is a lock-step
simulation (`runLoopL_sim`) along the same blocks and edges with the relation `St`: kept values
have equal registers in both frames, and the values of `f` placed in strict dominators of the
current block re-evaluate to their registers (lemma (D) for `runSched`). A block entry sets the
same `Phi`s (`phis_eq`), walks the two orders (`walk`), and the terminators read related
controls. `flagalloc_refinesSched` is the pass wrapper (the pass keeps the tables).
-/

namespace GoFV.Proof.FlagAllocL

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert GoFV.Proof GoFV.Proof.MoveL Dom GoFV.Opt

variable {tabs : Tables} {f g : Func} {md : LMode} {env : Env}

/-- The relation at a block entry: `b` a listed tree block, frames of one activation, kept
values agree, and `f`'s values in strict dominators of `b` re-evaluate to their registers. -/
structure St (tabs : Tables) (f g : Func) (md : LMode) (env : Env) (S T : Frame) (b : ID) :
    Prop where
  hb : b ∈ f.blocks
  tree : ((make f).depthOf b).isSome
  fr : T = { S with regs := T.regs }
  szS : S.regs.size = f.valueTab.size
  szT : T.regs.size = g.valueTab.size
  kept : ∀ x, keptB f g x = true → T.regs[x]? = S.regs[x]?
  anc : ∀ x v, Placed f x v → Anc (make f) v.block b → v.block ≠ b → v.op ≠ .Phi →
    ∃ y, S.regs[x]? = some (some y) ∧ evalValueL md env (Ctx.makeSched tabs f) S v = .ok y

/-- The facts the simulation uses. -/
structure Setup (tabs : Tables) (cert : Array (Option ID)) (f g : Func) : Prop where
  wf : ∃ ce, WF ce f
  cf : CertOK f
  ok : flagAllocWith tabs cert f g = true

/-! ## `Phi`s -/

private theorem filterMapM_filter {α : Type} {step : ID → Res (Option α)} {p : ID → Bool} :
    ∀ {l : List ID}, (∀ z ∈ l, p z = false → step z = .ok none) →
      l.filterMapM step = (l.filter p).filterMapM step
  | [], _ => rfl
  | z :: l, h => by
    have ih := filterMapM_filter (step := step) (p := p) (l := l)
      (fun y hy => h y (List.mem_cons_of_mem _ hy))
    cases hp : p z with
    | false =>
      rw [List.filter_cons_of_neg (by simp [hp]), List.filterMapM_cons, h z List.mem_cons_self hp]
      exact ih
    | true =>
      rw [List.filter_cons_of_pos hp, List.filterMapM_cons, List.filterMapM_cons, ih]

private theorem filterMapM_congr {α : Type} {s1 s2 : ID → Res (Option α)} :
    ∀ {l : List ID}, (∀ z ∈ l, s1 z = s2 z) → l.filterMapM s1 = l.filterMapM s2
  | [], _ => rfl
  | z :: l, h => by
    rw [List.filterMapM_cons, List.filterMapM_cons, h z List.mem_cons_self,
      filterMapM_congr (fun y hy => h y (List.mem_cons_of_mem _ hy))]

private theorem phiStep_nonphi {h : Func} {tabs : Tables} {blk : Block}
    (hid : ∀ x ∈ blk.values, ∃ v, h.value? x = some v) (S : Frame) (i : Nat) :
    ∀ z ∈ blk.values.toList, isPhiIn h z = false →
      phiStepL md (Ctx.makeSched tabs h) S i z = .ok none := by
  intro z hz hp
  obtain ⟨v, hv⟩ := hid z (Array.mem_toList_iff.1 hz)
  unfold isPhiIn at hp
  rw [hv] at hp
  have hp' : (v.op == .Phi) = false := by simpa using hp
  unfold phiStepL
  rw [makeSched_f, hv]
  simp only [hp', Bool.false_eq_true, ite_false]

/-- **The `Phi`s of a block entry**: `g` collects `f`'s. -/
theorem phis_eq {ce : CheckEnv} {b : ID} {fb gb : Block} (H : BHyp ce f g b fb gb)
    (hph : phisOK f g fb gb = true) {S T : Frame}
    (hkept : ∀ x, keptB f g x = true → T.regs[x]? = S.regs[x]?) {i : Nat} {ps : List (ID × Val)}
    (hps : fb.values.toList.filterMapM (phiStepL md (Ctx.makeSched tabs f) S i) = .ok ps) :
    gb.values.toList.filterMapM (phiStepL md (Ctx.makeSched tabs g) T i) = .ok ps := by
  obtain ⟨hl, hv⟩ := phisOK_spec hph
  rw [filterMapM_filter (p := isPhiIn f) (phiStep_nonphi (fun x hx =>
    (H.wf.valueId b fb ⟨H.hb, H.hfb⟩ x hx).imp fun _ h => h.1) S i)] at hps
  rw [filterMapM_filter (p := isPhiIn g) (phiStep_nonphi (fun x hx =>
    (H.og.valueId x hx).imp fun _ h => h.1) T i), ← hps,
    ← Array.toList_filter, ← Array.toList_filter, ← hl]
  refine filterMapM_congr fun z hz => ?_
  obtain ⟨fv, gv, hfv, hgv, hop, hty, hargs, hk⟩ := hv z (Array.mem_toList_iff.1 hz)
  unfold phiStepL
  rw [makeSched_f, makeSched_f, hfv, hgv]
  dsimp only
  rw [hop, hargs, tys_eq H.low hgv hfv hty]
  split
  · split
    · rename_i a ha
      rw [hkept a (hk a (Array.mem_of_getElem? ha))]
    · rfl
  · rfl

/-! ## One block -/

theorem frame_rel {S T : Frame} (h : T = { S with regs := T.regs }) (r r' : Array (Option Val)) :
    ({ T with regs := r } : Frame) = { ({ S with regs := r' } : Frame) with regs := r } := by
  obtain ⟨⟩ := S; obtain ⟨⟩ := T; cases h; rfl

private theorem setPhis_agree : ∀ (ps : List (ID × Val)) (r r' : Array (Option Val)) (x : ID),
    x < r.size → x < r'.size → r[x]? = r'[x]? → (setPhis ps r)[x]? = (setPhis ps r')[x]?
  | [], _, _, _, _, _, h => h
  | (id, y) :: ps, r, r', x, h1, h2, h => by
    unfold setPhis; rw [List.foldl_cons, List.foldl_cons]
    refine setPhis_agree ps _ _ x (by simpa using h1) (by simpa using h2) ?_
    by_cases hx : id = x
    · subst hx; simp [h1, h2]
    · simp [Array.getElem?_setIfInBounds_ne hx, h]

/-- **One block step** of the simulation. -/
theorem stepB {cert : Array (Option ID)} (SU : Setup tabs cert f g) {S T : Frame} {b : ID}
    {i : Nat} (hR : St tabs f g md env S T b) :
    StepSim (fun S T b _ => St tabs f g md env S T b)
      (blockStepL md env (Ctx.makeSched tabs f) S b i)
      (blockStepL md env (Ctx.makeSched tabs g) T b i) := by
  obtain ⟨ce, hwf⟩ := SU.wf
  obtain ⟨-, -, hown, hlow, hall⟩ := flagAllocWith_spec SU.ok
  obtain ⟨fb, gb, hfb, hgb, hO, hk, hai, hsu, -, hph, hoG, hoF, hW⟩ := blockB_spec (hall b hR.hb)
  have H : BHyp ce f g b fb gb := ⟨hwf, hO, SU.cf, hR.hb, hfb, hgb, hR.tree, hlow, hown⟩
  obtain ⟨fb', hfb', hfid⟩ := hwf.blockId b hR.hb
  rw [hfb] at hfb'; cases hfb'
  have hgid := hO.id
  unfold blockStepL
  rw [makeSched_f, makeSched_f, hfb, hgb]
  dsimp only
  cases hps : fb.values.toList.filterMapM (phiStepL md (Ctx.makeSched tabs f) S i) with
  | panic e m => exact absurd hps filterMapM_phiL_not_panic
  | stuck msg =>
    rw [enterBlockL_eq, hps]
    exact True.intro
  | ok ps =>
  have hpsT := phis_eq (tabs := tabs) H hph hR.kept hps
  rcases hoF with hoF | hoF
  · rw [enterBlockL_eq, hps, hfid, sched_makeSched hfb, hoF]
    exact True.intro
  rw [MoveL.enterBlockL_of hps (by rw [hfid, sched_makeSched hfb, hoF]),
    MoveL.enterBlockL_of hpsT (by rw [hgid, sched_makeSched hgb, hoG])]
  -- the frames after the `Phi`s
  have hsub := (filterMapM_phiL hps).1
  have hpsb : ∀ p ∈ ps, p.1 ∈ fb.values := fun p hp =>
    Array.mem_toList_iff.1 (hsub.subset (List.mem_map_of_mem hp))
  have hS0 : ({ S with regs := setPhis ps S.regs } : Frame) =
      { S with regs := ({ S with regs := setPhis ps S.regs } : Frame).regs } := rfl
  have hF0 : FInv tabs f md env b fb (fb.values.filter (!isPhiIn f ·)).toList []
      { S with regs := setPhis ps S.regs } := by
    refine ⟨by simp [setPhis_size, hR.szS],
      (hwf.valuesNodup b fb ⟨hR.hb, hfb⟩).sublist (by rw [Array.toList_filter]; exact List.filter_sublist),
      fun x hx => ?_, fun x hx => absurd hx List.not_mem_nil, fun x v hx hanc hne hnp => ?_,
      fun x hx hnp => .inr ?_⟩
    · rw [Array.toList_filter] at hx
      exact Array.mem_toList_iff.1 ((List.mem_filter.1 hx).1)
    · obtain ⟨y, hy, hev⟩ := hR.anc x v hx hanc hne hnp
      have hnot : ∀ z, z ∈ ps.map Prod.fst → blockOf f z = b ∧
          ∀ w, f.value? z = some w → w.block = b := by
        intro z hm
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hm
        obtain ⟨w', hw', -, hwb⟩ := hwf.valueId b fb ⟨hR.hb, hfb⟩ p.1 (hpsb p hp)
        refine ⟨by unfold blockOf; rw [hw']; exact hwb, fun w hw => ?_⟩
        rw [hw] at hw'; cases hw'; exact hwb
      have hxn : x ∉ ps.map Prod.fst := fun hm => hne ((hnot x hm).2 v hx.1)
      refine ⟨y, by show (setPhis ps S.regs)[x]? = _; rw [setPhis_not_mem ps S.regs x hxn]; exact hy,
        ?_⟩
      rw [← hev]
      refine (evalValueL_congr hS0 fun a ha => ?_).symm
      have han : a ∉ ps.map Prod.fst := fun hm => by
        obtain ⟨hv, hvb, blk, hblk, hxv⟩ := hx
        have hu := SU.cf.domRel.uses hvb hblk (Anc.left SU.cf.parents hanc) hxv hv hnp ha
        rw [(hnot a hm).1] at hu
        exact hne (Anc.antisymm SU.cf.parents hanc hu)
      show S.regs[a]? = (setPhis ps S.regs)[a]?
      rw [setPhis_not_mem ps S.regs a han]
    · rw [Array.toList_filter]
      exact List.mem_filter.2 ⟨Array.mem_toList_iff.2 hx, by simp [hnp]⟩
  have hR0 : RInv f g gb (fb.values.filter (!isPhiIn f ·)).toList
      (gb.values.filter (!isPhiIn g ·)).toList [] { S with regs := setPhis ps S.regs }
      { T with regs := setPhis ps T.regs } := by
    refine ⟨frame_rel hR.fr _ _, by simp [setPhis_size, hR.szT],
      hO.nd.sublist (by rw [Array.toList_filter]; exact List.filter_sublist),
      fun x hx => ?_, fun x hx => ?_, fun c o hc => absurd hc List.not_mem_nil⟩
    · rw [Array.toList_filter] at hx
      exact Array.mem_toList_iff.1 ((List.mem_filter.1 hx).1)
    · obtain ⟨fv, gv, hfv, hgv, -⟩ := keptB_spec hx
      exact setPhis_agree ps _ _ x (by rw [hR.szT]; exact lt_of_value? hgv)
        (by rw [hR.szS]; exact lt_of_value? hfv) (hR.kept x hx)
  have hw := walk (tabs := tabs) (md := md) (env := env) (cert := cert) H _ _ _ [] [] _ _ rfl hW
    hF0 hR0
  revert hw
  cases hS : evalAllL md env (Ctx.makeSched tabs f) { S with regs := setPhis ps S.regs }
      (fb.values.filter (!isPhiIn f ·)).toList with
  | stuck msg => intro _; exact True.intro
  | panic e m =>
    intro hw
    simp only [WOut] at hw
    rw [hw]
    rfl
  | ok S' =>
  intro hw
  obtain ⟨T', hT', P', C', hF', hR', hctl⟩ := hw
  rw [hT']
  dsimp only
  obtain ⟨hargs, hcase⟩ := ctrlsOK_spec hctl
  obtain ⟨-, hc2⟩ := args2_spec hargs
  cases hst : stepTermL S' fb with
  | stuck msg => exact True.intro
  | panic e m => exact absurd hst Dead.stepTermL_not_panic
  | ok n =>
  -- the relation at a successor
  have hnext : ∀ e, e ∈ fb.succs → St tabs f g md env S' T' e.b := fun e he => by
    have hed := SU.cf.domRel.edge hR.hb hfb hR.tree he
    obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.1 he
    refine ⟨(hwf.succLink b fb ⟨hR.hb, hfb⟩ j e hj).1, hed.1, hR'.fr, hF'.sz, hR'.sz, hR'.kept,
      fun x v hx hanc hne hnp => ?_⟩
    have hab := hed.2 _ hanc hne
    by_cases hvb : v.block = b
    · obtain ⟨hv, -, blk, hblk, hxv⟩ := hx
      rw [hvb, hfb] at hblk; cases hblk
      have hnp' : isPhiIn f x = false := by unfold isPhiIn; rw [hv]; simpa using hnp
      rcases hF'.cover x hxv hnp' with hP | hP
      · obtain ⟨-, -, v', y, hv', hy, hev, -⟩ := hF'.pre x hP
        rw [hv] at hv'; cases hv'
        exact ⟨y, hy, hev⟩
      · exact absurd hP List.not_mem_nil
    · exact hF'.anc x v hx hab hvb hnp
  rcases hcase with hce | harm
  · have hag : ∀ c ∈ fb.controls, T'.regs[c]? = S'.regs[c]? := fun c hc => by
      obtain ⟨k, hk'⟩ := Array.mem_iff_getElem?.1 hc
      obtain ⟨c', hc', hr⟩ := hc2 k c (by rw [Array.getElem?_toList]; exact hk')
      rw [Array.getElem?_toList, hce, hk'] at hc'
      cases hc'
      rcases argRel_spec hr with ⟨-, hkc⟩ | hcc
      · exact hR'.kept c hkc
      · obtain ⟨⟨y, h1, h2⟩, -, -⟩ := hR'.clones c c hcc
        rw [h1, h2]
    rcases Dead.stepTermL_rel (.inl hk) hai hce hag hst with ⟨k, e, rfl, he, -, hst'⟩ |
      ⟨rs, m, rfl, hst'⟩
    · rw [hst']
      unfold succ
      rw [hsu, he]
      exact ⟨T', rfl, hnext e (Array.mem_of_getElem? he)⟩
    · rw [hst']
      exact ⟨rs, rfl, RefinesList.refl rs⟩
  · obtain ⟨v, k, hcv, hs, hT⟩ := Dead.stepTermL_arm harm hst
    have hcv' : Sem.control T' gb 0 = .ok v := by
      unfold Sem.control at hcv ⊢
      cases hc0 : fb.controls[0]? with
      | none => simp only [hc0] at hcv; cases hcv
      | some c =>
        simp only [hc0] at hcv
        have hy : S'.regs[c]? = some (some v) := by
          cases h1 : S'.regs[c]? with
          | none => simp only [h1] at hcv; cases hcv
          | some o =>
            cases o with
            | none => simp only [h1] at hcv; cases hcv
            | some w => simp only [h1] at hcv; cases hcv; rfl
        obtain ⟨c', hc', hr⟩ := hc2 0 c (by rw [Array.getElem?_toList]; exact hc0)
        rw [Array.getElem?_toList] at hc'
        simp only [hc', argRel_regs hR' hr hy]
        rfl
    rw [hT T' gb hk hai hcv']
    obtain ⟨e, he, rfl⟩ := Dead.succ_ok hs
    unfold succ
    rw [hsu, he]
    exact ⟨T', rfl, hnext e (Array.mem_of_getElem? he)⟩

/-! ## The runs -/

private theorem entryFrame_rel {ctx ctx' : Ctx} (htabs : ctx'.tabs = ctx.tabs)
    (hpt : ctx'.paramTys = ctx.paramTys) (hloc : ctx'.locals = ctx.locals)
    (hact : ctx'.act = ctx.act) (args : List Val) (mem : Mem) :
    entryFrame env ctx' args mem =
      { entryFrame env ctx args mem with regs := Array.replicate ctx'.f.valueTab.size none } := by
  unfold entryFrame frameMem frameAllocs
  rw [htabs, hpt, hloc, hact]

private theorem paramTys_makeL (tabs : Tables) (f : Func) :
    (Ctx.makeL tabs f).paramTys = (Ctx.make tabs f).paramTys := by
  unfold Ctx.makeL; split <;> rfl

private theorem locals_makeL (tabs : Tables) (f : Func) :
    (Ctx.makeL tabs f).locals = (Ctx.make tabs f).locals := by
  unfold Ctx.makeL; split <;> rfl

/-- **A rewrite validated by `flagAllocWith` refines under `runSched`.** -/
theorem refinesSched_of_flagAllocWith {cert : Array (Option ID)} (SU : Setup tabs cert f g) :
    RefinesSched tabs g tabs f := by
  obtain ⟨ce, hwf⟩ := SU.wf
  have hcf := SU.cf
  obtain ⟨hent, -, hown, hlow, -⟩ := flagAllocWith_spec SU.ok
  have hpar : (Ctx.makeSched tabs g).params = (Ctx.makeSched tabs f).params := params_eq hown
  have hmd : LMode.sched g = LMode.sched f := by unfold LMode.sched; rw [hlow]
  intro env args mem fuel hd
  refine ⟨fuel, ?_⟩
  unfold runSched runCtxL at hd ⊢
  rw [hmd, hpar]
  split
  · rename_i hn; simp only [hn] at hd; exact hd.elim
  · rename_i hn
    simp only [hn, Bool.false_eq_true, ite_false] at hd
    have houts : (Ctx.makeSched tabs g).outs = (Ctx.makeSched tabs f).outs := by
      show (Ctx.makeL tabs g).outs = (Ctx.makeL tabs f).outs
      rw [outs_makeL, outs_makeL]
      simp only [Ctx.make, abiParams, hown]
    have hdefers : (Ctx.makeSched tabs g).defers = (Ctx.makeSched tabs f).defers := by
      show (Ctx.makeL tabs g).defers = (Ctx.makeL tabs f).defers
      unfold Ctx.makeL; split <;> split <;> rfl
    have hentry := entryFrame_rel (env := env) (ctx := Ctx.makeSched tabs f)
      (ctx' := Ctx.makeSched tabs g) (by rw [makeSched_tabs, makeSched_tabs])
      (by
        show (Ctx.makeL tabs g).paramTys = (Ctx.makeL tabs f).paramTys
        rw [paramTys_makeL, paramTys_makeL]; simp only [Ctx.make, abiParams, hown])
      (by
        show (Ctx.makeL tabs g).locals = (Ctx.makeL tabs f).locals
        rw [locals_makeL, locals_makeL]; simp only [Ctx.make, abiParams, hown])
      act_eq args mem
    rw [hentry, houts, hdefers, act_eq (f := f) (g := g), makeSched_f, makeSched_f, hent]
    rw [makeSched_f] at hd
    have h0 : St tabs f g (LMode.sched f) env (entryFrame env (Ctx.makeSched tabs f) args mem)
        { entryFrame env (Ctx.makeSched tabs f) args mem with
          regs := Array.replicate g.valueTab.size none } f.entry := by
      refine ⟨hwf.entry, hcf.domRel.entry, rfl, by simp [entryFrame, makeSched_f], by simp,
        fun x hx => ?_, fun x v hx ha hne _ => absurd (hcf.domRel.entry_anc ha) hne⟩
      obtain ⟨fv, gv, hfv, hgv, -⟩ := keptB_spec hx
      simp [entryFrame, makeSched_f, lt_of_value? hfv, lt_of_value? hgv]
    exact finish_refines hd (runLoopL_sim (fun S T b _ => St tabs f g (LMode.sched f) env S T b)
      (fun _ _ _ _ hR => stepB SU hR) fuel _ _ _ _ h0 (finish_defined hd))

/-- **flagalloc's rewrites validated by `flagAllocB` refine under `runSched`.** -/
theorem refinesSched_of_flagAlloc {ce : CheckEnv} {tabs : Tables} {f g : Func}
    (hf : check ce f = .ok ()) (hv : flagAllocB tabs f g = true) :
    RefinesSched tabs g tabs f :=
  refinesSched_of_flagAllocWith ⟨⟨ce, check_wf hf⟩, certOK_of_check (check_domCert hf), hv⟩

/-- **flagalloc refines its input under `runSched`** (issue #385): for an input that passes
`check` and a pair the validator `flagAllocB` accepts. -/
theorem flagalloc_refinesSched {penv : PassEnv} {f : Func} {out : PassOut} {ce : CheckEnv}
    (h : flagallocPass penv f = .ok out) (hf : check ce f = .ok ())
    (hv : flagAllocB penv.tables f out.func = true) :
    RefinesSched out.tables out.func penv.tables f := by
  simp only [flagallocPass, Pass.ofFunc, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · cases h
    exact refinesSched_of_flagAlloc hf hv

end GoFV.Proof.FlagAllocL
