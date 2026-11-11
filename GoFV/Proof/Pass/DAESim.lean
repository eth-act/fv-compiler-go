import GoFV.Proof.Pass.DAEEnter

variable [GoFV.SSA.Sem.Addrs]

/-!
# dead auto elim: the simulation

Lock-step simulation (`runLoop_simD`) in which, at each block entry (`SimAt`), the target's
registers are related to the source's (`VR`: equal, or memories equal outside the eliminated
frame temporaries `U`), the source's registers satisfy the invariant and are typed, and the
frame's inputs avoid `U`. One block step (`step`): related `Phi`s (`phis_rel`), the block's
schedule (`BlkSim.okCase`, `BlkSim.panicCase`), the terminator (`stepTerm_rel`). The entry frame
satisfies `SimAt` when the run's inputs avoid every frame temporary (`InitAvoids`, `entry_ok`);
`finish_rel` turns the related outcomes into refinement. `refines_of_rel`: functions related by
`ARelD` refine under frame-safe contracts.
-/

namespace GoFV.Proof.DAE

open GoFV.SSA GoFV.SSA.Sem GoFV.SSA.DomCert Dom GoFV.Proof.CopyElim GoFV.Opt GoFV.Opt.DAE

variable {env : Env} {tabs : Tables} {f g : Func} {T : ID → Option AuxRef} {E : List AuxRef}

/-- The simulation relation at the entry of block `bid` along edge `i`. -/
structure SimAt (env : Env) (tabs : Tables) (f : Func) (T : ID → Option AuxRef) (E : List AuxRef)
    (frS frT : Frame) (bid : ID) (i : Nat) : Prop where
  size : frS.regs.size = f.valueTab.size
  sizeT : frT.regs.size = frS.regs.size
  frame : frT = { frS with regs := frT.regs }
  agree : RegsRel (UE E) frS.regs frT.regs
  pr : RegsP (SPr tabs f T E) frS
  fok : FrameOK (UE E) frS
  pre : CSE.Pre env tabs f #[] frS bid i

/-- **One block step of dead auto elim's simulation.** -/
theorem step (hfs : env.FrameSafe) {ce : CheckEnv} (hwf : WF ce f) (hc : CertOK f)
    (R : ARelD tabs f g T E) {frS frT : Frame} {bid : ID} {i : Nat}
    (hA : SimAt env tabs f T E frS frT bid i) :
    StepRelD (UE E) (fun frS frT bid i => SimAt env tabs f T E frS frT bid i)
      (blockStep env (Ctx.make tabs f) frS bid i) (blockStep env (Ctx.make tabs g) frT bid i) := by
  have hbt := CSE.pre_tree hwf hc hA.pre
  unfold blockStep
  simp only [show (Ctx.make tabs f).f = f from rfl, show (Ctx.make tabs g).f = g from rfl]
  cases hfb : f.block? bid with
  | none => exact True.intro
  | some fb =>
  obtain ⟨gb, hgb, hkind, hvals, hctl, -⟩ := R.block bid hbt.1 fb hfb
  obtain ⟨gb', hgb', hgid, hsucc, -⟩ := cfgView_block R.cfg hfb
  rw [hgb] at hgb'; cases hgb'
  obtain ⟨fb', hfb', hfid⟩ := hwf.blockId bid hbt.1
  rw [hfb] at hfb'; cases hfb'
  rw [hgb]
  simp only
  -- the parts of the source's block entry, and the target's
  have parts : ∀ r, enterBlock env (Ctx.make tabs f) frS fb i = r → (∀ msg, r ≠ .stuck msg) →
      ∃ ps psT oS oT, fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) frS i) = .ok ps ∧
        PRel (UE E) ps psT ∧ schedule f fb = some oS ∧ schedule g gb = some oT ∧
        oT.toList.filter (CSE.rootNode g) = oS.toList.filter (CSE.rootNode g) ∧
        evalAll env (Ctx.make tabs f) { frS with regs := setPhis ps frS.regs } oS.toList = r ∧
        enterBlock env (Ctx.make tabs g) frT gb i =
          evalAll env (Ctx.make tabs g) { frT with regs := setPhis psT frT.regs } oT.toList := by
    intro r hen hr
    obtain ⟨ps, oS, hps, hsched, hev⟩ := CSE.enterBlock_split hen hr
    rw [hfid, sched_of_block hfb] at hsched
    obtain ⟨oT, hoT, hfilt⟩ := R.sched bid hbt.1 fb gb hfb hgb oS hsched
    obtain ⟨psT, hpsT, hpr⟩ := phis_rel R hA.agree i hps
    refine ⟨ps, psT, oS, oT, hps, hpr, hsched, hoT, hfilt, hev, CSE.enterBlock_of_parts ?_ ?_⟩
    · rw [hvals]; exact hpsT
    · rw [hgid, hfid, sched_of_block hgb, hoT]
  -- the block's evaluation
  have blk : ∀ ps psT oS oT,
      fb.values.toList.filterMapM (phiStep (Ctx.make tabs f) frS i) = .ok ps → PRel (UE E) ps psT →
      schedule f fb = some oS → schedule g gb = some oT →
      oT.toList.filter (CSE.rootNode g) = oS.toList.filter (CSE.rootNode g) →
      BlkSim env tabs f g T E bid fb gb { frS with regs := setPhis ps frS.regs }
        { frT with regs := setPhis psT frT.regs } oS oT := by
    intro ps psT oS oT hps hpr hoS hoT hfilt
    obtain ⟨-, -, -, hphiS⟩ := phis_spec (hwf.valuesNodup _ _ ⟨hbt.1, hfb⟩) hps
    refine ⟨R, hfs, ⟨ce, hwf⟩, hc, hbt, hfb, hgb, by simp [setPhis_size, hA.size],
      DSE.phis_strict hwf hc hA.pre hfb hps, fun z hz v hv hph => ?_, ?_,
      by simp [setPhis_size, hA.sizeT], setPhis_rel hpr hA.agree hA.sizeT,
      phis_pr R hwf ⟨hbt.1, hfb⟩ hA.pr hps,
      ⟨hA.fok.images, hA.fok.closure, hA.fok.mem0⟩, hoS, hoT, hfilt⟩
    · obtain ⟨a, y, -, -, h⟩ := hphiS z hz v hv hph (by rw [hA.size]; exact lt_of_value? hv)
      exact ⟨_, h⟩
    · conv => lhs; rw [hA.frame]
  cases hen : enterBlock env (Ctx.make tabs f) frS fb i with
  | stuck msg => exact True.intro
  | panic e m =>
    obtain ⟨ps, psT, oS, oT, hps, hpr, hoS, hoT, hfilt, hev, hT⟩ := parts _ hen nofun
    obtain ⟨m', hm', hEq, heA, hmA⟩ := (blk ps psT oS oT hps hpr hoS hoT hfilt).panicCase hev
    rw [hT, hm']
    exact ⟨m', rfl, hEq, heA, hmA⟩
  | ok G =>
  obtain ⟨ps, psT, oS, oT, hps, hpr, hoS, hoT, hfilt, hev, hT⟩ := parts _ hen nofun
  have K := blk ps psT oS oT hps hpr hoS hoT hfilt
  obtain ⟨GT, hGT, hGTf, hGTs, hGTa⟩ := K.okCase hev
  have hGpr : RegsP (SPr tabs f T E) G := K.srcPr (fun x hx => K.memS.1 hx) hev
  rw [hT, hGT]
  simp only
  obtain ⟨hD, hGfr, hGsz⟩ := dinv_enter hwf hc hbt.1 hfb hA.size (CSE.pre_strict hc hA.pre).1 hen
  obtain ⟨hgo, hret⟩ := stepTerm_rel (G := G) (GT := GT) (b := fb) (b' := gb) hkind hsucc hgid hctl
    hGTa
  cases hstp : stepTerm G fb with
  | ok n =>
    cases n with
    | goto e =>
      rw [hgo e hstp]
      refine ⟨GT, rfl, by rw [hGsz, hA.size], by rw [hGTs], hGTf, hGTa, hGpr, ?_,
        .inr ⟨bid, fb, hbt.1, hfb, hbt.2, ?_, hD, DSE.repInv_nil _ _⟩⟩
      · rw [hGfr]; exact ⟨hA.fok.images, hA.fok.closure, hA.fok.mem0⟩
      · cases e; exact stepTerm_goto_mem hstp
    | ret rs m =>
      obtain ⟨rs', m', h1, h2, h3⟩ := hret rs m hstp
      rw [h1]
      exact ⟨rs', m', rfl, h2, h3⟩
  | panic e m => exact absurd hstp stepTerm_not_panic
  | stuck msg => exact True.intro

/-! ## The entry -/

/-- A byte avoiding every frame temporary of activation 0 avoids `U`. -/
theorem byte_avoids_UE {x : Byte} (h : ∀ n, Byte.Avoids (· = .temp 0 n) x) :
    Byte.Avoids (UE E) x := by
  cases x with
  | frag p k => rintro ⟨n, -, hn⟩; exact h n hn
  | _ => trivial

theorem mem_avoids_UE {m : Mem} (h : ∀ n, m.Avoids (· = .temp 0 n)) : m.Avoids (UE E) := by
  intro b a hm hb x hx
  cases x with
  | frag p k =>
    rintro ⟨n, hnE, hn⟩
    exact h n b a hm (fun hb' => hb ⟨n, hnE, hb'⟩) _ hx hn
  | _ => trivial

mutual
/-- A value avoiding every frame temporary of activation 0 avoids `U`. -/
theorem val_avoids_UE : {v : Val} → (∀ n, v.Avoids (· = .temp 0 n)) → Val.Avoids (UE E) v
  | .ptr p, h => by rintro ⟨n, -, hn⟩; exact h n hn
  | .tuple vs, h => valList_avoids_UE (vs := vs) h
  | .agg vs, h => valList_avoids_UE (vs := vs) h
  | .blob bs, h => fun x hx => byte_avoids_UE fun n => h n x hx
  | .mem m, h => mem_avoids_UE h
  | .int _ _, _ | .bool _, _ | .empty, _ | .poison, _ => trivial
theorem valList_avoids_UE : {vs : List Val} → (∀ n, Val.AvoidsList (· = .temp 0 n) vs) →
    Val.AvoidsList (UE E) vs
  | [], _ => trivial
  | _ :: _, h => ⟨val_avoids_UE fun n => (h n).1, valList_avoids_UE fun n => (h n).2⟩
end

theorem addGlobals_avoids {env : Env} (hg : ∀ g ∈ env.globals, BAv (UE E) g.2.data) {m : Mem}
    (hm : m.Avoids (UE E)) : (addGlobals env m).Avoids (UE E) := by
  unfold addGlobals
  generalize env.globals = gs at hg
  induction gs generalizing m with
  | nil => exact hm
  | cons g gs ih =>
    simp only [List.foldl_cons]
    refine ih ?_ (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨name, a⟩ := g
    simp only
    split
    · exact hm
    · exact memAvoids_set hm fun _ => hg _ List.mem_cons_self

theorem frameAllocs_avoids {ctx : Ctx} {images : Array (Array Byte)}
    (hi : ∀ img ∈ images, BAv (UE E) img) {m : Mem} (hm : m.Avoids (UE E)) :
    (frameAllocs ctx images m).Avoids (UE E) := by
  unfold frameAllocs
  have h0 := memAvoids_set (b := .outargs ctx.act)
    (a := { data := Array.replicate (outargsSize ctx.tabs) .poison }) hm
    fun _ => bav_replicate_poison _ _
  generalize m.set (.outargs ctx.act) _ = m0 at h0
  generalize ctx.locals.toList = ls
  rw [← Array.foldl_toList]
  generalize ctx.locals.toList = ls
  induction ls generalizing m0 with
  | nil => exact h0
  | cons l ls ih =>
    simp only [List.foldl_cons]
    refine ih _ (memAvoids_set h0 fun _ => ?_)
    obtain ⟨n, sz, pi⟩ := l
    simp only
    split
    · rename_i img himg
      split
      · simp only [Option.bind_eq_some_iff] at himg
        obtain ⟨k, -, hk⟩ := himg
        exact hi img (Array.mem_of_getElem? hk)
      · exact bav_replicate_poison _ _
    · exact bav_replicate_poison _ _

/-- **The entry frame** satisfies `SimAt` when the run's inputs avoid every frame temporary. -/
theorem entry_ok {args : List Val} {mem : Mem} (hinit : InitAvoids env args mem) :
    SimAt env tabs f T E (entryFrame env (Ctx.make tabs f) args mem)
      (entryFrame env (Ctx.make tabs f) args mem) f.entry 0 := by
  have hargs : ∀ v ∈ args, Val.Avoids (UE E) v := fun v hv =>
    val_avoids_UE fun n => (hinit 0 n).1 v hv
  have hmem : mem.Avoids (UE E) := mem_avoids_UE fun n => (hinit 0 n).2.1
  have hglob : ∀ g ∈ env.globals, BAv (UE E) g.2.data := fun g hg x hx =>
    byte_avoids_UE fun n => (hinit 0 n).2.2.2.1 g hg x hx
  have hclo : ∀ c, env.closure = some c → Val.Avoids (UE E) c := fun c hc =>
    val_avoids_UE fun n => (hinit 0 n).2.2.2.2 c hc
  have himg : ∀ img ∈ (args.toArray.zip (Ctx.make tabs f).paramTys).map
      (fun (a, t) => encode t a), BAv (UE E) img := by
    intro img hi
    simp only [Array.mem_map] at hi
    obtain ⟨⟨a, t⟩, hm, rfl⟩ := hi
    have ha : a ∈ args := by
      have := (Array.of_mem_zip hm).1
      simpa using this
    exact encode_avoids t (hargs a ha)
  refine ⟨by simp [Ctx.make, entryFrame], rfl, rfl, fun z y h => ⟨y, h, .refl y⟩,
    fun z y h => ?_, ⟨himg, hclo, ?_⟩, .inl rfl⟩
  · simp [entryFrame, Array.getElem?_replicate] at h
  · exact frameAllocs_avoids himg (addGlobals_avoids hglob hmem)

/-- The open-coded defer variables are not eliminated (`ARelD.nodefer`). -/
theorem deferAvoid_UE (R : ARelD tabs f g T E) : DeferRel.DeferAvoid (UE E) (deferInfo tabs) 0 := by
  have hv := DeferRel.deferInfo_vars tabs
  refine ⟨fun nb hb hu => ?_, fun i sn hs hu => ?_⟩
  · obtain ⟨n, hnE, he⟩ := hu
    split at he
    · cases he
    · cases he
      have := R.nodefer _ hnE
      rw [hv.1 nb hb] at this; cases this
  · obtain ⟨n, hnE, he⟩ := hu
    split at he
    · cases he
    · cases he
      have := R.nodefer _ hnE
      rw [hv.2 i sn hs] at this; cases this

/-- **dead auto elim's output relation gives refinement** under frame-safe contracts, for
inputs that avoid the frame temporaries. -/
theorem refines_of_rel {ce : CheckEnv} (hwf : WF ce f) (hc : CertOK f) (R : ARelD tabs f g T E) :
    RefinesFrom (fun env args mem => env.FrameSafe ∧ InitAvoids env args mem) tabs g tabs f := by
  have hpar : (Ctx.make tabs g).params = (Ctx.make tabs f).params := by
    simp only [Ctx.make, abiParams, R.ownAux]
  have hpty : (Ctx.make tabs g).paramTys = (Ctx.make tabs f).paramTys := by
    simp only [Ctx.make, abiParams, R.ownAux]
  have houts : (Ctx.make tabs g).outs = (Ctx.make tabs f).outs := by
    simp only [Ctx.make, abiParams, R.ownAux]
  have hloc : (Ctx.make tabs g).locals = (Ctx.make tabs f).locals := by
    simp only [Ctx.make, abiParams, R.ownAux]
  intro env args mem ⟨hfs, hinit⟩ fuel hd
  refine ⟨fuel, ?_⟩
  unfold run runCtx at hd ⊢
  rw [hpar]
  split
  · rename_i hn; simp only [hn] at hd; exact hd.elim
  · rename_i hn
    simp only [hn] at hd
    have hsz : (Ctx.make tabs g).f.valueTab.size = (Ctx.make tabs f).f.valueTab.size := R.vsize
    have hentry : entryFrame env (Ctx.make tabs g) args mem =
        entryFrame env (Ctx.make tabs f) args mem := by
      unfold entryFrame frameMem frameAllocs
      rw [hpty, hloc, hsz]; rfl
    rw [hentry, houts, show (Ctx.make tabs g).act = (Ctx.make tabs f).act from rfl,
      show (Ctx.make tabs g).defers = (Ctx.make tabs f).defers from rfl,
      show (Ctx.make tabs g).f.entry = (Ctx.make tabs f).f.entry from cfgView_entry R.cfg]
    exact finish_rel hfs (tempU0_UE E) (deferAvoid_UE R) hd (runLoop_simD
      (fun frS frT bid i => SimAt env tabs f T E frS frT bid i)
      (fun frS frT bid i h => step hfs hwf hc R h) fuel _ _ _ _ (entry_ok hinit)
      (finish_defined hd))

end GoFV.Proof.DAE
