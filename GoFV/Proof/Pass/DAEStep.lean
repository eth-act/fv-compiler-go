import GoFV.Proof.Pass.DAESrc

/-!
# dead auto elim: one value in source and target

`tgt_ok`: a value the source evaluates (in frame `S`, whose registers satisfy the invariant and
are typed) evaluates in the target (frame `T`, registers related by `VR`) to a related register:

* a kept value whose arguments are all of a shape without memories or tuples reads equal
  registers (related registers of such shapes are equal), so evaluates alike;
* a kept value of `memOps` reads equal registers but its last one, related: `memOp_rel`;
* an eliminated write is `Copy mem` in the target: the source writes only into `U`
  (`EqOff.write_left`, `EqOff.poison_left`).

`tgt_panic`: a panicking value (a call, `PanicBounds`, `NilCheck`) panics alike, with memories
equal outside `U`.
-/

namespace GoFV.Proof.DAE

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Opt.DAE

variable {U : Blk → Prop}

/-- Related results of one value: a returned value is related, a panic is the same panic with
memories equal outside `U`. -/
def ResRel (U : Blk → Prop) (r r' : Res Val) : Prop :=
  (∀ y, r = .ok y → ∃ y', r' = .ok y' ∧ VR U y y') ∧
    (∀ e m, r = .panic e m → ∃ m', r' = .panic e m' ∧ Mem.EqOff U m m')

theorem resRel_refl (r : Res Val) : ResRel U r r :=
  ⟨fun y h => ⟨y, h, .refl y⟩, fun e m h => ⟨m, h, EqOff.refl U m⟩⟩

theorem resRel_ok {y y' : Val} (h : VR U y y') : ResRel U (.ok y) (.ok y') :=
  ⟨fun _ h' => by cases h'; exact ⟨_, rfl, h⟩, fun _ _ h' => (nomatch h')⟩

theorem resRel_stuck (msg : String) (r' : Res Val) : ResRel U (.stuck msg) r' :=
  ⟨fun _ h => (nomatch h), fun _ _ h => (nomatch h)⟩

theorem resRel_of_call {r r' : Res Val} (h : CallRel U r r') : ResRel U r r' :=
  ⟨fun y hy => (h.1 y hy).2, h.2⟩

/-- A `memRoot` that is neither a `NilCheck` nor stuck returns. -/
theorem memRoot_resRel {ctx : Ctx} {v : Value} (hn : v.op ≠ .NilCheck) {argv argv' : List Val}
    (hok : ∀ y, memRoot ctx v argv = .ok y → ∃ y', memRoot ctx v argv' = .ok y' ∧ VR U y y') :
    ResRel U (memRoot ctx v argv) (memRoot ctx v argv') :=
  ⟨hok, fun _ _ h => absurd (memRoot_panic h) hn⟩

/-- **A kept atomic root** on related memories. -/
theorem atomicRoot_rel {v : Value} {L : List Val} {w w' : Val} (hw : VR U w w')
    (hav : ∀ a ∈ L, Val.Avoids U a) :
    ResRel U (atomicRoot v (L ++ [w])) (atomicRoot v (L ++ [w'])) := by
  refine ⟨fun y h => ?_, fun e m h => absurd h atomicRoot_ne_panic⟩
  obtain ⟨M, rfl⟩ := atomicRoot_ok_mem h
  obtain ⟨M', rfl, hm⟩ := VR.mem_inv hw
  have hR : AtomicSimRel (Mem.EqOff U) (fun b => ¬ U b) :=
    ⟨fun t p h hp => EqOff.load h t p hp, fun _ _ h _ hw => EqOff.write h hw⟩
  obtain ⟨y', hy', m1, m1', hm1, hs⟩ := atomicRoot_sim hR (fun p hp => hav _ hp) hm h
  refine ⟨y', hy', ?_⟩
  rcases hs with ⟨rfl, rfl⟩ | ⟨z, rfl, rfl⟩
  · exact .mem hm1
  · exact .tuple (.cons (.refl z) (.cons (.mem hm1) .nil))

/-! ## The ops of `memOps` -/

/-- **A kept op of `memOps`** on equal registers and a related last one. -/
theorem memOp_rel {env : Env} (hfs : env.FrameSafe) (hU : TempU U) {ctx : Ctx} {fr : Frame}
    {v : Value} {ty : Ty} (hop : v.op ∈ memOps) {L : List Val} {w w' : Val} (hw : VR U w w')
    (hav : v.op ≠ .Copy → ∀ z ∈ L ++ [w], Val.Avoids U z) :
    ResRel U (evalOp env ctx fr v (L ++ [w]) ty) (evalOp env ctx fr v (L ++ [w']) ty) := by
  simp only [memOps, List.mem_cons, List.mem_nil_iff, or_false] at hop
  have pure : ∀ op, v.op = op → (op = .Copy ∨ op = .Select0 ∨ op = .Select1 ∨
      op = .SelectN ∨ op = .MakeResult ∨ op = .Convert ∨ op = .Load ∨ op = .AtomicLoad32 ∨
      op = .AtomicLoad64 ∨ op = .AtomicLoadPtr ∨ op = .MemEq) →
      ResRel U (evalOp env ctx fr v (L ++ [w]) ty) (evalOp env ctx fr v (L ++ [w']) ty) := by
    intro op hv ho
    have he : ∀ argv, evalOp env ctx fr v argv ty = .ok (evalPure v.op ty v.auxInt v.aux argv) :=
      fun _ => evalOp_pureOp (by rcases ho with h | h | h | h | h | h | h | h | h | h | h <;>
        simp [hv, h])
    rw [he, he]
    refine resRel_ok ?_
    have hL : v.op ≠ .Copy → ∀ z ∈ L, Val.Avoids U z := fun hc z hz => hav hc z (by simp [hz])
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [hv]
    · exact copy_rel _ _ _ L hw
    · exact select_rel 0 L hw
    · exact select_rel 1 L hw
    · exact selectN_rel _ L hw
    · exact .tuple (VRL.snoc L hw)
    · show VR U (PtrOps.convert ty (L ++ [w])) (PtrOps.convert ty (L ++ [w']))
      rw [convert_eq ty L w w']; exact .refl _
    · show VR U (loadOp ty (L ++ [w])) (loadOp ty (L ++ [w']))
      rw [loadOp_eq ty L hw (hL (by rw [hv]; nofun))]; exact .refl _
    · exact atomicLoad_rel ty L hw (hL (by rw [hv]; nofun))
    · exact atomicLoad_rel ty L hw (hL (by rw [hv]; nofun))
    · exact atomicLoad_rel ty L hw (hL (by rw [hv]; nofun))
    · show VR U (memEq (L ++ [w])) (memEq (L ++ [w']))
      rw [memEq_eq L hw (hL (by rw [hv]; nofun))]; exact .refl _
  have argfree : v.op = .LocalAddr ∨ v.op = .GetCallerSP ∨ v.op = .InlMark ∨ v.op = .GetG →
      ResRel U (evalOp env ctx fr v (L ++ [w]) ty) (evalOp env ctx fr v (L ++ [w']) ty) := by
    intro ho
    rw [evalOp_argfree ho (L ++ [w]) (L ++ [w'])]
    exact resRel_refl _
  have roots : ∀ op, v.op = op → (op = .Store ∨ op = .Zero ∨ op = .Move ∨ op = .VarDef ∨
      op = .VarLive ∨ op = .KeepAlive) →
      ResRel U (evalOp env ctx fr v (L ++ [w]) ty) (evalOp env ctx fr v (L ++ [w']) ty) := by
    intro op hv ho
    have hne : v.op ≠ .Copy := by rw [hv]; rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> nofun
    have hL : ∀ z ∈ L, Val.Avoids U z := fun z hz => hav hne z (by simp [hz])
    rw [evalOp_memRoot (by rcases ho with h | h | h | h | h | h <;> simp [hv, h]),
      evalOp_memRoot (by rcases ho with h | h | h | h | h | h <;> simp [hv, h])]
    refine memRoot_resRel (by rw [hv]; rcases ho with rfl | rfl | rfl | rfl | rfl | rfl <;> nofun)
      fun y h => ?_
    rcases ho with rfl | rfl | rfl | rfl | rfl | rfl
    · exact write_rel (.inl hv) hw hL h
    · exact write_rel (.inr (.inl hv)) hw hL h
    · exact write_rel (.inr (.inr hv)) hw hL h
    · exact (varDef_rel hv hw h).1
    · exact (varLive_rel (.inl hv) hw h).1
    · exact (varLive_rel (.inr hv) hw h).1
  have calls : v.op = .StaticCall ∨ v.op = .InterCall ∨ v.op = .ClosureCall →
      ResRel U (evalOp env ctx fr v (L ++ [w]) ty) (evalOp env ctx fr v (L ++ [w']) ty) := by
    intro ho
    have hne : v.op ≠ .Copy := by rcases ho with h | h | h <;> rw [h] <;> nofun
    have he : ∀ argv, evalOp env ctx fr v argv ty = callOp env ctx v argv := fun _ => by
      rcases ho with h | h | h <;> simp only [evalOp, h]
    rw [he, he]
    exact resRel_of_call (callOp_rel hfs hU hw (hav hne))
  rcases hop with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 |
    h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  · exact pure _ h1 (by simp)
  · exact argfree (.inl h1)
  · exact pure _ h1 (by simp)
  · exact argfree (.inr (.inr (.inl h1)))
  · exact argfree (.inr (.inr (.inr h1)))
  · exact argfree (.inr (.inl h1))
  · exact pure _ h1 (by simp)
  · exact pure _ h1 (by simp)
  · exact pure _ h1 (by simp)
  · exact pure _ h1 (by simp)
  · exact pure _ h1 (by simp)
  · exact pure _ h1 (by simp)
  · exact pure _ h1 (by simp)
  · exact pure _ h1 (by simp)
  · exact pure _ h1 (by simp)
  · exact roots _ h1 (by simp)
  · exact roots _ h1 (by simp)
  · exact roots _ h1 (by simp)
  · exact roots _ h1 (by simp)
  · exact roots _ h1 (by simp)
  · exact roots _ h1 (by simp)
  · -- NilCheck
    rw [evalOp_memRoot (by simp [h1]), evalOp_memRoot (by simp [h1])]
    obtain ⟨h2, h3⟩ := nilCheck_rel (ctx := ctx) h1 (L := L) hw
    exact ⟨fun y h => ⟨y, (h2 y h).1, .refl y⟩, h3⟩
  · -- PanicBounds
    rw [evalOp_panicBounds h1, evalOp_panicBounds h1]
    exact ⟨fun y h => absurd h panicBounds_not_ok, fun e m h => panicBounds_rel hw h⟩
  · exact calls (.inl h1)
  · exact calls (.inr (.inl h1))
  · exact calls (.inr (.inr h1))
  all_goals
    have he : ∀ argv, evalOp env ctx fr v argv ty = atomicRoot v argv :=
      fun argv => evalOp_atomic (by simp [h1])
    rw [he, he]
    exact atomicRoot_rel hw fun a ha => hav (by rw [h1]; nofun) a (by simp [ha])

/-! ## Registers -/

theorem evalValue_panic_inv {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {e : Panic} {m : Mem}
    (h : evalValue env ctx fr v = .panic e m) :
    ∃ vs, CSE.argVals fr v.args = some vs ∧
      evalOp env ctx fr v vs (ctx.tys[v.id]?.getD .other) = .panic e m := by
  obtain ⟨vs, hvs⟩ := CSE.argVals_of_eval (env := env) (ctx := ctx) (fr := fr) (v := v)
    (fun msg h' => by rw [h] at h'; cases h')
  rw [CSE.evalValue_of_argVals hvs] at h
  refine ⟨vs, hvs, ?_⟩
  revert h
  cases evalOp env ctx fr v vs (ctx.tys[v.id]?.getD .other) <;> intro h <;> cases h; rfl

theorem argVals_rel {S T : Frame} :
    ∀ {as : List ID} {vs : List Val},
      (∀ a ∈ as, ∃ vS vT, S.regs[a]? = some (some vS) ∧ T.regs[a]? = some (some vT) ∧ VR U vS vT) →
      as.mapM (fun a => (S.regs[a]?).join) = some vs →
      ∃ vsT, as.mapM (fun a => (T.regs[a]?).join) = some vsT ∧ VRL U vs vsT
  | [], vs, _, h => by simp at h; subst h; exact ⟨[], rfl, .nil⟩
  | a :: as, vs, hr, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys, hys, rfl⟩ := h
    obtain ⟨vS, vT, h1, h2, h3⟩ := hr a List.mem_cons_self
    rw [h1] at hy; simp at hy; subst hy
    obtain ⟨vsT, h4, h5⟩ := argVals_rel (fun b hb => hr b (List.mem_cons_of_mem _ hb)) hys
    exact ⟨vT :: vsT, by simp [List.mapM_cons, h2, h4], .cons h3 h5⟩

theorem argVals_rel' {S T : Frame} {as : Array ID} {vs : List Val}
    (hr : ∀ a ∈ as, ∃ vS vT, S.regs[a]? = some (some vS) ∧ T.regs[a]? = some (some vT) ∧ VR U vS vT)
    (h : CSE.argVals S as = some vs) : ∃ vsT, CSE.argVals T as = some vsT ∧ VRL U vs vsT :=
  argVals_rel (fun a ha => hr a (Array.mem_toList_iff.1 ha)) h

/-- A typed register of a shape without memories or tuples is neither. -/
theorem plain_val {tabs : Tables} {f : Func} {fr : Frame} (hty : Proof.Typed (Ctx.make tabs f) fr)
    {a : ID} {z : Val} (hz : fr.regs[a]? = some (some z)) (hp : plainArg tabs f a = true) :
    (∀ m, z ≠ .mem m) ∧ (∀ vs, z ≠ .tuple vs) := by
  have h := hty a z hz
  have hsh : memTy ((Ctx.make tabs f).tys[a]?.getD .other) = false := by
    unfold plainArg at hp
    cases hv : f.value? a with
    | some av =>
      rw [hv] at hp
      rw [tys_of_value hv]
      simpa using hp
    | none =>
      unfold Func.value? at hv
      simp only [Ctx.make, Array.getElem?_map]
      cases ht : f.valueTab[a]? with
      | none => rfl
      | some o =>
        rw [ht] at hv
        simp only [Option.join_some] at hv
        subst hv
        rfl
  generalize (Ctx.make tabs f).tys[a]?.getD .other = t at h hsh
  constructor
  · rintro m rfl
    cases t <;> simp [memTy, Val.retype] at h hsh
  · rintro vs rfl
    cases t <;> simp [memTy, Val.retype] at h hsh

theorem VRL.eq_of : {as bs : List Val} → VRL U as bs →
    (∀ z ∈ as, (∀ m, z ≠ .mem m) ∧ (∀ vs, z ≠ .tuple vs)) → bs = as
  | _, _, .nil, _ => rfl
  | a :: _, _, .cons h1 t, hp => by
    have := hp a List.mem_cons_self
    rw [h1.eq this.1 this.2, VRL.eq_of t fun z hz => hp z (List.mem_cons_of_mem _ hz)]

theorem VRL.snoc_inv : {as : List Val} → {w : Val} → {bs : List Val} → VRL U (as ++ [w]) bs →
    ∃ bs' w', bs = bs' ++ [w'] ∧ VRL U as bs' ∧ VR U w w'
  | [], _, _, .cons h .nil => ⟨[], _, rfl, .nil, h⟩
  | _ :: _, _, _, .cons h t => by
    obtain ⟨bs', w', rfl, h1, h2⟩ := VRL.snoc_inv t
    exact ⟨_ :: bs', w', rfl, .cons h h1, h2⟩

/-! ## One value -/

theorem ctxG_facts {tabs : Tables} {f g : Func} (hown : g.ownAux = f.ownAux) :
    (Ctx.make tabs g).tabs = (Ctx.make tabs f).tabs ∧
      (Ctx.make tabs g).params = (Ctx.make tabs f).params ∧
      (Ctx.make tabs g).act = (Ctx.make tabs f).act := by
  refine ⟨rfl, ?_, rfl⟩
  simp only [Ctx.make, abiParams, hown]

variable {T : ID → Option AuxRef} {E : List AuxRef}

/-- **One value in source and target.** -/
theorem tgt_rel {env : Env} (hfs : env.FrameSafe) {tabs : Tables} {f g : Func}
    (R : ARelD tabs f g T E) {S Tf : Frame} (hT : Tf = { S with regs := Tf.regs })
    (hinv : RegsP (SInv T E) S) (htyS : Proof.Typed (Ctx.make tabs f) S)
    {x : ID} {fv gv : Value} (hfv : f.value? x = some fv) (hgv : g.value? x = some gv)
    (hid : fv.id = x) (hph : fv.op ≠ .Phi)
    (hargs : ∀ a ∈ gv.args, ∃ vS vT, S.regs[a]? = some (some vS) ∧ Tf.regs[a]? = some (some vT) ∧
      VR (UE E) vS vT) :
    ResRel (UE E) (evalValue env (Ctx.make tabs f) S fv) (evalValue env (Ctx.make tabs g) Tf gv) := by
  have hU := tempU_UE E
  obtain ⟨htabs, hpar, hact⟩ := ctxG_facts (tabs := tabs) R.ownAux
  have htyF : (Ctx.make tabs f).tys[fv.id]?.getD .other = tabs.ty fv.type := by
    rw [hid, tys_of_value hfv]; rfl
  obtain ⟨gv', hgv', hk⟩ := R.value x fv hfv
  rw [hgv] at hgv'; cases hgv'
  rcases hk with ⟨hs, hok⟩ | ⟨he, n, hname, hnE⟩
  · -- a kept value
    obtain ⟨hgid, hgop, hgax, hgai, hgty, -, hgargs⟩ := DSE.sameV_spec hs
    rw [hgargs] at hargs
    have hevT : ∀ vsT, CSE.argVals Tf gv.args = some vsT →
        evalValue env (Ctx.make tabs g) Tf gv =
          (evalOp env (Ctx.make tabs f) S fv vsT (tabs.ty fv.type)).bind
            fun r => .ok (r.retype (tabs.ty fv.type)) := by
      intro vsT h'
      have htyG : (Ctx.make tabs g).tys[gv.id]?.getD .other = tabs.ty fv.type := by
        rw [hgid, hid, tys_of_value hgv, hgty]; rfl
      rw [CSE.evalValue_of_argVals h', htyG, hT, evalOp_frame,
        evalOp_congr hgop hgax hgai hgid htabs hpar hact]
    have hevS : ∀ vs, CSE.argVals S fv.args = some vs →
        evalValue env (Ctx.make tabs f) S fv =
          (evalOp env (Ctx.make tabs f) S fv vs (tabs.ty fv.type)).bind
            fun r => .ok (r.retype (tabs.ty fv.type)) := by
      intro vs h'
      rw [CSE.evalValue_of_argVals h', htyF]
    -- the source's arguments
    by_cases hst : ∃ msg, evalValue env (Ctx.make tabs f) S fv = .stuck msg
    · obtain ⟨msg, hm⟩ := hst; rw [hm]; exact resRel_stuck _ _
    obtain ⟨vs, hvs⟩ := CSE.argVals_of_eval (env := env) (ctx := Ctx.make tabs f) (fr := S)
      (v := fv) (fun msg h' => hst ⟨msg, h'⟩)
    obtain ⟨vsT, hvsT, hrel⟩ := argVals_rel' hargs hvs
    rw [hgargs] at hevT
    rw [hevS vs hvs, hevT vsT hvsT]
    have lift : ∀ {r r' : Res Val}, ResRel (UE E) r r' →
        ResRel (UE E) (r.bind fun r => .ok (r.retype (tabs.ty fv.type)))
          (r'.bind fun r => .ok (r.retype (tabs.ty fv.type))) := by
      intro r r' h
      refine ⟨fun y hy => ?_, fun e m hp => ?_⟩
      · cases r with
        | ok r =>
          obtain ⟨y', h1, h2⟩ := h.1 r rfl
          cases hy; rw [h1]; exact ⟨_, rfl, h2.retype _⟩
        | panic _ _ => cases hy
        | stuck _ => cases hy
      · cases r with
        | ok r => cases hp
        | panic e' m' =>
          cases hp
          obtain ⟨m'', h1, h2⟩ := h.2 _ _ rfl
          rw [h1]; exact ⟨m'', rfl, h2⟩
        | stuck _ => cases hp
    have hplain : ∀ a ∈ fv.args, plainArg tabs f a = true → ∀ z,
        S.regs[a]? = some (some z) → (∀ m, z ≠ .mem m) ∧ (∀ vs, z ≠ .tuple vs) :=
      fun a _ hp z hz => plain_val htyS hz hp
    rcases (opOK_spec hok).1 with hP | hall | ⟨hmem, hpop⟩
    · exact absurd hP hph
    · -- every argument plain: equal registers
      have : vsT = vs := hrel.eq_of fun z hz => by
        obtain ⟨a, ha, hza⟩ := argVals_mem hvs hz
        exact hplain a ha (hall a ha) z hza
      subst this
      exact lift (resRel_refl _)
    · -- `memOps`: the last argument related
      cases hb : fv.args.back? with
      | none =>
        have h0 : fv.args = #[] := by
          rw [Array.back?_eq_none_iff] at hb; exact hb
        rw [h0] at hvs
        simp [CSE.argVals] at hvs; subst hvs
        cases hrel
        exact lift (resRel_refl _)
      | some m =>
      obtain ⟨L, w, rfl, -, hL⟩ := argVals_snoc hvs hb
      obtain ⟨L', w', rfl, hLL, hww⟩ := VRL.snoc_inv hrel
      have : L' = L := hLL.eq_of fun z hz => by
        obtain ⟨a, ha, hza⟩ := hL z hz
        exact hplain a (DSE.mem_of_mem_pop ha) (hpop a ha) z hza
      subst this
      refine lift (memOp_rel hfs hU hmem hww fun hc z hz => ?_)
      obtain ⟨a, ha, hza⟩ := argVals_mem hvs hz
      refine (hinv a z hza).untainted fun hta => ?_
      obtain ⟨i, hi⟩ := Array.getElem?_of_mem ha
      rcases uses_spec hfv (R.uses x (DSE.lt_of_value? hfv)) hi hta with
        ⟨-, hp, -⟩ | ⟨gv', hgv', he, -⟩
      · unfold propOp at hp
        simp only [Bool.or_eq_true, beq_iff_eq] at hp
        rcases hp with ((hp | hp) | hp) | hp <;> rw [hp] at hmem hc
        · simp [memOps] at hmem
        · simp [memOps] at hmem
        · simp [memOps] at hmem
        · exact hc rfl
      · rw [hgv] at hgv'; cases hgv'
        exact elimV_ne_same he hs
  · -- an eliminated write
    obtain ⟨hop, hgc, -, -, hgid, hgty, -, m, hback, hgargs⟩ := elimV_spec he
    obtain ⟨vSm, vTm, hSm, hTm, hVm⟩ := hargs m (by rw [hgargs]; simp)
    have htyG : (Ctx.make tabs g).tys[gv.id]?.getD .other = tabs.ty fv.type := by
      rw [hgid, hid, tys_of_value hgv, hgty]; rfl
    have hevT := evalValue_copy (env := env) (ctx := Ctx.make tabs g) hgc hgargs hTm
    rw [htyG] at hevT
    rw [hevT]
    have hnp : ¬ Panicking fv.op := by
      rintro (h | h) <;> rcases hop with h' | h' | h' | h' <;> rw [h'] at h <;> cases h
    refine ⟨fun y hy => ?_, fun e mm hp => absurd (evalValue_panic_op hp) hnp⟩
    obtain ⟨vs, r, hvs, hr, rfl⟩ := evalValue_ok_inv hy
    rw [htyF] at hr ⊢
    refine ⟨_, rfl, VR.retype ?_ _⟩
    rcases hop with hop | hop | hop | hop
    rotate_right
    · rw [evalOp_memRoot (by simp [hop])] at hr
      obtain ⟨M, n0, rfl, hax, rfl, -⟩ := DSE.varDef_shape hop hr
      have hn0 : n0 = n := by
        unfold nameOf at hname; simp [hop, hax] at hname; exact hname
      subst hn0
      have hSM := DSE.argVals_back (L := []) (by simpa using hvs) hback
      rw [hSm] at hSM; cases hSM
      obtain ⟨M', rfl, hm⟩ := VR.mem_inv hVm
      have hfb : frameBlk (Ctx.make tabs f).tabs (Ctx.make tabs f).act n0 = .temp 0 n0 :=
        frameBlk_temp (R.temp n0 hnE) 0
      rw [hfb]
      exact .mem (EqOff.poison_left hm ⟨n0, hnE, rfl⟩)
    all_goals
      have hop3 : fv.op = .Store ∨ fv.op = .Zero ∨ fv.op = .Move := by simp [hop]
      rw [evalOp_memRoot (by simp [hop])] at hr
      obtain ⟨p, L, M, bs, M1, hvsE, hw, rfl, -, -⟩ := write_spec hop3 hr
      rw [hvsE] at hvs
      have hSM := DSE.argVals_back (L := .ptr p :: L) hvs hback
      rw [hSm] at hSM; cases hSM
      obtain ⟨M', rfl, hm⟩ := VR.mem_inv hVm
      refine .mem (EqOff.write_left hm hw ?_)
      have hname0 : nameOf T fv = (fv.args[0]?).bind T := by
        unfold nameOf; simp [hop]
      rw [hname0] at hname
      cases ha : fv.args[0]? with
      | none => rw [ha] at hname; cases hname
      | some a =>
        rw [ha] at hname
        simp only [Option.bind_some] at hname
        obtain ⟨z, hz, hza⟩ := DSE.argVals_get hvs ha
        simp only [List.cons_append, List.getElem?_cons_zero, Option.some.injEq] at hz
        subst hz
        rcases (hinv a _ hza).tainted hname hnE with h' | ⟨off, h'⟩
        · cases h'
        · cases h'; exact ⟨n, hnE, rfl⟩

end GoFV.Proof.DAE
