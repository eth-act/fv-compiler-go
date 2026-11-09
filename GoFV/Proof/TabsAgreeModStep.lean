import GoFV.Proof.TabsAgreeModSrc
import GoFV.Proof.Pass.DAEStep

variable [GoFV.SSA.Sem.Addrs]

/-!
# Running in tables with extra frame temporaries: one value

`memOp_rel`: an op of `GoFV.Opt.tamMemOps` on equal arguments but a related last one evaluates to
related results (`ResRel`: related returned values, the same panic with memories `EqX`).
`value_rel`: a value of the function (in `tamOpOK`) evaluated in a source frame and a target
frame with related registers and initial memories gives related results: arguments of shapes
without memories or tuples are equal (typed registers), so the value evaluates alike, and the
other values are `memOp_rel`'s. `value_avoids`: the source's result avoids the extra frame
temporaries.
-/

namespace GoFV.Proof.TabsMod

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof.DSE

variable {X : Blk → Bool}

local notation "U" => fun b => X b = true

/-- Related results of one value. -/
def ResRel (X : Blk → Bool) (r r' : Res Val) : Prop :=
  (∀ y, r = .ok y → ∃ y', r' = .ok y' ∧ VR X y y') ∧
    (∀ e m, r = .panic e m → ∃ m', r' = .panic e m' ∧ EqX X m m')

theorem resRel_refl (r : Res Val) : ResRel X r r :=
  ⟨fun y h => ⟨y, h, .refl y⟩, fun e m h => ⟨m, h, EqX.refl X m⟩⟩

theorem resRel_ok {y y' : Val} (h : VR X y y') : ResRel X (.ok y) (.ok y') :=
  ⟨fun _ h' => by cases h'; exact ⟨_, rfl, h⟩, fun _ _ h' => (nomatch h')⟩

theorem resRel_stuck (msg : String) (r' : Res Val) : ResRel X (.stuck msg) r' :=
  ⟨fun _ h => (nomatch h), fun _ _ h => (nomatch h)⟩

theorem resRel_of_call {r r' : Res Val} (h : CallRel X r r') : ResRel X r r' :=
  ⟨fun y hy => (h.1 y hy).2, fun e m hp => (h.2 e m hp).2.2⟩

theorem memRoot_resRel {ctx : Ctx} {v : Value} (hn : v.op ≠ .NilCheck) {argv argv' : List Val}
    (hok : ∀ y, memRoot ctx v argv = .ok y → ∃ y', memRoot ctx v argv' = .ok y' ∧ VR X y y') :
    ResRel X (memRoot ctx v argv) (memRoot ctx v argv') :=
  ⟨hok, fun _ _ h => absurd (memRoot_panic h) hn⟩

/-! ## The ops of `tamMemOps` -/

/-- **The pure ops of `tamMemOps`** on equal arguments but a related last one. -/
theorem evalPure_rel (hX : TempX X) {op : Op} (hop : op ∈ tamMemOps) (hn : op ∉ evalOpArms)
    (ty : Ty) (k : Int64) (aux : Option AuxRef) {L : List Val} {w w' : Val} (hw : VR X w w')
    (hL : ∀ a ∈ L, Val.Avoids U a) :
    VR X (evalPure op ty k aux (L ++ [w])) (evalPure op ty k aux (L ++ [w'])) := by
  simp only [tamMemOps, DAE.memOps, List.cons_append, List.nil_append, List.mem_cons,
    List.mem_nil_iff, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · -- Copy
    exact copy_rel ty k aux L hw
  · -- LocalAddr
    exact absurd (by decide) hn
  · -- Convert
    show VR X (PtrOps.convert ty (L ++ [w])) (PtrOps.convert ty (L ++ [w']))
    rw [DAE.convert_eq ty L w w']; exact .refl _
  · -- InlMark
    exact .refl _
  · -- GetG
    exact .refl _
  · -- GetCallerSP
    exact absurd (by decide) hn
  · -- Select0
    exact select_rel 0 L hw
  · -- Select1
    exact select_rel 1 L hw
  · -- SelectN
    exact selectN_rel k L hw
  · -- MakeResult
    exact .tuple (VRL.snoc L hw)
  · -- Load
    show VR X (loadOp ty (L ++ [w])) (loadOp ty (L ++ [w']))
    rw [loadOp_eq hX ty L hw hL]; exact .refl _
  · -- AtomicLoad32
    exact atomicLoad_rel hX ty L hw hL
  · -- AtomicLoad64
    exact atomicLoad_rel hX ty L hw hL
  · -- AtomicLoadPtr
    exact atomicLoad_rel hX ty L hw hL
  · -- MemEq
    show VR X (memEq (L ++ [w])) (memEq (L ++ [w']))
    rw [memEq_eq hX L hw hL]; exact .refl _
  · -- Store
    exact absurd (by decide) hn
  · -- Zero
    exact absurd (by decide) hn
  · -- Move
    exact absurd (by decide) hn
  · -- VarDef
    exact absurd (by decide) hn
  · -- VarLive
    exact absurd (by decide) hn
  · -- KeepAlive
    exact absurd (by decide) hn
  · -- NilCheck
    exact absurd (by decide) hn
  · -- PanicBounds
    exact absurd (by decide) hn
  · -- StaticCall
    exact absurd (by decide) hn
  · -- InterCall
    exact absurd (by decide) hn
  · -- ClosureCall
    exact absurd (by decide) hn
  · -- AtomicStore32
    exact .refl _
  · -- AtomicStore64
    exact .refl _
  · -- AtomicAdd32
    exact .refl _
  · -- AtomicAdd32Variant
    exact .refl _
  · -- AtomicAdd64
    exact .refl _
  · -- AtomicCompareAndSwap32
    exact .refl _
  · -- AtomicCompareAndSwap32Variant
    exact .refl _
  · -- AtomicCompareAndSwap64
    exact .refl _
  · -- AtomicCompareAndSwap64Variant
    exact .refl _
  · -- StaticLECall
    exact absurd (by decide) hn
  · -- InterLECall
    exact absurd (by decide) hn
  · -- ClosureLECall
    exact absurd (by decide) hn
  · -- Dereference
    show VR X (loadOp ty (L ++ [w])) (loadOp ty (L ++ [w']))
    rw [loadOp_eq hX ty L hw hL]; exact .refl _
  · -- AtomicLoad8
    exact atomicLoad_rel hX ty L hw hL
  · -- AtomicLoadAcq32
    exact atomicLoad_rel hX ty L hw hL
  · -- AtomicLoadAcq64
    exact atomicLoad_rel hX ty L hw hL
  · -- SelectNAddr
    show VR X (Tuple.selectNAddr k (L ++ [w])) (Tuple.selectNAddr k (L ++ [w']))
    rw [selectNAddr_eq k L hw]; exact .refl _
  · -- MakeTuple
    exact makeTuple_rel L hw

/-- **An op of `tamMemOps` or an `atomicRootOp`** on equal arguments but a related last one. -/
theorem memOp_rel {env : Env} (hE : env.TempOblivious) (hX : TempX X) {ctx : Ctx} {fr : Frame}
    {v : Value} {ty : Ty} (hop : v.op ∈ tamMemOps ∨ atomicRootOp v.op = true) {L : List Val}
    {w w' : Val} (hw : VR X w w')
    (hav : ∀ z ∈ L ++ [w], Val.Avoids U z) :
    ResRel X (evalOp env ctx fr v (L ++ [w]) ty) (evalOp env ctx fr v (L ++ [w']) ty) := by
  have hL : ∀ z ∈ L, Val.Avoids U z := fun z hz => hav z (by simp [hz])
  by_cases harm : v.op ∈ evalOpArms
  rotate_left
  · by_cases hr : isRoot v.op = true
    · rw [evalOp_notArm harm, evalOp_notArm harm, hr]
      refine ⟨fun y h => ?_, fun e m h => absurd h atomicRoot_ne_panic⟩
      obtain ⟨M, rfl⟩ := atomicRoot_ok_mem h
      obtain ⟨M', rfl, hm⟩ := VR.mem_inv hw
      have hR : AtomicSimRel (EqX X) (fun b => X b = false) :=
        ⟨fun t p h hp => EqX.load h t p hp, fun _ _ h hp hw => EqX.write h hp hw⟩
      obtain ⟨y', hy', m1, m1', hm1, hs⟩ := atomicRoot_sim hR
        (fun p hp => by have := hL _ hp; simp only [Val.Avoids] at this; simpa using this)
        (fun x => by simpa using DAE.ofAddr_notU (tempU_of hX) x) hm h
      refine ⟨y', hy', ?_⟩
      rcases hs with ⟨rfl, rfl⟩ | ⟨z, rfl, rfl⟩
      · exact .mem hm1
      · exact .tuple (.cons (.refl z) (.cons (.mem hm1) .nil))
    · have hr' : isRoot v.op = false := by simpa using hr
      rw [evalOp_pure_of harm hr', evalOp_pure_of harm hr']
      rcases hop with hop | hop
      · exact resRel_ok (evalPure_rel hX hop harm _ _ _ hw hL)
      · simp only [atomicRootOp, Bool.and_eq_true] at hop; rw [hop.1] at hr'; cases hr'
  have hop : v.op ∈ tamMemOps := hop.resolve_right fun h => by
    simp only [atomicRootOp, Bool.and_eq_true, Bool.not_eq_true'] at h
    rw [List.contains_iff_mem.2 harm] at h; cases h.2
  have excl : ∀ op, v.op = op → op ∉ tamMemOps →
      ResRel X (evalOp env ctx fr v (L ++ [w]) ty) (evalOp env ctx fr v (L ++ [w']) ty) :=
    fun op h1 hn => absurd (h1 ▸ hop) hn
  have calls : v.op = .StaticLECall ∨ v.op = .StaticCall ∨ v.op = .ClosureLECall ∨
      v.op = .ClosureCall ∨ v.op = .InterLECall ∨ v.op = .InterCall →
      ResRel X (evalOp env ctx fr v (L ++ [w]) ty) (evalOp env ctx fr v (L ++ [w']) ty) := by
    intro ho
    have he : ∀ argv, evalOp env ctx fr v argv ty = callOp env ctx v argv := fun _ => by
      rcases ho with h | h | h | h | h | h <;> simp only [evalOp, h]
    rw [he, he]
    exact resRel_of_call (callOp_rel hE hX hw hav)
  have roots : v.op = .Store ∨ v.op = .Zero ∨ v.op = .Move ∨ v.op = .VarDef ∨ v.op = .VarLive ∨
      v.op = .KeepAlive →
      ResRel X (evalOp env ctx fr v (L ++ [w]) ty) (evalOp env ctx fr v (L ++ [w']) ty) := by
    intro ho
    have hmr : v.op = .Store ∨ v.op = .Zero ∨ v.op = .Move ∨ v.op = .VarDef ∨ v.op = .VarLive ∨
        v.op = .KeepAlive ∨ v.op = .NilCheck := by
      rcases ho with h | h | h | h | h | h <;> simp [h]
    rw [DAE.evalOp_memRoot hmr, DAE.evalOp_memRoot hmr]
    refine memRoot_resRel (by rcases ho with h | h | h | h | h | h <;> rw [h] <;> nofun)
      fun y h => ?_
    rcases ho with h1 | h1 | h1 | h1 | h1 | h1
    · exact write_rel hX (.inl h1) hw hL h
    · exact write_rel hX (.inr (.inl h1)) hw hL h
    · exact write_rel hX (.inr (.inr h1)) hw hL h
    · exact varDef_rel h1 hw h
    · exact varLive_rel (.inl h1) hw h
    · exact varLive_rel (.inr h1) hw h
  simp only [evalOpArms, List.mem_cons, List.mem_nil_iff, or_false] at harm
  rcases harm with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 |
    h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  · exact excl _ h1 (by decide)
  · exact excl _ h1 (by decide)
  · exact excl _ h1 (by decide)
  · exact excl _ h1 (by decide)
  · -- PanicBounds
    rw [DAE.evalOp_panicBounds h1, DAE.evalOp_panicBounds h1]
    exact ⟨fun y h => absurd h panicBounds_not_ok, fun e m h => panicBounds_rel hw h⟩
  · exact calls (.inl h1)
  · exact calls (.inr (.inl h1))
  · exact calls (.inr (.inr (.inl h1)))
  · exact calls (.inr (.inr (.inr (.inl h1))))
  · exact calls (.inr (.inr (.inr (.inr (.inl h1)))))
  · exact calls (.inr (.inr (.inr (.inr (.inr h1)))))
  · exact excl _ h1 (by decide)
  · exact roots (.inl h1)
  · exact excl _ h1 (by decide)
  · exact roots (.inr (.inr (.inl h1)))
  · exact excl _ h1 (by decide)
  · exact roots (.inr (.inl h1))
  · exact excl _ h1 (by decide)
  · exact roots (.inr (.inr (.inr (.inl h1))))
  · exact roots (.inr (.inr (.inr (.inr (.inl h1)))))
  · exact roots (.inr (.inr (.inr (.inr (.inr h1)))))
  · exact excl _ h1 (by decide)
  · -- NilCheck
    rw [DAE.evalOp_memRoot (by simp [h1]), DAE.evalOp_memRoot (by simp [h1])]
    obtain ⟨h2, h3⟩ := nilCheck_rel (ctx := ctx) h1 (L := L) hw
    exact ⟨fun y h => ⟨y, h2 y h, .refl y⟩, h3⟩
  · exact excl _ h1 (by decide)
  · rw [DAE.evalOp_argfree (.inr (.inl h1)) (L ++ [w]) (L ++ [w'])]; exact resRel_refl _
  · rw [DAE.evalOp_argfree (.inl h1) (L ++ [w]) (L ++ [w'])]; exact resRel_refl _
  · exact excl _ h1 (by decide)
  · exact excl _ h1 (by decide)

/-! ## One value -/

theorem tamOpOK_spec {tabs : Tables} {f : Func} {fv : Value} (h : tamOpOK tabs f fv = true) :
    stuckRoot fv.op = true ∨
      ((fv.op = .Phi ∨ (∀ a ∈ fv.args, DAE.plainArg tabs f a = true) ∨
        ((fv.op ∈ tamMemOps ∨ atomicRootOp fv.op = true) ∧
          ∀ a ∈ fv.args.pop, DAE.plainArg tabs f a = true)) ∧
      ((fv.op ∈ tamPtrOps ∨ atomicRootOp fv.op = true) ∨ DAE.noPtrTy (tabs.ty fv.type) = true)) := by
  unfold tamOpOK at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true',
    List.contains_iff_mem] at h
  exact h.imp id fun ⟨a, b⟩ => ⟨or_assoc.mp a, b⟩

/-- `evalOp` reads the initial memory only for `InitMem`. -/
theorem evalOp_mem0 {env : Env} {ctx : Ctx} {fr : Frame} {v : Value} {argv : List Val} {ty : Ty}
    (hn : v.op ≠ .InitMem) (m : Mem) :
    evalOp env ctx { fr with mem0 := m } v argv ty = evalOp env ctx fr v argv ty := by
  by_cases harm : v.op ∈ evalOpArms
  · simp only [evalOpArms, List.mem_cons, List.mem_nil_iff, or_false] at harm
    rcases harm with h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 |
      h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
    · exact absurd h1 hn
    all_goals (simp only [evalOp, h1]; try rfl)
  · rw [evalOp_notArm harm, evalOp_notArm harm]

theorem argVals_rel {S T : Frame} :
    ∀ {as : List ID} {vs : List Val},
      (∀ a ∈ as, ∀ y, S.regs[a]? = some (some y) → ∃ y', T.regs[a]? = some (some y') ∧ VR X y y') →
      as.mapM (fun a => (S.regs[a]?).join) = some vs →
      ∃ vsT, as.mapM (fun a => (T.regs[a]?).join) = some vsT ∧ VRL X vs vsT
  | [], vs, _, h => by simp at h; subst h; exact ⟨[], rfl, .nil⟩
  | a :: as, vs, hr, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, hy, ys, hys, rfl⟩ := h
    cases h1 : S.regs[a]? with
    | none => rw [h1] at hy; cases hy
    | some o =>
      cases o with
      | none => rw [h1] at hy; cases hy
      | some vS =>
        rw [h1] at hy; simp at hy; subst hy
        obtain ⟨vT, h2, h3⟩ := hr a List.mem_cons_self _ h1
        obtain ⟨vsT, h4, h5⟩ := argVals_rel (fun b hb => hr b (List.mem_cons_of_mem _ hb)) hys
        exact ⟨vT :: vsT, by simp [List.mapM_cons, h2, h4], .cons h3 h5⟩

theorem argVals_rel' {S T : Frame} {as : Array ID} {vs : List Val}
    (hr : ∀ a ∈ as, ∀ y, S.regs[a]? = some (some y) → ∃ y', T.regs[a]? = some (some y') ∧ VR X y y')
    (h : CSE.argVals S as = some vs) : ∃ vsT, CSE.argVals T as = some vsT ∧ VRL X vs vsT :=
  argVals_rel (fun a ha => hr a (Array.mem_toList_iff.1 ha)) h

theorem VRL.eq_of : {as bs : List Val} → VRL X as bs →
    (∀ z ∈ as, (∀ m, z ≠ .mem m) ∧ (∀ vs, z ≠ .tuple vs)) → bs = as
  | _, _, .nil, _ => rfl
  | a :: _, _, .cons h1 t, hp => by
    have := hp a List.mem_cons_self
    rw [h1.eq this.1 this.2, VRL.eq_of t fun z hz => hp z (List.mem_cons_of_mem _ hz)]

theorem VRL.snoc_inv : {as : List Val} → {w : Val} → {bs : List Val} → VRL X (as ++ [w]) bs →
    ∃ bs' w', bs = bs' ++ [w'] ∧ VRL X as bs' ∧ VR X w w'
  | [], _, _, .cons h .nil => ⟨[], _, rfl, .nil, h⟩
  | _ :: _, _, _, .cons h t => by
    obtain ⟨bs', w', rfl, h1, h2⟩ := VRL.snoc_inv t
    exact ⟨_ :: bs', w', rfl, .cons h h1, h2⟩

theorem resRel_bind {r r' : Res Val} (t : Ty) (h : ResRel X r r') :
    ResRel X (r.bind fun r => .ok (r.retype t)) (r'.bind fun r => .ok (r.retype t)) := by
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

/-- **One value in source and target frames** with related registers and initial memories. -/
theorem value_rel {env : Env} (hE : env.TempOblivious) (hX : TempX X) {tabs : Tables} {f : Func}
    {S T : Frame} (hT : T = { S with regs := T.regs, mem0 := T.mem0 }) (hm0 : EqX X S.mem0 T.mem0)
    (hav : DAE.RegsP (fun _ y => Val.Avoids U y) S) (hty : Typed (Ctx.make tabs f) S)
    {fv : Value} (hok : tamOpOK tabs f fv = true)
    (hargs : ∀ a ∈ fv.args, ∀ y, S.regs[a]? = some (some y) →
      ∃ y', T.regs[a]? = some (some y') ∧ VR X y y') :
    ResRel X (evalValue env (Ctx.make tabs f) S fv) (evalValue env (Ctx.make tabs f) T fv) := by
  by_cases hst : ∃ msg, evalValue env (Ctx.make tabs f) S fv = .stuck msg
  · obtain ⟨msg, hm⟩ := hst; rw [hm]; exact resRel_stuck _ _
  obtain ⟨vs, hvs⟩ := CSE.argVals_of_eval (env := env) (ctx := Ctx.make tabs f) (fr := S)
    (v := fv) (fun msg h' => hst ⟨msg, h'⟩)
  obtain ⟨vsT, hvsT, hrel⟩ := argVals_rel' hargs hvs
  rw [CSE.evalValue_of_argVals hvs, CSE.evalValue_of_argVals hvsT]
  refine resRel_bind _ ?_
  generalize (Ctx.make tabs f).tys[fv.id]?.getD .other = ty
  have hTop : ∀ argv, fv.op ≠ .InitMem →
      evalOp env (Ctx.make tabs f) T fv argv ty = evalOp env (Ctx.make tabs f) S fv argv ty := by
    intro argv hn
    rw [hT]
    show evalOp env (Ctx.make tabs f) { { S with mem0 := T.mem0 } with regs := T.regs } fv argv ty = _
    rw [evalOp_frame, evalOp_mem0 hn]
  rcases tamOpOK_spec hok with hsr | ⟨hP | hall | ⟨hmem, hpop⟩, -⟩
  · obtain ⟨msg, hm⟩ := evalOp_stuckRoot (env := env) (ctx := Ctx.make tabs f) (fr := S)
      (argv := vs) (ty := ty) hsr
    rw [hm]; exact resRel_stuck _ _
  · have hn : fv.op ∉ evalOpArms := by rw [hP]; decide
    have hr : isRoot fv.op = false := by rw [hP]; rfl
    rw [evalOp_pure_of hn hr, evalOp_pure_of hn hr]
    refine resRel_ok ?_
    rw [hP]; exact .refl _
  · have : vsT = vs := hrel.eq_of fun z hz => by
      obtain ⟨a, ha, hza⟩ := DAE.argVals_mem hvs hz
      exact DAE.plain_val hty hza (hall a ha)
    subst this
    by_cases hin : fv.op = .InitMem
    · have he : ∀ fr : Frame, evalOp env (Ctx.make tabs f) fr fv vsT ty = .ok (.mem fr.mem0) :=
        fun fr => by simp only [evalOp, hin]; rfl
      rw [he, he]
      exact resRel_ok (.mem hm0)
    · rw [hTop _ hin]; exact resRel_refl _
  · have hn : fv.op ≠ .InitMem := by
      intro h; rw [h] at hmem; revert hmem; decide
    rw [hTop _ hn]
    cases hb : fv.args.back? with
    | none =>
      have h0 : fv.args = #[] := by
        rw [Array.back?_eq_none_iff] at hb; exact hb
      rw [h0] at hvs
      simp [CSE.argVals] at hvs; subst hvs
      cases hrel
      exact resRel_refl _
    | some m =>
    obtain ⟨L, w, rfl, -, hL⟩ := DAE.argVals_snoc hvs hb
    obtain ⟨L', w', rfl, hLL, hww⟩ := VRL.snoc_inv hrel
    have : L' = L := hLL.eq_of fun z hz => by
      obtain ⟨a, ha, hza⟩ := hL z hz
      exact DAE.plain_val hty hza (hpop a ha)
    subst this
    refine memOp_rel hE hX hmem hww fun z hz => ?_
    obtain ⟨a, -, hza⟩ := DAE.argVals_mem hvs hz
    exact hav a z hza

/-- **The source's result avoids `X`** (a value whose `LocalAddr` names no block of `X`, on
registers and frame inputs that avoid `X`). -/
theorem value_avoids {env : Env} (hE : env.TempOblivious) (hX : TempX X) {tabs : Tables}
    {f : Func} {S : Frame} (hfok : DAE.FrameOK U S) (hav : DAE.RegsP (fun _ y => Val.Avoids U y) S)
    {fv : Value} (hloc : ∀ n, fv.aux = some n → X (frameBlk tabs 0 n) = false) {y : Val}
    (h : evalValue env (Ctx.make tabs f) S fv = .ok y) : Val.Avoids U y := by
  obtain ⟨vs, r, hvs, hr, rfl⟩ := DAE.evalValue_ok_inv h
  have hargs : ∀ z ∈ vs, Val.Avoids U z := fun z hz => by
    obtain ⟨a, -, hza⟩ := DAE.argVals_mem hvs hz
    exact hav a z hza
  exact DAE.retype_avoids (tempU_of hX) _ (evalOp_avoids hE hX hfok hloc hargs hr)

/-! ## The source's panics avoid `X` -/

/-- An op on arguments avoiding `X` panics with a value and a memory avoiding `X`. -/
theorem evalOp_panic_avoidsX {env : Env} (hE : env.TempOblivious) (hX : TempX X) {ctx : Ctx}
    {fr : Frame} {v : Value} {argv : List Val} {ty : Ty}
    (hargs : ∀ z ∈ argv, Val.Avoids (X · = true) z) {e : Panic} {m : Mem}
    (h : evalOp env ctx fr v argv ty = .panic e m) :
    e.Avoids (X · = true) ∧ m.Avoids (X · = true) := by
  have pb : ∀ {k : Int64} {e : Panic} {m : Mem}, panicBounds k argv = .panic e m →
      e.Avoids (X · = true) ∧ m.Avoids (X · = true) := by
    intro k e m h
    unfold panicBounds at h
    split at h
    · cases h; exact ⟨trivial, hargs (.mem _) (by simp)⟩
    · cases h
  have call : ∀ {e : Panic} {m : Mem}, callOp env ctx v argv = .panic e m →
      e.Avoids (X · = true) ∧ m.Avoids (X · = true) := by
    intro e m h
    rcases List.eq_nil_or_concat argv with rfl | ⟨L, w, rfl⟩
    · obtain ⟨msg, hm⟩ := callOp_nil_stuck (env := env) (ctx := ctx) (v := v)
      rw [hm] at h; cases h
    · rw [List.concat_eq_append] at h hargs
      obtain ⟨h1, h2, -⟩ := (callOp_rel hE hX (.refl w) hargs).2 e m h
      exact ⟨h1, h2⟩
  unfold evalOp at h
  split at h
  all_goals first
    | cases h
    | exact absurd h argVal_not_panic
    | exact DAE.memRoot_panic_avoids hargs h
    | exact call h
    | exact pb h
    | (split at h <;> first
        | cases h
        | exact absurd h argVal_not_panic
        | (split at h
           · exact absurd h atomicRoot_ne_panic
           · cases h))

/-- **A value evaluated from registers avoiding `X` panics avoiding `X`.** -/
theorem evalValue_panic_avoidsX {env : Env} (hE : env.TempOblivious) (hX : TempX X) {ctx : Ctx}
    {S : Frame} (hav : DAE.RegsP (fun _ y => Val.Avoids (X · = true) y) S) {fv : Value}
    {e : Panic} {m : Mem} (h : evalValue env ctx S fv = .panic e m) :
    e.Avoids (X · = true) ∧ m.Avoids (X · = true) := by
  obtain ⟨vs, hvs, hr⟩ := DAE.evalValue_panic_inv h
  refine evalOp_panic_avoidsX hE hX (fun z hz => ?_) hr
  obtain ⟨a, -, ha⟩ := DAE.argVals_mem hvs hz
  exact hav a z ha

end GoFV.Proof.TabsMod
