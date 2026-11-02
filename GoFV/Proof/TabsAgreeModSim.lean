import GoFV.Proof.TabsAgreeModStep
import GoFV.Proof.Pass.DAEFinish
import GoFV.Proof.Avail
import GoFV.Proof.Pass.CSESim
import GoFV.Proof.Pass.DAEEnter

/-!
# Running in tables with extra frame temporaries: blocks and the loop

The source and the target run the same function in the same context (`Ctx.make tabs f`); the
target's frame has the same registers up to `VR X` and an initial memory `EqX` to the source's
(`FInv`, which also keeps the source's registers typed and avoiding `X`). Each layer keeps the
relation: a block's values (`evalAll_rel`), its `Phi`s (`phis_rel`), its terminator
(`stepTerm_rel`), the loop (`runLoop_simX`, `ORel`), and `finish` turns related outcomes into
refinement (`finish_rel`).
-/

namespace GoFV.Proof.TabsMod

open GoFV.SSA GoFV.SSA.Sem GoFV.Opt GoFV.Proof.DSE GoFV.Proof.CSE

variable {X : Blk → Bool}

local notation "U" => fun b => X b = true

/-- Related register files. -/
def RegsRel (X : Blk → Bool) (r r' : Array (Option Val)) : Prop :=
  ∀ (z : ID) (y : Val), r[z]? = some (some y) → ∃ y', r'[z]? = some (some y') ∧ VR X y y'

theorem RegsRel.set {r r' : Array (Option Val)} (h : RegsRel X r r') (hs : r'.size = r.size)
    (z : ID) {x x' : Val} (hx : VR X x x') : RegsRel X (r.set! z (some x)) (r'.set! z (some x')) := by
  intro z' y hy
  simp only [Array.set!_eq_setIfInBounds] at hy ⊢
  by_cases hz : z = z'
  · subst hz
    by_cases hlt : z < r.size
    · rw [Array.getElem?_setIfInBounds_self_of_lt hlt] at hy
      cases hy
      exact ⟨x', by rw [Array.getElem?_setIfInBounds_self_of_lt (by rw [hs]; exact hlt)], hx⟩
    · simp [hlt] at hy
  · rw [Array.getElem?_setIfInBounds_ne hz] at hy
    rw [Array.getElem?_setIfInBounds_ne hz]
    exact h z' y hy

/-- Collected `Phi`s, related. -/
inductive PRel (X : Blk → Bool) : List (ID × Val) → List (ID × Val) → Prop where
  | nil : PRel X [] []
  | cons {z : ID} {x x' : Val} {ps ps' : List (ID × Val)} : VR X x x' → PRel X ps ps' →
      PRel X ((z, x) :: ps) ((z, x') :: ps')

theorem setPhis_rel : {ps ps' : List (ID × Val)} → PRel X ps ps' → ∀ {r r' : Array (Option Val)},
    RegsRel X r r' → r'.size = r.size → RegsRel X (setPhis ps r) (setPhis ps' r')
  | _, _, .nil, _, _, h, _ => h
  | _, _, .cons (z := z) hx t, r, r', h, hs => by
    unfold setPhis
    rw [List.foldl_cons, List.foldl_cons]
    exact setPhis_rel t (h.set hs z hx) (by simp [hs])

/-- What the source's frame and the target's share at a block entry or inside a block. -/
structure FInv (X : Blk → Bool) (tabs : Tables) (f : Func) (S T : Frame) : Prop where
  size : S.regs.size = f.valueTab.size
  sizeT : T.regs.size = S.regs.size
  frame : T = { S with regs := T.regs, mem0 := T.mem0 }
  mem0 : EqX X S.mem0 T.mem0
  agree : RegsRel X S.regs T.regs
  av : DAE.RegsP (fun _ y => Val.Avoids (fun b => X b = true) y) S
  typed : Typed (Ctx.make tabs f) S
  fok : DAE.FrameOK (fun b => X b = true) S

/-- The fixed hypotheses of the simulation. -/
structure Hyps (env : Env) (X : Blk → Bool) (tabs : Tables) (f : Func) : Prop where
  E : env.TempOblivious
  temp : TempX X
  ok : ∀ x fv, f.value? x = some fv → tamOpOK tabs f fv = true
  loc : ∀ x fv n, f.value? x = some fv → fv.aux = some n → X (frameBlk tabs 0 n) = false

/-! ## A block's values -/

theorem FInv.set {tabs : Tables} {f : Func} {S T : Frame} (I : FInv X tabs f S T) (x : ID)
    {y y' : Val} (hy : VR X y y') (hav : Val.Avoids U y)
    (hty : y.retype ((Ctx.make tabs f).tys[x]?.getD .other) = y) :
    FInv X tabs f (S.set x y) (T.set x y') where
  size := by simp [Frame.set, I.size]
  sizeT := by simp [Frame.set, I.sizeT]
  frame := by
    unfold Frame.set
    conv => lhs; rw [I.frame]
  mem0 := I.mem0
  agree := I.agree.set I.sizeT x hy
  av := DAE.regsP_set I.av hav
  typed := DAE.regsP_set (P := fun x y => y.retype ((Ctx.make tabs f).tys[x]?.getD .other) = y)
    I.typed hty
  fok := ⟨I.fok.images, I.fok.closure, I.fok.mem0⟩

/-- **A list of values in source and target.** -/
theorem evalAll_rel {env : Env} {tabs : Tables} {f : Func} (H : Hyps env X tabs f) :
    ∀ (o : List ID) {S T : Frame}, (∀ x ∈ o, ∃ fv, f.value? x = some fv ∧ fv.id = x) →
      FInv X tabs f S T →
      (∀ S', evalAll env (Ctx.make tabs f) S o = .ok S' →
        ∃ T', evalAll env (Ctx.make tabs f) T o = .ok T' ∧ FInv X tabs f S' T') ∧
      (∀ e m, evalAll env (Ctx.make tabs f) S o = .panic e m →
        ∃ m', evalAll env (Ctx.make tabs f) T o = .panic e m' ∧ EqX X m m' ∧
          e.Avoids (X · = true) ∧ m.Avoids (X · = true))
  | [], S, T, _, I => ⟨fun S' h => (by cases h; exact ⟨T, rfl, I⟩), fun e m h => (by cases h)⟩
  | x :: o, S, T, hO, I => by
    obtain ⟨fv, hfv, hid⟩ := hO x List.mem_cons_self
    rw [evalAll_cons, evalAll_cons]
    unfold stepV
    simp only [show (Ctx.make tabs f).f = f from rfl, hfv]
    have hr := value_rel H.E H.temp I.frame I.mem0 I.av I.typed (H.ok x fv hfv)
      (fun a _ y hy => I.agree a y hy)
    cases hS : evalValue env (Ctx.make tabs f) S fv with
    | stuck msg => exact ⟨fun _ h => (by simp at h), fun _ _ h => (by simp at h)⟩
    | panic e m =>
      obtain ⟨m', hT, hm⟩ := hr.2 e m hS
      have hpa := evalValue_panic_avoidsX H.E H.temp I.av hS
      rw [hT]
      refine ⟨fun _ h => (by simp at h), fun e' m'' h => ?_⟩
      simp only [Res.panic.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨m', rfl, hm, hpa⟩
    | ok y =>
      obtain ⟨y', hT, hy⟩ := hr.1 y hS
      rw [hT]
      have hav := value_avoids H.E H.temp I.fok I.av hfv hid (H.ok x fv hfv)
        (fun n hn => H.loc x fv n hfv hn) hS
      have hty : y.retype ((Ctx.make tabs f).tys[x]?.getD .other) = y := by
        rw [← hid]; exact evalValue_typed hS
      exact evalAll_rel H o (fun z hz => hO z (List.mem_cons_of_mem _ hz)) (I.set x hy hav hty)

/-! ## `Phi`s -/

/-- One `Phi` step in source and target. -/
theorem phiStep_rel {ctx : Ctx} {S T : Frame} (hag : RegsRel X S.regs T.regs) (i : Nat) {z : ID}
    {o : Option (ID × Val)} (h : phiStep ctx S i z = .ok o) :
    ∃ o', phiStep ctx T i z = .ok o' ∧
      ((o = none ∧ o' = none) ∨ ∃ x x', o = some (z, x) ∧ o' = some (z, x') ∧ VR X x x') := by
  unfold phiStep at h ⊢
  cases hfv : ctx.f.value? z with
  | none => rw [hfv] at h; cases h
  | some fv =>
    rw [hfv] at h
    dsimp only at h ⊢
    by_cases hph : fv.op = .Phi
    · simp only [hph, beq_self_eq_true, ↓reduceIte] at h ⊢
      cases ha : fv.args[i]? with
      | none => rw [ha] at h; cases h
      | some a =>
        rw [ha] at h
        simp only at h ⊢
        cases hx : S.regs[a]? with
        | none => rw [hx] at h; cases h
        | some ox =>
          cases ox with
          | none => rw [hx] at h; cases h
          | some x =>
            rw [hx] at h
            simp only [Option.join] at h
            cases h
            obtain ⟨x', hx', hv⟩ := hag a x hx
            rw [hx']
            exact ⟨_, rfl, .inr ⟨_, _, rfl, rfl, hv.retype _⟩⟩
    · have h1 : (fv.op == .Phi) = false := by simpa using hph
      simp only [h1, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases h
      exact ⟨none, rfl, .inl ⟨rfl, rfl⟩⟩

/-- **The target collects related `Phi`s.** -/
theorem phis_rel {ctx : Ctx} {S T : Frame} (hag : RegsRel X S.regs T.regs) (i : Nat) :
    ∀ {l : List ID} {ps : List (ID × Val)},
      l.filterMapM (phiStep ctx S i) = .ok ps →
      ∃ ps', l.filterMapM (phiStep ctx T i) = .ok ps' ∧ PRel X ps ps'
  | [], ps, h => by
    simp only [List.filterMapM_nil] at h
    cases h; exact ⟨[], rfl, .nil⟩
  | z :: l, ps, h => by
    rw [List.filterMapM_cons] at h ⊢
    cases hz : phiStep ctx S i z with
    | panic e m => rw [hz] at h; cases h
    | stuck msg => rw [hz] at h; cases h
    | ok o =>
      rw [hz] at h
      obtain ⟨o', ho', hrel⟩ := phiStep_rel hag i hz
      rw [ho']
      cases hl : l.filterMapM (phiStep ctx S i) with
      | panic e m =>
        rcases hrel with ⟨rfl, rfl⟩ | ⟨x, x', rfl, rfl, hv⟩ <;>
          simp only [bind, Res.bind, hl] at h <;> cases h
      | stuck msg =>
        rcases hrel with ⟨rfl, rfl⟩ | ⟨x, x', rfl, rfl, hv⟩ <;>
          simp only [bind, Res.bind, hl] at h <;> cases h
      | ok rest =>
        obtain ⟨rest', hl', hr⟩ := phis_rel hag i hl
        rcases hrel with ⟨rfl, rfl⟩ | ⟨x, x', rfl, rfl, hv⟩
        · simp only [bind, Res.bind, hl] at h
          cases h
          exact ⟨rest', by simp only [bind, Res.bind, hl'], hr⟩
        · simp only [bind, Res.bind, hl, pure] at h
          cases h
          exact ⟨_, by simp only [bind, Res.bind, hl', pure], .cons hv hr⟩

/-- The source's `Phi`s keep its registers typed and avoiding `X`. -/
theorem phis_regs {tabs : Tables} {f : Func} {b : Block} (hnd : b.values.toList.Nodup) {S : Frame}
    {P : ID → Val → Prop} (hP : DAE.RegsP P S)
    (hcross : ∀ (z a : ID) (y : Val), DAE.RegsP P S → S.regs[a]? = some (some y) →
      P z (y.retype ((Ctx.make tabs f).tys[z]?.getD .other)))
    {i : Nat} {ps : List (ID × Val)}
    (hps : b.values.toList.filterMapM (phiStep (Ctx.make tabs f) S i) = .ok ps) :
    DAE.RegsP P { S with regs := setPhis ps S.regs } := by
  obtain ⟨hsz, hsome, hkeep, hphiS⟩ := phis_spec hnd hps
  intro z y hz
  change (setPhis ps S.regs)[z]? = some (some y) at hz
  by_cases hin : z ∈ b.values
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hsome z hin)
    by_cases hph : v.op = .Phi
    · have hlt : z < S.regs.size := by
        rw [← hsz]
        rcases Nat.lt_or_ge z (setPhis ps S.regs).size with h | h
        · exact h
        · rw [Array.getElem?_eq_none h] at hz; cases hz
      obtain ⟨a, x, -, hx, hset⟩ := hphiS z hin v hv hph hlt
      rw [hset] at hz
      cases hz
      exact hcross z a x hP hx
    · rw [hkeep z (.inr ⟨v, hv, hph⟩)] at hz
      exact hP z y hz
  · rw [hkeep z (.inl hin)] at hz
    exact hP z y hz

/-! ## A block's entry -/

/-- **Entering a block** in source and target. -/
theorem enterBlock_rel {env : Env} {tabs : Tables} {f : Func} (H : Hyps env X tabs f)
    {ce : CheckEnv} (hwf : WF ce f) {bid : ID} {b : Block} (hbin : bid ∈ f.blocks)
    (hb : f.block? bid = some b) (i : Nat) {S T : Frame} (I : FInv X tabs f S T) :
    (∀ S', enterBlock env (Ctx.make tabs f) S b i = .ok S' →
      ∃ T', enterBlock env (Ctx.make tabs f) T b i = .ok T' ∧ FInv X tabs f S' T') ∧
    (∀ e m, enterBlock env (Ctx.make tabs f) S b i = .panic e m →
      ∃ m', enterBlock env (Ctx.make tabs f) T b i = .panic e m' ∧ EqX X m m' ∧
        e.Avoids (X · = true) ∧ m.Avoids (X · = true)) := by
  have hnd := hwf.valuesNodup bid b ⟨hbin, hb⟩
  have hown := valuesOwn hwf hbin hb
  obtain ⟨b', hb', hid⟩ := hwf.blockId bid hbin
  rw [hb] at hb'; cases hb'
  have key : ∀ r, enterBlock env (Ctx.make tabs f) S b i = r → (∀ msg, r ≠ .stuck msg) →
      ∃ (ps : List (ID × Val)) (o : Array ID),
        evalAll env (Ctx.make tabs f) { S with regs := setPhis ps S.regs } o.toList = r ∧
        ∃ psT : List (ID × Val), enterBlock env (Ctx.make tabs f) T b i =
          evalAll env (Ctx.make tabs f) { T with regs := setPhis psT T.regs } o.toList ∧
        (∀ x ∈ o.toList, ∃ fv, f.value? x = some fv ∧ fv.id = x) ∧
        FInv X tabs f { S with regs := setPhis ps S.regs } { T with regs := setPhis psT T.regs } := by
    intro r hen hr
    obtain ⟨ps, o, hps, hsched, hev⟩ := CSE.enterBlock_split hen hr
    obtain ⟨psT, hpsT, hpr⟩ := phis_rel I.agree i hps
    have ho : schedule f b = some o := by
      rw [hid, sched_of_block hb] at hsched; exact hsched
    refine ⟨ps, o, hev, psT, CSE.enterBlock_of_parts hpsT hsched, fun x hx => ?_, ?_⟩
    · obtain ⟨hxb, -⟩ := ((schedule_topo hown hnd ho).2.2 x).1 hx
      obtain ⟨v, hv, hvid⟩ := hown x hxb
      exact ⟨v, hv, hvid⟩
    · refine ⟨by simp [setPhis_size, I.size], by simp [setPhis_size, I.sizeT], ?_, I.mem0,
        setPhis_rel hpr I.agree I.sizeT, ?_, ?_, ⟨I.fok.images, I.fok.closure, I.fok.mem0⟩⟩
      · conv => lhs; rw [I.frame]
      · exact phis_regs hnd I.av
          (fun _ a y hP hy => DAE.retype_avoids (tempU_of H.temp) _ (hP a y hy)) hps
      · exact phis_regs (P := fun z y => y.retype ((Ctx.make tabs f).tys[z]?.getD .other) = y)
          hnd I.typed (fun _ _ _ _ _ => retype_idem _ _) hps
  constructor
  · intro S' h
    obtain ⟨ps, o, hev, psT, hT, hO, I0⟩ := key _ h nofun
    obtain ⟨T', h1, h2⟩ := (evalAll_rel H o.toList hO I0).1 S' hev
    exact ⟨T', hT.trans h1, h2⟩
  · intro e m h
    obtain ⟨ps, o, hev, psT, hT, hO, I0⟩ := key _ h nofun
    obtain ⟨m', h1, h2⟩ := (evalAll_rel H o.toList hO I0).2 e m hev
    exact ⟨m', hT.trans h1, h2⟩

/-! ## Terminators -/

theorem control_rel {G GT : Frame} {b b' : Block} (hc : b'.controls = b.controls)
    (hreg : RegsRel X G.regs GT.regs) {k : Nat} {y : Val} (h : Sem.control G b k = .ok y) :
    ∃ y', Sem.control GT b' k = .ok y' ∧ VR X y y' := by
  unfold Sem.control at h ⊢
  rw [hc]
  cases hk : b.controls[k]? with
  | none => rw [hk] at h; cases h
  | some c =>
    rw [hk] at h
    simp only [Res.ofOption] at h ⊢
    cases hy : G.regs[c]? with
    | none => rw [hy] at h; cases h
    | some o =>
      cases o with
      | none => rw [hy] at h; cases h
      | some y0 =>
        rw [hy] at h
        simp only [Option.join] at h
        cases h
        obtain ⟨y', hy', hv⟩ := hreg c _ hy
        rw [hy']
        exact ⟨y', rfl, hv⟩

theorem VRL.any_eq (p : Val → Bool) (hp : ∀ a b, VR X a b → p b = p a) :
    {as bs : List Val} → VRL X as bs → bs.any p = as.any p
  | _, _, .nil => rfl
  | _, _, .cons h t => by simp only [List.any_cons, hp _ _ h, VRL.any_eq p hp t]

/-- **The terminators on related controls.** -/
theorem stepTerm_rel {G GT : Frame} {b b' : Block} (hk : b'.kind = b.kind) (hs : b'.succs = b.succs)
    (hid : b'.id = b.id) (hc : b'.controls = b.controls) (hreg : RegsRel X G.regs GT.regs) :
    (∀ e, stepTerm G b = .ok (.goto e) → stepTerm GT b' = .ok (.goto e)) ∧
    (∀ rs m, stepTerm G b = .ok (.ret rs m) →
      ∃ rs' m', stepTerm GT b' = .ok (.ret rs' m') ∧ VRL X rs rs' ∧ EqX X m m') := by
  have hsucc : ∀ k, Sem.succ b' k = Sem.succ b k := fun k => by unfold Sem.succ; rw [hs, hid]
  have hct : ∀ k y, Sem.control G b k = .ok y → ∃ y', Sem.control GT b' k = .ok y' ∧ VR X y y' :=
    fun k y h => control_rel hc hreg h
  -- the same step when the source's first control is neither a memory nor a tuple
  have same : ∀ n, stepTerm G b = .ok n → b.kind ≠ .Ret → stepTerm GT b' = .ok n := by
    intro n h hR
    unfold stepTerm at h ⊢
    rw [hk]
    simp only [hsucc, hid]
    cases hkb : b.kind <;> simp only [hkb] at h ⊢
    all_goals first
      | exact h
      | exact absurd hkb hR
      | (cases hc0 : Sem.control G b 0 with
          | ok y =>
            obtain ⟨y', hy', hv⟩ := hct 0 y hc0
            rw [hc0] at h
            rw [hy']
            cases y with
            | bool c => rw [hv.eq nofun nofun]; exact h
            | int w x => rw [hv.eq nofun nofun]; exact h
            | _ => simp [bind, Res.bind] at h
          | panic _ _ => exact absurd hc0 DAE.control_not_panic
          | stuck _ => rw [hc0] at h; cases h)
      | cases h
  refine ⟨fun e h => ?_, fun rs m h => ?_⟩
  · by_cases hR : b.kind = .Ret
    · unfold stepTerm at h
      rw [hR] at h
      cases hc0 : Sem.control G b 0 with
      | ok y =>
        rw [hc0] at h
        simp only [bind, Res.bind] at h
        split at h
        · split at h
          · split at h <;> cases h
          · cases h
        · cases h
      | panic _ _ => exact absurd hc0 DAE.control_not_panic
      | stuck _ => rw [hc0] at h; cases h
    · exact same _ h hR
  · by_cases hR : b.kind = .Ret
    · unfold stepTerm at h ⊢
      rw [hR] at h
      rw [hk, hR]
      cases hc0 : Sem.control G b 0 with
      | ok y =>
        obtain ⟨y', hy', hv⟩ := hct 0 y hc0
        rw [hc0] at h
        rw [hy']
        simp only [bind, Res.bind] at h ⊢
        cases y with
        | tuple vs =>
          obtain ⟨ws, rfl, hws⟩ := hv.tuple_inv
          simp only at h ⊢
          rcases hws.getLast? with ⟨h1, h2⟩ | ⟨a, a', h1, h2, ha⟩
          · rw [h1] at h; cases h
          · rw [h1] at h
            rw [h2]
            cases a with
            | mem M =>
              obtain ⟨M', rfl, hM⟩ := ha.mem_inv
              simp only at h ⊢
              rw [VRL.any_eq _ (fun a b h => by cases h <;> rfl) hws.dropLast]
              split at h
              · cases h
              · cases h
                rename_i hp
                simp only [hp, Bool.false_eq_true, ↓reduceIte]
                exact ⟨_, _, rfl, hws.dropLast, hM⟩
            | _ => simp at h
        | _ => simp at h
      | panic _ _ => exact absurd hc0 DAE.control_not_panic
      | stuck _ => rw [hc0] at h; cases h
    · exact ⟨rs, m, same _ h hR, VRL.refl rs, EqX.refl X m⟩


/-! ## The loop and `finish` -/

/-- Related outcomes of the loops. -/
inductive ORel (X : Blk → Bool) : Outcome → Outcome → Prop where
  | ret {rs rs' : List Val} {m m' : Mem} : VRL X rs rs' → EqX X m m' →
      ORel X (.returned rs m) (.returned rs' m')
  | panic (e : Panic) {m m' : Mem} : EqX X m m' → e.Avoids (X · = true) →
      m.Avoids (X · = true) → ORel X (.panicked e m) (.panicked e m')

/-- The target's block step matches a source block step along the same edge. -/
def StepRelX (X : Blk → Bool) (R : Frame → Frame → ID → Nat → Prop) : Step → Step → Prop
  | .goto frS e, sT => ∃ frT, sT = .goto frT e ∧ R frS frT e.b e.i
  | .ret rs m, sT => ∃ rs' m', sT = .ret rs' m' ∧ VRL X rs rs' ∧ EqX X m m'
  | .panic e m, sT => ∃ m', sT = .panic e m' ∧ EqX X m m' ∧ e.Avoids (X · = true) ∧
      m.Avoids (X · = true)
  | .stuck, _ => True

/-- **Lock-step simulation** with related outcomes. -/
theorem runLoop_simX {env : Env} {ctxS ctxT : Ctx} (R : Frame → Frame → ID → Nat → Prop)
    (hsim : ∀ frS frT bid i, R frS frT bid i →
      StepRelX X R (blockStep env ctxS frS bid i) (blockStep env ctxT frT bid i)) :
    ∀ fuel frS frT bid i, R frS frT bid i → (runLoop env ctxS fuel frS bid i).Defined →
      ORel X (runLoop env ctxS fuel frS bid i) (runLoop env ctxT fuel frT bid i) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ h; exact h.elim
  | succ n ih =>
    intro frS frT bid i hR hd
    have hs := hsim frS frT bid i hR
    obtain ⟨g1, r1, p1, s1⟩ := runLoop_blockStep env ctxS n frS bid i
    obtain ⟨g2, r2, p2, -⟩ := runLoop_blockStep env ctxT n frT bid i
    cases hS : blockStep env ctxS frS bid i with
    | goto frS' e =>
      rw [hS] at hs
      obtain ⟨frT', hT, hR'⟩ := hs
      rw [g1 _ _ hS] at hd ⊢
      rw [g2 _ _ hT]
      exact ih _ _ _ _ hR' hd
    | ret rs m =>
      rw [hS] at hs
      obtain ⟨rs', m', hT, hr, hm⟩ := hs
      rw [r1 _ _ hS, r2 _ _ hT]
      exact .ret hr hm
    | panic e m =>
      rw [hS] at hs
      obtain ⟨m', hT, hm, he, hmA⟩ := hs
      rw [p1 _ _ hS, p2 _ _ hT]
      exact .panic e hm he hmA
    | stuck => exact absurd hd (s1 hS)

/-! ## `finish` -/

theorem VRL.take : ∀ (n : Nat) {as bs : List Val}, VRL X as bs → VRL X (as.take n) (bs.take n)
  | 0, _, _, _ => by simp; exact .nil
  | _ + 1, _, _, .nil => .nil
  | n + 1, _, _, .cons h t => by simp only [List.take_succ_cons]; exact .cons h (VRL.take n t)

theorem VRL.drop : ∀ (n : Nat) {as bs : List Val}, VRL X as bs → VRL X (as.drop n) (bs.drop n)
  | 0, _, _, h => by simpa using h
  | _ + 1, _, _, .nil => .nil
  | n + 1, _, _, .cons _ t => by simp only [List.drop_succ_cons]; exact VRL.drop n t

theorem putBytes_fold_eq : ∀ {pieces pieces' : List Val}, VRL X pieces pieces' →
    ∀ (ls : List (Nat × Ty)) (buf : Array Byte),
      ((ls.zip pieces').foldl (fun buf ((o, lt), v) => putBytes buf o (encode lt v)) buf) =
        ((ls.zip pieces).foldl (fun buf ((o, lt), v) => putBytes buf o (encode lt v)) buf)
  | _, _, .nil, ls, _ => by simp
  | _, _, .cons _ _, [], _ => by simp
  | _, _, .cons h t, _ :: ls, buf => by
    simp only [List.zip_cons_cons, List.foldl_cons]
    rw [h.encode]
    exact putBytes_fold_eq t ls _

theorem local_X (hX : TempX X) (a n : Nat) : X (.local a n) = false := by
  cases h : X (.local a n)
  · rfl
  · obtain ⟨k, hk⟩ := hX _ h; cases hk

theorem goResults_post_eq (hX : TempX X) {m m' : Mem} (hm : EqX X m m') :
    ∀ (os : List (Option AuxRef × Ty × Nat)) {pieces pieces' : List Val},
      VRL X pieces pieces' →
      goResults.post 0 m' pieces' os = goResults.post 0 m pieces os
  | [], pieces, pieces', hp => by
    unfold goResults.post
    rw [show pieces'.isEmpty = pieces.isEmpty by cases hp <;> rfl]
  | (name, t, k) :: os, pieces, pieces', hp => by
    unfold goResults.post
    have hlen := hp.length
    simp only [hlen, goResults_post_eq hX hm os (hp.drop k),
      putBytes_fold_eq (hp.take k)]
    split
    · cases name with
      | none => rfl
      | some n =>
        have hr : ∀ (n' sz : Nat), m'.read ⟨.local 0 n', 0⟩ sz = m.read ⟨.local 0 n', 0⟩ sz :=
          fun n' sz => EqX.read hm ⟨.local 0 n', 0⟩ sz (local_X hX 0 n')
        rw [goResults_post_eq hX hm os hp]
        simp only [hr]
    · rfl

theorem encode_zip_eq : ∀ {rs rs' : List Val}, VRL X rs rs' →
    ∀ (os : List (Option AuxRef × Ty × Nat)),
      ((rs'.zip os).map fun (v, (_, t, _)) => encode t v) =
        ((rs.zip os).map fun (v, (_, t, _)) => encode t v)
  | _, _, .nil, _ => rfl
  | _, _, .cons _ _, [] => rfl
  | _, _, .cons h t, _ :: os => by
    simp only [List.zip_cons_cons, List.map_cons, h.encode, encode_zip_eq t os]

theorem hasTy_zip_eq' : ∀ {rs rs' : List Val}, VRL X rs rs' →
    ∀ (os : List (Option AuxRef × Ty × Nat)),
      ((rs'.zip os).all fun (v, (_, t, _)) => v.hasTy t) =
        ((rs.zip os).all fun (v, (_, t, _)) => v.hasTy t)
  | _, _, .nil, _ => rfl
  | _, _, .cons _ _, [] => rfl
  | _, _, .cons h t, _ :: os => by
    simp only [List.zip_cons_cons, List.all_cons, h.hasTy, hasTy_zip_eq' t os]

theorem goResults_eq (hX : TempX X) (outs : Array (Option AuxRef × Ty × Nat)) {rs rs' : List Val}
    {m m' : Mem} (hr : VRL X rs rs') (hm : EqX X m m') :
    goResults outs 0 rs' m' = goResults outs 0 rs m := by
  unfold goResults
  simp only [hr.length, hasTy_zip_eq' hr, encode_zip_eq hr, goResults_post_eq hX hm _ hr]

/-- **`finish` turns related loop outcomes into refinement**: at a panic, the deferred calls run
on memories equal once `X` is erased (`DeferRel.finish_panicked_refines`; the open-coded defer
variables are outside `X`, `hdi`). -/
theorem finish_rel {env : Env} (hE : env.TempOblivious) (hX : TempX X)
    {outs : Array (Option AuxRef × Ty × Nat)} {di : DeferInfo}
    (hdi : DeferRel.DeferAvoid (X · = true) di 0) {o o' : Outcome}
    (hd : (finish env outs di 0 o).Defined) (h : ORel X o o') :
    OutcomeRefines 0 (finish env outs di 0 o) (finish env outs di 0 o') := by
  cases h with
  | panic e hm he hmA =>
    exact DeferRel.finish_panicked_refines memRel_eqX (tempU_of hX)
      (respects_of_tempOblivious hE hX) outs hdi (fun _ _ h => (EqX.freeFrame hX h).symm)
      (fun _ _ h => (EqX.dropFrames hX h).symm) he hmA hm hd
  | @ret rs rs' m m' hr hm =>
    have hfin : finish env outs di 0 (.returned rs' m') = finish env outs di 0 (.returned rs m) := by
      simp only [finish, hr.anyPoison, goResults_eq hX outs hr hm, (EqX.freeFrame hX hm).symm]
    rw [hfin]
    exact OutcomeRefines.refl hd

end GoFV.Proof.TabsMod
