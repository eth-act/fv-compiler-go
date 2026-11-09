import GoFV.Gen.Check39
import GoFV.Proof.Gen.G38
import GoFV.Proof.CongLoc

/-!
# Slice G39 of the genssa validator: the homes of removed values (`docs/plans/proofs3.md` §4)

`checkG39 lc` (`GoFV/Gen/Check39.lean`) checks `refsLive lc` (every value of the function is at an
ID that is a value of the function, and so are its arguments), then is `checkG38` on `liveCtx lc`:
`lc` with the homes of the IDs that are no value of the function dropped (the homes `regalloc`
recorded for values `trim` removed, of shape `Ty.other`).

`runLoc` reads homes only of the values it runs, their arguments, the blocks' controls and the
arguments of a `MakeResult` control (`LocState.read`, `LocState.write`, `LocState.clobber`,
`LocState.control`), all values of the function under `refsLive`. So it runs alike under `lc` and
`liveCtx lc` (`stepLoc_live`, `enterListLoc_live`, `stepTermLoc_live`, `runLoopLoc_live`,
`runCtxLoc_live`, `runLoc_live`), and `g39_value`, `g39_term`, `g39_nilPanic` and
`g39_boundsPanic` are `g38_value`'s, `g38_term`'s, `g38_nilPanic`'s and `g38_boundsPanic`'s
statements on `liveCtx lc`.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

attribute [local irreducible] schedule kahn schedValid

/-! ## The check -/

/-- What `checkG39` accepted: `refsLive`, and G38 on the context without the removed homes. -/
theorem checkG39_spec {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {r : PcTab × KTab} (h : checkG39 lc ps bstart g = .ok r) :
    refsLive lc = true ∧ checkG38 (liveCtx lc) ps bstart g = .ok r := by
  unfold checkG39 at h
  cases hr : refsLive lc with
  | false => simp [hr] at h; cases h
  | true => simp only [hr] at h; exact ⟨rfl, by simpa using h⟩

/-- Under `refsLive`, a value of the function is at an ID that is a value of the function, and so
are its arguments. -/
theorem refsLive_spec {lc : LocCtx} (h : refsLive lc = true) {id : ID} {v : Value}
    (hv : lc.ctx.f.value? id = some v) :
    (lc.ctx.f.value? v.id).isSome ∧ ∀ a ∈ v.args, (lc.ctx.f.value? a).isSome := by
  have hlt : id < lc.ctx.f.valueTab.size := by
    unfold Func.value? at hv
    refine Nat.lt_of_not_le fun hge => ?_
    rw [Array.getElem?_eq_none hge] at hv
    cases hv
  unfold refsLive at h
  have h1 := List.all_eq_true.1 h id (List.mem_range.2 hlt)
  rw [hv] at h1
  simp only [Bool.and_eq_true, Array.all_eq_true_iff_forall_mem] at h1
  exact h1

/-! ## `runLoc` runs alike without the removed homes -/

section Run

variable {lc : LocCtx}

@[simp] theorem liveCtx_ctx : (liveCtx lc).ctx = lc.ctx := rfl

@[simp] theorem liveCtx_temps : (liveCtx lc).temps = lc.temps := rfl

theorem liveCtx_ty (id : ID) : (liveCtx lc).ty id = lc.ty id := rfl

theorem home_live {id : ID} (h : (lc.ctx.f.value? id).isSome) :
    (liveCtx lc).home id = lc.home id := by
  simp [liveCtx, LocCtx.home, h]

theorem read_live (s : LocState) {id : ID} (h : (lc.ctx.f.value? id).isSome) :
    s.read (liveCtx lc) id = s.read lc id := by
  unfold LocState.read LocState.raw
  rw [home_live h]
  rfl

theorem write_live (s : LocState) {id : ID} (h : (lc.ctx.f.value? id).isSome) (x : Val) :
    s.write (liveCtx lc) id x = s.write lc id x := by
  unfold LocState.write
  rw [home_live h]
  rfl

theorem clobber_live (s : LocState) {v : Value}
    (hargs : ∀ a ∈ v.args, (lc.ctx.f.value? a).isSome) :
    s.clobber (liveCtx lc) v = s.clobber lc v := by
  have hb : ∀ i : Nat, v.args[i]?.bind (liveCtx lc).regOf = v.args[i]?.bind lc.regOf := by
    intro i
    cases ha : v.args[i]? with
    | none => rfl
    | some a =>
      simp only [Option.bind_some]
      unfold LocCtx.regOf
      rw [home_live (hargs a (Array.mem_of_getElem? ha))]
  unfold LocState.clobber
  simp only [hb]
  rfl

theorem signOf_live : ∀ n id, (liveCtx lc).signOf n id = lc.signOf n id
  | 0, _ => rfl
  | n + 1, id => by
    unfold LocCtx.signOf
    rw [liveCtx_ctx]
    cases lc.ctx.f.value? id with
    | none => rfl
    | some u =>
      simp only
      split
      · rfl
      · split
        · rw [signOf_live n]
        · rfl
      · rfl

theorem movdLoc_live (v : Value) (argv : List Val) (ty : Ty) :
    movdLoc (liveCtx lc) v argv ty = movdLoc lc v argv ty := by
  unfold movdLoc
  rw [funext fun n => funext fun id => signOf_live (lc := lc) n id]
  rfl

/-- A value whose ID and arguments are values of the function runs alike under `lc` and
`liveCtx lc`. -/
theorem stepLoc_live {env : Env} (s : LocState) {v : Value} (hid : (lc.ctx.f.value? v.id).isSome)
    (hargs : ∀ a ∈ v.args, (lc.ctx.f.value? a).isSome) :
    stepLoc env (liveCtx lc) s v = stepLoc env lc s v := by
  have hm : v.args.toList.mapM (s.read (liveCtx lc)) = v.args.toList.mapM (s.read lc) :=
    mapM_congr' _ fun a ha => read_live s (hargs a (Array.mem_toList_iff.1 ha))
  have hall : v.args.all (fun a => (liveCtx lc).home a == (liveCtx lc).home v.id) =
      v.args.all (fun a => lc.home a == lc.home v.id) := by
    rw [Bool.eq_iff_iff]
    simp only [Array.all_eq_true_iff_forall_mem]
    refine forall₂_congr fun a ha => ?_
    rw [home_live (hargs a ha), home_live hid]
  have hw : ∀ s x, LocState.write (liveCtx lc) s v.id x = LocState.write lc s v.id x :=
    fun s x => write_live s hid x
  unfold stepLoc
  simp only [hall, hm, clobber_live s hargs, hw, movdLoc_live]
  rfl

theorem enterListLoc_live {env : Env} (hr : refsLive lc = true) :
    ∀ (s : LocState) (ids : List ID),
      enterListLoc env (liveCtx lc) s ids = enterListLoc env lc s ids := by
  intro s ids
  induction ids generalizing s with
  | nil => rfl
  | cons id ids ih =>
    unfold enterListLoc
    rw [liveCtx_ctx]
    cases hv : lc.ctx.f.value? id with
    | none => rfl
    | some v =>
      obtain ⟨hid, hargs⟩ := refsLive_spec hr hv
      simp only [stepLoc_live s hid hargs]
      split <;> simp only [ih]

theorem control_live (hr : refsLive lc = true) (s : LocState) (c : ID) :
    s.control (liveCtx lc) c = s.control lc c := by
  unfold LocState.control
  rw [liveCtx_ctx]
  cases hv : lc.ctx.f.value? c with
  | none => rfl
  | some v =>
    obtain ⟨-, hargs⟩ := refsLive_spec hr hv
    have hm : v.args.toList.mapM (s.read (liveCtx lc)) = v.args.toList.mapM (s.read lc) :=
      mapM_congr' _ fun a ha => read_live s (hargs a (Array.mem_toList_iff.1 ha))
    simp only [hm, read_live s (show (lc.ctx.f.value? c).isSome by rw [hv]; rfl), liveCtx_ty]

theorem stepTermLoc_live (hr : refsLive lc = true) (s : LocState) (b : Block) :
    stepTermLoc (liveCtx lc) s b = stepTermLoc lc s b := by
  unfold stepTermLoc
  simp only [control_live hr]

/-- **`runLoc` runs alike without the homes of removed values**: under `refsLive`, `runLoopLoc`
under `liveCtx lc` is `runLoopLoc` under `lc`. -/
theorem runLoopLoc_live {env : Env} (hr : refsLive lc = true) :
    ∀ (fuel : Nat) (s : LocState) (bid : ID),
      runLoopLoc env (liveCtx lc) fuel s bid = runLoopLoc env lc fuel s bid := by
  intro fuel
  induction fuel with
  | zero => intros; rfl
  | succ n ih =>
    intro s bid
    rw [runLoopLoc_succ, runLoopLoc_succ, liveCtx_ctx]
    cases lc.ctx.f.block? bid with
    | none => rfl
    | some b =>
      simp only
      rw [enterBlockLoc_eq, enterBlockLoc_eq, enterListLoc_live hr]
      split
      · rfl
      · rfl
      · next s1 _ =>
        rw [stepTermLoc_live hr s1 b]
        split <;> simp only [ih]

theorem runCtxLoc_live {env : Env} (hr : refsLive lc = true) (args : List Val) (mem : Mem)
    (fuel : Nat) : runCtxLoc env (liveCtx lc) args mem fuel = runCtxLoc env lc args mem fuel := by
  unfold runCtxLoc
  simp only [liveCtx_ctx, runLoopLoc_live hr]

end Run

/-- **`runLoc` is `runCtxLoc` on the context without the homes of removed values** (under
`refsLive`, which `checkG39` checks). -/
theorem runLoc_live {tabs : Tables} {f : Func} (hr : refsLive (LocCtx.make tabs f) = true)
    (env : Env) (args : List Val) (mem : Mem) (fuel : Nat) :
    runLoc env tabs f args mem fuel = runCtxLoc env (liveCtx (LocCtx.make tabs f)) args mem fuel :=
  (runCtxLoc_live hr args mem fuel).symm

/-! ## The slice -/

/-- **G39, values.** `g38_value`'s statement on `liveCtx lc`, over `checkG39 lc`. -/
theorem g39_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG39 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s)
    (hu : UOKL m (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk i))
    (hpre : G38Pre (liveCtx lc) s v)
    (hcall : CallOK H E g L (liveCtx lc) s s' v m) (hcallz : CallOKZ H E g L (liveCtx lc) s s' v m)
    (hicall : ICallOK H E L ret (liveCtx lc) s s' v m)
    (hwb : WbOK H E g L (liveCtx lc) s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hmeq : MemEqOK H E g L (liveCtx lc) s v m) (hs : stepLoc env (liveCtx lc) s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env (liveCtx lc) g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' (liveCtx lc) (kAt (liveCtx lc) kt bid blk (i + 1)) s' ∧
      UOKL m' (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk (i + 1)) :=
  g38_value (checkG39_spec hc).2 hE hbid hb hi hv hen hm hinv hu hpre hcall hcallz hicall hwb hclo
    hgetg hmeq hs

/-- **G39, nil panics.** `g38_nilPanic`'s statement on `liveCtx lc`, over `checkG39 lc`. -/
theorem g39_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG39 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s)
    (hs : stepLoc env (liveCtx lc) s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e :=
  g38_nilPanic (checkG39_spec hc).2 hE hbid hb hi hv hop hm hinv hs

/-- **G39, bounds panics.** `g38_boundsPanic`'s statement on `liveCtx lc`, over `checkG39 lc`. -/
theorem g39_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG39 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s)
    (hbok : BoundsOK H g L ps.toList) (hs : stepLoc env (liveCtx lc) s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' :=
  g38_boundsPanic (checkG39_spec hc).2 hE hbid hb hi hv hop hm hinv hbok hs

/-- **G39, terminators.** `g38_term`'s statement on `liveCtx lc`, over `checkG39 lc`. -/
theorem g39_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG39 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk blk.values.size) s)
    (hpre : G1TermPre (liveCtx lc) s blk)
    (hu : UOKL m (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk blk.values.size))
    (ht : stepTermLoc (liveCtx lc) s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧
      G3Inv E (liveCtx lc) (kt.at e.b) s' ∧ e.b ∈ lc.ctx.f.blocks.toList ∧
      UOKL m' (uIn35 (liveCtx lc) e.b) :=
  g38_term (checkG39_spec hc).2 hE hbid hb hm hinv hpre hu ht

end GoFV.Proof.Gen
