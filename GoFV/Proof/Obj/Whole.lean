import GoFV.Proof.Obj.G12
import GoFV.Proof.Obj.Frame
import GoFV.Proof.CongLoc

/-!
# Whole functions: `runLoc` → `runMach` across blocks (`docs/plans/proofs3.md` §1, §7)

`g12_obj_value`/`g12_obj_term` chained along a whole `runLoc` run, with the prologue (`obj_entry`)
before it and the epilogue (`obj_exit`) after it.
-/

namespace GoFV.Proof.Obj

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.CheckObj
open GoFV.Proof.Gen
open GoFV.Proof (enterListLoc enterBlockLoc_eq)

/-! ## `runLoc` from inside a block -/

theorem enterListLoc_append (env : Env) (lc : LocCtx) :
    ∀ (s : LocState) (l1 l2 : List ID), enterListLoc env lc s (l1 ++ l2) =
      match enterListLoc env lc s l1 with
      | .ok s' => enterListLoc env lc s' l2
      | .panic e m => .panic e m
      | .stuck msg => .stuck msg
  | s, [], l2 => by simp only [List.nil_append, enterListLoc]
  | s, id :: l1, l2 => by
    simp only [List.cons_append, enterListLoc]
    cases lc.ctx.f.value? id with
    | none => rfl
    | some v =>
      simp only
      cases stepLoc env lc s v with
      | ok s' => exact enterListLoc_append env lc s' l1 l2
      | panic e m => rfl
      | stuck msg => rfl

/-- The run from value `i` of block `bid`: the rest of the block, its terminator, then
`runLoopLoc` with `fuel` block entries. -/
def runFromLoc (env : Env) (lc : LocCtx) (fuel : Nat) (s : LocState) (bid : ID) (i : Nat) :
    Outcome :=
  match lc.ctx.f.block? bid with
  | none => .stuck s!"b{bid} is not in the function"
  | some b =>
    match enterListLoc env lc s (b.values.toList.drop i) with
    | .panic e m => .panicked e m
    | .stuck msg => .stuck msg
    | .ok s =>
      match stepTermLoc lc s b with
      | .ok (.goto e, s) => runLoopLoc env lc fuel s e.b
      | .ok (.ret rs m, _) => .returned rs m
      | .panic e m => .panicked e m
      | .stuck msg => .stuck msg

theorem runLoopLoc_succ (env : Env) (lc : LocCtx) (fuel : Nat) (s : LocState) (bid : ID) :
    runLoopLoc env lc (fuel + 1) s bid = runFromLoc env lc fuel s bid 0 := by
  simp only [runLoopLoc, runFromLoc, enterBlockLoc_eq, List.drop_zero]
  rfl

/-- The entry block's first `k` values run to `sk`: the run continues from value `k`. -/
theorem runLoopLoc_entry {env : Env} {lc : LocCtx} {fuel : Nat} {s sk : LocState} {bid : ID}
    {b : Block} {k : Nat} (hb : lc.ctx.f.block? bid = some b)
    (hk : enterListLoc env lc s (b.values.toList.take k) = .ok sk) :
    runLoopLoc env lc (fuel + 1) s bid = runFromLoc env lc fuel sk bid k := by
  rw [runLoopLoc_succ]
  simp only [runFromLoc, hb, List.drop_zero]
  have h := enterListLoc_append env lc s (b.values.toList.take k) (b.values.toList.drop k)
  rw [List.take_append_drop, hk] at h
  simp only at h
  rw [h]

/-- `runLoc`'s first state (`runCtxLoc`): the frame of `entryFrame`, every register `poison`,
no flags, no slot, the frame's memory. -/
def locInit (env : Env) (lc : LocCtx) (args : List Val) (mem : Mem) : LocState :=
  let fr := entryFrame env lc.ctx args mem
  { fr, regs := Array.replicate ARM64.registers.size .poison, flags := .poison, slots := [],
    mem := .mem fr.mem0 }

/-- `runLoc` is `finish` of `runLoopLoc` from `locInit` at the entry. -/
theorem runLoc_eq {env : Env} {tabs : Tables} {f : Func} {args : List Val} {mem : Mem}
    {fuel : Nat} (h : args.length = (LocCtx.make tabs f).ctx.params.size) :
    runLoc env tabs f args mem fuel =
      finish env (LocCtx.make tabs f).ctx.outs (LocCtx.make tabs f).ctx.defers
        (LocCtx.make tabs f).ctx.act
        (runLoopLoc env (LocCtx.make tabs f) fuel (locInit env (LocCtx.make tabs f) args mem)
          (LocCtx.make tabs f).ctx.f.entry) := by
  simp only [runLoc, runCtxLoc, h, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rfl

/-! ## Reachable states -/

/-- The states `runLoc` reaches from value `i0` of block `b0` in state `s0`: before value `i` of
block `b` (`i` = the number of values: before the terminator). -/
inductive LReach (env : Env) (lc : LocCtx) (b0 : ID) (i0 : Nat) (s0 : LocState) :
    ID → Nat → LocState → Prop where
  | refl : LReach env lc b0 i0 s0 b0 i0 s0
  | val {b i s s' blk id v} : LReach env lc b0 i0 s0 b i s → lc.ctx.f.block? b = some blk →
      blk.values[i]? = some id → lc.ctx.f.value? id = some v → stepLoc env lc s v = .ok s' →
      LReach env lc b0 i0 s0 b (i + 1) s'
  | term {b s s' blk e} : LReach env lc b0 i0 s0 b blk.values.size s →
      lc.ctx.f.block? b = some blk → stepTermLoc lc s blk = .ok (.goto e, s') →
      LReach env lc b0 i0 s0 e.b 0 s'

/-- **The per-step premises of the run** at every state it reaches from `(b0, i0, s0)`: those of
`g12_value` (`G7Pre`; the trusted contracts `CallOK`, `ICallOK`, `WbOK`, `CloOK` at every
`LocMatch`ed machine state of an activation extending `E0`) and `g12_term` (`G1TermPre`); no value
after the start is an entry value. -/
def RunPre (env : Env) (H : Hooks) (lc : LocCtx) (g : G2In) (L : Link) (ret : BitVec 64)
    (E0 : MatchEnv) (b0 : ID) (i0 : Nat) (s0 : LocState) : Prop :=
  ∀ b i s blk, LReach env lc b0 i0 s0 b i s → lc.ctx.f.block? b = some blk →
    (∀ id v, blk.values[i]? = some id → lc.ctx.f.value? id = some v →
      entryOp3 v.op = false ∧ G7Pre lc s v ∧
      ∀ s', stepLoc env lc s v = .ok s' → ∀ E m, E0.Extends E → LocMatch E s b i m →
        CallOK H E g L lc s s' v m ∧ ICallOK H E L ret lc s s' v m ∧ WbOK H E g L lc s v m ∧
          CloOK E s v m) ∧
    (i = blk.values.size → G1TermPre lc s blk)

/-! ## Functions of simple ops -/

/-- An op none of whose per-step premises says anything: no compare, load, pair load,
subtraction, nil check, call, write barrier or closure pointer, and no entry value. -/
def simpleOp (op : Op) : Bool :=
  op != .ARM64CMP && op != .ARM64CMPconst && (loadOp? op).isNone && op != .ARM64LDP &&
    op != .ARM64SUB && op != .ARM64LoweredNilCheck && op != .ARM64CALLstatic &&
    (icallLead op).isNone && op != .ARM64LoweredWB && op != .ARM64LoweredGetClosurePtr &&
    !entryOp3 op

/-- Every value of `f` from value `i0` of block `b0` on (and of every other block) has a simple
op, no block is a register test (`Z`/`NZ`) and no edge goes to `b0`. -/
def simpleFrom (f : Func) (b0 : ID) (i0 : Nat) : Bool :=
  (List.range f.blockTab.size).all fun b =>
    match f.block? b with
    | none => true
    | some blk =>
      blk.kind != .ARM64Z && blk.kind != .ARM64NZ && blk.succs.all (·.b != b0) &&
        (List.range blk.values.size).all fun i =>
          (b == b0 && decide (i < i0)) ||
            match blk.values[i]?.bind f.value? with
            | some v => simpleOp v.op
            | none => true

theorem succ_goto_mem {b : Block} {k : Nat} {e : Edge} (h : succ b k = .ok (.goto e)) :
    e ∈ b.succs.toList := by
  unfold succ Res.ofOption at h
  split at h
  · rename_i x hx
    cases h
    simp only [Option.map_eq_some_iff, Next.goto.injEq] at hx
    obtain ⟨e', he, rfl⟩ := hx
    simpa using Array.mem_of_getElem? he
  · cases h

/-- A terminator goes along an edge of its block. -/
theorem stepTermL_goto_mem {fr : GoFV.SSA.Sem.Frame} {b : Block} {e : Edge}
    (h : stepTermL fr b = .ok (.goto e)) : e ∈ b.succs.toList := by
  unfold stepTermL at h
  split at h
  · split at h
    all_goals
      simp only [bind, Res.bind] at h
      split at h <;> try cases h
      dsimp only at h
      split at h <;> first | exact succ_goto_mem h | cases h
  · unfold stepTerm at h
    split at h
    all_goals first
      | exact succ_goto_mem h
      | cases h
      | (simp only [bind, Res.bind] at h
         split at h <;> try cases h
         dsimp only at h
         split at h <;> first
           | exact succ_goto_mem h
           | cases h
           | (split at h <;> first | cases h | (split at h <;> cases h)))

/-- A reachable state is in the start block after the start, or in a block an edge goes to. -/
theorem lreach_cases {env : Env} {lc : LocCtx} {b0 : ID} {i0 : Nat} {s0 : LocState} {b : ID}
    {i : Nat} {s : LocState} (h : LReach env lc b0 i0 s0 b i s) :
    (b = b0 ∧ i0 ≤ i) ∨ ∃ b' blk' e, lc.ctx.f.block? b' = some blk' ∧ e ∈ blk'.succs.toList ∧
      e.b = b := by
  induction h with
  | refl => exact Or.inl ⟨rfl, Nat.le_refl _⟩
  | val _ _ _ _ _ ih =>
    rcases ih with ⟨h1, h2⟩ | h
    · exact Or.inl ⟨h1, by omega⟩
    · exact Or.inr h
  | term _ hb ht _ =>
    obtain ⟨R, -, hn⟩ := stepTermLoc_gen ht
    exact Or.inr ⟨_, _, _, hb, stepTermL_goto_mem hn, rfl⟩

theorem g7Pre_simple {lc : LocCtx} {v : Value} (h : simpleOp v.op = true) (s : LocState) :
    G7Pre lc s v := by
  simp only [simpleOp, Bool.and_eq_true, bne_iff_ne, ne_eq, Option.isNone_iff_eq_none,
    Bool.not_eq_eq_eq_not, Bool.not_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  exact ⟨⟨⟨fun h => by rcases h with h | h <;> contradiction,
    (fun _ _ _ hl => by rw [h3] at hl; cases hl), fun h => absurd h h5⟩, fun h => absurd h h4⟩,
    fun h => absurd h h6⟩

/-- **`RunPre` of a function of simple ops** (`simpleFrom`): every premise is vacuous. -/
theorem runPre_simple {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ret : BitVec 64} {E0 : MatchEnv} {b0 : ID} {i0 : Nat} {s0 : LocState}
    (h : simpleFrom lc.ctx.f b0 i0 = true) : RunPre env H lc g L ret E0 b0 i0 s0 := by
  have hall := List.all_eq_true.1 h
  have hblk : ∀ b blk, lc.ctx.f.block? b = some blk →
      blk.kind ≠ .ARM64Z ∧ blk.kind ≠ .ARM64NZ ∧ (∀ e ∈ blk.succs.toList, e.b ≠ b0) ∧
      ∀ i id v, blk.values[i]? = some id → lc.ctx.f.value? id = some v →
        (b = b0 ∧ i < i0) ∨ simpleOp v.op = true := by
    intro b blk hb
    have hlt : b < lc.ctx.f.blockTab.size := by
      have hb' : (lc.ctx.f.blockTab[b]?).join = some blk := hb
      cases h' : lc.ctx.f.blockTab[b]? with
      | none => rw [h'] at hb'; cases hb'
      | some _ => exact (Array.getElem?_eq_some_iff.1 h').1
    have := hall b (List.mem_range.2 hlt)
    rw [hb] at this
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Array.all_eq_true_iff_forall_mem,
      List.all_eq_true, List.mem_range] at this
    obtain ⟨⟨⟨hz, hnz⟩, hs⟩, hv⟩ := this
    refine ⟨hz, hnz, fun e he => by simpa using hs e (by simpa using he), ?_⟩
    intro i id v hi hval
    have hlt' : i < blk.values.size := (Array.getElem?_eq_some_iff.1 hi).1
    have := hv i hlt'
    rw [hi] at this
    simp only [Option.bind_some, hval, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at this
    exact this
  intro b i s blk hr hb
  obtain ⟨hz, hnz, -, hv⟩ := hblk b blk hb
  have hpos : b = b0 → i0 ≤ i := by
    rcases lreach_cases hr with ⟨-, h⟩ | ⟨b', blk', e, hb', he, rfl⟩
    · exact fun _ => h
    · exact fun h => absurd h ((hblk b' blk' hb').2.2.1 e he)
  refine ⟨fun id v hi hval => ?_, fun _ hk => ?_⟩
  · have hs : simpleOp v.op = true := by
      rcases hv i id v hi hval with ⟨h1, h2⟩ | h
      · exact absurd (hpos h1) (by omega)
      · exact h
    have hs' := hs
    simp only [simpleOp, Bool.and_eq_true, bne_iff_ne, ne_eq, Option.isNone_iff_eq_none,
      Bool.not_eq_eq_eq_not, Bool.not_true] at hs'
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, hc⟩, hic⟩, hwb⟩, hcl⟩, hen⟩ := hs'
    refine ⟨hen, g7Pre_simple hs s, fun s' _ E m _ _ => ⟨fun h => absurd h hc, ?_,
      fun h => absurd h hwb, fun h => absurd h hcl⟩⟩
    intro n _ _ _ _ _ _ _ _ _ hn
    rw [hic] at hn
    cases hn
  · rcases hk with hk | hk
    · exact absurd hk hz
    · exact absurd hk hnz

/-! ## The simulation invariant -/

section Sim

variable {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
  {bstart : ID → Option Nat} {tab : PcTab} {kt : KTab} {E0 : MatchEnv}
  {spills : Array Spill} {o : ObjIn} {otab : Tab} {base : BitVec 64} {code : Code}
  {retM : BitVec 64}

/-- Before value `i` of block `b` (of `blk`), `runLoc` in `s` and the machine in `t`: a P0 state
`m` `LocMatch`ed to `s` under an activation `E` extending `E0`, `ObjRel`-related to `t`. -/
def SimAt (lc : LocCtx) (g : G2In) (L : Link) (ps : Array Prog) (tab : PcTab) (kt : KTab)
    (E0 : MatchEnv) (otab : Tab) (base : BitVec 64) (b : ID) (blk : Block) (i : Nat)
    (s : LocState) (t : MState) : Prop :=
  ∃ E m, E0.Extends E ∧ G10Env lc g L ps (endP L.text ps.toList) tab E ∧ LocMatch E s b i m ∧
    G3Inv E lc (kAt lc kt b blk i) s ∧ ObjRel (ObjEnv.map otab ps L base) m t ∧
    b ∈ lc.ctx.f.blocks.toList

/-- One value. -/
theorem sim_value (hc : checkG12 lc ps bstart g = .ok (tab, kt))
    (hO : ObjEnv ps spills o otab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hic : ∀ u, ICallOut L ps.toList u)
    {b : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {t : MState}
    (hb : lc.ctx.f.block? b = some blk) (hi : blk.values[i]? = some id)
    (hv : lc.ctx.f.value? id = some v) (hs : stepLoc env lc s v = .ok s')
    (hS : SimAt lc g L ps tab kt E0 otab base b blk i s t)
    (hen : entryOp3 v.op = false) (hpre : G7Pre lc s v)
    (hok : ∀ E m, E0.Extends E → LocMatch E s b i m →
      CallOK H E g L lc s s' v m ∧ ICallOK H E L (endP L.text ps.toList) lc s s' v m ∧
        WbOK H E g L lc s v m ∧ CloOK E s v m) :
    ∃ t', MStar H code retM t t' ∧ SimAt lc g L ps tab kt E0 otab base b blk (i + 1) s' t' := by
  obtain ⟨E, m, hx, hE, hm, hinv, hR, hbid⟩ := hS
  obtain ⟨hcall, hicall, hwb, hclo⟩ := hok E m hx hm
  obtain ⟨E', m', t', hx', hE', hm', hinv', ht, hR'⟩ :=
    g12_obj_value hc hE hbid hb hi hv hen hm hinv hpre hcall hicall hwb hclo hs hO hH hR (fun u _ => hic u)
  exact ⟨t', ht, E', m', MatchEnv.Extends.trans hx hx', hE', hm', hinv', hR', hbid⟩

/-- A terminator that goes to a block. -/
theorem sim_goto (hc : checkG12 lc ps bstart g = .ok (tab, kt))
    (hO : ObjEnv ps spills o otab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hic : ∀ u, ICallOut L ps.toList u)
    {b : ID} {blk blk' : Block} {e : Edge} {s s' : LocState} {t : MState}
    (hb : lc.ctx.f.block? b = some blk) (ht : stepTermLoc lc s blk = .ok (.goto e, s'))
    (hS : SimAt lc g L ps tab kt E0 otab base b blk blk.values.size s t)
    (hpre : G1TermPre lc s blk) :
    ∃ t', MStar H code retM t t' ∧ SimAt lc g L ps tab kt E0 otab base e.b blk' 0 s' t' := by
  obtain ⟨E, m, hx, hE, hm, hinv, hR, hbid⟩ := hS
  obtain ⟨m', t', hm', hinv', hmem, htm, hR'⟩ :=
    g12_obj_term (H := H) hc hE hbid hb hm hinv hpre ht hO hH hR (fun u _ => hic u)
  exact ⟨t', htm, E, m', hx, hE, hm', by rw [kAt_zero]; exact hinv', hR', hmem⟩

/-- The values of a block from value `i` on. -/
theorem sim_values (hc : checkG12 lc ps bstart g = .ok (tab, kt))
    (hO : ObjEnv ps spills o otab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hic : ∀ u, ICallOut L ps.toList u)
    {b0 : ID} {i0 : Nat} {s0 : LocState}
    (hP : RunPre env H lc g L (endP L.text ps.toList) E0 b0 i0 s0)
    {b : ID} {blk : Block} (hb : lc.ctx.f.block? b = some blk) :
    ∀ (n i : Nat) (s s' : LocState) (t : MState), i + n = blk.values.size →
      LReach env lc b0 i0 s0 b i s → SimAt lc g L ps tab kt E0 otab base b blk i s t →
      enterListLoc env lc s (blk.values.toList.drop i) = .ok s' →
      LReach env lc b0 i0 s0 b blk.values.size s' ∧
        ∃ t', MStar H code retM t t' ∧
          SimAt lc g L ps tab kt E0 otab base b blk blk.values.size s' t'
  | 0, i, s, s', t, hn, hr, hS, hl => by
    have hd : blk.values.toList.drop i = [] := List.drop_eq_nil_of_le (by simp; omega)
    rw [hd] at hl
    cases hl
    have hi : i = blk.values.size := by omega
    subst hi
    exact ⟨hr, t, .refl, hS⟩
  | n + 1, i, s, s', t, hn, hr, hS, hl => by
    have hlt : i < blk.values.toList.length := by simp; omega
    rw [List.drop_eq_getElem_cons hlt] at hl
    simp only [enterListLoc] at hl
    have hi : blk.values[i]? = some blk.values.toList[i] := by simp
    generalize blk.values.toList[i] = id at hl hi
    cases hv : lc.ctx.f.value? id with
    | none => rw [hv] at hl; cases hl
    | some v =>
      rw [hv] at hl
      simp only at hl
      cases hs : stepLoc env lc s v with
      | panic e mm => rw [hs] at hl; cases hl
      | stuck msg => rw [hs] at hl; cases hl
      | ok s1 =>
        rw [hs] at hl
        obtain ⟨hen, hpre, hok⟩ := (hP b i s blk hr hb).1 id v hi hv
        obtain ⟨t1, ht1, hS1⟩ := sim_value hc hO hH hic hb hi hv hs hS hen hpre (hok s1 hs)
        obtain ⟨hr', t', ht', hS'⟩ := sim_values hc hO hH hic hP hb n (i + 1) s1 s' t1 (by omega)
          (.val hr hb hi hv hs) hS1 hl
        exact ⟨hr', t', mstar_trans ht1 ht', hS'⟩

/-! ## The return -/

/-- What `runLoc`'s activation knows of the machine state `s0` at the function's entry
(`MachEntry`): `SP` after the prologue of a frame of `az` bytes, `g`, the caller's `LR` and `FP`
(`R29 = SP - 8` at entry), framed iff `az ≠ 0`, and the return address is no P0 address. -/
structure EntryEnv (E : MatchEnv) (L : Link) (ps : List Prog) (az : Int) (s0 : MState) : Prop where
  sp : E.sp + BitVec.ofInt 64 az = s0.sp
  g : E.g = s0.x 28
  lr : E.lr = s0.x 30
  fp : E.fp = s0.x 29
  fp0 : s0.x 29 = s0.sp - 8
  framed : E.framed = decide (az ≠ 0)
  lrOut : ¬ IsProgAddr L.text ps (s0.x 30) ∧ s0.x 30 ≠ endP L.text ps

theorem EntryEnv.extend {E E' : MatchEnv} {L : Link} {ps : List Prog} {az : Int} {s0 : MState}
    (h : EntryEnv E L ps az s0) (hx : E.Extends E') : EntryEnv E' L ps az s0 := by
  obtain ⟨he, -⟩ := hx
  rw [he]
  exact ⟨h.sp, h.g, h.lr, h.fp, h.fp0, h.framed, h.lrOut⟩

/-- The machine after the epilogue: back at the caller's return address with its `SP`, `g` and
frame pointer (`MachRet s0`), the registers of `runLoc`'s state `s` in theirs (but `X29`, `X30`),
and `s`'s memory injected. -/
structure ExitRel (E : MatchEnv) (s : LocState) (s0 t : MState) : Prop where
  ret : MachRet s0 t
  regs : ∀ r v, s.regs[r]? = some v →
    (∀ k, objX? r = some k → k ≠ 29 → k ≠ 30 → ValRel E.ι v (t.x k)) ∧
      (∀ k, objV? r = some k → FValRel v (t.v k))
  mem : ∃ mm, s.mem = .mem mm ∧ MemInj E.ι mm t.mem

theorem objX?_ne27 {r : Nat} {k : Reg} (h : objX? r = some k) : k ≠ 27 := by
  unfold objX? at h
  split at h
  · cases h; intro he; have := congrArg BitVec.toNat he; simp at this; omega
  · split at h
    · cases h; intro he; have := congrArg BitVec.toNat he; simp at this; omega
    · split at h
      · cases h; intro he; have := congrArg BitVec.toNat he; simp at this; omega
      · cases h

theorem succ_goto {b : Block} {k : Nat} {n : Next} (h : succ b k = .ok n) : ∃ e, n = .goto e := by
  unfold succ Res.ofOption at h
  split at h
  · rename_i x hx
    cases h
    simp only [Option.map_eq_some_iff] at hx
    obtain ⟨e, -, rfl⟩ := hx
    exact ⟨e, rfl⟩
  · cases h

/-- Only a `Ret` block returns. -/
theorem stepTermL_ret_kind {fr : GoFV.SSA.Sem.Frame} {b : Block} {rs : List Val} {mm : Mem}
    (h : stepTermL fr b = .ok (.ret rs mm)) : b.kind = .Ret := by
  have hs : ∀ {k}, succ b k ≠ .ok (.ret rs mm) := fun hk => by
    obtain ⟨e, he⟩ := succ_goto hk; cases he
  unfold stepTermL at h
  split at h
  · split at h
    all_goals
      simp only [bind, Res.bind] at h
      split at h <;> try cases h
      dsimp only at h
      split at h <;> first | exact absurd h hs | cases h
  · unfold stepTerm at h
    split at h
    all_goals first
      | assumption
      | exact absurd h hs
      | cases h
      | (simp only [bind, Res.bind] at h
         split at h <;> try cases h
         dsimp only at h
         split at h <;> first | exact absurd h hs | cases h)

/-- The terminator of a `Ret` block that `Cx.termG3` accepted is a `RET` after no-ops. -/
theorem termG3_ret {cx : Cx} {b : Block} {j : Nat} {next : Option (ID × Nat)}
    (h : cx.termG3 b j next = .ok ()) (hk : b.kind = .Ret) :
    ∃ k, OneAt cx.ps j { as := .RET } k := by
  rcases Cx.termG3_spec h with ⟨-, h2⟩ | ⟨asm, inv, ht, -⟩
  · unfold Cx.termG2 at h2
    rw [hk] at h2
    simp only [show (BlockKind.Ret == BlockKind.Exit) = false from rfl, Bool.false_eq_true,
      ↓reduceIte] at h2
    unfold Cx.term at h2
    obtain ⟨-, h2⟩ := ex_guard h2
    rw [hk] at h2
    obtain ⟨-, h2⟩ := ex_guard h2
    obtain ⟨k, hk', -⟩ := ex_bind_eq_ok h2
    exact ⟨k, Cx.one_spec hk'⟩
  · rw [hk] at ht; cases ht

theorem word_rel {f : BitVec 64 → BitVec 64} {m t : MState} (hR : ObjRel f m t) (a : BitVec 64) :
    t.word a = m.word a := by
  simp only [MState.word, hR.mem]

/-- **The return.** A `Ret` block's terminator, from related states, is matched by the machine
steps of the `RET` and of the epilogue (`obj_exit`) to the caller's return address. -/
theorem sim_ret (hc : checkG12 lc ps bstart g = .ok (tab, kt))
    (hO : ObjEnv ps spills o otab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hic : ∀ u, ICallOut L ps.toList u)
    {s0 : MState} (hEE : EntryEnv E0 L ps.toList otab.autosize s0)
    (hlf : otab.autosize = 0 ∨ otab.leaf = false)
    {b : ID} {blk : Block} {s s' : LocState} {rs : List Val} {mm : Mem} {t : MState}
    (hb : lc.ctx.f.block? b = some blk) (ht : stepTermLoc lc s blk = .ok (.ret rs mm, s'))
    (hS : SimAt lc g L ps tab kt E0 otab base b blk blk.values.size s t) :
    ∃ E t', E0.Extends E ∧ MStar H code retM t t' ∧ ExitRel E s s0 t' := by
  obtain ⟨E, m, hx, hE, hm, -, hR, hbid⟩ := hS
  have hEE' := hEE.extend hx
  obtain ⟨R, -, hn⟩ := stepTermLoc_gen ht
  have hk := stepTermL_ret_kind hn
  have hE2 := hE.env.env.env
  have hinvm := locMatch_inv hE2 hm
  obtain ⟨-, hlink, hpcOf, hret, -, -, -, -, -, -, hfr⟩ := hE2
  obtain ⟨c, hlc, hps, -, -, -, htm, -, -, -, -, hlt, hnd, hblocks⟩ := checkG12_spec hc
  obtain ⟨b', j, js, e, next, hb', -, hvals, hterm, -, hrow⟩ := Cx2.blocks_spec hblocks b hbid
  rw [hlc] at hb'
  rw [hb] at hb'
  cases hb'
  obtain ⟨hlen, -, -⟩ := Cx2.values_spec hvals
  rw [htm] at hterm
  obtain ⟨k', hone⟩ := termG3_ret hterm hk
  have hj : E.pcOf b blk.values.size = pcAt L.text ps.toList e := by
    rw [hpcOf]
    simp only [pcOfTab, hrow, Option.getD_some]
    congr 1
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [hlen]),
      show blk.values.size - js.length = 0 by simp [hlen]]
    rfl
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hj hinvm
  rw [hps] at hone
  obtain ⟨k, rfl, hk2, hok, hstar⟩ := pstar_oneAt (H := H) (sym := sym) (az := az) (ez := ez)
    (ret := endP text ps.toList) hnd hlt (by rw [← hL, ← htext]; exact hret) rfl hone m
  rw [pc_eta hm hj, ← hL, ← htext] at hstar
  obtain ⟨t1, ht1, hR1, -⟩ := obj_star hO hH hstar hR (by rw [htext]; exact hinvm) (fun u _ => hic u)
  obtain ⟨hras, -, -, hrto, -⟩ := Shape.ok_eq hok
  obtain ⟨-, -, -, -, -, -, -, hofs, -⟩ := checkObj_spec hO.check
  have hlen' : otab.offs.toList.length = ps.toList.length := by simp; exact hofs
  have hk3 : k < ps.size := by simpa using hk2
  have htpc : t1.pc = base + BitVec.ofNat 64 (otab.offs[k]!) := by
    rw [hR1.pc]
    show objMap ps.toList otab.offs.toList otab.endOff L.text base (pcAt L.text ps.toList k) = _
    have hpa : pcAt L.text ps.toList k = addrP L.text ps.toList[k].id := by
      simp [pcAt, hk3, addrP]
    rw [hpa, objMap_at hnd hlt hlen' hk2]
    simp [hk3, hofs]
  have hsp1 : t1.sp = E.sp := by rw [hR1.sp]; exact hm.frame.1
  obtain ⟨t2, ht2, hpc2, -, hsp2, h292, hx2, hv2, hm2, -⟩ :=
    obj_exit (H := H) hO.check hO.linked hO.size hO.ret hk3 (by simpa using hras)
      (by have := congrArg Addr.type hrto; simpa using this)
      (by have := congrArg Addr.sym hrto; simpa using this) htpc
      (by rw [hsp1]; exact ⟨hfr.lo, hfr.hi⟩)
  have hx1 : ∀ q : Reg, q ≠ 27 → q ≠ 30 → t1.x q = m.x q := fun q h27 h30 => hR1.x q h27 h30
  refine ⟨E, t2, hx, mstar_trans ht1 ht2, ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩⟩
  · -- the return address
    rw [hpc2]
    rcases hlf with h0 | hnl
    · have hfr0 : E.framed = false := by rw [hEE'.framed, h0]; rfl
      rw [ite_eq_left_of_eq_true _ _ (eq_true (Or.inl h0)), hR1.x30]
      show ObjEnv.map otab ps L base (m.x 30) = s0.x 30
      rw [(hm.frame.2.2.2 hfr0).2, hEE'.lr]
      exact objMap_fix hEE'.lrOut.1 hEE'.lrOut.2
    · by_cases h0 : otab.autosize = 0
      · have hfr0 : E.framed = false := by rw [hEE'.framed, h0]; rfl
        rw [ite_eq_left_of_eq_true _ _ (eq_true (Or.inl h0)), hR1.x30]
        show ObjEnv.map otab ps L base (m.x 30) = s0.x 30
        rw [(hm.frame.2.2.2 hfr0).2, hEE'.lr]
        exact objMap_fix hEE'.lrOut.1 hEE'.lrOut.2
      · have hfr1 : E.framed = true := by rw [hEE'.framed]; simp [h0]
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by simp [h0, hnl])), hsp1, word_rel hR1]
        show m.word E.sp = s0.x 30
        rw [(hm.frame.2.2.1 hfr1).2.1, hEE'.lr]
  · rw [hsp2, hsp1, hEE'.sp]
  · rw [hx2 28 (by decide) (by decide) (by decide), hx1 28 (by decide) (by decide), hm.frame.2.1,
      hEE'.g]
  · rw [h292]
    by_cases h0 : otab.autosize = 0
    · have hfr0 : E.framed = false := by rw [hEE'.framed, h0]; rfl
      rw [ite_eq_left_of_eq_true _ _ (eq_true h0), hx1 29 (by decide) (by decide), (hm.frame.2.2.2 hfr0).1, hEE'.fp]
    · have hfr1 : E.framed = true := by rw [hEE'.framed]; simp [h0]
      have hnl : otab.leaf = false := hlf.resolve_left h0
      rw [ite_eq_right_of_eq_false _ _ (eq_false h0), hnl,
        ite_eq_right_of_eq_false _ _ (eq_false (by decide)), hsp1, word_rel hR1]
      show m.word (E.sp - 8) = s0.x 29
      rw [(hm.frame.2.2.1 hfr1).2.2, hEE'.fp]
  · intro r v hv
    obtain ⟨hX, hV⟩ := hm.regs r v hv
    refine ⟨fun q hq h29 h30 => ?_, fun q hq => ?_⟩
    · rw [hx2 q (objX?_ne27 hq) h29 h30, hx1 q (objX?_ne27 hq) h30]
      exact hX q hq
    · rw [hv2, hR1.v]
      exact hV q hq
  · obtain ⟨mm', hs, hinj⟩ := hm.mem
    exact ⟨mm', hs, by rw [hm2, hR1.mem]; exact hinj⟩

/-- **A returning run.** From related states before value `i` of block `b`, a run that returns is
matched by a machine run to the caller's return address, related to the state before the `Ret`
block's terminator (`ExitRel`). -/
theorem sim_from_ret (hc : checkG12 lc ps bstart g = .ok (tab, kt))
    (hO : ObjEnv ps spills o otab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hic : ∀ u, ICallOut L ps.toList u)
    {s0 : MState} (hEE : EntryEnv E0 L ps.toList otab.autosize s0)
    (hlf : otab.autosize = 0 ∨ otab.leaf = false)
    {b0 : ID} {i0 : Nat} {sI : LocState}
    (hP : RunPre env H lc g L (endP L.text ps.toList) E0 b0 i0 sI) {rs : List Val} {mm : Mem} :
    ∀ (fuel : Nat) (b : ID) (blk : Block) (i : Nat) (s : LocState) (t : MState),
      LReach env lc b0 i0 sI b i s → lc.ctx.f.block? b = some blk → i ≤ blk.values.size →
      SimAt lc g L ps tab kt E0 otab base b blk i s t →
      runFromLoc env lc fuel s b i = .returned rs mm →
      ∃ E bF blkF sF sF' t', E0.Extends E ∧ MStar H code retM t t' ∧ ExitRel E sF s0 t' ∧
        lc.ctx.f.block? bF = some blkF ∧ stepTermLoc lc sF blkF = .ok (.ret rs mm, sF') := by
  intro fuel
  induction fuel with
  | zero => ?_
  | succ n ih => ?_
  all_goals
    intro b blk i s t hr hb hi hS hrun
    simp only [runFromLoc, hb] at hrun
    cases hl : enterListLoc env lc s (blk.values.toList.drop i) with
    | panic e mm' => rw [hl] at hrun; cases hrun
    | stuck msg => rw [hl] at hrun; cases hrun
    | ok s1 =>
      rw [hl] at hrun
      simp only at hrun
      obtain ⟨hr1, t1, ht1, hS1⟩ :=
        sim_values hc hO hH hic hP hb (blk.values.size - i) i s s1 t (by omega) hr hS hl
      cases hst : stepTermLoc lc s1 blk with
      | panic e mm' => rw [hst] at hrun; cases hrun
      | stuck msg => rw [hst] at hrun; cases hrun
      | ok r =>
        obtain ⟨nx, s2⟩ := r
        rw [hst] at hrun
        cases nx with
        | ret rs' mm' =>
          simp only [Outcome.returned.injEq] at hrun
          obtain ⟨rfl, rfl⟩ := hrun
          obtain ⟨E, t2, hx, ht2, hX⟩ := sim_ret hc hO hH hic hEE hlf hb hst hS1
          exact ⟨E, b, blk, s1, s2, t2, hx, mstar_trans ht1 ht2, hX, hb, hst⟩
        | goto e =>
          simp only at hrun
          first
          | (simp [runLoopLoc] at hrun; done)
          | (rw [runLoopLoc_succ] at hrun
             cases hb2 : lc.ctx.f.block? e.b with
             | none => simp [runFromLoc, hb2] at hrun
             | some blk2 =>
               have hpre := ((hP b blk.values.size s1 blk hr1 hb).2 rfl)
               obtain ⟨t2, ht2, hS2⟩ := sim_goto (blk' := blk2) hc hO hH hic hb hst hS1 hpre
               obtain ⟨E, bF, blkF, sF, sF', t3, hx, ht3, hX, hbF, hF⟩ :=
                 ih e.b blk2 0 s2 t2 (.term hr1 hb hst) hb2 (Nat.zero_le _) hS2 hrun
               exact ⟨E, bF, blkF, sF, sF', t3, hx, mstar_trans ht1 (mstar_trans ht2 ht3), hX,
                 hbF, hF⟩)

/-! ## The entry -/

/-- What the run's first state `s` (before value `k` of the entry block) holds of the machine
state `s0` at the function's entry: every register its value (the registers the prologue may
write, `R16`, `R17`, `R20`, `R29`, hold none), no flags, no slot, and its memory injected. -/
structure EntryMatch (E : MatchEnv) (s : LocState) (s0 : MState) : Prop where
  regs : ∀ r v, s.regs[r]? = some v →
    (∀ q, objX? r = some q → ((q = 16 ∨ q = 17 ∨ q = 20 ∨ q = 29) → v = .poison) ∧
      ValRel E.ι v (s0.x q)) ∧ (∀ q, objV? r = some q → FValRel v (s0.v q))
  flags : s.flags = .poison
  slots : s.slots = []
  mem : ∃ mm, s.mem = .mem mm ∧ MemInj E.ι mm s0.mem

@[simp] private theorem wh_throw {ε α : Type} (e : ε) : (throw e : Except ε α) = .error e := rfl

@[simp] private theorem wh_ite_ok {ε α : Type} {c : Prop} [Decidable c] {e : ε}
    {b : Except ε α} {v : α} : ((if c then Except.error e else b) = .ok v) ↔ ¬c ∧ b = .ok v := by
  split <;> simp [*]

@[simp] private theorem wh_ite_ok' {ε α : Type} {c : Prop} [Decidable c] {e : ε}
    {b : Except ε α} {v : α} : ((if c then b else Except.error e) = .ok v) ↔ c ∧ b = .ok v := by
  split <;> simp [*]

/-- `checkObj`'s frame size is non-negative (the `TEXT` offset modulo `2^32`). -/
private theorem wh_az_nonneg {ps : Array Prog} {spills : Array Spill} {o : ObjIn} {tab : Tab}
    (h : checkObj ps spills o = .ok tab) : 0 ≤ tab.autosize := by
  unfold checkObj at h
  cases h0 : ps[0]? with
  | none =>
    rw [h0] at h
    cases h
  | some text =>
    rw [h0] at h
    simp only [bind, Except.bind, pure, Except.pure, wh_throw, wh_ite_ok, wh_ite_ok'] at h
    obtain ⟨-, -, -, -, h⟩ := h
    split at h
    case h_2 => cases h
    split at h
    · cases h
    split at h
    · cases h
    rw [wh_ite_ok] at h
    obtain ⟨-, h⟩ := h
    split at h
    · cases h
    split at h
    · split at h
      · cases h
      · cases h
        exact Int.emod_nonneg _ (by decide)
    · cases h
      exact Int.emod_nonneg _ (by decide)

theorem stk_window {sp y : BitVec 64} (hlo : 4096 + 8 ≤ sp.toNat) (hhi : sp.toNat + 8 ≤ 2 ^ 64)
    (h : (y - (sp - 8)).toNat < 16) : sp.toNat - 8 ≤ y.toNat ∧ y.toNat < sp.toNat + 8 := by
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  rw [h64] at hhi
  bv_omega

/-- **The entry.** From the machine state `s0` at the function's entry (`MachEntry`), when the
stack check passes, the prologue (`obj_entry`) runs to a state related (`SimAt`) to the run's
first state `sI` before value `k` of block `b`, whose P0 address maps to the body's start. -/
theorem sim_entry (hO : ObjEnv ps spills o otab L base code retM)
    {room : Nat} {s0 : MState} (hME : MachEntry code base room s0)
    (hroom : otab.autosize + 8 ≤ room) (hg : (s0.x 28).toNat + 32 ≤ 2 ^ 64)
    (hpass : ∀ ce tail gOff, otab.check = some (ce, tail, gOff) →
      CheckPasses otab.autosize gOff s0)
    (hE : G10Env lc g L ps (endP L.text ps.toList) tab E0)
    (hEE : EntryEnv E0 L ps.toList otab.autosize s0)
    {sI : LocState} {b : ID} {blk : Block} {k : Nat} (hent : EntryMatch E0 sI s0)
    (hinv : G3Inv E0 lc (kAt lc kt b blk k) sI) (hbm : b ∈ lc.ctx.f.blocks.toList)
    (hpc : ObjEnv.map otab ps L base (E0.pcOf b k) = base + BitVec.ofNat 64 (otab.offs[0]!)) :
    ∃ t, MStar H code retM s0 t ∧ SimAt lc g L ps tab kt E0 otab base b blk k sI t := by
  obtain ⟨s1, h1, hbody, hpc1, hx1, hv1, hm1⟩ :=
    obj_entry (H := H) hO.check hO.linked hO.size hO.ret hME hroom hg hpass
  have haz := wh_az_nonneg hO.check
  have hfr := hE.env.env.env.frame
  have hsp0 : E0.sp = s0.sp - BitVec.ofInt 64 otab.autosize := by
    rw [← hEE.sp, BitVec.add_sub_cancel]
  have h30 : s1.x 30 = s0.x 30 := hx1 30 (by decide) (by decide) (by decide) (by decide)
    (by decide)
  refine ⟨s1, h1, E0, { s1 with pc := E0.pcOf b k }, ⟨rfl, fun _ _ h => h⟩, hE, ?_, hinv,
    ⟨fun _ _ _ => rfl, ?_, rfl, rfl, rfl, rfl, by rw [hpc1, ← hpc]⟩, hbm⟩
  rotate_left
  · show s1.x 30 = objMap ps.toList otab.offs.toList otab.endOff L.text base (s1.x 30)
    rw [h30, objMap_fix hEE.lrOut.1 hEE.lrOut.2]
  -- the `LocMatch` at the entry
  by_cases h0 : otab.autosize = 0
  · simp only [h0, ↓reduceIte] at hbody
    subst hbody
    have hfr0 : E0.framed = false := by rw [hEE.framed, h0]; rfl
    refine ⟨fun r v hv => ?_, ?_, ?_, ?_, ⟨?_, ?_, fun h => ?_, fun _ => ?_⟩, rfl⟩
    · obtain ⟨hX, hV⟩ := hent.regs r v hv
      exact ⟨fun q hq => (hX q hq).2, hV⟩
    · rw [hent.flags]; trivial
    · intro k v h; rw [hent.slots] at h; cases h
    · exact hent.mem
    · show s1.sp = E0.sp
      rw [hsp0, h0]; simp
    · exact hEE.g.symm
    · rw [hfr0] at h; cases h
    · exact ⟨hEE.fp.symm, hEE.lr.symm⟩
  · simp only [h0, ↓reduceIte] at hbody
    have hfr1 : E0.framed = true := by rw [hEE.framed]; simp [h0]
    have hsp1 : s1.sp = E0.sp := by
      rw [hbody.sp, hsp0, ofInt_nonneg haz]
    refine ⟨fun r v hv => ?_, ?_, ?_, ?_, ⟨hsp1, ?_, fun _ => ⟨?_, ?_, ?_⟩, fun h => ?_⟩, rfl⟩
    · obtain ⟨hX, hV⟩ := hent.regs r v hv
      refine ⟨fun q hq => ?_, fun q hq => ?_⟩
      · by_cases hq' : q = 16 ∨ q = 17 ∨ q = 20 ∨ q = 29
        · rw [(hX q hq).1 hq']; trivial
        · simp only [not_or] at hq'
          show ValRel E0.ι v (s1.x q)
          rw [hx1 q hq'.1 hq'.2.1 hq'.2.2.1 (objX?_ne27 hq) hq'.2.2.2]
          exact (hX q hq).2
      · show FValRel v (s1.v q)
        rw [hv1]; exact hV q hq
    · rw [hent.flags]; trivial
    · intro k v h; rw [hent.slots] at h; cases h
    · obtain ⟨mm, hmm, hinj⟩ := hent.mem
      refine ⟨mm, hmm, memInj_congr hinj fun bk al a hb ha i hi => hm1 _ ?_⟩
      obtain ⟨mm', hmm', -, hsep⟩ := hinv.core.mem
      rw [hmm] at hmm'
      cases hmm'
      obtain ⟨a', ha', -, hwin⟩ := hinj.mapped bk al hb
      rw [ha] at ha'
      cases ha'
      have hy : (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
        have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
        rw [h64] at hwin
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h64]
        omega
      refine Nat.le_of_not_lt fun hlt =>
        hsep bk al a hb ha (a + BitVec.ofNat 64 i) (Or.inl ⟨hfr1, ?_⟩) ⟨by omega, by omega⟩
      rw [hsp1] at hlt
      exact stk_window hfr.lo hfr.hi hlt
    · show s1.x 28 = E0.g
      rw [hbody.g, hEE.g]
    · show s1.x 29 = E0.sp - 8
      rw [hbody.r29, hsp1]
    · show s1.word E0.sp = E0.lr
      rw [← hsp1, hbody.lr, hEE.lr]
    · show s1.word (E0.sp - 8) = E0.fp
      rw [← hsp1, hbody.fp, hEE.fp]
    · rw [hfr1] at h; cases h

/-! ## Whole functions -/

/-- A run of the machine that reaches the return address returns. -/
theorem mstar_returned {s0 t : MState} (h : MStar H code retM s0 t) (hpc : t.pc = retM) :
    ∃ n, runMach H code retM n s0 = .returned t := by
  obtain ⟨n, hn⟩ := h.runMach
  exact ⟨n + 1, by rw [hn 1]; simp [runMach, hpc]⟩

/-- **A whole function of slice G12, returning, down to the machine words.** `checkG12` and
`checkObj` accept the function; the machine starts at its entry (`MachEntry`, the return address
`s0.x 30`) and the stack check passes. The run of `runLoc` (`runLoopLoc`, from the state `s` at
the entry block) first runs `k` values of the entry block (the entry values) to `sI`, which is
related to `s0` (`EntryMatch`, `EntryEnv`: the arguments in their registers, the memory injected,
the frame); every later step meets its premises (`RunPre`). If it returns, `runMach` returns to
`s0.x 30` in a state related to the state `sF` before the returning terminator (`ExitRel`:
`MachRet s0`, the registers, the memory). -/
theorem obj_whole_ret (hc : checkG12 lc ps bstart g = .ok (tab, kt))
    {room : Nat} {s0 : MState} (hO : ObjEnv ps spills o otab L base code (s0.x 30))
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hic : ∀ u, ICallOut L ps.toList u)
    (hME : MachEntry code base room s0) (hroom : otab.autosize + 8 ≤ room)
    (hg : (s0.x 28).toNat + 32 ≤ 2 ^ 64)
    (hpass : ∀ ce tail gOff, otab.check = some (ce, tail, gOff) →
      CheckPasses otab.autosize gOff s0)
    (hlf : otab.autosize = 0 ∨ otab.leaf = false)
    (hE : G10Env lc g L ps (endP L.text ps.toList) tab E0)
    (hEE : EntryEnv E0 L ps.toList otab.autosize s0)
    {s sI : LocState} {blkE : Block} {k : Nat}
    (hbE : lc.ctx.f.block? lc.ctx.f.entry = some blkE)
    (hbm : lc.ctx.f.entry ∈ lc.ctx.f.blocks.toList) (hk : k ≤ blkE.values.size)
    (hpre : enterListLoc env lc s (blkE.values.toList.take k) = .ok sI)
    (hent : EntryMatch E0 sI s0) (hinv : G3Inv E0 lc (kAt lc kt lc.ctx.f.entry blkE k) sI)
    (hpc : ObjEnv.map otab ps L base (E0.pcOf lc.ctx.f.entry k) =
      base + BitVec.ofNat 64 (otab.offs[0]!))
    (hP : RunPre env H lc g L (endP L.text ps.toList) E0 lc.ctx.f.entry k sI)
    {fuel : Nat} {rs : List Val} {mm : Mem}
    (hrun : runLoopLoc env lc fuel s lc.ctx.f.entry = .returned rs mm) :
    ∃ E bF blkF sF sF' t' n, E0.Extends E ∧ runMach H code (s0.x 30) n s0 = .returned t' ∧
      ExitRel E sF s0 t' ∧ lc.ctx.f.block? bF = some blkF ∧
      stepTermLoc lc sF blkF = .ok (.ret rs mm, sF') := by
  cases fuel with
  | zero => simp [runLoopLoc] at hrun
  | succ n =>
    rw [runLoopLoc_entry hbE hpre] at hrun
    obtain ⟨t1, ht1, hS⟩ := sim_entry (H := H) hO hME hroom hg hpass hE hEE hent hinv hbm hpc
    obtain ⟨E, bF, blkF, sF, sF', t', hx, ht', hX, hbF, hF⟩ :=
      sim_from_ret hc hO hH hic hEE hlf hP n _ blkE k sI t1 .refl hbE hk hS hrun
    obtain ⟨n', hn'⟩ := mstar_returned (mstar_trans ht1 ht') hX.ret.pc
    exact ⟨E, bF, blkF, sF, sF', t', n', hx, hn', hX, hbF, hF⟩

end Sim

end GoFV.Proof.Obj
