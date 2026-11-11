import GoFV.Proof.Obj.AtomPanic
import GoFV.Proof.Obj.EntrySkip
import GoFV.Gen.Entry62
import GoFV.Proof.Pass.DeadRelL
import GoFV.Proof.Obj.Results
import GoFV.Proof.Obj.Frame
import GoFV.Proof.CongLoc

variable [GoFV.SSA.Sem.Addrs]

/-!
# Whole functions: `runLoc` → `runMach` across blocks (`docs/plans/proofs3.md` §1, §7, §9)

`g66_obj_value`/`g66_obj_term` chained along a whole `runLoc` run, with the prologue (`obj_entry`)
before it and the epilogue (`obj_exit`) after it; the results in their ABI registers (`retRegsOK`,
`ret_results`); a panicking run (nil checks, faulting accesses and atomics, bounds checks, callees
that panic) matched by a panicking machine run.
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

/-- In a lowered function, the first `k` values of a block, which keep the memory (`keepsTo`),
keep the initial memory (`MemInit`, `memInit_stepLoc_keep`). -/
theorem memInit_enterKeep {env : Env} {lc : LocCtx} {b : Block} (hl : lc.ctx.f.lowered = true) :
    ∀ (k : Nat) (s s' : LocState), keepsTo lc b k = true → MemInit s →
      enterListLoc env lc s (b.values.toList.take k) = .ok s' → MemInit s'
  | 0, s, s', _, h, he => by
    simp only [List.take_zero, enterListLoc, Res.ok.injEq] at he
    exact he ▸ h
  | k + 1, s, s', hk, h, he => by
    have hk0 : keepsTo lc b k = true := by
      unfold keepsTo at hk ⊢
      rw [List.range_succ, List.all_append, Bool.and_eq_true] at hk
      exact hk.1
    rw [List.take_add_one, enterListLoc_append] at he
    cases h1 : enterListLoc env lc s (b.values.toList.take k) with
    | panic e m => rw [h1] at he; cases he
    | stuck msg => rw [h1] at he; cases he
    | ok s1 =>
      rw [h1] at he
      simp only at he
      have ih := memInit_enterKeep hl k s s1 hk0 h h1
      cases hid : b.values.toList[k]? with
      | none =>
        rw [hid] at he
        simp only [Option.toList, enterListLoc, Res.ok.injEq] at he
        exact he ▸ ih
      | some id =>
        rw [hid] at he
        simp only [Option.toList, enterListLoc] at he
        have hi : b.values[k]? = some id := by simpa using hid
        cases hv : lc.ctx.f.value? id with
        | none => rw [hv] at he; cases he
        | some v =>
          rw [hv] at he
          simp only at he
          cases hs : stepLoc env lc s1 v with
          | ok s2 =>
            rw [hs] at he
            simp only [enterListLoc, Res.ok.injEq] at he
            exact he ▸ memInit_stepLoc_keep hl (keepsTo_succ hk hi hv).2 ih hs
          | panic e m => rw [hs] at he; cases he
          | stuck msg => rw [hs] at he; cases he

/-- The run's first state holding the initial memory, the entry values before `k` run to a state
that holds it at a clean position `k` of the entry block (`MemAt`). -/
theorem memAt_enter {env : Env} {lc : LocCtx} {b : ID} {blk : Block} {k : Nat} {s sI : LocState}
    (h : MemInit s) (he : enterListLoc env lc s (blk.values.toList.take k) = .ok sI) :
    MemAt lc b blk k sI := fun hl _ hc => by
  unfold cleanAt at hc
  rw [Bool.and_eq_true] at hc
  exact memInit_enterKeep hl k s sI hc.2 h he

/-- G56's read-only premise along the run: every state the run reaches from `(b0, i0, s0)` has
the float constant symbols among the Prog list's symbols in its memory (`RoPre56`;
`verified_mach` gives it by `lreach_roMem`). -/
def RoRun (g : G2In) (env : Env) (lc : LocCtx) (b0 : ID) (i0 : Nat) (s0 : LocState) : Prop :=
  ∀ b i s, LReach env lc b0 i0 s0 b i s → RoPre56 g s

/-- `RoRun` of a Prog list with no float constant symbol. -/
theorem roRun_nil {g : G2In} {env : Env} {lc : LocCtx} {b0 : ID} {i0 : Nat} {s0 : LocState}
    (h : constRo (symNames g) = []) : RoRun g env lc b0 i0 s0 := by
  intro _ _ _ _ _ _ n a hn
  rw [h] at hn
  cases hn

/-- **The per-step premises of the run** at every state it reaches from `(b0, i0, s0)`: those of
`g66L_value` at a value whose step succeeds (`G54Pre`: `G53Pre`, that is `G51Pre` (G49 and G52
adding none: `G50Pre` (`G46Pre`, G47 adding none: `G38Pre`, `CmpPre` and `FLoadPre`; and G50's
`PairPre50`) and G51's `Pre51a`) and G53's `Pre53a`; and G54's `Pre54a` and `Pre54b`; G55–G62
adding none; G63's `FReloadPre` (a float reload reads no pointer without an integer form) and
G64's `QLoadPre` (a 128-bit load reads valid bytes); G65 and G66 adding none;
`GetGOK` and the trusted contracts `CallOK`,
`CallOKZ`, `ICallOK`, `WbOK`, `CloOK`, `MemEqOK` at every `LocMatch`ed machine state of an
activation extending `E0`; nothing at a step that panics, which `RunPanicPre`
covers) and `g66L_term` (`G1TermPre`); no value after the start is an entry value, but an
`InitMem` in a lowered function (`g66L_initMem`, at the clean positions `checkG66L` accepts). -/
def RunPre (env : Env) (H : Hooks) (lc : LocCtx) (g : G2In) (L : Link) (ret : BitVec 64)
    (E0 : MatchEnv) (b0 : ID) (i0 : Nat) (s0 : LocState) : Prop :=
  ∀ b i s blk, LReach env lc b0 i0 s0 b i s → lc.ctx.f.block? b = some blk →
    (∀ id v, blk.values[i]? = some id → lc.ctx.f.value? id = some v →
      (entryOp24 v.op = false ∨ (v.op = .InitMem ∧ lc.ctx.f.lowered = true)) ∧
      ∀ s', stepLoc env lc s v = .ok s' →
        (G54Pre lc s v ∧ FReloadPre lc s v ∧ QLoadPre lc s v) ∧ ∀ E m, E0.Extends E →
        LocMatch E s b i m →
        CallOK H E g L lc s s' v m ∧ CallOKZ H E g L lc s s' v m ∧ ICallOK H E L ret lc s s' v m ∧
          WbOK H E g L lc s v m ∧ CloOK E s v m ∧ GetGOK E v ∧ MemEqOK H E g L lc s v m) ∧
    (i = blk.values.size → G1TermPre lc s blk)

/-- **`RunPre` in G48's mode** (an activation whose `outargs` block sits at `SP`, for a function
that needs it, `needs48`): `RunPre` with the trusted contracts `CallOKS`, `CallOKZS`, `ICallOKS`,
`WbOKS`, `MemEqOKS` (`SepFromW` in place of `SepFrom`) and G48's `CallOKStk` (a static call with
stack arguments or results). -/
def RunPreS (env : Env) (H : Hooks) (lc : LocCtx) (g : G2In) (L : Link) (ret : BitVec 64)
    (E0 : MatchEnv) (b0 : ID) (i0 : Nat) (s0 : LocState) : Prop :=
  ∀ b i s blk, LReach env lc b0 i0 s0 b i s → lc.ctx.f.block? b = some blk →
    (∀ id v, blk.values[i]? = some id → lc.ctx.f.value? id = some v →
      (entryOp24 v.op = false ∨ (v.op = .InitMem ∧ lc.ctx.f.lowered = true)) ∧
      ∀ s', stepLoc env lc s v = .ok s' →
        (G54Pre lc s v ∧ FReloadPre lc s v ∧ QLoadPre lc s v) ∧ ∀ E m, E0.Extends E →
        LocMatch E s b i m →
        CallOKS H E g L lc s s' v m ∧ CallOKZS H E g L lc s s' v m ∧
          ICallOKS H E L ret lc s s' v m ∧ WbOKS H E g L lc s v m ∧ CloOK E s v m ∧
          GetGOK E v ∧ MemEqOKS H E g L lc s v m ∧ CallOKStk H E g L lc s s' v m) ∧
    (i = blk.values.size → G1TermPre lc s blk)

/-- `RunPre` (`osp = false`) or `RunPreS` (`osp = true`) in one form: the contracts of the mode
`osp`, `CallOKStk` at the mode `true`. -/
def RunPreM (osp : Bool) (env : Env) (H : Hooks) (lc : LocCtx) (g : G2In) (L : Link)
    (ret : BitVec 64) (E0 : MatchEnv) (b0 : ID) (i0 : Nat) (s0 : LocState) : Prop :=
  ∀ b i s blk, LReach env lc b0 i0 s0 b i s → lc.ctx.f.block? b = some blk →
    (∀ id v, blk.values[i]? = some id → lc.ctx.f.value? id = some v →
      (entryOp24 v.op = false ∨ (v.op = .InitMem ∧ lc.ctx.f.lowered = true)) ∧
      ∀ s', stepLoc env lc s v = .ok s' →
        (G54Pre lc s v ∧ FReloadPre lc s v ∧ QLoadPre lc s v) ∧ ∀ E m, E0.Extends E →
        LocMatch E s b i m →
        CallOKAt osp H E g L lc s s' v m ∧ CallOKZAt osp H E g L lc s s' v m ∧
          ICallOKAt osp H E L ret lc s s' v m ∧ WbOKAt osp H E g L lc s v m ∧
          CloOK E s v m ∧ GetGOK E v ∧ MemEqOKAt osp H E g L lc s v m ∧
          (osp = true → CallOKStk H E g L lc s s' v m)) ∧
    (i = blk.values.size → G1TermPre lc s blk)

section RunPreM

variable {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ret : BitVec 64}
  {E0 : MatchEnv} {b0 : ID} {i0 : Nat} {s0 : LocState}

theorem RunPre.m (h : RunPre env H lc g L ret E0 b0 i0 s0) :
    RunPreM false env H lc g L ret E0 b0 i0 s0 := fun b i s blk hr hb =>
  ⟨fun id v hi hv => ⟨(h b i s blk hr hb).1 id v hi hv |>.1, fun s' hs =>
    ⟨((h b i s blk hr hb).1 id v hi hv |>.2 s' hs).1, fun E m hx hm =>
      have ⟨h1, h2, h3, h4, h5, h6, h7⟩ := ((h b i s blk hr hb).1 id v hi hv |>.2 s' hs).2 E m hx hm
      ⟨h1, h2, h3, h4, h5, h6, h7, fun h => by cases h⟩⟩⟩,
    (h b i s blk hr hb).2⟩

theorem RunPreS.m (h : RunPreS env H lc g L ret E0 b0 i0 s0) :
    RunPreM true env H lc g L ret E0 b0 i0 s0 := fun b i s blk hr hb =>
  ⟨fun id v hi hv => ⟨(h b i s blk hr hb).1 id v hi hv |>.1, fun s' hs =>
    ⟨((h b i s blk hr hb).1 id v hi hv |>.2 s' hs).1, fun E m hx hm =>
      have ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
        ((h b i s blk hr hb).1 id v hi hv |>.2 s' hs).2 E m hx hm
      ⟨h1, h2, h3, h4, h5, h6, h7, fun _ => h8⟩⟩⟩,
    (h b i s blk hr hb).2⟩

theorem RunPreM.pre (h : RunPreM false env H lc g L ret E0 b0 i0 s0) :
    RunPre env H lc g L ret E0 b0 i0 s0 := fun b i s blk hr hb =>
  ⟨fun id v hi hv => ⟨(h b i s blk hr hb).1 id v hi hv |>.1, fun s' hs =>
    ⟨((h b i s blk hr hb).1 id v hi hv |>.2 s' hs).1, fun E m hx hm =>
      have ⟨h1, h2, h3, h4, h5, h6, h7, _⟩ :=
        ((h b i s blk hr hb).1 id v hi hv |>.2 s' hs).2 E m hx hm
      ⟨h1, h2, h3, h4, h5, h6, h7⟩⟩⟩,
    (h b i s blk hr hb).2⟩

theorem RunPreM.preS (h : RunPreM true env H lc g L ret E0 b0 i0 s0) :
    RunPreS env H lc g L ret E0 b0 i0 s0 := fun b i s blk hr hb =>
  ⟨fun id v hi hv => ⟨(h b i s blk hr hb).1 id v hi hv |>.1, fun s' hs =>
    ⟨((h b i s blk hr hb).1 id v hi hv |>.2 s' hs).1, fun E m hx hm =>
      have ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
        ((h b i s blk hr hb).1 id v hi hv |>.2 s' hs).2 E m hx hm
      ⟨h1, h2, h3, h4, h5, h6, h7, h8 rfl⟩⟩⟩,
    (h b i s blk hr hb).2⟩

end RunPreM

/-! ## Functions of simple ops -/

/-- An op none of whose per-step premises says anything: no compare, load, pair load,
register-index load, subtraction, nil check, zeroing, call, write barrier, closure pointer,
`GetG`, `LoweredMemEq`, acquire load, G41 compare, float load, float register-index load, G46
float op (`fops46`), G50 pair load (`pairOp50`), G51 `CMN`/`CMPshiftRA` (`Pre51a`), G53
`LoweredMove` (`Pre53a`) or G54 loop (`Pre54a`, `Pre54b`), G63 reload (`LoadReg`, `FReloadPre`)
or G64 128-bit load (`FMOVQload`, `FLDPQ`, `QLoadPre`), and no entry value. -/
def simpleOp (op : Op) : Bool :=
  op != .LoadReg && op != .ARM64FMOVQload && op != .ARM64FLDPQ &&
    op != .ARM64CMP && op != .ARM64CMPconst && (loadOp? op).isNone && op != .ARM64LDP &&
    op != .ARM64SUB && op != .ARM64LoweredNilCheck && op != .ARM64CALLstatic &&
    (icallLead op).isNone && op != .ARM64LoweredWB && op != .ARM64LoweredGetClosurePtr &&
    !entryOp3 op && op != .ARM64LoweredZero && (loadIdxOp? op).isNone && op != .GetG &&
    op != .ARM64LoweredMemEq && (ldar? op).isNone && op != .ARM64CMNconst &&
    (cmpSh41? op).isNone && op != .ARM64FMOVSload && op != .ARM64FMOVDload &&
    (fLoadIdxOp? op).isNone && decide (op ∉ fops46) && (pairOp50 op).isNone &&
    op != .ARM64CMN && op != .ARM64CMPshiftRA && op != .ARM64LoweredMove &&
    op != .ARM64LoweredZeroLoop && op != .ARM64LoweredMoveLoop

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

/-- A run whose first step panics reaches no state but its start. -/
theorem lreach_of_panicAt {env : Env} {lc : LocCtx} {b0 : ID} {i0 : Nat} {s0 : LocState}
    {blk : Block} {id : ID} {v : Value} {e : Panic} {mm : Mem}
    (hb : lc.ctx.f.block? b0 = some blk) (hi : blk.values[i0]? = some id)
    (hv : lc.ctx.f.value? id = some v) (hs : stepLoc env lc s0 v = .panic e mm) {b : ID}
    {i : Nat} {s : LocState} (h : LReach env lc b0 i0 s0 b i s) : b = b0 ∧ i = i0 ∧ s = s0 := by
  induction h with
  | refl => exact ⟨rfl, rfl, rfl⟩
  | val _ hb' hi' hv' hs' ih =>
    obtain ⟨rfl, rfl, rfl⟩ := ih
    rw [hb] at hb'
    cases hb'
    rw [hi] at hi'
    cases hi'
    rw [hv] at hv'
    cases hv'
    rw [hs] at hs'
    cases hs'
  | term _ hb' _ ih =>
    obtain ⟨rfl, hsz, rfl⟩ := ih
    rw [hb] at hb'
    cases hb'
    rw [← hsz] at hi
    simp at hi

/-! ## No `Arg` after the start

G62's `Arg`s run at the head of the entry block before the start `k` (`entryLen`), on `runLoc`'s
side only; their slots are related at the entry by the caller's side (`EntryMatch.stack`). No
state the run reaches from `(entry, k)` is at an `Arg` (`argsBefore`, checked), so `ArgOK`,
`g66_value`'s premise, holds vacuously along the run. -/

/-- No state the run reaches from `(b0, i0, s0)` is at an `Arg`. -/
def NoArgRun (env : Env) (lc : LocCtx) (b0 : ID) (i0 : Nat) (s0 : LocState) : Prop :=
  ∀ b i s blk id v, LReach env lc b0 i0 s0 b i s → lc.ctx.f.block? b = some blk →
    blk.values[i]? = some id → lc.ctx.f.value? id = some v → v.op ≠ .Arg

/-- Every `Arg` before value `k` of the entry block, no edge to the entry block (`argsBefore`):
no `Arg` runs from `(entry, k)`. -/
theorem noArgRun_of_argsBefore {env : Env} {lc : LocCtx} {k : Nat} {s0 : LocState}
    (h : argsBefore lc k = true) : NoArgRun env lc lc.ctx.f.entry k s0 := by
  have hall := List.all_eq_true.1 h
  have hblk : ∀ b blk, lc.ctx.f.block? b = some blk →
      (∀ e ∈ blk.succs.toList, e.b ≠ lc.ctx.f.entry) ∧
      ∀ i id v, blk.values[i]? = some id → lc.ctx.f.value? id = some v →
        (b = lc.ctx.f.entry ∧ i < k) ∨ v.op ≠ .Arg := by
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
    obtain ⟨hs, hv⟩ := this
    refine ⟨fun e he => by simpa using hs e (by simpa using he), ?_⟩
    intro i id v hi hval
    have hlt' : i < blk.values.size := (Array.getElem?_eq_some_iff.1 hi).1
    have := hv i hlt'
    rw [hi] at this
    simp only [Option.bind_some, hval, Option.all_some, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq, decide_eq_true_eq, bne_iff_ne, ne_eq] at this
    exact this
  intro b i s blk id v hr hb hi hv
  rcases (hblk b blk hb).2 i id v hi hv with ⟨rfl, hik⟩ | h
  · rcases lreach_cases hr with ⟨-, h⟩ | ⟨b', blk', e, hb', he, hbe⟩
    · omega
    · exact absurd hbe ((hblk b' blk' hb').1 e he)
  · exact h

/-- A function with an `Arg` is no `noArg` one. -/
theorem noArg_false {lc : LocCtx} {id : ID} {u : Value} (hu : lc.ctx.f.value? id = some u)
    (hop : u.op = .Arg) : noArg lc = false := by
  refine Bool.eq_false_iff.2 fun hn' => ?_
  have hlt : id < lc.ctx.f.valueTab.size := by
    have hu' : (lc.ctx.f.valueTab[id]?).join = some u := hu
    cases h' : lc.ctx.f.valueTab[id]? with
    | none => rw [h'] at hu'; cases hu'
    | some _ => exact (Array.getElem?_eq_some_iff.1 h').1
  have := List.all_eq_true.1 hn' id (List.mem_range.2 hlt)
  rw [hu] at this
  simp [hop] at this

theorem g46Pre_simple {lc : LocCtx} {v : Value} (h : simpleOp v.op = true) (s : LocState) :
    G46Pre lc s v := by
  simp only [simpleOp, Bool.and_eq_true, bne_iff_ne, ne_eq, Option.isNone_iff_eq_none,
    Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hz⟩, hix⟩,
    -⟩, -⟩, hld⟩, hcmn⟩, hsh⟩, hfs⟩, hfd⟩, hfi⟩, hno⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨fun h => by rcases h with h | h <;> contradiction,
    (fun _ _ _ hl => by rw [h3] at hl; cases hl), fun h => absurd h h5⟩, fun h => absurd h h4⟩,
    fun h => absurd h h6⟩, fun h => absurd h hz⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩,
    fun _ _ _ h2 => absurd (fops46_fp2 h2) hno, fun _ _ _ _ h3 => absurd (fops46_fp3 h3) hno⟩
  · intro as n sh sg hl
    rw [hix] at hl
    cases hl
  · intro as n hl
    rw [hld] at hl
    cases hl
  · intro hop
    rcases hop with hop | hop | hop
    · exact absurd hop hcmn
    all_goals rw [hop] at hsh; cases hsh
  · intro hop
    rcases hop with hop | hop
    · exact absurd hop hfs
    · exact absurd hop hfd
  · intro n sh hl
    rw [hfi] at hl
    cases hl

theorem g51Pre_simple {lc : LocCtx} {v : Value} (h : simpleOp v.op = true) (s : LocState) :
    G51Pre lc s v := by
  refine ⟨⟨g46Pre_simple h s, fun _ _ _ _ hp => ?_⟩, ?_⟩
  · simp only [simpleOp, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    rw [h.1.1.1.1.1.2] at hp
    cases hp
  · simp only [simpleOp, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    refine ⟨fun hop => ?_, fun hop => absurd hop h.1.1.1.1.2⟩
    rcases hop with hop | hop
    · exact absurd hop h.1.1.1.1.2
    · exact absurd hop h.1.1.1.2

theorem g54Pre_simple {lc : LocCtx} {v : Value} (h : simpleOp v.op = true) (s : LocState) :
    G54Pre lc s v := by
  refine ⟨⟨g51Pre_simple h s, fun hop => ?_⟩, fun hop => ?_, fun hop => ?_⟩ <;>
    simp only [simpleOp, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  · exact absurd hop h.1.1.2
  · exact absurd hop h.1.2
  · exact absurd hop h.2

/-- G63's and G64's premises of a simple op: no `LoadReg`, `FMOVQload` or `FLDPQ`. -/
theorem pre64_simple {lc : LocCtx} {v : Value} (h : simpleOp v.op = true) (s : LocState) :
    FReloadPre lc s v ∧ QLoadPre lc s v := by
  have hne : ∀ o, simpleOp o = false → v.op ≠ o := fun _ ho hop => by
    rw [hop, ho] at h
    cases h
  exact ⟨fun hop => absurd hop (hne _ (by decide)), fun hop => absurd hop (hne _ (by decide)),
    fun hop => absurd hop (hne _ (by decide))⟩

/-- **`RunPreM` of a function of simple ops** (`simpleFrom`): every premise is vacuous. -/
theorem runPreM_simple {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ret : BitVec 64} {E0 : MatchEnv} {b0 : ID} {i0 : Nat} {s0 : LocState} {osp : Bool}
    (h : simpleFrom lc.ctx.f b0 i0 = true) : RunPreM osp env H lc g L ret E0 b0 i0 s0 := by
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
      Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_true_eq] at hs'
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, hc⟩, hic⟩, hwb⟩, hcl⟩, hen⟩, -⟩,
      -⟩, hgg⟩, hme⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hs'
    refine ⟨.inl (by simp [entryOp24, hen]), fun s' _ => ⟨⟨g54Pre_simple hs s, pre64_simple hs s⟩,
      fun E m _ _ =>
      ⟨?_, ?_, ?_, ?_, fun h => absurd h hcl, fun h => absurd h hgg, ?_,
        fun _ h => absurd h hc⟩⟩⟩ <;> cases osp
    all_goals first
      | exact fun h => absurd h hc
      | exact fun h => absurd h hwb
      | exact fun h => absurd h hme
      | (intro n _ _ _ _ _ _ _ _ _ hn
         rw [hic] at hn
         cases hn)
  · rcases hk with hk | hk
    · exact absurd hk hz
    · exact absurd hk hnz

/-- **`RunPre` of a function of simple ops** (`simpleFrom`): every premise is vacuous. -/
theorem runPre_simple {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ret : BitVec 64} {E0 : MatchEnv} {b0 : ID} {i0 : Nat} {s0 : LocState}
    (h : simpleFrom lc.ctx.f b0 i0 = true) : RunPre env H lc g L ret E0 b0 i0 s0 :=
  (runPreM_simple h).pre

/-- **`RunPreS` of a function of simple ops** (`simpleFrom`): every premise is vacuous. -/
theorem runPreS_simple {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ret : BitVec 64} {E0 : MatchEnv} {b0 : ID} {i0 : Nat} {s0 : LocState}
    (h : simpleFrom lc.ctx.f b0 i0 = true) : RunPreS env H lc g L ret E0 b0 i0 s0 :=
  (runPreM_simple h).preS

/-! ## The simulation invariant -/

section Sim

variable {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
  {bstart : ID → Option Nat} {tab : PcTab} {kt : KTab} {E0 : MatchEnv} {osp : Bool}
  {spills : Array Spill} {o : ObjIn} {otab : Tab} {base : BitVec 64} {code : Code}
  {retM : BitVec 64}

/-- Before value `i` of block `b` (of `blk`), `runLoc` in `s` and the machine in `t`: a P0 state
`m` `LocMatch`ed to `s` under an activation `E` extending `E0`, in the separation of the mode
`osp` (`G3Inv … osp`), with `SPInv` in a lowered function at the mode `true`, its X registers
meeting G35's
upper-bit table (`UOKL` of `uL35` from the block's start `uIn35`), `ObjRel`-related to `t` with
`X27` where `checkObj` relied on it (`X27At`); in a
leaf (`otab.leaf`), `X30` still the caller's return address `E0.lr`, which is no P0 address; at
a clean position, `s` holds the initial memory (`MemAt`). -/
def SimAt (lc : LocCtx) (g : G2In) (L : Link) (ps : Array Prog) (tab : PcTab) (kt : KTab)
    (E0 : MatchEnv) (osp : Bool) (otab : Tab) (base : BitVec 64) (b : ID) (blk : Block) (i : Nat)
    (s : LocState) (t : MState) : Prop :=
  ∃ E m, E0.Extends E ∧ G49Env lc g L ps (endP L.text ps.toList) tab E ∧ LocMatch E s b i m ∧
    G3Inv E lc (kAt lc kt b blk i) s osp ∧ (osp = true → lc.ctx.f.lowered = true → SPInv E s) ∧
    UOKL m (uL35 lc (uIn35 lc b) blk i) ∧
    ObjRel (ObjEnv.map otab ps L base) m t ∧ X27At otab L ps.toList m t ∧
    b ∈ lc.ctx.f.blocks.toList ∧
    (otab.leaf = true → m.x 30 = E0.lr ∧ ¬ IsProgAddr L.text ps.toList E0.lr ∧
      E0.lr ≠ endP L.text ps.toList) ∧ MemAt lc b blk i s

/-- A step whose P0 run keeps a leaf's `X30` outside the P0 addresses keeps `SimAt`'s leaf
clause. -/
theorem leafLR_keep {otab : Tab} {L : Link} {ps : Array Prog} {E0 : MatchEnv} {m m' : MState}
    (h : otab.leaf = true → m.x 30 = E0.lr ∧ ¬ IsProgAddr L.text ps.toList E0.lr ∧
      E0.lr ≠ endP L.text ps.toList)
    (hk : otab.leaf = true → ¬ IsProgAddr L.text ps.toList (m.x 30) →
      m.x 30 ≠ endP L.text ps.toList → m'.x 30 = m.x 30) :
    otab.leaf = true → m'.x 30 = E0.lr ∧ ¬ IsProgAddr L.text ps.toList E0.lr ∧
      E0.lr ≠ endP L.text ps.toList := fun hl => by
  obtain ⟨h30, h1, h2⟩ := h hl
  refine ⟨(hk hl (by rw [h30]; exact h1) (by rw [h30]; exact h2)).trans h30, h1, h2⟩

/-- One value. -/
theorem sim_value (hc : checkG66L lc ps bstart g = .ok (tab, kt))
    (hO : ObjEnv ps spills o otab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hic : ∀ u, ICallOut L ps.toList u) (hosp : osp = true → E0.outSP = true)
    (hn48 : needs48 lc = true → osp = true)
    {b : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {t : MState}
    (hb : lc.ctx.f.block? b = some blk) (hi : blk.values[i]? = some id)
    (hv : lc.ctx.f.value? id = some v) (hs : stepLoc env lc s v = .ok s')
    (hS : SimAt lc g L ps tab kt E0 osp otab base b blk i s t)
    (hen : entryOp24 v.op = false ∨ (v.op = .InitMem ∧ lc.ctx.f.lowered = true))
    (hpre : G54Pre lc s v ∧ FReloadPre lc s v ∧ QLoadPre lc s v) (hro : RoPre56 g s)
    (hok : ∀ E m, E0.Extends E → LocMatch E s b i m →
      CallOKAt osp H E g L lc s s' v m ∧ CallOKZAt osp H E g L lc s s' v m ∧
        ICallOKAt osp H E L (endP L.text ps.toList) lc s s' v m ∧
        WbOKAt osp H E g L lc s v m ∧ CloOK E s v m ∧ GetGOK E v ∧
        MemEqOKAt osp H E g L lc s v m ∧ (osp = true → CallOKStk H E g L lc s s' v m))
    (hna : v.op ≠ .Arg) :
    ∃ t', MStar H code retM t t' ∧ SimAt lc g L ps tab kt E0 osp otab base b blk (i + 1) s' t' := by
  obtain ⟨E, m, hx, hE, hm, hinv, hsp, hu, hR, hX, hbid, hlr, hma⟩ := hS
  have ho : E.outSP = E0.outSP := hx.outSP
  obtain ⟨hcall, hcallz, hicall, hwb, hclo, hgetg, hmeq, hcallk⟩ := hok E m hx hm
  obtain ⟨E', m', t', hx', hE', hm', hinv', hsp', hu', ht, hR', hX', hk⟩ :=
    g66_obj_value hc hE hbid hb hi hv hen hma hm hinv hsp (fun h => ho.trans (hosp h)) hn48 hu
      hpre.1 hro hcall hcallz hicall hwb hclo hgetg hmeq hcallk (fun hop => absurd hop hna)
      hpre.2.1 hpre.2.2 hs hO hH
      hR hX (fun u _ => hic u)
  exact ⟨t', ht, E', m', MatchEnv.Extends.trans hx hx', hE', hm', hinv', hsp', hu', hR', hX', hbid,
    leafLR_keep hlr hk, fun hl hok hcl => memInit_clean_step hl hi hv (hma hl hok) hs hcl⟩

/-- A terminator that goes to a block. -/
theorem sim_goto (hc : checkG66L lc ps bstart g = .ok (tab, kt))
    (hO : ObjEnv ps spills o otab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hic : ∀ u, ICallOut L ps.toList u)
    {b : ID} {blk blk' : Block} {e : Edge} {s s' : LocState} {t : MState}
    (hb : lc.ctx.f.block? b = some blk) (ht : stepTermLoc lc s blk = .ok (.goto e, s'))
    (hS : SimAt lc g L ps tab kt E0 osp otab base b blk blk.values.size s t)
    (hpre : G1TermPre lc s blk) :
    ∃ t', MStar H code retM t t' ∧ SimAt lc g L ps tab kt E0 osp otab base e.b blk' 0 s' t' := by
  obtain ⟨E, m, hx, hE, hm, hinv, hsp, hu, hR, hX, hbid, hlr, hma⟩ := hS
  obtain ⟨m', t', hm', hinv', hsp', hmem, hu', htm, hR', hX', hk⟩ :=
    g66_obj_term (H := H) hc hE hbid hb hm hinv hsp hpre hu ht hO hH hR hX (fun u _ => hic u)
  obtain ⟨R, -, hn⟩ := stepTermLoc_gen ht
  have he := stepTermL_goto_mem hn
  exact ⟨t', htm, E, m', hx, hE, hm', by rw [kAt_zero]; exact hinv', hsp', hu', hR', hX', hmem,
    leafLR_keep hlr hk, fun hl hok hcl => memInit_clean_term hok hbid hb he (hma hl hok) ht
      (by rwa [cleanAt_zero] at hcl)⟩

/-- The values of a block from value `i` on. -/
theorem sim_values (hc : checkG66L lc ps bstart g = .ok (tab, kt))
    (hO : ObjEnv ps spills o otab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hic : ∀ u, ICallOut L ps.toList u) (hosp : osp = true → E0.outSP = true)
    (hn48 : needs48 lc = true → osp = true)
    {b0 : ID} {i0 : Nat} {s0 : LocState}
    (hP : RunPreM osp env H lc g L (endP L.text ps.toList) E0 b0 i0 s0)
    (hRo : RoRun g env lc b0 i0 s0) (hA : NoArgRun env lc b0 i0 s0)
    {b : ID} {blk : Block} (hb : lc.ctx.f.block? b = some blk) :
    ∀ (n i : Nat) (s s' : LocState) (t : MState), i + n = blk.values.size →
      LReach env lc b0 i0 s0 b i s → SimAt lc g L ps tab kt E0 osp otab base b blk i s t →
      enterListLoc env lc s (blk.values.toList.drop i) = .ok s' →
      LReach env lc b0 i0 s0 b blk.values.size s' ∧
        ∃ t', MStar H code retM t t' ∧
          SimAt lc g L ps tab kt E0 osp otab base b blk blk.values.size s' t'
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
        obtain ⟨hen, hok⟩ := (hP b i s blk hr hb).1 id v hi hv
        obtain ⟨hpre, hok⟩ := hok s1 hs
        obtain ⟨t1, ht1, hS1⟩ :=
          sim_value hc hO hH hic hosp hn48 hb hi hv hs hS hen hpre (hRo b i s hr) hok
          (hA b i s blk id v hr hb hi hv)
        obtain ⟨hr', t', ht', hS'⟩ := sim_values hc hO hH hic hosp hn48 hP hRo hA hb n (i + 1) s1 s' t1
          (by omega)
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
      (∀ k, objV? r = some k → VRel E.ι v (t.v k))
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

/-- `retRegsOK` checks every block of the function. -/
theorem retRegsOK_block {lc : LocCtx} {kt : KTab} (h : retRegsOK lc kt = true) {b : ID}
    {blk : Block} (hbid : b ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? b = some blk) :
    retBlockOK lc kt (ownOutRegs lc) b blk = true := by
  unfold retRegsOK at h
  have := List.all_eq_true.1 h b hbid
  rwa [hb] at this

theorem low_ne {r : Nat} (hr : r < 16) {k : Nat} (hk : 16 ≤ k) (hk' : k < 32) :
    (BitVec.ofNat 5 r : Reg) ≠ BitVec.ofNat 5 k := by
  intro he; have := congrArg BitVec.toNat he; simp at this; omega

/-- What `sim_ret` reads of `checkG66L`'s acceptance, with or without an arm64 op: the blocks'
check (`termG3` terminators) and the Progs' IDs. -/
theorem checkG66L_cx {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} (hc : checkG66L lc ps bstart g = .ok (tab, kt)) :
    ∃ c : Cx2, c.cx.lc = lc ∧ c.cx.ps = ps ∧ c.tm = c.cx.termG3 ∧
      (∀ p ∈ ps.toList, p.id < 2 ^ 32) ∧ (ps.toList.map (·.id)).Nodup ∧
      c.blocks lc.ctx.f.blocks.toList = .ok tab := by
  cases hl : lc.ctx.f.lowered
  · obtain ⟨c, h1, h2, -, -, -, h6, -, -, -, -, h11, h12, h13, -, -⟩ :=
      checkNL30_spec (checkNL30_of_66L hl hc)
    exact ⟨c, h1, h2, h6, h11, h12, h13⟩
  · obtain ⟨c, h1, h2, -, -, -, h6, -, -, -, -, h11, h12, h13, -, -, -, -⟩ := checkG66L_spec hl hc
    exact ⟨c, h1, h2, h6, h11, h12, h13⟩

/-- `checkG66L` accepted: the entry block starts with nothing in the upper-bit table. -/
theorem checkG66L_uIn_entry {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat}
    {g : G2In} {tab : PcTab} {kt : KTab} (hc : checkG66L lc ps bstart g = .ok (tab, kt)) :
    uIn35 lc lc.ctx.f.entry = [] := by
  cases hl : lc.ctx.f.lowered
  · exact uIn35_nl hl _
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, he, -⟩ := checkG66L_spec hl hc
    exact uEdgesOK35_entry he

/-- **The return.** A `Ret` block's terminator, from related states, is matched by the machine
steps of the `RET` and of the epilogue (`obj_exit`) to the caller's return address, with the
results in their ABI registers (`retRegsOK`, `ResultRel`). A frameless function and a leaf return
through `X30`, the caller's return address (`FrameRel`, `SimAt`'s leaf clause); a leaf's frame
pointer is recomputed, the caller's (`R29 = SP - 8` at entry, `EntryEnv.fp0`). -/
theorem sim_ret (hc : checkG66L lc ps bstart g = .ok (tab, kt))
    (hO : ObjEnv ps spills o otab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hic : ∀ u, ICallOut L ps.toList u)
    {s0 : MState} (hEE : EntryEnv E0 L ps.toList otab.autosize s0)
    (hrok : retRegsOK lc kt = true)
    {b : ID} {blk : Block} {s s' : LocState} {rs : List Val} {mm : Mem} {t : MState}
    (hb : lc.ctx.f.block? b = some blk) (ht : stepTermLoc lc s blk = .ok (.ret rs mm, s'))
    (hS : SimAt lc g L ps tab kt E0 osp otab base b blk blk.values.size s t) :
    ∃ E t', E0.Extends E ∧ MStar H code retM t t' ∧ ExitRel E s s0 t' ∧
      ResultRel E (ownOutRegs lc) rs mm t' := by
  obtain ⟨E, m, hx, hE, hm, hinv, -, -, hR, hX, hbid, hlr, -⟩ := hS
  have hEE' := hEE.extend hx
  obtain ⟨R, -, hn⟩ := stepTermLoc_gen ht
  have hk := stepTermL_ret_kind hn
  have hE2 := hE.env.env.env.env.env
  have hinvm := locMatch_inv hE2 hm
  obtain ⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, hfr⟩ := hE2
  obtain ⟨c, hlc, hps, htm, hlt, hnd, hblocks⟩ := checkG66L_cx hc
  have hRes := ret_results hA hm hinv.core (retRegsOK_block hrok hbid hb) hk ht
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
  obtain ⟨t1, ht1, hR1, -⟩ := obj_star hO hH hstar hR hX (by rw [htext]; exact hinvm)
    (fun u _ => hic u)
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
  refine ⟨E, t2, hx, mstar_trans ht1 ht2, ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩, ⟨hRes.len, ?_, ?_⟩⟩
  · -- the return address
    rw [hpc2]
    by_cases h0 : otab.autosize = 0
    · have hfr0 : E.framed = false := by rw [hEE'.framed, h0]; rfl
      rw [ite_eq_left_of_eq_true _ _ (eq_true (Or.inl h0)), hR1.x30]
      show ObjEnv.map otab ps L base (m.x 30) = s0.x 30
      rw [(hm.frame.2.2.2 hfr0).2, hEE'.lr]
      exact objMap_fix hEE'.lrOut.1 hEE'.lrOut.2
    · cases hl : otab.leaf
      · have hfr1 : E.framed = true := by rw [hEE'.framed]; simp [h0]
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by simp [h0, hl])), hsp1, word_rel hR1]
        show m.word E.sp = s0.x 30
        rw [(hm.frame.2.2.1 hfr1).2.1, hEE'.lr]
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (Or.inr rfl)), hR1.x30]
        show ObjEnv.map otab ps L base (m.x 30) = s0.x 30
        rw [(hlr hl).1, hEE.lr]
        exact objMap_fix hEE.lrOut.1 hEE.lrOut.2
  · rw [hsp2, hsp1, hEE'.sp]
  · rw [hx2 28 (by decide) (by decide) (by decide), hx1 28 (by decide) (by decide), hm.frame.2.1,
      hEE'.g]
  · rw [h292]
    by_cases h0 : otab.autosize = 0
    · have hfr0 : E.framed = false := by rw [hEE'.framed, h0]; rfl
      rw [ite_eq_left_of_eq_true _ _ (eq_true h0), hx1 29 (by decide) (by decide), (hm.frame.2.2.2 hfr0).1, hEE'.fp]
    · have hfr1 : E.framed = true := by rw [hEE'.framed]; simp [h0]
      rw [ite_eq_right_of_eq_false _ _ (eq_false h0)]
      cases hl : otab.leaf
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (by decide)), hsp1, word_rel hR1]
        show m.word (E.sp - 8) = s0.x 29
        rw [(hm.frame.2.2.1 hfr1).2.2, hEE'.fp]
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (rfl : true = true)), hsp1, hEE'.fp0, ← hEE'.sp,
          Int.sub_eq_add_neg, BitVec.ofInt_add]
        have h8 : BitVec.ofInt 64 (-8) = -8#64 := by decide
        rw [h8]
        bv_omega
  · intro r v hv
    obtain ⟨hX, hV⟩ := hm.regs r v hv
    refine ⟨fun q hq h29 h30 => ?_, fun q hq => ?_⟩
    · rw [hx2 q (objX?_ne27 hq) h29 h30, hx1 q (objX?_ne27 hq) h30]
      exact hX q hq
    · rw [hv2, hR1.v]
      exact hV q hq
  · obtain ⟨mm', hs, hinj⟩ := hm.mem
    exact ⟨mm', hs, by rw [hm2, hR1.mem]; exact hinj⟩
  · intro j y r hy hr
    rcases hRes.regs j y r hy hr with ⟨h16, hv⟩ | ⟨h31, h47, hv⟩
    · refine .inl ⟨h16, ?_⟩
      rw [hx2 _ (low_ne h16 (by decide) (by decide)) (low_ne h16 (by decide) (by decide))
        (low_ne h16 (by decide) (by decide)), hx1 _ (low_ne h16 (by decide) (by decide))
        (low_ne h16 (by decide) (by decide))]
      exact hv
    · refine .inr ⟨h31, h47, ?_⟩
      rw [hv2, hR1.v]
      exact hv
  · rw [hm2, hR1.mem]
    exact hRes.mem

/-- **A returning run.** From related states before value `i` of block `b`, a run that returns is
matched by a machine run to the caller's return address (`MachRet`) with the results in their
ABI registers (`ResultRel`). -/
theorem sim_from_ret (hc : checkG66L lc ps bstart g = .ok (tab, kt))
    (hO : ObjEnv ps spills o otab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hic : ∀ u, ICallOut L ps.toList u) (hosp : osp = true → E0.outSP = true)
    (hn48 : needs48 lc = true → osp = true)
    {s0 : MState} (hEE : EntryEnv E0 L ps.toList otab.autosize s0)
    (hrok : retRegsOK lc kt = true)
    {b0 : ID} {i0 : Nat} {sI : LocState}
    (hP : RunPreM osp env H lc g L (endP L.text ps.toList) E0 b0 i0 sI)
    (hRo : RoRun g env lc b0 i0 sI) (hA : NoArgRun env lc b0 i0 sI)
    {rs : List Val} {mm : Mem} :
    ∀ (fuel : Nat) (b : ID) (blk : Block) (i : Nat) (s : LocState) (t : MState),
      LReach env lc b0 i0 sI b i s → lc.ctx.f.block? b = some blk → i ≤ blk.values.size →
      SimAt lc g L ps tab kt E0 osp otab base b blk i s t →
      runFromLoc env lc fuel s b i = .returned rs mm →
      ∃ E t', E0.Extends E ∧ MStar H code retM t t' ∧ MachRet s0 t' ∧
        ResultRel E (ownOutRegs lc) rs mm t' := by
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
        sim_values hc hO hH hic hosp hn48 hP hRo hA hb (blk.values.size - i) i s s1 t (by omega) hr
          hS hl
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
          obtain ⟨E, t2, hx, ht2, hX, hRes⟩ := sim_ret hc hO hH hic hEE hrok hb hst hS1
          exact ⟨E, t2, hx, mstar_trans ht1 ht2, hX.ret, hRes⟩
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
               obtain ⟨E, t3, hx, ht3, hX, hRes⟩ :=
                 ih e.b blk2 0 s2 t2 (.term hr1 hb hst) hb2 (Nat.zero_le _) hS2 hrun
               exact ⟨E, t3, hx, mstar_trans ht1 (mstar_trans ht2 ht3), hX, hRes⟩)

/-! ## The entry -/

/-- What the run's first state `s` (before value `k` of the entry block, after the entry values
and the `Arg`s of the incoming stack arguments) holds of the machine state `s0` at the function's
entry: every register its value (the registers the prologue may write, `R16`, `R17`, `R20`,
`R29`, hold none), no flags, its memory injected into a memory `M` that is `s0`'s but for the
bytes `W` (the windows of the register-assigned parameters, `pendWins`, which the entry stores
write: `sim_entryStores`), and the stack clause: every slot is an incoming stack argument's,
which the caller stored (ABI0: `cmd/compile/internal/abi/abiutils.go`, the stack-assigned
parameters from `FixedFrameSize = 8` at their offsets). -/
structure EntryMatch (E : MatchEnv) (g : G2In) (W : BitVec 64 → Prop) (s : LocState)
    (s0 : MState) : Prop where
  regs : ∀ r v, s.regs[r]? = some v →
    (∀ q, objX? r = some q → ((q = 16 ∨ q = 17 ∨ q = 20 ∨ q = 29) → v = .poison) ∧
      ValRel E.ι v (s0.x q)) ∧ (∀ q, objV? r = some q → FValRel v (s0.v q))
  flags : s.flags = .poison
  /-- **The stack clause** (the caller's side of ABI0): every slot of `s` is the home of an
  `Arg` (G62: an incoming stack argument, no code) with a `NAME_PARAM` operand `x+off(FP)`, and
  the caller's bytes at `8 + off` above the entry `SP` hold its value as a spill slot holds a
  value (`SlotRel`), below `2^64` and apart from `g`'s first 32 bytes. -/
  stack : ∀ k v, s.slots.lookup k = some v → ∃ id u off, E.lc.home id = some (.slot k) ∧
    E.lc.ctx.f.value? id = some u ∧ u.op = .Arg ∧ g.slotOp k = some (.PARAM, off) ∧ 0 ≤ off ∧
    SlotRel E.ι (E.lc.slotTy k) v s0.mem (s0.sp + BitVec.ofInt 64 (off + 8)) ∧
    s0.sp.toNat + off.toNat + 8 + (E.lc.slotTy k).size ≤ 2 ^ 64 ∧
    (s0.sp.toNat + off.toNat + 8 + (E.lc.slotTy k).size ≤ (s0.x 28).toNat ∨
      (s0.x 28).toNat + 32 ≤ s0.sp.toNat + off.toNat + 8)
  mem : ∃ mm, s.mem = .mem mm ∧ ∃ M, MemInj E.ι mm M ∧ ∀ y, ¬ W y → M y = s0.mem y

/-- **The stack clause reduces to the condition before G62** (`slots = []`) for a function with
no incoming stack argument (`noArg`, no `Arg`): `EntryMatch` is then G61's entry condition,
field by field. -/
theorem EntryMatch_stack_nil {E : MatchEnv} {g : G2In} {W : BitVec 64 → Prop} {s : LocState}
    {s0 : MState} (hna : noArg E.lc = true) :
    EntryMatch E g W s s0 ↔
      (∀ r v, s.regs[r]? = some v →
        (∀ q, objX? r = some q → ((q = 16 ∨ q = 17 ∨ q = 20 ∨ q = 29) → v = .poison) ∧
          ValRel E.ι v (s0.x q)) ∧ (∀ q, objV? r = some q → FValRel v (s0.v q))) ∧
      s.flags = .poison ∧ s.slots = [] ∧
      (∃ mm, s.mem = .mem mm ∧ ∃ M, MemInj E.ι mm M ∧ ∀ y, ¬ W y → M y = s0.mem y) := by
  constructor
  · intro h
    refine ⟨h.regs, h.flags, ?_, h.mem⟩
    cases hs : s.slots with
    | nil => rfl
    | cons p ps =>
      obtain ⟨id, u, -, -, hu, hop, -⟩ := h.stack p.1 p.2 (by rw [hs]; simp [List.lookup])
      rw [noArg_false hu hop] at hna
      cases hna
  · rintro ⟨hr, hf, hs, hm⟩
    exact ⟨hr, hf, fun k v hk => (by rw [hs] at hk; cases hk), hm⟩

/-- The caller's side of the morestack path (`sim_entry`, a function whose stack check reads
`gOff(g)` and whose morestack tail spills `spills`) for the run's first state `s` and the entry
state `s0`: every register holding a value but `R26` (the closure context, which the tail's call
keeps when `s` holds a value there, `live26`) is reloaded by the tail from a slot the value fits
(`ValFits`; a vector register from a slot of its `F` register, whose value `FValRel` reads in its
low bits only: the hook clobbers the vector registers), and the live blocks of `s`'s memory lie
apart from the slots and the guard word. -/
structure MoreEntry (E : MatchEnv) (spills : List Spill) (gOff : Nat) (s : LocState) (s0 : MState) :
    Prop where
  regs : ∀ r v, s.regs[r]? = some v → v ≠ .poison →
    (∀ q, objX? r = some q → q = 26 ∨ ∀ sl, tailPlan spills = .ok sl →
      ∃ sq, reloadOf sl false q.toNat = some sq ∧ ValFits v sq.n) ∧
    ∀ q, objV? r = some q → ∀ sl, tailPlan spills = .ok sl →
      ∃ sq, reloadOf sl true q.toNat = some sq ∧ ValFits v sq.n
  sep : ∀ mm, s.mem = .mem mm → ∀ sl, tailPlan spills = .ok sl →
    SepFrom E.ι (fun y => InSlots sl s0.sp y ∨ InWord (s0.x 28 + BitVec.ofNat 64 gOff) y) mm

/-- A spill slot's relation reads its bytes only. -/
private theorem slotRel_congr {ι : Blk → Option (BitVec 64)} {t : Ty} {v : Val}
    {mm mm' : Memory} {a : BitVec 64}
    (h : ∀ j, j < t.size → mm' (a + BitVec.ofNat 64 j) = mm (a + BitVec.ofNat 64 j))
    (hr : SlotRel ι t v mm a) : SlotRel ι t v mm' a := by
  unfold SlotRel at hr ⊢
  rwa [readMem_congr t.size a h]

/-- A byte of the caller's stack argument at `8 + off` above `sp` (`EntryMatch.stack`). -/
private theorem argAddr_toNat {sp : BitVec 64} {off : Int} {n j : Nat} (h0 : 0 ≤ off)
    (h : sp.toNat + off.toNat + 8 + n ≤ 2 ^ 64) (hj : j < n) :
    (sp + BitVec.ofInt 64 (off + 8) + BitVec.ofNat 64 j).toNat = sp.toNat + off.toNat + 8 + j := by
  rw [ofInt_nonneg (by omega : (0 : Int) ≤ off + 8)]
  have h8 : (off + 8).toNat = off.toNat + 8 := by omega
  rw [h8]
  have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h64] at h ⊢
  omega

/-- The run's state `s` holds a value (not `poison`) in `R26` (Go register 25, `ctxReg`), the
closure context register: the morestack path must then keep it (`MorestackOK`'s context). -/
def live26 (s : LocState) : Bool :=
  match (s.regs[25]? : Option Val) with
  | some Val.poison => false
  | some _ => true
  | none => false

theorem live26_eq_false {s : LocState} :
    live26 s = false ↔ ∀ v, s.regs[25]? = some v → v = .poison := by
  unfold live26
  cases s.regs[25]? with
  | none => simp
  | some v => cases v <;> simp

/-- `X26` is the X register of Go register 25 alone. -/
theorem objX?_eq_26 {r : Nat} (h : objX? r = some 26) : r = 25 := by
  have h26 : (26 : GoFV.Arm64.Reg).toNat = 26 := rfl
  unfold objX? at h
  split at h
  · have := congrArg BitVec.toNat (Option.some.inj h)
    simp only [BitVec.toNat_ofNat, h26] at this
    omega
  · split at h
    · have := congrArg BitVec.toNat (Option.some.inj h)
      simp only [BitVec.toNat_ofNat, h26] at this
      omega
    · split at h
      · have := congrArg BitVec.toNat (Option.some.inj h)
        simp only [BitVec.toNat_ofNat, h26] at this
        omega
      · cases h

/-! ### `R26` before value `k` of the entry block (`ctxtBefore`) -/

/-- `R26` holds no value. -/
private def Dead26 (s : LocState) : Prop := ∀ v, s.regs[25]? = some v → v = .poison

private theorem dead26_setReg {s : LocState} {r : Nat} {x : Val} (h : Dead26 s)
    (hx : r = 25 → x = .poison) : Dead26 (s.setReg r x) := by
  intro v hv
  simp only [LocState.setReg] at hv
  split at hv
  · change (s.regs.setIfInBounds r x)[25]? = some v at hv
    rw [Array.getElem?_setIfInBounds] at hv
    split at hv
    · rename_i hr
      split at hv
      · cases hv; exact hx hr
      · cases hv
    · exact h v hv
  · exact h v hv

private theorem regs25_setReg {s : LocState} {r : Nat} {x : Val} (hr : r ≠ 25) :
    (s.setReg r x).regs[25]? = s.regs[25]? := by
  simp only [LocState.setReg]
  split
  · exact Array.getElem?_setIfInBounds_ne hr
  · rfl

private theorem regs25_writeParts : ∀ (s : LocState) (ts : List Ty) (xs : List Val)
    (rs : List (Option Nat)), (∀ r ∈ rs, r ≠ some 25) →
    (s.writeParts ts xs rs).regs[25]? = s.regs[25]?
  | s, t :: ts, x :: xs, rs, h => by
    unfold LocState.writeParts
    split
    · exact regs25_writeParts _ ts xs rs h
    · split
      · exact regs25_writeParts _ ts xs rs h
      · split
        · rename_i r rs'
          rw [regs25_writeParts _ ts xs _ (fun q hq => h q (List.mem_cons_of_mem _ hq)),
            regs25_setReg (fun e => h (some r) List.mem_cons_self (by rw [e]))]
        · exact regs25_writeParts _ ts xs _ (fun q hq => h q (List.mem_cons_of_mem _ hq))
        · exact regs25_writeParts _ ts xs _ (fun _ hq => by cases hq)
  | s, [], _, _, _ => by simp [LocState.writeParts]
  | s, _ :: _, [], _, _ => by simp [LocState.writeParts]

private theorem regs25_write {lc : LocCtx} {s : LocState} {id : ID} {x : Val}
    (h : (lc.home id).any (fun h => h.regList.contains (some 25)) = false) :
    (s.write lc id x).regs[25]? = s.regs[25]? := by
  unfold LocState.write
  dsimp only
  split
  · rfl
  · apply regs25_writeParts
    intro r hr he
    subst he
    cases hh : lc.home id with
    | none => simp [hh] at hr
    | some l => simp_all
  · rename_i r _ _
    apply regs25_setReg
    intro e
    subst e
    simp_all [GoFV.SSA.Location.regList]
  · rfl
  · split <;> rfl

private theorem dead26_clobberMask {s : LocState} {m : RegMask} (h : Dead26 s) :
    Dead26 (s.clobberMask m) := by
  unfold LocState.clobberMask
  split
  · exact h
  · intro v hv
    simp only [Array.getElem?_mapIdx] at hv
    cases h25 : s.regs[25]? with
    | none => rw [h25] at hv; cases hv
    | some w =>
      rw [h25] at hv
      simp only [Option.map_some] at hv
      split at hv
      · injection hv with hv; exact hv.symm
      · injection hv with hv; subst hv; exact h _ h25

private theorem dead26_clobber {lc : LocCtx} {s : LocState} {v : Value} (h : Dead26 s) :
    Dead26 (s.clobber lc v) := by
  unfold LocState.clobber
  have h1 := dead26_clobberMask (m := v.op.regInfo.clobbers) h
  have harg : ∀ (b : Bool) (i : Nat) (s : LocState), Dead26 s → Dead26 (if !b then s else
      match v.args[i]?.bind lc.regOf with
      | some r => s.setReg r .poison
      | none => s) := by
    intro b i s hs
    split
    · exact hs
    · split
      · exact dead26_setReg hs fun _ => rfl
      · exact hs
  have h2 := harg v.op.regInfo.clobbersArg0 0 _ (harg v.op.regInfo.clobbersArg1 1 _ h1)
  have h3 : ∀ (s : LocState), Dead26 s → Dead26 (match (lc.temps[v.id]?).join with
      | some r => s.setReg r .poison
      | none => s) := by
    intro s hs
    split
    · exact dead26_setReg hs fun _ => rfl
    · exact hs
  have h4 := h3 _ h2
  dsimp only
  split
  · exact fun w hw => h4 w hw
  · exact h4

private theorem wh_res_bind_ok {α β : Type} {x : Res α} {k : α → Res β} {y : β}
    (h : (x >>= k) = .ok y) : ∃ a, x = .ok a ∧ k a = .ok y := by
  cases x with
  | ok a => exact ⟨a, rfl, h⟩
  | panic e m => cases h
  | stuck msg => cases h

private theorem dead26_stepLoc {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}
    (hs : stepLoc env lc s v = .ok s')
    (hh : (lc.home v.id).any (fun h => h.regList.contains (some 25)) = false) (h : Dead26 s) :
    Dead26 s' := by
  unfold stepLoc at hs
  split at hs
  · split at hs
    · cases hs; exact h
    · cases hs
  · obtain ⟨argv, -, hs⟩ := wh_res_bind_ok hs
    dsimp only at hs
    split at hs <;> obtain ⟨r, -, hs⟩ := wh_res_bind_ok hs <;> cases hs <;>
      exact fun w hw => dead26_clobber h w ((regs25_write hh).symm.trans hw)

private theorem dead26_enter {env : Env} {lc : LocCtx} :
    ∀ {s s' : LocState} {l : List ID}, enterListLoc env lc s l = .ok s' →
      (∀ id ∈ l, ∀ v, lc.ctx.f.value? id = some v →
        (lc.home v.id).any (fun h => h.regList.contains (some 25)) = false) →
      Dead26 s → Dead26 s'
  | s, s', [], h, _, hd => by cases h; exact hd
  | s, s', id :: ids, h, hh, hd => by
    simp only [enterListLoc] at h
    split at h
    · cases h
    · rename_i v hv
      split at h
      · rename_i s1 hs1
        exact dead26_enter h (fun j hj => hh j (List.mem_cons_of_mem _ hj))
          (dead26_stepLoc hs1 (hh id List.mem_cons_self v hv) hd)
      · cases h
      · cases h

/-- **`R26` after the first values of the entry block.** From a state whose `R26` holds no value,
the state after the first `k` values of the entry block holds a value in `R26` only if one of
them writes it (`ctxtBefore`): a step writes a register of its value's home or `poison`. -/
theorem ctxtBefore_of_live26_from {env : Env} {lc : LocCtx} {s : LocState} {blk : Block}
    {k : Nat} {sI : LocState} (hs : live26 s = false)
    (hb : lc.ctx.f.block? lc.ctx.f.entry = some blk)
    (hpre : enterListLoc env lc s (blk.values.toList.take k) = .ok sI)
    (hl : live26 sI = true) : ctxtBefore lc k = true := by
  cases hc : ctxtBefore lc k
  · exfalso
    have hd : Dead26 sI := by
      refine dead26_enter hpre (fun id hid v hv => ?_) (live26_eq_false.1 hs)
      simp only [ctxtBefore, hb, List.any_eq_false] at hc
      have := hc id hid
      simp only [hv, Option.any_some, Bool.not_eq_true] at this
      exact this
    rw [live26_eq_false.2 hd] at hl
    cases hl
  · rfl

/-- `locInit`'s registers are `poison`. -/
theorem live26_locInit (env : Env) (lc : LocCtx) (args : List Val) (mem : Mem) :
    live26 (locInit env lc args mem) = false := by
  refine live26_eq_false.2 fun w hw => ?_
  simp only [locInit, Array.getElem?_replicate] at hw
  split at hw
  · cases hw; rfl
  · cases hw

/-- **`R26` at the entry state** (`ctxtBefore_of_live26_from` from `locInit`): the run's state
after the first `k` values of the entry block holds a value in `R26` only if one of them writes
it. -/
theorem ctxtBefore_of_live26 {env : Env} {lc : LocCtx} {args : List Val} {mem : Mem}
    {blk : Block} {k : Nat} {sI : LocState} (hb : lc.ctx.f.block? lc.ctx.f.entry = some blk)
    (hpre : enterListLoc env lc (locInit env lc args mem) (blk.values.toList.take k) = .ok sI)
    (hl : live26 sI = true) : ctxtBefore lc k = true :=
  ctxtBefore_of_live26_from (live26_locInit env lc args mem) hb hpre hl

/-- `EntryMatch` survives the morestack path: a function with a slot at the entry (an `Arg`) has
no morestack spill slot (`argsOK`), the caller's stack arguments lie apart from the guard word,
among `g`'s first 32 bytes (`gOff` 16 or 24), and `R26` survives where `s` holds a value in it
(`live26`: the tail's call then has a context; a `poison` there relates to anything). -/
theorem EntryMatch.more {E : MatchEnv} {g : G2In} {W : BitVec 64 → Prop} {spills : List Spill}
    {gOff : Nat} {sl : List TailSlot} {s : LocState} {s0 s0' : MState} (h : EntryMatch E g W s s0)
    (hm : MoreEntry E spills gOff s s0) (hpl : tailPlan spills = .ok sl)
    (hst : MoreStep (live26 s) sl gOff s0 s0') (hsl : ∀ k v, s.slots.lookup k = some v → sl = [])
    (hgo : gOff ≤ 24) (hg : (s0.x 28).toNat + 32 ≤ 2 ^ 64) : EntryMatch E g W s s0' := by
  obtain ⟨-, hslot⟩ := tailPlan_spec hpl
  refine ⟨fun r v hv => ?_, h.flags, ?_, ?_⟩
  · obtain ⟨hX, hV⟩ := h.regs r v hv
    by_cases hp : v = .poison
    · subst hp
      exact ⟨fun q hq => ⟨(hX q hq).1, trivial⟩, fun q hq => trivial⟩
    obtain ⟨hmX, hmV⟩ := hm.regs r v hv hp
    refine ⟨fun q hq => ⟨(hX q hq).1, ?_⟩, fun q hq => ?_⟩
    · rcases hmX q hq with rfl | hfit
      · have hr := objX?_eq_26 hq
        subst hr
        have hl : live26 s = true := by
          cases hl : live26 s
          · exact absurd (live26_eq_false.1 hl v hv) hp
          · rfl
        rw [hst.x26 hl]
        exact (hX 26 hq).2
      · obtain ⟨sq, hsq, hf⟩ := hfit sl hpl
        have hn := hslot sq (reloadOf_mem hsq).1
        rcases hst.regs q sq hsq with e | e
        · rw [e]
          exact (hX q hq).2
        · rw [e]
          exact valRel_reloadVal sq.sg hn.2.1 hn.2.2.1 (hX q hq).2 hf
    · obtain ⟨sq, hsq, hf⟩ := hmV q hq sl hpl
      have hn := hslot sq (reloadOf_mem hsq).1
      rcases hst.vregs q sq hsq with e | e
      · rw [e]
        exact hV q hq
      · rw [e]
        exact fvalRel_vreloadVal hn.2.2.1 (hV q hq) hf
  · intro k v hk
    obtain ⟨id, u, off, hh, hu, hop, hso, h0, hrel, hbnd, hsg⟩ := h.stack k v hk
    have hsl0 : sl = [] := hsl k v hk
    refine ⟨id, u, off, hh, hu, hop, hso, h0, ?_, by rw [hst.sp]; exact hbnd,
      by rw [hst.sp, hst.x28]; exact hsg⟩
    rw [hst.sp]
    refine slotRel_congr (fun j hj => ?_) hrel
    have ha := argAddr_toNat (sp := s0.sp) h0 hbnd hj
    refine hst.mem _ (fun ⟨q, hq, _⟩ => by rw [hsl0] at hq; cases hq) fun hw => ?_
    have hgg : (s0.x 28 + BitVec.ofNat 64 gOff).toNat = (s0.x 28).toNat + gOff := by
      have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
      rw [h64] at hg
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h64]
      omega
    unfold InWord at hw
    rw [ha, hgg] at hw
    omega
  · classical
    obtain ⟨mm, hmm, M, hinj, hag⟩ := h.mem
    refine ⟨mm, hmm, fun y => if W y then M y else s0'.mem y,
      memInj_congr hinj fun b al a hb ha i hi => ?_, fun y hy => by simp only [hy, ↓reduceIte]⟩
    by_cases hw : W (a + BitVec.ofNat 64 i)
    · simp only [hw, ↓reduceIte]
    simp only [hw, ↓reduceIte]
    rw [hag _ hw]
    obtain ⟨a', ha', -, hwin⟩ := hinj.mapped b al hb
    rw [ha] at ha'
    cases ha'
    have hy : (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
      have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
      rw [h64] at hwin
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, h64]
      omega
    have hsep := hm.sep mm hmm sl hpl b al a hb ha (a + BitVec.ofNat 64 i)
    rw [hy] at hsep
    exact hst.mem _ (fun hin => hsep (Or.inl hin) ⟨by omega, by omega⟩)
      (fun hin => hsep (Or.inr hin) ⟨by omega, by omega⟩)

/-- `EntryEnv` survives the morestack path. -/
theorem EntryEnv.more {E : MatchEnv} {L : Link} {ps : List Prog} {az : Int}
    {ctxt : Bool} {check : Option (Nat × Nat × Nat)} {spills : List Spill} {s0 s0' : MState}
    (h : EntryEnv E L ps az s0) (hm : MoreRel ctxt check spills s0 s0') :
    EntryEnv E L ps az s0' := by
  obtain ⟨-, hsp, -, h28, h29, h30⟩ := hm.keep
  exact ⟨by rw [hsp]; exact h.sp, by rw [h28]; exact h.g, by rw [h30]; exact h.lr,
    by rw [h29]; exact h.fp, by rw [h29, hsp]; exact h.fp0, h.framed, by rw [h30]; exact h.lrOut⟩

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

/-- `SimAt` with the P0 state's memory relaxed: the P0 state `m` is `LocMatch`ed to `s` with
its memory replaced by `M`, which agrees with `m.mem` outside the bytes `W` (the windows the
entry stores still have to write). -/
def SimAtW (lc : LocCtx) (g : G2In) (L : Link) (ps : Array Prog) (tab : PcTab) (kt : KTab)
    (E0 : MatchEnv) (osp : Bool) (otab : Tab) (base : BitVec 64) (W : BitVec 64 → Prop) (b : ID)
    (blk : Block) (i : Nat) (s : LocState) (t : MState) : Prop :=
  ∃ E m M, E0.Extends E ∧ G49Env lc g L ps (endP L.text ps.toList) tab E ∧
    LocMatch E s b i { m with mem := M } ∧ (∀ y, ¬ W y → M y = m.mem y) ∧
    G3Inv E lc (kAt lc kt b blk i) s osp ∧ (osp = true → lc.ctx.f.lowered = true → SPInv E s) ∧
    UOKL m (uL35 lc (uIn35 lc b) blk i) ∧
    ObjRel (ObjEnv.map otab ps L base) m t ∧ X27At otab L ps.toList m t ∧
    b ∈ lc.ctx.f.blocks.toList ∧
    (otab.leaf = true → m.x 30 = E0.lr ∧ ¬ IsProgAddr L.text ps.toList E0.lr ∧
      E0.lr ≠ endP L.text ps.toList) ∧ MemAt lc b blk i s

theorem SimAtW.mono {W W' : BitVec 64 → Prop} (h : ∀ y, W y → W' y) {b : ID} {blk : Block}
    {i : Nat} {s : LocState} {t : MState}
    (hS : SimAtW lc g L ps tab kt E0 osp otab base W b blk i s t) :
    SimAtW lc g L ps tab kt E0 osp otab base W' b blk i s t := by
  obtain ⟨E, m, M, hx, hE, hm, hag, rest⟩ := hS
  exact ⟨E, m, M, hx, hE, hm, fun y hy => hag y fun hw => hy (h y hw), rest⟩

/-- With no byte left out, `SimAtW` is `SimAt`. -/
theorem SimAtW.simAt {W : BitVec 64 → Prop} (h : ∀ y, ¬ W y) {b : ID} {blk : Block}
    {i : Nat} {s : LocState} {t : MState}
    (hS : SimAtW lc g L ps tab kt E0 osp otab base W b blk i s t) :
    SimAt lc g L ps tab kt E0 osp otab base b blk i s t := by
  obtain ⟨E, m, M, hx, hE, hm, hag, rest⟩ := hS
  have hM : M = m.mem := funext fun y => hag y (h y)
  subst hM
  exact ⟨E, m, hx, hE, hm, rest⟩

/-- The guard word a stack check reads is at `16(g)` or `24(g)` (`checkPrologue`). -/
theorem checkObj_gOff {ps : Array Prog} {spills : Array Spill} {o : ObjIn} {tab : Tab}
    {ce tail gOff : Nat} (hc : checkObj ps spills o = .ok tab)
    (hck : tab.check = some (ce, tail, gOff)) : gOff = 16 ∨ gOff = 24 := by
  obtain ⟨-, body, -, -, -, -, -, -, -, -, -, hpro, -, -⟩ := checkObj_spec hc
  rcases checkPrologue_spec hpro with ⟨-, -, h⟩ | ⟨-, fo, σ, hchk, -⟩
  · rw [h] at hck; cases hck
  · rcases hchk with ⟨h, -⟩ | ⟨ce', tail', gOff', h, -, hgo, -⟩
    · rw [h] at hck; cases hck
    · rw [h] at hck
      cases hck
      exact hgo

/-- **The entry.** From the machine state `s0` at the function's entry (`MachEntry`), the prologue
(`obj_entry`: the stack check, looping through the morestack tail under `MorestackOK` and
`TailSep` until it passes, then the frame) runs to a state related (`SimAtW`, but for the bytes
`W` `EntryMatch` leaves out) to the run's first state `sI` before value `k` of block `b`, whose
P0 address maps to the body's start; on the morestack path `sI`'s values survive the tail
(`MoreEntry`). The relaxed memory is `s0`'s relaxed one on `W`, but for the saved `LR`/`FP`
words, which are the machine's. -/
theorem sim_entry (hO : ObjEnv ps spills o otab L base code retM)
    {room : Nat} {s0 : MState} (hME : MachEntry code base room s0)
    (hroom : otab.autosize + 8 ≤ room) (hg : (s0.x 28).toNat + 32 ≤ 2 ^ 64)
    {W : BitVec 64 → Prop} {sI : LocState} {b : ID} {blk : Block} {k : Nat}
    (hms : ∀ ce tail gOff, otab.check = some (ce, tail, gOff) → ∀ n add,
      tailCall o.text o.relocs.toList tail = some (n, add) →
      MorestackOK H code retM (L.sym n + BitVec.ofInt 64 add) otab.autosize gOff (live26 sI) s0)
    (hsep : ∀ ce tail gOff, otab.check = some (ce, tail, gOff) → TailSep spills.toList s0)
    (hE : G49Env lc g L ps (endP L.text ps.toList) tab E0)
    (hEE : EntryEnv E0 L ps.toList otab.autosize s0)
    (hent : EntryMatch E0 g W sI s0)
    (hstk : ∀ k v, sI.slots.lookup k = some v → (∀ y, ¬ W y) ∧ spills = #[])
    (hmore : ∀ ce tail gOff, otab.check = some (ce, tail, gOff) →
      MoreEntry E0 spills.toList gOff sI s0)
    (hinv : G3Inv E0 lc (kAt lc kt b blk k) sI osp)
    (hspI : osp = true → lc.ctx.f.lowered = true → SPInv E0 sI)
    (huE : uL35 lc (uIn35 lc b) blk k = [])
    (hbm : b ∈ lc.ctx.f.blocks.toList) (hma : MemAt lc b blk k sI)
    (hpc : ObjEnv.map otab ps L base (E0.pcOf b k) = base + BitVec.ofNat 64 (otab.offs[0]!)) :
    ∃ t, MStar H code retM s0 t ∧ SimAtW lc g L ps tab kt E0 osp otab base W b blk k sI t := by
  classical
  obtain ⟨s0', s1, hmr, h1, hbody, hpc1, hx1, hv1, hm1⟩ :=
    obj_entry (H := H) hO.check hO.linked hO.size hO.ret hME hroom hg hms hsep
  replace hent : EntryMatch E0 g W sI s0' := by
    rcases hmr with rfl | ⟨ce, tail, gOff, sl, hck, hpl, hst⟩
    · exact hent
    · refine hent.more (hmore ce tail gOff hck) hpl hst (fun k v hk => ?_)
        (by rcases checkObj_gOff hO.check hck with h | h <;> omega) hg
      have h0 : tailPlan (#[] : Array Spill).toList = .ok [] := rfl
      rw [(hstk k v hk).2, h0] at hpl
      exact (Except.ok.inj hpl).symm
  replace hEE := hEE.more hmr
  have haz := wh_az_nonneg hO.check
  have hfr := hE.env.env.env.env.env.frame
  have hsp0 : E0.sp = s0'.sp - BitVec.ofInt 64 otab.autosize := by
    rw [← hEE.sp, BitVec.add_sub_cancel]
  have h30 : s1.x 30 = s0'.x 30 := hx1 30 (by decide) (by decide) (by decide) (by decide)
    (by decide)
  obtain ⟨mm, hmm, M, hinj, hag⟩ := hent.mem
  -- the relaxed memory: `M` on the bytes of `W` (outside the saved words in a framed function),
  -- else the machine's
  let M1 : Memory := fun y =>
    if W y ∧ (otab.autosize = 0 ∨ 16 ≤ (y - (s1.sp - 8)).toNat) then M y else s1.mem y
  have hM1 : ∀ y, ¬ W y → M1 y = s1.mem y := fun y hy => by simp only [M1, hy, false_and,
    ↓reduceIte]
  -- the slots: the incoming stack arguments, which the caller stored (`EntryMatch.stack`), at
  -- their frame operands, above the saved words and outside `W`
  have hlaz : L.autosize = otab.autosize := (congrArg Link.autosize hO.link).trans rfl
  have hslots : ∀ k v, sI.slots.lookup k = some v → ∃ o, E0.slot k = some o ∧
      SlotRel E0.ι (E0.lc.slotTy k) v M1 (E0.sp + BitVec.ofInt 64 o) := by
    intro k v hk
    obtain ⟨hW, -⟩ := hstk k v hk
    obtain ⟨id, u, off, hh, -, -, hso, h0, hrel, hbnd, -⟩ := hent.stack k v hk
    rw [hE.env.env.env.env.env.lcEq] at hh
    refine ⟨frameOff L .PARAM off,
      hE.env.env.env.env.env.slot k (mem_homeSlots hh) .PARAM off hso, ?_⟩
    have haddr : E0.sp + BitVec.ofInt 64 (frameOff L .PARAM off) =
        s0'.sp + BitVec.ofInt 64 (off + 8) := by
      rw [hsp0, frameOff, hlaz, show otab.autosize + off + 8 = otab.autosize + (off + 8) by omega,
        BitVec.ofInt_add, ← BitVec.add_assoc, BitVec.sub_add_cancel]
    rw [haddr]
    refine slotRel_congr (fun j hj => ?_) hrel
    rw [hM1 _ (hW _)]
    by_cases h0z : otab.autosize = 0
    · simp only [h0z, ↓reduceIte] at hbody
      rw [hbody]
    · simp only [h0z, ↓reduceIte] at hbody
      refine hm1 _ ?_
      have ha := argAddr_toNat (sp := s0'.sp) h0 hbnd hj
      have hs0 : 4096 + otab.autosize.toNat + 8 ≤ s0'.sp.toNat := by
        have := hME.room
        rw [hmr.keep.2.1]
        omega
      rw [hbody.sp]
      have h64 : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
      have h8 : (8 : BitVec 64).toNat = 8 := rfl
      rw [h64] at hbnd
      simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, h64, h8, ha]
      omega
  refine ⟨s1, h1, E0, { s1 with pc := E0.pcOf b k }, M1, ⟨rfl, fun _ _ h => h⟩, hE, ?_, hM1,
    hinv, hspI, (by rw [huE]; intro _ he; cases he),
    ⟨fun _ _ _ => rfl, ?_, rfl, rfl, rfl, rfl, by rw [hpc1, ← hpc]⟩,
    x27At_of_eq hO rfl (pcOf_inv hE.env.env.env.env.env b k), hbm,
    fun _ => ⟨by show s1.x 30 = E0.lr; rw [h30, hEE.lr], by rw [hEE.lr]; exact hEE.lrOut.1,
      by rw [hEE.lr]; exact hEE.lrOut.2⟩, hma⟩
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
      exact ⟨fun q hq => (hX q hq).2, fun q hq => VRel.of_fval (hV q hq)⟩
    · rw [hent.flags]; trivial
    · exact hslots
    · refine ⟨mm, hmm, memInj_congr hinj fun bk al a hb ha i hi => ?_⟩
      show M1 _ = M _
      by_cases hw : W (a + BitVec.ofNat 64 i)
      · simp only [M1, hw, h0, true_or, and_self, ↓reduceIte]
      · simp only [M1, hw, false_and, ↓reduceIte]
        exact (hag _ hw).symm
    · show s1.sp = E0.sp
      rw [hsp0, h0]; simp
    · exact hEE.g.symm
    · rw [hfr0] at h; cases h
    · exact ⟨hEE.fp.symm, hEE.lr.symm⟩
  · simp only [h0, ↓reduceIte] at hbody
    have hfr1 : E0.framed = true := by rw [hEE.framed]; simp [h0]
    have hsp1 : s1.sp = E0.sp := by
      rw [hbody.sp, hsp0, ofInt_nonneg haz]
    have hw16 : ∀ y, (y - (s1.sp - 8)).toNat < 16 → M1 y = s1.mem y := fun y hy => by
      simp only [M1, h0, show ¬ 16 ≤ (y - (s1.sp - 8)).toNat by omega, or_self, and_false,
        ↓reduceIte]
    have hword : ∀ a, (∀ j, j < 8 → (a + BitVec.ofNat 64 j - (s1.sp - 8)).toNat < 16) →
        ({ { s1 with pc := E0.pcOf b k } with mem := M1 } : MState).word a = s1.word a :=
      fun a ha => by
        simp only [MState.word]
        rw [readMem_congr 8 a fun j hj => hw16 _ (ha j hj)]
    refine ⟨fun r v hv => ?_, ?_, ?_, ?_, ⟨hsp1, ?_, fun _ => ⟨?_, ?_, ?_⟩, fun h => ?_⟩, rfl⟩
    · obtain ⟨hX, hV⟩ := hent.regs r v hv
      refine ⟨fun q hq => ?_, fun q hq => ?_⟩
      · by_cases hq' : q = 16 ∨ q = 17 ∨ q = 20 ∨ q = 29
        · rw [(hX q hq).1 hq']; trivial
        · simp only [not_or] at hq'
          show ValRel E0.ι v (s1.x q)
          rw [hx1 q hq'.1 hq'.2.1 hq'.2.2.1 (objX?_ne27 hq) hq'.2.2.2]
          exact (hX q hq).2
      · show VRel E0.ι v (s1.v q)
        rw [hv1]; exact VRel.of_fval (hV q hq)
    · rw [hent.flags]; trivial
    · exact hslots
    · -- `M1` is `M` but for the saved words, which are in `StkAt E0`: the live blocks' bytes
      -- there are `poison` (`SepAt` of either mode, `SepFromW`)
      obtain ⟨mm', hmm', -, hsep⟩ := hinv.core.mem
      rw [hmm] at hmm'
      cases hmm'
      refine ⟨mm, hmm, memInj_of_sepW hinj hsep.sepW fun y hy => ?_⟩
      have h16 : 16 ≤ (y - (s1.sp - 8)).toNat := by
        refine Nat.le_of_not_lt fun hlt => hy (Or.inl ⟨hfr1, ?_⟩)
        rw [hsp1] at hlt
        exact stk_window hfr.lo hfr.hi hlt
      show M1 _ = M _
      by_cases hw : W y
      · simp only [M1, hw, h16, or_true, and_self, ↓reduceIte]
      · simp only [M1, hw, false_and, ↓reduceIte]
        rw [hm1 _ h16, hag _ hw]
    · show s1.x 28 = E0.g
      rw [hbody.g, hEE.g]
    · show s1.x 29 = E0.sp - 8
      rw [hbody.r29, hsp1]
    · rw [hword _ fun j hj => by rw [hsp1]; bv_omega]
      show s1.word E0.sp = E0.lr
      rw [← hsp1, hbody.lr, hEE.lr]
    · rw [hword _ fun j hj => by rw [hsp1]; bv_omega]
      show s1.word (E0.sp - 8) = E0.fp
      rw [← hsp1, hbody.fp, hEE.fp]
    · rw [hfr1] at h; cases h

/-- The run from value `i` continues from value `i + 1` after a value that steps. -/
theorem runFromLoc_val {env : Env} {lc : LocCtx} {fuel : Nat} {s s1 : LocState} {b : ID}
    {blk : Block} {i : Nat} {id : ID} {ids : List ID} {v : Value}
    (hb : lc.ctx.f.block? b = some blk) (hd : blk.values.toList.drop i = id :: ids)
    (hv : lc.ctx.f.value? id = some v) (hs : stepLoc env lc s v = .ok s1) :
    runFromLoc env lc fuel s b i = runFromLoc env lc fuel s1 b (i + 1) := by
  have hd' : blk.values.toList.drop (i + 1) = ids := by
    have := congrArg (List.drop 1) hd
    simpa [List.drop_drop, Nat.add_comm] using this
  simp only [runFromLoc, hb, hd, hd', enterListLoc, hv, hs]

/-- **One entry store** (`entryStore?`) from `SimAtW` with its window and `W` to `SimAtW` with
`W` (`g66L_entryStore`, `obj_star`). -/
theorem sim_entryStore (hc : checkG66L lc ps bstart g = .ok (tab, kt))
    (hO : ObjEnv ps spills o otab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hic : ∀ u, ICallOut L ps.toList u)
    {b : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {t : MState}
    {w : Int × Nat} {W : BitVec 64 → Prop}
    (hb : lc.ctx.f.block? b = some blk) (hi : blk.values[i]? = some id)
    (hv : lc.ctx.f.value? id = some v) (hes : entryStore? lc g v = some w)
    (hs : stepLoc env lc s v = .ok s')
    (hS : SimAtW lc g L ps tab kt E0 osp otab base (fun y => (∃ j, j < w.2 ∧
      y = E0.sp + BitVec.ofInt 64 (frameOff L .PARAM w.1) + BitVec.ofNat 64 j) ∨ W y)
      b blk i s t) :
    ∃ t', MStar H code retM t t' ∧
      SimAtW lc g L ps tab kt E0 osp otab base W b blk (i + 1) s' t' := by
  obtain ⟨E, m, M, hx, hE, hm, hag, hinv, hspI, -, hR, hX, hbid, hlr, hma⟩ := hS
  have hsp : E.sp = E0.sp := by rw [hx.1]
  have hspI' : osp = true → lc.ctx.f.lowered = true → SPInv E s' := fun ho hl => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hsh, -⟩ := checkG66L_spec hl hc
    exact spInv_step hE.env.env.env.env.env.addr ⟨rfl, fun _ _ h => h⟩
      hE.env.env.env.env.env.lcEq (fun _ => ⟨hl, spHomes48_spec hsh⟩) hv (hspI ho hl) hs
  obtain ⟨m', M', hp, hxm, hm', hinv', hu', hag'⟩ := g66L_entryStore (H := H) hc hE hbid hb hi hv
    hes hm (W := W) (fun y hy hw => hag y fun h => h.elim
      (fun ⟨j, hj, he⟩ => hw j hj (by rw [hsp]; exact he)) hy) hinv hs
  have hI0 := locMatch_inv hE.env.env.env.env.env hm
  have hI : ObjInv L ps.toList m ∨ m.pc = endP L.text ps.toList := hI0
  obtain ⟨t', ht, hR', -, hX'⟩ := obj_star hO hH hp hR hX hI (fun u _ => hic u)
  exact ⟨t', ht, E, m', M', hx, hE, hm', hag', hinv', hspI', hu', hR', hX', hbid,
    fun hl => ⟨(congrFun hxm 30).trans (hlr hl).1, (hlr hl).2⟩,
    fun hl hok hcl => memInit_clean_step hl hi hv (hma hl hok) hs hcl⟩

/-- **One value the entry stores come after** (`entrySkip`) from `SimAtW` with `W` to `SimAtW`
with `W` (`g66L_entrySkip`, `obj_star`). -/
theorem sim_entrySkip (hc : checkG66L lc ps bstart g = .ok (tab, kt))
    (hO : ObjEnv ps spills o otab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hic : ∀ u, ICallOut L ps.toList u)
    {b : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {t : MState}
    {W : BitVec 64 → Prop}
    (hb : lc.ctx.f.block? b = some blk) (hi : blk.values[i]? = some id)
    (hv : lc.ctx.f.value? id = some v) (hsk : entrySkip lc v = true)
    (hs : stepLoc env lc s v = .ok s')
    (hS : SimAtW lc g L ps tab kt E0 osp otab base W b blk i s t) :
    ∃ t', MStar H code retM t t' ∧
      SimAtW lc g L ps tab kt E0 osp otab base W b blk (i + 1) s' t' := by
  obtain ⟨E, m, M, hx, hE, hm, hag, hinv, hspI, hu, hR, hX, hbid, hlr, hma⟩ := hS
  have hspI' : osp = true → lc.ctx.f.lowered = true → SPInv E s' := fun ho hl => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hsh, -⟩ := checkG66L_spec hl hc
    exact spInv_step hE.env.env.env.env.env.addr ⟨rfl, fun _ _ h => h⟩
      hE.env.env.env.env.env.lcEq (fun _ => ⟨hl, spHomes48_spec hsh⟩) hv (hspI ho hl) hs
  obtain ⟨m', M', hp, hxm, hm', hinv', hu', hag'⟩ := g66L_entrySkip (H := H) hc hE hbid hb hi hv
    hsk hm hag hinv hu hma hs
  have hI0 := locMatch_inv hE.env.env.env.env.env hm
  have hI : ObjInv L ps.toList m ∨ m.pc = endP L.text ps.toList := hI0
  obtain ⟨t', ht, hR', -, hX'⟩ := obj_star hO hH hp hR hX hI (fun u _ => hic u)
  exact ⟨t', ht, E, m', M', hx, hE, hm', hag', hinv', hspI', hu', hR', hX', hbid,
    fun hl => ⟨(congrFun hxm 30).trans (hlr hl).1, (hlr hl).2⟩,
    fun hl hok hcl => memInit_clean_step hl hi hv (hma hl hok) hs hcl⟩

/-- **The entry stores.** From `SimAtW` with the windows of the entry stores at the head of the
rest `ids` of block `b` from value `i` (past the values `entrySkip` takes), a run that is defined
runs them and the skipped values (none panics: an entry store has a symbol,
`stepLoc_mem_panic_aux`; a skipped value is a spill or has no code,
`stepLoc_entrySkip_ne_panic`) to a state related by `SimAt`, from which the run continues
alike. -/
theorem sim_entryStores (hc : checkG66L lc ps bstart g = .ok (tab, kt))
    (hO : ObjEnv ps spills o otab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hic : ∀ u, ICallOut L ps.toList u)
    {b0 : ID} {i0 : Nat} {sI : LocState} {b : ID} {blk : Block}
    (hb : lc.ctx.f.block? b = some blk) {fuel : Nat} :
    ∀ (ids : List ID) (i : Nat) (s : LocState) (t : MState), blk.values.toList.drop i = ids →
      i ≤ blk.values.size → LReach env lc b0 i0 sI b i s →
      SimAtW lc g L ps tab kt E0 osp otab base (InWins L E0.sp (storesFrom lc g ids)) b blk i s t →
      (runFromLoc env lc fuel s b i).Defined →
      ∃ i' s' t', LReach env lc b0 i0 sI b i' s' ∧ i' ≤ blk.values.size ∧
        MStar H code retM t t' ∧ SimAt lc g L ps tab kt E0 osp otab base b blk i' s' t' ∧
        runFromLoc env lc fuel s' b i' = runFromLoc env lc fuel s b i
  | [], i, s, t, _, hi, hr, hS, _ =>
    ⟨i, s, t, hr, hi, .refl, hS.simAt fun _ => inWins_nil, rfl⟩
  | id :: ids, i, s, t, hd, hi, hr, hS, hdef => by
    have hidx : blk.values[i]? = some id := by
      have := congrArg List.head? hd
      simpa using this
    have hlt : i < blk.values.size := (Array.getElem?_eq_some_iff.1 hidx).1
    have hd1 : blk.values.toList.drop (i + 1) = ids := by
      have := congrArg (List.drop 1) hd
      simpa [List.drop_drop, Nat.add_comm] using this
    -- a value that does not panic and steps to a state related with the rest's windows
    have step : ∀ v, lc.ctx.f.value? id = some v → (∀ e mm, stepLoc env lc s v ≠ .panic e mm) →
        (∀ s1, stepLoc env lc s v = .ok s1 → ∃ t1, MStar H code retM t t1 ∧
          SimAtW lc g L ps tab kt E0 osp otab base (InWins L E0.sp (storesFrom lc g ids)) b blk
            (i + 1) s1 t1) →
        ∃ i' s' t', LReach env lc b0 i0 sI b i' s' ∧ i' ≤ blk.values.size ∧
          MStar H code retM t t' ∧ SimAt lc g L ps tab kt E0 osp otab base b blk i' s' t' ∧
          runFromLoc env lc fuel s' b i' = runFromLoc env lc fuel s b i := fun v hv hnp hone => by
      cases hst : stepLoc env lc s v with
      | ok s1 =>
        obtain ⟨t1, ht1, hS1⟩ := hone s1 hst
        have hrun := runFromLoc_val (fuel := fuel) hb hd hv hst
        obtain ⟨i', s', t', hr', hi', ht', hS', hrun'⟩ := sim_entryStores hc hO hH hic hb ids
          (i + 1) s1 t1 hd1 (by omega) (.val hr hb hidx hv hst) hS1 (hrun ▸ hdef)
        exact ⟨i', s', t', hr', hi', mstar_trans ht1 ht', hS', hrun'.trans hrun.symm⟩
      | panic e mm => exact absurd hst (hnp e mm)
      | stuck msg =>
        exfalso
        simp only [runFromLoc, hb, hd, enterListLoc, hv, hst] at hdef
        exact hdef
    cases hw : (lc.ctx.f.value? id).bind (entryStore? lc g) with
    | some w =>
      obtain ⟨v, hv, hes⟩ := Option.bind_eq_some_iff.1 hw
      have hsf : storesFrom lc g (id :: ids) = w :: storesFrom lc g ids := by
        simp only [storesFrom, hw]
      rw [hsf] at hS
      exact step v hv
        (fun e mm hst => absurd (stepLoc_mem_panic_aux (entryStore?_memFault hes) hst)
          (entryStore?_aux hes))
        fun s1 hst => sim_entryStore hc hO hH hic hb hidx hv hes hst
          (hS.mono fun y hy => inWins_cons.1 hy)
    | none =>
      cases hk : (lc.ctx.f.value? id).any (entrySkip lc) with
      | false =>
        have hsf : storesFrom lc g (id :: ids) = [] := by simp [storesFrom, hw, hk]
        rw [hsf] at hS
        exact ⟨i, s, t, hr, hi, .refl, hS.simAt fun _ => inWins_nil, rfl⟩
      | true =>
        obtain ⟨v, hv, hsk⟩ : ∃ v, lc.ctx.f.value? id = some v ∧ entrySkip lc v = true := by
          cases hv : lc.ctx.f.value? id with
          | none => rw [hv] at hk; cases hk
          | some v => rw [hv] at hk; exact ⟨v, rfl, hk⟩
        have hsf : storesFrom lc g (id :: ids) = storesFrom lc g ids := by
          simp [storesFrom, hw, hk]
        rw [hsf] at hS
        exact step v hv (fun e mm => stepLoc_entrySkip_ne_panic hsk) fun s1 hst =>
          sim_entrySkip hc hO hH hic hb hidx hv hsk hst hS

/-- The entry stores from value `k` of the entry block (`entryStores`) are those at the head of
its values from `k` (`storesFrom`). -/
theorem entryStores_entry {lc : LocCtx} {g : G2In} {k : Nat} {blkE : Block}
    (hbE : lc.ctx.f.block? lc.ctx.f.entry = some blkE) :
    entryStores lc g k = storesFrom lc g (blkE.values.toList.drop k) := by
  simp only [entryStores, hbE]

/-- What `argsOK` gives the entry: no `Arg` runs from `(entry, k)`, and a slot at the entry (an
`Arg`'s, `EntryMatch.stack`) comes with no pending window and no morestack spill. -/
theorem argsOK_entry {k : Nat} {sI : LocState} {s0 : MState}
    (h : argsOK lc g spills.toList k = true) (hlc : E0.lc = lc)
    (hent : EntryMatch E0 g (InWins L E0.sp (pendWins lc g)) sI s0) :
    NoArgRun env lc lc.ctx.f.entry k sI ∧ ∀ k' v, sI.slots.lookup k' = some v →
      (∀ y, ¬ InWins L E0.sp (pendWins lc g) y) ∧ spills = #[] := by
  simp only [argsOK, Bool.and_eq_true] at h
  refine ⟨noArgRun_of_argsBefore h.1, fun k' v hk => ?_⟩
  obtain ⟨id, u, -, -, hu, hop, -⟩ := hent.stack k' v hk
  rw [hlc] at hu
  have h2 := h.2
  rw [noArg_false hu hop, Bool.false_or, Bool.and_eq_true, List.isEmpty_iff,
    List.isEmpty_iff] at h2
  obtain ⟨hpw, hsp⟩ := h2
  refine ⟨fun y hy => ?_, Array.toList_eq_nil_iff.1 hsp⟩
  rw [hpw] at hy
  exact inWins_nil hy

/-! ## Whole functions -/

/-- A run of the machine that reaches the return address returns. -/
theorem mstar_returned {s0 t : MState} (h : MStar H code retM s0 t) (hpc : t.pc = retM) :
    ∃ n, runMach H code retM n s0 = .returned t := by
  obtain ⟨n, hn⟩ := h.runMach
  exact ⟨n + 1, by rw [hn 1]; simp [runMach, hpc]⟩

/-- **A whole function of slice G66, returning, down to the machine words.** `checkG66L` and
`checkObj` accept the function and `retRegsOK` its returns; the machine starts at its entry
(`MachEntry`, the return address `s0.x 30`); a stack check that fails loops through the
morestack tail (`runtime.morestack`'s contract `MorestackOK`, the slots apart from `g`,
`TailSep`, and `sI`'s values surviving the tail, `MoreEntry`). The run of `runLoc`
(`runLoopLoc`, from the state `s` at the entry block) first runs `k` values of the entry block
(the entry values) to `sI`, which is related to `s0` (`EntryMatch`, `EntryEnv`: the arguments in
their registers, the memory injected but for the windows of the register-assigned parameters the
function accesses, `pendWins`, the frame; no upper-bit fact is carried into the body:
G35's table after the entry values, from the entry block's empty start, is empty,
`uL35 lc [] … k = []`); the entry stores from value `k` cover those windows (`entryStoresOK`,
checked), so after them the memory is related in full (`sim_entryStores`); every later step meets
its premises (`RunPre`) and every state it reaches has the float constant symbols (`RoRun`). If
it returns `(rs, mm)`,
`runMach` returns to `s0.x 30` with the caller's `SP`, `g` and frame pointer (`MachRet s0`), the
results `rs` in the function's ABI result registers (`ownOutRegs`; a result on the stack is in
its `PPARAMOUT` variable in `mm`) and the memory `mm` injected (`ResultRel`). -/
theorem obj_whole_ret (hc : checkG66L lc ps bstart g = .ok (tab, kt))
    {room : Nat} {s0 : MState} (hO : ObjEnv ps spills o otab L base code (s0.x 30))
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hic : ∀ u, ICallOut L ps.toList u)
    (hrok : retRegsOK lc kt = true)
    (hME : MachEntry code base room s0) (hroom : otab.autosize + 8 ≤ room)
    (hg : (s0.x 28).toNat + 32 ≤ 2 ^ 64)
    {s sI : LocState} {blkE : Block} {k : Nat}
    (hms : ∀ ce tail gOff, otab.check = some (ce, tail, gOff) → ∀ n add,
      tailCall o.text o.relocs.toList tail = some (n, add) →
      MorestackOK H code (s0.x 30) (L.sym n + BitVec.ofInt 64 add) otab.autosize gOff (live26 sI)
        s0)
    (hsep : ∀ ce tail gOff, otab.check = some (ce, tail, gOff) → TailSep spills.toList s0)
    (hE : G49Env lc g L ps (endP L.text ps.toList) tab E0)
    (hEE : EntryEnv E0 L ps.toList otab.autosize s0)
    (hbE : lc.ctx.f.block? lc.ctx.f.entry = some blkE)
    (hbm : lc.ctx.f.entry ∈ lc.ctx.f.blocks.toList) (hk : k ≤ blkE.values.size)
    (hMs : MemInit s)
    (hpre : enterListLoc env lc s (blkE.values.toList.take k) = .ok sI)
    (hes : entryStoresOK lc g k = true) (hargs : argsOK lc g spills.toList k = true)
    (hent : EntryMatch E0 g (InWins L E0.sp (pendWins lc g)) sI s0)
    (hmore : ∀ ce tail gOff, otab.check = some (ce, tail, gOff) →
      MoreEntry E0 spills.toList gOff sI s0)
    (hinv : G3Inv E0 lc (kAt lc kt lc.ctx.f.entry blkE k) sI osp)
    (hosp : osp = true → E0.outSP = true)
    (hn48 : needs48 lc = true → osp = true)
    (hspI : osp = true → lc.ctx.f.lowered = true → SPInv E0 sI)
    (huE : uL35 lc [] blkE k = [])
    (hpc : ObjEnv.map otab ps L base (E0.pcOf lc.ctx.f.entry k) =
      base + BitVec.ofNat 64 (otab.offs[0]!))
    (hP : RunPreM osp env H lc g L (endP L.text ps.toList) E0 lc.ctx.f.entry k sI)
    (hRo : RoRun g env lc lc.ctx.f.entry k sI)
    {fuel : Nat} {rs : List Val} {mm : Mem}
    (hrun : runLoopLoc env lc fuel s lc.ctx.f.entry = .returned rs mm) :
    ∃ E t' n, E0.Extends E ∧ runMach H code (s0.x 30) n s0 = .returned t' ∧ MachRet s0 t' ∧
      ResultRel E (ownOutRegs lc) rs mm t' := by
  cases fuel with
  | zero => simp [runLoopLoc] at hrun
  | succ n =>
    rw [runLoopLoc_entry hbE hpre] at hrun
    obtain ⟨hA, hstk⟩ := argsOK_entry (env := env) hargs hE.env.env.env.env.env.lcEq hent
    obtain ⟨t1, ht1, hS⟩ := sim_entry (H := H) hO hME hroom hg hms hsep hE hEE hent hstk hmore hinv
      hspI (by rw [checkG66L_uIn_entry hc]; exact huE) hbm (memAt_enter hMs hpre) hpc
    obtain ⟨i', s', t2, hr', hi', ht2, hS', hrun'⟩ :=
      sim_entryStores hc hO hH hic hbE (fuel := n) _ k sI t1 rfl hk .refl
        (hS.mono fun y hy => by
          have := entryStoresOK_cover hes L E0.sp hy
          rwa [entryStores_entry hbE] at this)
        (by rw [hrun]; trivial)
    obtain ⟨E, t', hx, ht', hX, hRes⟩ :=
      sim_from_ret hc hO hH hic hosp hn48 hEE hrok hP hRo hA n _ blkE
      i' s' t2 hr' hbE hi' hS' (hrun'.trans hrun)
    obtain ⟨n', hn'⟩ := mstar_returned (mstar_trans ht1 (mstar_trans ht2 ht')) hX.pc
    exact ⟨E, t', n', hx, hn', hX, hRes⟩

/-! ## Panics -/

/-- **The panic premise of the run** at every state it reaches from `(b0, i0, s0)`: a value
whose step panics is a nil check, a load or store that faults in the nil page (`memFaultOp`: no
premise, the machine's access faults too), an acquire load that faults in the nil page (`ldar?`:
no premise), an atomic of G61's group A that faults in the nil page (`atom61?`: no premise), a
bounds check (the runtime's bounds panic is the trusted `BoundsOK`, a premise of the whole run), a
static call whose callee panics as the trusted contract `CallPanicOK` says, or an interface or
closure call whose callee panics as the trusted `ICallPanicOK` says (P0's return address `ret`),
at every `LocMatch`ed machine state of an activation extending `E0`. -/
def RunPanicPre (env : Env) (H : Hooks) (lc : LocCtx) (g : G2In) (L : Link) (ret : BitVec 64)
    (E0 : MatchEnv) (b0 : ID) (i0 : Nat) (s0 : LocState) : Prop :=
  ∀ b i s blk, LReach env lc b0 i0 s0 b i s → lc.ctx.f.block? b = some blk →
    ∀ id v e mm, blk.values[i]? = some id → lc.ctx.f.value? id = some v →
      stepLoc env lc s v = .panic e mm →
      v.op = .ARM64LoweredNilCheck ∨ memFaultOp v.op = true ∨ (ldar? v.op).isSome = true ∨
        (atom61? v.op).isSome = true ∨
        pbOp v.op = true ∨
        (v.op = .ARM64CALLstatic ∧ ∀ E m, E0.Extends E → LocMatch E s b i m →
          CallPanicOK H E g L lc s v m e) ∨
        ((icallLead v.op).isSome = true ∧ ∀ E m, E0.Extends E → LocMatch E s b i m →
          ICallPanicOK H E L ret lc s v m e)

/-- **`RunPanicPre` in G48's mode**: the callee contracts `CallPanicOKS` and `ICallPanicOKS`
(`SepFromW`; a static call's registers by `callRegsZ` or `callRegsS`). -/
def RunPanicPreS (env : Env) (H : Hooks) (lc : LocCtx) (g : G2In) (L : Link) (ret : BitVec 64)
    (E0 : MatchEnv) (b0 : ID) (i0 : Nat) (s0 : LocState) : Prop :=
  ∀ b i s blk, LReach env lc b0 i0 s0 b i s → lc.ctx.f.block? b = some blk →
    ∀ id v e mm, blk.values[i]? = some id → lc.ctx.f.value? id = some v →
      stepLoc env lc s v = .panic e mm →
      v.op = .ARM64LoweredNilCheck ∨ memFaultOp v.op = true ∨ (ldar? v.op).isSome = true ∨
        (atom61? v.op).isSome = true ∨
        pbOp v.op = true ∨
        (v.op = .ARM64CALLstatic ∧ ∀ E m, E0.Extends E → LocMatch E s b i m →
          CallPanicOKS H E g L lc s v m e) ∨
        ((icallLead v.op).isSome = true ∧ ∀ E m, E0.Extends E → LocMatch E s b i m →
          ICallPanicOKS H E L ret lc s v m e)

/-- `RunPanicPre` (`osp = false`) or `RunPanicPreS` (`osp = true`) in one form. -/
def RunPanicPreM (osp : Bool) (env : Env) (H : Hooks) (lc : LocCtx) (g : G2In) (L : Link)
    (ret : BitVec 64) (E0 : MatchEnv) (b0 : ID) (i0 : Nat) (s0 : LocState) : Prop :=
  ∀ b i s blk, LReach env lc b0 i0 s0 b i s → lc.ctx.f.block? b = some blk →
    ∀ id v e mm, blk.values[i]? = some id → lc.ctx.f.value? id = some v →
      stepLoc env lc s v = .panic e mm →
      v.op = .ARM64LoweredNilCheck ∨ memFaultOp v.op = true ∨ (ldar? v.op).isSome = true ∨
        (atom61? v.op).isSome = true ∨
        pbOp v.op = true ∨
        (v.op = .ARM64CALLstatic ∧ ∀ E m, E0.Extends E → LocMatch E s b i m →
          CallPanicOKAt osp H E g L lc s v m e) ∨
        ((icallLead v.op).isSome = true ∧ ∀ E m, E0.Extends E → LocMatch E s b i m →
          ICallPanicOKAt osp H E L ret lc s v m e)

theorem RunPanicPre.m {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ret : BitVec 64} {E0 : MatchEnv} {b0 : ID} {i0 : Nat} {s0 : LocState}
    (h : RunPanicPre env H lc g L ret E0 b0 i0 s0) :
    RunPanicPreM false env H lc g L ret E0 b0 i0 s0 := h

theorem RunPanicPreS.m {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ret : BitVec 64} {E0 : MatchEnv} {b0 : ID} {i0 : Nat} {s0 : LocState}
    (h : RunPanicPreS env H lc g L ret E0 b0 i0 s0) :
    RunPanicPreM true env H lc g L ret E0 b0 i0 s0 := h

theorem mapM_loop_ne_panic {α β : Type} {f : α → Res β} (hf : ∀ a e m, f a ≠ .panic e m) :
    ∀ (l : List α) (acc : List β) e m, List.mapM.loop f l acc ≠ .panic e m
  | [], acc, e, m => by simp [List.mapM.loop, pure]
  | a :: l, acc, e, m => by
    simp only [List.mapM.loop]
    cases h : f a with
    | ok x => simp only [bind, Res.bind]; exact mapM_loop_ne_panic hf l (x :: acc) e m
    | panic e' m' => exact absurd h (hf a e' m')
    | stuck msg => simp [bind, Res.bind]

/-- `LocState.control` does not panic. -/
theorem control_noPanic {lc : LocCtx} {s : LocState} {c : ID} {e : Panic} {m : Mem} :
    s.control lc c ≠ .panic e m := by
  have hm : ∀ (l : List ID) e' m', l.mapM (s.read lc) ≠ .panic e' m' := fun l e' m' => by
    unfold List.mapM
    exact mapM_loop_ne_panic (fun _ _ _ => read_noPanic) l [] e' m'
  unfold LocState.control
  split
  · rename_i v _
    split
    · cases h : v.args.toList.mapM (s.read lc) with
      | ok xs => simp [bind, Res.bind, pure]
      | panic e' m' => exact absurd h (hm _ e' m')
      | stuck msg => simp [bind, Res.bind]
    · exact read_noPanic
  · nofun

theorem forIn_res_ne_panic {α β : Type} {f : α → β → Res (ForInStep β)}
    (hf : ∀ a b e m, f a b ≠ .panic e m) :
    ∀ (l : List α) (b : β) e m, forIn l b f ≠ .panic e m
  | [], b, e, m => by simp [pure]
  | a :: l, b, e, m => by
    rw [List.forIn_cons]
    cases h : f a b with
    | ok r =>
      cases r with
      | done b' => simp [bind, Res.bind, pure]
      | yield b' => simp only [bind, Res.bind]; exact forIn_res_ne_panic hf l b' e m
    | panic e' m' => exact absurd h (hf a b e' m')
    | stuck msg => simp [bind, Res.bind]

/-- A terminator does not panic under `runLoc`. -/
theorem stepTermLoc_ne_panic {lc : LocCtx} {s : LocState} {blk : Block} {e : Panic} {m : Mem} :
    stepTermLoc lc s blk ≠ .panic e m := by
  intro h
  unfold stepTermLoc at h
  dsimp only at h
  rw [← Array.forIn_toList] at h
  simp only [bind, Res.bind] at h
  split at h
  · dsimp only at h
    split at h
    · cases h
    · rename_i hn
      exact GoFV.Proof.Dead.stepTermL_not_panic hn
    · cases h
  · rename_i hf
    refine forIn_res_ne_panic (fun c regs e' m' hc => ?_) _ _ _ _ hf
    split at hc
    · cases hc
    · rename_i hx
      exact control_noPanic hx
    · cases hc
  · cases h

/-- One value whose step panics: a nil check, a load, store, acquire load or atomic that faults, a
bounds check, or a static, interface or closure call whose callee panics, matched by machine steps
to a state that panics alike (`BoundsAgree`: the same panic, or for a bounds check the runtime's
report of the same failure). -/
theorem sim_valuePanic (hc : checkG66L lc ps bstart g = .ok (tab, kt))
    (hO : ObjEnv ps spills o otab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hHP : HookPanicMap H L ps.toList (ObjEnv.map otab ps L base))
    (hbok : BoundsOK H g L ps.toList)
    (hic : ∀ u, ICallOut L ps.toList u) (hosp : osp = true → E0.outSP = true)
    (hn48 : needs48 lc = true → osp = true)
    {b : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState} {e : Panic} {mm : Mem}
    {t : MState} (hb : lc.ctx.f.block? b = some blk) (hi : blk.values[i]? = some id)
    (hv : lc.ctx.f.value? id = some v) (hs : stepLoc env lc s v = .panic e mm)
    (hS : SimAt lc g L ps tab kt E0 osp otab base b blk i s t)
    (hpp : v.op = .ARM64LoweredNilCheck ∨ memFaultOp v.op = true ∨ (ldar? v.op).isSome = true ∨
      (atom61? v.op).isSome = true ∨
      pbOp v.op = true ∨
      (v.op = .ARM64CALLstatic ∧ ∀ E m, E0.Extends E → LocMatch E s b i m →
        CallPanicOKAt osp H E g L lc s v m e) ∨
      ((icallLead v.op).isSome = true ∧ ∀ E m, E0.Extends E → LocMatch E s b i m →
        ICallPanicOKAt osp H E L (endP L.text ps.toList) lc s v m e)) :
    ∃ e', BoundsAgree e e' ∧ ∃ t', MStar H code retM t t' ∧ MPanics H code retM t' e' := by
  obtain ⟨E, m, hx, hE, hm, hinv, hsp, -, hR, hX, hbid, -, -⟩ := hS
  have ho : E.outSP = E0.outSP := hx.outSP
  rcases hpp with hop | hop | hop | hop | hop | ⟨hop, hok⟩ | ⟨hop, hok⟩
  · obtain ⟨-, t', ht, hp⟩ := g66_obj_nilPanic hc hE hbid hb hi hv hop hm hinv hs hO hH hHP hR hX
      (fun u _ => hic u)
    exact ⟨e, Or.inl rfl, t', ht, hp⟩
  · obtain ⟨-, t', ht, hp⟩ := g66_obj_memPanic hc hE.env hbid hb hi hv hop hm hinv
      (fun hl h => have ho' := hn48 (take48_of_needs48 hl hv h); ⟨hsp ho' hl, ho.trans (hosp ho')⟩)
      hs hO hH hHP hR hX (fun u _ => hic u)
    exact ⟨e, Or.inl rfl, t', ht, hp⟩
  · obtain ⟨-, t', ht, hp⟩ := g66_obj_ldarPanic hc hE.env hbid hb hi hv hop hm hinv hs hO hH hHP
      hR hX (fun u _ => hic u)
    exact ⟨e, Or.inl rfl, t', ht, hp⟩
  · obtain ⟨-, t', ht, hp⟩ := g66_obj_atomPanic hc hE.env hbid hb hi hv hop hm hinv hs hO hH hHP
      hR hX (fun u _ => hic u)
    exact ⟨e, Or.inl rfl, t', ht, hp⟩
  · exact g66_obj_boundsPanic hc hE hbid hb hi hv hop hm hinv hbok hs hO hH hHP hR hX
      (fun u _ => hic u)
  · exact ⟨e, Or.inl rfl, g66_obj_callPanic hc hE.env hbid hb hi hv hop hm hinv (hok E m hx hm)
      hn48 hO hH hHP hR hX (fun u _ => hic u)⟩
  · obtain ⟨n, hn⟩ := Option.isSome_iff_exists.1 hop
    exact ⟨e, Or.inl rfl, g66_obj_icallPanic hc hE.env hbid hb hi hv hn hm hinv (hok E m hx hm) hO
      hH hHP hR hX (fun u _ => hic u)⟩

/-- The values of a block from value `i` on, which panic. -/
theorem sim_valuesPanic (hc : checkG66L lc ps bstart g = .ok (tab, kt))
    (hO : ObjEnv ps spills o otab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hHP : HookPanicMap H L ps.toList (ObjEnv.map otab ps L base))
    (hbok : BoundsOK H g L ps.toList)
    (hic : ∀ u, ICallOut L ps.toList u) (hosp : osp = true → E0.outSP = true)
    (hn48 : needs48 lc = true → osp = true)
    {b0 : ID} {i0 : Nat} {s0 : LocState}
    (hP : RunPreM osp env H lc g L (endP L.text ps.toList) E0 b0 i0 s0)
    (hRo : RoRun g env lc b0 i0 s0) (hA : NoArgRun env lc b0 i0 s0)
    (hPP : RunPanicPreM osp env H lc g L (endP L.text ps.toList) E0 b0 i0 s0) {e : Panic} {mm : Mem}
    {b : ID} {blk : Block} (hb : lc.ctx.f.block? b = some blk) :
    ∀ (n i : Nat) (s : LocState) (t : MState), i + n = blk.values.size →
      LReach env lc b0 i0 s0 b i s → SimAt lc g L ps tab kt E0 osp otab base b blk i s t →
      enterListLoc env lc s (blk.values.toList.drop i) = .panic e mm →
      ∃ e', BoundsAgree e e' ∧ ∃ t', MStar H code retM t t' ∧ MPanics H code retM t' e'
  | 0, i, s, t, hn, hr, hS, hl => by
    have hd : blk.values.toList.drop i = [] := List.drop_eq_nil_of_le (by simp; omega)
    rw [hd] at hl
    cases hl
  | n + 1, i, s, t, hn, hr, hS, hl => by
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
      | panic e' mm' =>
        rw [hs] at hl
        cases hl
        exact sim_valuePanic hc hO hH hHP hbok hic hosp hn48 hb hi hv hs hS
          (hPP b i s blk hr hb id v _ _ hi hv hs)
      | stuck msg => rw [hs] at hl; cases hl
      | ok s1 =>
        rw [hs] at hl
        obtain ⟨hen, hok⟩ := (hP b i s blk hr hb).1 id v hi hv
        obtain ⟨hpre, hok⟩ := hok s1 hs
        obtain ⟨t1, ht1, hS1⟩ :=
          sim_value hc hO hH hic hosp hn48 hb hi hv hs hS hen hpre (hRo b i s hr) hok
          (hA b i s blk id v hr hb hi hv)
        obtain ⟨e', he, t', ht', hp⟩ :=
          sim_valuesPanic hc hO hH hHP hbok hic hosp hn48 hP hRo hA hPP hb n
          (i + 1)
          s1 t1 (by omega) (.val hr hb hi hv hs) hS1 hl
        exact ⟨e', he, t', mstar_trans ht1 ht', hp⟩

/-- **A panicking run.** From related states before value `i` of block `b`, a run that panics
with `e` is matched by a machine run to a state that panics with a panic `BoundsAgree`ing with
`e` (`MPanics`). -/
theorem sim_from_panic (hc : checkG66L lc ps bstart g = .ok (tab, kt))
    (hO : ObjEnv ps spills o otab L base code retM)
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hHP : HookPanicMap H L ps.toList (ObjEnv.map otab ps L base))
    (hbok : BoundsOK H g L ps.toList)
    (hic : ∀ u, ICallOut L ps.toList u) (hosp : osp = true → E0.outSP = true)
    (hn48 : needs48 lc = true → osp = true)
    {b0 : ID} {i0 : Nat} {sI : LocState}
    (hP : RunPreM osp env H lc g L (endP L.text ps.toList) E0 b0 i0 sI)
    (hRo : RoRun g env lc b0 i0 sI) (hA : NoArgRun env lc b0 i0 sI)
    (hPP : RunPanicPreM osp env H lc g L (endP L.text ps.toList) E0 b0 i0 sI)
    {e : Panic} {mm : Mem} :
    ∀ (fuel : Nat) (b : ID) (blk : Block) (i : Nat) (s : LocState) (t : MState),
      LReach env lc b0 i0 sI b i s → lc.ctx.f.block? b = some blk → i ≤ blk.values.size →
      SimAt lc g L ps tab kt E0 osp otab base b blk i s t →
      runFromLoc env lc fuel s b i = .panicked e mm →
      ∃ e', BoundsAgree e e' ∧ ∃ t', MStar H code retM t t' ∧ MPanics H code retM t' e' := by
  intro fuel
  induction fuel with
  | zero => ?_
  | succ n ih => ?_
  all_goals
    intro b blk i s t hr hb hi hS hrun
    simp only [runFromLoc, hb] at hrun
    cases hl : enterListLoc env lc s (blk.values.toList.drop i) with
    | panic e' mm' =>
      rw [hl] at hrun
      simp only [Outcome.panicked.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      exact sim_valuesPanic hc hO hH hHP hbok hic hosp hn48 hP hRo hA hPP hb (blk.values.size - i) i
        s t
        (by omega)
        hr hS hl
    | stuck msg => rw [hl] at hrun; cases hrun
    | ok s1 =>
      rw [hl] at hrun
      simp only at hrun
      obtain ⟨hr1, t1, ht1, hS1⟩ :=
        sim_values hc hO hH hic hosp hn48 hP hRo hA hb (blk.values.size - i) i s s1 t (by omega) hr
          hS hl
      cases hst : stepTermLoc lc s1 blk with
      | panic e' mm' => exact absurd hst stepTermLoc_ne_panic
      | stuck msg => rw [hst] at hrun; cases hrun
      | ok r =>
        obtain ⟨nx, s2⟩ := r
        rw [hst] at hrun
        cases nx with
        | ret rs' mm' => cases hrun
        | goto e2 =>
          simp only at hrun
          first
          | (simp [runLoopLoc] at hrun; done)
          | (rw [runLoopLoc_succ] at hrun
             cases hb2 : lc.ctx.f.block? e2.b with
             | none => simp [runFromLoc, hb2] at hrun
             | some blk2 =>
               have hpre := ((hP b blk.values.size s1 blk hr1 hb).2 rfl)
               obtain ⟨t2, ht2, hS2⟩ := sim_goto (blk' := blk2) hc hO hH hic hb hst hS1 hpre
               obtain ⟨e', he, t3, ht3, hp⟩ :=
                 ih e2.b blk2 0 s2 t2 (.term hr1 hb hst) hb2 (Nat.zero_le _) hS2 hrun
               exact ⟨e', he, t3, mstar_trans ht1 (mstar_trans ht2 ht3), hp⟩)

/-- A run of the machine to a state that panics panics. -/
theorem mstar_panicked {s0 t : MState} {e : Panic} (h : MStar H code retM s0 t)
    (hp : MPanics H code retM t e) : ∃ n t', runMach H code retM n s0 = .panicked e t' := by
  obtain ⟨n, hn⟩ := h.runMach
  obtain ⟨t', ht'⟩ := hp.runMach 0
  exact ⟨n + 1, t', by rw [hn 1, ht']⟩

/-- **A whole function of slice G66, panicking, down to the machine words.** `obj_whole_ret`'s
premises on the entry and the steps (`RunPre`, `RoRun`), the trusted `HookPanicMap` and `BoundsOK`, and
the panic premise `RunPanicPre` (the run's panics come from nil checks, loads, stores, acquire
loads and atomics that fault in the nil page, bounds checks and static, interface or closure calls
whose callee
panics, `CallPanicOK`, `ICallPanicOK`): if the run of `runLoc` panics with `e`, `runMach` panics
with `e` (the nil-page fault of the nil check's `MOVB` or of the access, `sigpanic`; or the
callee's hook) or, for a bounds check, with the runtime's report of the same failure
(`BoundsAgree`). -/
theorem obj_whole_panic (hc : checkG66L lc ps bstart g = .ok (tab, kt))
    {room : Nat} {s0 : MState} (hO : ObjEnv ps spills o otab L base code (s0.x 30))
    (hH : HookMap H L ps.toList (ObjEnv.map otab ps L base))
    (hHP : HookPanicMap H L ps.toList (ObjEnv.map otab ps L base))
    (hbok : BoundsOK H g L ps.toList)
    (hic : ∀ u, ICallOut L ps.toList u)
    (hME : MachEntry code base room s0) (hroom : otab.autosize + 8 ≤ room)
    (hg : (s0.x 28).toNat + 32 ≤ 2 ^ 64)
    {s sI : LocState} {blkE : Block} {k : Nat}
    (hms : ∀ ce tail gOff, otab.check = some (ce, tail, gOff) → ∀ n add,
      tailCall o.text o.relocs.toList tail = some (n, add) →
      MorestackOK H code (s0.x 30) (L.sym n + BitVec.ofInt 64 add) otab.autosize gOff (live26 sI)
        s0)
    (hsep : ∀ ce tail gOff, otab.check = some (ce, tail, gOff) → TailSep spills.toList s0)
    (hE : G49Env lc g L ps (endP L.text ps.toList) tab E0)
    (hEE : EntryEnv E0 L ps.toList otab.autosize s0)
    (hbE : lc.ctx.f.block? lc.ctx.f.entry = some blkE)
    (hbm : lc.ctx.f.entry ∈ lc.ctx.f.blocks.toList) (hk : k ≤ blkE.values.size)
    (hMs : MemInit s)
    (hpre : enterListLoc env lc s (blkE.values.toList.take k) = .ok sI)
    (hes : entryStoresOK lc g k = true) (hargs : argsOK lc g spills.toList k = true)
    (hent : EntryMatch E0 g (InWins L E0.sp (pendWins lc g)) sI s0)
    (hmore : ∀ ce tail gOff, otab.check = some (ce, tail, gOff) →
      MoreEntry E0 spills.toList gOff sI s0)
    (hinv : G3Inv E0 lc (kAt lc kt lc.ctx.f.entry blkE k) sI osp)
    (hosp : osp = true → E0.outSP = true)
    (hn48 : needs48 lc = true → osp = true)
    (hspI : osp = true → lc.ctx.f.lowered = true → SPInv E0 sI)
    (huE : uL35 lc [] blkE k = [])
    (hpc : ObjEnv.map otab ps L base (E0.pcOf lc.ctx.f.entry k) =
      base + BitVec.ofNat 64 (otab.offs[0]!))
    (hP : RunPreM osp env H lc g L (endP L.text ps.toList) E0 lc.ctx.f.entry k sI)
    (hRo : RoRun g env lc lc.ctx.f.entry k sI)
    (hPP : RunPanicPreM osp env H lc g L (endP L.text ps.toList) E0 lc.ctx.f.entry k sI)
    {fuel : Nat} {e : Panic} {mm : Mem}
    (hrun : runLoopLoc env lc fuel s lc.ctx.f.entry = .panicked e mm) :
    ∃ e' n t', BoundsAgree e e' ∧ runMach H code (s0.x 30) n s0 = .panicked e' t' := by
  cases fuel with
  | zero => simp [runLoopLoc] at hrun
  | succ n =>
    rw [runLoopLoc_entry hbE hpre] at hrun
    obtain ⟨hA, hstk⟩ := argsOK_entry (env := env) hargs hE.env.env.env.env.env.lcEq hent
    obtain ⟨t1, ht1, hS⟩ := sim_entry (H := H) hO hME hroom hg hms hsep hE hEE hent hstk hmore hinv
      hspI (by rw [checkG66L_uIn_entry hc]; exact huE) hbm (memAt_enter hMs hpre) hpc
    obtain ⟨i', s', t2, hr', hi', ht2, hS', hrun'⟩ :=
      sim_entryStores hc hO hH hic hbE (fuel := n) _ k sI t1 rfl hk .refl
        (hS.mono fun y hy => by
          have := entryStoresOK_cover hes L E0.sp hy
          rwa [entryStores_entry hbE] at this)
        (by rw [hrun]; trivial)
    obtain ⟨e', he, t', ht', hp⟩ :=
      sim_from_panic hc hO hH hHP hbok hic hosp hn48 hP hRo hA hPP n _ blkE i' s' t2 hr' hbE hi' hS'
        (hrun'.trans hrun)
    obtain ⟨n', t'', hn⟩ := mstar_panicked (mstar_trans ht1 (mstar_trans ht2 ht')) hp
    exact ⟨e', n', t'', he, hn⟩

end Sim

end GoFV.Proof.Obj
