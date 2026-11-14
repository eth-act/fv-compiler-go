import GoFV.Proof.Gen.G39
import GoFV.Proof.Gen.Spec40

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G40 of the genssa validator: `InitMem` after the entry values (`docs/plans/proofs3.md` §4)

`checkG40 lc` (`GoFV/Gen/Check40.lean`) is G39 (`refsLive lc`, then the check on `liveCtx lc`) with,
in a function with an arm64 op whose values keep the memory (`memPure`), `InitMem` anywhere,
without code.

**The memory.** `runLoc` starts with the activation's initial memory in the state (`MemInit`:
`s.mem = .mem s.fr.mem0`). In a function where `memPure` holds, every step keeps `MemInit`
(`memInit_stepLoc`): a `Phi` changes nothing, a value of a shape without a memory component writes
no memory (`stepLoc_shape`, `clobber_memfr`, `write_memfr`), `InitMem` writes the initial memory
(`stepLoc_initMem`), and `MakeResult`'s write changes nothing (G1's `write_result_noop`); a
terminator only stages its controls (`memInit_stepTermLoc`).

**The slice.** Under `MemInit`, `InitMem` changes nothing (`stepLoc_initMem`), and the machine runs
no code for it: `g40_initMem` relates the states after it, as `g40_value` does for the other
values. `g40_value`, `g40_term`, `g40_nilPanic` and `g40_boundsPanic` are G39's statements over
`checkG40`.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The memory -/

/-- The state's memory is the activation's initial memory. -/
def MemInit (s : LocState) : Prop := s.mem = .mem s.fr.mem0

section Mem

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

theorem clobberMask_memfr (s : LocState) (m : RegMask) :
    (s.clobberMask m).mem = s.mem ∧ (s.clobberMask m).fr = s.fr := by
  unfold LocState.clobberMask; split <;> exact ⟨rfl, rfl⟩

/-- `LocState.clobber` keeps the memory and the frame. -/
theorem clobber_memfr (lc : LocCtx) (s : LocState) (v : Value) :
    (s.clobber lc v).mem = s.mem ∧ (s.clobber lc v).fr = s.fr := by
  have hA : ∀ (b : Bool) (i : Nat) (s : LocState),
      ((if !b then s else match v.args[i]?.bind lc.regOf with
        | some r => s.setReg r .poison | none => s) : LocState).mem = s.mem ∧
      ((if !b then s else match v.args[i]?.bind lc.regOf with
        | some r => s.setReg r .poison | none => s) : LocState).fr = s.fr := by
    intro b i s
    split
    · exact ⟨rfl, rfl⟩
    · split <;> exact ⟨rfl, rfl⟩
  unfold LocState.clobber
  dsimp only
  obtain ⟨h1, h2⟩ := clobberMask_memfr s v.op.regInfo.clobbers
  generalize s.clobberMask v.op.regInfo.clobbers = s1 at h1 h2
  obtain ⟨h3, h4⟩ := hA v.op.regInfo.clobbersArg1 1 s1
  generalize (if !v.op.regInfo.clobbersArg1 then s1 else match v.args[1]?.bind lc.regOf with
        | some r => s1.setReg r .poison | none => s1) = s2 at h3 h4
  obtain ⟨h5, h6⟩ := hA v.op.regInfo.clobbersArg0 0 s2
  generalize (if !v.op.regInfo.clobbersArg0 then s2 else match v.args[0]?.bind lc.regOf with
        | some r => s2.setReg r .poison | none => s2) = s3 at h5 h6
  split <;> split <;> exact ⟨h5.trans (h3.trans h1), h6.trans (h4.trans h2)⟩

theorem writeParts_memfr : ∀ (ts : List Ty) (s : LocState) (xs : List Val) (rs : List (Option Nat)),
    (ts.all fun t => !memTy t) = true →
      (s.writeParts ts xs rs).mem = s.mem ∧ (s.writeParts ts xs rs).fr = s.fr
  | [], s, xs, rs, _ => by cases xs <;> exact ⟨rfl, rfl⟩
  | _ :: _, s, [], rs, _ => ⟨rfl, rfl⟩
  | t :: ts, s, x :: xs, rs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨ht, hts⟩ := h
    unfold LocState.writeParts
    split
    · simp [memTy] at ht
    · split
      · exact writeParts_memfr ts _ xs rs hts
      · split
        · exact writeParts_memfr ts _ xs _ hts
        · exact writeParts_memfr ts _ xs _ hts
        · exact writeParts_memfr ts _ xs _ hts

/-- Writing a value of a shape without a memory component keeps the memory and the frame. -/
theorem write_memfr {id : ID} (hi : memInert (lc.ty id) = true) (x : Val) :
    (s.write lc id x).mem = s.mem ∧ (s.write lc id x).fr = s.fr := by
  unfold LocState.write
  generalize lc.ty id = t at hi
  generalize lc.home id = h
  cases t with
  | mem => cases hi
  | tuple ts =>
    cases h with
    | none => exact writeParts_memfr ts _ _ _ hi
    | some l => cases l with
      | slot k => exact ⟨rfl, rfl⟩
      | _ => exact writeParts_memfr ts _ _ _ hi
  | _ =>
    cases h with
    | none => dsimp only; split <;> exact ⟨rfl, rfl⟩
    | some l => cases l with
      | slot k => exact ⟨rfl, rfl⟩
      | reg r => exact ⟨rfl, rfl⟩
      | _ => dsimp only; split <;> exact ⟨rfl, rfl⟩

/-- A step is a `Phi` that changes nothing, or a write of the value's result after its clobbers. -/
theorem stepLoc_shape (h : stepLoc env lc s v = .ok s') :
    (v.op = .Phi ∧ s' = s) ∨ ∃ x, s' = (s.clobber lc v).write lc v.id x := by
  unfold stepLoc at h
  split at h
  · rename_i hp
    split at h
    · cases h; exact .inl ⟨by simpa using hp, rfl⟩
    · cases h
  · cases hm : v.args.toList.mapM (s.read lc) with
    | panic e m => rw [hm] at h; cases h
    | stuck msg => rw [hm] at h; cases h
    | ok argv =>
      rw [hm] at h
      simp only [bind, Res.bind] at h
      repeat' split at h
      all_goals first
        | (injection h with h; subst h; exact .inr ⟨_, rfl⟩)
        | cases h

/-- `InitMem` without temporary or home, of shape `mem`: the initial memory. -/
theorem stepLoc_initMem (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .InitMem) (hh : lc.home v.id = none) (hmt : memTy (lc.ty v.id) = true)
    (h : stepLoc env lc s v = .ok s') : s' = { s with mem := .mem s.fr.mem0 } := by
  obtain ⟨argv, r, -, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
    (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
  have he : evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) = .ok (.mem s.fr.mem0) := by
    unfold evalOpL evalOp; rw [hop]; rfl
  rw [he] at hr
  cases hr
  rw [write_mem hh hmt, memTy_eq hmt, retypeL_mem]

/-- **Every step keeps the initial memory** in a function whose values keep the memory. -/
theorem memInit_stepLoc (hl : lc.ctx.f.lowered = true) (hp : memPure lc = true) {id : ID}
    (hv : lc.ctx.f.value? id = some v) (h : MemInit s) (hs : stepLoc env lc s v = .ok s') :
    MemInit s' := by
  rcases memKeep_spec (memPure_spec hp hv) with hop | hi | ⟨hop, ht, hh, hmt⟩ |
    ⟨hop, ht, hh, hty, hmem⟩
  · rw [stepLoc_phi hop hs]; exact h
  · rcases stepLoc_shape hs with ⟨-, rfl⟩ | ⟨x, rfl⟩
    · exact h
    · obtain ⟨h1, h2⟩ := write_memfr (s := s.clobber lc v) hi x
      obtain ⟨h3, h4⟩ := clobber_memfr lc s v
      unfold MemInit
      rw [h1, h2, h3, h4]
      exact h
  · rw [stepLoc_initMem hl ht hop hh hmt hs]
    rfl
  · obtain ⟨argv, hargv, rfl⟩ := stepLoc_makeResult hl ht hop hs
    rw [write_result_noop hl h hh hty hmem hargv]
    exact h

/-- A terminator keeps the initial memory: it only stages its controls. -/
theorem memInit_stepTermLoc {b : Block} {n : Next} (h : MemInit s)
    (ht : stepTermLoc lc s b = .ok (n, s')) : MemInit s' := by
  obtain ⟨R, rfl, -⟩ := stepTermLoc_gen ht
  exact h

end Mem

/-! ## `InitMem` -/

/-- `InitMem` empties G35's table. -/
theorem uStep35_initMem {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value}
    (hop : v.op = .InitMem) : uStep35 lc L v = [] := by
  have hl : loadOp? v.op = none := by rw [hop]; rfl
  have hi : loadIdxOp? v.op = none := by rw [hop]; rfl
  have hp : pairOp35 lc v = false := by simp [pairOp35, hop]
  have hk : keep34 v = false := by simp [keep34, keep31, keepOp31, keepOp34, hop]
  have hk31 : keep31 v = false := by simp [keep31, keepOp31, hop]
  have hue : uEntry lc v = none := by
    have : narrowLd? lc v = none := by
      unfold narrowLd?
      rw [hl, hi]
    simp only [uEntry, this]
  rw [uStep35_other (ldEntry35_none hl) hp (by rw [hop]; nofun), uStep34_other hk,
    uStep31_other hk31,
    uStepL_other hue (by rw [hop]; nofun) (by rw [hop]; nofun)]

/-- `InitMem` in a function whose values keep the memory, from a state holding the initial
memory (`MemInit`): no code, and the state is unchanged. -/
theorem g40L_initMem {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG40L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hl : lc.ctx.f.lowered = true) (hp : memPure lc = true)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .InitMem) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hpre : MemInit s)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' ∧
      UOKL m' (uL35 lc (uIn35 lc bid) blk (i + 1)) := by
  have hE0 := hE
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, -, -, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, -, -, -, -, -, -, hblocks, -, -, -⟩ := checkG40L_spec hl hc
  obtain ⟨b, j, js, e, next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk] at hkd
  obtain ⟨ht, -, hh, hmt, rfl⟩ := vkind40_initMem hkd hop hp
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hpc : E.pcOf bid (i + 1) = E.pcOf bid i := by rw [hj', hj, hvs]
  have hss : s' = s := by
    rw [stepLoc_initMem hl ht hop hh hmt hs]
    exact congrArg (fun x => { s with mem := x }) hpre.symm
  subst hss
  have hK : kAt c.cx.lc kt bid blk (i + 1) = kAt c.cx.lc kt bid blk i := by
    rw [kAt_succ hi hv, kStep_none (by rw [hh]; nofun) (by rw [hh]; nofun) (by rw [hh]; nofun)]
  refine ⟨E, m, ⟨rfl, fun _ _ h => h⟩, hE0, .refl, locMatch_pc hm (hpc.trans hm.pc.symm),
    hK ▸ hinv, ?_⟩
  rw [uL35_succ hl hi hv, uStep35_initMem hop]
  intro e he
  cases he

/-! ## The theorems on G40's check -/

/-- G38's values under G40's check. -/
theorem g40L_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG40L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hu : UOKL m (uL35 lc (uIn35 lc bid) blk i))
    (hpre : G38Pre lc s v)
    (hcall : CallOK H E g L lc s s' v m) (hcallz : CallOKZ H E g L lc s s' v m)
    (hicall : ICallOK H E L ret lc s s' v m)
    (hwb : WbOK H E g L lc s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hmeq : MemEqOK H E g L lc s v m) (hmp : MemEqPre lc s v)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' ∧
      UOKL m' (uL35 lc (uIn35 lc bid) blk (i + 1)) := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    obtain ⟨E', m', hx, hE', h1, h2, h3, -⟩ := g33_value (checkG33_of_40L hl hc) hE hbid hb hi hv
      hen hm hinv (by rw [uL31_nl hl]; intro e he; cases he) hpre.1 hcall hcallz hicall hwb hclo
      hgetg hmeq hmp hs
    refine ⟨E', m', hx, hE', h1, h2, h3, ?_⟩
    rw [uL35_nl hl]
    intro e he
    cases he
  | true =>
  rw [uL35_succ hl hi hv]
  have hE0 := hE
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, hcf, hk, hlt, hnd, hblocks, -, hmovd, -⟩ :=
    checkG40L_spec hl hc
  obtain ⟨b, j, js, e, next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk] at hkd
  obtain ⟨htemp, hVK⟩ := vkind40_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  rw [kAt_succ hi hv]
  exact vk38_step hE0 F hhome hcf hv hVK hvs htemp hj hj' hreads hm hinv hu
    (fun x hop hx => movdOK35_spec hmovd hbid hb hi hv hop hx)
    hpre hcall hcallz hicall hwb hclo hgetg hmeq hmp hs

/-- G38's nil panics under G40's check. -/
theorem g40L_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG40L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  cases hl : lc.ctx.f.lowered with
  | false => exact g33_nilPanic (checkG33_of_40L hl hc) hE hbid hb hi hv hop hm hinv hs
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, -⟩ :=
    checkG40L_spec hl hc
  obtain ⟨b, j, js, e', next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk] at hkd
  obtain ⟨-, hVK⟩ := vkind40_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases vk38_nil hVK hop with
  | g6 hne _ => exact absurd hop hne
  | nil _ hsz2 _ _ hao hma =>
    exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao hma hvs hs

/-- G38's bounds panics under G40's check. -/
theorem g40L_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG40L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hbok : BoundsOK H g L ps.toList)
    (hs : stepLoc env lc s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    exact g33_boundsPanic (checkG33_of_40L hl hc) hE hbid hb hi hv hop hm hinv hbok hs
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, hsyms, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, hpb, -, -⟩ :=
    checkG40L_spec hl hc
  obtain ⟨b, j, js, e', next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk] at hkd
  have hen : entryOp24 v.op = false := by
    rcases pbOp_cases hop with h | h | h | h <;> rw [h] <;> rfl
  obtain ⟨-, hVK⟩ := vkind40_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases hVK with
  | ldar h => rw [(ldar_ne h).2.2.2.2.1] at hop; cases hop
  | sel0 h => rw [h] at hop; cases hop
  | sel1 h => rw [h] at hop; cases hop
  | g37 _ _ hVK37 =>
  cases hVK37 with
  | bin h => rw [(aluOp37_ne (aluOp37_bin h)).2.2.2.2] at hop; cases hop
  | un h => rw [(aluOp37_ne (aluOp37_un h)).2.2.2.2] at hop; cases hop
  | madd h => rw [(aluOp37_ne (aluOp37_madd h)).2.2.2.2] at hop; cases hop
  | sbfx h => rw [h] at hop; cases hop
  | g36 _ _ _ _ _ hVK36 =>
  cases hVK36 with
  | g33 _ _ _ hVK33 =>
    cases hVK33 with
    | g32 _ _ _ _ hVK32 =>
      cases hVK32 with
      | g28 _ _ _ _ _ hVK28 =>
        exact vk28_boundsPanic F hsyms hpb hrow hb hi hv hVK28 hvs hj hreads hop hm hinv hbok hs
      | bin h =>
        rw [(aluOp32_ne (aluOp32_bin h)).2.2.2.2] at hop; cases hop
      | binK h =>
        rw [(aluOp32_ne (aluOp32_binK h)).2.2.2.2] at hop; cases hop
      | un h =>
        rw [(aluOp32_ne (aluOp32_un h)).2.2.2.2] at hop; cases hop
      | csinc h => rw [h] at hop; cases hop
      | stlr h => rw [(stlr_ne (lc := c.cx.lc) h).2.2.2.2.1] at hop; cases hop
    | un h => rw [(aluOp33_ne (aluOp33_un h)).2.2.2.2] at hop; cases hop
    | ubfiz h => rw [h] at hop; cases hop
    | sra h => rw [h] at hop; cases hop
    | cmnw h => rw [h] at hop; cases hop
  | sh h => rw [(aluOp36_ne (aluOp36_sh h)).2.2.2.2] at hop; cases hop
  | shOp h => rw [(aluOp36_ne (aluOp36_shOp h)).2.2.2.2] at hop; cases hop
  | tst h => rw [h] at hop; cases hop

/-- G38's terminators under G40's check. -/
theorem g40L_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG40L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s) (hpre : G1TermPre lc s blk)
    (hu : UOKL m (uL35 lc (uIn35 lc bid) blk blk.values.size))
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' ∧
      e.b ∈ lc.ctx.f.blocks.toList ∧ UOKL m' (uIn35 lc e.b) := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g33_term (checkG33_of_40L hl hc) hE hbid hb hm hinv hpre
      (by rw [uL31_nl hl]; intro e he; cases he) ht
    refine ⟨m', h1, h2, h3, h4, ?_⟩
    rw [uIn35_nl hl]
    intro e he
    cases he
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, hedges⟩ :=
    checkG40L_spec hl hc
  obtain ⟨m', h1, h2, h3, h4, he, hx⟩ := termK_stepX hpcOf
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb hm hinv hpre ht
  refine ⟨m', h1, h2, h3, h4, fun x hxin => ?_⟩
  exact uok_of_x hx (hu x (uEdgesOK35_edge hedges hbid hb he x hxin))

/-! ## The slice: the theorems on `checkG40 lc`, on `liveCtx lc` -/

/-- **G40, values.** `g39_value`'s statement over `checkG40`. -/
theorem g40_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG40 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s)
    (hu : UOKL m (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk i))
    (hpre : G38Pre (liveCtx lc) s v)
    (hcall : CallOK H E g L (liveCtx lc) s s' v m) (hcallz : CallOKZ H E g L (liveCtx lc) s s' v m)
    (hicall : ICallOK H E L ret (liveCtx lc) s s' v m)
    (hwb : WbOK H E g L (liveCtx lc) s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hmeq : MemEqOK H E g L (liveCtx lc) s v m) (hmp : MemEqPre (liveCtx lc) s v)
    (hs : stepLoc env (liveCtx lc) s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env (liveCtx lc) g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' (liveCtx lc) (kAt (liveCtx lc) kt bid blk (i + 1)) s' ∧
      UOKL m' (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk (i + 1)) :=
  g40L_value (checkG40_spec hc).2 hE hbid hb hi hv hen hm hinv hu hpre hcall hcallz hicall hwb hclo
    hgetg hmeq hmp hs

/-- **G40, `InitMem`.** In a lowered function whose values keep the memory, from a state holding
the initial memory (`MemInit`, which every step keeps: `memInit_stepLoc`, `memInit_stepTermLoc`),
`InitMem` changes nothing and has no code: `g40_value`'s conclusion. -/
theorem g40_initMem {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG40 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hl : lc.ctx.f.lowered = true) (hp : memPure (liveCtx lc) = true)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .InitMem) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s) (hpre : MemInit s)
    (hs : stepLoc env (liveCtx lc) s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env (liveCtx lc) g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' (liveCtx lc) (kAt (liveCtx lc) kt bid blk (i + 1)) s' ∧
      UOKL m' (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk (i + 1)) :=
  g40L_initMem (checkG40_spec hc).2 hE hl hp hbid hb hi hv hop hm hinv hpre hs

/-- **G40, nil panics.** `g39_nilPanic`'s statement over `checkG40`. -/
theorem g40_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG40 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s)
    (hs : stepLoc env (liveCtx lc) s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e :=
  g40L_nilPanic (checkG40_spec hc).2 hE hbid hb hi hv hop hm hinv hs

/-- **G40, bounds panics.** `g39_boundsPanic`'s statement over `checkG40`. -/
theorem g40_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG40 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s)
    (hbok : BoundsOK H g L ps.toList) (hs : stepLoc env (liveCtx lc) s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' :=
  g40L_boundsPanic (checkG40_spec hc).2 hE hbid hb hi hv hop hm hinv hbok hs

/-- **G40, terminators.** `g39_term`'s statement over `checkG40`. -/
theorem g40_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG40 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk blk.values.size) s)
    (hpre : G1TermPre (liveCtx lc) s blk)
    (hu : UOKL m (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk blk.values.size))
    (ht : stepTermLoc (liveCtx lc) s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧
      G3Inv E (liveCtx lc) (kt.at e.b) s' ∧ e.b ∈ lc.ctx.f.blocks.toList ∧
      UOKL m' (uIn35 (liveCtx lc) e.b) :=
  g40L_term (checkG40_spec hc).2 hE hbid hb hm hinv hpre hu ht

end GoFV.Proof.Gen
