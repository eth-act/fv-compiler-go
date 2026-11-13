import GoFV.Proof.Gen.G53

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G53 for a function whose `outargs` block sits at `SP` (`docs/plans/proofs3.md` §8 item 7)

A function with stack arguments or results places its activation's `outargs` block at `SP`
(`MatchEnv.outSP`), whose first word is the frame's saved `LR`: the live blocks are then away from
the frame but for that word's `poison` bytes (`SepFromW`), not wholly (`SepFrom`), and the calls
go by the contracts of that separation (`CallOKS`, `CallOKZS`, `ICallOKS`, `WbOKS`, `MemEqOKS`).
`g53_value` and its siblings hold in the separation of any mode `osp` (`SepAt`, `G3Inv … osp`, the
contracts `CallOKAt osp` …); the theorems here take the mode `E.outSP` and add `SPInv`: when
`E.outSP`, `ι` puts the `outargs` block at `SP` (`SPAt`) and the Go register `SP` (`spReg`) holds
`SP`'s value or `poison` (`SPRegRel`). Every step keeps `SPInv` (`spInv_step`, from the shape of a
step, `stepLoc_shape`) when the function homes only `SP` values in `spReg` (`SPHomes`, a static
premise).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The premises -/

/-- When the activation's `outargs` block sits at `SP` (`E.outSP`): `ι` puts it at `SP`, and the
Go register `SP` (`spReg`, no machine register) holds a value related to `SP`. -/
def SPInv (E : MatchEnv) (s : LocState) : Prop :=
  E.outSP = true → E.ι (.outargs E.lc.ctx.act) = some E.sp ∧
    ∀ x, s.regs[spReg]? = some x → ValRel E.ι x E.sp

/-- A lowered function whose only values homed in `spReg` (alone, or as a part of a register
list) are `Phi`s (which write nothing) and `SP` values of a 64-bit class without a temporary
register. -/
def SPHomes (lc : LocCtx) : Prop :=
  lc.ctx.f.lowered = true ∧ ∀ id v, lc.ctx.f.value? id = some v → ∀ l, lc.home v.id = some l →
    some spReg ∈ l.regList → v.op = .Phi ∨
      (l = .reg spReg ∧ v.op = .SP ∧ cls (lc.ty v.id) = some 64 ∧ (lc.temps[v.id]?).join = none)

/-! ## Registers after a step -/

section Regs

variable {lc : LocCtx} {s : LocState} {r : Nat} {y : Val}

theorem writeParts_regs : ∀ (ts : List Ty) (xs : List Val) (rs : List (Option Nat))
    (s : LocState), (s.writeParts ts xs rs).regs[r]? = some y → s.regs[r]? = some y ∨ some r ∈ rs
  | [], _, _, _, h => .inl (by simpa [LocState.writeParts] using h)
  | _ :: _, [], _, _, h => .inl (by simpa [LocState.writeParts] using h)
  | t :: ts, x :: xs, rs, s, h => by
    unfold LocState.writeParts at h
    split at h
    · exact writeParts_regs ts xs rs { s with mem := x } h
    · split at h
      · exact writeParts_regs ts xs rs { s with flags := x } h
      · split at h
        · rename_i r' rs'
          rcases writeParts_regs ts xs rs' _ h with h' | h'
          · rcases setReg_get h' with ⟨rfl, -⟩ | ⟨-, h''⟩
            · exact .inr (by simp)
            · exact .inl h''
          · exact .inr (by simp [h'])
        · rename_i rs'
          rcases writeParts_regs ts xs rs' _ h with h' | h'
          · exact .inl h'
          · exact .inr (by simp [h'])
        · exact writeParts_regs ts xs [] _ h

/-- A register after a value's result is written: as before, the result in its register home, or
a part of a tuple in a register of its home's list. -/
theorem write_regs {id : ID} {x : Val} (h : (s.write lc id x).regs[r]? = some y) :
    s.regs[r]? = some y ∨ (lc.home id = some (.reg r) ∧ y = x) ∨
      ∃ l ts, lc.home id = some l ∧ lc.ty id = .tuple ts ∧ some r ∈ l.regList := by
  unfold LocState.write at h
  cases hh : lc.home id with
  | none =>
    cases ht : lc.ty id <;> simp only [hh, ht] at h
    case tuple ts =>
      rcases writeParts_regs _ _ _ _ h with h' | h'
      · exact .inl h'
      · simp at h'
    all_goals first
      | exact .inl h
      | (split at h <;> exact .inl h)
  | some l =>
    cases l with
    | slot k =>
      simp only [hh] at h
      exact .inl h
    | reg r' =>
      cases ht : lc.ty id <;> simp only [hh, ht] at h
      case tuple ts =>
        rcases writeParts_regs _ _ _ _ h with h' | h'
        · exact .inl h'
        · exact .inr (.inr ⟨_, ts, rfl, rfl, h'⟩)
      all_goals
        rcases setReg_get h with ⟨rfl, rfl⟩ | ⟨-, h'⟩
        · exact .inr (.inl ⟨rfl, rfl⟩)
        · exact .inl h'
    | pair a b =>
      cases ht : lc.ty id <;> simp only [hh, ht] at h
      case tuple ts =>
        rcases writeParts_regs _ _ _ _ h with h' | h'
        · exact .inl h'
        · exact .inr (.inr ⟨_, ts, rfl, rfl, h'⟩)
      all_goals first
        | exact .inl h
        | (split at h <;> exact .inl h)
    | results rs =>
      cases ht : lc.ty id <;> simp only [hh, ht] at h
      case tuple ts =>
        rcases writeParts_regs _ _ _ _ h with h' | h'
        · exact .inl h'
        · exact .inr (.inr ⟨_, ts, rfl, rfl, h'⟩)
      all_goals first
        | exact .inl h
        | (split at h <;> exact .inl h)

/-- The registers of `t` are those of `s` or `poison`. -/
abbrev PoisonOrOld (s t : LocState) : Prop :=
  ∀ (q : Nat) (z : Val), t.regs[q]? = some z → s.regs[q]? = some z ∨ z = .poison

theorem PoisonOrOld.refl (s : LocState) : PoisonOrOld s s := fun _ _ h => .inl h

theorem PoisonOrOld.setReg {t : LocState} (h : PoisonOrOld s t) (q : Nat) :
    PoisonOrOld s (t.setReg q .poison) := fun r y hy => by
  rcases setReg_get hy with ⟨-, rfl⟩ | ⟨-, h'⟩
  · exact .inr rfl
  · exact h r y h'

theorem PoisonOrOld.clobberMask {t : LocState} (h : PoisonOrOld s t) (msk : RegMask) :
    PoisonOrOld s (t.clobberMask msk) := fun r y hy => by
  unfold LocState.clobberMask at hy
  split at hy
  · exact h r y hy
  · simp only [Array.getElem?_mapIdx] at hy
    cases hr : t.regs[r]? with
    | none => rw [hr] at hy; cases hy
    | some z =>
      rw [hr] at hy
      simp only [Option.map_some, Option.some.injEq] at hy
      split at hy
      · exact .inr hy.symm
      · exact h r y (by rw [hr, hy])

theorem PoisonOrOld.ofRegs {t t' : LocState} (h : PoisonOrOld s t) (he : t'.regs = t.regs) :
    PoisonOrOld s t' := fun q z hz => h q z (he ▸ hz)

/-- A register after a value's clobbers: as before, or `poison`. -/
theorem clobber_regs {v : Value} (h : (s.clobber lc v).regs[r]? = some y) :
    s.regs[r]? = some y ∨ y = .poison := by
  suffices hs : PoisonOrOld s (s.clobber lc v) from hs r y h
  have h0 := (PoisonOrOld.refl s).clobberMask v.op.regInfo.clobbers
  unfold LocState.clobber
  dsimp only
  generalize s.clobberMask v.op.regInfo.clobbers = s0 at h0
  split
  · refine PoisonOrOld.ofRegs ?_ rfl
    repeat' split
    all_goals repeat (first | apply PoisonOrOld.setReg | exact h0)
  · repeat' split
    all_goals repeat (first | apply PoisonOrOld.setReg | exact h0)

end Regs

/-! ## `SPInv` across a step -/

/-- `SP` writes the pointer to the activation's `outargs` block to its home. -/
theorem stepLoc_sp_val {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}
    (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none) (hop : v.op = .SP)
    (h : stepLoc env lc s v = .ok s') :
    s' = s.write lc v.id ((Val.ptr ⟨.outargs lc.ctx.act, 0⟩).retypeL (lc.ty v.id)) := by
  obtain ⟨argv, r, -, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
    (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
  have he : evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) =
      .ok (.ptr ⟨.outargs lc.ctx.act, 0⟩) := by
    have hr : isRoot Op.SP = false := by decide
    unfold evalOpL evalOp frameVal
    rw [hop]
    simp only [show Op.SP.generic = true by decide, hr, ↓reduceIte, Bool.false_eq_true]
    rfl
  rw [he] at hr
  cases hr
  rfl

/-- **Every step keeps `SPInv`** in a function whose only values homed in `spReg` are `SP` values
(`SPHomes`), under an extension of the injection. -/
theorem spInv_step {env : Env} {E E' : MatchEnv} {lc : LocCtx} {s s' : LocState} {v : Value}
    {id : ID} (hA : AddrAgree E'.ι) (hx : E.Extends E') (hlc : E.lc = lc)
    (hsph : E.outSP = true → SPHomes lc) (hv : lc.ctx.f.value? id = some v) (h : SPInv E s)
    (hs : stepLoc env lc s v = .ok s') : SPInv E' s' := by
  obtain ⟨hxe, hext⟩ := hx
  have hsp : E'.sp = E.sp := by rw [hxe]
  have hlc' : E'.lc = E.lc := by rw [hxe]
  have hosp : E'.outSP = E.outSP := by rw [hxe]
  intro ho
  rw [hosp] at ho
  obtain ⟨hat, hreg⟩ := h ho
  obtain ⟨hl, hh⟩ := hsph ho
  refine ⟨by rw [hsp, hlc']; exact hext _ _ hat, fun y hy => ?_⟩
  rw [hsp]
  have old : ∀ y, s.regs[spReg]? = some y → ValRel E'.ι y E.sp := fun y hy =>
    valRel_mono hext (hreg y hy)
  by_cases hphi : v.op = .Phi
  · rw [stepLoc_phi hphi hs] at hy
    exact old y hy
  by_cases hin : ∃ l, lc.home v.id = some l ∧ some spReg ∈ l.regList
  · obtain ⟨l, hhl, hin⟩ := hin
    obtain ⟨rfl, hop, hcls, htemp⟩ := (hh id v hv l hhl hin).resolve_left hphi
    rw [stepLoc_sp_val hl htemp hop hs] at hy
    rcases write_regs hy with hy | ⟨-, rfl⟩ | ⟨l', ts, hhl', hts, -⟩
    · exact old y hy
    · subst hlc
      exact valRel_retypeL hA hcls rfl ⟨E.sp, hext _ _ hat, by simp⟩
    · rw [hts] at hcls
      simp [Gen.Check.cls] at hcls
  · rcases stepLoc_shape hs with ⟨hp, -⟩ | ⟨x, rfl⟩
    · exact absurd hp hphi
    rcases write_regs hy with hy | ⟨hhl, -⟩ | ⟨l, ts, hhl, -, hl'⟩
    · rcases clobber_regs hy with hy | rfl
      · exact old y hy
      · trivial
    · exact absurd ⟨_, hhl, by simp [Location.regList]⟩ hin
    · exact absurd ⟨l, hhl, hl'⟩ hin

/-- A terminator keeps `SPInv`: it only stages its controls. -/
theorem spInv_term {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {blk : Block} {n : Next}
    (h : SPInv E s) (ht : stepTermLoc lc s blk = .ok (n, s')) : SPInv E s' := by
  obtain ⟨R, rfl, -⟩ := stepTermLoc_gen ht
  exact h

/-! ## The theorems on `checkG53L`, in the mode `E.outSP` -/

/-- `g53L_value` in the separation of mode `E.outSP`, keeping `SPInv`. -/
theorem g53L_valueS {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState}
    (hc : checkG53L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s E.outSP) (hsp : SPInv E s)
    (hsph : E.outSP = true → SPHomes lc) (hu : UOKL m (uL35 lc (uIn35 lc bid) blk i))
    (hpre : G53Pre lc s v)
    (hcall : CallOKAt E.outSP H E g L lc s s' v m)
    (hcallz : CallOKZAt E.outSP H E g L lc s s' v m)
    (hicall : ICallOKAt E.outSP H E L ret lc s s' v m)
    (hwb : WbOKAt E.outSP H E g L lc s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hmeq : MemEqOKAt E.outSP H E g L lc s v m) (hmp : MemEqPre lc s v)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' E.outSP ∧
      SPInv E' s' ∧ UOKL m' (uL35 lc (uIn35 lc bid) blk (i + 1)) := by
  obtain ⟨E', m', hx, hE', h1, h2, h3, h4⟩ := g53L_value hc hE hbid hb hi hv hen hm hinv hu hpre
    hcall hcallz hicall hwb hclo hgetg hmeq hmp hs
  exact ⟨E', m', hx, hE', h1, h2, h3,
    spInv_step hE'.env.env.env.env.env.addr hx hE.env.env.env.env.env.lcEq hsph hv hsp hs, h4⟩

/-- `g53L_initMem` in the separation of mode `E.outSP`, keeping `SPInv`. -/
theorem g53L_initMemS {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState}
    (hc : checkG53L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
    (hl : lc.ctx.f.lowered = true)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .InitMem) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s E.outSP) (hsp : SPInv E s)
    (hsph : E.outSP = true → SPHomes lc) (hpre : MemInit s)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' E.outSP ∧
      SPInv E' s' ∧ UOKL m' (uL35 lc (uIn35 lc bid) blk (i + 1)) := by
  obtain ⟨E', m', hx, hE', h1, h2, h3, h4⟩ :=
    g53L_initMem (H := H) hc hE hl hbid hb hi hv hop hm hinv hpre hs
  exact ⟨E', m', hx, hE', h1, h2, h3,
    spInv_step hE'.env.env.env.env.env.addr hx hE.env.env.env.env.env.lcEq hsph hv hsp hs, h4⟩

/-- `g53L_term` in the separation of mode `E.outSP`, keeping `SPInv`. -/
theorem g53L_termS {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG53L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s E.outSP) (hsp : SPInv E s)
    (hpre : G1TermPre lc s blk) (hu : UOKL m (uL35 lc (uIn35 lc bid) blk blk.values.size))
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧
      G3Inv E lc (kt.at e.b) s' E.outSP ∧ SPInv E s' ∧ e.b ∈ lc.ctx.f.blocks.toList ∧
      UOKL m' (uIn35 lc e.b) := by
  obtain ⟨m', h1, h2, h3, h4, h5⟩ := g53L_term (H := H) hc hE hbid hb hm hinv hpre hu ht
  exact ⟨m', h1, h2, h3, spInv_term hsp ht, h4, h5⟩

/-! ## The slice in the mode `E.outSP`: the theorems on `checkG53 lc`, on `liveCtx lc` -/

/-- **G53, values, `outargs` at `SP`.** `g53_value` in the separation of mode `E.outSP` (the
contracts of that mode), keeping `SPInv`. -/
theorem g53_valueS {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState}
    (hc : checkG53 lc ps bstart g = .ok (tab, kt)) (hE : G49Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s E.outSP) (hsp : SPInv E s)
    (hsph : E.outSP = true → SPHomes (liveCtx lc))
    (hu : UOKL m (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk i))
    (hpre : G53Pre (liveCtx lc) s v)
    (hcall : CallOKAt E.outSP H E g L (liveCtx lc) s s' v m)
    (hcallz : CallOKZAt E.outSP H E g L (liveCtx lc) s s' v m)
    (hicall : ICallOKAt E.outSP H E L ret (liveCtx lc) s s' v m)
    (hwb : WbOKAt E.outSP H E g L (liveCtx lc) s v m) (hclo : CloOK E s v m)
    (hgetg : GetGOK E v) (hmeq : MemEqOKAt E.outSP H E g L (liveCtx lc) s v m)
    (hmp : MemEqPre (liveCtx lc) s v) (hs : stepLoc env (liveCtx lc) s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env (liveCtx lc) g L ps ret tab E' ∧
      PStar H L ps.toList ret m m' ∧ LocMatch E' s' bid (i + 1) m' ∧
      G3Inv E' (liveCtx lc) (kAt (liveCtx lc) kt bid blk (i + 1)) s' E.outSP ∧ SPInv E' s' ∧
      UOKL m' (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk (i + 1)) :=
  g53L_valueS (checkG53_spec hc).2 hE hbid hb hi hv hen hm hinv hsp hsph hu hpre hcall hcallz
    hicall hwb hclo hgetg hmeq hmp hs

/-- **G53, `InitMem`, `outargs` at `SP`.** `g53_initMem` in the mode `E.outSP`, keeping
`SPInv`. -/
theorem g53_initMemS {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState}
    (hc : checkG53 lc ps bstart g = .ok (tab, kt)) (hE : G49Env (liveCtx lc) g L ps ret tab E)
    (hl : lc.ctx.f.lowered = true)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .InitMem) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s E.outSP) (hsp : SPInv E s)
    (hsph : E.outSP = true → SPHomes (liveCtx lc)) (hpre : MemInit s)
    (hs : stepLoc env (liveCtx lc) s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env (liveCtx lc) g L ps ret tab E' ∧
      PStar H L ps.toList ret m m' ∧ LocMatch E' s' bid (i + 1) m' ∧
      G3Inv E' (liveCtx lc) (kAt (liveCtx lc) kt bid blk (i + 1)) s' E.outSP ∧ SPInv E' s' ∧
      UOKL m' (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk (i + 1)) :=
  g53L_initMemS (checkG53_spec hc).2 hE hl hbid hb hi hv hop hm hinv hsp hsph hpre hs

/-- **G53, terminators, `outargs` at `SP`.** `g53_term` in the mode `E.outSP`, keeping
`SPInv`. -/
theorem g53_termS {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG53 lc ps bstart g = .ok (tab, kt)) (hE : G49Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk blk.values.size) s E.outSP)
    (hsp : SPInv E s) (hpre : G1TermPre (liveCtx lc) s blk)
    (hu : UOKL m (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk blk.values.size))
    (ht : stepTermLoc (liveCtx lc) s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧
      G3Inv E (liveCtx lc) (kt.at e.b) s' E.outSP ∧ SPInv E s' ∧ e.b ∈ lc.ctx.f.blocks.toList ∧
      UOKL m' (uIn35 (liveCtx lc) e.b) :=
  g53L_termS (checkG53_spec hc).2 hE hbid hb hm hinv hsp hpre hu ht

end GoFV.Proof.Gen
