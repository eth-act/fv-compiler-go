import GoFV.Proof.Gen.G48
import GoFV.Proof.Gen.G58a
import GoFV.Proof.Gen.Spec58

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G58 of the genssa validator: narrow and boolean operands, wider store-release sources,
`LoweredRound*F`; G35's upper-bit table across more writes (`docs/plans/proofs3.md` §4)

`checkG58 lc` (`GoFV/Gen/Check58.lean`) is G48 (on G57) with the values of `Check58a.lean`
(`REV16W`, `MADDW`/`MSUBW` of narrow arguments, boolean operands of G32's register and constant
ops, G36's shifts, `UBFIZ` and `CSINC`, `STLRW`/`STLRB` of wider sources, `LoweredRound32F`/`64F`),
each the earlier check's Prog (or none), proven one value at a time in `G58a.lean` (`vk58a_step`,
no premise, in either `outSP` mode; the upper-bit table keeps the other registers' entries where
G32's ops or `keepOps35`'s do). Group B is G35's table (`uStep35`), which G35's proof and every
later slice already carry.
The theorems are G48's (`g48_value`, …) over `checkG58`: in an activation whose `outargs` block
sits at `SP` (`hosp : E.outSP = true`, `SPInv`), with G57's premise `G54Pre`, the contracts of the
mode `true` and G48's `CallOKStk`; `g58_value`, `g58_initMem`, `g58_term` keep `SPInv`.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## One value -/

/-- One value of G58's kinds: `vk48_step`'s statement. -/
theorem vk58_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)}
    (hE : G49Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK58 lc g v kd)
    (hvs : VStep2 ps kd j j') (hloop : loopOp lc v = true → loopTgt ps j = true)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s true) (hL : UOKL m L)
    (hmem : ∀ x, (v.op = .ARM64MOVDnop ∨ v.op = .ARM64MOVDreg) → v.args[0]? = some x →
      ∃ r c, regHome? lc x = some r ∧ cls (lc.ty x) = some c ∧
        (r, c, lc.signOf lc.ctx.f.valueTab.size x) ∈ L)
    (hpre : G54Pre lc s v) (hsp : SPInv E s) (hosp : E.outSP = true)
    (hcall : CallOKAt true H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hcallz : CallOKZAt true H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hicall : ICallOKAt true H E (Link.byId sym text az ez ps.toList) ret lc s s' v m)
    (hwb : WbOKAt true H E g (Link.byId sym text az ez ps.toList) lc s v m) (hclo : CloOK E s v m)
    (hgetg : GetGOK E v)
    (hmeq : MemEqOKAt true H E g (Link.byId sym text az ez ps.toList) lc s v m)
    (hcallk : CallOKStk H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' true ∧
      UOKL m' (uStep35 lc L v) := by
  cases hVK with
  | g48 hVK48 =>
    exact vk48_step hE F hhome hcf hv hVK48 hvs hloop hj hj' hreads hm hinv hL hmem hpre hsp hosp
      hcall hcallz hicall hwb hclo hgetg hmeq hcallk hs
  | a htemp hVK =>
    exact vk58a_step hE F hcf hv hVK hvs htemp hj hj' hreads hm hinv hL hs

/-- A nil check of G58's kinds is G7's. -/
theorem vk58_nil {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK58 lc g v kd)
    (hop : v.op = .ARM64LoweredNilCheck) : VK7 lc g v kd := by
  cases h with
  | g48 h => exact vk48_nil h hop
  | a _ h => exact absurd hop (ops58a_facts (ops58a_of (vk58a_op h))).2.2.2.2.2.2.2.2.2.1

/-- A bounds check of G58's kinds is G28's. -/
theorem vk58_pb {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK58 lc g v kd)
    (hop : pbOp v.op = true) : VK28 lc g v kd := by
  cases h with
  | g48 h => exact vk48_pb h hop
  | a _ h =>
    rw [(ops58a_facts (ops58a_of (vk58a_op h))).2.2.2.2.2.2.2.2.2.2.1] at hop
    cases hop

/-! ## The theorems on G58's check -/

/-- G48's values and G58's group A under G58's check, in a function whose `outargs` block sits at
`SP` (`hosp`, `SPInv`), keeping `SPInv`. -/
theorem g58L_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState}
    (hc : checkG58L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
    (hl : lc.ctx.f.lowered = true)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s E.outSP) (hsp : SPInv E s)
    (hosp : E.outSP = true) (hu : UOKL m (uL35 lc (uIn35 lc bid) blk i))
    (hpre : G54Pre lc s v)
    (hcall : CallOKAt E.outSP H E g L lc s s' v m)
    (hcallz : CallOKZAt E.outSP H E g L lc s s' v m)
    (hicall : ICallOKAt E.outSP H E L ret lc s s' v m)
    (hwb : WbOKAt E.outSP H E g L lc s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hmeq : MemEqOKAt E.outSP H E g L lc s v m) (hcallk : CallOKStk H E g L lc s s' v m)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' E.outSP ∧
      SPInv E' s' ∧ UOKL m' (uL35 lc (uIn35 lc bid) blk (i + 1)) := by
  have hsh : spHomes48 lc = true := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := checkG58L_spec hl hc
    exact h
  suffices key : ∃ E' m', E.Extends E' ∧ G49Env lc g L ps ret tab E' ∧
      PStar H L ps.toList ret m m' ∧ LocMatch E' s' bid (i + 1) m' ∧
      G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' E.outSP ∧
      UOKL m' (uL35 lc (uIn35 lc bid) blk (i + 1)) by
    obtain ⟨E', m', hx, hE', h1, h2, h3, h4⟩ := key
    exact ⟨E', m', hx, hE', h1, h2, h3, spInv_step hE'.env.env.env.env.env.addr hx
      hE.env.env.env.env.env.lcEq (fun _ => ⟨hl, spHomes48_spec hsh⟩) hv hsp hs, h4⟩
  rw [hosp] at hinv hcall hcallz hicall hwb hmeq ⊢
  rw [uL35_succ hl hi hv]
  have hE0 := hE
  obtain ⟨⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, hcf, hk, hlt, hnd, hblocks, -, hmovd, -, hlp,
    -⟩ := checkG58L_spec hl hc
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
  have hVK := vkind58_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  have hloop : loopOp c.cx.lc v = true → loopTgt c.cx.ps ((js ++ [e]).getD i 0) = true :=
    fun hop => loopOK_spec hlp hrow hb hi hv hop
  rw [kAt_succ hi hv]
  exact vk58_step hE0 F hhome hcf hv hVK hvs hloop hj hj' hreads hm hinv hu
    (fun x hop hx => movdOK35_spec hmovd hbid hb hi hv hop hx)
    hpre hsp hosp hcall hcallz hicall hwb hclo hgetg hmeq hcallk hs

/-- `InitMem` under G58's check: `g48L_initMem`'s statement over `checkG58L`. -/
theorem g58L_initMem {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState}
    (hc : checkG58L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
    (hl : lc.ctx.f.lowered = true)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .InitMem) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s E.outSP) (hsp : SPInv E s) (hpre : MemInit s)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' E.outSP ∧
      SPInv E' s' ∧ UOKL m' (uL35 lc (uIn35 lc bid) blk (i + 1)) := by
  have hsh : spHomes48 lc = true := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := checkG58L_spec hl hc
    exact h
  have hsp' := spInv_step (s' := s') hE.env.env.env.env.env.addr ⟨rfl, fun _ _ h => h⟩
    hE.env.env.env.env.env.lcEq (fun _ => ⟨hl, spHomes48_spec hsh⟩) hv hsp hs
  have hE0 := hE
  obtain ⟨⟨⟨⟨⟨⟨-, hlink, hpcOf, -, -, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, -, -, -, -, -, -, hblocks, -, -, -, -, -⟩ :=
    checkG58L_spec hl hc
  obtain ⟨b, j, js, e, next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk, vkind58_initMem hop] at hkd
  have hkd := vkind48_initMem hop hkd
  rw [vkind57_initMem hop, vkind55_initMem hop, vkind54_initMem hop, vkind53_initMem hop,
    vkind52_initMem hop] at hkd
  have hkd := vkind49_initMem hop hkd
  rw [vkind51_initMem hop, vkind50_initMem hop, vkind47_initMem hop, vkind46_initMem hop,
    vkind45_initMem hop, vkind44_initMem hop] at hkd
  obtain ⟨-, -, ht, -, hh, hmt, rfl⟩ := vkind43_initMem hkd hop
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
    hK ▸ hinv, hsp', ?_⟩
  rw [uL35_succ hl hi hv, uStep35_initMem hop]
  intro e he
  cases he

/-- G38's nil panics under G58's check. -/
theorem g58L_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG58L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s osp) (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  cases hl : lc.ctx.f.lowered with
  | false => exact g33_nilPanic (checkG33_of_58L hl hc) hE.env hbid hb hi hv hop hm hinv hs
  | true =>
  obtain ⟨⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, -, -, -⟩ :=
    checkG58L_spec hl hc
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
  have hVK := vkind58_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases vk58_nil hVK hop with
  | g6 hne _ => exact absurd hop hne
  | nil _ hsz2 _ _ hao hma =>
    exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao hma hvs hs

/-- G38's bounds panics under G58's check. -/
theorem g58L_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG58L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s osp) (hbok : BoundsOK H g L ps.toList)
    (hs : stepLoc env lc s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    exact g33_boundsPanic (checkG33_of_58L hl hc) hE.env hbid hb hi hv hop hm hinv hbok hs
  | true =>
  obtain ⟨⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, hsyms, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, hpb, -, -, -, -⟩ :=
    checkG58L_spec hl hc
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
  have hVK := vkind58_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  exact vk28_boundsPanic F hsyms hpb hrow hb hi hv (vk58_pb hVK hop) hvs hj hreads hop hm hinv
    hbok hs

/-- G38's terminators under G58's check, keeping `SPInv`. -/
theorem g58L_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG58L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s E.outSP) (hsp : SPInv E s)
    (hpre : G1TermPre lc s blk) (hu : UOKL m (uL35 lc (uIn35 lc bid) blk blk.values.size))
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧
      G3Inv E lc (kt.at e.b) s' E.outSP ∧ SPInv E s' ∧ e.b ∈ lc.ctx.f.blocks.toList ∧
      UOKL m' (uIn35 lc e.b) := by
  suffices key : ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧
      G3Inv E lc (kt.at e.b) s' E.outSP ∧ e.b ∈ lc.ctx.f.blocks.toList ∧
      UOKL m' (uIn35 lc e.b) by
    obtain ⟨m', h1, h2, h3, h4, h5⟩ := key
    exact ⟨m', h1, h2, h3, spInv_term hsp ht, h4, h5⟩
  cases hl : lc.ctx.f.lowered with
  | false =>
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g33_term (checkG33_of_58L hl hc) hE.env hbid hb hm hinv hpre
      (by rw [uL31_nl hl]; intro e he; cases he) ht
    refine ⟨m', h1, h2, h3, h4, ?_⟩
    rw [uIn35_nl hl]
    intro e he
    cases he
  | true =>
  obtain ⟨⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, hedges, -, -⟩ :=
    checkG58L_spec hl hc
  obtain ⟨m', h1, h2, h3, h4, he, hx⟩ := termK_stepX hpcOf
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb hm hinv hpre ht
  refine ⟨m', h1, h2, h3, h4, fun x hxin => ?_⟩
  exact uok_of_x hx (hu x (uEdgesOK35_edge hedges hbid hb he x hxin))

/-! ## The slice: the theorems on `checkG58 lc`, on `liveCtx lc` -/

/-- **G58, values.** `g48_value`'s statement over `checkG58`: G48's values (with G57's, under
`G54Pre`, the contracts of the mode `E.outSP` and `CallOKStk`) and G58's group A (no premise), in an
activation whose `outargs` block sits at `SP` (`hosp`, `SPInv`), keeping `SPInv`. -/
theorem g58_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState}
    (hc : checkG58 lc ps bstart g = .ok (tab, kt)) (hE : G49Env (liveCtx lc) g L ps ret tab E)
    (hl : lc.ctx.f.lowered = true)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s E.outSP) (hsp : SPInv E s)
    (hosp : E.outSP = true)
    (hu : UOKL m (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk i))
    (hpre : G54Pre (liveCtx lc) s v)
    (hcall : CallOKAt E.outSP H E g L (liveCtx lc) s s' v m)
    (hcallz : CallOKZAt E.outSP H E g L (liveCtx lc) s s' v m)
    (hicall : ICallOKAt E.outSP H E L ret (liveCtx lc) s s' v m)
    (hwb : WbOKAt E.outSP H E g L (liveCtx lc) s v m) (hclo : CloOK E s v m)
    (hgetg : GetGOK E v) (hmeq : MemEqOKAt E.outSP H E g L (liveCtx lc) s v m)
    (hcallk : CallOKStk H E g L (liveCtx lc) s s' v m)
    (hs : stepLoc env (liveCtx lc) s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env (liveCtx lc) g L ps ret tab E' ∧
      PStar H L ps.toList ret m m' ∧ LocMatch E' s' bid (i + 1) m' ∧
      G3Inv E' (liveCtx lc) (kAt (liveCtx lc) kt bid blk (i + 1)) s' E.outSP ∧ SPInv E' s' ∧
      UOKL m' (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk (i + 1)) :=
  g58L_value (checkG58_spec hc).2 hE hl hbid hb hi hv hen hm hinv hsp hosp hu hpre hcall hcallz
    hicall hwb hclo hgetg hmeq hcallk hs

/-- **G58, `InitMem`.** `g48_initMem`'s statement over `checkG58`, `SPInv` kept by the checker's
`spHomes48`. -/
theorem g58_initMem {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState}
    (hc : checkG58 lc ps bstart g = .ok (tab, kt)) (hE : G49Env (liveCtx lc) g L ps ret tab E)
    (hl : lc.ctx.f.lowered = true)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .InitMem) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s E.outSP) (hsp : SPInv E s)
    (hpre : MemInit s) (hs : stepLoc env (liveCtx lc) s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env (liveCtx lc) g L ps ret tab E' ∧
      PStar H L ps.toList ret m m' ∧ LocMatch E' s' bid (i + 1) m' ∧
      G3Inv E' (liveCtx lc) (kAt (liveCtx lc) kt bid blk (i + 1)) s' E.outSP ∧ SPInv E' s' ∧
      UOKL m' (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk (i + 1)) :=
  g58L_initMem (checkG58_spec hc).2 hE hl hbid hb hi hv hop hm hinv hsp hpre hs

/-- **G58, nil panics.** `g48_nilPanic`'s statement over `checkG58`. -/
theorem g58_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG58 lc ps bstart g = .ok (tab, kt)) (hE : G49Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s osp)
    (hs : stepLoc env (liveCtx lc) s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e :=
  g58L_nilPanic (checkG58_spec hc).2 hE hbid hb hi hv hop hm hinv hs

/-- **G58, bounds panics.** `g48_boundsPanic`'s statement over `checkG58`. -/
theorem g58_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG58 lc ps bstart g = .ok (tab, kt)) (hE : G49Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s osp)
    (hbok : BoundsOK H g L ps.toList) (hs : stepLoc env (liveCtx lc) s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' :=
  g58L_boundsPanic (checkG58_spec hc).2 hE hbid hb hi hv hop hm hinv hbok hs

/-- **G58, terminators.** `g48_term`'s statement over `checkG58`, keeping `SPInv`. -/
theorem g58_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG58 lc ps bstart g = .ok (tab, kt)) (hE : G49Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk blk.values.size) s E.outSP)
    (hsp : SPInv E s) (hpre : G1TermPre (liveCtx lc) s blk)
    (hu : UOKL m (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk blk.values.size))
    (ht : stepTermLoc (liveCtx lc) s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧
      G3Inv E (liveCtx lc) (kt.at e.b) s' E.outSP ∧ SPInv E s' ∧ e.b ∈ lc.ctx.f.blocks.toList ∧
      UOKL m' (uIn35 (liveCtx lc) e.b) :=
  g58L_term (checkG58_spec hc).2 hE hbid hb hm hinv hsp hpre hu ht

end GoFV.Proof.Gen
