import GoFV.Proof.Gen.G61
import GoFV.Proof.Gen.G62a

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G62 of the genssa validator: incoming stack arguments (`docs/plans/proofs3.md` §4)

`checkG62 lc` (`GoFV/Gen/Check62.lean`) is G61 with the `Arg` of a parameter the ABI assigns to
the stack, homed in the slot of its piece at its `NAME_PARAM` operand, with no code (`vkind62a`,
`VK62.arg`). A value of G61 is `vk61_step`'s; an `Arg` is `g62_arg`'s (`G62a.lean`). The theorems
are G61's over `checkG62`, at either mode `osp` (`G3Inv … osp`; the mode `true` for a function that
needs G48's mode, `hn48`, with the activation's `outargs` block at `SP`, `hosp`, `SPInv`, kept),
with G61's premises and `ArgOK`: the caller's stack argument in the machine's slot of the piece
when the `Arg` runs.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## One value -/

/-- One value of G62's kinds: `vk61_step`'s statement, with `ArgOK` for an `Arg`. -/
theorem vk62_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)} {osp : Bool}
    (hE : G49Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK62 lc g v kd)
    (hvs : VStep2 ps kd j j') (hloop : loopOp lc v = true → loopTgt ps j = true)
    (hatom : ∀ f n, atom61? v.op = some (f, n) → atomTgt f ps j = true)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s osp) (hL : UOKL m L)
    (hmem : ∀ x, (v.op = .ARM64MOVDnop ∨ v.op = .ARM64MOVDreg) → v.args[0]? = some x →
      ∃ r c, regHome? lc x = some r ∧ cls (lc.ty x) = some c ∧
        (r, c, lc.signOf lc.ctx.f.valueTab.size x) ∈ L)
    (hpre : G54Pre lc s v) (hro : RoPre56 g s) (h48 : take48 lc v = true → osp = true)
    (hsp : osp = true → SPInv E s ∧ E.outSP = true)
    (hcall : CallOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hcallz : CallOKZAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hicall : ICallOKAt osp H E (Link.byId sym text az ez ps.toList) ret lc s s' v m)
    (hwb : WbOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s v m) (hclo : CloOK E s v m)
    (hgetg : GetGOK E v)
    (hmeq : MemEqOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s v m)
    (hmp : MemEqPre lc s v)
    (hcallk : osp = true → CallOKStk H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (harg : ArgOK E lc s v m)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp ∧
      UOKL m' (uStep35 lc L v) := by
  cases hVK with
  | g61 hVK61 =>
    exact vk61_step hE F hhome hcf hv hVK61 hvs hloop hatom hj hj' hreads hm hinv hL hmem hpre hro
      h48 hsp hcall hcallz hicall hwb hclo hgetg hmeq hmp hcallk hs
  | @arg x o htemp hop _ hx _ hcv hh hso =>
    obtain ⟨h1, h2, h3⟩ := g62_arg (H := H) hE.env.env.env.env.env F.lowered hvs hj hj' hm hinv
      htemp hop hx hcf hcv hh hso harg hs
    exact ⟨E, m, ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, h3,
      by rw [uStep35_arg hop]; exact fun e he => by cases he⟩

/-- A nil check of G62's kinds is G7's. -/
theorem vk62_nil {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK62 lc g v kd)
    (hop : v.op = .ARM64LoweredNilCheck) : VK7 lc g v kd := by
  cases h with
  | g61 h => exact vk61_nil h hop
  | arg _ hop' => rw [hop'] at hop; cases hop

/-- A bounds check of G62's kinds is G28's. -/
theorem vk62_pb {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK62 lc g v kd)
    (hop : pbOp v.op = true) : VK28 lc g v kd := by
  cases h with
  | g61 h => exact vk61_pb h hop
  | arg _ hop' => rw [hop'] at hop; cases hop

/-! ## The theorems on G62's check -/

/-- G61's values and the incoming stack arguments under G62's check at either mode `osp` (the
mode `true` for a function that needs G48's mode, `hn48`; there the `outargs` block sits at `SP`,
`hosp`, `SPInv`, kept), under G61's premises and `ArgOK`. -/
theorem g62L_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {osp : Bool}
    (hc : checkG62L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
    (hl : lc.ctx.f.lowered = true)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s osp) (hsp : osp = true → SPInv E s)
    (hosp : osp = true → E.outSP = true) (hn48 : needs48 lc = true → osp = true)
    (hu : UOKL m (uL35 lc (uIn35 lc bid) blk i))
    (hpre : G54Pre lc s v) (hro : RoPre56 g s)
    (hcall : CallOKAt osp H E g L lc s s' v m)
    (hcallz : CallOKZAt osp H E g L lc s s' v m)
    (hicall : ICallOKAt osp H E L ret lc s s' v m)
    (hwb : WbOKAt osp H E g L lc s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hmeq : MemEqOKAt osp H E g L lc s v m) (hmp : MemEqPre lc s v)
    (hcallk : osp = true → CallOKStk H E g L lc s s' v m)
    (harg : ArgOK E lc s v m)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' osp ∧
      (osp = true → SPInv E' s') ∧ UOKL m' (uL35 lc (uIn35 lc bid) blk (i + 1)) := by
  have hsh : spHomes48 lc = true := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := checkG62L_spec hl hc
    exact h
  have h48 : take48 lc v = true → osp = true := fun h => hn48 (take48_of_needs48 hl hv h)
  suffices key : ∃ E' m', E.Extends E' ∧ G49Env lc g L ps ret tab E' ∧
      PStar H L ps.toList ret m m' ∧ LocMatch E' s' bid (i + 1) m' ∧
      G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' osp ∧
      UOKL m' (uL35 lc (uIn35 lc bid) blk (i + 1)) by
    obtain ⟨E', m', hx, hE', h1, h2, h3, h4⟩ := key
    exact ⟨E', m', hx, hE', h1, h2, h3, fun ho => spInv_step hE'.env.env.env.env.env.addr hx
      hE.env.env.env.env.env.lcEq (fun _ => ⟨hl, spHomes48_spec hsh⟩) hv (hsp ho) hs, h4⟩
  rw [uL35_succ hl hi hv]
  have hE0 := hE
  obtain ⟨⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, hcf, hk, hlt, hnd, hblocks, -, hmovd, -, hlp,
    -, hat⟩ := checkG62L_spec hl hc
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
  have hVK := vkind62_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  have hloop : loopOp c.cx.lc v = true → loopTgt c.cx.ps ((js ++ [e]).getD i 0) = true :=
    fun hop => loopOK_spec hlp hrow hb hi hv hop
  have hatom : ∀ f n, atom61? v.op = some (f, n) →
      atomTgt f c.cx.ps ((js ++ [e]).getD i 0) = true :=
    fun _ _ hop => atomOK_spec hat hrow hb hi hv hop
  rw [kAt_succ hi hv]
  exact vk62_step hE0 F hhome hcf hv hVK hvs hloop hatom hj hj' hreads hm hinv hu
    (fun x hop hx => movdOK35_spec hmovd hbid hb hi hv hop hx)
    hpre hro h48 (fun ho => ⟨hsp ho, hosp ho⟩) hcall hcallz hicall hwb hclo hgetg hmeq hmp hcallk
    harg hs

/-- `InitMem` under G62's check: `g61L_initMem`'s statement over `checkG62L`. -/
theorem g62L_initMem {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {osp : Bool}
    (hc : checkG62L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
    (hl : lc.ctx.f.lowered = true)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .InitMem) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s osp) (hsp : osp = true → SPInv E s)
    (hpre : MemInit s) (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' osp ∧
      (osp = true → SPInv E' s') ∧ UOKL m' (uL35 lc (uIn35 lc bid) blk (i + 1)) := by
  have hsh : spHomes48 lc = true := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := checkG62L_spec hl hc
    exact h
  have hsp' := fun ho => spInv_step (s' := s') hE.env.env.env.env.env.addr
    ⟨rfl, fun _ _ h => h⟩ hE.env.env.env.env.env.lcEq (fun _ => ⟨hl, spHomes48_spec hsh⟩) hv
    (hsp ho) hs
  have hE0 := hE
  obtain ⟨⟨⟨⟨⟨⟨-, hlink, hpcOf, -, -, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, -, -, -, -, -, -, hblocks, -, -, -, -, -, -⟩ :=
    checkG62L_spec hl hc
  obtain ⟨b, j, js, e, next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk, vkind62_initMem hop, vkind61_initMem hop, vkind60_initMem hop, vkind59_initMem hop,
    vkind58_initMem hop]
    at hkd
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

/-- G38's nil panics under G62's check. -/
theorem g62L_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG62L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s osp) (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  cases hl : lc.ctx.f.lowered with
  | false => exact g33_nilPanic (checkG33_of_62L hl hc) hE.env hbid hb hi hv hop hm hinv hs
  | true =>
  obtain ⟨⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, -, -, -, -⟩ :=
    checkG62L_spec hl hc
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
  have hVK := vkind62_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases vk62_nil hVK hop with
  | g6 hne _ => exact absurd hop hne
  | nil _ hsz2 _ _ hao hma =>
    exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao hma hvs hs

/-- G38's bounds panics under G62's check. -/
theorem g62L_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG62L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s osp) (hbok : BoundsOK H g L ps.toList)
    (hs : stepLoc env lc s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    exact g33_boundsPanic (checkG33_of_62L hl hc) hE.env hbid hb hi hv hop hm hinv hbok hs
  | true =>
  obtain ⟨⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, hsyms, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, hpb, -, -, -, -, -⟩ :=
    checkG62L_spec hl hc
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
  have hVK := vkind62_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  exact vk28_boundsPanic F hsyms hpb hrow hb hi hv (vk62_pb hVK hop) hvs hj hreads hop hm hinv
    hbok hs

/-- G38's terminators under G62's check, keeping `SPInv`. -/
theorem g62L_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState} {osp : Bool}
    (hc : checkG62L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s osp)
    (hsp : osp = true → SPInv E s)
    (hpre : G1TermPre lc s blk) (hu : UOKL m (uL35 lc (uIn35 lc bid) blk blk.values.size))
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧
      G3Inv E lc (kt.at e.b) s' osp ∧ (osp = true → SPInv E s') ∧
      e.b ∈ lc.ctx.f.blocks.toList ∧ UOKL m' (uIn35 lc e.b) := by
  suffices key : ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧
      G3Inv E lc (kt.at e.b) s' osp ∧ e.b ∈ lc.ctx.f.blocks.toList ∧
      UOKL m' (uIn35 lc e.b) by
    obtain ⟨m', h1, h2, h3, h4, h5⟩ := key
    exact ⟨m', h1, h2, h3, fun ho => spInv_term (hsp ho) ht, h4, h5⟩
  cases hl : lc.ctx.f.lowered with
  | false =>
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g33_term (checkG33_of_62L hl hc) hE.env hbid hb hm hinv hpre
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
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, hedges, -, -,
    -⟩ := checkG62L_spec hl hc
  obtain ⟨m', h1, h2, h3, h4, he, hx⟩ := termK_stepX hpcOf
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb hm hinv hpre ht
  refine ⟨m', h1, h2, h3, h4, fun x hxin => ?_⟩
  exact uok_of_x hx (hu x (uEdgesOK35_edge hedges hbid hb he x hxin))

/-! ## The slice: the theorems on `checkG62 lc`, on `liveCtx lc` -/

/-- **G62, values.** `g61_value`'s statement over `checkG62`: G61's values (under `G54Pre`,
`RoPre56`, the contracts of the mode and `CallOKStk`) and the `Arg` of an incoming stack argument
(under `ArgOK`), in an activation whose `outargs` block sits at `SP` at the mode `true` (`hosp`,
`SPInv`), keeping `SPInv`. -/
theorem g62_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {osp : Bool}
    (hc : checkG62 lc ps bstart g = .ok (tab, kt)) (hE : G49Env (liveCtx lc) g L ps ret tab E)
    (hl : lc.ctx.f.lowered = true)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s osp)
    (hsp : osp = true → SPInv E s) (hosp : osp = true → E.outSP = true)
    (hn48 : needs48 (liveCtx lc) = true → osp = true)
    (hu : UOKL m (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk i))
    (hpre : G54Pre (liveCtx lc) s v) (hro : RoPre56 g s)
    (hcall : CallOKAt osp H E g L (liveCtx lc) s s' v m)
    (hcallz : CallOKZAt osp H E g L (liveCtx lc) s s' v m)
    (hicall : ICallOKAt osp H E L ret (liveCtx lc) s s' v m)
    (hwb : WbOKAt osp H E g L (liveCtx lc) s v m) (hclo : CloOK E s v m)
    (hgetg : GetGOK E v) (hmeq : MemEqOKAt osp H E g L (liveCtx lc) s v m)
    (hmp : MemEqPre (liveCtx lc) s v)
    (hcallk : osp = true → CallOKStk H E g L (liveCtx lc) s s' v m)
    (harg : ArgOK E (liveCtx lc) s v m)
    (hs : stepLoc env (liveCtx lc) s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env (liveCtx lc) g L ps ret tab E' ∧
      PStar H L ps.toList ret m m' ∧ LocMatch E' s' bid (i + 1) m' ∧
      G3Inv E' (liveCtx lc) (kAt (liveCtx lc) kt bid blk (i + 1)) s' osp ∧
      (osp = true → SPInv E' s') ∧
      UOKL m' (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk (i + 1)) :=
  g62L_value (checkG62_spec hc).2 hE hl hbid hb hi hv hen hm hinv hsp hosp hn48 hu hpre hro hcall
    hcallz hicall hwb hclo hgetg hmeq hmp hcallk harg hs

/-- **G62, `InitMem`.** `g61_initMem`'s statement over `checkG62`. -/
theorem g62_initMem {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {osp : Bool}
    (hc : checkG62 lc ps bstart g = .ok (tab, kt)) (hE : G49Env (liveCtx lc) g L ps ret tab E)
    (hl : lc.ctx.f.lowered = true)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .InitMem) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s osp)
    (hsp : osp = true → SPInv E s)
    (hpre : MemInit s) (hs : stepLoc env (liveCtx lc) s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env (liveCtx lc) g L ps ret tab E' ∧
      PStar H L ps.toList ret m m' ∧ LocMatch E' s' bid (i + 1) m' ∧
      G3Inv E' (liveCtx lc) (kAt (liveCtx lc) kt bid blk (i + 1)) s' osp ∧
      (osp = true → SPInv E' s') ∧
      UOKL m' (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk (i + 1)) :=
  g62L_initMem (checkG62_spec hc).2 hE hl hbid hb hi hv hop hm hinv hsp hpre hs

/-- **G62, nil panics.** `g61_nilPanic`'s statement over `checkG62`. -/
theorem g62_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG62 lc ps bstart g = .ok (tab, kt)) (hE : G49Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s osp)
    (hs : stepLoc env (liveCtx lc) s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e :=
  g62L_nilPanic (checkG62_spec hc).2 hE hbid hb hi hv hop hm hinv hs

/-- **G62, bounds panics.** `g61_boundsPanic`'s statement over `checkG62`. -/
theorem g62_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG62 lc ps bstart g = .ok (tab, kt)) (hE : G49Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s osp)
    (hbok : BoundsOK H g L ps.toList) (hs : stepLoc env (liveCtx lc) s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' :=
  g62L_boundsPanic (checkG62_spec hc).2 hE hbid hb hi hv hop hm hinv hbok hs

/-- **G62, terminators.** `g61_term`'s statement over `checkG62`, keeping `SPInv`. -/
theorem g62_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState} {osp : Bool}
    (hc : checkG62 lc ps bstart g = .ok (tab, kt)) (hE : G49Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk blk.values.size) s osp)
    (hsp : osp = true → SPInv E s) (hpre : G1TermPre (liveCtx lc) s blk)
    (hu : UOKL m (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk blk.values.size))
    (ht : stepTermLoc (liveCtx lc) s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧
      G3Inv E (liveCtx lc) (kt.at e.b) s' osp ∧ (osp = true → SPInv E s') ∧
      e.b ∈ lc.ctx.f.blocks.toList ∧
      UOKL m' (uIn35 (liveCtx lc) e.b) :=
  g62L_term (checkG62_spec hc).2 hE hbid hb hm hinv hsp hpre hu ht

end GoFV.Proof.Gen
