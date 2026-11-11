import GoFV.Proof.Gen.G65a

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G65 of the genssa validator: float loads of frame variables, float pair stores through a
register or to a global (`docs/plans/proofs3.md` §4)

`checkG65 lc` (`GoFV/Gen/Check65.lean`) is G64 with `FMOVSload`/`FMOVDload` of a frame variable
(`VK65.fvload`) and `FSTPS`/`FSTPD` at G3's operands (`off(Rn)`, `sym+off(SB)`; `VK65.fstp`). A
value of G64 is `vk64_step`'s; a float load of a frame variable is `g65_fvload`'s, a float pair
store `g65_fstpReg`'s or `g65_fstpGlob`'s (`G65a.lean`). The theorems are G64's over `checkG65`,
at either mode `osp`, with G64's premises: the float loads take G44's `FLoadPre`, part of
`G54Pre`.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## One value -/

/-- One value of G65's kinds: `vk64_step`'s statement. -/
theorem vk65_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)} {osp : Bool}
    (hE : G49Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK65 lc g v kd)
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
    (hcallk : osp = true → CallOKStk H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (harg : ArgOK E lc s v m) (hfr : FReloadPre lc s v)
    (hq : QLoadPre lc s v)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp ∧
      UOKL m' (uStep35 lc L v) := by
  have hR := kread_of_reads hreads
  have hempty : ∀ m', UOKL m' [] := fun _ e he => by cases he
  obtain ⟨hlcE, -, -, -, -, hglob, -, -, -, -, hF⟩ := hE.env.env.env.env.env
  have hsz := slot_sizes hlcE hcf hinv.slots
  cases hVK with
  | g64 hVK64 =>
    exact vk64_step hE F hhome hcf hv hVK64 hvs hloop hatom hj hj' hreads hm hinv hL hmem hpre hro
      h48 hsp hcall hcallz hicall hwb hclo hgetg hmeq hcallk harg hfr hq hs
  | fvload hfv htemp hop hsz2 hma hro' =>
    obtain ⟨r, hvh, -, -, -⟩ := fresObj_spec hro'
    obtain ⟨bk, hB⟩ := varAt57 hE hv hfv
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g65_fvload (H := H) F hm hinv.core hinv.slots
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hpre.1.1.1.1.1.1.2 hj hj' hB hop hsz2 hma hro'
      hvs htemp hs
    refine ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩, ?_⟩
    rw [uStep35_f44 (by rcases hop with h | h <;> simp [FOp44, h])]
    exact hempty m'
  | fstp htemp hop hsz4 hmt hhn hxo hyo hma hacc =>
    obtain ⟨P, hP, hPs⟩ := accessA_spec hacc
    obtain ⟨m', h1, h2, h3, h4⟩ : ∃ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret
        m m' ∧ LocMatch E s' bid (i + 1) m' ∧ CoreInv E.ι (StkAt E) (kStep lc K v).get s' osp ∧
        SlotInv lc s' := by
      cases hP with
      | reg hax hao =>
        exact g65_fstpReg (H := H) F hF hsz hm hinv.core hinv.slots hR
          (knext_kStep fun _ => (hs_none hhn).noRegs) hj hj' hop hsz4 hax hmt hhn hao hxo hyo hma
          (fun A h => hPs A h) hvs htemp hs
      | glob hx _ _ hsy =>
        exact g65_fstpGlob (H := H) F hF hsz (fun y name abi h => hglob y name abi h) hm
          hinv.core hinv.slots hR (knext_kStep fun _ => (hs_none hhn).noRegs) hj hj' hop hx hsy
          hsz4 hmt hhn hxo hyo hma (fun A h => hPs A h) hvs htemp hs
    refine ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩, ?_⟩
    rw [uStep35_57b (fstpOf_mem hop)]
    exact hempty m'

/-- A nil check of G65's kinds is G7's. -/
theorem vk65_nil {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK65 lc g v kd)
    (hop : v.op = .ARM64LoweredNilCheck) : VK7 lc g v kd := by
  cases h with
  | g64 h => exact vk64_nil h hop
  | fvload _ _ hop' => rcases hop' with h | h <;> rw [h] at hop <;> cases hop
  | fstp _ hop' =>
    rcases fstpOf_some hop' with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] at hop <;> cases hop

/-- A bounds check of G65's kinds is G28's. -/
theorem vk65_pb {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK65 lc g v kd)
    (hop : pbOp v.op = true) : VK28 lc g v kd := by
  cases h with
  | g64 h => exact vk64_pb h hop
  | fvload _ _ hop' => rcases hop' with h | h <;> rw [h] at hop <;> cases hop
  | fstp _ hop' =>
    rcases fstpOf_some hop' with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] at hop <;> cases hop

/-! ## The theorems on G65's check -/

/-- G64's values and G65's float accesses under G65's check at either mode `osp` (the
mode `true` for a function that needs G48's mode, `hn48`; there the `outargs` block sits at `SP`,
`hosp`, `SPInv`, kept), under G64's premises. -/
theorem g65L_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {osp : Bool}
    (hc : checkG65L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
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
    (hmeq : MemEqOKAt osp H E g L lc s v m) (hcallk : osp = true → CallOKStk H E g L lc s s' v m)
    (harg : ArgOK E lc s v m) (hfr : FReloadPre lc s v) (hq : QLoadPre lc s v)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' osp ∧
      (osp = true → SPInv E' s') ∧ UOKL m' (uL35 lc (uIn35 lc bid) blk (i + 1)) := by
  have hsh : spHomes48 lc = true := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := checkG65L_spec hl hc
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
    -, hat⟩ := checkG65L_spec hl hc
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
  have hVK := vkind65_spec hkd hen
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
  exact vk65_step hE0 F hhome hcf hv hVK hvs hloop hatom hj hj' hreads hm hinv hu
    (fun x hop hx => movdOK35_spec hmovd hbid hb hi hv hop hx)
    hpre hro h48 (fun ho => ⟨hsp ho, hosp ho⟩) hcall hcallz hicall hwb hclo hgetg hmeq hcallk harg
    hfr hq hs

/-- `InitMem` under G65's check: `g64L_initMem`'s statement over `checkG65L`. -/
theorem g65L_initMem {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {osp : Bool}
    (hc : checkG65L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
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
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := checkG65L_spec hl hc
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
    checkG65L_spec hl hc
  obtain ⟨b, j, js, e, next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk, vkind65_initMem hop, vkind64_initMem hop, vkind63_initMem hop, vkind62_initMem hop,
    vkind61_initMem hop, vkind60_initMem hop,
    vkind59_initMem hop, vkind58_initMem hop]
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

/-- G38's nil panics under G65's check. -/
theorem g65L_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG65L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s osp) (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  cases hl : lc.ctx.f.lowered with
  | false => exact g33_nilPanic (checkG33_of_65L hl hc) hE.env hbid hb hi hv hop hm hinv hs
  | true =>
  obtain ⟨⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, -, -, -, -⟩ :=
    checkG65L_spec hl hc
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
  have hVK := vkind65_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases vk65_nil hVK hop with
  | g6 hne _ => exact absurd hop hne
  | nil _ hsz2 _ _ hao hma =>
    exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao hma hvs hs

/-- G38's bounds panics under G65's check. -/
theorem g65L_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG65L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s osp) (hbok : BoundsOK H g L ps.toList)
    (hs : stepLoc env lc s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    exact g33_boundsPanic (checkG33_of_65L hl hc) hE.env hbid hb hi hv hop hm hinv hbok hs
  | true =>
  obtain ⟨⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, hsyms, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, hpb, -, -, -, -, -⟩ :=
    checkG65L_spec hl hc
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
  have hVK := vkind65_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  exact vk28_boundsPanic F hsyms hpb hrow hb hi hv (vk65_pb hVK hop) hvs hj hreads hop hm hinv
    hbok hs

/-- G38's terminators under G65's check, keeping `SPInv`. -/
theorem g65L_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState} {osp : Bool}
    (hc : checkG65L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
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
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g33_term (checkG33_of_65L hl hc) hE.env hbid hb hm hinv hpre
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
    -⟩ := checkG65L_spec hl hc
  obtain ⟨m', h1, h2, h3, h4, he, hx⟩ := termK_stepX hpcOf
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb hm hinv hpre ht
  refine ⟨m', h1, h2, h3, h4, fun x hxin => ?_⟩
  exact uok_of_x hx (hu x (uEdgesOK35_edge hedges hbid hb he x hxin))

/-! ## The slice: the theorems on `checkG65 lc`, on `liveCtx lc` -/

/-- **G65, values.** `g64_value`'s statement over `checkG65`: G64's values (under `G54Pre`,
`RoPre56`, the contracts of the mode, `CallOKStk`, `ArgOK`, `FReloadPre` and `QLoadPre`) and
G65's float loads of frame variables (under `G54Pre`'s `FLoadPre`) and float pair stores, in an
activation whose `outargs` block sits at `SP` at the mode `true` (`hosp`, `SPInv`), keeping
`SPInv`. -/
theorem g65_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {osp : Bool}
    (hc : checkG65 lc ps bstart g = .ok (tab, kt)) (hE : G49Env (liveCtx lc) g L ps ret tab E)
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
    (hcallk : osp = true → CallOKStk H E g L (liveCtx lc) s s' v m)
    (harg : ArgOK E (liveCtx lc) s v m) (hfr : FReloadPre (liveCtx lc) s v)
    (hq : QLoadPre (liveCtx lc) s v)
    (hs : stepLoc env (liveCtx lc) s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env (liveCtx lc) g L ps ret tab E' ∧
      PStar H L ps.toList ret m m' ∧ LocMatch E' s' bid (i + 1) m' ∧
      G3Inv E' (liveCtx lc) (kAt (liveCtx lc) kt bid blk (i + 1)) s' osp ∧
      (osp = true → SPInv E' s') ∧
      UOKL m' (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk (i + 1)) :=
  g65L_value (checkG65_spec hc).2 hE hl hbid hb hi hv hen hm hinv hsp hosp hn48 hu hpre hro hcall
    hcallz hicall hwb hclo hgetg hmeq hcallk harg hfr hq hs

/-- **G65, `InitMem`.** `g64_initMem`'s statement over `checkG65`. -/
theorem g65_initMem {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {osp : Bool}
    (hc : checkG65 lc ps bstart g = .ok (tab, kt)) (hE : G49Env (liveCtx lc) g L ps ret tab E)
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
  g65L_initMem (checkG65_spec hc).2 hE hl hbid hb hi hv hop hm hinv hsp hpre hs

/-- **G65, nil panics.** `g64_nilPanic`'s statement over `checkG65`. -/
theorem g65_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG65 lc ps bstart g = .ok (tab, kt)) (hE : G49Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s osp)
    (hs : stepLoc env (liveCtx lc) s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e :=
  g65L_nilPanic (checkG65_spec hc).2 hE hbid hb hi hv hop hm hinv hs

/-- **G65, bounds panics.** `g64_boundsPanic`'s statement over `checkG65`. -/
theorem g65_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG65 lc ps bstart g = .ok (tab, kt)) (hE : G49Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s osp)
    (hbok : BoundsOK H g L ps.toList) (hs : stepLoc env (liveCtx lc) s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' :=
  g65L_boundsPanic (checkG65_spec hc).2 hE hbid hb hi hv hop hm hinv hbok hs

/-- **G65, terminators.** `g64_term`'s statement over `checkG65`, keeping `SPInv`. -/
theorem g65_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState} {osp : Bool}
    (hc : checkG65 lc ps bstart g = .ok (tab, kt)) (hE : G49Env (liveCtx lc) g L ps ret tab E)
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
  g65L_term (checkG65_spec hc).2 hE hbid hb hm hinv hsp hpre hu ht

end GoFV.Proof.Gen
