import GoFV.Proof.Gen.Keep31
import GoFV.Proof.Gen.Spec31

variable [GoFV.SSA.Sem.Addrs]

/-!
# Soundness of the genssa validator's slice G31: the upper-bit table across values and blocks
(`docs/plans/proofs3.md` §4)

`g31_value`, `g31_term`, `g31_nilPanic`, `g31_boundsPanic`: `g32_value`'s, `g32_term`'s,
`g32_nilPanic`'s and `g32_boundsPanic`'s statements over `checkG31`, with the upper-bit table
`uL31` in place of G29's `uL`. `g31_value` carries `UOKL m (uL31 lc (uIn lc bid) blk i)` to value
`i + 1`; `g31_term` takes the table at the block's end and gives the successor's start
`UOKL m' (uIn lc e.b)`. `uIn lc entry = []` (`uEdgesOK_entry`), so the premise is trivial at the
function's entry.

Across a value that `keep31` keeps the table for (G1's kinds and G3's `CMPW`/`CMPWconst`), the
value is G3's (`vk32_vk3`, `GoFV/Proof/Gen/Keep31.lean`), and its step writes at most its register
home's X register (`XW`: `g2_g1`, `g3_cmpw`, `g3_cmpwK`; `vk3_keep`), so the entries of the other
registers stay true (`uokl_keep`). Every other value steps as in G32 (`vk32_stepU`; `uStep31` is
`uStepL` there). A terminator keeps every X register (`termK_stepX`), and each successor's start is
in the end of its predecessor (`uEdgesOK_edge`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The table -/

/-- `UOK` reads only the X registers. -/
theorem uok_of_x {m m' : MState} {e : Option (Nat × Nat × Bool)} (hx : m'.x = m.x) (h : UOK m e) :
    UOK m' e := by
  cases e with
  | none => trivial
  | some e =>
    obtain ⟨r, c, sg⟩ := e
    intro k hk ho
    rw [hx]
    exact h k hk ho

theorem uokl_of_x {m m' : MState} {L : List (Nat × Nat × Bool)} (hx : m'.x = m.x) (h : UOKL m L) :
    UOKL m' L := fun e he => uok_of_x hx (h e he)

/-- The table across a value `keep31` keeps it for. -/
theorem uStep31_keep {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value} (hk : keep31 v = true) :
    uStep31 lc L v = L.filter fun e => regHome? lc v.id != some e.1 := by
  simp [uStep31, hk]

/-- The table across any other value: G29's step. -/
theorem uStep31_other {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value}
    (hk : keep31 v = false) : uStep31 lc L v = uStepL lc L v := by
  simp [uStep31, hk]

/-- The entries of the registers a value does not write stay true across it (`XW`). -/
theorem uokl_keep {lc : LocCtx} {v : Value} {m m' : MState} {L : List (Nat × Nat × Bool)}
    (hL : UOKL m L) (hx : XW lc v m m') :
    UOKL m' (L.filter fun e => regHome? lc v.id != some e.1) := by
  rcases hx with hx | ⟨r, kd, val, hh, hor, hx⟩
  · intro e he
    exact uok_of_x hx (hL e (List.mem_filter.1 he).1)
  · have hf : (L.filter fun e => regHome? lc v.id != some e.1) = L.filter (·.1 != r) := by
      rw [regHome?_eq.2 hh]
      apply List.filter_congr
      intro e _
      by_cases h : e.1 = r
      · simp [h]
      · have h1 : (e.1 != r) = true := bne_iff_ne.2 h
        have h2 : (some r != some e.1) = true := bne_iff_ne.2 fun h' => h (Option.some.inj h').symm
        rw [h1, h2]
    rw [hf]
    exact uokl_filter hL (keepsX_wX hor hx)

/-! ## A value the table is kept across -/

/-- A value of G3's kinds that `keep31` keeps the table across: G1's step (through G2) or a 32-bit
compare, which writes at most its register home's X register (`XW`). -/
theorem vk3_keep {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2}
    (hE : G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hcf : checkFrame lc g = .ok ())
    (hVK : VK3 lc g v kd) (hk : keep31 v = true)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s) (hpre : G14Pre lc s v)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E s' bid (i + 1) m' ∧ G3Inv E lc (kStep lc K v) s' ∧ XW lc v m m' := by
  obtain ⟨hlcE, -, -, -, -, -, -, -, -, -, hF⟩ := hE.env.env.env.env
  have hsz := slot_sizes hlcE hcf hinv.slots
  have hR := kread_of_reads hreads
  have hops : keepOp31 v.op = true ∨
      ((v.op = .ARM64MOVDload ∨ v.op = .ARM64MOVDstore) ∧ v.aux = none) := by
    unfold keep31 at hk
    simpa [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] using hk
  have hko : ∀ o : Op, keepOp31 o = false → o ≠ .ARM64MOVDload → o ≠ .ARM64MOVDstore →
      v.op ≠ o := by
    rintro o h1 h2 h3 rfl
    rcases hops with h | ⟨h | h, -⟩
    · rw [h1] at h; cases h
    · exact h2 h
    · exact h3 h
  have hnc : v.op ≠ .ARM64CALLstatic := hko _ rfl nofun nofun
  have hK : KNext lc v K.get (kStep lc K v).get :=
    knext_kStep fun hnp => (vk3_noRes hVK hnc hnp).noRegs
  cases hVK with
  | g2 hops3 _ hVK2 =>
    cases hVK2 with
    | g1 _ _ _ _ _ hvk =>
      have haux : v.op = .ARM64MOVDload → v.aux = none := by
        intro hop
        rcases hops3 with ⟨hl0, -⟩ | ⟨-, hx⟩
        · rw [hop] at hl0; simp [loadOp?] at hl0
        · exact hx
      obtain ⟨m', h1, h2, h3, h4, h5⟩ := g2_g1 (H := H) F hF hsz hm hinv.core hinv.slots hj hj'
        hvs hvk htemp (hpre.1.1.1.1.g1 haux) hR hK hs
      exact ⟨m', h1, h2, ⟨h3, h4⟩, h5⟩
    | call hop => exact absurd hop hnc
    | selMem hop => exact absurd hop (hko _ rfl nofun nofun)
    | selReg hop => exact absurd hop (hko _ rfl nofun nofun)
    | addr hop => exact absurd hop (hko _ rfl nofun nofun)
    | spill hop => exact absurd hop (hko _ rfl nofun nofun)
    | reload hop => exact absurd hop (hko _ rfl nofun nofun)
  | load hop hmovd =>
    rcases hops with h | ⟨h | h, hx⟩
    · rcases loadOp?_op hop with ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ |
        ⟨h', -⟩ <;> rw [h'] at h <;> cases h
    · rw [h] at hop
      simp only [loadOp?, beq_self_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hop
      exact absurd hx (hmovd hop.1.symm)
    · rw [h] at hop; simp [loadOp?, narrowLoad?] at hop
  | store hop hmovd =>
    rcases hops with h | ⟨h | h, hx⟩
    · rcases storeOp?_op hop with ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ | ⟨h', -⟩ <;> rw [h'] at h <;>
        cases h
    · rw [h] at hop; simp [storeOp?, narrowStore?] at hop
    · rw [h] at hop
      simp only [storeOp?, beq_self_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hop
      exact absurd hx (hmovd hop.1.symm)
  | sb hop => exact absurd hop (hko _ rfl nofun nofun)
  | ext he =>
    rcases extOp?_op he with h | h | h | h | h | h <;> exact absurd h (hko _ rfl nofun nofun)
  | aluK hop =>
    rcases hop with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> exact absurd h (hko _ rfl nofun nofun)
  | ubfx hop => exact absurd hop (hko _ rfl nofun nofun)
  | cmpw hop hsz2 hfl hhn hao hbo hca hcb =>
    obtain ⟨m', h1, h2, h3, h4, h5⟩ := g3_cmpw (H := H) F hm hinv.core hinv.slots hR hK hj hj'
      hop hsz2 hfl hhn hao hbo hca hcb hvs htemp hs
    exact ⟨m', h1, h2, ⟨h3, h4⟩, .inl h5⟩
  | cmpwK hop hsz1 hfl hhn hao hca =>
    obtain ⟨m', h1, h2, h3, h4, h5⟩ := g3_cmpwK (H := H) F hm hinv.core hinv.slots hR hK hj hj'
      hop hsz1 hfl hhn hao hca hvs htemp hs
    exact ⟨m', h1, h2, ⟨h3, h4⟩, .inl h5⟩

/-- One value of G32's kinds: `vk32_stepU`'s statement over G31's table step `uStep31`. -/
theorem vk31_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)}
    (hE : G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK32 lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s) (hL : UOKL m L)
    (hmem : ∀ x, (v.op = .ARM64MOVDnop ∨ v.op = .ARM64MOVDreg) → v.args[0]? = some x →
      ∃ r c, regHome? lc x = some r ∧ cls (lc.ty x) = some c ∧
        (r, c, lc.signOf lc.ctx.f.valueTab.size x) ∈ L)
    (hpre : G14Pre lc s v)
    (hcall : CallOK H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hcallz : CallOKZ H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hicall : ICallOK H E (Link.byId sym text az ez ps.toList) ret lc s s' v m)
    (hwb : WbOK H E g (Link.byId sym text az ez ps.toList) lc s v m) (hclo : CloOK E s v m)
    (hgetg : GetGOK E v) (hmeq : MemEqOK H E g (Link.byId sym text az ez ps.toList) lc s v m)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' ∧
      UOKL m' (uStep31 lc L v) := by
  cases hk : keep31 v with
  | true =>
    obtain ⟨m', h1, h2, h3, h4⟩ := vk3_keep hE F hcf (vk32_vk3 hVK hk) hk hvs htemp hj hj' hreads
      hm hinv hpre hs
    refine ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, h3, ?_⟩
    rw [uStep31_keep hk]
    exact uokl_keep hL h4
  | false =>
    rw [uStep31_other hk]
    exact vk32_stepU hE F hhome hcf hv hVK hvs htemp hj hj' hreads hm hinv hL hmem hpre hcall
      hcallz hicall hwb hclo hgetg hmeq hs

/-- On a function with no arm64 op that `checkNL30` accepted, G29's table is empty: no value is a
narrow load, `MOVDnop` or `MOVDreg`. -/
theorem uL_nl30 {lc : LocCtx} {ps : Array Prog} {bstart : ID → Option Nat} {g : G2In}
    {tab : PcTab} {kt : KTab} {bid : ID} {blk : Block}
    (hc : checkNL30 lc ps bstart g = .ok (tab, kt))
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk) :
    ∀ i, uL lc blk i = []
  | 0 => rfl
  | i + 1 => by
    cases hi : blk.values[i]? with
    | none => simp [uL, hi]
    | some id =>
      cases hv : lc.ctx.f.value? id with
      | none => simp [uL, hi, hv]
      | some v =>
        rw [uL_succ hi hv]
        have hops : v.op = .MakeResult ∨ v.op = .InlMark ∨ v.op = .Copy ∨ v.op = .Convert ∨
            v.op = .InitMem ∨ v.op = .ArgIntReg ∨ v.op = .ArgFloatReg := by
          cases hen : entryOp24 v.op with
          | false =>
            rcases nl30_ops hc hbid hb hi hv hen with h | h | h | h <;> simp [h]
          | true =>
            unfold entryOp24 entryOp3 entryOp at hen
            revert hen
            cases v.op <;> simp
        have hnl : narrowLd? lc v = none := by
          rcases hops with h | h | h | h | h | h | h <;> · unfold narrowLd?; rw [h]; rfl
        apply uStepL_other (by simp only [uEntry, hnl])
        · rcases hops with h | h | h | h | h | h | h <;> rw [h] <;> nofun
        · rcases hops with h | h | h | h | h | h | h <;> rw [h] <;> nofun

/-! ## The theorems -/

/-- **G31, values.** `g32_value`'s statement over `checkG31`, carrying the upper-bit invariant
`UOKL` of G31's table `uL31` (started from `uIn lc bid`) from value `i` to value `i + 1`. -/
theorem g31_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG31 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hu : UOKL m (uL31 lc (uIn lc bid) blk i))
    (hpre : G14Pre lc s v)
    (hcall : CallOK H E g L lc s s' v m) (hcallz : CallOKZ H E g L lc s s' v m)
    (hicall : ICallOK H E L ret lc s s' v m)
    (hwb : WbOK H E g L lc s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hmeq : MemEqOK H E g L lc s v m) (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' ∧
      UOKL m' (uL31 lc (uIn lc bid) blk (i + 1)) := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    have hc30 : checkG30 lc ps bstart g = .ok (tab, kt) := by
      have := checkG31_nl hl hc
      simpa [checkG30, hl] using this
    obtain ⟨E', m', hx, hE', h1, h2, h3, -⟩ := g30_value hc30 hE hbid hb hi hv hen hm hinv
      (by rw [uL_nl30 (checkG31_nl hl hc) hbid hb i]; intro e he; cases he) hpre hcall hcallz
      hicall hwb hclo hgetg hmeq hs
    refine ⟨E', m', hx, hE', h1, h2, h3, ?_⟩
    rw [uL31_nl hl]
    intro e he
    cases he
  | true =>
  rw [uL31_succ hl hi hv]
  have hE0 := hE
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, hcf, hk, hlt, hnd, hblocks, -, hmovd, -⟩ :=
    checkG31_spec hl hc
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
  obtain ⟨htemp, hVK⟩ := vkind32_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  rw [kAt_succ hi hv]
  exact vk31_step hE0 F hhome hcf hv hVK hvs htemp hj hj' hreads hm hinv hu
    (fun x hop hx => movdOK31_spec hmovd hbid hb hi hv hop hx)
    hpre hcall hcallz hicall hwb hclo hgetg hmeq hs

/-- **G31, nil panics.** `g32_nilPanic`'s statement over `checkG31`. -/
theorem g31_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG31 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    rcases nl30_ops (checkG31_nl hl hc) hbid hb hi hv (by rw [hop]; rfl) with h | h | h | h <;>
      rw [h] at hop <;> cases hop
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, -⟩ :=
    checkG31_spec hl hc
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
  obtain ⟨-, hVK⟩ := vkind32_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases vk32_nil hVK hop with
  | g6 hne _ => exact absurd hop hne
  | nil _ hsz2 _ _ hao hma =>
    exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao hma hvs hs

/-- **G31, bounds panics.** `g32_boundsPanic`'s statement over `checkG31`, under `BoundsOK`. -/
theorem g31_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG31 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hbok : BoundsOK H g L ps.toList)
    (hs : stepLoc env lc s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    have hen : entryOp24 v.op = false := by
      rcases pbOp_cases hop with h | h | h | h <;> rw [h] <;> rfl
    rcases nl30_ops (checkG31_nl hl hc) hbid hb hi hv hen with h | h | h | h <;> rw [h] at hop <;>
      cases hop
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, hsyms, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, hpb, -, -⟩ :=
    checkG31_spec hl hc
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
  obtain ⟨-, hVK⟩ := vkind32_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases hVK with
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

/-- **G31, terminators.** `g32_term`'s statement over `checkG31`, taking the upper-bit invariant of
the table at the block's end and giving it for the successor's start `uIn lc e.b`. -/
theorem g31_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG31 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s) (hpre : G1TermPre lc s blk)
    (hu : UOKL m (uL31 lc (uIn lc bid) blk blk.values.size))
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' ∧
      e.b ∈ lc.ctx.f.blocks.toList ∧ UOKL m' (uIn lc e.b) := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    obtain ⟨-, -, -, -, -, -, -, hr, -⟩ := checkNL30_spec (checkG31_nl hl hc)
    obtain ⟨R, -, hn⟩ := stepTermLoc_gen ht
    exact (stepTermL_ret (allRet_spec hr hbid hb) hn).elim
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, hedges⟩ :=
    checkG31_spec hl hc
  obtain ⟨m', h1, h2, h3, h4, he, hx⟩ := termK_stepX hpcOf
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb hm hinv hpre ht
  refine ⟨m', h1, h2, h3, h4, fun x hxin => ?_⟩
  exact uok_of_x hx (hu x (uEdgesOK_edge hedges hbid hb he x hxin))

end GoFV.Proof.Gen
