import GoFV.Proof.Gen.G10
import GoFV.Proof.Gen.Spec11

/-!
# Soundness of the genssa validator's slice G11: the closure context (`docs/plans/proofs3.md` §4)

`g11_value`, `g11_term`, `g11_nilPanic`: `g10_value`'s, `g10_term`'s and `g10_nilPanic`'s
statements over `checkG11`, `g11_value` with the trusted premise `CloOK` (listed in
`docs/proofs/STATUS.md` Assumptions): at `LoweredGetClosurePtr`, `X26` holds the activation's
closure context, a 64-bit word.

`LoweredGetClosurePtr` runs under `runLoc` as `arm64Op`'s read of the activation's closure context
`fr.closure` (`poison` outside a closure call), written to its home `R26` (`stepLoc_clo`); genssa
emits no code for it. Go's internal ABI passes the closure context in `R26`; `checkG11` places the
value in the entry block after the register arguments only (`cloFirst`, as genssa's
`CheckLoweredGetClosurePtr`), so no code but the prologue (whose `morestack` path keeps the
context) runs before it, and `CloOK` is the entry's `R26` (`g11_clo`: the machine does not move).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm

/-! ## The premise -/

/-- **The closure context at entry** (trusted; `docs/proofs/STATUS.md` Assumptions): at
`LoweredGetClosurePtr`, `X26` holds the activation's closure context (`fr.closure`, `poison`
outside a closure call), a 64-bit word. -/
def CloOK (E : MatchEnv) (s : LocState) (v : Value) (m : MState) : Prop :=
  v.op = .ARM64LoweredGetClosurePtr →
    Fits 64 (s.fr.closure.getD .poison) ∧ ValRel E.ι (s.fr.closure.getD .poison) (m.x 26)

/-! ## `stepLoc` of `LoweredGetClosurePtr` -/

section Step

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

/-- `LoweredGetClosurePtr` writes the closure context to its home. -/
theorem stepLoc_clo (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .ARM64LoweredGetClosurePtr) (hsz0 : v.args.size = 0)
    (h : stepLoc env lc s v = .ok s') :
    s' = s.write lc v.id ((s.fr.closure.getD .poison).retypeL (lc.ty v.id)) := by
  obtain ⟨argv, r, hmv, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
    (by rw [hop]; decide) (by rw [hop]; decide) (by rw [hop]; decide) (by rw [hop]; decide) h
  have hargs : v.args = #[] := Array.eq_empty_of_size_eq_zero hsz0
  rw [hargs] at hmv
  change Res.ok [] = Res.ok argv at hmv
  cases hmv
  have hnf : nilFaults true lc.ctx v [] = none := rfl
  have he : evalOpL true env lc.ctx s.fr v [] (lc.ty v.id) = .ok (s.fr.closure.getD .poison) := by
    unfold evalOpL arm64Op
    simp only [hop, hnf]
    rfl
  rw [he] at hr
  cases hr
  rfl

end Step

/-! ## The value -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- `LoweredGetClosurePtr` homed in `R26`: no code; `X26` holds the closure context (`CloOK`). -/
theorem g11_clo (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    (hop : v.op = .ARM64LoweredGetClosurePtr) (hsz0 : v.args.size = 0)
    (hvh : lc.home v.id = some (.reg ctxReg)) (hcv : cls (lc.ty v.id) = some 64)
    (hvs : j' = j) (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s')
    (hclo : CloOK E s v m) :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  rw [stepLoc_clo hl htemp hop hsz0 hs, write_reg hvh hcv]
  obtain ⟨hfit, hval⟩ := hclo hop
  have hrel : ValRel E.ι ((s.fr.closure.getD .poison).retypeL (lc.ty v.id))
      (m.rX (BitVec.ofNat 5 26)) := by
    rw [rX_lt (by decide)]
    exact valRel_retypeL hA hcv hfit hval
  obtain ⟨hlm, hinv'⟩ := finish_reg hm hinv (by decide : destOK ctxReg = true)
    (by decide : 26 < 32) (by decide : objOf? ctxReg = some (GoFV.Asm.ARM64.REG_R0 + 26)) hrel
    (fits_retypeL hcv _) (b' := b) (i' := i + 1)
  rw [wX_rX_self, hj', hvs, ← hj, ← hm.pc] at hlm
  exact ⟨m, .refl, hlm, hinv'.mono (knext_set hK (by rw [hop]; nofun) hvh hcv), hsi⟩

end Cases

/-! ## The theorems -/

/-- One value of G11's kinds (`VK11`) emitted at the Progs from `j` to `j'`: `vk10_step`'s
statement for G11's values, with the closure context premise `CloOK`. -/
theorem vk11_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2}
    (hE : G10Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK11 lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s) (hpre : G7Pre lc s v)
    (hcall : CallOK H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hicall : ICallOK H E (Link.byId sym text az ez ps.toList) ret lc s s' v m)
    (hwb : WbOK H E g (Link.byId sym text az ez ps.toList) lc s v m) (hclo : CloOK E s v m)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G10Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' := by
  cases hVK with
  | g10 hVK10 =>
    exact vk10_step hE F hhome hcf hv hVK10 hvs htemp hj hj' hreads hm hinv hpre hcall hicall hwb
      hs
  | clo hop hsz0 hvh hcv =>
    obtain ⟨m', h1, h2, h3, h4⟩ := g11_clo (H := H) F hm hinv.core hinv.slots
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz0 hvh hcv hvs htemp hs hclo
    exact ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩⟩

/-- **G11, values.** `g10_value`'s statement over `checkG11`, with the trusted closure context
premise `CloOK` next to `CallOK`, `ICallOK` and `WbOK`. -/
theorem g11_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG11 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp3 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hpre : G7Pre lc s v)
    (hcall : CallOK H E g L lc s s' v m) (hicall : ICallOK H E L ret lc s s' v m)
    (hwb : WbOK H E g L lc s v m) (hclo : CloOK E s v m) (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G10Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' := by
  have hE0 := hE
  obtain ⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, hcf, hk, hlt, hnd, hblocks⟩ := checkG11_spec hc
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
  obtain ⟨htemp, hVK⟩ := vkind11_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  rw [kAt_succ hi hv]
  exact vk11_step hE0 F hhome hcf hv hVK hvs htemp hj hj' hreads hm hinv hpre hcall hicall hwb hclo
    hs

/-- **G11, nil panics.** `g10_nilPanic`'s statement over `checkG11`. -/
theorem g11_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG11 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  obtain ⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks⟩ := checkG11_spec hc
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
  obtain ⟨-, hVK⟩ := vkind11_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases hVK with
  | g10 hVK10 =>
    cases hVK10 with
    | g9 hVK9 =>
      cases hVK9 with
      | g8 _ hVK8 =>
        cases hVK8 with
        | g7 hVK7 =>
          cases hVK7 with
          | g6 hne _ => exact absurd hop hne
          | nil _ hsz2 _ _ hao hma =>
            exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao
              hma hvs hs
        | wb hop' => rw [hop] at hop'; cases hop'
        | sel0 hop' => rw [hop] at hop'; cases hop'
        | sel1 hop' => rw [hop] at hop'; cases hop'
      | call hop' => rw [hop] at hop'; cases hop'
    | icall hn => rw [hop] at hn; cases hn
    | selMem hop' => rw [hop] at hop'; cases hop'
    | selReg hop' => rw [hop] at hop'; cases hop'
  | clo hop' => rw [hop] at hop'; cases hop'

/-- **G11, terminators.** `g10_term`'s statement over `checkG11`. -/
theorem g11_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG11 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s) (hpre : G1TermPre lc s blk)
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' ∧
      e.b ∈ lc.ctx.f.blocks.toList := by
  obtain ⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome, -, hk, hlt, hnd, hblocks⟩ := checkG11_spec hc
  exact termK_step hpcOf ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb
    hm hinv hpre ht

end GoFV.Proof.Gen
