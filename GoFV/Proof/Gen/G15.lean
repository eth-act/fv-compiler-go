import GoFV.Proof.Gen.G14
import GoFV.Proof.Gen.Spec15

variable [GoFV.SSA.Sem.Addrs]

/-!
# Soundness of the genssa validator's slice G15: zero-sized stack arguments (proofs3 §4)

`g15_value`, `g15_term`, `g15_nilPanic`: `g14_value`'s, `g14_term`'s and `g14_nilPanic`'s
statements over `checkG15`. A static call whose ABI assigns zero-sized inputs to the stack passes
no byte for them: genssa emits the same `CALL sym(SB)` as for a call with register arguments only,
and `checkG15` checks it as G9 does on the ABI without those inputs (`callRegsZ`). The proof is
`g2_call`'s (`g2_callAt`), with the callee contract for such calls: `CallOKZ`, `CallOK` with
`callRegsZ` in place of `callRegs` (a trusted premise next to `CallOK`; STATUS Assumptions).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm

/-- The callee contract (`CallAt`) at the static call `v` from `s` (to `s'`) whose register
arguments and results `callRegsZ` gives (the ABI without its zero-sized stack inputs). -/
def CallOKZ (H : Hooks) (E : MatchEnv) (g : G2In) (L : Link) (lc : LocCtx) (s s' : LocState)
    (v : Value) (m : MState) : Prop :=
  v.op = .ARM64CALLstatic → ∀ name abi cabi ins outs,
    callOf? lc.ctx.tabs v.aux = some (name, abi, cabi) →
    callRegsZ lc.ctx.tabs cabi = .ok (ins, outs) → CallAt H E g L lc s s' v m name abi ins outs

/-- One value of G15's kinds (`VK15`) emitted at the Progs from `j` to `j'`: `vk14_step`'s
statement for G15's values, with the contract `CallOKZ` of their static calls. -/
theorem vk15_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2}
    (hE : G10Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK15 lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s) (hpre : G14Pre lc s v)
    (hcall : CallOK H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hcallz : CallOKZ H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hicall : ICallOK H E (Link.byId sym text az ez ps.toList) ret lc s s' v m)
    (hwb : WbOK H E g (Link.byId sym text az ez ps.toList) lc s v m) (hclo : CloOK E s v m)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G10Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' := by
  cases hVK with
  | g14 _ hVK14 =>
    exact vk14_step hE F hhome hcf hv hVK14 hvs htemp hj hj' hreads hm hinv hpre hcall hicall
      hwb hclo hs
  | call hop hcall' hcr hnd _ _ _ h16 hlen hargs hres hct =>
    have hE0 := hE.env.env.env
    obtain ⟨hlcE, -, -, -, -, -, hsyms, hcalls, -, -, hF⟩ := hE.env.env.env
    have hframed : E.framed = true := by
      cases hfr : E.framed
      · exact absurd hop (hcalls hfr id v hv)
      · rfl
    have hnp : v.op ≠ .Phi := by rw [hop]; nofun
    obtain ⟨ι', hext', hA', m', hstar, hlm, hcore', hsl'⟩ := g2_callAt (H := H) F hF hlcE hcf
      hframed hsyms hm hinv.core hinv.slots (kread_of_reads hreads) hj hj' hop h16 hlen hargs hres
      hct (kcall_kStep hnp hres hnd (callTy_len hct)) (fun _ hp => callPat_spec hp) hvs htemp hs
      (hcallz hop _ _ _ _ _ hcall' hcr)
    have hx : E.Extends { E with ι := ι' } := ⟨rfl, hext'⟩
    exact ⟨_, m', hx, hE.extend hx (hE.env.extend hx (hE0.extend hext' hA')), hstar, hlm,
      ⟨hcore', hsl'⟩⟩

/-- **G15, values.** `g14_value`'s statement over `checkG15`, under G15's per-value premises
(`G14Pre`) and the contract `CallOKZ` of its static calls. -/
theorem g15_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG15 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp3 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hpre : G14Pre lc s v)
    (hcall : CallOK H E g L lc s s' v m) (hcallz : CallOKZ H E g L lc s s' v m)
    (hicall : ICallOK H E L ret lc s s' v m)
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
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, hcf, hk, hlt, hnd, hblocks⟩ := checkG15_spec hc
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
  obtain ⟨htemp, hVK⟩ := vkind15_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  rw [kAt_succ hi hv]
  exact vk15_step hE0 F hhome hcf hv hVK hvs htemp hj hj' hreads hm hinv hpre hcall hcallz hicall
    hwb hclo hs

/-- **G15, nil panics.** `g14_nilPanic`'s statement over `checkG15`. -/
theorem g15_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG15 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
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
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks⟩ := checkG15_spec hc
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
  obtain ⟨-, hVK⟩ := vkind15_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases hVK with
  | g14 _ hVK14 =>
    cases hVK14 with
    | g13 hVK13 =>
      cases hVK13 with
      | g12 hVK12 =>
        cases hVK12 with
        | g11 hVK11 =>
          cases hVK11 with
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
                    exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2
                      hao hma hvs hs
                | wb hop' => rw [hop] at hop'; cases hop'
                | sel0 hop' => rw [hop] at hop'; cases hop'
                | sel1 hop' => rw [hop] at hop'; cases hop'
              | call hop' => rw [hop] at hop'; cases hop'
            | icall hn => rw [hop] at hn; cases hn
            | selMem hop' => rw [hop] at hop'; cases hop'
            | selReg hop' => rw [hop] at hop'; cases hop'
          | clo hop' => rw [hop] at hop'; cases hop'
        | conv hop' => rw [hop] at hop'; cases hop'
      | zero hop' => rw [hop] at hop'; cases hop'
    | idx hop' => rw [hop] at hop'; cases hop'
  | call hop' => rw [hop] at hop'; cases hop'

/-- **G15, terminators.** `g14_term`'s statement over `checkG15`. -/
theorem g15_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG15 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
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
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome, -, hk, hlt, hnd, hblocks⟩ := checkG15_spec hc
  exact termK_step hpcOf ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb
    hm hinv hpre ht

end GoFV.Proof.Gen
