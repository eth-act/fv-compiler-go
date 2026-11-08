import GoFV.Proof.Gen.G8
import GoFV.Proof.Gen.Spec9

/-!
# Soundness of the genssa validator's slice G9: call results (`docs/plans/proofs3.md` §4)

`g9_value`, `g9_term`, `g9_nilPanic`: `g8_value`'s, `g8_term`'s and `g8_nilPanic`'s statements
over `checkG9`. G9 accepts the static calls whose result registers hold values of other classes
elsewhere in the function. The proof of a static call (`g2_call`) never used G2's function-wide
condition on the result registers (`resultReg`): the class table follows a call by setting each of
its distinct result registers to its result's class (`kcall_kStep`), which is all `g2_call` needs
of the classes after the call (`KCall`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm

/-- One value of G9's kinds (`VK9`) emitted at the Progs from `j` to `j'`: `vk8_step`'s statement
for G9's values. -/
theorem vk9_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2}
    (hE : G8Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hns : CallsNotSlot lc)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK9 lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s) (hpre : G7Pre lc s v)
    (hcall : CallOK H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hwb : WbOK H E g (Link.byId sym text az ez ps.toList) lc s v m)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G8Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' := by
  cases hVK with
  | g8 _ hVK8 =>
    exact vk8_step hE F hns hcf hv hVK8 hvs htemp hj hj' hreads hm hinv hpre hcall hwb hs
  | call hop hcall' hcr hnd _ _ _ h16 hlen hargs hres hct =>
    have hE0 := hE.env.env
    obtain ⟨hlcE, -, -, -, -, -, hsyms, hcalls, -, -, hF⟩ := hE.env.env
    have hframed : E.framed = true := by
      cases hfr : E.framed
      · exact absurd hop (hcalls hfr id v hv)
      · rfl
    have hnp : v.op ≠ .Phi := by rw [hop]; nofun
    obtain ⟨ι', hext', hA', m', hstar, hlm, hcore', hsl'⟩ := g2_call (H := H) F hF hlcE hcf
      hframed hsyms hm hinv.core hinv.slots (kread_of_reads hreads) hj hj' hop hcall' hcr h16 hlen
      hargs hres hct (kcall_kStep hnp hres hnd (callTy_len hct)) (fun _ hp => callPat_spec hp) hvs
      htemp hs hcall
    exact ⟨_, m', ⟨rfl, hext'⟩, hE.extend ⟨rfl, hext'⟩ (hE0.extend hext' hA'), hstar, hlm,
      ⟨hcore', hsl'⟩⟩

/-- **G9, values.** `g8_value`'s statement over `checkG9`: a value (not an entry value) of an
accepted function run by `runLoc` is matched by `runProg` steps of genssa's P0 Progs to a state
related before the next value, with the registers at the classes before the next value, under an
activation that extends `E`'s injection (by the callee's at a call, by the buffer at a write
barrier) and is again a `G8Env`. -/
theorem g9_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG9 lc ps bstart g = .ok (tab, kt)) (hE : G8Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp3 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hpre : G7Pre lc s v)
    (hcall : CallOK H E g L lc s s' v m) (hwb : WbOK H E g L lc s v m)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G8Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' := by
  have hE0 := hE
  obtain ⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome4, hcf, hk, hlt, hnd, hblocks⟩ := checkG9_spec hc
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
  obtain ⟨htemp, hVK⟩ := vkind9_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home4 hhome4, hnd, hlt, hret, hA⟩
  rw [kAt_succ hi hv]
  exact vk9_step hE0 F (call_not_slot4 hhome4) hcf hv hVK hvs htemp hj hj' hreads hm hinv hpre
    hcall hwb hs

/-- **G9, nil panics.** `g8_nilPanic`'s statement over `checkG9`. -/
theorem g9_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState} {m : MState}
    {e : Panic} {mm' : Mem}
    (hc : checkG9 lc ps bstart g = .ok (tab, kt)) (hE : G8Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  obtain ⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome4, -, hk, hlt, hnd, hblocks⟩ := checkG9_spec hc
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
  obtain ⟨-, hVK⟩ := vkind9_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home4 hhome4, hnd, hlt, hret, hA⟩
  cases hVK with
  | g8 _ hVK8 =>
    cases hVK8 with
    | g7 hVK7 =>
      cases hVK7 with
      | g6 hne _ => exact absurd hop hne
      | nil _ hsz2 _ _ hao hma =>
        exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao hma hvs
          hs
    | wb hop' => rw [hop] at hop'; cases hop'
    | sel0 hop' => rw [hop] at hop'; cases hop'
    | sel1 hop' => rw [hop] at hop'; cases hop'
  | call hop' => rw [hop] at hop'; cases hop'

/-- **G9, terminators.** `g8_term`'s statement over `checkG9`. -/
theorem g9_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG9 lc ps bstart g = .ok (tab, kt)) (hE : G8Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s) (hpre : G1TermPre lc s blk)
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' ∧
      e.b ∈ lc.ctx.f.blocks.toList := by
  obtain ⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome4, -, hk, hlt, hnd, hblocks⟩ := checkG9_spec hc
  exact termK_step hpcOf ⟨hl, clsReg_of_home4 hhome4, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb
    hm hinv hpre ht

end GoFV.Proof.Gen
