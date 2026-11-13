import GoFV.Proof.Gen.G46
import GoFV.Proof.Gen.Spec47

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G47 of the genssa validator: calls with float arguments or results
(`docs/plans/proofs3.md` §4, float stage (c))

`checkG47 lc` (`GoFV/Gen/Check47.lean`) is G46 with the static, interface and closure calls whose
ABI registers are in `R0`–`R15` or `F0`–`F15` (Go 31–46), and the selects of their results in an
`F` register. Nothing new is trusted: the callee contracts (`CallOKZ`, `ICallOK`, through
`CallSpec`) relate every ABI register to its value by `RegRel`, which covers the V registers.

* A call is G2's (`g2_callAt`) or G10's (`g10_icall`), whose register-range premise now admits
  `F0`–`F15`: an argument in an `F` register is read at its float shape from its V register
  (`arg_relV`, `argsV`), the rest of the proof (the clobbered and kept registers, the class table)
  is unchanged.
* A select of a result in an `F` register is G2's select with the V register (`g47_selF`): the
  call left the result there (`LocMatch`'s V clause), read at the select's float shape
  (`fvalRel_retypeL`).

None of them writes an X register the upper-bit table keeps (`uStep35_call47`). `g47_value` takes
G46's premise `G46Pre`; `g47_initMem`, `g47_term`, `g47_nilPanic`, `g47_boundsPanic` are G46's
statements over `checkG47`.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The cases -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {g : G2In} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- The arguments `as` of `v` in `F` registers, read at their float shapes: related to their V
registers (`arg_relV`). -/
theorem argsV (F : Facts lc sym text az ez psA.toList ret E) (hm : LocMatch E s b i m)
    {P : BitVec 64 → Prop} (hinv : CoreInv E.ι P K s osp) (hR : KRead lc v K) (hnp : v.op ≠ .Phi)
    {as : List ID} {rs : List Nat} (has : ∀ a ∈ as, a ∈ v.args.toList)
    (hargs : ∀ a r, (a, r) ∈ as.zip rs → lc.home a = some (.reg r))
    (hfa : ∀ a r, (a, r) ∈ as.zip rs → 31 ≤ r → fTy (lc.ty a) = true) :
    ∀ a r, (a, r) ∈ as.zip rs → 31 ≤ r →
      ∃ x, s.read lc a = .ok x ∧ ∀ k, objV? r = some k → FValRel x (m.v k) := by
  intro a r har h31
  have hh := hargs a r har
  have hrz : r ≠ zeroReg := by unfold zeroReg; omega
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 ((F.clsReg a r hh hrz).resolve_right fun h => by
    have := hfa a r har h31; rw [h.2.2] at this; simp [fTy] at this)
  have hK := hR hnp a (has a (List.of_mem_zip har).1) r c hh hrz hc
  refine ⟨_, read_reg F.lowered hh hc, fun k hk => ?_⟩
  obtain ⟨x, hx, hxv, -⟩ := arg_relV F.lowered hm hinv hh (hfa a r har h31) hc hK hk
  rw [read_reg F.lowered hh hc] at hx
  cases hx
  exact hxv

/-- `SelectN [i]` of a call's result `i` in its result register, an `F` register, at a float shape
(`g2_selReg` with the V register): no code. -/
theorem g47_selF (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {c : ID} {ts : List Ty} {r : Nat} {rs : Array (Option Nat)} {t : Ty}
    (hop : v.op = .SelectN) (hsz1 : v.args.size = 1) (hc0 : v.args[0]? = some c)
    (hns : ∀ k, lc.home c ≠ some (.slot k)) (hts : lc.ty c = .tuple ts)
    (hct : callTy (ts.length - 1) (.tuple ts) = true) (hpos : 0 ≤ v.auxInt.toInt)
    (hvh : lc.home v.id = some (.reg r)) (hr31 : 31 ≤ r) (hr47 : r < 47)
    (hKr : ∀ c0, cls (lc.ty v.id) = some c0 → K r = some c0)
    (hlt : v.auxInt.toInt.toNat + 1 < ts.length) (ht : ts[v.auxInt.toInt.toNat]? = some t)
    (hcl : cls t = cls (lc.ty v.id)) (hft : fTy t = true) (hfv : fTy (lc.ty v.id) = true)
    (hhc : lc.home c = some (.results rs)) (hrs : rs[v.auxInt.toInt.toNat]? = some (some r))
    (hvs : j' = j) (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' := by
  have hl := F.lowered
  obtain ⟨ts', rfl, -, hcls⟩ := callTy_split hct
  obtain ⟨xs, hread, hlen, -, hcomp⟩ := read_call (s := s) hl hts hcls hns
  obtain ⟨x, hx, rfl⟩ := stepLoc_selectN hl htemp hop (arr1 hsz1 hc0) hs
  rw [hread] at hx
  cases hx
  have hi' : v.auxInt.toInt.toNat < ts'.length := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hlt; omega
  have ht' : ts'[v.auxInt.toInt.toNat]? = some t := by
    rw [List.getElem?_append_left hi'] at ht; exact ht
  obtain ⟨c0, hc0t⟩ : ∃ c0, cls t = some c0 :=
    Option.isSome_iff_exists.1 (hcls t (List.mem_of_getElem? ht'))
  have hcv : cls (lc.ty v.id) = some c0 := by rw [← hcl]; exact hc0t
  have hxs := hcomp _ t r ht' (by simpa [hhc, Location.regList] using hrs)
  rw [selectN_retypeL (by simp [hlen]) hpos ht hxs, write_reg hvh hcv]
  have hk : objV? r = some (BitVec.ofNat 5 (r - 31)) := by
    simp [objV?, hr31, show r < 63 by omega]
  have hrz : r ≠ zeroReg := by unfold zeroReg; omega
  have hrel : FValRel (((s.reg t r).retypeL t).retypeL (lc.ty v.id))
      (m.v (BitVec.ofNat 5 (r - 31))) := by
    simp only [LocState.reg, beq_iff_eq, hrz, ↓reduceIte]
    cases hv : s.regs[r]? with
    | none => simp only [Option.getD_none, retypeL_poison]; trivial
    | some raw =>
      simp only [Option.getD_some]
      have hfit := hinv.regs r raw c0 hrz hv (hKr c0 hcv)
      exact fvalRel_retypeL (fvalRel_retypeLW (vrel_fvalW ((hm.regs r raw hv).2 _ hk) hfit) hfit
        hft hc0t)
        (fits_retypeL hc0t _) hfv hcv
  have hlm := locMatch_setRegV hm hk hrel (b' := b) (i' := i + 1)
  have hpc : E.pcOf b (i + 1) = m.pc := by rw [hj', hvs, ← hj, hm.pc]
  rw [hpc, wV_self_pc] at hlm
  exact ⟨m, .refl, hlm, (core_setReg hinv (fits_retypeL hcv _)).mono
    (knext_set hK (by rw [hop]; nofun) hvh hcv), hsi⟩

end Cases

/-! ## One value -/

/-- The upper-bit table is empty after a call or a select of one. -/
theorem uStep35_call47 {lc : LocCtx} {L : List (Nat × Nat × Bool)} {v : Value}
    (hop : v.op = .ARM64CALLstatic ∨ v.op = .ARM64CALLinter ∨ v.op = .ARM64CALLclosure ∨
      v.op = .SelectN) : uStep35 lc L v = [] := by
  rcases hop with h | h | h | h <;>
    simp [uStep35, ldEntry35, loadOp?, narrowLoad?, pairOp35, uStep34, keep34, keep31, keepOp31,
      keepOp34, uStepL, uEntry, narrowLd?, loadIdxOp?, h]

/-- G47's own values are calls and selects. -/
theorem vk47_ops {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK47 lc g v kd) :
    VK46 lc g v kd ∨ (v.op = .ARM64CALLstatic ∨ v.op = .ARM64CALLinter ∨
      v.op = .ARM64CALLclosure ∨ v.op = .SelectN) := by
  cases h with
  | g46 h => exact .inl h
  | call hop => exact .inr (.inl hop)
  | icall hk =>
    rcases icallLead_some hk with ⟨h, -⟩ | ⟨h, -⟩
    · exact .inr (.inr (.inl h))
    · exact .inr (.inr (.inr (.inl h)))
  | selF hop => exact .inr (.inr (.inr (.inr hop)))

/-- One value of G47's kinds: `vk46_step`'s statement, under `G46Pre`. -/
theorem vk47_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)}
    (hE : G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK47 lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s osp) (hL : UOKL m L)
    (hmem : ∀ x, (v.op = .ARM64MOVDnop ∨ v.op = .ARM64MOVDreg) → v.args[0]? = some x →
      ∃ r c, regHome? lc x = some r ∧ cls (lc.ty x) = some c ∧
        (r, c, lc.signOf lc.ctx.f.valueTab.size x) ∈ L)
    (hpre : G46Pre lc s v)
    (hcall : CallOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hcallz : CallOKZAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hicall : ICallOKAt osp H E (Link.byId sym text az ez ps.toList) ret lc s s' v m)
    (hwb : WbOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s v m) (hclo : CloOK E s v m)
    (hgetg : GetGOK E v) (hmeq : MemEqOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s v m)
    (hmp : MemEqPre lc s v) (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp ∧
      UOKL m' (uStep35 lc L v) := by
  have hR := kread_of_reads hreads
  have hempty : ∀ m', UOKL m' [] := fun _ e he => by cases he
  have hE0 := hE.env.env.env.env
  obtain ⟨hlcE, -, -, -, -, -, hsyms, hcalls, -, -, hF⟩ := hE.env.env.env.env
  cases hVK with
  | g46 hVK46 =>
    exact vk46_step hE F hhome hcf hv hVK46 hvs htemp hj hj' hreads hm hinv hL hmem hpre hcall
      hcallz hicall hwb hclo hgetg hmeq hmp hs
  | call hop hcall' hcr hnd _ _ _ h16 hlen hargs hfa hres hct =>
    have hframed : E.framed = true := by
      cases hfr : E.framed
      · exact absurd hop (hcalls hfr id v hv)
      · rfl
    have hnp : v.op ≠ .Phi := by rw [hop]; nofun
    obtain ⟨ι', hext', hA', m', hstar, hlm, hcore', hsl'⟩ := g2_callAt (H := H) F hF hlcE hcf
      hframed hsyms hm hinv.core hinv.slots hR hj hj' hop h16 hlen hargs
      (argsV F hm hinv.core hR hnp (fun a ha => List.dropLast_subset _ ha) hargs hfa) hres
      hct (kcall_kStep hnp hres hnd (callTy_len hct)) (fun _ hp => callPat_spec hp) hvs htemp hs
      (hcallz.spec hop _ _ _ _ _ hcall' hcr)
    have hx : E.Extends { E with ι := ι' } := ⟨rfl, hext'⟩
    refine ⟨_, m', hx, hE.extend hx (hE.env.extend hx (hE.env.env.extend hx
      (hE0.extend hext' hA'))), hstar, hlm, ⟨hcore', hsl'⟩, ?_⟩
    rw [uStep35_call47 (.inl hop)]
    exact hempty m'
  | icall hn hcabi hcr hnd _ _ _ _ h16 ha0 hrc hrc26 hcl0 ho hctx hlen hargs hfa hres hct =>
    have hframed : E.framed = true := by
      cases hfr : E.framed
      · rw [hE.env.icalls hfr id v hv] at hn; cases hn
      · rfl
    have hnp := icall_notPhi hn
    obtain ⟨ι', hext', hA', m', hstar, hlm, hcore', hsl'⟩ := g10_icall (H := H) (g := g) F hF hlcE
      hcf hframed hm hinv.core hinv.slots hR hj hj' hn hcabi hcr h16 ha0 hrc
      hrc26 hcl0 ho hctx hlen hargs
      (argsV F hm hinv.core hR hnp
        (fun a ha => List.mem_of_mem_drop (List.dropLast_subset _ ha)) hargs hfa) hres hct
      (kcall_kStep hnp hres hnd (callTy_len hct)) hvs htemp hs hicall
    have hx : E.Extends { E with ι := ι' } := ⟨rfl, hext'⟩
    refine ⟨_, m', hx, hE.extend hx (hE.env.extend hx (hE.env.env.extend hx
      (hE0.extend hext' hA'))), hstar, hlm, ⟨hcore', hsl'⟩, ?_⟩
    rw [uStep35_call47 (by rcases icallLead_some hn with ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h])]
    exact hempty m'
  | selF hop hsz1 hc0 hu hcu hts hct hpos hvh hr31 hr47 hlt ht hcl hft hfv hhc hrs =>
    obtain ⟨m', h1, h2, h3, h4⟩ := g47_selF (H := H) F hm hinv.core hinv.slots
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz1 hc0
      (by rcases hcu with hcu | hcu <;>
        first | exact callsNotSlot10 hhome _ _ hu hcu | exact icallNotSlot10 hhome hu hcu)
      hts hct hpos hvh hr31 hr47
      (fun c0 hc0' => ksel_of_reads hreads hop hc0 hts hhc hrs (by rw [ht]; exact hcl.trans hc0'))
      hlt ht hcl hft hfv hhc hrs hvs htemp hs
    refine ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩, ?_⟩
    rw [uStep35_call47 (.inr (.inr (.inr hop)))]
    exact hempty m'

/-- A nil check of G47's kinds is G7's. -/
theorem vk47_nil {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK47 lc g v kd)
    (hop : v.op = .ARM64LoweredNilCheck) : VK7 lc g v kd := by
  rcases vk47_ops h with h | h
  · exact vk46_nil h hop
  · rcases h with h | h | h | h <;> rw [hop] at h <;> cases h

/-- A bounds check of G47's kinds is G28's. -/
theorem vk47_pb {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK47 lc g v kd)
    (hop : pbOp v.op = true) : VK28 lc g v kd := by
  rcases vk47_ops h with h | h
  · exact vk46_pb h hop
  · rcases h with h | h | h | h <;> rw [h] at hop <;> cases hop

/-! ## The theorems on G47's check -/

/-- G46's values and G47's calls and selects under G47's check, under `G46Pre`. -/
theorem g47L_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG47L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hu : UOKL m (uL35 lc (uIn35 lc bid) blk i))
    (hpre : G46Pre lc s v)
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
    obtain ⟨E', m', hx, hE', h1, h2, h3, -⟩ := g33_value (checkG33_of_47L hl hc) hE hbid hb hi hv
      hen hm hinv (by rw [uL31_nl hl]; intro e he; cases he) hpre.1.1.1.1.1 hcall hcallz hicall
      hwb hclo hgetg hmeq hmp hs
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
    checkG47L_spec hl hc
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
  obtain ⟨htemp, hVK⟩ := vkind47_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  rw [kAt_succ hi hv]
  exact vk47_step hE0 F hhome hcf hv hVK hvs htemp hj hj' hreads hm hinv hu
    (fun x hop hx => movdOK35_spec hmovd hbid hb hi hv hop hx)
    hpre hcall hcallz hicall hwb hclo hgetg hmeq hmp hs

/-- `InitMem` under G47's check: `g46L_initMem`'s statement. -/
theorem g47L_initMem {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG47L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hl : lc.ctx.f.lowered = true)
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
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, -, -, -, -, -, -, hblocks, -, -, -⟩ := checkG47L_spec hl hc
  obtain ⟨b, j, js, e, next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk, vkind47_initMem hop, vkind46_initMem hop, vkind45_initMem hop,
    vkind44_initMem hop] at hkd
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
    hK ▸ hinv, ?_⟩
  rw [uL35_succ hl hi hv, uStep35_initMem hop]
  intro e he
  cases he

/-- G38's nil panics under G47's check. -/
theorem g47L_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG47L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  cases hl : lc.ctx.f.lowered with
  | false => exact g33_nilPanic (checkG33_of_47L hl hc) hE hbid hb hi hv hop hm hinv hs
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, -⟩ :=
    checkG47L_spec hl hc
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
  obtain ⟨-, hVK⟩ := vkind47_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases vk47_nil hVK hop with
  | g6 hne _ => exact absurd hop hne
  | nil _ hsz2 _ _ hao hma =>
    exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao hma hvs hs

/-- G38's bounds panics under G47's check. -/
theorem g47L_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG47L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hbok : BoundsOK H g L ps.toList)
    (hs : stepLoc env lc s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    exact g33_boundsPanic (checkG33_of_47L hl hc) hE hbid hb hi hv hop hm hinv hbok hs
  | true =>
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, hsyms, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, hpb, -, -⟩ :=
    checkG47L_spec hl hc
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
  obtain ⟨-, hVK⟩ := vkind47_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  exact vk28_boundsPanic F hsyms hpb hrow hb hi hv (vk47_pb hVK hop) hvs hj hreads hop hm hinv
    hbok hs

/-- G38's terminators under G47's check. -/
theorem g47L_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG47L lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s) (hpre : G1TermPre lc s blk)
    (hu : UOKL m (uL35 lc (uIn35 lc bid) blk blk.values.size))
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' ∧
      e.b ∈ lc.ctx.f.blocks.toList ∧ UOKL m' (uIn35 lc e.b) := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g33_term (checkG33_of_47L hl hc) hE hbid hb hm hinv hpre
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
    checkG47L_spec hl hc
  obtain ⟨m', h1, h2, h3, h4, he, hx⟩ := termK_stepX hpcOf
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb hm hinv hpre ht
  refine ⟨m', h1, h2, h3, h4, fun x hxin => ?_⟩
  exact uok_of_x hx (hu x (uEdgesOK35_edge hedges hbid hb he x hxin))

/-! ## The slice: the theorems on `checkG47 lc`, on `liveCtx lc` -/

/-- **G47, values.** `g46_value`'s statement over `checkG47`, under G46's premise `G46Pre`: the
calls with float arguments or results and the selects of their results in `F` registers add no
premise (the callee contracts `CallOKZ` and `ICallOK` already relate the V registers). -/
theorem g47_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG47 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s)
    (hu : UOKL m (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk i))
    (hpre : G46Pre (liveCtx lc) s v)
    (hcall : CallOK H E g L (liveCtx lc) s s' v m) (hcallz : CallOKZ H E g L (liveCtx lc) s s' v m)
    (hicall : ICallOK H E L ret (liveCtx lc) s s' v m)
    (hwb : WbOK H E g L (liveCtx lc) s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hmeq : MemEqOK H E g L (liveCtx lc) s v m) (hmp : MemEqPre (liveCtx lc) s v)
    (hs : stepLoc env (liveCtx lc) s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env (liveCtx lc) g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' (liveCtx lc) (kAt (liveCtx lc) kt bid blk (i + 1)) s' ∧
      UOKL m' (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk (i + 1)) :=
  g47L_value (checkG47_spec hc).2 hE hbid hb hi hv hen hm hinv hu hpre hcall hcallz hicall hwb hclo
    hgetg hmeq hmp hs

/-- **G47, `InitMem`.** `g46_initMem`'s statement over `checkG47`. -/
theorem g47_initMem {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG47 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hl : lc.ctx.f.lowered = true)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .InitMem) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s) (hpre : MemInit s)
    (hs : stepLoc env (liveCtx lc) s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env (liveCtx lc) g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' (liveCtx lc) (kAt (liveCtx lc) kt bid blk (i + 1)) s' ∧
      UOKL m' (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk (i + 1)) :=
  g47L_initMem (checkG47_spec hc).2 hE hl hbid hb hi hv hop hm hinv hpre hs

/-- **G47, nil panics.** `g46_nilPanic`'s statement over `checkG47`. -/
theorem g47_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG47 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s)
    (hs : stepLoc env (liveCtx lc) s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e :=
  g47L_nilPanic (checkG47_spec hc).2 hE hbid hb hi hv hop hm hinv hs

/-- **G47, bounds panics.** `g46_boundsPanic`'s statement over `checkG47`. -/
theorem g47_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG47 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s)
    (hbok : BoundsOK H g L ps.toList) (hs : stepLoc env (liveCtx lc) s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' :=
  g47L_boundsPanic (checkG47_spec hc).2 hE hbid hb hi hv hop hm hinv hbok hs

/-- **G47, terminators.** `g46_term`'s statement over `checkG47`. -/
theorem g47_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG47 lc ps bstart g = .ok (tab, kt)) (hE : G28Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk blk.values.size) s)
    (hpre : G1TermPre (liveCtx lc) s blk)
    (hu : UOKL m (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk blk.values.size))
    (ht : stepTermLoc (liveCtx lc) s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧
      G3Inv E (liveCtx lc) (kt.at e.b) s' ∧ e.b ∈ lc.ctx.f.blocks.toList ∧
      UOKL m' (uIn35 (liveCtx lc) e.b) :=
  g47L_term (checkG47_spec hc).2 hE hbid hb hm hinv hpre hu ht

end GoFV.Proof.Gen
