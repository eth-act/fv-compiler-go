import GoFV.Proof.Gen.G20
import GoFV.Proof.Gen.Spec21

/-!
# Soundness of the genssa validator's slice G21: `MOVDreg` after its narrow load
(`docs/plans/proofs3.md` §4, §8)

`g21_value`, `g21_term`, `g21_nilPanic`, `g21_boundsPanic`: `g20_value`'s, `g20_term`'s,
`g20_nilPanic`'s and `g20_boundsPanic`'s statements over `checkG21`.

`MOVDreg x` is `Copy`'s code (`MOVD Rx, Rv`, or nothing in one register) with `MOVDnop`'s
semantics: `runLoc` writes the 64-bit zero or sign extension of `x` that `signOf x` names
(`movdLoc`, `stepLoc_nop`). `movdOK` puts the upper-bit table's entry for `x`'s register before
it, so `x`'s machine register is that extension of its low bits (`lo_movd`), which `MOVD` copies
whole (`g21_mov`) or which stays in place (`g20_nop`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- `MOVDreg x` with `x` in another register: `MOVD Rx, Rv` copies `x`'s register, which the
upper-bit table names, so it holds the extension `runLoc` writes. The machine writes only `Rv`. -/
theorem g21_mov (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {ca cd : Nat} {ra rd : Int} (hop : v.op = .ARM64MOVDreg) (hsz : v.args.size = 1)
    (hao : argObj lc v 0 = .ok (ca, ra)) (hro : resObj lc v = .ok (cd, rd))
    (hz : ra ≠ ARM64.REGZERO) (hca : ca = 8 ∨ ca = 16 ∨ ca = 32)
    (hcd : cd = 8 ∨ cd = 16 ∨ cd = 32 ∨ cd = 64)
    (hvs : OneAt2 psA j (.ofShape { as := .MOVD, from_ := regA ra, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s')
    (hu : ∀ x, v.args[0]? = some x → ∃ r c, regHome? lc x = some r ∧ cls (lc.ty x) = some c ∧
      UOK m (some (r, c, lc.signOf lc.ctx.f.valueTab.size x))) :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' ∧
      ∃ ka kd : Nat, ra = ARM64.REG_R0 + ka ∧ rd = ARM64.REG_R0 + kd ∧ ka < 31 ∧
        m'.x = (m.wX (BitVec.ofNat 5 kd) (m.x (BitVec.ofNat 5 ka))).x := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨x, r1, hx0, hxh, hor1, hcx⟩ := argObj_spec hao
  obtain ⟨r2, hvh, hd, hor2, hcv⟩ := resObj_spec hro
  obtain ⟨ka, hka, rfl, hkka⟩ := objOf?_some hor1
  obtain ⟨kd, hkd, rfl, -⟩ := objOf?_some hor2
  obtain ⟨hka31, hobj⟩ : ka < 31 ∧ objX? r1 = some (BitVec.ofNat 5 ka) := by
    rcases hkka with ⟨-, rfl⟩ | h
    · exact absurd rfl hz
    · exact h
  obtain ⟨a, ha, hxa, hfa⟩ := arg_rel hA hl hm hinv hxh hcx (kread_arg hR hnp hx0 hxh hcx) hkka
  obtain ⟨a', ha', rfl⟩ := stepLoc_nop hl htemp (.inr hop) hsz hx0 hs
  rw [ha] at ha'
  cases ha'
  rw [rX_lt hka31] at hxa
  obtain ⟨r, c, hr, hc, hu0⟩ := hu x hx0
  rw [regHome?_eq.2 hxh] at hr
  cases hr
  rw [hcx] at hc
  cases hc
  have hcv8 : 8 ≤ cd := by omega
  have hbool := cls_ne_bool hcv hcv8
  have hlo := lo_movd (t := lc.ty v.id) hx0 hbool hca hfa hxa (hu0 ka hka31 hobj)
  rw [write_reg hvh hcv]
  have hrel := valRel_retypeL_lo hA hcv hbool (hlo.mono (cls_le hcv))
  refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor2 hrel (fits_retypeL hcv _)
    (knext_set hK hnp hvh hcv) (fun k hk hok => ?_)).imp
    fun m' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, hsi, ka, kd, rfl, rfl, hka31, h4⟩
  obtain ⟨has, hf, -, ht, -⟩ := Shape.ok_eq hok
  rw [progStep_movReg hka hkd (nextAddr_pcAt F.nodup hk) has hf ht, wX_pc, rX_lt hka31]

end Cases

/-! ## The theorems -/

/-- One value of G21's kinds: `vk20_step`'s statement. -/
theorem vk21_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2}
    (hE : G10Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK21 lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s)
    (hu : ∀ x, (v.op = .ARM64MOVDnop ∨ v.op = .ARM64MOVDreg) → v.args[0]? = some x →
      ∃ r c, regHome? lc x = some r ∧ cls (lc.ty x) = some c ∧
        UOK m (some (r, c, lc.signOf lc.ctx.f.valueTab.size x)))
    (hpre : G14Pre lc s v)
    (hcall : CallOK H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hcallz : CallOKZ H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hicall : ICallOK H E (Link.byId sym text az ez ps.toList) ret lc s s' v m)
    (hwb : WbOK H E g (Link.byId sym text az ez ps.toList) lc s v m) (hclo : CloOK E s v m)
    (hgetg : GetGOK E v) (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G10Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' ∧ UOK m' (uEntry lc v) := by
  cases hVK with
  | g20 _ hVK20 =>
    exact vk20_step hE F hhome hcf hv hVK20 hvs htemp hj hj' hreads hm hinv hu hpre hcall hcallz
      hicall hwb hclo hgetg hs
  | regSame hop hsz hao hro hz hca hcd =>
    have hne : uEntry lc v = none := by
      have : narrowLd? lc v = none := by unfold narrowLd?; rw [hop]; rfl
      simp only [uEntry, this]
    rw [hne]
    obtain ⟨x, r1, hx0, hxh, hor1, hcx⟩ := argObj_spec hao
    obtain ⟨r2, hvh, hd, hor2, hcv⟩ := resObj_spec hro
    obtain rfl := objOf?_inj hor1 hor2
    have hz' : r1 ≠ zeroReg := by
      rintro rfl
      simp only [objOf?, ↓reduceIte, Option.some.injEq] at hor1
      exact hz hor1.symm
    obtain ⟨r', c', hr', hc', hu0⟩ := hu x (.inr hop) hx0
    rw [regHome?_eq.2 hxh] at hr'
    cases hr'
    rw [hcx] at hc'
    cases hc'
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g20_nop (H := H) F hm hinv.core hinv.slots
      (kread_of_reads hreads) (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' (.inr hop) hsz
      hx0 hvh hd hz' hxh hcv (by omega) hcx hca hvs htemp hs hu0
    exact ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩, trivial⟩
  | regMov hop hsz hao hro hz hca hcd hne =>
    have hue : uEntry lc v = none := by
      have : narrowLd? lc v = none := by unfold narrowLd?; rw [hop]; rfl
      simp only [uEntry, this]
    rw [hue]
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g21_mov (H := H) F hm hinv.core hinv.slots
      (kread_of_reads hreads) (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj'
      hop hsz hao hro hz hca hcd hvs htemp hs (fun x hx => hu x (.inr hop) hx)
    exact ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩, trivial⟩

/-- **G21, values.** `g20_value`'s statement over `checkG21`. -/
theorem g21_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG21 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp3 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hu : UOK m (uAt lc blk i))
    (hpre : G14Pre lc s v)
    (hcall : CallOK H E g L lc s s' v m) (hcallz : CallOKZ H E g L lc s s' v m)
    (hicall : ICallOK H E L ret lc s s' v m)
    (hwb : WbOK H E g L lc s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G10Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' ∧
      UOK m' (uAt lc blk (i + 1)) := by
  have hE0 := hE
  obtain ⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, hcf, hk, hlt, hnd, hblocks, -, hmovd⟩ :=
    checkG21_spec hc
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
  obtain ⟨htemp, hVK⟩ := vkind21_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  have hu1 : uAt c.cx.lc blk (i + 1) = uEntry c.cx.lc v := by simp [uAt, hi, hv]
  rw [kAt_succ hi hv, hu1]
  exact vk21_step hE0 F hhome hcf hv hVK hvs htemp hj hj' hreads hm hinv
    (fun x hop hx => by
      obtain ⟨r, c', hr, hc', hu0⟩ := movdOK_spec hmovd hbid hb hi hv hop hx
      exact ⟨r, c', hr, hc', hu0 ▸ hu⟩)
    hpre hcall hcallz hicall hwb hclo hgetg hs

/-- A nil check of G21's kinds is G7's. -/
theorem vk21_nil {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK21 lc g v kd)
    (hop : v.op = .ARM64LoweredNilCheck) : VK7 lc g v kd := by
  cases h with
  | g20 _ h => exact vk20_nil h hop
  | regSame hop' => rw [hop] at hop'; cases hop'
  | regMov hop' => rw [hop] at hop'; cases hop'

/-- **G21, nil panics.** `g20_nilPanic`'s statement over `checkG21`. -/
theorem g21_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG21 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
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
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, -, -⟩ :=
    checkG21_spec hc
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
  obtain ⟨-, hVK⟩ := vkind21_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases vk21_nil hVK hop with
  | g6 hne _ => exact absurd hop hne
  | nil _ hsz2 _ _ hao hma =>
    exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao hma hvs hs

/-- **G21, bounds panics.** `g20_boundsPanic`'s statement over `checkG21`, under `BoundsOK`. -/
theorem g21_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG21 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hbok : BoundsOK H g L ps.toList)
    (hs : stepLoc env lc s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' := by
  obtain ⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, hsyms, -, -, -, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, hpb, -⟩ :=
    checkG21_spec hc
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
  have hen : entryOp3 v.op = false := by
    rcases pbOp_cases hop with h | h | h | h <;> rw [h] <;> rfl
  obtain ⟨-, hVK⟩ := vkind21_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases hVK with
  | regSame hop' => rw [hop'] at hop; cases hop
  | regMov hop' => rw [hop'] at hop; cases hop
  | g20 _ hVK20 =>
    cases hVK20 with
    | nop hop' => rw [hop'] at hop; cases hop
    | g19 _ hVK19 =>
      exact vk19_boundsPanic F hsyms hpb hrow hb hi hv hVK19 hvs hj hreads hop hm hinv hbok hs

/-- **G21, terminators.** `g20_term`'s statement over `checkG21`. -/
theorem g21_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG21 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
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
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome, -, hk, hlt, hnd, hblocks, -, -⟩ :=
    checkG21_spec hc
  exact termK_step hpcOf ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb
    hm hinv hpre ht

end GoFV.Proof.Gen
