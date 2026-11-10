import GoFV.Proof.Gen.G22
import GoFV.Proof.Gen.Spec23

variable [GoFV.SSA.Sem.Addrs]

/-!
# Soundness of the genssa validator's slice G23: flags to a register (`docs/plans/proofs3.md` §4)

`g23_value`, `g23_term`, `g23_nilPanic`, `g23_boundsPanic`: `g22_value`'s, `g22_term`'s,
`g22_nilPanic`'s and `g22_boundsPanic`'s statements over `checkG23`.

A comparison pseudo-op (`Equal`, …; `Cond.ofOp`) runs in `runLoc` as `Arm64.cset`: the boolean its
condition gives on the flags register, or `poison` when a flag bit it reads is unknown
(`stepLoc_cset`). genssa's `CSET cond, Rd` writes 1 or 0 by `ConditionHolds(cond)` on `NZCV`
(`progStep_cset`), and `condBits` names the same condition (`cset_cond`). `LocMatch` relates the
flags register to `NZCV` (`FlagsRel`), on which the two decisions agree (`onVal_holds`), so the
register holds the boolean as 0 or 1 (`g23_cset`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The comparison pseudo-ops -/

/-- The ops `Cond.ofOp` names a condition for. -/
def csetOps : List Op :=
  [.ARM64Equal, .ARM64NotEqual, .ARM64LessThan, .ARM64LessThanU, .ARM64LessEqual,
    .ARM64LessEqualU, .ARM64GreaterThan, .ARM64GreaterThanU, .ARM64GreaterEqual,
    .ARM64GreaterEqualU, .ARM64LessThanF, .ARM64LessEqualF, .ARM64GreaterThanF,
    .ARM64GreaterEqualF, .ARM64NotLessThanF, .ARM64NotLessEqualF, .ARM64NotGreaterThanF,
    .ARM64NotGreaterEqualF, .ARM64LessThanNoov, .ARM64GreaterEqualNoov]

theorem csetOps_of {op : Op} (h : (Cond.ofOp op).isSome = true) : op ∈ csetOps := by
  unfold Cond.ofOp at h
  split at h <;> first | exact absurd h (by decide) | simp [csetOps]

/-- The condition `condBits` names for a comparison pseudo-op is `Cond.ofOp`'s, as the 4-bit
condition of its `SPECIAL` operand (`condOfSpecial`). -/
theorem cset_cond {op : Op} {c : Cond} {cc : Int} (hc : Cond.ofOp op = some c)
    (hb : ARM64.condBits op = some cc) :
    (SPOP_EQ ≤ cc ∧ cc < SPOP_EQ + 16) ∧ condOf (BitVec.ofInt 4 (cc - SPOP_EQ)) = c := by
  unfold Cond.ofOp at hc
  split at hc <;>
  first
  | (cases hc
     simp only [ARM64.condBits, Option.some.injEq] at hb
     subst hb
     decide)
  | cases hc

/-- A comparison pseudo-op writes no register but its home and keeps the flags: `runLoc` runs
`Arm64.cset` on its argument. -/
theorem stepLoc_cset {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}
    (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hc : (Cond.ofOp v.op).isSome = true) (h : stepLoc env lc s v = .ok s') :
    ∃ argv, v.args.toList.mapM (s.read lc) = .ok argv ∧
      s' = s.write lc v.id ((Arm64.cset (lc.ty v.id) v.op argv).retypeL (lc.ty v.id)) := by
  have hm := csetOps_of hc
  simp only [csetOps, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with hop | hop | hop | hop | hop | hop | hop | hop | hop | hop | hop | hop | hop |
    hop | hop | hop | hop | hop | hop | hop <;>
  · obtain ⟨argv, r, hm, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
      (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
      (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
    have he : evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) =
        .ok (Arm64.cset (lc.ty v.id) v.op argv) := by
      unfold evalOpL; rw [hop]; rfl
    rw [he] at hr; cases hr
    exact ⟨argv, hm, rfl⟩

/-- A comparison pseudo-op is none of the narrow loads (`narrowLd?`). -/
theorem narrowLd?_cset {lc : LocCtx} {v : Value} (hc : (Cond.ofOp v.op).isSome = true) :
    narrowLd? lc v = none := by
  have hm := csetOps_of hc
  simp only [csetOps, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with hop | hop | hop | hop | hop | hop | hop | hop | hop | hop | hop | hop | hop |
    hop | hop | hop | hop | hop | hop | hop <;>
  · unfold narrowLd?; rw [hop]; rfl

section Progs

variable {L : Link} {p : Prog} {s : MState} {next : BitVec 64}

/-- `CSET cond, Rd` (`cond` a `SPECIAL` operand `SPOP_EQ + k`, `k < 16`): 1 in `Rd` when the
condition holds on `NZCV`, else 0. -/
theorem progStep_cset {kd : Nat} {cc : Int} (hkd : kd < 32) (hn : L.nextAddr p.id = some next)
    (has : p.as = .CSET) (hf : p.from_ = specA cc) (hcc : SPOP_EQ ≤ cc ∧ cc < SPOP_EQ + 16)
    (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      (if s.holds (BitVec.ofInt 4 (cc - SPOP_EQ)) then 1 else 0) with pc := next } := by
  have hname : As.name .CSET = "CSET" := rfl
  have hsp : ProgOp.condOfSpecial (specA cc) = .ok (BitVec.ofInt 4 (cc - SPOP_EQ)) := by
    simp only [ProgOp.condOfSpecial, specA, hcc.1, hcc.2, decide_true, Bool.and_self,
      beq_self_eq_true, ↓reduceIte]
    rfl
  have he : progEffect ⟨L, s, p⟩ =
      .ok (effWd {} kd (if s.holds (BitVec.ofInt 4 (cc - SPOP_EQ)) then 1 else 0)) := by
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, ProgOp.baseOf, ↓reduceIte,
      ProgOp.binNames]
    simp only [hf, hsp, ht, regA]
    exact eff_wX_dest hkd
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
    (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]), wd_apply hkd]

end Progs

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- The boolean of a condition on flags related to `NZCV`, as 0 or 1, is the machine's `CSET`
word. -/
theorem valRel_cset {ι : Blk → Option (BitVec 64)} {c : Cond} {f : Val} {nz : Flags} {op : Op}
    (hc : Cond.ofOp op = some c) (hf : FlagsRel f nz) :
    ValRel ι ((Arm64.cset .bool op [f]).retypeL .bool) (if c.holds nz then 1 else 0) := by
  unfold Arm64.cset
  rw [hc]
  simp only [Option.bind_some]
  cases ho : c.onVal f with
  | none => exact trivial
  | some t =>
    rw [onVal_holds hf ho]
    cases t <;> rfl

/-- A comparison pseudo-op: `CSET cond, Rd` writes the boolean its condition gives on the flags
register as 0 or 1. -/
theorem g23_cset (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {cc : Int} {a : ID} {rd : Int} (hc : (Cond.ofOp v.op).isSome = true)
    (hcc : ARM64.condBits v.op = some cc) (hsz : v.args.size = 1) (ha : v.args[0]? = some a)
    (hfl : (lc.ty a).isFlags = true) (hhn : lc.home a = none) (hro : resObj lc v = .ok (1, rd))
    (hvs : OneAt2 psA j ⟨plain .CSET (· == specA cc) (· == regA rd), "CSET"⟩ j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      XW lc v m m' := by
  have hl := F.lowered
  obtain ⟨c, hcs⟩ := Option.isSome_iff_exists.1 hc
  have hnp : v.op ≠ .Phi := by intro h; rw [h] at hcs; cases hcs
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kd, hkd, rfl, -⟩ := objOf?_some hor
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_cset hl htemp hc hs
  rw [arr1 hsz ha] at hargv
  obtain rfl := mapM_res_one hargv (read_flags hl hhn hfl)
  rw [write_reg hvh hcv, isFlags_eq hfl, cls_bool hcv]
  obtain ⟨hfr, -⟩ := flags_retypeL hm.flags
  obtain ⟨hrange, hcond⟩ := cset_cond hcs hcc
  refine (op_reg2W (H := H) F hm hinv hj hj' hvs hd hkd hor (valRel_cset hcs hfr)
    (fits_retypeL (c := 1) rfl _) (knext_set hK hnp hvh hcv) (fun k hk hok => ?_)).imp
    fun m' ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, hsi, .inr ⟨r, kd, _, hvh, hor, h4⟩⟩
  obtain ⟨has, hf, -, ht, -⟩ := plain_spec hok
  simp only [beq_iff_eq] at hf ht
  rw [progStep_cset hkd (nextAddr_pcAt F.nodup hk) has hf hrange ht, wX_pc]
  simp only [MState.holds, hcond]

end Cases

/-! ## The theorems -/

/-- One value of G23's kinds: `vk22_step`'s statement. -/
theorem vk23_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2}
    (hE : G10Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK23 lc g v kd)
    (hvs : VStep2 ps kd j j') (htemp : (lc.temps[v.id]?).join = none)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s osp)
    (hu : ∀ x, (v.op = .ARM64MOVDnop ∨ v.op = .ARM64MOVDreg) → v.args[0]? = some x →
      ∃ r c, regHome? lc x = some r ∧ cls (lc.ty x) = some c ∧
        UOK m (some (r, c, lc.signOf lc.ctx.f.valueTab.size x)))
    (hpre : G14Pre lc s v)
    (hcall : CallOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hcallz : CallOKZAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hicall : ICallOKAt osp H E (Link.byId sym text az ez ps.toList) ret lc s s' v m)
    (hwb : WbOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s v m) (hclo : CloOK E s v m)
    (hgetg : GetGOK E v) (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G10Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp ∧ UOK m' (uEntry lc v) := by
  cases hVK with
  | g22 _ hVK22 =>
    exact vk22_step hE F hhome hcf hv hVK22 hvs htemp hj hj' hreads hm hinv hu hpre hcall hcallz
      hicall hwb hclo hgetg hs
  | cset hc hcc hsz ha hfl hhn hro =>
    have hue : uEntry lc v = none := by simp only [uEntry, narrowLd?_cset hc]
    rw [hue]
    obtain ⟨r2, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g23_cset (H := H) F hm hinv.core hinv.slots
      (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hc hcc hsz ha hfl hhn hro hvs htemp hs
    exact ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩, trivial⟩

/-- **G23, values.** `g22_value`'s statement over `checkG23`. -/
theorem g23_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG23 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
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
    checkG23_spec hc
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
  obtain ⟨htemp, hVK⟩ := vkind23_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  have hu1 : uAt c.cx.lc blk (i + 1) = uEntry c.cx.lc v := by simp [uAt, hi, hv]
  rw [kAt_succ hi hv, hu1]
  exact vk23_step hE0 F hhome hcf hv hVK hvs htemp hj hj' hreads hm hinv
    (fun x hop hx => by
      obtain ⟨r, c', hr, hc', hu0⟩ := movdOK_spec hmovd hbid hb hi hv hop hx
      exact ⟨r, c', hr, hc', hu0 ▸ hu⟩)
    hpre hcall hcallz hicall hwb hclo hgetg hs

/-- A nil check of G23's kinds is G7's. -/
theorem vk23_nil {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK23 lc g v kd)
    (hop : v.op = .ARM64LoweredNilCheck) : VK7 lc g v kd := by
  cases h with
  | g22 _ h => exact vk22_nil h hop
  | cset hc => rw [hop] at hc; simp [Cond.ofOp] at hc

/-- **G23, nil panics.** `g22_nilPanic`'s statement over `checkG23`. -/
theorem g23_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG23 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
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
    checkG23_spec hc
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
  obtain ⟨-, hVK⟩ := vkind23_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases vk23_nil hVK hop with
  | g6 hne _ => exact absurd hop hne
  | nil _ hsz2 _ _ hao hma =>
    exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao hma hvs hs

/-- **G23, bounds panics.** `g22_boundsPanic`'s statement over `checkG23`, under `BoundsOK`. -/
theorem g23_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG23 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
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
    checkG23_spec hc
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
  obtain ⟨-, hVK⟩ := vkind23_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases hVK with
  | cset hc =>
    rcases pbOp_cases hop with h | h | h | h <;> rw [h] at hc <;> simp [Cond.ofOp] at hc
  | g22 _ hVK22 =>
    cases hVK22 with
    | ldp hop' => rw [hop'] at hop; cases hop
    | stp hop' => rw [hop'] at hop; cases hop
    | g21 _ hVK21 =>
      cases hVK21 with
      | regSame hop' => rw [hop'] at hop; cases hop
      | regMov hop' => rw [hop'] at hop; cases hop
      | g20 _ hVK20 =>
        cases hVK20 with
        | nop hop' => rw [hop'] at hop; cases hop
        | g19 _ hVK19 =>
          exact vk19_boundsPanic F hsyms hpb hrow hb hi hv hVK19 hvs hj hreads hop hm hinv hbok hs

/-- **G23, terminators.** `g22_term`'s statement over `checkG23`. -/
theorem g23_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG23 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
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
    checkG23_spec hc
  exact termK_step hpcOf ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb
    hm hinv hpre ht

end GoFV.Proof.Gen
