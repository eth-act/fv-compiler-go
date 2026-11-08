import GoFV.Proof.Gen.G15
import GoFV.Proof.Gen.Spec16

/-!
# Soundness of the genssa validator's slice G16: shifted adds (`docs/plans/proofs3.md` §4)

`g16_value`, `g16_term`, `g16_nilPanic`: `g15_value`'s, `g15_term`'s and `g15_nilPanic`'s
statements over `checkG16`, under the same premises.

`ADDshiftLL [k] x y` runs under `runLoc` as `Arm64.addSh … .ll k` on the arguments read from their
homes (`stepLoc_addSh`): `addP` of `x` and `y`'s register shifted left by `k`. Genssa emits `ADD
Rm<<k, Rn, Rd`, whose shifted source operand (`shiftLLA`) reads `X[m] <<< k` (`ctx_src_shiftLL`),
so the machine writes `X[n] + (X[m] <<< k)` (`progStep_addShiftLL`). Both registers are related to
the arguments on the low bits of their classes, which the shift keeps, so the sum is related on the
low bits of the result's class, with `ADD`'s pointer case (`lo_addSh`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## `stepLoc` -/

/-- `ADDshiftLL`: `Arm64.addSh … .ll k` of the arguments read from their homes. -/
theorem stepLoc_addSh {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}
    (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .ARM64ADDshiftLL) (h : stepLoc env lc s v = .ok s') :
    ∃ argv, v.args.toList.mapM (s.read lc) = .ok argv ∧
      s' = s.write lc v.id ((Arm64.addSh (lc.ty v.id) .ll v.auxInt argv).retypeL (lc.ty v.id)) := by
  obtain ⟨argv, r, hm, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
    (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
  have he : evalOpL true env lc.ctx s.fr v argv (lc.ty v.id) =
      .ok (Arm64.addSh (lc.ty v.id) .ll v.auxInt argv) := by
    unfold evalOpL; rw [hop]; rfl
  rw [he] at hr
  cases hr
  exact ⟨argv, hm, rfl⟩

/-! ## The machine's `ADD Rm<<k, Rn, Rd` -/

/-- The shifted register operand `shiftLLA (R0 + km) k`: `X[km] <<< k`. -/
theorem ctx_src_shiftLL {c : ProgCtx} {km k : Nat} (hkm : km < 32) (hk : k < 64) :
    c.src true (shiftLLA (REG_R0 + km) k) = .ok (c.s.rX (BitVec.ofNat 5 km) <<< k) := by
  have ho : ((REG_R0 + (km : Int) - REG_R0) * 65536 + (k : Int) * 1024).toNat =
      km * 65536 + k * 1024 := by omega
  have h1 : (km * 65536 + k * 1024) / 65536 % 32 = km := by omega
  have h2 : (km * 65536 + k * 1024) / 4194304 % 4 = 0 := by omega
  have h3 : (km * 65536 + k * 1024) / 1024 % 64 = k := by omega
  simp only [ProgCtx.src, shiftLLA, ho, h1, h2, h3]
  simp [sized, shiftOf, Arm64.Shift.apply, Nat.mod_eq_of_lt hk]
  rfl

/-- `ADD Rm<<k, Rn, Rd`. -/
theorem progStep_addShiftLL {L : Link} {p : Prog} {s : MState} {next : BitVec 64}
    {kn km kd k : Nat} (hkn : kn < 32) (hkm : km < 32) (hkd : kd < 32) (hk : k < 64)
    (hn : L.nextAddr p.id = some next) (has : p.as = .ADD)
    (hf : p.from_ = shiftLLA (REG_R0 + km) k) (hr : p.reg = REG_R0 + kn)
    (ht : p.to = regA (REG_R0 + kd)) :
    progStep L p s = .ok { s.wX (BitVec.ofNat 5 kd)
      (s.rX (BitVec.ofNat 5 kn) + s.rX (BitVec.ofNat 5 km) <<< k) with pc := next } := by
  have hrn := rn_reg (c := ⟨L, s, p⟩) hr
  have hname : As.name .ADD = "ADD" := rfl
  have he : progEffect ⟨L, s, p⟩ =
      .ok (effWd {} kd (s.rX (BitVec.ofNat 5 kn) + s.rX (BitVec.ofNat 5 km) <<< k)) := by
    unfold progEffect
    simp (config := { decide := true }) only [has, hname, hf, ht, hrn, regA, shiftLLA,
      ProgOp.baseOf, ↓reduceIte, ProgOp.binNames, ctx_src_reg hkn, ProgOp.binOp, addSub_add]
    rw [← shiftLLA, ctx_src_shiftLL hkm hk]
    simp only [ProgOp.binOp, addSub_add, eff_wX_dest hkd]
    by_cases h : kd = 31 <;> simp [effWd, h] <;> rfl
  rw [progStep_eq hn (by simp [Prog.isSkip, has]) he
    (by by_cases h : kd = 31 <;> simp [effWd, h, Eff.nilAccess?]), wd_apply hkd]

/-! ## The value -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- `ADD Rm<<k, Rn, Rd`. -/
theorem g16_addSh (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {ca cb c : Nat} {rn rm rd : Int} (hop : v.op = .ARM64ADDshiftLL) (hsz : v.args.size = 2)
    (hk0 : 0 ≤ v.auxInt.toInt) (hk64 : v.auxInt.toInt < 64)
    (hao : argObj lc v 0 = .ok (ca, rn)) (hbo : argObj lc v 1 = .ok (cb, rm))
    (hro : resObj lc v = .ok (c, rd)) (h8 : 8 ≤ c) (hca : c ≤ ca) (hcb : c ≤ cb)
    (hvs : OneAt2 psA j (.ofShape
      { as := .ADD, from_ := shiftLLA rm v.auxInt.toInt.toNat, reg := rn, to := regA rd }) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' := by
  have hl := F.lowered
  have hA := F.addr
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨a0, r0, ha0, hah0, hor0, hca0⟩ := argObj_spec hao
  obtain ⟨a1, r1, ha1, hah1, hor1, hca1⟩ := argObj_spec hbo
  obtain ⟨r, hvh, hd, hor, hcv⟩ := resObj_spec hro
  obtain ⟨kn, hkn, rfl, hkkn⟩ := objOf?_some hor0
  obtain ⟨km, hkm, rfl, hkkm⟩ := objOf?_some hor1
  obtain ⟨kd, hkd, hrd, -⟩ := objOf?_some hor
  subst hrd
  obtain ⟨x, hx, hxv, hxf⟩ :=
    arg_rel hA hl hm hinv hah0 hca0 (kread_arg hR hnp ha0 hah0 hca0) hkkn
  obtain ⟨y, hy, hyv, hyf⟩ :=
    arg_rel hA hl hm hinv hah1 hca1 (kread_arg hR hnp ha1 hah1 hca1) hkkm
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_addSh hl htemp hop hs
  rw [arr2 hsz ha0 ha1] at hargv
  obtain rfl := mapM_res_two hargv hx hy
  rw [write_reg hvh hcv]
  have ht := cls_ne_bool hcv h8
  have hamt : Arm64.amt v.auxInt = v.auxInt.toInt.toNat := rfl
  have hk : v.auxInt.toInt.toNat < 64 := by omega
  have hlo := lo_addSh hA hxv hyv hxf hyf (cls_le hcv) hca hcb ht (k := v.auxInt) (t := lc.ty v.id)
    (by rw [hamt]; exact hk)
  rw [hamt] at hlo
  refine (op_reg2 (H := H) F hm hinv hj hj' hvs hd hkd hor (valRel_retypeL_lo hA hcv ht hlo)
    (fits_retypeL hcv _) (knext_set hK hnp hvh hcv) (fun k0 hk0' hok => ?_)).imp
    fun m' ⟨h1, h2, h3⟩ => ⟨h1, h2, h3, hsi⟩
  obtain ⟨has, hf, hr, ht', -⟩ := Shape.ok_eq hok
  rw [progStep_addShiftLL hkn hkm hkd hk (nextAddr_pcAt F.nodup hk0') has hf hr ht', wX_pc]
  rfl

end Cases

/-! ## The theorems -/

/-- One value of G16's kinds (`VK16`) emitted at the Progs from `j` to `j'`: `vk15_step`'s
statement for G16's values. -/
theorem vk16_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2}
    (hE : G10Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK16 lc g v kd)
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
  | g15 hVK15 =>
    exact vk15_step hE F hhome hcf hv hVK15 hvs htemp hj hj' hreads hm hinv hpre hcall hcallz
      hicall hwb hclo hs
  | addSh hop hsz hk0 hk64 hao hbo hro h8 hca hcb =>
    obtain ⟨r, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4⟩ := g16_addSh (H := H) F hm hinv.core hinv.slots
      (kread_of_reads hreads) (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hk0 hk64
      hao hbo hro h8 hca hcb hvs htemp hs
    exact ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩⟩

/-- **G16, values.** `g15_value`'s statement over `checkG16`. -/
theorem g16_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG16 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
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
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, hcf, hk, hlt, hnd, hblocks⟩ := checkG16_spec hc
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
  obtain ⟨htemp, hVK⟩ := vkind16_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  rw [kAt_succ hi hv]
  exact vk16_step hE0 F hhome hcf hv hVK hvs htemp hj hj' hreads hm hinv hpre hcall hcallz hicall
    hwb hclo hs

/-- **G16, nil panics.** `g15_nilPanic`'s statement over `checkG16`. -/
theorem g16_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG16 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
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
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks⟩ := checkG16_spec hc
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
  obtain ⟨-, hVK⟩ := vkind16_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases hVK with
  | g15 hVK15 =>
    cases hVK15 with
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
                      exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop
                        hsz2 hao hma hvs hs
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
  | addSh hop' => rw [hop] at hop'; cases hop'

/-- **G16, terminators.** `g15_term`'s statement over `checkG16`. -/
theorem g16_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG16 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
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
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome, -, hk, hlt, hnd, hblocks⟩ := checkG16_spec hc
  exact termK_step hpcOf ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb
    hm hinv hpre ht

end GoFV.Proof.Gen
