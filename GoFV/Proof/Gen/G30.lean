import GoFV.Proof.Gen.G29
import GoFV.Proof.Gen.Spec30

variable [GoFV.SSA.Sem.Addrs]

/-!
# Soundness of the genssa validator's slice G30: pointer conversions in functions with no arm64
op (`docs/plans/proofs3.md` §4)

`g30_value`, `g30_term`, `g30_nilPanic`, `g30_boundsPanic`: `g29_value`'s, `g29_term`'s,
`g29_nilPanic`'s and `g29_boundsPanic`'s statements over `checkG30`. On a function with an arm64
op, `checkG30` is `checkG29` (`checkG30_lowered`) and the theorems are G29's. On one without, the
values are G26's (`nl_core`) and `Convert`, which G12 accepts in lowered functions: in Phase 1's
mode it writes `PtrOps.convert` of its argument read with `Val.retype`, at its shape, again with
`Val.retype` (`stepLoc_convP`). A register content of class 64 converts to one of class 64 related
to the same machine word (`convert_rel`), and `Val.retype` keeps that (`valRel_retype`), so the
register, shared by the argument and the value, needs no code (`nl_conv`). No value is a narrow
load, `MOVDnop` or `MOVDreg`, so the upper-bit table `uL` stays empty.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## `Convert` in Phase 1's mode -/

section Conv

variable {lc : LocCtx} {s s' : LocState} {env : Env} {v : Value}

/-- `Convert x mem` (Phase 1): `PtrOps.convert` of its arguments at the value's shape. -/
theorem stepLoc_convP (hl : lc.ctx.f.lowered = false) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .Convert) {a mem : ID} (ha : v.args = #[a, mem])
    (h : stepLoc env lc s v = .ok s') :
    ∃ x y, s.read lc a = .ok x ∧ s.read lc mem = .ok y ∧
      s' = s.write lc v.id ((PtrOps.convert (lc.ty v.id) [x, y]).retype (lc.ty v.id)) := by
  obtain ⟨argv, r, hmv, hr, rfl⟩ := stepLoc_noclobberP hl ht (by rw [hop]; nofun)
    (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun) (by rw [hop]; nofun)
    (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) (by rw [hop]; rfl) h
  rw [ha] at hmv
  change ((s.read lc a).bind fun x => (s.read lc mem).bind fun y => .ok [x, y]) = .ok argv at hmv
  cases hx : s.read lc a with
  | panic e mm => rw [hx] at hmv; cases hmv
  | stuck msg => rw [hx] at hmv; cases hmv
  | ok x =>
    cases hy : s.read lc mem with
    | panic e mm => rw [hx, hy] at hmv; cases hmv
    | stuck msg => rw [hx, hy] at hmv; cases hmv
    | ok y =>
      rw [hx, hy] at hmv
      cases hmv
      have he : evalOpL true env lc.ctx s.fr v [x, y] (lc.ty v.id) =
          .ok (PtrOps.convert (lc.ty v.id) [x, y]) := by
        unfold evalOpL evalOp frameVal; rw [hop]; rfl
      rw [he] at hr
      cases hr
      exact ⟨x, y, rfl, rfl, rfl⟩

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {b : ID} {i : Nat} {m : MState} {j j' : Nat}
  {K K' : Nat → Option Nat} {P : BitVec 64 → Prop}

/-- `Convert` in its argument's register (Phase 1): no code; the register keeps its word. -/
theorem nl_conv (hl : lc.ctx.f.lowered = false) (hA : AddrAgree E.ι)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι P K s)
    (hj : E.pcOf b i = pcAt text psA.toList j)
    (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j') (hvs : j' = j)
    {o : Int} (hop : v.op = .Convert) (hsz : v.args.size = 2) (hao : argObj lc v 0 = .ok (64, o))
    (hro : resObj lc v = .ok (64, o)) (hma : memArg lc v 1 = .ok ())
    (htemp : (lc.temps[v.id]?).join = none)
    (hR : KRead lc v K) (hK : KNext lc v K K') (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι P K' s' ∧ s'.slots = s.slots := by
  obtain ⟨a, r1, ha0, hah, hor1, hca⟩ := argObj_spec hao
  obtain ⟨r2, hvh, hd, hor2, hcv⟩ := resObj_spec hro
  obtain rfl := objOf?_inj hor1 hor2
  obtain ⟨mem, ha1, -, -⟩ := memArg_spec hma
  obtain ⟨k, hk32, ho, hkk⟩ := objOf?_some hor1
  rw [ho] at hor1
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨x, hx, hxv, hxf⟩ := arg_relP hA hl hm hinv hah hca (kread_arg hR hnp ha0 hah hca) hkk
  obtain ⟨x', y, hx', -, rfl⟩ := stepLoc_convP hl htemp hop (arr2 hsz ha0 ha1) hs
  rw [hx] at hx'
  cases hx'
  rw [write_reg hvh hcv]
  obtain ⟨hf, hrel⟩ := convert_rel (t := lc.ty v.id) (y := y) hA hxf hxv
  obtain ⟨hlm, hinv'⟩ := finish_reg hm hinv hd hk32 hor1 (valRel_retype hA hcv hf hrel)
    (fits_retype hcv _) (b' := b) (i' := i + 1)
  rw [wX_rX_self, hj', hvs, ← hj, ← hm.pc] at hlm
  exact ⟨m, .refl, hlm, hinv'.mono (knext_set hK hnp hvh hcv), rfl⟩

end Conv

/-! ## The theorems -/

/-- A value `checkNL30` accepted that is not an activation value is a `MakeResult`, `InlMark`,
`Copy` or `Convert`. -/
theorem nl30_ops {lc : LocCtx} {g : G2In} {ps : Array Prog} {bstart : ID → Option Nat}
    {tab : PcTab} {kt : KTab} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value}
    (hc : checkNL30 lc ps bstart g = .ok (tab, kt))
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) :
    v.op = .MakeResult ∨ v.op = .InlMark ∨ v.op = .Copy ∨ v.op = .Convert := by
  obtain ⟨c, hlc, -, -, -, hvk, -, -, -, -, -, -, -, hblocks, -, -⟩ := checkNL30_spec hc
  subst hlc
  obtain ⟨b, j, js, e', next, hb', -, hvals, -, -, -⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, -⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk] at hkd
  rcases (vkindNL30_spec hkd hen).2 with ⟨hop, -⟩ | ⟨hops, -⟩
  · exact .inr (.inr (.inr hop))
  · rcases hops with h | h | h
    · exact .inl h
    · exact .inr (.inl h)
    · exact .inr (.inr (.inl h))

/-- **G30, values.** `g29_value`'s statement over `checkG30`. -/
theorem g30_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG30 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hu : UOKL m (uL lc blk i))
    (hpre : G14Pre lc s v)
    (hcall : CallOK H E g L lc s s' v m) (hcallz : CallOKZ H E g L lc s s' v m)
    (hicall : ICallOK H E L ret lc s s' v m)
    (hwb : WbOK H E g L lc s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hmeq : MemEqOK H E g L lc s v m) (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G28Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' ∧
      UOKL m' (uL lc blk (i + 1)) := by
  cases hl : lc.ctx.f.lowered with
  | true =>
    exact g29_value (checkG30_lowered hl hc) hE hbid hb hi hv hen hm hinv hu hpre hcall hcallz
      hicall hwb hclo hgetg hmeq hs
  | false =>
  rw [uL_succ hi hv]
  have hE0 := hE
  obtain ⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, -, -, -, hk, hlt, hnd, hblocks, -, -⟩ :=
    checkNL30_spec (checkG30_nl hl hc)
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
  obtain ⟨htemp, hcase⟩ := vkindNL30_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  rw [kAt_succ hi hv]
  -- no value of `checkNL30` touches the upper-bit table
  have fin : ∀ m', v.op ≠ .ARM64MOVDnop → v.op ≠ .ARM64MOVDreg → narrowLd? c.cx.lc v = none →
      PStar H (Link.byId sym text az ez c.cx.ps.toList) c.cx.ps.toList ret m m' →
      LocMatch E s' bid (i + 1) m' →
      CoreInv E.ι (StkAt E) (kStep c.cx.lc (kAt c.cx.lc kt bid blk i) v).get s' →
      s'.slots = s.slots →
      ∃ E' m', E.Extends E' ∧
        G28Env c.cx.lc c.g (Link.byId sym text az ez c.cx.ps.toList) c.cx.ps ret tab E' ∧
        PStar H (Link.byId sym text az ez c.cx.ps.toList) c.cx.ps.toList ret m m' ∧
        LocMatch E' s' bid (i + 1) m' ∧
        G3Inv E' c.cx.lc (kStep c.cx.lc (kAt c.cx.lc kt bid blk i) v) s' ∧
        UOKL m' (uStepL c.cx.lc (uL c.cx.lc blk i) v) := by
    intro m' h1 h2 hnl hp hlm hcore hsl
    have hue : uEntry c.cx.lc v = none := by simp only [uEntry, hnl]
    refine ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE0, hp, hlm,
      ⟨hcore, fun k v hk => hinv.slots k v (hsl ▸ hk)⟩, ?_⟩
    rw [uStepL_other hue h1 h2]
    intro e he
    cases he
  rcases hcase with ⟨hop, hsz, ⟨o, hao, hro⟩, hma, rfl⟩ | ⟨hops, kd1, rfl, hVK⟩
  · obtain ⟨r, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4⟩ := nl_conv (H := H) hl hA hm hinv.core hj hj' hvs hop hsz hao hro
      hma htemp (kread_of_reads hreads) (knext_kStep fun _ => (hs_reg hvh).noRegs) hs
    exact fin m' (by rw [hop]; nofun) (by rw [hop]; nofun)
      (by unfold narrowLd?; rw [hop]; rfl) h1 h2 h3 h4
  · obtain ⟨m', h1, h2, h3, h4⟩ := nl_core (H := H) hl hA hnd hlt hret hm hinv.core hj hj'
      (vstep_v2 hvs) hops hVK htemp (kread_of_reads hreads)
      (knext_kStep fun hnp => nl_homes hnp hVK) hs
    exact fin m' (by rcases hops with h | h | h <;> rw [h] <;> nofun)
      (by rcases hops with h | h | h <;> rw [h] <;> nofun) (narrowLd?_nl hops) h1 h2 h3 h4

/-- **G30, nil panics.** `g29_nilPanic`'s statement over `checkG30`. -/
theorem g30_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG30 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  cases hl : lc.ctx.f.lowered with
  | true => exact g29_nilPanic (checkG30_lowered hl hc) hE hbid hb hi hv hop hm hinv hs
  | false =>
    rcases nl30_ops (checkG30_nl hl hc) hbid hb hi hv (by rw [hop]; rfl) with h | h | h | h <;>
      rw [h] at hop <;> cases hop

/-- **G30, bounds panics.** `g29_boundsPanic`'s statement over `checkG30`. -/
theorem g30_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG30 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s) (hbok : BoundsOK H g L ps.toList)
    (hs : stepLoc env lc s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' := by
  cases hl : lc.ctx.f.lowered with
  | true =>
    exact g29_boundsPanic (checkG30_lowered hl hc) hE hbid hb hi hv hop hm hinv hbok hs
  | false =>
    have hen : entryOp24 v.op = false := by
      rcases pbOp_cases hop with h | h | h | h <;> rw [h] <;> rfl
    rcases nl30_ops (checkG30_nl hl hc) hbid hb hi hv hen with h | h | h | h <;> rw [h] at hop <;>
      cases hop

/-- **G30, terminators.** `g29_term`'s statement over `checkG30`; a function with no arm64 op
has only `Ret` blocks, which go to no successor. -/
theorem g30_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG30 lc ps bstart g = .ok (tab, kt)) (hE : G28Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s) (hpre : G1TermPre lc s blk)
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' ∧
      e.b ∈ lc.ctx.f.blocks.toList := by
  cases hl : lc.ctx.f.lowered with
  | true => exact g29_term (checkG30_lowered hl hc) hE hbid hb hm hinv hpre ht
  | false =>
    obtain ⟨-, -, -, -, -, -, -, hr, -⟩ := checkNL30_spec (checkG30_nl hl hc)
    obtain ⟨R, -, hn⟩ := stepTermLoc_gen ht
    exact (stepTermL_ret (allRet_spec hr hbid hb) hn).elim

end GoFV.Proof.Gen
