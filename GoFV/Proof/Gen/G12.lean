import GoFV.Proof.Gen.G11
import GoFV.Proof.Gen.Spec12

variable [GoFV.SSA.Sem.Addrs]

/-!
# Soundness of the genssa validator's slice G12: pointer conversions (`docs/plans/proofs3.md` §4)

`g12_value`, `g12_term`, `g12_nilPanic`: `g11_value`'s, `g11_term`'s and `g11_nilPanic`'s
statements over `checkG12`, with no new premise.

`Convert x mem` runs under `runLoc` as Phase 1's `PtrOps.convert` (`stepLoc_conv`): a pointer
converted to `uintptr` is its Phase 1 address when it has one and is convertible (else `poison`),
anything else is unchanged; the result takes the value's shape. Genssa emits no code: `checkG12`
puts the argument and the value in one register of class 64. The machine does not move; the
register keeps its word, which is the converted value's (`valRel_convert`): a convertible pointer
is no frame temporary, so under `AddrAgree` its injected address is its Phase 1 address
(`ptrRel_addr`), and a pointer read back from an integer relates as the integer did
(`valRel_retypeL`).
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm

/-! ## `stepLoc` of `Convert` -/

section Step

variable {env : Env} {lc : LocCtx} {s s' : LocState} {v : Value}

/-- `Convert x mem` writes `PtrOps.convert` of its arguments, at its shape, to its home. -/
theorem stepLoc_conv (hl : lc.ctx.f.lowered = true) (ht : (lc.temps[v.id]?).join = none)
    (hop : v.op = .Convert) {a mem : ID} (ha : v.args = #[a, mem])
    (h : stepLoc env lc s v = .ok s') :
    ∃ x y, s.read lc a = .ok x ∧ s.read lc mem = .ok y ∧
      s' = s.write lc v.id ((PtrOps.convert (lc.ty v.id) [x, y]).retypeL (lc.ty v.id)) := by
  obtain ⟨argv, r, hmv, hr, rfl⟩ := stepLoc_noclobber hl ht (by rw [hop]; nofun)
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

end Step

/-! ## The relation -/

/-- A register content of class 64, converted: of class 64 and related to the same machine word. -/
theorem convert_rel {ι : Blk → Option (BitVec 64)} (hA : AddrAgree ι) {t : Ty} {x y : Val}
    {r : BitVec 64} (hf : Fits 64 x) (hv : ValRel ι x r) :
    Fits 64 (PtrOps.convert t [x, y]) ∧ ValRel ι (PtrOps.convert t [x, y]) r := by
  simp only [PtrOps.convert]
  split
  · rename_i p
    cases hc : p.convertible with
    | false => exact ⟨trivial, trivial⟩
    | true =>
      cases ha : p.addr? with
      | none => exact ⟨trivial, trivial⟩
      | some a => exact ⟨rfl, Or.inl (ptrRel_addr hA hv ha (notTemp_of_convertible hc))⟩
  · exact ⟨hf, hv⟩

/-- A register content of class 64 converted to a shape of class 64 keeps its machine word. -/
theorem valRel_convert {ι : Blk → Option (BitVec 64)} (hA : AddrAgree ι) {t : Ty} {x y : Val}
    {r : BitVec 64} (ht : cls t = some 64) (hf : Fits 64 x) (hv : ValRel ι x r) :
    ValRel ι ((PtrOps.convert t [x, y]).retypeL t) r :=
  have key := convert_rel (t := t) (y := y) hA hf hv
  valRel_retypeL hA ht key.1 key.2

/-! ## The value -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat}

/-- `Convert` in its argument's register: no code; the register keeps its word, and so does every
X register (`XW`). -/
theorem g12_conv (F : Facts lc sym text az ez psA.toList ret E)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s) (hsi : SlotInv lc s)
    (hR : KRead lc v K) (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {o : Int} (hop : v.op = .Convert) (hsz : v.args.size = 2) (hao : argObj lc v 0 = .ok (64, o))
    (hro : resObj lc v = .ok (64, o)) (hma : memArg lc v 1 = .ok ()) (hvs : j' = j)
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' ∧ SlotInv lc s' ∧
      XW lc v m m' := by
  have hl := F.lowered
  have hA := F.addr
  obtain ⟨a, r1, ha0, hah, hor1, hca⟩ := argObj_spec hao
  obtain ⟨r2, hvh, hd, hor2, hcv⟩ := resObj_spec hro
  obtain rfl := objOf?_inj hor1 hor2
  obtain ⟨mem, ha1, -, -⟩ := memArg_spec hma
  obtain ⟨k, hk32, ho, hkk⟩ := objOf?_some hor1
  rw [ho] at hor1
  have hnp : v.op ≠ .Phi := by rw [hop]; nofun
  obtain ⟨x, hx, hxv, hxf⟩ := arg_rel hA hl hm hinv hah hca (kread_arg hR hnp ha0 hah hca) hkk
  obtain ⟨x', y, hx', -, rfl⟩ := stepLoc_conv hl htemp hop (arr2 hsz ha0 ha1) hs
  rw [hx] at hx'
  cases hx'
  rw [write_reg hvh hcv]
  obtain ⟨hlm, hinv'⟩ := finish_reg hm hinv hd hk32 hor1 (valRel_convert hA hcv hxf hxv)
    (fits_retypeL hcv _) (b' := b) (i' := i + 1)
  rw [wX_rX_self, hj', hvs, ← hj, ← hm.pc] at hlm
  exact ⟨m, .refl, hlm, hinv'.mono (knext_set hK hnp hvh hcv), hsi, .inl rfl⟩

end Cases

/-! ## The theorems -/

/-- One value of G12's kinds (`VK12`) emitted at the Progs from `j` to `j'`: `vk11_step`'s
statement for G12's values. -/
theorem vk12_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2}
    (hE : G10Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK12 lc g v kd)
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
  | g11 hVK11 =>
    exact vk11_step hE F hhome hcf hv hVK11 hvs htemp hj hj' hreads hm hinv hpre hcall hicall hwb
      hclo hs
  | conv hop hsz hao hro hma =>
    obtain ⟨r, hvh, -, -, -⟩ := resObj_spec hro
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g12_conv (H := H) F hm hinv.core hinv.slots
      (kread_of_reads hreads) (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hao hro
      hma hvs htemp hs
    exact ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩⟩

/-- **G12, values.** `g11_value`'s statement over `checkG12`. -/
theorem g12_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG12 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
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
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, hcf, hk, hlt, hnd, hblocks⟩ := checkG12_spec hc
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
  obtain ⟨htemp, hVK⟩ := vkind12_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  rw [kAt_succ hi hv]
  exact vk12_step hE0 F hhome hcf hv hVK hvs htemp hj hj' hreads hm hinv hpre hcall hicall hwb hclo
    hs

/-- **G12, nil panics.** `g11_nilPanic`'s statement over `checkG12`. -/
theorem g12_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG12 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
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
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks⟩ := checkG12_spec hc
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
  obtain ⟨-, hVK⟩ := vkind12_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases hVK with
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
  | conv hop' => rw [hop] at hop'; cases hop'

/-- **G12, terminators.** `g11_term`'s statement over `checkG12`. -/
theorem g12_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG12 lc ps bstart g = .ok (tab, kt)) (hE : G10Env lc g L ps ret tab E)
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
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome, -, hk, hlt, hnd, hblocks⟩ := checkG12_spec hc
  exact termK_step hpcOf ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb
    hm hinv hpre ht

end GoFV.Proof.Gen
