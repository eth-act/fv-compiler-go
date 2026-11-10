import GoFV.Proof.Gen.G55
import GoFV.Proof.Gen.Spec56
import GoFV.Proof.Gen.RoByte

variable [GoFV.SSA.Sem.Addrs]

/-!
# Slice G56 of the genssa validator: float constants in read-only symbols (`docs/plans/proofs3.md` §10)

`checkG56 lc` (`GoFV/Gen/Check56.lean`) is G55 with `FMOVSconst`/`FMOVDconst` homed either by
G44's `FMOVS`/`FMOVD $c, Fd` or, on P0' (`progedit`'s rewrite), by the load
`FMOVS`/`FMOVD sym(SB), Fd` of a float constant symbol of `G2In.syms` whose name says it holds the
bits `$c` writes (`constSymA`, `constSymAlloc?`). `g56_fconst`: from a `LocMatch`ed state whose
memory has the float constant symbols among the Prog list's (`RoPre56`, what `lreach_roMem` gives
along the run from `RoMem (constRo …)` of the input), the load reads, at the symbol's linked
address (`G2Env.glob`), the bytes the memory injection puts there (`ro_byte`, above the nil page by
`ro_addr`): the bits of the constant (`readMem_fconst`), which `FCONST` writes too. `g56_value`
takes G54's premise `G54Pre` (G55 adds none) and `RoPre56`; `g56_initMem`, `g56_term`,
`g56_nilPanic`, `g56_boundsPanic` are G55's statements over `checkG56`, under `G49Env`.
-/

namespace GoFV.Proof.Gen

open GoFV.SSA GoFV.SSA.Sem GoFV.Gen.Check GoFV.Arm64 GoFV.Asm GoFV.Asm.ARM64

/-! ## The premise -/

/-- G56's premise: the state's memory has the float constant symbols among the Prog list's
symbols (`constRo (symNames g)`), read-only. -/
def RoPre56 (g : G2In) (s : LocState) : Prop :=
  ∀ mm, s.mem = .mem mm → RoMem (constRo (symNames g)) mm

/-! ## The constant's bytes -/

/-- Byte `j` of the allocation of `n` little-endian bytes of `x`. -/
theorem roAlloc_byte {x n j : Nat} (hj : j < n) :
    (roAlloc (leBytesU8 x n)).data[j]? = some (.b (BitVec.ofNat 8 (x / 256 ^ j))) := by
  simp only [roAlloc, leBytesU8, Array.getElem?_map, Array.getElem?_ofFn, List.getElem?_toArray,
    List.getElem?_range hj, Option.map_some, Option.some.injEq, Byte.b.injEq]
  apply BitVec.eq_of_toNat_eq
  simp [UInt8.toNat_ofNat]

/-- A constant symbol of `G2In.syms` is among `constRo (symNames g)`. -/
theorem constRo_mem {g : G2In} {y : Nat} {name : GoStr} {abi : Nat} {al : Alloc}
    (hy : g.syms[y]? = some (name, abi)) (hal : constSymAlloc? name.toStringLossy = some al) :
    (name.toStringLossy, al) ∈ constRo (symNames g) := by
  unfold constRo symNames
  rw [List.mem_filterMap]
  refine ⟨name.toStringLossy, List.mem_map.2 ⟨(name, abi), ?_, rfl⟩, by rw [hal]; rfl⟩
  exact Array.mem_toList_iff.2 (Array.mem_of_getElem? hy)

/-- The `n` bytes of the constant `fconstNat n k` read from memory are the bits `FCONST` writes. -/
theorem readMem_fconst {M : GoFV.Arm64.Memory} {a : BitVec 64} {n : Nat} (hn : n = 4 ∨ n = 8)
    {k : Int64}
    (hb : ∀ j, j < n → M (a + BitVec.ofNat 64 j) = BitVec.ofNat 8 (fconstNat n k / 256 ^ j)) :
    (readMem M a n).setWidth 128 = fconstBits n k.toUInt64 := by
  have hlt : fconstNat n k < 256 ^ n := by
    rcases hn with rfl | rfl
    · have := (GoFV.IEEE.convert GoFV.IEEE.Fmt.b64 GoFV.IEEE.Fmt.b32 .rne
        (BitVec.ofNat 64 k.toUInt64.toNat)).isLt
      simp only [fconstNat, ↓reduceIte]
      exact Nat.lt_of_lt_of_le this (by decide)
    · have := k.toUInt64.toNat_lt
      simp only [fconstNat, show (8 : Nat) ≠ 4 by decide, ↓reduceIte]
      exact Nat.lt_of_lt_of_le this (by decide)
  have hr := readMem_of_bytes M n a (fconstNat n k) hlt fun j hj => by
    rw [hb j hj, BitVec.toNat_ofNat]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, hr]
  rcases hn with rfl | rfl
  · simp only [fconstBits, fconstNat, ↓reduceIte, BitVec.toNat_setWidth]
  · have := k.toUInt64.toNat_lt
    simp only [fconstBits, fconstNat, show (8 : Nat) ≠ 4 by decide, ↓reduceIte,
      BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt this]

/-! ## The value -/

section Cases

variable {H : Hooks} {sym : Nat → BitVec 64} {text : BitVec 64} {az ez : Int} {psA : Array Prog}
  {ret : BitVec 64} {E : MatchEnv} {lc : LocCtx} {s s' : LocState} {b : ID} {i : Nat}
  {m : MState} {env : Env} {v : Value} {j j' : Nat} {K K' : Nat → Option Nat} {g : G2In}

/-- `FMOVSconst`/`FMOVDconst`: `FMOVS`/`FMOVD $c, Fd`, or the load `FMOVS`/`FMOVD sym(SB), Fd`
of its constant symbol, whose bytes the memory has (`RoPre56`). -/
theorem g56_fconst (F : Facts lc sym text az ez psA.toList ret E)
    (hglob : ∀ y name abi, g.syms[y]? = some (name, abi) →
      E.ι (.global name.toStringLossy) = some (sym y))
    (hro : RoPre56 g s)
    (hm : LocMatch E s b i m) (hinv : CoreInv E.ι (StkAt E) K s osp) (hsi : SlotInv lc s)
    (hK : KNext lc v K K')
    (hj : E.pcOf b i = pcAt text psA.toList j) (hj' : E.pcOf b (i + 1) = pcAt text psA.toList j')
    {c : Nat} {rd : Int} (hop : v.op = .ARM64FMOVSconst ∨ v.op = .ARM64FMOVDconst)
    (hsz0 : v.args.size = 0) (hrc : fresObj lc v = .ok (c, rd)) (hc : c = 8 * fBytes v.op)
    (hvs : OneAt2 psA j (fconstPat56 g v c rd) j')
    (htemp : (lc.temps[v.id]?).join = none) (hs : stepLoc env lc s v = .ok s') :
    ∃ m', PStar H (Link.byId sym text az ez psA.toList) psA.toList ret m m' ∧
      LocMatch E s' b (i + 1) m' ∧ CoreInv E.ι (StkAt E) K' s' osp ∧ SlotInv lc s' ∧
      m'.x = m.x := by
  have hl := F.lowered
  have hnp : v.op ≠ .Phi := by rcases hop with h | h <;> rw [h] <;> nofun
  obtain ⟨r, hvh, hfo, hft, hcv⟩ := fresObj_spec hrc
  obtain ⟨kd, hkd, rfl, hkd'⟩ := fobjOf?_some hfo
  obtain ⟨mm, hmm, hMI⟩ := hm.mem
  have hroM := hro mm hmm
  obtain ⟨argv, hargv, rfl⟩ := stepLoc_pureF hl htemp
    (by rcases hop with h | h <;> simp [h]) hs
  have hnil : v.args.toList = [] := by rw [Array.size_eq_zero_iff.mp hsz0]
  rw [hnil] at hargv
  cases hargv
  simp only [List.reverse_nil]
  rw [write_reg hvh hcv]
  subst hc
  have hn := fBytes_cases v.op
  obtain ⟨hty, -⟩ := fTy_eq hft hcv
  have he : Arm64.evalPure v.op (lc.ty v.id) v.auxInt v.aux [] =
      if fBytes v.op = 4 then FOps.const32 v.auxInt else FOps.const64 v.auxInt := by
    rcases hop with h | h <;> rw [h] <;> rfl
  rw [he, hty]
  have hz := fvalRel_fconst hn v.auxInt
  have hzf := fits_retypeL (hty ▸ hcv)
    (if fBytes v.op = 4 then FOps.const32 v.auxInt else FOps.const64 v.auxInt)
  have hmov := fmovAs_movMem hn
  refine (op_regV (H := H) F hm hinv hj hj' hvs hkd' hz hzf
    (knext_set hK hnp hvh hcv) (fun k0 hk0 hok => ?_)).imp
    fun _ h => ⟨h.1, h.2.1, h.2.2.1, hsi, h.2.2.2⟩
  simp only [fconstPat56, Bool.or_eq_true] at hok
  rcases hok with hok | hok
  · -- `FMOVS`/`FMOVD $c, Fd`
    obtain ⟨has, hf, -, ht, -⟩ := Shape.ok_eq hok
    rw [progStep_fconst hkd (nextAddr_pcAt F.nodup hk0) (by rw [has]; exact hmov) hf ht]
    rfl
  · -- the load of the constant symbol
    have hok' : (Pat.mk (plain (fmovAs (8 * fBytes v.op))
        (constSymA g (fBytes v.op) (fconstNat (fBytes v.op) v.auxInt))
        (· == regA (REG_F0 + kd))) "").ok psA.toList[k0] = true := hok
    obtain ⟨has, hf, -, ht, -⟩ := plain_spec hok'
    obtain ⟨hf1, hf2, hf5, y, name, abi, hy1, hy, hal⟩ := constSymA_spec hf
    have hpa := hglob y name abi hy
    have hmem := constRo_mem hy hal
    have hsize : 0 < (roAlloc (leBytesU8 (fconstNat (fBytes v.op) v.auxInt)
        (fBytes v.op))).data.size := by
      simp only [roAlloc, leBytesU8, Array.size_map, List.size_toArray, List.length_range]
      omega
    obtain ⟨h4096, -⟩ := ro_addr hMI hroM hmem hpa hsize
    have hnilp : nilPage (sym y) = false := by
      simp only [nilPage, decide_eq_false_iff_not, Nat.not_lt]
      exact h4096
    have hma' : (ProgCtx.mk (Link.byId sym text az ez psA.toList)
        { m with pc := pcAt text psA.toList k0 } psA.toList[k0]).mem psA.toList[k0].from_ =
        .ok (sym y, none) := by
      rw [ctx_mem_glob hf1 hf2 hf5 hy1]
      simp only [BitVec.ofInt_ofNat, BitVec.add_zero]
      rfl
    have hrd : (readMem ({ m with pc := pcAt text psA.toList k0 } : MState).mem (sym y)
        (fBytes v.op)).setWidth 128 = fconstBits (fBytes v.op) v.auxInt.toUInt64 :=
      readMem_fconst hn fun j hj => ro_byte F.addr hMI hroM hmem hpa (roAlloc_byte hj)
    rw [progStep_floadAt hkd (nextAddr_pcAt F.nodup hk0) (by rw [has]; exact hmov) hf1 hma'
      (beq_iff_eq.mp ht) hnilp, hrd]
    rfl

end Cases

/-! ## One value -/

/-- One value of G56's kinds: `vk54_step`'s statement, under `G54Pre` and `RoPre56`. -/
theorem vk56_step {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {sym : Nat → BitVec 64}
    {text : BitVec 64} {az ez : Int} {ps : Array Prog} {ret : BitVec 64} {tab : PcTab}
    {E : MatchEnv} {bid : ID} {i j j' : Nat} {id : ID} {v : Value} {s s' : LocState}
    {m : MState} {K : KMap} {kd : VKind2} {L : List (Nat × Nat × Bool)}
    (hE : G49Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E)
    (F : Facts lc sym text az ez ps.toList ret E) (hhome : ∀ i, homeOK10 lc i = true)
    (hcf : checkFrame lc g = .ok ()) (hv : lc.ctx.f.value? id = some v) (hVK : VK56 lc g v kd)
    (hvs : VStep2 ps kd j j') (hloop : loopOp lc v = true → loopTgt ps j = true)
    (hj : E.pcOf bid i = pcAt text ps.toList j) (hj' : E.pcOf bid (i + 1) = pcAt text ps.toList j')
    (hreads : ∀ rc ∈ kReads lc v, K.get rc.1 = some rc.2)
    (hm : LocMatch E s bid i m) (hinv : G3Inv E lc K s osp) (hL : UOKL m L)
    (hmem : ∀ x, (v.op = .ARM64MOVDnop ∨ v.op = .ARM64MOVDreg) → v.args[0]? = some x →
      ∃ r c, regHome? lc x = some r ∧ cls (lc.ty x) = some c ∧
        (r, c, lc.signOf lc.ctx.f.valueTab.size x) ∈ L)
    (hpre : G54Pre lc s v) (hro : RoPre56 g s)
    (hcall : CallOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hcallz : CallOKZAt osp H E g (Link.byId sym text az ez ps.toList) lc s s' v m)
    (hicall : ICallOKAt osp H E (Link.byId sym text az ez ps.toList) ret lc s s' v m)
    (hwb : WbOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s v m) (hclo : CloOK E s v m)
    (hgetg : GetGOK E v) (hmeq : MemEqOKAt osp H E g (Link.byId sym text az ez ps.toList) lc s v m)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env lc g (Link.byId sym text az ez ps.toList) ps ret tab E' ∧
      PStar H (Link.byId sym text az ez ps.toList) ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kStep lc K v) s' osp ∧
      UOKL m' (uStep35 lc L v) := by
  cases hVK with
  | g55 _ _ hVK55 =>
    exact vk55_step hE F hhome hcf hv hVK55 hvs hloop hj hj' hreads hm hinv hL hmem hpre hcall
      hcallz hicall hwb hclo hgetg hmeq hs
  | fconst hop ht hsz hrc hc =>
    obtain ⟨-, -, -, -, -, hglob, -, -, -, -, -⟩ := hE.env.env.env.env.env
    obtain ⟨r, hvh, -, -, -⟩ := fresObj_spec hrc
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g56_fconst (H := H) F (fun y name abi h => hglob y name abi h)
      hro hm hinv.core hinv.slots (knext_kStep fun _ => (hs_reg hvh).noRegs) hj hj' hop hsz hrc hc
      hvs ht hs
    refine ⟨E, m', ⟨rfl, fun _ _ h => h⟩, hE, h1, h2, ⟨h3, h4⟩, ?_⟩
    rw [uStep35_f44 (by rcases hop with h | h <;> simp [FOp44, h])]
    exact fun e he => by cases he

/-- A nil check of G56's kinds is G7's. -/
theorem vk56_nil {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK56 lc g v kd)
    (hop : v.op = .ARM64LoweredNilCheck) : VK7 lc g v kd := by
  cases h with
  | g55 _ _ h => exact vk55_nil h hop
  | fconst h => rcases h with h | h <;> rw [hop] at h <;> cases h

/-- A bounds check of G56's kinds is G28's. -/
theorem vk56_pb {lc : LocCtx} {g : G2In} {v : Value} {kd : VKind2} (h : VK56 lc g v kd)
    (hop : pbOp v.op = true) : VK28 lc g v kd := by
  cases h with
  | g55 _ _ h => exact vk55_pb h hop
  | fconst h => rcases h with h | h <;> rw [h] at hop <;> cases hop

/-! ## The theorems on G56's check -/

/-- G54's values and the float constants under G56's check, under `G54Pre` and `RoPre56`. -/
theorem g56L_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG56L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s osp) (hu : UOKL m (uL35 lc (uIn35 lc bid) blk i))
    (hpre : G54Pre lc s v) (hro : RoPre56 g s)
    (hcall : CallOKAt osp H E g L lc s s' v m) (hcallz : CallOKZAt osp H E g L lc s s' v m)
    (hicall : ICallOKAt osp H E L ret lc s s' v m)
    (hwb : WbOKAt osp H E g L lc s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hmeq : MemEqOKAt osp H E g L lc s v m) (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' osp ∧
      UOKL m' (uL35 lc (uIn35 lc bid) blk (i + 1)) := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    obtain ⟨E', m', hx, hE', h1, h2, h3, -⟩ := g33_value (checkG33_of_56L hl hc) hE.env hbid hb
      hi hv hen hm hinv (by rw [uL31_nl hl]; intro e he; cases he) hpre.1.1.1.1.1.1.1.1.1 hcall
      hcallz hicall hwb hclo hgetg hmeq hs
    refine ⟨E', m', hx, ⟨hE', hE.vars.extend hx⟩, h1, h2, h3, ?_⟩
    rw [uL35_nl hl]
    intro e he
    cases he
  | true =>
  rw [uL35_succ hl hi hv]
  have hE0 := hE
  obtain ⟨⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, hcf, hk, hlt, hnd, hblocks, -, hmovd, -, hlp⟩ :=
    checkG56L_spec hl hc
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
  have hVK := vkind56_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e]).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hj' : E.pcOf bid (i + 1) = pcAt text c.cx.ps.toList ((js ++ [e]).getD (i + 1) 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  have hloop : loopOp c.cx.lc v = true → loopTgt c.cx.ps ((js ++ [e]).getD i 0) = true :=
    fun hop => loopOK_spec hlp hrow hb hi hv hop
  rw [kAt_succ hi hv]
  exact vk56_step hE0 F hhome hcf hv hVK hvs hloop hj hj' hreads hm hinv hu
    (fun x hop hx => movdOK35_spec hmovd hbid hb hi hv hop hx)
    hpre hro hcall hcallz hicall hwb hclo hgetg hmeq hs

/-- `InitMem` under G56's check: `g54L_initMem`'s statement. -/
theorem g56L_initMem {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG56L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
    (hl : lc.ctx.f.lowered = true)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .InitMem) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s osp) (hpre : MemInit s)
    (hs : stepLoc env lc s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env lc g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' lc (kAt lc kt bid blk (i + 1)) s' osp ∧
      UOKL m' (uL35 lc (uIn35 lc bid) blk (i + 1)) := by
  have hE0 := hE
  obtain ⟨⟨⟨⟨⟨⟨-, hlink, hpcOf, -, -, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, -, -, -, -, -, -, hblocks, -, -, -, -⟩ := checkG56L_spec hl hc
  obtain ⟨b, j, js, e, next, hb', -, hvals, -, -, hrow⟩ := Cx2.blocks_spec hblocks bid hbid
  rw [hb] at hb'
  cases hb'
  obtain ⟨-, -, hstep⟩ := Cx2.values_spec hvals
  obtain ⟨hi', hid⟩ := Array.getElem?_eq_some_iff.1 hi
  obtain ⟨v', kd, hv', hkd, hvs⟩ := hstep i (by simpa using hi')
  have hid' : blk.values.toList[i] = id := by simpa using hid
  rw [hid', hv] at hv'
  cases hv'
  rw [hvk, vkind56_initMem hop, vkind55_initMem hop, vkind54_initMem hop, vkind53_initMem hop,
    vkind52_initMem hop] at hkd
  have hkd := vkind49_initMem hop hkd
  rw [vkind51_initMem hop, vkind50_initMem hop, vkind47_initMem hop, vkind46_initMem hop,
    vkind45_initMem hop, vkind44_initMem hop] at hkd
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

/-- G38's nil panics under G56's check. -/
theorem g56L_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG56L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s osp) (hs : stepLoc env lc s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e := by
  cases hl : lc.ctx.f.lowered with
  | false => exact g33_nilPanic (checkG33_of_56L hl hc) hE.env hbid hb hi hv hop hm hinv hs
  | true =>
  obtain ⟨⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, -, -⟩ :=
    checkG56L_spec hl hc
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
  have hVK := vkind56_spec hkd (by rw [hop]; rfl)
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  cases vk56_nil hVK hop with
  | g6 hne _ => exact absurd hop hne
  | nil _ hsz2 _ _ hao hma =>
    exact g7_nilFault (H := H) F hm hinv.core (kread_of_reads hreads) hj hop hsz2 hao hma hvs hs

/-- G38's bounds panics under G56's check. -/
theorem g56L_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG56L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E lc (kAt lc kt bid blk i) s osp) (hbok : BoundsOK H g L ps.toList)
    (hs : stepLoc env lc s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    exact g33_boundsPanic (checkG33_of_56L hl hc) hE.env hbid hb hi hv hop hm hinv hbok hs
  | true =>
  obtain ⟨⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, hsyms, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, hvk, -, hl, hhome, -, hk, hlt, hnd, hblocks, hpb, -, -, -⟩ :=
    checkG56L_spec hl hc
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
  have hVK := vkind56_spec hkd hen
  have hj : E.pcOf bid i = pcAt text c.cx.ps.toList ((js ++ [e']).getD i 0) := by
    rw [hpcOf]; simp only [pcOfTab, hrow, Option.getD_some]
  have hreads := ((checkK_spec hk).2 bid hbid blk hb).1 i id v hi hv
  have F : Facts c.cx.lc sym text az ez c.cx.ps.toList ret E :=
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩
  exact vk28_boundsPanic F hsyms hpb hrow hb hi hv (vk56_pb hVK hop) hvs hj hreads hop hm hinv
    hbok hs

/-- G38's terminators under G56's check. -/
theorem g56L_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG56L lc ps bstart g = .ok (tab, kt)) (hE : G49Env lc g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E lc (kAt lc kt bid blk blk.values.size) s osp) (hpre : G1TermPre lc s blk)
    (hu : UOKL m (uL35 lc (uIn35 lc bid) blk blk.values.size))
    (ht : stepTermLoc lc s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧ G3Inv E lc (kt.at e.b) s' osp ∧
      e.b ∈ lc.ctx.f.blocks.toList ∧ UOKL m' (uIn35 lc e.b) := by
  cases hl : lc.ctx.f.lowered with
  | false =>
    obtain ⟨m', h1, h2, h3, h4, -⟩ := g33_term (checkG33_of_56L hl hc) hE.env hbid hb hm hinv hpre
      (by rw [uL31_nl hl]; intro e he; cases he) ht
    refine ⟨m', h1, h2, h3, h4, ?_⟩
    rw [uIn35_nl hl]
    intro e he
    cases he
  | true =>
  obtain ⟨⟨⟨⟨⟨⟨-, hlink, hpcOf, hret, hA, -, -, -, -, -, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hE
  obtain ⟨sym, text, az, ez, hL⟩ : ∃ sym text az ez, L = Link.byId sym text az ez ps.toList :=
    ⟨_, _, _, _, hlink⟩
  have htext : L.text = text := by rw [hL]; rfl
  rw [htext] at hpcOf
  subst hL
  obtain ⟨c, rfl, rfl, -, rfl, -, htm, hl, hhome, -, hk, hlt, hnd, hblocks, -, -, hedges, -⟩ :=
    checkG56L_spec hl hc
  obtain ⟨m', h1, h2, h3, h4, he, hx⟩ := termK_stepX hpcOf
    ⟨hl, clsReg_of_home10 hhome, hnd, hlt, hret, hA⟩ htm hk hblocks hbid hb hm hinv hpre ht
  refine ⟨m', h1, h2, h3, h4, fun x hxin => ?_⟩
  exact uok_of_x hx (hu x (uEdgesOK35_edge hedges hbid hb he x hxin))

/-! ## The slice: the theorems on `checkG56 lc`, on `liveCtx lc` -/

/-- **G56, values.** `g54_value`'s statement over `checkG56`, under `G49Env`, `G54Pre` and
`RoPre56` (the state's memory has the float constant symbols among the Prog list's symbols). -/
theorem g56_value {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG56 lc ps bstart g = .ok (tab, kt)) (hE : G49Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hen : entryOp24 v.op = false) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s osp)
    (hu : UOKL m (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk i))
    (hpre : G54Pre (liveCtx lc) s v) (hro : RoPre56 g s)
    (hcall : CallOKAt osp H E g L (liveCtx lc) s s' v m)
    (hcallz : CallOKZAt osp H E g L (liveCtx lc) s s' v m)
    (hicall : ICallOKAt osp H E L ret (liveCtx lc) s s' v m)
    (hwb : WbOKAt osp H E g L (liveCtx lc) s v m) (hclo : CloOK E s v m) (hgetg : GetGOK E v)
    (hmeq : MemEqOKAt osp H E g L (liveCtx lc) s v m) (hs : stepLoc env (liveCtx lc) s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env (liveCtx lc) g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' (liveCtx lc)
      (kAt (liveCtx lc) kt bid blk (i + 1)) s' osp ∧
      UOKL m' (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk (i + 1)) :=
  g56L_value (checkG56_spec hc).2 hE hbid hb hi hv hen hm hinv hu hpre hro hcall hcallz hicall hwb
    hclo hgetg hmeq hs

/-- **G56, `InitMem`.** `g54_initMem`'s statement over `checkG56`. -/
theorem g56_initMem {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s s' : LocState} {m : MState}
    (hc : checkG56 lc ps bstart g = .ok (tab, kt)) (hE : G49Env (liveCtx lc) g L ps ret tab E)
    (hl : lc.ctx.f.lowered = true)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .InitMem) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s osp) (hpre : MemInit s)
    (hs : stepLoc env (liveCtx lc) s v = .ok s') :
    ∃ E' m', E.Extends E' ∧ G49Env (liveCtx lc) g L ps ret tab E' ∧ PStar H L ps.toList ret m m' ∧
      LocMatch E' s' bid (i + 1) m' ∧ G3Inv E' (liveCtx lc)
      (kAt (liveCtx lc) kt bid blk (i + 1)) s' osp ∧
      UOKL m' (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk (i + 1)) :=
  g56L_initMem (checkG56_spec hc).2 hE hl hbid hb hi hv hop hm hinv hpre hs

/-- **G56, nil panics.** `g54_nilPanic`'s statement over `checkG56`. -/
theorem g56_nilPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG56 lc ps bstart g = .ok (tab, kt)) (hE : G49Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : v.op = .ARM64LoweredNilCheck) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s osp)
    (hs : stepLoc env (liveCtx lc) s v = .panic e mm') :
    e = .nilDeref ∧ ∃ m', PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e :=
  g56L_nilPanic (checkG56_spec hc).2 hE hbid hb hi hv hop hm hinv hs

/-- **G56, bounds panics.** `g54_boundsPanic`'s statement over `checkG56`. -/
theorem g56_boundsPanic {env : Env} {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link}
    {ps : Array Prog} {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab}
    {E : MatchEnv} {bid : ID} {blk : Block} {i : Nat} {id : ID} {v : Value} {s : LocState}
    {m : MState} {e : Panic} {mm' : Mem}
    (hc : checkG56 lc ps bstart g = .ok (tab, kt)) (hE : G49Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hi : blk.values[i]? = some id) (hv : lc.ctx.f.value? id = some v)
    (hop : pbOp v.op = true) (hm : LocMatch E s bid i m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk i) s osp)
    (hbok : BoundsOK H g L ps.toList) (hs : stepLoc env (liveCtx lc) s v = .panic e mm') :
    ∃ e' m', BoundsAgree e e' ∧ PStar H L ps.toList ret m m' ∧ PPanics H L ps.toList ret m' e' :=
  g56L_boundsPanic (checkG56_spec hc).2 hE hbid hb hi hv hop hm hinv hbok hs

/-- **G56, terminators.** `g54_term`'s statement over `checkG56`. -/
theorem g56_term {H : Hooks} {lc : LocCtx} {g : G2In} {L : Link} {ps : Array Prog}
    {bstart : ID → Option Nat} {ret : BitVec 64} {tab : PcTab} {kt : KTab} {E : MatchEnv}
    {bid : ID} {blk : Block} {e : Edge} {s s' : LocState} {m : MState}
    (hc : checkG56 lc ps bstart g = .ok (tab, kt)) (hE : G49Env (liveCtx lc) g L ps ret tab E)
    (hbid : bid ∈ lc.ctx.f.blocks.toList) (hb : lc.ctx.f.block? bid = some blk)
    (hm : LocMatch E s bid blk.values.size m)
    (hinv : G3Inv E (liveCtx lc) (kAt (liveCtx lc) kt bid blk blk.values.size) s osp)
    (hpre : G1TermPre (liveCtx lc) s blk)
    (hu : UOKL m (uL35 (liveCtx lc) (uIn35 (liveCtx lc) bid) blk blk.values.size))
    (ht : stepTermLoc (liveCtx lc) s blk = .ok (.goto e, s')) :
    ∃ m', PStar H L ps.toList ret m m' ∧ LocMatch E s' e.b 0 m' ∧
      G3Inv E (liveCtx lc) (kt.at e.b) s' osp ∧ e.b ∈ lc.ctx.f.blocks.toList ∧
      UOKL m' (uIn35 (liveCtx lc) e.b) :=
  g56L_term (checkG56_spec hc).2 hE hbid hb hm hinv hpre hu ht

end GoFV.Proof.Gen
